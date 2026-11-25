# -*- coding: utf-8 -*-
"""
hazard_monitor.py - זיהוי סכנה ברקע מתוך מקטעי הקול שהמאזין הקולי כבר קולט (voice_trigger_module).

- לא פותח את המיקרופון בפעם השנייה: מקבל את אותם מקטעים (VAD - רק כשיש קול), ומריץ עליהם את audio_intel
  בתהליכון נפרד. תור באורך 1: אם הניתוח עסוק - המקטע מדולג (אסור לעכב את זיהוי מילות הקוד).
- זמין רק כשהמאזין הקולי פעיל. כשהוא כבוי - אין זיהוי ברקע (status() אומר זאת במפורש).
- אין שמירת אודיו. רק מטא-דאטה של הזיהוי עוברת ל-hazard_alerts.
- תוצאה -> AlertManager -> on_alert(kind, alert) לממשק, או רישום בלבד (חלונות כבויים / מצב לא מתאים).
- אירוע חדש/מוחמר בחומרה בינונית ומעלה -> גם on_checkin(category, confidence, severity): בדיקת "הכל בסדר?"
  שקטה (wellness_check.on_audio). לא תלוי בהעדפת החלונות; ההחלטה וההגבלות - ב-WellnessMonitor.
"""
import queue
import threading
import time

import hazard_alerts as HA

MIN_SECONDS = 0.5
MAX_SECONDS = 6.0
WINDOW_S = 1.5


def load_sequence_rule():
    """כלל "רצף צעקות" (research_tools/shout_sequence.py). קיים רק אם עמד בקריטריון; אחרת None."""
    import json
    import os
    import config
    base = getattr(config, "BASE_DIR", os.path.dirname(os.path.abspath(__file__)))
    p = os.path.join(base, "models", "shout_sequence.json")
    try:
        with open(p, encoding="utf-8") as fh:
            r = json.load(fh)
        return r if {"k", "t_low", "s_low", "span_s"} <= set(r) else None
    except (OSError, ValueError):
        return None


class HazardMonitor:
    def __init__(self, username, can_show=lambda: True, on_alert=None, analyze=None, prefs_fn=None,
                 on_checkin=None):
        self.username = username
        self.can_show = can_show                 # () -> (bool, סיבה) - מצב המנוע (SOS/שקט/כיבוי מדומה)
        self.on_alert = on_alert or (lambda kind, alert: None)
        self.on_checkin = on_checkin             # (category, confidence, severity) -> "הכל בסדר?" שקט
        self.prefs_fn = prefs_fn or (lambda: HA.load_prefs(username))
        self._analyze = analyze
        self.manager = HA.AlertManager()
        self._q = queue.Queue(maxsize=1)
        self._stop = threading.Event()
        self._thread = None
        self.stats = {"chunks": 0, "skipped_busy": 0, "analyzed": 0, "detections": 0}
        self.sequence_rule = load_sequence_rule()
        self._soft = []                          # (זמן, האם "כמעט-צעקה") לחלונות האחרונים

    # ------------------------------------------------------------ קלט
    def feed(self, audio_data):
        """נקרא מתהליכון המאזין. לא חוסם."""
        self.stats["chunks"] += 1
        try:
            self._q.put_nowait(audio_data)
        except queue.Full:
            self.stats["skipped_busy"] += 1

    def start(self):
        if self._thread and self._thread.is_alive():
            return
        self._stop.clear()
        self._thread = threading.Thread(target=self._loop, daemon=True)
        self._thread.start()

    def stop(self):
        self._stop.set()

    def running(self):
        return bool(self._thread and self._thread.is_alive() and not self._stop.is_set())

    # ------------------------------------------------------------ עיבוד
    def _loop(self):
        while not self._stop.is_set():
            try:
                item = self._q.get(timeout=0.5)
            except queue.Empty:
                continue
            try:
                self.process(item)
            except Exception:  # noqa: BLE001 - כשל בניתוח לא מפיל את המאזין
                pass

    def _run_analyze(self, x, sr):
        if self._analyze is not None:
            return self._analyze(x, sr)
        import audio_intel
        return audio_intel.analyze(x, sr)

    def process(self, audio_data, now=None):
        """מקטע אחד -> אפס או יותר החלטות. מחזיר רשימת (kind, alert) לבדיקות."""
        import speech_local
        x, sr = speech_local.audio_data_to_float(audio_data)
        if len(x) < MIN_SECONDS * sr:
            return []
        x = x[-int(MAX_SECONDS * sr):]
        # חלונות של 1.5 ש' (כמו במדידה): כל חלון מנותח לבד; הדו"ח החזק קובע, וכל חלון נספר לכלל הרצף
        n = int(WINDOW_S * sr)
        wins = [x[i:i + n] for i in range(0, len(x), n)]
        if len(wins) > 1 and len(wins[-1]) < n // 2:
            wins.pop()
        now = time.time() if now is None else now
        reps = []
        for j, w in enumerate(wins):
            r = self._run_analyze(w, sr)
            self.stats["analyzed"] += 1
            if not r or (r.get("quality") or {}).get("status") == "unavailable":
                continue
            reps.append(r)
            self._note_soft(r, now - (len(wins) - 1 - j) * WINDOW_S)
        if not reps:
            return []
        rep = max(reps, key=lambda r: (len(r.get("events") or []), bool((r.get("distress") or {}).get("detected"))))
        rep = dict(rep, events=_merge_events(reps))
        if any((r.get("distress") or {}).get("detected") for r in reps):
            rep["distress"] = max(((r.get("distress") or {}) for r in reps), key=lambda d: d.get("score") or -1e9)
        dets = []
        for e in rep.get("events") or []:
            if HA.SEVERITY_RANK.get(e.get("severity_prior"), 0) < HA.SEVERITY_RANK["low"]:
                continue                                   # "מידע" (סירנה) - לא מקפיץ חלון
            dets.append({"category": e["category"], "severity": e["severity_prior"],
                         "confidence": float(e.get("detection_confidence") or 0.0), "label_he": e.get("label_he"),
                         "explanation": _explain(e),
                         "meta": {"score": e.get("score"), "threshold": e.get("threshold"), "model": e.get("model"),
                                  "model_version": rep.get("model_version"),
                                  "quality": (rep.get("quality") or {}).get("status"),
                                  "near_threshold": bool(e.get("near_threshold"))}})
        d = rep.get("distress") or {}
        if d.get("detected"):
            dets.append({"category": "distress_voice", "severity": "medium",
                         "confidence": float(d.get("probability") or 0.0), "label_he": "קול מצוקה (צרחה / צעקה / בכי)",
                         "explanation": "צליל שדומה לצרחה, צעקה או בכי. צעקות שמחה ומשחק נשמעות דומה.",
                         "meta": {"score": d.get("score"), "model_version": rep.get("model_version")}})
        if not d.get("detected") and self._sequence_fired(now):
            k = self.sequence_rule["k"]
            dets.append({"category": "distress_voice", "severity": "medium", "confidence": self._seq_conf,
                         "label_he": "צעקות חוזרות",
                         "explanation": f"{k} קטעי קול דמויי צעקה בתוך שניות ספורות. צעקות שמחה ומשחק נשמעות דומה.",
                         "meta": {"rule": self.sequence_rule.get("version"), "model_version": rep.get("model_version")}})
        out = []
        prefs = self.prefs_fn()
        for det in dets:
            self.stats["detections"] += 1
            kind, alert = self.manager.decide(det)
            if alert is None:
                continue                                    # שקט אחרי תגובה / הגבלת קצב - לא נרשם שוב
            show, why = True, None
            if not prefs.get("popups", True):
                show, why = False, "popups_disabled"
            elif not HA.severity_allowed(alert["severity"], prefs):
                show, why = False, "below_min_severity"
            else:
                ok, reason = self.can_show()
                if not ok:
                    show, why = False, reason
            if kind in ("new", "update"):
                try:
                    HA.record_alert(self.username, alert, shown=show, reason_not_shown=why)
                except Exception:  # noqa: BLE001
                    pass
                if show:
                    self.on_alert(kind, alert)
                if self.on_checkin and HA.SEVERITY_RANK.get(alert["severity"], 0) >= HA.SEVERITY_RANK["medium"]:
                    try:
                        self.on_checkin(alert["category"], float(alert.get("confidence") or 0.0), alert["severity"])
                    except Exception:  # noqa: BLE001 - כשל בבדיקה לא מפיל את הזיהוי
                        pass
            out.append((kind, alert, show, why))
        return out

    def _note_soft(self, rep, ts):
        rule = self.sequence_rule
        if not rule:
            return
        d = (rep.get("distress") or {}).get("score")
        s = (rep.get("category_scores") or {}).get("scream")
        hit = (d is not None and d >= rule["t_low"]) or (s is not None and s >= rule["s_low"])
        prob = float((rep.get("distress") or {}).get("probability") or 0.0)
        self._soft.append((ts, bool(hit), prob))
        self._soft = [e for e in self._soft if ts - e[0] <= rule["span_s"] * 2][-6:]

    def _sequence_fired(self, now):
        rule = self.sequence_rule
        if not rule:
            return False
        hits = [e for e in self._soft if e[1] and now - e[0] <= rule["span_s"] * 2]
        if len(hits) < rule["k"]:
            return False
        self._seq_conf = float(sorted(h[2] for h in hits)[len(hits) // 2])
        self._soft = []                          # אותו רצף לא נספר פעמיים
        return True

    def status(self, listener_active):
        if not listener_active:
            return "הזיהוי ברקע לא פעיל: הוא עובד רק כשההאזנה הקולית למילות הקוד פועלת"
        return "הזיהוי ברקע פעיל (מקומי, בלי שמירת אודיו)"


def _merge_events(reps):
    best = {}
    for r in reps:
        for e in r.get("events") or []:
            if e["category"] not in best or (e.get("margin") or 0) > (best[e["category"]].get("margin") or 0):
                best[e["category"]] = e
    return list(best.values())


def _explain(e):
    base = {"gunshot": "צליל שדומה לירי", "explosion": "צליל שדומה לפיצוץ", "glass_break": "צליל של שבירת זכוכית",
            "alarm": "צליל של אזעקה", "scream": "צליל שדומה לצרחה", "impact": "חבטה חזקה",
            "fireworks": "צליל שדומה לזיקוקים", "siren": "סירנה"}.get(e["category"], e.get("label_he") or "")
    note = {"gunshot": "זיקוקים ותופים יכולים להישמע דומה", "explosion": "זיקוקים ורעם יכולים להישמע דומה",
            "alarm": "צופר רכב לפעמים מזוהה כאזעקה", "scream": "צעקות שמחה ומשחק נשמעות דומה"}.get(e["category"])
    near = " (קרוב לסף - לא ודאי)" if e.get("near_threshold") else ""
    return base + near + (f". {note}" if note else "")
