# -*- coding: utf-8 -*-
"""
wellness_check.py - "הכל בסדר?": המערכת שואלת אחרי אירוע חשוד, ופועלת אם אין תשובה.

טריגרים:
- נפילה / מכה חזקה (חיישן תאוצה בטלפון/שעון - sensor_module, דרך engine.report_sensor_signal)
- עצירה פתאומית: תנועה מהירה (ריצה/רכב) ואז עמידה במקום - לפי רצף מיקומים (detect_abrupt_stop)
- קול חשוד (hazard_monitor -> engine -> on_audio): אירוע קולי בחומרה בינונית ומעלה (שבירה / אזעקה / צרחה /
  ירי / פיצוץ) או קול מצוקה. בדיקה *שקטה* (רטט, בלי צפצופים) - הקול לבד לא מספיק לקריאת חירום
  (research/hazard_v3_freesound.md: צרחת פחד וצרחת שמחה לא נפרדות). אין תשובה -> engine.trigger *בלי* force_panic:
  ספירה לאחור עם ביטול + הערכת הסיכון הרגילה (risk_module) - לא SOS מיידי. "מידע"/"נמוכה" (סירנה, זיקוקים,
  חבטה) לא שואלים בכלל. הגבלת קצב: שאלה קולית אחת לכל AUDIO_MIN_INTERVAL_SECONDS.
- אין קליטה: הטלפון בלי חיבור יותר מ-SIGNAL_LOSS_SECONDS בזמן ליווי/טיימר בטיחות פעיל.
  במצב כזה השרת לא יכול לשאול - לכן השאלה והתגובה קורות *במכשיר עצמו* (סירנה מקומית, SOS שנשמר
  ויישלח כשהקליטה תחזור; בטלפון - גם SMS ישיר לאנשי הקשר).

התנהגות:
- שאלה "הכל בסדר?" עם ספירה לאחור (CHECKIN_SECONDS). "אני בסדר" -> שקט COOLDOWN_SECONDS.
  "אני צריך/ה עזרה" או אין תשובה -> SOS (כמו לחיצה על הכפתור).
- לא שואלים כשכבר יש אירוע פעיל, ולא במעקב שקט (שם אסור שיופיע משהו על המסך).
"""

import math
import threading
import time

CHECKIN_SECONDS = 45
COOLDOWN_SECONDS = 5 * 60
SIGNAL_LOSS_SECONDS = 5 * 60
SENSOR_TRIGGERS = {"fall": 0.7, "impact": 0.8, "abrupt_stop": 0.7}
FAST_MPS = 4.0          # ~14 קמ"ש: ריצה או רכב
STILL_MPS = 0.5
STILL_SECONDS = 20
REASONS_HE = {"fall": "זוהתה נפילה", "impact": "זוהתה מכה חזקה", "abrupt_stop": "עצירה פתאומית",
              "signal_loss": "אין קליטה כבר כמה דקות"}
# קול: רק חומרה בינונית ומעלה (audio_intel severity_prior). info/low - לעולם לא שואלים.
AUDIO_SEVERITIES = ("medium", "high")
AUDIO_MIN_INTERVAL_SECONDS = 2 * 60     # שאלה קולית אחת לכל 2 דק' - חלונות חוזרים של אותו צליל לא מציפים
AUDIO_PREFIX = "audio:"
AUDIO_REASONS_HE = {"distress_voice": "נשמע קול מצוקה", "scream": "נשמעה צרחה", "glass_break": "נשמעה שבירת זכוכית",
                    "alarm": "נשמעה אזעקה", "gunshot": "נשמע צליל שדומה לירי", "explosion": "נשמע צליל שדומה לפיצוץ"}


def reason_text(reason):
    if reason.startswith(AUDIO_PREFIX):
        return AUDIO_REASONS_HE.get(reason[len(AUDIO_PREFIX):], "נשמע צליל חשוד")
    return REASONS_HE.get(reason, reason)


def is_audio_reason(reason):
    return bool(reason) and reason.startswith(AUDIO_PREFIX)


def _speed(a, b):
    dt = b[0] - a[0]
    if dt <= 0:
        return 0.0
    la1, lo1, la2, lo2 = map(math.radians, (a[1], a[2], b[1], b[2]))
    h = math.sin((la2 - la1) / 2) ** 2 + math.cos(la1) * math.cos(la2) * math.sin((lo2 - lo1) / 2) ** 2
    return 2 * 6371000 * math.asin(math.sqrt(h)) / dt


def detect_abrupt_stop(fixes, fast=FAST_MPS, still=STILL_MPS, still_seconds=STILL_SECONDS, window=60):
    """fixes: [(t, lat, lon)] ממוין. True אם הייתה תנועה מהירה ואחריה עמידה של still_seconds לפחות,
    והמעבר קרה תוך window שניות (עצירה *פתאומית*, לא האטה הדרגתית לרמזור)."""
    if len(fixes) < 3:
        return False
    speeds = [(fixes[i + 1][0], _speed(fixes[i], fixes[i + 1])) for i in range(len(fixes) - 1)]
    last_fast = max((t for t, v in speeds if v >= fast), default=None)
    if last_fast is None:
        return False
    after = [(t, v) for t, v in speeds if t > last_fast]
    if not after or any(v > still for _, v in after):
        return False
    still_from = after[0][0]
    return fixes[-1][0] - still_from >= still_seconds and still_from - last_fast <= window


class WellnessMonitor:
    def __init__(self, engine, ask=None, clock=time.time, checkin_seconds=CHECKIN_SECONDS):
        """ask(reason_text, deadline, answer_fn) - מציג שאלה בממשק. answer_fn(ok: bool)."""
        self.engine, self.ask, self.clock = engine, ask, clock
        self.checkin_seconds = checkin_seconds
        self.pending = None            # {"reason", "deadline"}
        self.quiet_until = 0.0
        self.fixes = []
        self.offline_since = None
        self.audio_last = None         # זמן השאלה הקולית האחרונה (הגבלת קצב)
        self._lock = threading.RLock()
        self._timer = None

    # ------------------------------------------------------------ טריגרים
    def on_sensor(self, signal, confidence):
        thr = SENSOR_TRIGGERS.get(signal)
        if thr is not None and confidence >= thr:
            self.start_checkin(signal)

    def on_audio(self, category, confidence=0.0, severity="medium"):
        """זיהוי קולי (hazard_monitor). רק medium/high -> בדיקה שקטה. מחזיר True אם נפתחה שאלה."""
        if severity not in AUDIO_SEVERITIES:
            return False
        now = self.clock()
        with self._lock:
            if self.audio_last is not None and now - self.audio_last < AUDIO_MIN_INTERVAL_SECONDS:
                return False
        started = self.start_checkin(AUDIO_PREFIX + str(category), silent=True,
                                     meta={"confidence": float(confidence or 0.0), "severity": severity})
        if started:
            with self._lock:
                self.audio_last = now
        return started

    def dismiss_audio(self):
        """המשתמש/ת הגיב/ה לחלון הסכנה הקולי (כל תגובה מוכיחה שהוא/היא ערני/ת) - סוגר שאלה קולית פתוחה."""
        with self._lock:
            audio = bool(self.pending) and is_audio_reason(self.pending["reason"])
        if audio:
            self.answer(True)
        return audio

    def on_location(self, t, lat, lon):
        with self._lock:
            self.fixes = [f for f in self.fixes if t - f[0] <= 120] + [(t, lat, lon)]
            fire = detect_abrupt_stop(self.fixes)
            if fire:
                self.fixes = self.fixes[-1:]          # לא לשאול שוב על אותה עצירה
        if fire:
            self.start_checkin("abrupt_stop")

    def on_connectivity(self, online, watching):
        """watching: האם יש ליווי/טיימר בטיחות פעיל (רק אז היעדר קליטה מדאיג)."""
        now = self.clock()
        with self._lock:
            if online or not watching:
                self.offline_since = None
                return
            if self.offline_since is None:
                self.offline_since = now
                return
            fire = now - self.offline_since >= SIGNAL_LOSS_SECONDS
            if fire:
                self.offline_since = now               # שאלה אחת לכל חלון
        if fire:
            self.start_checkin("signal_loss")

    # ------------------------------------------------------------ שאלה
    def _engine_busy(self):
        st = getattr(getattr(self.engine, "state", None), "name", "IDLE")
        return st not in ("IDLE", "FEEDBACK")

    def start_checkin(self, reason, silent=False, meta=None):
        """silent=True: רטט בלבד (בלי צפצופים) - הממשק קורא pending["silent"]."""
        now = self.clock()
        with self._lock:
            if self.pending or now < self.quiet_until or self._engine_busy():
                return False
            self.pending = {"reason": reason, "deadline": now + self.checkin_seconds, "silent": bool(silent),
                            "meta": dict(meta or {})}
            deadline = self.pending["deadline"]
        self._log(f"❓ {reason_text(reason)} - שואל 'הכל בסדר?' ({self.checkin_seconds} שנ')"
                  + (" - בדיקה שקטה" if silent else ""))
        if self.ask:
            self.ask(reason_text(reason), deadline, self.answer)
        self._timer = threading.Timer(self.checkin_seconds, self._expire)
        self._timer.daemon = True
        self._timer.start()
        return True

    def answer(self, ok):
        with self._lock:
            if not self.pending:
                return
            reason = self.pending["reason"]
            self.pending = None
            if self._timer:
                self._timer.cancel()
            if ok:
                self.quiet_until = self.clock() + COOLDOWN_SECONDS
        if ok:
            self._log("✅ המשתמש/ת אישר/ה שהכל בסדר")
        else:
            self._escalate(reason, "המשתמש/ת ביקש/ה עזרה")

    def _expire(self):
        with self._lock:
            if not self.pending:
                return
            reason = self.pending["reason"]
            self.pending = None
        self._escalate(reason, "לא הייתה תשובה ל'הכל בסדר?'", confirmed=False)

    def _escalate(self, reason, why, confirmed=True):
        """confirmed: המשתמש/ת ביקש/ה עזרה במפורש -> SOS מיידי. קול + אין תשובה -> המסלול הרגיל
        (ספירה לאחור עם ביטול + הערכת סיכון), כי קול לבדו לעולם לא מפעיל SOS אוטומטי."""
        trig = getattr(self.engine, "trigger", None)
        if is_audio_reason(reason) and not confirmed:
            self._log(f"⚠️ {why} ({reason_text(reason)}) - פותח ספירה לאחור עם אפשרות ביטול")
            if trig:
                trig(force_panic=False, source="wellness_audio")
            return
        self._log(f"🚨 {why} ({reason_text(reason)}) - מפעיל SOS")
        if trig:
            trig(force_panic=True, source="wellness_check")

    def _log(self, text):
        log = getattr(self.engine, "log", None)
        if log:
            log(text)
