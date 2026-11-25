# -*- coding: utf-8 -*-
"""
engine.py
LifeGuardEngine - מכונת המצבים המרכזית שמנהלת את כל זרימת האירוע:
IDLE -> ASSESSING -> COUNTDOWN -> ACTIVE_SOS -> FEEDBACK -> IDLE

זהו ה"מוח" - הוא לא יודע כלום על ה-UI, רק קורא ל-callbacks כדי לעדכן אותו.
כך אפשר בעתיד להחליף את ה-UI (Tkinter -> מובייל) בלי לגעת בלוגיקה.

מ-v3: המנוע פועל בהקשר של משתמש מחובר (username) - סיסמה ואנשי קשר נטענים
דרך auth_module (מוצפן), לא מ-config גלובלי יותר.
"""

import json
import os
import threading
import time
from enum import Enum, auto

import config
import auth_module
import audio_module
import camera_module
import location_module
import map_module
import risk_module
import sensor_module
import siren_module
import voice_trigger_module
import voice_warning_module
import alert_gateway
import incident_store
import connectivity_module
import storage


_RATING_LABELS = {"true_event": "אירוע אמת", "felt_danger": "תחושת סכנה", "false_alarm": "התראת שווא"}

_SOURCE_LABELS = {
    "button": "כפתור SOS", "hotkey": "קיצור מקלדת", "panic_button": "PANIC",
    "voice": "פקודה קולית", "safety_timer": "טיימר בטיחות שפג", "manual": "הפעלה ידנית",
    "duress": "ביטוי כפייה", "silent_voice": "ביטוי אזעקה שקטה",
    "wellness_check": "אין תשובה ל'הכל בסדר?' (נפילה / עצירה פתאומית / אין קליטה)",
    "wellness_audio": "אין תשובה ל'הכל בסדר?' אחרי קול חשוד (ספירה עם ביטול - קול לבד אינו SOS)",
}


def _escort_loc(loc):
    """מיקום לליווי בשרת - רק קואורדינטות אמיתיות; IP מסומן כמשוער ולעולם לא כ-GPS."""
    if not loc or not loc.get("available") or loc.get("lat") is None:
        return None
    return {"lat": loc["lat"], "lon": loc["lon"], "is_precise": bool(loc.get("is_precise")),
            "source": loc.get("source")}



def _manual_confidence(username, trigger):
    try:
        import risk_feedback
        return risk_feedback.confidence({}, trigger=trigger, username=username)
    except Exception:  # noqa: BLE001
        return None

class State(Enum):
    IDLE = auto()
    ASSESSING = auto()
    COUNTDOWN = auto()
    ACTIVE_SOS = auto()
    FEEDBACK = auto()
    SILENT_TRACKING = auto()  # קוד מצוקה שקט הופעל - כלפי חוץ נראה בדיוק כמו IDLE!


class LifeGuardEngine:
    def __init__(self, username, on_state_change=None, on_log=None,
                 on_location_update=None, on_route_update=None,
                 on_photo_captured=None, on_live_risk_update=None,
                 on_safety_timer_tick=None, on_delivery_update=None, gateway=None):
        self.username = username
        # כל ההתראות יוצאות דרך שרת LifeGuard בלבד (alert_gateway). אין Telegram/WhatsApp/SMS/אימייל.
        self.gateway = gateway or alert_gateway.AlertGateway(username)
        self.gateway.on_status = self._on_gateway_status
        # on_delivery_update(status_dict) - מצב שליחה *אמיתי* לאנשי הקשר (ראה _delivery_status)
        self.on_delivery_update = on_delivery_update or (lambda status: None)
        # נעילה למעברי מצב: מונעת שני טריגרים בו-זמניים (קיצור מקלדת + קול + כפתור) שיוצרים
        # שני אירועים כפולים או דורסים את current_event אחד של השני.
        self._state_lock = threading.RLock()
        self._outbox_stop = threading.Event()
        self._delivery = None
        self._storage_warning_shown = False
        self._pending_silent_source = None
        self.countdown_deadline = None
        self.state = State.IDLE
        self.on_state_change = on_state_change or (lambda s: None)
        self.on_log = on_log or (lambda msg: None)
        self.on_location_update = on_location_update or (lambda loc: None)
        self.on_route_update = on_route_update or (lambda route_info: None)
        self.on_photo_captured = on_photo_captured or (lambda path, kind: None)
        self.on_live_risk_update = on_live_risk_update or (lambda score, level: None)
        # on_safety_timer_tick(remaining_seconds|None, is_warning) - None = הטיימר לא פעיל
        self.on_safety_timer_tick = on_safety_timer_tick or (lambda remaining, is_warning: None)
        self.on_fake_call = lambda linked=False: None         # main.py מחבר את זה למתזמן השיחה המזויפת (fake_call.py)

        self._countdown_thread = None
        self._siren_stop = threading.Event()
        self._audio_stop = threading.Event()
        self._gps_stop = threading.Event()
        self._manual_location = None
        self._camera_stop = threading.Event()
        self._live_monitor_stop = threading.Event()
        self._voice_warning_stop = threading.Event()          # אזהרה קולית - קשורה לאירוע SOS
        self._standalone_voice_warning_stop = threading.Event()  # אזהרה קולית - מצב עצמאי ידני
        self._safety_timer_stop = threading.Event()             # טיימר בטיחות ("ליווי הביתה")
        self._threads = []

        self.current_event = None  # דיקט עם פרטי האירוע הנוכחי
        self._last_trigger_time = None  # לזיהוי "retrigger מהיר" (סימן לדחיפות אמיתית)
        self._voice_listener = None
        self._safety_timer_deadline = None   # timestamp שבו הטיימר נגמר (None = לא פעיל)
        self._safety_timer_silent = False    # האם בתום הטיימר להפעיל אזעקה שקטה במקום רועשת
        self._safety_timer_destination = ""  # תיאור חופשי ("הביתה", "לרכב") - לשידור לאנשי קשר
        self._escort_id = None               # הליווי המקביל בשרת (נאכף שם גם אם המחשב כבה)
        self._escort_pending_action = None   # הגעה/ביטול שנבחרו לפני שהשרת סיים ליצור את הליווי
        self._escort_lock = threading.RLock()
        # "הכל בסדר?" אחרי נפילה / עצירה פתאומית / אין קליטה (wellness_check.py). הממשק מחבר ask.
        import wellness_check
        self.wellness = wellness_check.WellnessMonitor(self)
        # התראות סכנה אינטראקטיביות (hazard_alerts / hazard_monitor): הזיהוי רק מציע - לעולם לא SOS לבד
        import hazard_monitor
        self.on_hazard_alert = lambda kind, alert: None      # main.py מחבר לחלון ההתראה
        self.hazard_monitor = hazard_monitor.HazardMonitor(
            self.username, can_show=self._hazard_can_show,
            on_alert=lambda kind, alert: self.on_hazard_alert(kind, alert),
            on_checkin=self._audio_checkin)
        self._escort_for_incident = None     # ליווי שהטיימר שלו פג - לקישור לאירוע שנפתח

        self._recover_interrupted_incidents()

    @property
    def vault(self):
        """כספת ראיות (evidence_vault.py): תמונות SOS מוצפנות, לא מטושטשות; טשטוש רק בהתראת שווא."""
        import evidence_vault
        return evidence_vault.EvidenceVault(os.path.join(config.DATA_DIR, "evidence", self.username or "_"))

    # ---------- תיעוד אירוע מובנה (Incident Timeline) ----------
    def _recover_interrupted_incidents(self):
        """אירועים שנשארו 'פתוחים' מהרצה קודמת (קריסה/כיבוי מחשב) נסגרים ומסומנים ככאלה."""
        try:
            for inc in incident_store.list_incidents(self.username, limit=50):
                if inc.get("ended_at") is None:
                    incident_store.add_event(self.username, inc["id"], "system",
                                             "האירוע נקטע: התוכנה נסגרה/קרסה לפני סיום מסודר")
                    incident_store.update_incident(self.username, inc["id"], ended_at=time.time(),
                                                   outcome="interrupted")
                    incident_store.expire_outbox_for_incident(self.username, inc["id"])
            removed = incident_store.purge_expired(self.username)
            if removed:
                self.log(f"🧹 נמחקו {removed} אירועים ישנים לפי מדיניות השמירה שלך")
        except Exception as exc:
            self._storage_failure(exc)

    def _storage_failure(self, exc):
        # אחסון ההיסטוריה אינו רכיב קריטי - כשל בו לעולם לא עוצר SOS. מדווחים פעם אחת.
        if not self._storage_warning_shown:
            self._storage_warning_shown = True
            try:
                with open(os.path.join(config.LOG_DIR, "engine.log"), "a", encoding="utf-8") as f:
                    f.write(f"[{self.username}] [{time.strftime('%H:%M:%S')}] storage error: {exc}\n")
            except Exception:
                pass
            if self.state != State.SILENT_TRACKING:
                self.on_log(f"[{time.strftime('%H:%M:%S')}] ⚠️ תיעוד היסטוריית האירוע נכשל ({exc}) - "
                            "פעולות החירום ממשיכות כרגיל")

    def _new_incident(self, kind, trigger_source, confidential=False):
        """יוצר current_event + רשומת היסטוריה. נקרא תחת _state_lock."""
        now = time.time()
        event_id = f"lg-{self.username}-{int(now * 1000)}"
        self.current_event = {
            "event_id": event_id, "start_time": now, "audio_files": [], "locations": [],
            "photos": [], "risk_assessment": None, "safe_route": None,
            "kind": kind, "trigger_source": trigger_source,
        }
        self._delivery = None
        self._manual_location = None   # מיקום שהוזן ידנית באירוע הזה (מתאפס באירוע חדש)
        try:
            incident_store.create_incident(self.username, kind, trigger_source,
                                           incident_id=event_id, started_at=now,
                                           confidential=confidential)
        except Exception as exc:
            self._storage_failure(exc)
        return self.current_event

    def _record(self, category, message, provenance=incident_store.PROVENANCE_AUTOMATIC, data=None):
        event = self.current_event
        if not event:
            return
        try:
            incident_store.add_event(self.username, event["event_id"], category, message,
                                     provenance=provenance, data=data)
        except Exception as exc:
            self._storage_failure(exc)

    def _close_incident(self, outcome):
        event = self.current_event
        if not event:
            return
        event["outcome"] = outcome
        event.setdefault("end_time", time.time())
        self._outbox_stop.set()
        try:
            incident_store.update_incident(self.username, event["event_id"],
                                           ended_at=event["end_time"], outcome=outcome)
            expired = incident_store.expire_outbox_for_incident(self.username, event["event_id"])
            if expired:
                self._record("delivery", f"{expired} התראות שלא נשלחו בוטלו עם סיום האירוע "
                                         "(לא נשלחות באיחור)")
        except Exception as exc:
            self._storage_failure(exc)

    def describe_emergency_type(self, emergency_type, label):
        """המשתמש בחר סוג חירום במסך ה-SOS - מתועד כפעולה מאושרת (לא משפיע על השידור)."""
        if self.current_event is not None:
            self.current_event["emergency_type"] = emergency_type
            self.gateway.set_emergency_type(self.current_event["event_id"], emergency_type)
            self._record("user_action", f"המשתמש סימן סוג חירום: {label}",
                         incident_store.PROVENANCE_CONFIRMED, {"emergency_type": emergency_type})

    # ---------- ניהול מצב ----------
    def _set_state(self, new_state: State):
        previous_state = self.state
        self.state = new_state
        if new_state == State.SILENT_TRACKING or previous_state == State.SILENT_TRACKING:
            # קריטי: גם הכניסה למעקב שקט וגם היציאה ממנו (חזרה ל-IDLE) לא נכתבות ליומן
            # הגלוי - אם מישהו צפה במסך בזמן שהמשתמש האמיתי הזין את קוד המצוקה בשנית
            # (כדי לעצור את המעקב), אסור שהמעבר "בחזרה ל-IDLE" ייראה שונה מכל מעבר רגיל אחר.
            self._log_silent(f"מצב מערכת (מוסתר): {previous_state.name} -> {new_state.name}")
        else:
            self.log(f"מצב מערכת: {new_state.name}")
            if self.current_event is not None and new_state != State.IDLE:
                self._record("state", f"מצב מערכת: {previous_state.name} -> {new_state.name}")
        self.on_state_change(new_state)

    def log(self, message):
        """
        קריטי: אם המערכת נמצאת כרגע במעקב שקט (SILENT_TRACKING), *כל* קריאה ל-log() מנותבת
        אוטומטית לתיעוד הפרטי בלבד - כי thread-ים ברקע (הקלטה/מצלמה/GPS) ממשיכים לרוץ
        ולקרוא ל-log() בלי לדעת/לבדוק את המצב בעצמם (למשל "🎙️ הוקלט צ'אנק" או "👤 זוהו פנים").
        בלי ההגנה הזו כאן, במקום אחד, כל אחד מהם היה יכול לחשוף את המעקב השקט על המסך.
        """
        if self.state == State.SILENT_TRACKING:
            self._log_silent(message)
            return
        timestamp = time.strftime("%H:%M:%S")
        line = f"[{timestamp}] {message}"
        self.on_log(line)
        try:
            with open(os.path.join(config.LOG_DIR, "engine.log"), "a", encoding="utf-8") as f:
                f.write(f"[{self.username}] {line}\n")
        except Exception:
            pass

    def _log_silent(self, message):
        """
        כמו log(), אבל *לא* קורא ל-on_log (לא מוצג במסך בשום מקרה).
        בשימוש בלעדי לפרטי קוד המצוקה השקט, שאסור שיופיעו על המסך תחת שום נסיבות.

        תיקון אבטחה: בעבר השורות נכתבו כטקסט גלוי ל-engine.log עם התג [CONFIDENTIAL] - כל מי
        שפתח את קובץ הלוג (כולל התוקף בתרחיש כפייה) ראה שהמעקב השקט פעיל. כעת הן נרשמות רק
        בציר הזמן של האירוע (מוצפן ב-DPAPI, ונגיש רק אחרי הזנת סיסמת החשבון במסך ההיסטוריה).
        """
        self._record("system", message)

    # ---------- טריגר ----------
    def _finalize_pending_feedback(self):
        """
        באג קריטי שתוקן: אחרי סיום אירוע המצב נשאר FEEDBACK עד שהמשתמש מדרג. כל טריגר
        באותו זמן (כפתור/קיצור/קול/טיימר) *נבלע* ("אירוע כבר פעיל - מתעלם") - כלומר
        SOS חדש לא היה עובד אם חלון הדירוג לא נסגר. כעת: האירוע הקודם נשמר כ"לא דורג"
        והטריגר החדש ממשיך מיד.
        """
        if self.state != State.FEEDBACK:
            return
        if self.current_event is not None:
            self.current_event["rating"] = None
            self.current_event["username"] = self.username
            try:
                self._save_event_to_db(self.current_event)
            except Exception as exc:
                self._storage_failure(exc)
        self.current_event = None
        self.state = State.IDLE  # ללא callback - מיד נכנסים למצב חדש

    def trigger(self, force_panic=False, source="manual"):
        """
        נקרא כשמזוהה מילת הקוד / קיצור המקלדת / כפתור ידני.
        force_panic=True (כפתור/קיצור PANIC) -> מדלג לגמרי על הערכת סיכון וספירה, SOS מיידי.
        source: 'button' | 'hotkey' | 'panic_button' | 'voice' | 'safety_timer' | 'manual'
        """
        with self._state_lock:
            if self.state == State.FEEDBACK:
                self._finalize_pending_feedback()
            if self.state != State.IDLE:
                self.log("טריגר התקבל אך אירוע כבר פעיל - מתעלם (מניעת אירוע כפול)")
                return False
            # תופסים את המצב *לפני* שחרור הנעילה - טריגר שני במקביל יראה ASSESSING ויידחה.
            self.state = State.ASSESSING
            self._trigger_locked_body(force_panic, source)
        return True

    def _trigger_locked_body(self, force_panic, source):
        self.stop_live_monitor()  # לא מריצים ניטור-כיול וטריגר אמיתי במקביל
        self.stop_voice_warning_standalone()  # מצב הרתעה עצמאי מתבטל - ה-SOS ינהל את זה בעצמו אם רלוונטי
        # אם טיימר בטיחות היה פעיל - הוא מתייתר ברגע שיש אירוע אמיתי (בין אם הוא זה שהפעיל
        # אותו ובין אם המשתמש לחץ SOS בעצמו קודם). מנקים כדי שלא "יירה" שוב בהמשך.
        if self._safety_timer_deadline is not None:
            self._clear_safety_timer_state()
        # שימו לב: לא עוצרים כאן את start_voice_trigger בכוונה - ממשיך להאזין לביטוי האזעקה
        # השקטה גם תוך כדי ספירה/אירוע פעיל (ראה start_voice_trigger). כן עוצרים אותו לרגע
        # קצר בזמן ASSESSING בלבד, כדי לפנות את המיקרופון לזיהוי המילים המסוכנות של ההערכה עצמה.

        now = time.time()
        is_rapid_retrigger = bool(
            self._last_trigger_time and (now - self._last_trigger_time) < config.RAPID_RETRIGGER_WINDOW
        )
        self._last_trigger_time = now

        self._new_incident("SOS", source)
        user_initiated = source in ("button", "hotkey", "panic_button", "voice", "manual")
        self._record("user_action" if user_initiated else "system",
                     f"אירוע הופעל ({_SOURCE_LABELS.get(source, source)})"
                     + (" - PANIC ללא ספירה" if force_panic else ""),
                     incident_store.PROVENANCE_CONFIRMED if user_initiated else incident_store.PROVENANCE_AUTOMATIC,
                     {"source": source, "force_panic": bool(force_panic)})

        # מתחילים לחפש מיקום + מקום בטוח *מיד* עם הטריגר - לא ממתינים לסוף הספירה לאחור.
        # כך המפה כבר מוכנה גם אם המשתמש בסוף מבטל, וגם חוסך זמן יקר אם האירוע כן מופעל.
        threading.Thread(target=self._show_initial_location_and_route, daemon=True).start()

        if force_panic or not config.RISK_ASSESSMENT_ENABLED:
            reason = "עקיפת PANIC ידנית" if force_panic else "הערכת סיכון מושבתת בהגדרות"
            self.log(f"🆘 {reason} - מפעיל SOS מיידי ללא ספירה לאחור וללא אפשרות ביטול")
            self.current_event["risk_assessment"] = {
                "level": "HIGH", "score": None, "reasons": [reason],
                "noise_level": None, "keywords_found": [],
                "confidence": _manual_confidence(self.username, source),
            }
            self.state = State.IDLE  # _activate_sos קובע ACTIVE_SOS ומודיע לממשק
            self._activate_sos()
            return

        # SOS ידני (כפתור / קיצור): לא ממתינים להערכת ה-AI. הספירה (הגנה מלחיצה בטעות, עם ביטול בסיסמה)
        # מתחילה מיד, וההערכה רצה במקביל - היא רק מוסיפה מידע למגיבים, ובסכנה גבוהה מקצרת את הספירה.
        self.state = State.IDLE
        self.stop_voice_trigger()  # מפנים את המיקרופון לזיהוי המילים המסוכנות של ההערכה עצמה
        self._set_state(State.COUNTDOWN)
        self._countdown_thread = threading.Thread(target=self._run_countdown, args=(config.COUNTDOWN_SECONDS,),
                                                  daemon=True)
        self._countdown_thread.start()
        threading.Thread(target=self._run_risk_assessment, args=(is_rapid_retrigger,), daemon=True).start()

    def _run_risk_assessment(self, is_rapid_retrigger):
        self.log("🔍 מעריך רמת סכנה (קול + מילות מצוקה + חיישני תנועה זמינים)...")
        # המאזין הקולי נעצר רגע לפני כן; ממתינים (עד 3 שנ') שישחרר את המיקרופון, כדי שמדידת
        # הרעש לא תפתח זרם שמע מקביל לזרם שנסגר (סיכון קריסה ב-PortAudio).
        voice_trigger_module.wait_for_mic_release(3.0)
        # נלכדים לפני ההערכה - ביטול בזמנה מאפס את current_event
        incident_id = (self.current_event or {}).get("event_id")
        trigger_source = (self.current_event or {}).get("trigger_source")
        result = risk_module.assess_risk(
            is_rapid_retrigger=is_rapid_retrigger, log_callback=self.log,
            sensor_signals=sensor_module.get_recent_sensor_signals(config.SENSOR_EVIDENCE_WINDOW_SECONDS),
            username=self.username,
            # מיקום אחרון ידוע (מטמון, בלי פנייה לרשת): לילה לפי השמש במקום, תאורה לפי עמודי העירייה
            location=location_module.get_last_known(),
            trigger=trigger_source,
        )
        if self.current_event is not None:
            self.current_event["risk_assessment"] = result
        try:
            # פנקס הערכות (assessment_ledger.py): בלי אודיו/מיקום/מילים; התווית נגזרת אחר כך מהדירוג בלבד
            import assessment_ledger
            assessment_ledger.record(self.username, incident_id, result, trigger=trigger_source)
        except Exception as exc:  # noqa: BLE001 - תיעוד לעולם לא עוצר אירוע
            self._storage_failure(exc)

        reasons_text = ", ".join(result["reasons"]) if result["reasons"] else "לא זוהו גורמי סיכון נוספים"
        self.log(f"📊 רמת סכנה: {result['level']} (ניקוד {result['score']}) - {reasons_text}")
        self._record("system", f"הערכת סכנה היוריסטית: {result['level']} - {reasons_text}",
                     data={"level": result.get("level"), "score": result.get("score")})

        if self.state in (State.COUNTDOWN, State.ACTIVE_SOS) and self.current_event is not None:
            # SOS ידני שכבר רץ: ההערכה לא מעכבת. סכנה גבוהה -> לא מחכים לסוף הספירה; אם כבר הופעל -
            # ההערכה נשלחת לשרת כעדכון (המגיבים רואים אותה)
            with self._state_lock:
                if self.state == State.COUNTDOWN and result["level"] == "HIGH" and result.get("automatic_sos_eligible"):
                    self.log("🚨 זוהה שילוב של ראיות בלתי תלויות - מפעיל SOS מיידי")
                    self._activate_sos()
                elif self.state == State.ACTIVE_SOS:
                    self.gateway.update_risk(self.current_event["event_id"], result)
            self.start_voice_trigger()
            return
        if self.state != State.ASSESSING:
            return  # משהו אחר כבר שינה את המצב בינתיים (למשל כיבוי) - לא ממשיכים

        if result["level"] == "HIGH" and result.get("automatic_sos_eligible"):
            self.log("🚨 זוהה שילוב של ראיות בלתי תלויות - מפעיל SOS מיידי")
            self._activate_sos()
            self.start_voice_trigger()
        else:
            # LOW, MEDIUM וגם UNKNOWN אינם מדלגים על חלון תגובה: רעש בלבד או חוסר בנתונים
            # אינם הוכחה לחירום. PANIC/מילת הקוד הרועשת עדיין עוקפים זאת מיד.
            seconds = config.RISK_MEDIUM_COUNTDOWN_SECONDS if result["level"] == "MEDIUM" else config.COUNTDOWN_SECONDS
            self.log(f"⏱️ הערכה {result['level']} - נפתח חלון אימות של {seconds} שניות; SOS ידני/קולי עדיין מיידי")
            self._set_state(State.COUNTDOWN)
            self.start_voice_trigger()
            self._countdown_thread = threading.Thread(target=self._run_countdown, args=(seconds,), daemon=True)
            self._countdown_thread.start()

    def _run_countdown(self, seconds=None):
        seconds = int(seconds or config.COUNTDOWN_SECONDS)
        self.countdown_deadline = time.time() + seconds  # מסך ה-SOS מציג ספירה חיה לפי זה
        self.log(f"⏱️ ספירה לאחור {seconds} שניות - הזן סיסמת חשבון לביטול או השתמש/י ב-PANIC אם נדרשת עזרה מיידית")
        for remaining in range(seconds, 0, -1):
            if self.state != State.COUNTDOWN:
                return  # בוטל
            self.log(f"... {remaining}")
            time.sleep(1)
        with self._state_lock:
            if self.state == State.COUNTDOWN:
                self._activate_sos()

    def skip_countdown(self):
        """'שלח עכשיו' במסך הספירה - המשתמש מאשר שזה חירום אמיתי ואין טעם לחכות."""
        with self._state_lock:
            if self.state != State.COUNTDOWN:
                return False
            self._record("user_action", "המשתמש לחץ 'שלח עכשיו' - דילוג על הספירה",
                         incident_store.PROVENANCE_CONFIRMED)
            self._activate_sos()
            return True

    def cancel_with_password(self, password_entered):
        """סיסמת החשבון מבטלת; ביטוי כפייה מאמת לכאורה ביטול אך ממשיך בדיווח שקט."""
        if auth_module.verify_duress_phrase_typed(self.username, password_entered):
            self.activate_duress_mode(source="typed")
            return True
        if not auth_module.verify_password(self.username, password_entered):
            if self.state != State.SILENT_TRACKING:
                self.log("❌ סיסמה שגויה - האירוע ממשיך")
            return False

        if self.state == State.SILENT_TRACKING:
            return self.end_silent_tracking()
        if self.state in (State.ACTIVE_SOS, State.COUNTDOWN):
            # ביטול מאובטח (סיסמה) נרשם ביומן הביקורת - גם אם אין כרגע חיבור (תור מקומי)
            try:
                import privacy_sync
                privacy_sync.queue_audit(self.username, "false_alarm_cancelled",
                                         details={"stage": self.state.name.lower()},
                                         event_client_id=(self.current_event or {}).get("event_id"))
            except Exception:  # noqa: BLE001
                pass
        if self.state == State.ACTIVE_SOS:
            self._real_cancel_active()
            return True
        if self.state == State.COUNTDOWN:
            self._real_cancel_countdown()
            return True
        if self.state == State.ASSESSING:
            # מאפשר ביטול גם בזמן הערכת הסיכון, לפני שמופיע מסך הספירה.
            self.stop_voice_trigger()
            self._record("user_action", "האירוע בוטל בזמן הערכת הסכנה (סיסמה)",
                         incident_store.PROVENANCE_CONFIRMED)
            self._close_incident("cancelled_during_assessment")
            self._set_state(State.IDLE)
            self.current_event = None
            self.log("✅ הערכת הסיכון בוטלה באמצעות סיסמת החשבון")
            self.start_voice_trigger()
            return True
        return False

    # תאימות לקוד/תוספים ישנים שקראו לשיטה בשם הקודם.
    def cancel_with_pin(self, pin_entered):
        return self.cancel_with_password(pin_entered)

    def _real_cancel_active(self, via="password"):
        """עוצר SOS פעיל ומעדכן את אנשי הקשר שהאזעקה הופסקה - בלי להניח שהמשתמש בטוח."""
        self._record("user_action", f"אזעקה פעילה הופסקה ({'סיסמת חשבון' if via == 'password' else 'מילת ביטול קולית'})",
                     incident_store.PROVENANCE_CONFIRMED)
        self._stop_active_sos()
        # השרת מודיע לנמענים שהאזעקה בוטלה ("מומלץ לוודא שהמשתמש/ת בטוח/ה") ומבטל גישת מתנדבים
        self.gateway.close(self.current_event["event_id"], "cancelled")
        self._close_incident("stopped_by_user")
        self._set_state(State.FEEDBACK)

    def _real_cancel_countdown(self, via="password"):
        """ביטול אמיתי ומלא בזמן ספירה לאחור (התראת שווא)."""
        self._record("user_action", f"האירוע בוטל בזמן הספירה ({'סיסמה' if via == 'password' else 'מילת ביטול קולית'})"
                     " - לא נשלחה התראה", incident_store.PROVENANCE_CONFIRMED)
        self._close_incident("cancelled_during_countdown")
        self._set_state(State.IDLE)
        self.log("✅ האירוע בוטל בזמן (התראת שווא / קוד נכון)")
        self.current_event = None

    def _last_known_latlon(self):
        if self.current_event and self.current_event.get("locations"):
            for last in reversed(self.current_event["locations"]):
                if last.get("available") and last.get("is_precise") and last.get("lat") is not None and last.get("lon") is not None:
                    return last["lat"], last["lon"]
        return None

    def _go_silent(self, already_tracking):
        """
        המעבר בפועל למצב מעקב שקט - נקודת כניסה אחת ומשותפת לכל שלושת המסלולים:
        (1) הקלדת מילת הקוד השקטה בתוך מסך SOS/ספירה, (2) ביטוי קולי שקט (trigger_silent
        או תוך כדי אירוע פעיל), (3) קריאה ישירה מ-IDLE.
        already_tracking=True כשההקלטה/מצלמה/GPS כבר רצים (הגענו מ-ACTIVE_SOS, רק משתיקים
        את הסירנה); False כשצריך להתחיל אותם עכשיו (הגענו מ-IDLE/COUNTDOWN, שם עוד לא רצו).
        """
        # ההאזנה ממשיכה לרוץ (שליטה קולית מלאה חייבת להישאר במעקב שקט); מחליפים רק את יעד
        # התיעוד ל-_log_silent. בעבר המאזין נעצר ונפתח מחדש כאן - מה שגרם לקריסת PortAudio
        # (access violation) בדיוק ברגע הפעלת מצב כפייה.
        self._set_state(State.SILENT_TRACKING)
        self._retarget_voice_log()

        if already_tracking:
            self._siren_stop.set()  # רק משתיקים את מה שכבר רץ - שאר ה-threads ממשיכים כרגיל
        else:
            self._start_tracking_threads(include_siren=False, include_voice_warning=False)

        loc = next((item for item in reversed((self.current_event or {}).get("locations", []))
                    if item.get("available")), None)
        # אם האירוע כבר נפתח בשרת כגלוי (הגענו מ-ACTIVE_SOS) - הנמענים כבר הוזעקו; לא פותחים שני.
        self.gateway.open_incident(self.current_event["event_id"], mode="silent",
                                   emergency_type=(self.current_event or {}).get("emergency_type", "unknown"),
                                   severity="high", location=loc, profile=self._profile_for_responders(),
                                   log=self._log_silent, escort_id=self._take_escort_for_incident(),
                                   risk=(self.current_event or {}).get("risk_assessment"))
        self._record("state", "מעקב שקט פעיל: הקלטה, מצלמה ומיקום רצים ללא סירנה/מסך")

    def end_silent_tracking(self):
        """
        עוצר בפועל את כל המעקב השקט (המשתמש האמיתי מזין את סיסמת החשבון, כשהוא/היא
        כבר בטוח/ה) - ומעדכן את אנשי הקשר שהמצב הסתיים בשלום.
        """
        if self.state != State.SILENT_TRACKING:
            return False
        self._log_silent("ℹ️ אמצעי הביטול הופעל - המעקב השקט הופסק")

        if self.current_event is not None:
            self.gateway.close(self.current_event["event_id"], "resolved")
        self._audio_stop.set()
        self._gps_stop.set()
        self._camera_stop.set()
        self._voice_warning_stop.set()
        if self.current_event is not None:
            self._record("user_action", "המעקב השקט הופסק ע\"י בעל החשבון", incident_store.PROVENANCE_CONFIRMED)
            self.current_event["end_time"] = time.time()
            self.current_event["username"] = self.username
            self._close_incident("silent_tracking_stopped_by_account_owner")
            try:
                self._save_event_to_db(self.current_event)
            except Exception as exc:
                self._storage_failure(exc)

        threading.Thread(target=self._join_threads_background, args=(list(self._threads),), daemon=True).start()
        self._set_state(State.IDLE)
        # המאזין חוזר ל-log רגיל (גלוי) - בלי לפתוח מחדש את המיקרופון.
        self._retarget_voice_log()
        return True

    # ---------- שלב SOS פעיל ----------
    def _activate_sos(self):
        self._set_state(State.ACTIVE_SOS)
        self.log("🚨 אירוע SOS פעיל!")
        if not self.gateway.connected():   # כל הפעלה נרשמת; בלי חיבור - בתור המקומי עם זמן המכשיר
            try:
                import privacy_sync
                privacy_sync.queue_audit(self.username, "sos_activated_offline",
                                         details={"trigger": (self.current_event or {}).get("trigger_source")},
                                         event_client_id=(self.current_event or {}).get("event_id"))
            except Exception:  # noqa: BLE001
                pass
        self._start_tracking_threads(include_siren=True, include_voice_warning=True)
        # שידור טקסט ראשוני מיידי + מיקום חי + חיפוש מקום/מסלול בטוח (במקביל, לא חוסמים)
        threading.Thread(target=self._initial_broadcast, daemon=True).start()
        threading.Thread(target=self._find_safe_route, daemon=True).start()

    def _start_tracking_threads(self, include_siren, include_voice_warning):
        """
        מתחיל את שרשורי המעקב (הקלטה/מצלמה/GPS, ואופציונלית סירנה+אזהרה קולית) - משותף
        בין הפעלת SOS רגילה (include_siren=True) לבין הפעלה שקטה ישירה (include_siren=False,
        למשל דרך ביטוי קולי ייעודי - ראה trigger_silent) שבה אסור שיישמע/יוצג שום דבר.
        """
        self._siren_stop.clear()
        self._audio_stop.clear()
        self._gps_stop.clear()
        self._camera_stop.clear()
        self._voice_warning_stop.clear()
        self._threads = [
            threading.Thread(
                target=audio_module.record_loop,
                args=(self._audio_stop, config.AUDIO_DIR, config.AUDIO_CHUNK_SECONDS, self.log,
                      self._on_audio_chunk_recorded),
                daemon=True,
            ),
            threading.Thread(target=self._gps_loop, daemon=True),
            threading.Thread(
                target=camera_module.capture_loop,
                args=(self._camera_stop, config.PHOTOS_DIR, self._on_photo_captured, self.log),
                daemon=True,
            ),
        ]

        if include_siren:
            self._threads.append(threading.Thread(
                target=siren_module.play_siren, args=(self._siren_stop, self.log), daemon=True
            ))

        # אזהרה קולית מרתיעה - רק כשרמת הסיכון היא בינונית/גבוהה, ואף פעם לא במעקב שקט
        # (זה הרי בדיוק מה שאסור שיישמע!)
        risk_level = None
        if self.current_event is not None and self.current_event.get("risk_assessment"):
            risk_level = self.current_event["risk_assessment"].get("level")
        if include_voice_warning and risk_level in config.VOICE_WARNING_DANGEROUS_LEVELS:
            self._threads.append(threading.Thread(
                target=voice_warning_module.warning_loop, args=(self._voice_warning_stop, self.log), daemon=True
            ))
            self.log(f"📢 רמת סכנה {risk_level} - אזהרה קולית מרתיעה תופעל אוטומטית")

        for t in self._threads:
            t.start()

    def trigger_silent(self):
        """
        מפעיל מעקב שקט *ישירות* - בלי מסך SOS, בלי סירנה, בלי ספירה לאחור. נקרא כשנאמר
        ביטוי האזעקה השקטה הקולי (voice_trigger_module) מ-IDLE. קריטי: שום דבר כאן לא
        נכתב ליומן הגלוי - רק ל-_log_silent (דרך _go_silent).
        """
        with self._state_lock:
            if self.state == State.FEEDBACK:
                self._finalize_pending_feedback()
            if self.state != State.IDLE:
                return False
            self.state = State.ASSESSING  # תפיסת המצב (ללא callback - חייב להישאר בלתי נראה)
            try:
                return self._trigger_silent_locked()
            finally:
                if self.state == State.ASSESSING:
                    self.state = State.IDLE

    def _trigger_silent_locked(self, source="silent_voice"):
        self.stop_live_monitor()
        # טיימר בטיחות פעיל מתייתר (ראה הערה זהה ב-trigger). חשוב: _clear_safety_timer_state
        # לא כותב ליומן הגלוי, אז זה בטוח גם במסלול השקט.
        if self._safety_timer_deadline is not None:
            self._clear_safety_timer_state()

        now = time.time()
        self._last_trigger_time = now
        self._new_incident("SILENT_ALERT", self._pending_silent_source or source, confidential=True)
        self._pending_silent_source = None
        self.current_event["risk_assessment"] = {
            "level": "HIGH", "score": None, "reasons": ["הפעלה שקטה ישירה"],
            "noise_level": None, "keywords_found": [],
            "confidence": _manual_confidence(self.username, "silent_voice"),
        }
        self._log_silent("🤫 אזעקה שקטה הופעלה ישירות (ביטוי קולי) - ללא מסך/סירנה מלכתחילה")

        threading.Thread(target=self._show_initial_location_and_route, daemon=True).start()
        self._go_silent(already_tracking=False)
        return True

    def set_manual_location(self, text, resolver=None):
        """
        מיקום שהמשתמש/ת כתב/ה בזמן SOS (אין GPS). קדימות: GPS אמיתי > ידני > IP משוער.
        תמיד: הטקסט עצמו נשלח לאנשי הקשר כהודעה (תיאור כמו "קומה 3" שימושי גם בלי קואורדינטות).
        מחזיר את התוצאה (manual_location.resolve). חוסם (חיפוש כתובת) - לקרוא מ-thread.
        """
        import manual_location
        res = (resolver or manual_location.resolve)(text)
        ev = self.current_event
        if ev is None:
            return res
        eid = ev["event_id"]
        self._record("user_action", f"מיקום הוזן ידנית: {res.get('manual_text', '')}"
                     + (f" -> {res['lat']:.5f}, {res['lon']:.5f}" if res.get("available") else " (לא נמצאו קואורדינטות)"),
                     incident_store.PROVENANCE_CONFIRMED, {k: res.get(k) for k in ("lat", "lon", "source", "manual_text")})
        if res.get("available"):
            self._manual_location = res
            ev.setdefault("locations", []).append(res)
            self.gateway.update_location_now(eid, res)
            self.on_location_update(res)
            # מסלול למקום בטוח מהכתובת שהוזנה (עד עכשיו המסלול חושב רק פעם אחת בהפעלה, ורק מ-GPS)
            threading.Thread(target=self._find_safe_route_for_location, args=(res,), daemon=True).start()
        silent = ev.get("kind") == "SILENT_ALERT"
        self.gateway.send_message(eid, f"📍 המיקום שלי (כתבתי ידנית): {res.get('manual_text', '')}"
                                  + (f"\n{res.get('display')}" if res.get("available") and res.get("display")
                                     and res.get("display") != res.get("manual_text") else ""))
        if not silent:
            self.log("📍 המיקום שכתבת נשלח לאנשי הקשר" + ("" if res.get("available")
                                                          else " (כטקסט - לא נמצאו קואורדינטות לכתובת)"))
        return res

    def _effective_location(self, loc):
        """GPS אמיתי גובר תמיד; אחרת מיקום ידני (אם הוזן) עדיף על מיקום IP משוער."""
        manual = getattr(self, "_manual_location", None)
        if manual and not (loc.get("available") and loc.get("is_precise") and loc.get("source") != "manual"):
            return manual
        return loc

    def _gps_loop(self):
        """מעדכן מיקום. רק GNSS אמיתי נשלח כמיקום חי; IP נשאר מסומן כמשוער."""
        last_logged_source = None
        while not self._gps_stop.is_set():
            loc = self._effective_location(location_module.get_location(log_callback=self.log))
            if self.current_event is not None and loc.get("available"):
                self.current_event.setdefault("locations", []).append(loc)
            self._record_location(loc)
            self.on_location_update(loc)
            if loc.get("available"):
                self.log(f"📍 מיקום: {loc.get('city', '—')} | {loc.get('source', '?')} | {loc.get('accuracy', '?')}")
                if self.current_event is not None:
                    # מיקום חי לשרת (מסומן is_precise; IP נשלח כמשוער ולעולם לא כ-GPS)
                    self.gateway.update_location(self.current_event["event_id"], loc)
            else:
                self.log("⚠️ אין כרגע מיקום GPS או IP זמין; לא נשלחו קואורדינטות מדומות")
            last_logged_source = loc.get("source")
            self._gps_stop.wait(config.GPS_UPDATE_INTERVAL_SECONDS)

    def _initial_broadcast(self):
        """פותח את האירוע בשרת LifeGuard: אנשי קשר מהימנים + המתנדב המתאים הקרוב (הסלמה בשרת)."""
        loc = self._effective_location(location_module.get_location(log_callback=self.log))
        risk = (self.current_event or {}).get("risk_assessment") or {}
        severity = alert_gateway.SEVERITY_FROM_RISK.get(risk.get("level"), "unknown")
        if (self.current_event or {}).get("trigger_source") in ("panic_button", "voice", "safety_timer"):
            severity = "high"
        if not self.gateway.connected():
            self.log("❗ לא מחובר לשרת LifeGuard - ההתראה נשמרה ותישלח כשיחובר. התקשר/י בעצמך למוקד החירום!")
        self.gateway.open_incident(self.current_event["event_id"], mode="loud",
                                   emergency_type=(self.current_event or {}).get("emergency_type", "unknown"),
                                   severity=severity, location=loc if loc.get("available") else None,
                                   profile=self._profile_for_responders(), escort_id=self._take_escort_for_incident(),
                                   risk=risk)   # מד הסכנה מוצג למגיבים בלבד, ומשמש לתור המתנדבים

    def _take_escort_for_incident(self):
        """אירוע שנפתח בזמן ליווי (בתום הטיימר או SOS ידני בדרך) מקושר לליווי בשרת, והליווי נסגר -
        כדי שהשרת לא יפתח אירוע נוסף בתום הזמן."""
        eid = self._escort_for_incident or self._escort_id
        self._escort_for_incident = None
        if self._escort_id:
            self._escort_id = None
            self._clear_safety_timer_state()
        return eid

    def _profile_for_responders(self):
        """שם תצוגה תמיד; מידע רפואי רק אם המשתמש בחר לשתף אותו עם מגיבים (ברירת מחדל: לא)."""
        profile = {"display_name": auth_module.get_display_name(self.username)}
        try:
            if incident_store.get_setting(self.username, "share_medical_with_responders", "0") == "1":
                notes = incident_store.get_safety_plan(self.username).get("medical_notes")
                if notes:
                    profile["medical_notes"] = notes
        except Exception:
            pass
        return profile

    # ---------- מצב מסירה - מבוסס אך ורק על אישורי השרת ----------
    def get_delivery_status(self):
        event_id = (self.current_event or {}).get("event_id")
        if not event_id:
            return alert_gateway._describe(None, self.gateway.connected())
        return self.gateway.status(event_id)

    def _on_gateway_status(self, event_id, status):
        if (self.current_event or {}).get("event_id") != event_id:
            return
        self._record("delivery", status["text"].replace("\n", " "), data={
            "recipients": [{k: r.get(k) for k in ("display_name", "role", "state")} for r in status.get("recipients", [])]})
        if self.state == State.SILENT_TRACKING:
            return  # במעקב שקט אסור שמצב השליחה יוצג על המסך
        try:
            self.on_delivery_update(status)
        except Exception:
            pass

    def _record_location(self, loc, force=False):
        """מתעד מיקום בציר הזמן רק כשהוא משתנה משמעותית (או כל דקה) - לא כל 5 שניות."""
        if self.current_event is None:
            return
        now = time.time()
        last = getattr(self, "_last_loc_record", None)
        if not loc or not loc.get("available"):
            if force or (last and last[3] != "unavailable"):
                self._record("location", "מיקום לא זמין")
                self._last_loc_record = (now, None, None, "unavailable")
            return
        lat, lon, source = loc.get("lat"), loc.get("lon"), loc.get("source")
        moved = True
        if last and last[1] is not None:
            moved = map_module._haversine_m(last[1], last[2], lat, lon) > 50
        if force or not last or last[3] != source or moved or now - last[0] > 60:
            kind = "GPS" if loc.get("is_precise") else "IP משוער"
            self._record("location", f"מיקום ({kind}): {lat:.5f}, {lon:.5f} - {loc.get('accuracy', '')}",
                         data={"lat": lat, "lon": lon, "source": source,
                               "is_precise": bool(loc.get("is_precise")),
                               "accuracy_m_estimate": loc.get("accuracy_m_estimate"),
                               "captured_at": loc.get("timestamp")})
            self._last_loc_record = (now, lat, lon, source)

    # מיקום שהוזן ידנית: מחשבים ממנו מסלול רק אם הוא ברמת רחוב/שכונה. כתובת של עיר שלמה (~3-5 ק"מ)
    # הייתה שולחת למקום "קרוב" למרכז העיר - לא לאדם. אז במקום מסלול מבקשים כתובת מדויקת יותר.
    MANUAL_ROUTE_MAX_ACC_M = 800

    def _route_origin(self, loc):
        """-> (מיקום לחישוב מסלול, סיבה אם אי אפשר). GPS אמיתי > מיקום ידני מספיק מדויק > כלום (IP לא)."""
        loc = self._effective_location(loc or {})
        if not loc.get("available"):
            return None, "אין מיקום - כתבו כתובת (רחוב ומספר) או הדביקו קישור מפה"
        if str(loc.get("source", "")).startswith("manual"):
            if (loc.get("accuracy_m_estimate") or 10 ** 6) <= self.MANUAL_ROUTE_MAX_ACC_M:
                return loc, None
            return None, "הכתובת שכתבת כללית מדי (עיר/אזור שלם) - כתבו רחוב ומספר כדי לקבל מסלול"
        if loc.get("source") == "windows_location":
            # שירות המיקום של Windows (Wi-Fi): בדרך כלל ±50-300 מ' - מספיק לכיוון מקום בטוח, כמו כתובת ברמת רחוב
            if (loc.get("accuracy_m_estimate") or 10 ** 6) <= self.MANUAL_ROUTE_MAX_ACC_M:
                return loc, None
            return None, "מיקום ה-Wi-Fi לא מדויק מספיק - כתבו כתובת או הדביקו קישור מפה כדי לקבל מסלול"
        if loc.get("is_precise"):
            return loc, None
        return None, "מיקום IP משוער בלבד - כתבו כתובת או הדביקו קישור מפה כדי לקבל מסלול"

    def _find_safe_route(self):
        """מוצא מקום בטוח קרוב (משטרה/בי"ח) + מסלול הליכה, ומעדכן את ה-UI. (רענון בזמן אירוע פעיל)"""
        self._find_safe_route_for_location(location_module.get_location(log_callback=self.log))

    def _show_initial_location_and_route(self):
        """
        קריאה ראשונית ומיידית (רצה כבר מרגע הטריגר, לפני שהאירוע בכלל הופעל במלואו) -
        כדי שהמפה תציג משהו מייד ולא רק אחרי שהספירה לאחור מסתיימת.
        """
        loc = location_module.get_location(log_callback=self.log)
        if self.current_event is not None and loc.get("available"):
            self.current_event["locations"].append(loc)
        self._record_location(loc, force=True)
        self.on_location_update(loc)
        if loc.get("available"):
            self.log(f"📍 מיקום ראשוני: {loc['city']} ({loc['source']}; {loc['accuracy']})")
        else:
            self.log("⚠️ מיקום ראשוני לא זמין")
        self._find_safe_route_for_location(loc)

    def _find_safe_route_for_location(self, loc):
        origin, reason = self._route_origin(loc)
        if origin is None:
            if self.state != State.SILENT_TRACKING:
                self.log(f"⚠️ מסלול למקום בטוח לא חושב: {reason}")
            self.on_route_update({"origin": loc, "result": None, "reason": reason})
            return
        ev = self.current_event
        silent = (ev or {}).get("kind") == "SILENT_ALERT"
        log = self._log_silent if silent else self.log      # במעקב שקט שום דבר לא נכתב ליומן הגלוי
        manual = str(origin.get("source", "")).startswith("manual")
        base = {"origin": origin, "manual": manual, "accuracy_m": origin.get("accuracy_m_estimate") if manual else None}
        lat, lon = origin["lat"], origin["lon"]
        # שלב 1 - מיידי (<0.1 שנ', בלי רשת): רשימה מובנית ארצית (כיבוי רשמי, משטרה, בי"ח עם מיון) + מטמון,
        # ומיד מסלול הליכה (OSRM, ~0.2-2 שנ'). כך יש יעד ומסלול על המסך כמעט מיד, גם כששירותי החיפוש איטיים.
        import worship_pref
        worship = worship_pref.get(self.username)       # מקומי בלבד; מקום תפילה רק כשאין מקום אחר קרוב
        quick = map_module.find_safe_route(lat, lon, log_callback=None, online=False, worship=worship)
        if quick:
            quick["route"] = map_module.get_walking_route(lat, lon, quick["place"]["lat"], quick["place"]["lon"])
            if ev is not None and self.current_event is ev:
                ev["safe_route"] = quick
            self.on_route_update(dict(base, result=quick, refining=True))
        # שלב 2 - רשת (עד ~10 שנ'): Overpass + Nominatim + דירוג לפי מרחק הליכה אמיתי. מעדכן רק אם השתנה.
        full = map_module.find_safe_route(lat, lon, log_callback=log, worship=worship)
        if ev is not None and self.current_event is not ev:
            return                                          # האירוע הסתיים בינתיים
        result = full if (full and (full.get("route") or not (quick and quick.get("route")))) else (quick or full)
        if self.current_event is not None:
            self.current_event["safe_route"] = result
        self.on_route_update(dict(base, result=result, reason=None if result else
                                  "עדיין לא נמצא מקום בטוח (שירותי המפות לא ענו / אין בקרבת מקום) - מנסה שוב..."))
        if (not result or not result.get("route")) and ev is not None:
            self._schedule_route_retry(ev, loc)

    ROUTE_RETRY_DELAYS_S = (20, 40, 60, 120, 240)

    def _schedule_route_retry(self, ev, loc):
        """שירותי מפות ציבוריים נופלים לפעמים (Overpass היה למטה לגמרי ב-2026-11-08). באירוע פעיל -
        מנסים שוב, עם המיקום העדכני ביותר, עד שיש מסלול או שהאירוע נגמר."""
        n = ev.get("_route_retries", 0)
        if n >= len(self.ROUTE_RETRY_DELAYS_S):
            return
        ev["_route_retries"] = n + 1

        def again():
            if self.current_event is not ev or ev.get("safe_route"):
                return
            latest = (ev.get("locations") or [None])[-1] or loc
            self._find_safe_route_for_location(latest)
        t = threading.Timer(self.ROUTE_RETRY_DELAYS_S[n], again)
        t.daemon = True
        t.start()

    def _on_photo_captured(self, filepath, kind):
        if self.current_event is not None:
            # ראיה: נשמרת בלי טשטוש, מוצפנת מיד, והקובץ הגלוי נמחק (evidence_vault.py)
            try:
                filepath = self.vault.seal(filepath, self.current_event["event_id"], kind)
                note = "תמונה נשמרה כראיה מוצפנת"
            except Exception as exc:  # noqa: BLE001 - לא מאבדים ראיה בגלל כשל הצפנה
                note = f"תמונה נשמרה מקומית (ההצפנה נכשלה: {exc})"
            self.current_event["photos"].append({"path": filepath, "kind": kind, "time": time.time()})
            self._record("media", f"{note} ({kind})", data={"path": filepath, "type": "photo", "kind": kind})
        self.on_photo_captured(filepath, kind)
        # מדיה נשמרת מקומית בלבד. העלאה לשרת דורשת אחסון מוצפן (לא קיים עדיין) - לא נשלחת לשום ערוץ חיצוני.

    def _on_audio_chunk_recorded(self, filepath):
        """
        נקרא ע"י audio_module בכל צ'אנק הקלטה שנשמר. ההקלטה נשמרת מקומית ומתועדת בציר הזמן.
        """
        if self.current_event is not None:
            note = "קטע הקלטה נשמר כראיה מוצפנת"
            try:   # כמו תמונות: מוצפן מיד, SHA-256 של המקור, הקובץ הגלוי נמחק (evidence_vault.py)
                filepath = self.vault.seal(filepath, self.current_event["event_id"], "audio")
                try:   # תור העלאה (רק אם השרת יאשר: הרשאת הקלטות + אירוע מאושר) - privacy_sync.py
                    import privacy_sync
                    item = self.vault.manifest(self.current_event["event_id"])["items"][-1]
                    privacy_sync.queue_recording(self.username, self.current_event["event_id"], item)
                except Exception:  # noqa: BLE001 - התור הוא תוספת; ההקלטה המקומית כבר נשמרה
                    pass
            except Exception as exc:  # noqa: BLE001 - לא מאבדים ראיה בגלל כשל הצפנה
                note = f"קטע הקלטה נשמר מקומית (ההצפנה נכשלה: {exc})"
            self.current_event["audio_files"].append(filepath)
            self._record("media", note, data={"path": filepath, "type": "audio"})


    def _stop_active_sos(self):
        """
        מסמן לכל ה-threads לעצור, בלי לחסום את הקורא (למשל את ה-UI thread שמזין סיסמה).
        הניקוי בפועל (join) קורה ב-thread נפרד ברקע - כך שביטול אירוע מרגיש מיידי,
        ולא "מקפיא" את האפליקציה עד 8 שניות כמו שקרה קודם.
        """
        self.log("מסיים אירוע פעיל - עוצר סירנה, הקלטה, מצלמה ומעקב GPS")
        self._siren_stop.set()
        self._audio_stop.set()
        self._gps_stop.set()
        self._camera_stop.set()
        self._voice_warning_stop.set()
        if self.current_event is not None:
            self.current_event["end_time"] = time.time()

        threading.Thread(target=self._join_threads_background, args=(list(self._threads),), daemon=True).start()

    def _join_threads_background(self, threads_to_join):
        for t in threads_to_join:
            t.join(timeout=5)
        self.log("🧹 כל רכיבי החומרה (מצלמה/מיקרופון) שוחררו במלואם")

    # ---------- ניטור חי לכיול (לא אירוע אמיתי!) ----------
    def start_live_monitor(self):
        """
        מריץ מדידת רעש חיה ברקע לצורך כיול (רואים את המד זז לפי רעש אמיתי בסביבה),
        בלי להפעיל אף רכיב אחר (לא סירנה, לא שידור, לא הקלטה). זמין רק במצב IDLE.
        """
        if self.state != State.IDLE:
            return
        self._live_monitor_stop.clear()
        threading.Thread(target=self._live_monitor_loop, daemon=True).start()

    def stop_live_monitor(self):
        self._live_monitor_stop.set()

    def _live_monitor_loop(self):
        while not self._live_monitor_stop.is_set() and self.state == State.IDLE:
            noise = risk_module.measure_noise_level(0.6, log_callback=None)
            if noise is None:
                score, level = 0, "UNKNOWN"
            else:
                score = noise / config.LOUD_NOISE_RMS_THRESHOLD if config.LOUD_NOISE_RMS_THRESHOLD else 0
                # The live calibration gauge reports acoustic level only; it never calls SOS.
                level = "MEDIUM" if noise >= config.LOUD_NOISE_RMS_THRESHOLD else "LOW"
            self.on_live_risk_update(score, level)
            self._live_monitor_stop.wait(config.LIVE_MONITOR_INTERVAL_SECONDS)

    # ---------- זיהוי מילת קוד קולית ברקע ----------
    def start_voice_trigger(self):
        """
        מתחיל להאזין לשלוש פקודות החובה ולביטוי כפייה אופציונלי.
        דורש שכל שלושת הביטויים יהיו מוגדרים. רץ באופן רציף בכל המצבים, כולל *בתוך מעקב שקט* - שם זה
        קריטי במיוחד: זה בדיוק המצב שבו אי אפשר להגיע למקלדת, ולכן חייבת להיות שליטה קולית
        מלאה (ביטול האזעקה השקטה, או הסלמה לאזעקה רועשת).
        נעצר רק בהערכת סיכון (ASSESSING, כ-3 שניות) כדי לפנות את המיקרופון לזיהוי המילים
        המסוכנות של ההערכה עצמה.
        """
        if self.state == State.ASSESSING:
            return
        if self._voice_listener is not None:
            return
        secret_word = auth_module.get_voice_secret_word(self.username)
        silent_phrase = auth_module.get_silent_alarm_phrase(self.username)
        cancel_phrase = auth_module.get_secret_cancel_phrase(self.username)
        duress_phrase = auth_module.get_duress_phrase(self.username)
        if not (secret_word and silent_phrase and cancel_phrase):
            return  # פרופיל ישן ללא שלושת הביטויים - לא מפעילים מאזין חלקי; יש להשלים בהגדרות

        # קריטי: במעקב שקט, *אסור* להעביר את self.log כ-log_callback - הוא מדפיס למסך.
        # במצב הזה כל תיעוד חייב ללכת ל-_log_silent בלבד, אחרת עצם ההודעה "האזנה קולית
        # פעילה" הייתה מסגירה שמשהו רץ ברקע.
        log_cb = self._log_silent if self.state == State.SILENT_TRACKING else self.log

        self._voice_listener = voice_trigger_module.VoiceTriggerListener(
            secret_word=secret_word,
            silent_phrase=silent_phrase,
            cancel_phrase=cancel_phrase,
            duress_phrase=duress_phrase,
            on_triggered=self._handle_alarm_phrase_spoken,
            on_silent_triggered=self._handle_silent_phrase_spoken,
            on_cancel_triggered=self._handle_cancel_phrase_spoken,
            on_duress_triggered=self._handle_duress_phrase_spoken,
            log_callback=log_cb,
            language=config.VOICE_TRIGGER_LANGUAGE,
            username=self.username,   # מודל קולי אישי (personal_kws), אם אומן בפרופיל
            fake_call_phrase=self._fake_call_phrase(),
            on_fake_call=self._handle_fake_call_phrase,
            danger_fn=self._cloud_speech_now,
            on_audio=self.hazard_monitor.feed,
        )
        self.hazard_monitor.start()
        self._voice_listener.start()

    DANGER_STATES = ("ASSESSING", "COUNTDOWN", "ACTIVE_SOS", "SILENT_TRACKING")

    def _cloud_speech_now(self):
        """חיסכון בחשמל: ברגיל רק זיהוי מקומי. בזמן סכנה - גם Google לדיוק (אם לא כובה בהגדרות)."""
        import speech_local
        return self.state.name in self.DANGER_STATES and speech_local.cloud_assist_enabled(self.username)

    def _fake_call_phrase(self):
        try:
            import fake_call
            s = fake_call.load_settings(self.username)
            return s["phrase"] if s.get("enabled") else ""
        except Exception:  # noqa: BLE001
            return ""

    FAKE_CALL_SOURCE = "fake_call"

    def _handle_fake_call_phrase(self):
        """
        שיחה מזויפת - רק כשאין אירוע פעיל (בזמן ספירה / SOS / מעקב שקט לא מציגים כלום).
        עם "גם התראה שקטה": מתחילה מיד התראה שקטה (כמו ביטוי המצוקה השקטה), והשיחה היא נקודת ההחלטה:
        ניתוק -> ההתראה מבוטלת (fake_call_declined); מענה או בלי תגובה -> ההתראה נשארת.
        """
        if self.state != State.IDLE:
            return
        linked = False
        try:
            import fake_call
            linked = bool(fake_call.load_settings(self.username).get("with_silent_alert"))
        except Exception:  # noqa: BLE001
            linked = False
        if linked:
            self._pending_silent_source = self.FAKE_CALL_SOURCE
            self.trigger_silent()
            linked = self.state == State.SILENT_TRACKING and \
                (self.current_event or {}).get("trigger_source") == self.FAKE_CALL_SOURCE
            if self._pending_silent_source == self.FAKE_CALL_SOURCE:
                self._pending_silent_source = None      # לא הופעל - שלא "ידבק" להתראה אחרת
        self.on_fake_call(linked)

    def fake_call_declined(self):
        """ניתוק השיחה המזויפת: מבטל את ההתראה השקטה *רק* אם השיחה היא שהתחילה אותה - לעולם לא התראה אחרת."""
        if self.state == State.SILENT_TRACKING and \
                (self.current_event or {}).get("trigger_source") == self.FAKE_CALL_SOURCE:
            self._log_silent("השיחה המזויפת נותקה - ההתראה השקטה בוטלה")
            return self.end_silent_tracking()
        return False

    def restart_voice_trigger(self):
        """אחרי שינוי הגדרות (למשל ביטוי השיחה המזויפת) - מפעילים את ההאזנה מחדש עם הביטויים העדכניים."""
        if self.state != State.IDLE:
            return
        try:
            self.stop_voice_trigger()
        except Exception:  # noqa: BLE001
            pass
        self.start_voice_trigger()

    def _handle_alarm_phrase_spoken(self):
        """
        נקרא כשנאמרה מילת הקוד להפעלת אזעקה רועשת. מנתב לפי המצב:
        - IDLE: מפעיל SOS רועש מיידי, ללא הערכת סיכון וללא ספירה לאחור.
        - COUNTDOWN: עוקף את הספירה ומפעיל SOS מיד.
        - SILENT_TRACKING: מסלים את המעקב השקט לאזעקה רועשת מלאה.
        """
        if self.state in (State.IDLE, State.FEEDBACK):
            self.trigger(force_panic=True, source="voice")
        elif self.state == State.COUNTDOWN:
            self._record("user_action", "פקודה קולית לאזעקה רועשת - דילוג על הספירה",
                         incident_store.PROVENANCE_CONFIRMED)
            # פקודת האזעקה הרועשת גוברת על ספירה לאחור ומפעילה SOS מיד. תחת נעילה - אחרת
            # thread הספירה והפקודה הקולית עלולים להפעיל SOS פעמיים באותה שנייה.
            with self._state_lock:
                if self.state == State.COUNTDOWN:
                    self._activate_sos()
        elif self.state == State.SILENT_TRACKING:
            self.escalate_silent_to_loud()

    def escalate_silent_to_loud(self):
        """
        הסלמה ממעקב שקט לאזעקה רועשת מלאה: מדליק סירנה + מסך SOS + אזהרה קולית מרתיעה,
        בלי לאבד את ההקלטה/מצלמה/מיקום שכבר רצים (הם ממשיכים כרגיל, לא מופעלים מחדש).
        """
        if self.state != State.SILENT_TRACKING:
            return False
        # קריטי - סדר הפעולות: משנים קודם את המצב ל-ACTIVE_SOS ורק *אחר כך* כותבים ליומן.
        # self.log() מנתב אוטומטית ל-_log_silent כל עוד המצב הוא SILENT_TRACKING, אז לוג
        # שנכתב לפני שינוי המצב היה נעלם מהמסך - וזו הסלמה מכוונת שכן צריכה להיות גלויה.
        self._set_state(State.ACTIVE_SOS)
        self.log("🚨 הסלמה: אזעקה שקטה הפכה לאזעקה מלאה (נאמרה מילת ההפעלה)")
        self._record("user_action", "הסלמה ממעקב שקט לאזעקה רועשת (פקודה קולית)",
                     incident_store.PROVENANCE_CONFIRMED)
        try:
            incident_store.update_incident(self.username, self.current_event["event_id"], kind="SOS")
        except Exception as exc:
            self._storage_failure(exc)
        # המאזין תיעד עד עכשיו ל-_log_silent - מחזירים ללוג גלוי, בלי לפתוח מחדש את המיקרופון
        self._retarget_voice_log()

        # מדליקים את מה שהיה כבוי בלבד - הסירנה, והאזהרה הקולית המרתיעה.
        self._siren_stop.clear()
        siren_thread = threading.Thread(
            target=siren_module.play_siren, args=(self._siren_stop, self.log), daemon=True
        )
        self._threads.append(siren_thread)
        siren_thread.start()

        self._voice_warning_stop.clear()
        warning_thread = threading.Thread(
            target=voice_warning_module.warning_loop, args=(self._voice_warning_stop, self.log), daemon=True
        )
        self._threads.append(warning_thread)
        warning_thread.start()

        # השרת מעדכן את המהימנים ומתחיל לשלוח למתנדבים (במצב שקט הם לא הוזעקו)
        self.gateway.set_loud(self.current_event["event_id"])
        return True

    def _handle_silent_phrase_spoken(self):
        """
        נקרא מ-voice_trigger_module כשזוהה ביטוי האזעקה השקטה - מנתב לפי המצב הנוכחי:
        מ-IDLE מפעיל מעקב חדש; תוך כדי ספירה/אירוע גלוי - ממיר אותו למעקב שקט (במקום
        שיהיה צריך להקליד קוד). קריטי: שום קריאה כאן לא רושמת ליומן הגלוי.
        """
        if self.state in (State.IDLE, State.FEEDBACK):
            self.trigger_silent()
        elif self.state == State.COUNTDOWN:
            self._log_silent("🤫 ביטוי אזעקה שקטה נאמר בזמן ספירה - עובר ישר למעקב שקט")
            self._go_silent(already_tracking=False)
        elif self.state == State.ACTIVE_SOS:
            self._log_silent("🤫 ביטוי אזעקה שקטה נאמר תוך כדי אירוע פעיל - ממיר למעקב שקט")
            self._go_silent(already_tracking=True)
        # ASSESSING/FEEDBACK/SILENT_TRACKING - מתעלמים, אין מה לעשות שם

    def _handle_cancel_phrase_spoken(self):
        """
        נקרא מ-voice_trigger_module כשזוהה קוד הביטול הסודי - מבטל *מיד* כל דבר שקורה כרגע,
        בין אם רועש ובין אם שקט, בהתאם למצב הנוכחי. במצב שקט - הביטול עצמו נשאר לגמרי שקט
        (end_silent_tracking כבר מטפל בזה); במצב רועש - ביטול רגיל וגלוי, בדיוק כאילו הוקלד
        קוד הביטול הרגיל.
        """
        if self.state == State.SILENT_TRACKING:
            self.end_silent_tracking()
        elif self.state == State.ACTIVE_SOS:
            self._real_cancel_active(via="voice")
        elif self.state == State.COUNTDOWN:
            self._real_cancel_countdown(via="voice")
        # IDLE/ASSESSING/FEEDBACK - אין כלום לבטל, מתעלמים

    def activate_duress_mode(self, source="voice"):
        """Covert duress path: appears to cancel, but keeps/starts silent SOS tracking."""
        if self.state == State.SILENT_TRACKING:
            self._log_silent("ביטוי כפייה התקבל בזמן מעקב שקט; המעקב ממשיך")
            return True
        self._log_silent(f"מצב כפייה הופעל דרך {source}; ממשיך/מתחיל דיווח שקט")
        if self.state in (State.IDLE, State.FEEDBACK):
            self._pending_silent_source = "duress"
            self.trigger_silent()
            return self.state == State.SILENT_TRACKING
        if self.state in (State.COUNTDOWN, State.ASSESSING):
            self._record("user_action", f"ביטוי כפייה הוזן ({source}) - האירוע הומר למעקב שקט",
                         incident_store.PROVENANCE_CONFIRMED)
            self._go_silent(already_tracking=False)
            return self.state == State.SILENT_TRACKING
        if self.state == State.ACTIVE_SOS:
            self._record("user_action", f"ביטוי כפייה הוזן ({source}) - האירוע הומר למעקב שקט",
                         incident_store.PROVENANCE_CONFIRMED)
            self._go_silent(already_tracking=True)
            return self.state == State.SILENT_TRACKING
        return False

    def _handle_duress_phrase_spoken(self):
        # No visible log entry or UI state transition is exposed for this event.
        self.activate_duress_mode(source="voice")

    def report_sensor_signal(self, signal, confidence=0.5, metadata=None):
        """Entry point for future Android/iOS accelerometer/gyroscope/wearable adapters."""
        event = sensor_module.report_sensor_signal(signal, confidence=confidence, metadata=metadata)
        if self.state == State.IDLE:
            self.log(f"📡 התקבל אירוע חיישן: {signal}; ממתין לטריגר/אימות משתמש")
            if self.wellness is not None:
                self.wellness.on_sensor(signal, confidence)     # נפילה/מכה -> "הכל בסדר?"
        else:
            self._log_silent(f"אירוע חיישן במהלך אירוע פעיל: {signal}")
        return event

    def _retarget_voice_log(self):
        """מעדכן את יעד התיעוד של המאזין לפי המצב הנוכחי; מפעיל מאזין אם אין."""
        listener = self._voice_listener
        if listener is None:
            self.start_voice_trigger()
            return
        callback = self._log_silent if self.state == State.SILENT_TRACKING else self.log
        if hasattr(listener, "set_log_callback"):
            listener.set_log_callback(callback)
        else:
            listener.log_callback = callback

    def stop_voice_trigger(self, suppress_log=False):
        if self._voice_listener is not None:
            self._voice_listener.stop(suppress_log=suppress_log)
            self._voice_listener = None

    # ---------- מצב הרתעה קולית עצמאי (בלי להפעיל SOS מלא) ----------
    def start_voice_warning_standalone(self):
        """
        משמיע את אזהרת ההרתעה הקולית בלולאה, בלי סירנה/הקלטה/מצלמה/שידור לאנשי קשר.
        שימושי כשרוצים רק להרתיע מישהו שמתקרב בלי לדווח/לתעד את המצב.
        זמין רק כשאין אירוע SOS פעיל (לא רוצים שתי לולאות אזהרה יתנגשו).
        """
        if self.state != State.IDLE:
            self.log("⚠️ לא ניתן להפעיל מצב הרתעה עצמאי בזמן שאירוע SOS פעיל")
            return
        self._standalone_voice_warning_stop.clear()
        threading.Thread(
            target=voice_warning_module.warning_loop,
            args=(self._standalone_voice_warning_stop, self.log),
            daemon=True,
        ).start()
        self.log("📢 מצב הרתעה קולית עצמאי הופעל ידנית (ללא סירנה/הקלטה/שידור)")

    def stop_voice_warning_standalone(self):
        self._standalone_voice_warning_stop.set()

    # ---------- בדיקת שליחה לאנשי קשר (לא אירוע אמיתי!) ----------
    # ---------- טיימר בטיחות ("ליווי הביתה") ----------
    def start_safety_timer(self, minutes, silent_on_expiry=False, destination=""):
        """
        מפעיל טיימר בטיחות: "אני אמור/ה להגיע ליעד תוך X דקות". אם לא מאשרים הגעה עד אז -
        מופעלת אזעקה אוטומטית (רועשת או שקטה, לפי silent_on_expiry).
        זמין רק ב-IDLE (אין טעם באמצע אירוע). מחזיר (bool, msg).
        """
        if self.state != State.IDLE:
            return False, "לא ניתן להפעיל טיימר באמצע אירוע"
        if self._safety_timer_deadline is not None:
            return False, "טיימר בטיחות כבר פעיל - בטל/י או אשר/י הגעה קודם"
        try:
            minutes = float(minutes)
        except (TypeError, ValueError):
            return False, "מספר דקות לא תקין"
        if minutes <= 0 or minutes > 24 * 60:
            return False, "מספר הדקות חייב להיות בין 1 ל-1440 (24 שעות)"

        self._safety_timer_stop.clear()
        self._safety_timer_deadline = time.time() + minutes * 60
        self._safety_timer_silent = bool(silent_on_expiry)
        self._safety_timer_destination = (destination or "").strip()

        mode_txt = "אזעקה שקטה" if silent_on_expiry else "אזעקה מלאה"
        dest_txt = f" ({self._safety_timer_destination})" if self._safety_timer_destination else ""
        self.log(f"⏳ טיימר בטיחות הופעל: {minutes:.0f} דקות{dest_txt} - בתום הזמן תופעל {mode_txt}")

        threading.Thread(target=self._safety_timer_loop, daemon=True).start()
        self._start_server_escort(minutes, self._safety_timer_destination, bool(silent_on_expiry), dest_txt)
        return True, f"טיימר בטיחות פעיל ל-{minutes:.0f} דקות"

    # ---------- ליווי הביתה משותף: הטיימר נשמר גם בשרת ----------
    def _start_server_escort(self, minutes, destination, silent, dest_txt):
        """השרת אוכף את הזמן: אם המחשב כבה/נגנב באמצע, השרת פותח קריאת חירום בעצמו עם המיקום
        האחרון. אנשי הקשר המחוברים רואים את הליווי ואת המיקום החי."""
        self._escort_id = None
        self._escort_pending_action = None

        def work():
            client = self.gateway.client
            if not self.gateway.connected():
                self.log("⚠️ לא מחובר לשרת - הטיימר מקומי בלבד: אם המחשב יכבה, אף אחד לא יקבל התראה")
                return
            loc = location_module.get_location()
            try:
                esc = client.start_escort(minutes, destination, "silent" if silent else "loud",
                                          _escort_loc(loc))
            except Exception as exc:  # noqa: BLE001
                self.log(f"⚠️ הליווי לא נשמר בשרת ({getattr(exc, 'message', exc)}) - טיימר מקומי בלבד")
                if config.SAFETY_TIMER_NOTIFY_CONTACTS_ON_START:
                    self._notify_trusted_async(
                        f"ℹ️ {auth_module.get_display_name(self.username)} הפעיל/ה טיימר בטיחות ל-{minutes:.0f} "
                        f"דקות{dest_txt}. אם לא יאשר/תאשר הגעה בזמן - תישלח התראת חירום.")
                return
            with self._escort_lock:
                closed_meanwhile = self._safety_timer_deadline is None
                if not closed_meanwhile:
                    self._escort_id = esc["id"]
                action, self._escort_pending_action = self._escort_pending_action, None
            if closed_meanwhile:
                # המשתמש אישר הגעה/ביטל לפני שהשרת ענה - שולחים את הפעולה שהוא בחר בפועל
                # (באג שנמצא בבדיקה: בעבר נשלח תמיד "בוטל", והעוקבים לא ראו "הגיע/ה בשלום")
                try:
                    client.escort_action(esc["id"], action or "cancelled")
                except Exception as exc:  # noqa: BLE001
                    self.log(f"⚠️ עדכון הליווי בשרת נכשל ({getattr(exc, 'message', exc)})")
                return
            names = ", ".join(w["display_name"] for w in esc.get("watchers", [])) or "אין אנשי קשר מחוברים"
            self.log(f"📡 הליווי נשמר בשרת - גם אם המחשב יכבה, השרת יתריע בתום הזמן. עוקבים: {names}")
        threading.Thread(target=work, daemon=True).start()

    def _escort_server_action(self, action, minutes=None):
        eid = self._escort_id
        if not eid or not self.gateway.connected():
            return
        client = self.gateway.client

        def work():
            try:
                client.escort_action(eid, action, minutes)
            except Exception as exc:  # noqa: BLE001
                self.log(f"⚠️ עדכון הליווי בשרת נכשל ({getattr(exc, 'message', exc)})")
        threading.Thread(target=work, daemon=True).start()

    def _escort_send_location(self):
        eid = self._escort_id
        if not eid or not self.gateway.connected():
            return
        loc = _escort_loc(location_module.get_location())
        if loc:
            if self.wellness is not None and loc.get("is_precise"):
                self.wellness.on_location(time.time(), loc["lat"], loc["lon"])   # עצירה פתאומית
            try:
                self.gateway.client.escort_location(eid, loc)
            except Exception:
                pass

    def _safety_timer_loop(self):
        warned = False
        last_loc = time.time()
        while not self._safety_timer_stop.is_set():
            if time.time() - last_loc >= config.ESCORT_LOCATION_SECONDS:
                last_loc = time.time()
                threading.Thread(target=self._escort_send_location, daemon=True).start()
            deadline = self._safety_timer_deadline
            if deadline is None:
                return
            remaining = deadline - time.time()

            if remaining <= 0:
                self._on_safety_timer_expired()
                return

            is_warning = remaining <= config.SAFETY_TIMER_WARNING_BEFORE_SECONDS
            if is_warning and not warned:
                warned = True
                self.log(f"⚠️ טיימר הבטיחות מסתיים בעוד {int(remaining)} שניות! "
                          "אשר/י הגעה או הארך/י את הזמן, אחרת תופעל אזעקה אוטומטית")
            self.on_safety_timer_tick(remaining, is_warning)
            self._safety_timer_stop.wait(1)

        # יצאנו מהלולאה כי בוטל/אושר - מנקים את התצוגה
        self.on_safety_timer_tick(None, False)

    def _on_safety_timer_expired(self):
        """הזמן נגמר בלי אישור הגעה - מפעילים אזעקה אוטומטית."""
        dest = self._safety_timer_destination
        # האירוע שנפתח כאן מקושר לליווי בשרת -> השרת לא יפתח אירוע כפול בתום תקופת החסד
        self._escort_for_incident = self._escort_id
        self._escort_id = None
        self._clear_safety_timer_state()

        dest_txt = f" ({dest})" if dest else ""
        if self._safety_timer_silent:
            self._log_silent(f"⏰ טיימר הבטיחות הסתיים ללא אישור הגעה{dest_txt} - מפעיל אזעקה שקטה")
            self._pending_silent_source = "safety_timer"
            self.trigger_silent()
        else:
            self.log(f"⏰ טיימר הבטיחות הסתיים ללא אישור הגעה{dest_txt} - מפעיל אזעקה אוטומטית!")
            self.trigger(force_panic=True, source="safety_timer")

    def confirm_safe_arrival(self):
        """המשתמש הגיע בשלום - מבטל את הטיימר ומעדכן אנשי קשר אם הם יודעו בהפעלה."""
        if self._safety_timer_deadline is None:
            return False, "אין טיימר בטיחות פעיל"
        dest = self._safety_timer_destination
        had_escort = self._end_escort("arrived")  # השרת מעדכן את העוקבים ("הגיע/ה בשלום")
        self.log("✅ אישרת הגעה בשלום - טיימר הבטיחות בוטל")

        if not had_escort and config.SAFETY_TIMER_NOTIFY_CONTACTS_ON_START:
            dest_txt = f" ל{dest}" if dest else ""
            msg = f"✅ {auth_module.get_display_name(self.username)} הגיע/ה בשלום{dest_txt}. הטיימר בוטל."
            self._notify_trusted_async(msg)
        return True, "הגעה אושרה"

    def extend_safety_timer(self, extra_minutes):
        """מאריך טיימר פעיל (למשל כשמתעכבים) בלי לבטל ולהתחיל מחדש."""
        if self._safety_timer_deadline is None:
            return False, "אין טיימר בטיחות פעיל"
        try:
            extra_minutes = float(extra_minutes)
        except (TypeError, ValueError):
            return False, "מספר דקות לא תקין"
        if extra_minutes <= 0:
            return False, "יש להזין מספר דקות חיובי"
        self._safety_timer_deadline += extra_minutes * 60
        self._escort_server_action("extend", extra_minutes)
        self.log(f"⏳ טיימר הבטיחות הוארך ב-{extra_minutes:.0f} דקות")
        return True, f"הוארך ב-{extra_minutes:.0f} דקות"

    def cancel_safety_timer(self):
        """ביטול מלא של הטיימר (בלי 'הגעתי') - למשל אם שינית תוכניות."""
        if self._safety_timer_deadline is None:
            return False, "אין טיימר בטיחות פעיל"
        self._end_escort("cancelled")
        self.log("🚫 טיימר הבטיחות בוטל")
        return True, "הטיימר בוטל"

    def _end_escort(self, action):
        """מסיים את הטיימר המקומי ואת הליווי בשרת באותה פעולה אטומית (מול ה-thread שיוצר את הליווי):
        אם הליווי עוד בדרך לשרת - הפעולה נרשמת ונשלחת כשהשרת יענה. מחזיר האם היה/יהיה ליווי בשרת."""
        with self._escort_lock:
            eid = self._escort_id
            self._escort_id = None
            if not eid:
                self._escort_pending_action = action
            self._clear_safety_timer_state()
        if eid and self.gateway.connected():
            client = self.gateway.client

            def work():
                try:
                    client.escort_action(eid, action)
                except Exception as exc:  # noqa: BLE001
                    self.log(f"⚠️ עדכון הליווי בשרת נכשל ({getattr(exc, 'message', exc)})")
            threading.Thread(target=work, daemon=True).start()
        return bool(eid) or self.gateway.connected()

    def _clear_safety_timer_state(self):
        self._safety_timer_stop.set()
        self._safety_timer_deadline = None
        self._safety_timer_destination = ""
        self.on_safety_timer_tick(None, False)

    # ---------- התראות סכנה אינטראקטיביות (hazard_alerts.py) ----------
    def _hazard_can_show(self):
        """חלון קופץ רק כשאין אירוע פעיל. במעקב שקט - לעולם לא (חלון היה חושף את המעקב)."""
        if self.state == State.SILENT_TRACKING:
            return False, "silent_tracking"
        if self.state != State.IDLE:
            return False, "event_active"
        return True, None

    def _audio_checkin(self, category, confidence, severity):
        """זיהוי קולי בינוני ומעלה -> "הכל בסדר?" שקט (רטט). רק ב-IDLE; במעקב שקט/אירוע פעיל - לא."""
        if self.state != State.IDLE or self.wellness is None:
            return False
        return self.wellness.on_audio(category, confidence, severity)

    def hazard_respond(self, alert, response, reason=None):
        """רישום תגובת המשתמש/ת וסגירת האירוע (שקט לפי סוג התגובה). לא מבצע את הפעולה עצמה."""
        import hazard_alerts
        hazard_alerts.record_response(self.username, alert, response, reason)
        self.hazard_monitor.manager.close(alert, response)
        if self.wellness is not None and response != "sos":
            self.wellness.dismiss_audio()      # תגובה לחלון = המשתמש/ת ערני/ת; "sos" ממשיך במסלול שלו

    def hazard_activate_sos(self, alert):
        """אחרי אישור מפורש בלבד (החלון שואל). אותו מסלול כמו לחיצה על הכפתור: הערכת סיכון + ספירה לאחור."""
        self.hazard_respond(alert, "sos")
        return self.trigger(source="hazard_alert")

    def hazard_notify_contacts(self, alert, lang="he"):
        """אחרי אישור מפורש. מחזיר את תשובת השרת (למי נשלח + מזהי הודעות לבדיקת קבלה) או זורק שגיאה -
        בלי "נשלח" מדומה כשאין חיבור."""
        import hazard_alerts
        if not self.gateway.connected():
            raise RuntimeError("לא מחובר לשרת LifeGuard - ההודעה לא נשלחה")
        res = self.gateway.client.notify_trusted(hazard_alerts.contacts_message(alert, lang))
        self.hazard_respond(alert, "contacts")
        return res

    def hazard_delivery_status(self, notification_ids):
        """האם אפליקציות אנשי הקשר אישרו קבלה (לא רק "נשלח")."""
        if not self.gateway.connected() or not notification_ids:
            return {}
        return self.gateway.client.notification_status(notification_ids)

    def is_safety_timer_active(self):
        return self._safety_timer_deadline is not None

    def _notify_trusted_async(self, text):
        def _send():
            if not self.gateway.connected():
                self.log("⚠️ ההודעה לאנשי הקשר לא נשלחה: לא מחובר לשרת LifeGuard")
                return
            try:
                self.gateway.client.notify_trusted(text)
            except Exception as exc:
                self.log(f"⚠️ ההודעה לאנשי הקשר לא נשלחה: {exc}")
        threading.Thread(target=_send, daemon=True).start()

    def send_test_broadcast(self):
        """התראת בדיקה דרך השרת; מדווח מי *אישר קבלה באפליקציה* - לא רק "נשלח"."""
        threading.Thread(target=self.gateway.test_alert, args=(self.log,), daemon=True).start()

    def log_configuration_status(self):
        if self.gateway.connected():
            self.log(f"📡 מחובר לשרת LifeGuard ({self.gateway.client.base_url}) - התראות נשלחות לאפליקציות "
                     "של אנשי קשר מאושרים ושל מתנדבים זמינים")
        else:
            self.log("❗ לא מחובר לשרת LifeGuard - התראות SOS לא יגיעו לאף אחד עד להתחברות")

    # ---------- שלב Feedback ----------
    def submit_feedback(self, rating):
        """rating: 'true_event' | 'felt_danger' | 'false_alarm'"""
        if self.current_event is not None:
            self.current_event["rating"] = rating
            self.current_event["username"] = self.username
            self._record("user_action", f"דירוג המשתמש: {_RATING_LABELS.get(rating, rating)}",
                         incident_store.PROVENANCE_CONFIRMED)
            try:
                incident_store.update_incident(self.username, self.current_event["event_id"], rating=rating)
                self._save_event_to_db(self.current_event)
            except Exception as exc:
                self._storage_failure(exc)
        self.log(f"📝 דירוג התקבל: {rating} - נשמר לבסיס הנתונים לאימון עתידי")
        # למידה מהמשוב: אילו מקורות הופעלו, והאם האירוע היה אמיתי (משנה רק את ה"ביטחון", לא את החומרה)
        conf = ((self.current_event or {}).get("risk_assessment") or {}).get("confidence") or {}
        try:
            import risk_feedback
            if risk_feedback.record(self.username, conf.get("sources") or [], rating):
                self.log("🧠 המשוב נלמד: הערכת הביטחון של מקורות הראיה עודכנה")
        except Exception as exc:  # noqa: BLE001
            self.log(f"⚠️ שמירת המשוב ללמידה נכשלה: {exc}")
        if self.current_event is not None and self.current_event.get("photos"):
            threading.Thread(target=self._process_evidence, args=(self.current_event["event_id"], rating),
                             daemon=True).start()
        self.current_event = None
        self._set_state(State.IDLE)

    def _process_evidence(self, event_id, rating):
        """אמת -> נשמר כראיה. שווא -> טשטוש פנים; לאימון רק בהסכמה; המקור נמחק."""
        consent = incident_store.get_setting(self.username, "train_on_false_alarm_media", "0") == "1"
        training = os.path.join(config.DATA_DIR, "training_media", self.username) if consent else None
        try:
            m = self.vault.on_rating(event_id, rating, training_dir=training)
            if rating == "false_alarm":
                self.log(f"🔒 התראת שווא: {len(m['items'])} תמונות טושטשו"
                         + (f", {m.get('training_items', 0)} נשמרו לאימון" if consent else "") + "; המקור נמחק")
            else:
                self.log("🔒 התמונות נשמרו כראיה מוצפנת (לא מטושטשות) - אפשר לייצא למשטרה מהיסטוריית האירועים")
        except Exception as exc:  # noqa: BLE001
            self.log(f"⚠️ עיבוד הראיות נכשל: {exc}")

    # ---------- כיבוי מלא של המנוע (נפרד מביטול אירוע) ----------
    def shutdown(self):
        """
        מסמן לכל ה-threads לעצור באופן מיידי, ללא המתנה חוסמת (לא join!).
        זה נקרא ממש לפני סגירת התוכנה - כל ה-threads הם daemon, כך שהתהליך
        ייסגר מיד וה-OS ישחרר את המשאבים (מצלמה/מיקרופון) בעצמו ברגע שהתהליך נגמר.
        המתנה סינכרונית כאן הייתה תוקעת את כל ה-UI עד 8 שניות (2 שנ' * 4 threads) -
        בדיוק התקלה שגרמה לתחושה ש"לוקח למצלמה הרבה זמן להתכבות".
        """
        self.log("⛔ מתקבלת פקודת כיבוי מלא של התוכנה")
        if self.current_event is not None and self.state != State.FEEDBACK:
            self._record("system", "התוכנה נסגרה בזמן שהאירוע היה פעיל")
            self._close_incident("app_shutdown")
        self._outbox_stop.set()
        if self.current_event is not None and self.state in (State.ACTIVE_SOS, State.SILENT_TRACKING):
            self.gateway.close(self.current_event["event_id"], "cancelled")
            time.sleep(0.1)
        self._siren_stop.set()
        self._audio_stop.set()
        self._gps_stop.set()
        self._camera_stop.set()
        self._live_monitor_stop.set()
        self.hazard_monitor.stop()
        self.stop_voice_trigger()
        self._voice_warning_stop.set()
        self._standalone_voice_warning_stop.set()
        self._safety_timer_stop.set()
        self._safety_timer_deadline = None
        self.state = State.IDLE
        self.current_event = None

    def _save_event_to_db(self, event):
        """
        קובץ ה-JSON הישן (נתוני דירוג לכיול). תיקון: בעבר קובץ פגום הוחלף בשקט ברשימה ריקה
        ונדרס - כל ההיסטוריה נמחקה. כעת storage.load_json מגבה קובץ פגום וזורק שגיאה.
        """
        with storage.file_lock(config.EVENTS_DB_FILE):
            events = storage.load_json(config.EVENTS_DB_FILE, [])
            if not isinstance(events, list):
                raise storage.StorageError("events_log.json אינו רשימה")
            events.append(event)
            storage.atomic_write_json(config.EVENTS_DB_FILE, events)
