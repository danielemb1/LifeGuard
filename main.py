# -*- coding: utf-8 -*-
"""
main.py
LifeGuard Engine - נקודת הכניסה הראשית.
UI ב-Tkinter. הרצה: python main.py
זרימה: LoginWindow (התחברות/הרשמה - נכנסים ישר גם אחרי הרשמה, בלי מסך login נפרד)
        -> LifeGuardApp (המסך הראשי).
"""

import json
import queue
import sys
import threading
import time
import tkinter as tk
import ui_theme as T
from tkinter import font as tkfont

import config
import appearance
import auth_module
import location_module
import map_tiles
import map_hidpi
import emergency_numbers_module
from engine import LifeGuardEngine, State
from login_ui import LoginWindow
from settings_ui import SettingsWindow
import alert_gateway
import backend_client
from alert_window import AlertWindow
from app_screens import CommunityScreen, HomeScreen, MapScreen, ProfileScreen, run_bg
from safety_circle_ui import SafetyCircleScreen
from first_aid_ui import FirstAidScreen
import agent_bridge
import connectivity_module
import features_ui
import windows_notify
import guidance_engine
import health_module
import incident_store
from health_ui import HealthWindow
from incident_history_ui import IncidentHistoryWindow
from safety_center_ui import SafetyCenterWindow, GuidancePanel

try:
    import keyboard  # לקיצור מקלדת גלובלי (טריגר "מילת קוד")
    HAS_KEYBOARD = True
except ImportError:
    keyboard = None  # השם תמיד מוגדר - בלי זה Pylance מסמן "possibly unbound" בכל שימוש
    HAS_KEYBOARD = False

try:
    from tkintermapview import TkinterMapView
    HAS_MAP_WIDGET = True
except Exception:
    TkinterMapView = None
    HAS_MAP_WIDGET = False


# ==================== צבעים וטוקנים: רק דרך ui_theme (T.*) ====================
# לא מעתיקים ערכים לקבועים מקומיים: הערכה (בהירה/כהה) נבחרת בזמן ריצה, והקבועים היו "נתקעים" על הבהירה.


class LifeGuardApp:
    def __init__(self, root, username, password=None, open_target=None):
        self.root = root
        # הסוכן ברקע שותק כל עוד האפליקציה רצה (כולל מעקב שקט - שם אסור להציג שום דבר)
        agent_bridge.mark_app_running()
        self._open_target = open_target or {}  # לחיצה על התראת Windows: lifeguard://open?incident=...
        self.username = username
        self.client = None            # BackendClient מחובר (או None)
        self.server_error = None
        # הסיסמה נשמרת בזיכרון רק עד ההתחברות הראשונה לשרת (לניסיונות חוזרים), ואז נמחקת.
        self._password = password
        self._alert_windows = {}
        self._pending_alerts = set()
        self._reach = None
        # תור thread-safe לעדכוני UI: thread-ים של המנוע (הקלטה/GPS/שידור) לעולם לא נוגעים ב-Tk
        # ישירות. root.after() מ-thread רקע זורק RuntimeError כשהחלון נסגר (כיבוי באמצע אירוע).
        self._ui_queue = queue.Queue()
        self._alive = True
        self.root.after(50, self._drain_ui_queue)
        # סקאלת הטקסט הנבחרת נטענת לפני בניית הממשק, כדי שכל הגדלים ייבנו כבר בגודל הנכון.
        try:
            T.set_scale(incident_store.get_setting(username, "text_scale", "normal"))
        except Exception:
            pass
        # מראה (בהיר/כהה/לפי Windows) והפחתת תנועה של המשתמש/ת - לפני שבונים אף רכיב
        try:
            T.apply_theme(appearance.load_theme_setting(username))
            T.set_reduced_motion(appearance.load_reduce_motion(username))
            T.style_root(self.root)
        except Exception:  # noqa: BLE001
            pass
        display_name = auth_module.get_display_name(username)
        self.display_name = display_name
        self.root.title(f"LifeGuard - {display_name}")
        # החלון מותאם למסך (במסכים עם הגדלת תצוגה גבוהה 860 פיקסלים חורגים מהמסך וסרגל הניווט נחתך)
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        self.root.geometry(f"{min(1280, sw - 40)}x{min(860, sh - 90)}+{max(0, (sw - min(1280, sw - 40)) // 2)}+10")
        self.root.configure(bg=T.BG)
        self.root.resizable(True, True)
        self.root.minsize(min(1000, self.root.winfo_screenwidth() - 40), min(640, self.root.winfo_screenheight() - 90))

        self.title_font = tkfont.Font(family="Segoe UI", size=20, weight="bold")
        self.normal_font = tkfont.Font(family="Segoe UI", size=11)
        self.log_font = tkfont.Font(family="Consolas", size=max(10, int(10 * T.get_scale())))

        self.latest_location = None
        self.community_window = None
        self.emergency_numbers = emergency_numbers_module.get_emergency_numbers(None)
        self._community_registered = set()
        self._windows = {}
        self.gateway = alert_gateway.AlertGateway(username, None, log=self._on_log)
        self.engine = LifeGuardEngine(
            username=username,
            gateway=self.gateway,
            on_state_change=self._on_state_change,
            on_log=self._on_log,
            on_location_update=self._on_location_update,
            on_route_update=self._on_route_update,
            on_photo_captured=self._on_photo_captured,
            on_live_risk_update=self._on_live_risk_update,
            on_safety_timer_tick=self._on_safety_timer_tick,
            on_delivery_update=self._on_delivery_update,
        )
        # שיחה מזויפת (fake_call.py): הביטוי נשמע ב-thread ההאזנה -> המתזמן מעביר לתור ה-UI
        import fake_call
        self.fake_call = fake_call.FakeCallScheduler(self.root, lambda: fake_call.load_settings(self.username),
                                                     post=self._post, on_declined=self.engine.fake_call_declined)
        self.engine.on_fake_call = self.fake_call.trigger      # trigger(linked): ניתוק מבטל את ההתראה השקטה

        self.sos_window = None
        self.live_monitor_on = False
        self.voice_trigger_on = False
        self._build_shell()
        # מיקום Wi-Fi של Windows ברקע כבר בהפעלה (~3-7 שנ') - כדי שב-SOS יהיה מיד, בלי לעכב את השליחה
        threading.Thread(target=location_module.prefetch_windows_location, name="LG-WinLocPrefetch",
                         daemon=True).start()
        self._register_hotkey()
        self._register_quit_hotkey()
        self.root.protocol("WM_DELETE_WINDOW", self._on_root_close_attempt)
        self.root.bind("<<ForceQuit>>", lambda e: self._force_quit())
        self._set_live_monitor(True)  # ניטור חי דולק אוטומטית מרגע ההתחברות
        self._set_voice_trigger(True)  # וגם האזנה למילת הקוד הקולית, אם הוגדרה בהרשמה
        self._refresh_emergency_number()  # מזהה מדינה ומציג את מספר החירום הנכון (ברקע)
        # ניווט מקלדת עקבי: F2 מרכז בטיחות, F3 היסטוריה, F4 תקינות מערכת
        self.root.bind_all("<F2>", lambda e: self._open_safety_center())
        self.root.bind_all("<F3>", lambda e: self._open_history())
        self.root.bind_all("<F4>", lambda e: self._open_health())
        connectivity_module.add_listener(lambda st: self._post(self._update_connectivity_ui, st))
        connectivity_module.start_monitor()
        self.engine.wellness.ask = lambda reason, deadline, answer: self._post(self._ask_wellness, reason, deadline,
                                                                               answer)
        # התראות סכנה אינטראקטיביות (hazard_alert_ui.py) - הזיהוי רק מציע; כל פעולה אחרי אישור
        self._hazard_windows = {}
        self.engine.on_hazard_alert = lambda kind, alert: self._post(self._show_hazard_alert, kind, alert)
        self.root.after(1500, self._poll_connectivity_ui)
        self._run_startup_health_check()
        self.root.after(1000, self._tick_indicators)
        if password:
            self.connect_server(password)
        else:
            self.server_error = "נדרשת סיסמה"

    def _post(self, fn, *args):
        """נקרא מכל thread. הפונקציה תרוץ על ה-thread של הממשק בלבד."""
        if self._alive:
            self._ui_queue.put((fn, args))

    def _drain_ui_queue(self):
        if not self._alive:
            return
        for _ in range(200):  # תקרה לכל סבב - ממשק לא ננעל גם בהצפת לוגים
            try:
                fn, args = self._ui_queue.get_nowait()
            except queue.Empty:
                break
            try:
                fn(*args)
            except tk.TclError:
                pass  # חלון שכבר נסגר - לא קריטי
            except Exception as exc:
                try:
                    self._append_log(f"[WARN] שגיאת ממשק: {exc}")
                except Exception:
                    pass
        try:
            self.root.after(50, self._drain_ui_queue)
        except tk.TclError:
            self._alive = False

    # ---------------- כיבוי מלא של התוכנה ----------------
    def _register_quit_hotkey(self):
        if not HAS_KEYBOARD or keyboard is None:
            return
        try:
            keyboard.add_hotkey(config.QUIT_HOTKEY, lambda: self._post(self._open_account_password_dialog))
            self._on_log(f"[INFO] קיצור כיבוי מלא פעיל: {config.QUIT_HOTKEY}")
        except Exception as e:
            self._on_log(f"[WARN] לא ניתן לרשום קיצור כיבוי: {e}")

    def _open_account_password_dialog(self):
        AccountPasswordDialog(self.root, self.engine, on_confirm=self._force_quit,
                              on_fake_quit=self._fake_quit, on_restore=self._restore_window)

    def _fake_quit(self):
        """
        ביטוי כפייה הוקלד בחלון הכיבוי: החלון "נסגר" כלפי חוץ, אבל התוכנה ממשיכה לרוץ
        במעקב שקט (הקלטה/מיקום/שידור). שחזור: קיצור הכיבוי + סיסמת החשבון האמיתית.
        """
        self._close_all_secondary_windows()
        self.root.withdraw()

    def _restore_window(self):
        try:
            self.root.deiconify()
            self.root.lift()
        except tk.TclError:
            pass

    def _on_root_close_attempt(self):
        if config.DEV_MODE:
            self._force_quit()
        else:
            self._open_account_password_dialog()

    def _force_quit(self):
        self._on_log("⏻ כיבוי מלא של התוכנה...")
        try:
            self.engine.shutdown()
        except Exception:
            pass
        connectivity_module.stop_monitor()
        if self.client is not None:
            self.client.stop_stream()
        self.gateway.shutdown()
        self._alive = False
        if HAS_KEYBOARD and keyboard is not None:
            try:
                keyboard.unhook_all_hotkeys()
            except Exception:
                pass
        self.root.after(50, self.root.destroy)

    # ---------------- מעטפת האפליקציה: כותרת, מסכים, ניווט תחתון ----------------
    NAV_ITEMS = (("home", "🏠", "בית"), ("first_aid", "🩹", "עזרה ראשונה"), ("map", "🗺️", "מפה"),
                 ("community", "🤝", "קהילה"), ("circle", "👨‍👩‍👧", "מעגל הביטחון"), ("profile", "👤", "פרופיל"))

    def _build_shell(self):
        # פס מותג נייבי (הזהות: נייבי / לבן / כחול): מגן וקטורי חד + שם, ומימין לשמאל - פעמון ההתראות
        header = tk.Frame(self.root, bg=T.NAVY)
        header.pack(fill="x")
        brand = tk.Frame(header, bg=T.NAVY)
        brand.pack(side="right", padx=20, pady=10)
        logo = tk.Label(brand, bg=T.NAVY, bd=0)
        if T.HAS_PIL:
            s = T.px(34)
            T.set_image(logo, ("shield", s, T.BLUE, T.NAVY), lambda: T.shield_pil(s, T.BLUE, T.NAVY))
        else:
            logo.configure(text="🛡️", fg=T.ON_NAVY, font=T.F(18))
        logo.pack(side="right", padx=(10, 0))
        words = tk.Frame(brand, bg=T.NAVY)
        words.pack(side="right")
        tk.Label(words, text="LifeGuard", font=T.F(19, "bold"), fg=T.ON_NAVY, bg=T.NAVY).pack(anchor="e")
        tk.Label(words, text="Safe Steps. Safer Community.", font=T.F(10), fg=T.ON_NAVY_MUTED,
                 bg=T.NAVY).pack(anchor="e")
        self.bell_btn = T.PillButton(header, text="🔔", command=self._open_bell, fill=T.NAVY_2, fg=T.ON_NAVY,
                                     size=13, bold=True, padx=14, pady=6)
        self.bell_btn.pack(side="left", padx=18)

        self.content = tk.Frame(self.root, bg=T.BG)
        # הודעה צפה (HUD): גלולה חלקה שמחליקה פנימה (מבוטל בהפחתת תנועה)
        self.toast = T.Chip(self.root, "", T.NAVY_2, T.ON_NAVY, size=12, padx=20, pady=11, radius=T.px(14))
        self.toast.configure(wraplength=700, justify="right")
        # סרגל לשוניות תחתון בסגנון iOS: משטח בהיר, קו עליון דק, הלשונית הפעילה בכחול עם פס סימון
        nav = tk.Frame(self.root, bg=T.NAV_BG)
        nav.pack(side="bottom", fill="x")
        tk.Frame(self.root, bg=T.BORDER, height=1).pack(side="bottom", fill="x")
        self.content.pack(fill="both", expand=True)
        self.screens = {
            "home": HomeScreen(self.content, self),
            "map": MapScreen(self.content, self),
            "community": CommunityScreen(self.content, self),
            "circle": SafetyCircleScreen(self.content, self),
            "profile": ProfileScreen(self.content, self),
            # עזרה ראשונה אופליין: שורת חיפוש, בלי שרת/חשבון/אינטרנט (first_aid/)
            "first_aid": FirstAidScreen(self.content, self),
        }
        self.nav_buttons, self._nav_marks = {}, {}
        for key, icon, label in self.NAV_ITEMS:
            cell = tk.Frame(nav, bg=T.NAV_BG)
            cell.pack(side="right", fill="x", expand=True)
            mark = tk.Frame(cell, bg=T.NAV_BG, height=3)
            mark.pack(fill="x", padx=28)
            b = tk.Button(cell, text=f"{icon}\n{label}", font=T.F(10, "bold"), bg=T.NAV_BG, fg=T.TEXT_MUTED,
                          bd=0, cursor="hand2", activebackground=T.hover_of(T.NAV_BG), activeforeground=T.BLUE,
                          takefocus=True, highlightthickness=2, highlightcolor=T.FOCUS,
                          highlightbackground=T.NAV_BG, pady=6, command=lambda k=key: self.show_screen(k))
            T.bind_activate(b, lambda k=key: self.show_screen(k))
            b.pack(fill="x", pady=(2, 6))
            b.bind("<Enter>", lambda e, w=b: w.configure(bg=T.hover_of(T.NAV_BG)), add="+")
            b.bind("<Leave>", lambda e, w=b: w.configure(bg=T.NAV_BG), add="+")
            self.nav_buttons[key] = b
            self._nav_marks[key] = mark
        self.current_screen = None
        self.show_screen("home")

    def _open_bell(self):
        """התראות חירום קודמות להזמנות; אם יש רק הזמנות - ישר למעגל הביטחון."""
        invites = len(((self._reach or {}).get("trusted") or {}).get("received_invitations") or [])
        self.show_screen("circle" if invites and not self._pending_alerts else "community")

    def show_screen(self, name):
        if self.current_screen == name:
            return
        if self.current_screen:
            self.screens[self.current_screen].pack_forget()
        self.current_screen = name
        screen = self.screens[name]
        screen.pack(fill="both", expand=True)
        for key, b in self.nav_buttons.items():
            b.configure(fg=T.BLUE if key == name else T.TEXT_MUTED)
            self._nav_marks[key].configure(bg=T.BLUE if key == name else T.NAV_BG)
        if hasattr(screen, "on_show"):
            screen.on_show()

    def show_toast(self, text, ms=6000, level="info"):
        bg = {"info": T.NAVY_2, "ok": T.GREEN, "warn": T.YELLOW, "critical": T.SOS_FILL}.get(level, T.NAVY_2)
        self.toast.configure(text=text, bg=bg, fg=T.on(bg))
        if getattr(self, "_toast_after", None):
            self.root.after_cancel(self._toast_after)
        # החלקה קצרה מלמעלה (240ms) - מידע משני בלבד; בהפחתת תנועה מופיע מיד
        self.toast.lift()
        T.animate(self.toast, T.MOTION_STD, lambda t: self.toast.place(relx=0.5, y=int(64 + 22 * t), anchor="n"))
        self._toast_after = self.root.after(ms, self._hide_toast)

    def _hide_toast(self):
        try:
            if self.toast.winfo_exists():
                self.toast.place_forget()
        except tk.TclError:
            pass

    # ---------------- הגדרות משתמש מקומיות ----------------
    def get_setting(self, key, default=None):
        try:
            return incident_store.get_setting(self.username, key, default)
        except Exception:
            return default

    def set_setting(self, key, value):
        try:
            incident_store.set_setting(self.username, key, value)
        except Exception:
            pass

    # ---------------- שרת LifeGuard: התחברות, זרם התראות, נוכחות ----------------
    def connect_server(self, password, on_done=None):
        if not password:
            if on_done:
                on_done(False, "נדרשת סיסמה")
            return

        def work():
            # מצב מקומי: אם השרת לא רץ - מפעילים אותו ברקע (במקום "לא מחובר" בלי הסבר)
            import local_server
            up, why = local_server.ensure_running(config.SERVER_URL, log=lambda t: self._post(self._on_log, t))
            if not up:
                raise backend_client.BackendUnavailable(why)
            client = backend_client.BackendClient(config.SERVER_URL)
            mode, _ = client.login_or_register(self.username, password, self.display_name)
            if self.get_setting("background_agent", "1") == "1":
                # סשן נפרד (ניתן לביטול בנפרד) לסוכן הרקע: התראות חירום גם כשהאפליקציה סגורה
                try:
                    if agent_bridge.provision(config.SERVER_URL, self.username, password):
                        agent_bridge.install_autostart()
                        agent_bridge.ensure_agent_running()
                except Exception as exc:  # noqa: BLE001 - לא מונע חיבור לשרת
                    self._post(self._on_log, f"⚠️ סוכן הרקע לא הופעל: {exc}")
            return client, mode

        def done(res):
            client, mode = res
            self.client = client
            self.gateway.set_client(client)
            self.server_error = None
            self._password = None
            self.set_setting("server_account", "1")   # מעכשיו הסיסמה משותפת לשרת (החלפה רק דרכו)
            self._on_log("📡 מחובר לשרת LifeGuard" + (" (נוצר חשבון שרת)" if mode == "registered" else ""))
            client.start_stream(lambda n: self._post(self._on_server_notification, n),
                                lambda st: self._post(self._on_stream_state, st))
            self._sync_circle_on_connect()
            target, self._open_target = self._open_target, {}
            if target.get("incident"):
                self.open_alert(target["incident"])
            elif target.get("escort"):
                self.show_screen("home")
            self.push_presence_now()
            self._refresh_reach()
            self._update_server_chip()
            # הבדיקה בהפעלה רצה לפני שהחיבור הסתיים - מריצים שוב כדי שהבאנר ישקף את המצב האמיתי
            self.root.after(1500, self._run_startup_health_check)
            self.root.after(12000, self._readiness_reminder)
            self.root.after(5000, self._privacy_sync)
            self.screens["home"].refresh_extras()
            if on_done:
                on_done(True, "✅ מחובר לשרת")

        def err(exc):
            self.server_error = getattr(exc, "message", str(exc))
            self._update_server_chip()
            self._on_log(f"❗ לא מחובר לשרת LifeGuard: {self.server_error}")
            if on_done:
                on_done(False, f"❌ {self.server_error}")
            if isinstance(exc, backend_client.BackendUnavailable) and self._password:
                self.root.after(15000, lambda: self.client is None and self.connect_server(self._password))

        run_bg(self, work, done, err)

    PRIVACY_SYNC_MS = 30_000

    def _privacy_sync(self):
        """הקלטות חירום מורשות ואירועי ביקורת מהמחשב -> שרת (תור מקומי, מנסה שוב עד שיש חיבור)."""
        if self.client is None:
            return
        import privacy_sync
        run_bg(self, lambda: privacy_sync.sync(self.client, self.engine.vault, self.username,
                                               log=lambda t: self._post(self._on_log, t)),
               lambda r: None, lambda e: None)
        self.root.after(self.PRIVACY_SYNC_MS, self._privacy_sync)

    def _open_privacy(self):
        from privacy_ui import PrivacyWindow
        self._open_single("privacy", lambda: PrivacyWindow(self.root, self))

    def _sync_circle_on_connect(self):
        """אחרי חיבור: טלפון (להתאמת הזמנות), קוד הזמנה שהוזן בהרשמה, והזמנת אנשי קשר מקומיים ישנים.
        המצב עצמו (מי מחובר) נטען תמיד מהשרת - לא מהמחשב הזה."""
        contacts = auth_module.get_contacts(self.username)
        phone = auth_module.get_phone(self.username)
        code = self.get_setting("pending_invite_code", "") or ""
        try:
            invited = set(json.loads(self.get_setting("contacts_invited", "[]") or "[]"))
        except ValueError:
            invited = set()

        def work():
            notes, preview = [], None
            if phone:
                try:
                    self.client.set_phone(phone)
                except backend_client.BackendError as exc:
                    notes.append(f"⚠️ מספר הטלפון לא נשמר בשרת: {exc.message}")
            if code:
                try:
                    preview = self.client.preview_code(code)
                except backend_client.BackendError as exc:
                    if isinstance(exc, backend_client.BackendUnavailable):
                        raise
                    notes.append(f"⚠️ קוד ההזמנה מההרשמה לא בתוקף: {exc.message}")
                    preview = False
            # אנשי קשר מהטופס/גרסה קודמת -> הזמנה בשרת, *פעם אחת בלבד* לכל איש קשר
            # (אחרת מי שדחה/שההזמנה אליו בוטלה היה מקבל הזמנה חוזרת בכל כניסה)
            for c in contacts:
                acc = (c.get("account") or "").strip().lower()
                if not acc or acc in invited:
                    continue
                if "@" in acc:
                    notes.append(f"ℹ️ איש הקשר {c.get('name')} מוגדר לפי אימייל - התראות באימייל הוסרו. "
                                 "הזמן/י אותו במעגל הביטחון לפי שם משתמש או טלפון.")
                    invited.add(acc)
                    continue
                try:
                    self.client.invite(acc)
                    notes.append(f"📨 נשלחה הזמנת קשר ל-@{acc} (ממתין לאישור שלו/ה)")
                    invited.add(acc)
                except backend_client.BackendError as exc:
                    if exc.code in ("duplicate_invitation", "already_connected", "declined_recently"):
                        invited.add(acc)
                    else:
                        notes.append(f"⚠️ {c.get('name')} (@{acc}): {exc.message}")
            return notes, preview, sorted(invited)

        def done(res):
            notes, preview, invited_now = res
            self.set_setting("contacts_invited", json.dumps(invited_now))
            for n in notes:
                self._on_log(n)
            if preview is not None:
                self.set_setting("pending_invite_code", "")
            if preview:  # הקוד בתוקף: מציגים מי מזמין - המשתמש מאשר בעצמו
                circle = self.screens["circle"]
                circle.code_var.set(code)
                self.show_screen("circle")
                circle.check_code()
        run_bg(self, work, done, lambda e: self._on_log(f"⚠️ סנכרון מעגל הביטחון נכשל: {e}"))

    def push_presence_now(self):
        if self.client is None:
            return

        def work():
            loc = location_module.get_location()
            if loc.get("available"):
                self.client.update_presence(loc)
            return loc
        run_bg(self, work, lambda loc: None, lambda e: None)

    def _presence_loop(self):
        if not self._alive:
            return
        if self.engine.state == State.IDLE:
            self.push_presence_now()
        self.root.after(int(config.PRESENCE_UPDATE_SECONDS * 1000), self._presence_loop)

    def _refresh_reach(self):
        if self.client is None:
            return
        radius = max(2.0, float(self.get_setting("safety_radius_km", "1") or 1))

        def work():
            return self.client.community_summary(radius)
        run_bg(self, work, self._apply_reach, lambda e: None)

    def _apply_reach(self, s):
        self._reach = s
        connected = len(s["trusted"]["my_contacts"])
        vols = len(s.get("volunteers") or [])
        invites = len(s["trusted"].get("received_invitations") or [])
        if connected:
            text, color = f"SOS יגיע אל: {connected} אנשי קשר מחוברים · {vols} מתנדבים זמינים בקרבתך", T.GREEN
        elif vols:
            text, color = (f"SOS יגיע אל {vols} מתנדבים זמינים בקרבתך · אין אנשי קשר מחוברים - "
                           "הזמן/י במעגל הביטחון", T.YELLOW)
        else:
            text, color = "❗ אין כרגע מי שיקבל SOS ממך - הזמן/י אנשי קשר במעגל הביטחון", T.RED
        self.reach_label.configure(text=text, fg=color)
        count = invites + len(self._pending_alerts)
        self.bell_btn.configure(text=f"🔔 {count}" if count else "🔔")

    def _on_stream_state(self, st):
        self._update_server_chip()

    def _update_server_chip(self):
        if not hasattr(self, "server_chip"):
            return
        if self.client is None:
            text, lvl = "📡 שרת: לא מחובר", "critical"
            self.reach_label.configure(text="❗ לא מחובר לשרת LifeGuard - SOS לא יגיע לאף אחד. ראה/י פרופיל.",
                                       fg=T.RED)
        elif self.client.stream_state.get("connected"):
            text, lvl = "📡 שרת: מחובר · התראות בזמן אמת", "ok"
        else:
            text, lvl = "📡 שרת: מתחבר מחדש...", "warn"
        self.server_chip.configure(text=f" {text} ", fg=T.STATUS_COLORS[lvl], bg=T.STATUS_BG[lvl])
        prof = self.screens.get("profile")
        if prof is not None:
            prof.update_server()

    def _on_server_notification(self, n):
        ntype, payload = n["type"], n.get("payload") or {}
        quiet = self.engine.state == State.SILENT_TRACKING or self.root.state() == "withdrawn"
        if ntype == "incident_new":
            iid = payload.get("id")
            if payload.get("owner") == self.username:
                return
            self._pending_alerts.add(iid)
            if not quiet:
                # ring=True: את/ה איש הקשר שמצלצלים אליו עכשיו (הקרוב ביותר) - צפצוף חוזר עד מענה.
                # ring=False: עדכון שקט (מישהו אחר כבר מטפל) - בלי צפצוף.
                ringing = payload.get("ring", True)
                self.open_alert(iid, ringing=ringing)
                from app_screens import EMERGENCY_TYPE_LABELS
                dist = f" · {payload['distance_km']:.1f} ק\"מ ממך" if payload.get("distance_km") else ""
                if payload.get("my_role") == "helper":      # שיחת תמיכה / הזעקת רשויות - לא הגעה למקום
                    liaison = payload.get("helper_kind") == "authority_liaison"
                    self._os_notify("👮 מבקשים ממך להזעיק רשויות" if liaison else "💬 מישהו צריך לדבר",
                                    f"{payload.get('helper_kind_label', '')} · פתח/י את LifeGuard", urgent=liaison, tag=iid)
                    return self._refresh_reach()
                title = (f"🚨 {payload.get('owner_display', '')} צריך/ה עזרה" if ringing else
                         f"ℹ️ עדכון: {payload.get('owner_display', '')} באירוע חירום - מישהו כבר מטפל")
                self._os_notify(title, f"{EMERGENCY_TYPE_LABELS.get(payload.get('emergency_type'), 'מצב חירום')}{dist} · "
                                "פתח/י את LifeGuard", urgent=ringing, tag=iid)
        elif ntype in ("incident_update", "incident_closed"):
            iid = payload.get("incident_id")
            win = self._alert_windows.get(iid)
            if win is not None and win.winfo_exists():
                if payload.get("event") == "ring_stopped":
                    win.stop_ringing("עברנו לאיש הקשר הבא. אפשר עדיין לענות ולקבל את האירוע.")
                win.refresh()
            sw = self.sos_window
            if (sw is not None and getattr(sw, "chat", None) is not None and iid
                    and iid == getattr(sw, "_server_id", None) and payload.get("event") in ("message", "read")):
                sw.chat.refresh()
            if (sw is not None and iid and iid == getattr(sw, "_server_id", None)
                    and payload.get("event") in ("helper", "liaison") and hasattr(sw, "refresh_helpers")):
                sw.refresh_helpers()
            supp = getattr(self, "_support_window", None)
            if supp is not None and supp.winfo_exists() and iid == supp.iid:
                supp.refresh()
            if ntype == "incident_closed":
                self._pending_alerts.discard(iid)
                windows_notify.remove((iid or "")[-16:])  # לא משאירים במרכז ההודעות אירוע שנסגר
                if payload.get("text") and not quiet:
                    self.show_toast("ℹ️ " + payload["text"])
        elif ntype in ("relationship_invite", "relationship_update", "relationship_removed", "test", "info"):
            # המסך נטען מחדש מהשרת גם כשהשינוי נעשה במכשיר אחר / ע"י הצד השני
            if ntype.startswith("relationship") and self.current_screen == "circle":
                self.screens["circle"].refresh()
            text = None if quiet else self._circle_toast(ntype, payload)
            if text:
                self.show_toast(text, 8000)
                if ntype.startswith("relationship") or ntype == "test":
                    self._os_notify("LifeGuard · מעגל הביטחון", text)
        elif ntype.startswith("escort_"):
            self._on_escort_notification(ntype, payload, quiet)
        elif ntype == "national_mode":
            home = self.screens.get("home")
            if home is not None and hasattr(home, "national"):
                home.national.refresh()
            if not quiet and payload.get("active"):
                text = f"⚠️ {payload.get('title', 'מצב חירום לאומי')}" + (f" - {payload['text']}" if payload.get("text") else "")
                self.show_toast(text, 15000, level="critical")
                self._os_notify("⚠️ LifeGuard - חירום לאומי", text, urgent=True, tag="national")
        elif ntype == "readiness_check" and not quiet:
            self.show_toast(f"🧪 {payload.get('from_display')} הריץ/ה בדיקת מוכנות - האפליקציה שלך אישרה קבלה. "
                            "זו לא קריאת חירום.", 8000)
            self._os_notify("🧪 בדיקת מוכנות LifeGuard", f"מ{payload.get('from_display')} - זו לא קריאת חירום")
        self._refresh_reach()
        if self.current_screen == "community":
            self.screens["community"].refresh()

    def _on_escort_notification(self, ntype, p, quiet):
        """ליווי הביתה: עוקבים מקבלים התחלה/עדכונים/התראה; בעל הליווי - 'הכל בסדר?' כשהזמן עבר."""
        home = self.screens.get("home")
        if home is not None:
            home.escort_watch.refresh()
        if quiet:
            return
        if ntype == "escort_started":
            dest = f" ל{p['destination']}" if p.get("destination") else ""
            text = f"🚶 {p.get('owner_display')} בדרך{dest} - את/ה מלווה. תקבל/י התראה אם לא יאשר/תאשר הגעה."
            self.show_toast(text, 8000)
            self._os_notify("🚶 ליווי הביתה", text)
        elif ntype == "escort_update" and p.get("text"):
            # נסיעה בטוחה: חריגה (anomaly) = אזהרה; "אישר/ה שהכל בסדר" / "מסלול חלופי" / "מתעכב/ת" = מידע
            level = {"arrived": "ok", "signal_back": "ok", "signal_lost": "warn", "anomaly": "warn",
                     "anomaly_cleared": "ok", "unconfirmed_arrival": "warn"}.get(p.get("event"), "info")
            self.show_toast(p["text"], 12000 if p.get("event") == "signal_lost" else 6000, level=level)
            if p.get("event") in ("arrived", "signal_lost", "signal_back", "anomaly", "unconfirmed_arrival"):
                self._os_notify("LifeGuard", p["text"], urgent=p.get("event") in ("signal_lost", "anomaly"))
        elif ntype == "escort_overdue":
            # הליווי שלי: הזמן עבר לפי השרת. הטיימר המקומי מטפל גם הוא; זו התראה למקרה שהחלון מוסתר
            self.show_toast("⏰ " + p.get("text", ""), 15000, level="warn")
            self._os_notify("⏰ הליווי הסתיים - הכל בסדר?", p.get("text", ""), urgent=True, tag=p.get("escort_id", "esc"))
        elif ntype == "escort_alarm" and p.get("text"):
            self.show_toast(p["text"], 15000, level="critical")
            if p.get("incident_id"):
                self.open_alert(p["incident_id"])

    def _app_in_foreground(self):
        try:
            return self.root.state() not in ("iconic", "withdrawn") and self.root.focus_displayof() is not None
        except (tk.TclError, KeyError):
            return False

    def _os_notify(self, title, body, urgent=False, tag="lg"):
        """התראת Windows - רק כשהאפליקציה לא מול המשתמש (ממוזערת/ברקע), ורק על אירוע שהגיע מהשרת.
        לא נקרא במעקב שקט/כפייה (הקוראים בודקים quiet)."""
        if self._app_in_foreground() or self.get_setting("os_notifications", "1") != "1":
            return
        windows_notify.notify(title, body, urgent=urgent, tag=(tag or "lg")[-16:])

    def _circle_toast(self, ntype, payload):
        """טקסט התראה - נבנה רק מאירוע שהשרת כבר שמר (ההתראה נוצרת בשרת אחרי ה-commit)."""
        if ntype == "relationship_invite":
            return "📨 " + payload.get("text", "") + " (מעגל הביטחון)"
        if ntype == "relationship_removed":
            if payload.get("by") == self.username:
                return None
            if payload.get("owner") == self.username:
                return f"ℹ️ {payload.get('by_display')} הפסיק/ה להיות איש קשר לחירום שלך"
            return f"ℹ️ {payload.get('by_display')} הסיר/ה אותך מאנשי הקשר לחירום שלו/ה"
        if ntype == "relationship_update":
            st = payload.get("status")
            if payload.get("resent"):
                return None
            if st == "connected":
                if payload.get("owner") == self.username:
                    return f"✅ {payload.get('contact_display')} אישר/ה - מחובר/ת עכשיו כאיש קשר לחירום"
                return f"✅ את/ה עכשיו איש קשר לחירום של {payload.get('owner_display')}"
            if st == "awaiting_confirmation" and payload.get("contact") != self.username:
                return (f"❓ {payload.get('contact_display')} אישר/ה הזמנה שנשלחה לטלפון - אשר/י במעגל הביטחון "
                        "שזה באמת הוא/היא")
            if st == "declined" and payload.get("contact_display") and payload.get("contact_display") != self.display_name:
                return f"⚠️ {payload.get('contact_display')} דחה/תה את ההזמנה"
            if st == "expired":
                return "⌛ תוקף של הזמנה פג - אפשר לשלוח אותה שוב ממעגל הביטחון"
            return None
        if ntype == "test":
            return f"🧪 התקבלה הודעת בדיקה מ-{payload.get('from_display')} (האפליקציה שלך אישרה קבלה)"
        return f"ℹ️ {payload.get('from_display')}: {payload.get('text', '')}"

    def _show_hazard_alert(self, kind, alert):
        """חלון אחד לכל אירוע: זיהוי חוזר של אותו אירוע מעדכן את החלון הקיים, לא פותח חדש."""
        if self.root.state() == "withdrawn":
            return                              # מצב כיבוי מדומה / שקט - שום דבר לא קופץ על המסך
        import hazard_alert_ui
        win = self._hazard_windows.get(alert["id"])
        if win is not None and win.winfo_exists():
            win.refresh(alert, updated=(kind == "update"))
            win.lift()
            return
        win = hazard_alert_ui.HazardAlertWindow(self.root, self, alert)
        self._hazard_windows = {k: w for k, w in self._hazard_windows.items() if w.winfo_exists()}
        self._hazard_windows[alert["id"]] = win
        self._os_notify("⚠️ LifeGuard - סכנה אפשרית", f"{alert.get('label_he') or alert['category']}. "
                        "פתח/י את האפליקציה לבחירת פעולה.", urgent=False, tag="hazard")

    def _ask_wellness(self, reason, deadline, answer):
        """חלון 'הכל בסדר?' בולט, עם ספירה לאחור. לא מוצג כשהחלון מוסתר (מצב כיבוי מדומה/שקט)."""
        if self.root.state() == "withdrawn":
            return
        win = tk.Toplevel(self.root)
        win.title("LifeGuard | הכל בסדר?")
        win.configure(bg=T.BG)
        win.attributes("-topmost", True)
        win.geometry("460x300")
        tk.Label(win, text="הכל בסדר?", font=T.F(26, "bold"), fg=T.RED, bg=T.BG).pack(pady=(18, 4))
        tk.Label(win, text=f"{reason}. אם לא תענה/י - תישלח קריאת חירום.", font=T.F(12), fg=T.TEXT, bg=T.BG,
                 wraplength=420).pack()
        left = tk.Label(win, text="", font=T.F(30, "bold"), fg=T.RED, bg=T.BG)
        left.pack(pady=6)
        row = tk.Frame(win, bg=T.BG)
        row.pack(pady=8)

        def done(ok):
            answer(ok)
            if win.winfo_exists():
                win.destroy()
        T.big_button(row, "✅ אני בסדר", lambda: done(True), bg=T.GREEN, size=14).pack(side="right", padx=6)
        T.big_button(row, "🚨 אני צריך/ה עזרה", lambda: done(False), bg=T.SOS_FILL, size=14).pack(side="right", padx=6)
        win.protocol("WM_DELETE_WINDOW", lambda: None)      # סגירה בטעות לא נחשבת "בסדר"

        def tick():
            if not win.winfo_exists():
                return
            rem = int(round(deadline - time.time()))
            if rem <= 0 or self.engine.wellness.pending is None:
                win.destroy()
                return
            left.configure(text=str(rem))
            silent = bool((self.engine.wellness.pending or {}).get("silent"))   # בדיקה קולית: בלי צפצופים
            if rem % 5 == 0 and not silent:
                try:
                    import winsound
                    winsound.MessageBeep(winsound.MB_ICONEXCLAMATION)
                except Exception:
                    pass
            win.after(500, tick)
        tick()
        self._os_notify("❓ LifeGuard - הכל בסדר?", reason + ". פתח/י את האפליקציה כדי לענות.", urgent=True, tag="wellness")
        self._wellness_window = win

    def open_support(self):
        """'צריך/ה לדבר עם מישהו?' - חלון אחד; אם כבר פתוח מקדימים אותו."""
        win = getattr(self, "_support_window", None)
        if win is not None and win.winfo_exists():
            win.lift()
            return
        import support_ui
        self._support_window = support_ui.SupportWindow(self.root, self)

    def open_alert(self, incident_id, ringing=False):
        win = self._alert_windows.get(incident_id)
        if win is not None and win.winfo_exists():
            win.lift()
            if ringing:
                win.start_ringing()
            return
        self._alert_windows[incident_id] = AlertWindow(self.root, self, incident_id, alert_sound=ringing)

    def _tick_indicators(self):
        """חיווי הקלטה/האזנה אמיתי (מבוסס מצב המנוע בפועל), כל 2 שניות."""
        if not self._alive:
            return
        try:
            listener = self.engine._voice_listener
            listening = bool(listener is not None and getattr(listener, "_running", False))
            if self.engine.state == State.ACTIVE_SOS:
                text, lvl = "● מקליט - אירוע פעיל", "critical"
            elif listening or self.live_monitor_on:
                # במעקב שקט מוצג בדיוק כמו במצב רגיל - אין רמז להקלטה
                text, lvl = "🎙️ האזנה פעילה", "ok"
            else:
                text, lvl = "⏸ המיקרופון לא בשימוש", "not_verified"
            self.recording_label.configure(text=f" {text} ", fg=T.STATUS_COLORS[lvl], bg=T.STATUS_BG[lvl])
        except tk.TclError:
            return
        if not getattr(self, "_presence_started", False) and self.client is not None:
            self._presence_started = True
            self.root.after(int(config.PRESENCE_UPDATE_SECONDS * 1000), self._presence_loop)
        if not hasattr(self, "_reach_tick") or time.time() - self._reach_tick > 60:
            self._reach_tick = time.time()
            self._refresh_reach()
            if self.current_screen == "home" and self.client is not None:
                self.screens["home"].refresh_extras()
        self.root.after(2000, self._tick_indicators)

    def _readiness_reminder(self):
        """פעם בהפעלה: אם בדיקת המוכנות האחרונה ישנה מ-READINESS_REMINDER_DAYS - תזכורת עדינה."""
        if self.client is None or self.engine.state != State.IDLE:
            return
        client = self.client

        def work():
            circle = client.circle()
            return client.readiness() if circle["my_contacts"] else None

        def done(r):
            if r is not None and self.screens["home"].readiness.is_stale(r):
                self.show_toast("🧪 עבר יותר מחודש מבדיקת המוכנות האחרונה - כדאי לוודא שאנשי הקשר שלך מקבלים "
                                "התראות (בית ← בדיקת מוכנות)", 10000, level="warn")
        run_bg(self, work, done, lambda e: None)

    def _toggle_live_monitor(self):
        self._set_live_monitor(not self.live_monitor_on)

    def _set_live_monitor(self, on):
        self.live_monitor_on = on
        if on:
            self.engine.start_live_monitor()
            self.live_monitor_btn.configure(text="■ השהה מד רעש", bg=T.CARD_BG_ALT)
        else:
            self.engine.stop_live_monitor()
            self.live_monitor_btn.configure(text="▶ הפעל מד רעש", bg=T.CARD_BG_ALT)

    def _set_voice_trigger(self, on):
        self.voice_trigger_on = on
        if on:
            self.engine.start_voice_trigger()
        else:
            self.engine.stop_voice_trigger()
        if getattr(self, "voice_trigger_btn", None) is not None:
            if on:
                self.voice_trigger_btn.configure(text="🎙️ פקודת קול: פעילה", bg=T.LIGHT_BLUE, fg=T.LINK)
            else:
                self.voice_trigger_btn.configure(text="🎙️ פקודת קול: מושהית", bg=T.CARD_BG_ALT, fg=T.TEXT_MUTED)

    def _toggle_voice_trigger(self):
        self._set_voice_trigger(not self.voice_trigger_on)

    def _toggle_deterrent_mode(self):
        self.deterrent_on = not self.deterrent_on
        if self.deterrent_on:
            self.engine.start_voice_warning_standalone()
            self.deterrent_btn.configure(text="■ עצור הרתעה", bg=T.ORANGE, fg=T.on(T.ORANGE))
        else:
            self.engine.stop_voice_warning_standalone()
            self.deterrent_btn.configure(text="📢 הרתעה קולית", bg=T.CARD_BG_ALT, fg=T.LINK)

    def _run_test_broadcast(self):
        self.engine.send_test_broadcast()

    # ---------------- טיימר בטיחות ----------------
    def _open_safety_timer_dialog(self):
        if self.engine.state != State.IDLE:
            self._on_log("⚠️ אי אפשר להפעיל טיימר באמצע אירוע")
            return
        SafetyTimerDialog(self.root, self.engine)

    def _confirm_safe_arrival(self):
        self.engine.confirm_safe_arrival()

    def _extend_safety_timer(self, minutes):
        self.engine.extend_safety_timer(minutes)

    def _cancel_safety_timer(self):
        self.engine.cancel_safety_timer()

    def _on_safety_timer_tick(self, remaining, is_warning):
        self._post(self._update_safety_timer_ui, remaining, is_warning)

    def _update_safety_timer_ui(self, remaining, is_warning):
        bar = getattr(self, "safety_timer_progress", None)
        if remaining is None:
            self._timer_total = None
            self.safety_timer_status_label.configure(text="לא פעיל", fg=T.TEXT_SECONDARY)
            self.safety_timer_actions.pack_forget()
            if bar is not None:
                bar.pack_forget()
            self.safety_timer_btn.pack(side="right")
            return
        mins, secs = divmod(int(remaining), 60)
        color = T.RED if is_warning else T.GREEN
        prefix = "⚠️ " if is_warning else "⏳ "
        self.safety_timer_status_label.configure(text=f"{prefix}{mins:02d}:{secs:02d} נותרו", fg=color)
        self.safety_timer_btn.pack_forget()
        self.safety_timer_actions.pack(side="right")
        if bar is not None:
            # פס זמן שנותר (מחליק בין עדכונים; בלי קשר למסלול ה-SOS)
            total = max(float(remaining), getattr(self, "_timer_total", None) or 0.0)
            self._timer_total = total
            if not bar.winfo_ismapped():
                bar.pack(fill="x", pady=(8, 0), before=self.safety_timer_holder)
            bar.set(remaining / total if total else 0, color=T.RED if is_warning else T.BLUE)

    # ---------------- מספר חירום מקומי ----------------
    def _refresh_emergency_number(self):
        """
        מזהה את המדינה לפי המיקום ומציג את מספר החירום הנכון. רץ ברקע כדי לא לעכב את
        פתיחת החלון (זיהוי המיקום דורש קריאת רשת).
        """
        def _work():
            try:
                loc = location_module.get_location()
                numbers = emergency_numbers_module.get_emergency_numbers(loc.get("country_code"))
                self._post(self._update_emergency_number_ui, numbers)
            except Exception:
                fallback = emergency_numbers_module.get_emergency_numbers(None)
                self._post(self._update_emergency_number_ui, fallback)
        threading.Thread(target=_work, daemon=True).start()

    def _update_emergency_number_ui(self, numbers):
        self.emergency_numbers = numbers
        primary = emergency_numbers_module.format_primary_number(numbers)
        summary = emergency_numbers_module.format_summary_line(numbers)
        self.emergency_number_label.configure(text=primary)
        if numbers.get("is_fallback"):
            detail = f"{summary}\n⚠️ מדינה לא זוהתה - 112 הוא ברירת מחדל בינלאומית"
        else:
            detail = f"{numbers['name']} · {summary}"
        self.emergency_detail_label.configure(text=detail)

    def _open_settings(self):
        if self.engine.state != State.IDLE:
            self._on_log("⚠️ אי אפשר לפתוח הגדרות באמצע אירוע/ספירה - חכה/י שהמצב יחזור ל'ממתין'")
            return
        SettingsWindow(self.root, self.engine, self.username)

    def _register_hotkey(self):
        if not HAS_KEYBOARD or keyboard is None:
            self._on_log("[INFO] חבילת keyboard לא מותקנת - טריגר גלובלי מושבת. pip install keyboard.")
            return
        try:
            keyboard.add_hotkey(config.TRIGGER_HOTKEY, lambda: self.engine.trigger(source="hotkey"))
            keyboard.add_hotkey(config.PANIC_HOTKEY, lambda: self.engine.trigger(force_panic=True, source="hotkey"))
            self._on_log(f"[INFO] קיצורים פעילים: SOS={config.TRIGGER_HOTKEY} | PANIC={config.PANIC_HOTKEY}")
        except Exception as e:
            self._on_log(f"[WARN] לא ניתן לרשום קיצור מקלדת גלובלי: {e}")

    # ---------------- Callbacks מה-engine (רצים ב-thread אחר!) ----------------
    def _on_log(self, message):
        self._post(self._append_log, message)

    def _append_log(self, message):
        self.log_text.configure(state="normal")
        self.log_text.insert("end", message + "\n", "rtl")
        self.log_text.see("end")
        self.log_text.configure(state="disabled")

    def _on_state_change(self, new_state: State):
        self._post(self._handle_state_change, new_state)

    def _handle_state_change(self, new_state: State):
        labels = {
            State.IDLE: ("●  ממתין", T.GREEN),
            State.SILENT_TRACKING: ("●  ממתין", T.GREEN),  # מכוון! זהה ל-IDLE, בלי שום רמז
            State.ASSESSING: ("●  🔍 בודק רמת סכנה...", T.BLUE),
            State.COUNTDOWN: ("●  ספירה לאחור - הזן סיסמה לביטול!", T.YELLOW),
            State.ACTIVE_SOS: ("●  🚨 SOS פעיל", T.RED),
            State.FEEDBACK: ("●  אירוע הסתיים - נדרש דירוג", T.BLUE),
        }
        text, color = labels[new_state]
        self.status_label.configure(text=text, fg=color)

        if new_state == State.COUNTDOWN:
            self._open_sos_window(countdown_mode=True)
        elif new_state == State.ACTIVE_SOS:
            self._open_sos_window(countdown_mode=False)
        elif new_state == State.FEEDBACK:
            self._close_sos_window()
            self._open_feedback_window()
        elif new_state == State.SILENT_TRACKING:
            # קריטי: סוגרים את מסך ה-SOS בדיוק כמו בביטול רגיל, ולא נוגעים בכלום אחר -
            # לא מפעילים מחדש ניטור חי/זיהוי קולי (המיקרופון כבר תפוס במעקב השקט),
            # ולא מציגים שום אינדיקציה שונה מ-IDLE רגיל.
            self._close_sos_window()
        elif new_state in (State.IDLE, State.ASSESSING):
            self._close_sos_window()
            if new_state == State.IDLE:
                self._set_live_monitor(True)  # חוזר לניטור חי אוטומטית אחרי כל אירוע
                self._set_voice_trigger(True)  # וגם להאזנה הקולית
                self._run_startup_health_check()  # מרעננים את באנר התקינות אחרי אירוע
            else:
                # נכנסים ל-ASSESSING (טריגר אמיתי הופעל) - מצב הרתעה עצמאי מתבטל אוטומטית
                self.deterrent_on = False
                self.deterrent_btn.configure(text="📢 הרתעה קולית", bg=T.CARD_BG_ALT, fg=T.LINK)

    # ---------------- חלונות משניים (singleton לכל סוג) ----------------
    def _open_single(self, key, factory):
        win = self._windows.get(key)
        if win is not None and win.winfo_exists():
            win.lift()
            win.focus_force()
            return win
        win = factory()
        self._windows[key] = win
        return win

    def _close_all_secondary_windows(self):
        for key, win in list(self._windows.items()):
            try:
                if win is not None and win.winfo_exists():
                    win.destroy()
            except tk.TclError:
                pass
            self._windows.pop(key, None)
        if self.community_window is not None:
            try:
                if self.community_window.winfo_exists():
                    self.community_window.destroy()
            except tk.TclError:
                pass
            self.community_window = None

    def _safety_context(self):
        """ההקשר שמנוע ההנחיות צריך - תמיד עדכני ברגע הפתיחה (מיקום/חיבור/אנשי קשר/תוכנית)."""
        loc = self.latest_location if isinstance(self.latest_location, dict) else {}
        desc = location_module.describe_location(loc) if loc else {"confidence": "unavailable"}
        conn = connectivity_module.status()
        try:
            plan = incident_store.get_safety_plan(self.username)
            meeting = plan.get("meeting_points", [])
        except Exception:
            meeting = []
        alerts_delivered = None
        if self.engine.state == State.ACTIVE_SOS:
            d = self.engine.get_delivery_status()
            if d.get("total") is not None:
                alerts_delivered = d.get("accepted", 0) > 0
        return {
            "alerts_delivered": alerts_delivered,
            "country_code": self.emergency_numbers.get("country_code"),
            "emergency_numbers": self.emergency_numbers,
            "location_confidence": desc.get("confidence"),
            "online": conn.get("online"),
            "meeting_points": meeting,
            "silent_mode": self.engine.state == State.SILENT_TRACKING,
        }

    def _open_safety_center(self, tab=None):
        win = self._open_single("safety", lambda: SafetyCenterWindow(self.root, self.username,
                                                                    self._safety_context, initial_tab=tab))
        if tab and hasattr(win, "select_tab"):
            win.select_tab(tab)

    def _open_history(self):
        self._open_single("history", lambda: IncidentHistoryWindow(self.root, self.username, client=self.client,
                                                                     vault=getattr(self.engine, "vault", None)))

    def _open_health(self):
        self._open_single("health", lambda: HealthWindow(self.root, self.engine, self.username))

    # ---------------- נגישות: סקאלת טקסט ----------------
    def _update_text_size_btn(self):
        order = ["normal", "large", "xlarge"]
        current = incident_store.get_setting(self.username, "text_scale", "normal")
        self.text_size_btn.configure(text=f"🔎 גודל טקסט: {T.SCALE_LABELS.get(current, 'רגיל')}")

    def _cycle_text_size(self):
        order = ["normal", "large", "xlarge"]
        current = incident_store.get_setting(self.username, "text_scale", "normal")
        nxt = order[(order.index(current) + 1) % len(order)] if current in order else "large"
        incident_store.set_setting(self.username, "text_scale", nxt)
        self._on_log(f"🔎 גודל הטקסט שונה ל'{T.SCALE_LABELS[nxt]}'. ייכנס לתוקף מלא בהפעלה הבאה של LifeGuard.")
        T.set_scale(nxt)
        self._update_text_size_btn()

    # ---------------- אינדיקטור חיבור ----------------
    def _poll_connectivity_ui(self):
        st = connectivity_module.status()
        self._update_connectivity_ui(st)
        # אין קליטה בזמן ליווי/טיימר בטיחות -> אחרי כמה דקות "הכל בסדר?" (גם בלי שרת - שאלה מקומית)
        if st.get("online") is not None and getattr(self.engine, "wellness", None) is not None:
            self.engine.wellness.on_connectivity(bool(st.get("online")), self.engine.is_safety_timer_active())
        try:
            self.root.after(5000, self._poll_connectivity_ui)
        except tk.TclError:
            pass

    def _update_connectivity_ui(self, st):
        if not hasattr(self, "connectivity_label") or not self.connectivity_label.winfo_exists():
            return
        online = st.get("online")
        text, lvl = {True: ("🌐 אינטרנט: מחובר", "ok"), False: ("🌐 אין אינטרנט", "critical")}.get(
            online, ("🌐 בודק חיבור...", "not_verified"))
        self.connectivity_label.configure(text=f" {text} ", fg=T.STATUS_COLORS[lvl], bg=T.STATUS_BG[lvl])

    # ---------------- בדיקת תקינות בהפעלה ----------------
    def _run_startup_health_check(self):
        def _work():
            try:
                results = health_module.run_all(self.engine, self.username, include_hardware=False)
                self._post(self._update_health_banner, results)
            except Exception:
                pass
        threading.Thread(target=_work, daemon=True).start()

    def _update_health_banner(self, results):
        if not hasattr(self, "health_banner"):
            return
        critical = [r for r in results if r["status"] == health_module.UNAVAILABLE and r["affects_emergency"]]
        if critical:
            names = ", ".join(r["name"] for r in critical[:3])
            self.health_banner.configure(
                text=f"❗ רכיב חירום לא זמין: {names}. לחץ/י כאן לפרטים ולדרך תיקון.")
            self.health_banner.pack(fill="x", pady=(8, 0))
        else:
            self.health_banner.pack_forget()

    # ---------------- מצב שליחה אמיתי ----------------
    def _on_delivery_update(self, status):
        self._post(self._apply_delivery_status, status)

    def _apply_delivery_status(self, status):
        if self.sos_window is not None and self.sos_window.winfo_exists():
            self.sos_window.update_delivery(status)

    def _open_community(self):
        self.show_screen("community")

    def _on_location_update(self, loc):
        self.latest_location = loc
        self._post(self._update_location_in_sos_window, loc)

    def _update_location_in_sos_window(self, loc):
        if self.sos_window is not None and self.sos_window.winfo_exists():
            self.sos_window.update_location(loc)

    def _on_route_update(self, route_info):
        self._post(self._update_route_in_sos_window, route_info)

    def _update_route_in_sos_window(self, route_info):
        if self.sos_window is not None and self.sos_window.winfo_exists():
            self.sos_window.update_route(route_info)

    def _on_photo_captured(self, filepath, kind):
        pass  # כבר מתועד ביומן ע"י engine.log - אין צורך בפעולה נוספת כרגע

    def _on_live_risk_update(self, score, level):
        self._post(lambda: self.idle_gauge.set_value(score, level, "רעש חי מהמיקרופון"))

    # ---------------- חלון SOS מלא-מסך ----------------
    def _open_sos_window(self, countdown_mode):
        if self.sos_window is None or not self.sos_window.winfo_exists():
            self.sos_window = SosWindow(self.root, self.engine, context_provider=self._safety_context, app=self)
        self.sos_window.set_mode(countdown_mode)

    def _close_sos_window(self):
        if self.sos_window is not None and self.sos_window.winfo_exists():
            self.sos_window.destroy()
        self.sos_window = None

    def _open_feedback_window(self):
        FeedbackWindow(self.root, self.engine)
        # בנוסף: אם מתנדב קיבל את האירוע - הצעה לדרג/לדווח (נתוני השרת בלבד)
        server_id = (self.engine.get_delivery_status() or {}).get("server_id")
        features_ui.offer_volunteer_feedback(self, server_id)

    def _open_medical(self):
        self._open_single("medical", lambda: features_ui.MedicalWindow(self.root, self))


class SafetyTimerDialog(tk.Toplevel):
    """דיאלוג הפעלת טיימר בטיחות: כמה זמן, לאן, ומה קורה בתום הזמן (רועש/שקט)."""

    def __init__(self, master, engine):
        super().__init__(master)
        self.engine = engine
        self.title("טיימר בטיחות")
        self.geometry("420x400")
        self.configure(bg=T.BG)
        self.attributes("-topmost", True)
        self.grab_set()

        tk.Label(self, text="⏳ טיימר בטיחות", font=T.F(14, "bold"),
                 fg=T.TEXT, bg=T.BG).pack(pady=(16, 2))
        tk.Label(self, text="אם לא תאשר/י הגעה בזמן - תופעל אזעקה אוטומטית",
                 font=T.F(10), fg=T.TEXT_MUTED, bg=T.BG).pack(pady=(0, 12))

        tk.Label(self, text="תוך כמה דקות אני אמור/ה להגיע?", font=T.F(9),
                 fg=T.TEXT_SECONDARY, bg=T.BG, anchor="e").pack(fill="x", padx=24)
        self.minutes_var = tk.StringVar(value=str(config.SAFETY_TIMER_DEFAULT_MINUTES))
        presets = tk.Frame(self, bg=T.BG)
        presets.pack(fill="x", padx=24, pady=(4, 2))
        for m in config.SAFETY_TIMER_PRESET_MINUTES:
            T.big_button(presets, str(m), lambda v=m: self.minutes_var.set(str(v)), size=10, padx=10,
                         pady=4).pack(side="right", padx=2)
        tk.Entry(self, textvariable=self.minutes_var, font=T.F(11),
                 justify="center", width=10).pack(pady=(4, 10))

        tk.Label(self, text="יעד (אופציונלי - יופיע בהתראה לאנשי הקשר)", font=T.F(9),
                 fg=T.TEXT_SECONDARY, bg=T.BG, anchor="e").pack(fill="x", padx=24)
        self.destination_var = tk.StringVar()
        tk.Entry(self, textvariable=self.destination_var, font=T.F(10),
                 justify="right").pack(fill="x", padx=24, pady=(2, 10))

        self.silent_var = tk.BooleanVar(value=False)
        tk.Checkbutton(
            self, text="בתום הזמן להפעיל אזעקה שקטה (במקום רועשת)", variable=self.silent_var,
            font=T.F(9), fg=T.TEXT, bg=T.BG, selectcolor=T.CARD_BG_ALT,
            activebackground=T.BG, activeforeground=T.TEXT, anchor="e"
        ).pack(fill="x", padx=24)

        self.error_label = tk.Label(self, text="", font=T.F(9), fg=T.RED, bg=T.BG,
                                     wraplength=330)
        self.error_label.pack(pady=(6, 0))

        btns = tk.Frame(self, bg=T.BG)
        btns.pack(pady=12)
        T.primary_button(btns, "▶ הפעל טיימר", self._start, size=11, pady=7).pack(side="right", padx=6)
        T.big_button(btns, "ביטול", self.destroy, size=11, pady=7).pack(side="right", padx=6)

    def _start(self):
        ok, msg = self.engine.start_safety_timer(
            minutes=self.minutes_var.get().strip(),
            silent_on_expiry=self.silent_var.get(),
            destination=self.destination_var.get(),
        )
        if ok:
            self.destroy()
        else:
            self.error_label.configure(text=msg)


class AccountPasswordDialog(tk.Toplevel):
    """אותה סיסמת חשבון מאמתת כיבוי תוכנה או ביטול אירוע פעיל."""

    def __init__(self, master, engine, on_confirm, on_fake_quit=None, on_restore=None):
        super().__init__(master)
        self.engine = engine
        self.on_confirm = on_confirm
        self.on_fake_quit = on_fake_quit or (lambda: None)
        self.on_restore = on_restore or (lambda: None)
        emergency_active = engine.state in (State.SILENT_TRACKING, State.ACTIVE_SOS, State.COUNTDOWN, State.ASSESSING)
        self.title("ביטול אירוע חירום" if emergency_active else "כיבוי התוכנה")
        self.geometry("380x230")
        self.configure(bg=T.BG)
        self.attributes("-topmost", True)
        self.grab_set()

        prompt = "הזן סיסמה כדי לבטל את האירוע/המעקב:" if emergency_active else "הזן סיסמה כדי לכבות את התוכנה:"
        tk.Label(self, text=prompt, font=T.F(10),
                 fg=T.TEXT, bg=T.BG).pack(pady=(20, 10))

        self.password_var = tk.StringVar()
        entry = tk.Entry(self, textvariable=self.password_var, font=T.F(16), show="•",
                          justify="center", width=16)
        entry.pack()
        entry.bind("<Return>", lambda e: self._check())
        entry.focus_set()

        self.error_label = tk.Label(self, text="", font=T.F(9), fg=T.RED, bg=T.BG)
        self.error_label.pack(pady=(6, 0))

        btns = tk.Frame(self, bg=T.BG)
        btns.pack(pady=14)
        T.big_button(btns, "בטל אירוע" if emergency_active else "כבה תוכנה", self._check, bg=T.RED_DARK,
                     size=11, pady=6).pack(side="left", padx=6)
        T.big_button(btns, "ביטול", self.destroy, size=11, pady=6).pack(side="left", padx=6)

    def _check(self):
        password = self.password_var.get()
        username = self.engine.username
        was_hidden = self.engine.state == State.SILENT_TRACKING  # ייתכן שכבר במצב כפייה מוסתר

        # ביטוי כפייה בשדה הכיבוי: מדמה כיבוי (החלון נעלם) אך משאיר/מתחיל מעקב שקט.
        if auth_module.verify_duress_phrase_typed(username, password):
            self.destroy()
            self.engine.cancel_with_password(password)  # מפעיל activate_duress_mode
            self.on_fake_quit()
            return

        if not auth_module.verify_password(username, password):
            self.error_label.configure(text="סיסמה שגויה")
            self.password_var.set("")
            return

        self.destroy()
        if was_hidden:
            # יצאנו ממצב כפייה מוסתר באמצעות הסיסמה האמיתית: עוצרים מעקב שקט ומחזירים חלון.
            self.engine.cancel_with_password(password)
            self.on_restore()
        elif self.engine.state in (State.ACTIVE_SOS, State.COUNTDOWN, State.ASSESSING):
            # בזמן חירום הסיסמה תמיד מבטלת את האירוע/המעקב; היא לא מכבה את המערכת.
            self.engine.cancel_with_password(password)
        else:
            self.on_confirm()


class SosWindow(tk.Toplevel):
    """
    מסך SOS מלא-מסך. סדר העמודות (מימין לשמאל): העזרה שלך + מיקום ידני | ספירה/ביטול + מצב שליחה + צ'אט |
    מפה למקום בטוח + לשוניות "מה קורה?" / "עזרה ראשונה". בהירות תחת לחץ: כותרת גדולה אחת, מספר גדול, פעולה
    אחת בולטת. אין אנימציה במסך הזה - שום דבר לא מעכב את השליחה.
    """

    def __init__(self, master, engine: LifeGuardEngine, context_provider=None, app=None):
        super().__init__(master)
        self.engine = engine
        self.app = app
        self._server_id = None
        self.context_provider = context_provider or (lambda: {})
        self.attributes("-fullscreen", True)
        self.attributes("-topmost", True)
        # פלטה זהה למסך הבית (רקע בהיר/כהה, כרטיסים). מצב החירום מסומן בפס אדום, בתג ובכותרת אדומה.
        self.configure(bg=T.BG)
        self.protocol("WM_DELETE_WINDOW", lambda: None)

        header = tk.Frame(self, bg=T.NAVY)
        header.pack(fill="x")
        brand = tk.Frame(header, bg=T.NAVY)
        brand.pack(side="right", padx=20, pady=10)
        logo = tk.Label(brand, bg=T.NAVY, bd=0)
        if T.HAS_PIL:
            s = T.px(30)
            T.set_image(logo, ("shield", s, T.BLUE, T.NAVY), lambda: T.shield_pil(s, T.BLUE, T.NAVY))
            logo.pack(side="right", padx=(10, 0))
        tk.Label(brand, text="LifeGuard", font=T.F(18, "bold"), fg=T.ON_NAVY, bg=T.NAVY).pack(side="right")
        T.Chip(header, " 🚨 מצב חירום ", T.SOS_FILL, "#FFFFFF", size=13, padx=14, pady=5).pack(side="left", padx=20)
        tk.Frame(self, bg=T.SOS_FILL, height=4).pack(fill="x")

        if config.DEV_MODE:
            tk.Button(self, text="✕ DEV CLOSE", font=T.F(9, "bold"),
                      fg=T.ON_NAVY, bg=T.NAVY_2, bd=0, cursor="hand2",
                      command=lambda: master.event_generate("<<ForceQuit>>")).place(x=10, y=10)

        columns = tk.Frame(self, bg=T.BG)
        columns.pack(fill="both", expand=True, padx=10, pady=10)

        # --- עמודה שמאלית: מפה + ניווט למקום בטוח ---
        map_card, self.map_frame = T.card(columns, width=460)
        map_card.pack(side="left", anchor="n", padx=6, pady=6)
        tk.Label(self.map_frame, text="🗺️ מסלול למקום בטוח קרוב", font=T.F(13, "bold"),
                 fg=T.TEXT, bg=T.CARD_BG).pack(anchor="e", pady=(0, 8))

        if HAS_MAP_WIDGET and TkinterMapView is not None:
            # מפה נמוכה: מתחתיה, באותה עמודה, לשוניות "מה קורה?" / "עזרה ראשונה"
            self.map_widget = map_hidpi.prepare(map_tiles.configure(
                TkinterMapView(self.map_frame, width=420, height=230, corner_radius=0)))
            self.map_widget.pack(fill="x")
            self.map_widget.set_zoom(15)
        else:
            self.map_widget = None
            tk.Label(
                self.map_frame,
                text="⚠️ tkintermapview לא מותקן\n(pip install tkintermapview pillow)\n\nמפה חזותית לא זמינה -\nמידע הניווט יוצג כטקסט למטה.",
                font=T.F(10), fg=T.TEXT_MUTED, bg=T.CARD_BG, justify="center", wraplength=340
            ).pack(pady=20)
        self._user_marker = None
        self._dest_marker = None

        self.route_text_label = tk.Label(
            self.map_frame, text="🔎 מחפש מקום בטוח קרוב...", font=T.F(11),
            fg=T.TEXT_SECONDARY, bg=T.CARD_BG, justify="right", anchor="e", wraplength=400
        )
        self.route_text_label.pack(fill="x", pady=(8, 0))
        # לשוניות מתחת למפה (מוצגות רק כש-SOS פעיל): פירוט הסיטואציה / עזרה ראשונה
        self.left_tabs = tk.Frame(self.map_frame, bg=T.CARD_BG)
        self._tab_var = tk.StringVar(master=self, value="guidance")
        self._tab_btns = {}
        self.tab_control = T.Segmented(self.left_tabs, [("guidance", "🧭 מה קורה?"), ("first_aid", "🩹 עזרה ראשונה")],
                                       self._tab_var, command=self.show_left_tab, size=11, bg=T.CARD_BG)
        self.tab_control.pack(fill="x", pady=(10, 6))
        self.left_body = tk.Frame(self.left_tabs, bg=T.CARD_BG)
        self.left_body.pack(fill="both", expand=True)
        self._left_panels = {}
        self._left_tab = None

        # --- עמודה ימנית: מצב העזרה ---
        # מד הסכנה *לא* מוצג לאדם שבמצוקה (זה רק מוסיף לחץ ולא עוזר לו לפעול). ההערכה נשלחת לשרת
        # ומוצגת רק לאנשי הקשר ולמתנדבים, וקובעת את מיקום האירוע בתור הפנייה למתנדבים.
        help_card, right = T.card(columns, width=300)
        help_card.pack(side="right", anchor="n", padx=6, pady=6)
        tk.Label(right, text="🤝 העזרה שלך", font=T.F(13, "bold"), fg=T.TEXT, bg=T.CARD_BG).pack(anchor="e")
        self.help_status_label = tk.Label(right, text="ממתין לאישור מהשרת...", font=T.F(12, "bold"),
                                          fg=T.TEXT_SECONDARY, bg=T.CARD_BG, wraplength=260, justify="right",
                                          anchor="e")
        self.help_status_label.pack(fill="x", pady=(6, 8))
        calm = tk.Frame(right, bg=T.CARD_BG_ALT)
        calm.pack(fill="x")
        tk.Label(calm, text="נשמו עמוק. אם אפשר - התרחקו למקום מואר עם אנשים.\nבסכנה מיידית: 100 · מד\"א 101",
                 font=T.F(11), fg=T.TEXT, bg=T.CARD_BG_ALT, wraplength=250, justify="right",
                 anchor="e").pack(fill="x", padx=10, pady=8)
        # מיקום ידני: אין GPS / רק מיקום IP משוער -> כתובת, "lat, lon" או קישור מפה
        tk.Frame(right, bg=T.BORDER, height=1).pack(fill="x", pady=12)
        tk.Label(right, text="📍 איפה את/ה?", font=T.F(12, "bold"), fg=T.TEXT, bg=T.CARD_BG).pack(anchor="e")
        tk.Label(right, text="אין GPS? כתבו כתובת, תיאור, או הדביקו קישור מפה", font=T.F(10), fg=T.TEXT_MUTED,
                 bg=T.CARD_BG, wraplength=260, justify="right", anchor="e").pack(fill="x")
        self.manual_loc_var = tk.StringVar()
        self.manual_loc_entry = tk.Entry(right, textvariable=self.manual_loc_var, font=T.F(12), justify="right",
                                         width=24, relief="flat", highlightthickness=2,
                                         highlightcolor=T.FOCUS, highlightbackground=T.BORDER)
        self.manual_loc_entry.pack(pady=(8, 6), ipady=5, fill="x")
        T.rtl_entry(self.manual_loc_entry, self.manual_loc_var)     # רווח אחרי מילה עברית מוצג במקום הנכון
        self.manual_loc_entry.bind("<Return>", lambda e: self._send_manual_location())
        self.manual_loc_btn = T.primary_button(right, "שלח מיקום", self._send_manual_location, size=11, pady=7)
        self.manual_loc_btn.pack(fill="x")
        self.manual_loc_status = tk.Label(right, text="", font=T.F(10), fg=T.TEXT_SECONDARY, bg=T.CARD_BG,
                                          wraplength=260, justify="right", anchor="e")
        self.manual_loc_status.pack(fill="x", pady=(4, 0))
        # עזרה שלא חייבת להגיע פיזית: מתנדב/ת מאומת/ת שמזעיק/ה רשויות בשבילך (כשאי אפשר לדבר בטלפון),
        # או מתנדב/ת לשיחה - בלי לראות שם ומיקום (server/helpers.py)
        self.helpers_label = None
        self._helper_kinds = set()
        if app is not None:
            tk.Frame(right, bg=T.BORDER, height=1).pack(fill="x", pady=12)
            tk.Label(right, text="🙋 עוד סוגי עזרה", font=T.F(12, "bold"), fg=T.TEXT, bg=T.CARD_BG).pack(anchor="e")
            T.big_button(right, "👮 שמישהו יזעיק משטרה בשבילי", lambda: self._request_helper("authority_liaison"),
                         size=11, pady=7, bg=T.BLUE).pack(fill="x", pady=(8, 4))
            T.big_button(right, "💬 מישהו לדבר איתו עכשיו", lambda: self._request_helper("remote_support"),
                         size=11, pady=7).pack(fill="x", pady=4)
            self.helpers_label = tk.Label(right, text="", font=T.F(10), fg=T.TEXT_SECONDARY, bg=T.CARD_BG,
                                          wraplength=260, justify="right", anchor="e")
            self.helpers_label.pack(fill="x", pady=(4, 0))

        # --- עמודה מרכזית: ספירה/סיסמת ביטול + מצב שליחה ---
        center_card, center = T.card(columns)
        center_card.pack(side="left", fill="x", expand=True, anchor="n", padx=6, pady=6)

        self.title_label = tk.Label(center, text="", font=T.F(28, "bold"), fg=T.RED, bg=T.CARD_BG)
        self.title_label.pack(pady=(12, 6))
        self.sub_label = tk.Label(center, text="", font=T.F(13), fg=T.TEXT_SECONDARY, bg=T.CARD_BG,
                                  wraplength=720, justify="center")
        self.sub_label.pack(pady=(0, 10))

        # ספירה חיה גדולה (מצב countdown בלבד) + פס זמן שנותר (בלי אנימציה - מתעדכן עם הספירה עצמה)
        self.countdown_label = tk.Label(center, text="", font=T.F(64, "bold"), fg=T.RED, bg=T.CARD_BG)
        self.countdown_bar = T.ProgressBar(center, height=8, color=T.SOS_FILL, bg=T.CARD_BG)
        self._countdown_total = None
        self._countdown_after = None

        self.location_label = tk.Label(center, text="📍 ממתין למיקום...", font=T.F(12),
                                        fg=T.TEXT_SECONDARY, bg=T.CARD_BG, wraplength=720, justify="center")

        # מצב שליחה אמיתי לאנשי הקשר (מצב SOS פעיל) - אף פעם לא "נשלח" אם זה לא באמת נשלח
        self.delivery_label = tk.Label(center, text="⏳ שולח התראה לאנשי הקשר...", font=T.F(14, "bold"),
                                       fg=T.YELLOW, bg=T.CARD_BG, wraplength=720, justify="center")

        password_frame = tk.Frame(center, bg=T.CARD_BG)
        self.password_frame = password_frame
        tk.Label(password_frame, text="הזן את סיסמת החשבון לביטול:", font=T.F(13), fg=T.TEXT, bg=T.CARD_BG).pack()
        self.password_var = tk.StringVar()
        password_entry = tk.Entry(password_frame, textvariable=self.password_var, font=T.F(18), show="•",
                                  justify="center", width=16, relief="flat", highlightthickness=3,
                                  highlightcolor=T.FOCUS, highlightbackground=T.BORDER)
        password_entry.pack(pady=10, ipady=6)
        password_entry.bind("<Return>", lambda e: self._try_cancel())
        password_entry.focus_set()
        self.password_entry = password_entry
        btn_row = tk.Frame(password_frame, bg=T.CARD_BG)
        btn_row.pack(pady=6)
        T.big_button(btn_row, "אישור ביטול", self._try_cancel, bg=T.CARD_BG_ALT, size=13).pack(side="right", padx=6)
        # 'שלח עכשיו' - למי שיודע שזה חירום אמיתי ולא רוצה לחכות לסיום הספירה
        self.send_now_btn = T.big_button(btn_row, "🚨 שלח עכשיו", self._send_now, bg=T.SOS_FILL, size=13)
        self.error_label = tk.Label(center, text="", font=T.F(12, "bold"), fg=T.RED, bg=T.CARD_BG)
        self.error_label.pack()

        # צ'אט עם אנשי הקשר והמתנדבים - במרכז (רק במצב SOS גלוי; במעקב שקט אין שום חלון).
        # הודעות מהירות בלחיצה + הכתבה קולית: לא תמיד אפשר להקליד בזמן סכנה.
        self.chat = None
        self._chat_sep = None
        if app is not None:
            from chat_panel import ChatPanel
            self._chat_sep = tk.Frame(center, bg=T.BORDER, height=1)
            self.chat = ChatPanel(center, app, lambda: self._server_id, engine.username, height=7,
                                  on_error=lambda t: self.error_label.configure(text=t), quick_cols=3)

    def set_mode(self, countdown_mode):
        self.countdown_label.pack_forget()
        self.countdown_bar.pack_forget()
        self.location_label.pack_forget()
        self.delivery_label.pack_forget()
        self.password_frame.pack_forget()
        self.left_tabs.pack_forget()
        if countdown_mode:
            self.title_label.configure(text="⏱️ מזוהה טריגר SOS")
            self.sub_label.configure(text="SOS יופעל בתום הספירה. הזן/י סיסמת חשבון לביטול, או 'שלח עכשיו'.")
            self.countdown_label.pack(pady=(4, 2))
            self.countdown_bar.pack(fill="x", padx=60, pady=(0, 10))
            self.send_now_btn.pack(side="right", padx=6)
            self.password_frame.pack(pady=12)
            self.password_entry.focus_set()
            self._tick_countdown()
        else:
            self.title_label.configure(text="🚨 SOS פעיל")  # בעבר: "עזרה נשלחת" - גם כשלא נשלח כלום
            self.sub_label.configure(text="סירנה, מיקום, אודיו ותמונות מתועדים. מצב השליחה בפועל מוצג למטה.")
            self.send_now_btn.pack_forget()
            self.delivery_label.pack(pady=(4, 10))
            self.location_label.pack(pady=(0, 12))
            self.password_frame.pack(pady=10)
            self.password_entry.focus_set()
            self.update_delivery(self.engine.get_delivery_status())
            if self.chat is not None and not self.chat.winfo_ismapped():
                self._chat_sep.pack(fill="x", padx=12, pady=(6, 6))
                self.chat.pack(fill="x", padx=12, pady=(0, 10))
            # פירוט הסיטואציה + עזרה ראשונה - בעמודה השמאלית; מוצג רק אחרי שה-SOS פעיל, לא מעכב את ההפעלה
            self.left_tabs.pack(fill="both", expand=True)
            self.show_left_tab(self._left_tab or "guidance")

    def _tick_countdown(self):
        if not self.winfo_exists():
            return
        deadline = getattr(self.engine, "countdown_deadline", None)
        if self.engine.state != State.COUNTDOWN or deadline is None:
            self.countdown_label.configure(text="")
            return
        left = max(0.0, deadline - time.time())
        remaining = max(0, int(round(left)))
        self.countdown_label.configure(text=str(remaining))
        if not self._countdown_total:
            self._countdown_total = max(1.0, left)
        self.countdown_bar.set(left / self._countdown_total, smooth=False)
        self._countdown_after = self.after(200, self._tick_countdown)

    def _send_now(self):
        self.engine.skip_countdown()

    def show_left_tab(self, key):
        """לשונית בעמודה השמאלית: 'מה קורה?' (הנחיות לפי תרחיש) או 'עזרה ראשונה' (חיפוש, עובד בלי אינטרנט)."""
        if self._tab_var.get() != key:
            self._tab_var.set(key)
        if key not in self._left_panels:
            try:
                self._left_panels[key] = (self._build_guidance if key == "guidance" else self._build_first_aid)()
            except Exception as exc:  # noqa: BLE001 - פאנל עזר לעולם לא מפיל את מסך ה-SOS
                self._left_panels[key] = (tk.Label(self.left_body, text=f"⚠️ לא נטען: {exc}", font=T.F(10),
                                                   fg=T.RED, bg=T.CARD_BG, wraplength=380), None)
        for k, (frame, _cv) in self._left_panels.items():
            if k != key:
                frame.pack_forget()
        self._left_panels[key][0].pack(fill="both", expand=True)
        self._left_tab = key
        self.after(50, self._fit_left)

    def _build_guidance(self):
        holder = tk.Frame(self.left_body, bg=T.CARD_BG)
        tk.Label(holder, text="לא מעכב את שליחת ה-SOS · גלגלת/PageDown לגלילה", font=T.F(9), fg=T.TEXT_MUTED,
                 bg=T.CARD_BG).pack(side="bottom")
        outer, inner = T.scrollable(holder, bg=T.CARD_BG)
        outer.canvas.configure(height=240)
        outer.pack(fill="both", expand=True)
        outer.bind_all_keys(self)
        GuidancePanel(inner, self.engine.username, self.context_provider, bg=T.CARD_BG, compact=True,
                      persist_checks=False, cols=2, text_wrap=340).pack(fill="both", expand=True)
        return holder, outer.canvas

    def _build_first_aid(self):
        from first_aid_ui import FirstAidScreen
        fa = FirstAidScreen(self.left_body, self.app, compact=True, bg=T.CARD_BG)
        fa._refresh_net()
        return fa, fa._outer.canvas

    def _show_guidance(self):          # תאימות לאחור
        self.show_left_tab("guidance")

    def _fit_left(self):
        """האזור הגליל בלשונית ממלא בדיוק את מה שנשאר עד תחתית המסך - בלי להיחתך ובלי רווח."""
        try:
            panel = self._left_panels.get(self._left_tab)
            cv = panel[1] if panel else None
            if cv is None or not self.winfo_exists():
                return
            self.update_idletasks()
            if not cv.winfo_ismapped() or self.winfo_height() < 200:
                self.after(80, self._fit_left)                     # עוד לא מסודר (מסך מלא נפתח) - שוב בעוד רגע
                return
            bottom = self.winfo_rooty() + self.winfo_height()
            free = bottom - cv.winfo_rooty() - (30 if self._left_tab == "guidance" else 10) - 40
            cv.configure(height=max(140, free))
        except tk.TclError:
            pass

    def update_delivery(self, status):
        if not self.winfo_exists() or not status:
            return
        color = T.STATUS_COLORS.get(status.get("level"), T.YELLOW)
        self.delivery_label.configure(text=status.get("text", ""), fg=color)
        self.help_status_label.configure(text=self.help_summary(status), fg=color)
        if status.get("server_id") and self.chat is not None:
            self._server_id = status["server_id"]
            now = time.time()
            if now - getattr(self, "_chat_refreshed", 0) > 2.5:     # עדכוני מסירה מגיעים לעיתים קרובות
                self._chat_refreshed = now
                self.chat.refresh()

    # ---------- מתנדבי תמיכה / הזעקת רשויות ----------
    def _request_helper(self, kind):
        client = getattr(self.app, "client", None)
        if not self._server_id or client is None:
            self.helpers_label.configure(text="ההתראה עוד לא אושרה בשרת - נסו שוב בעוד רגע.\nבסכנה מיידית: 100",
                                         fg=T.RED)
            return
        self.helpers_label.configure(text="⏳ שולח בקשה...", fg=T.TEXT_SECONDARY)
        iid = self._server_id

        def done(view):
            self._helper_kinds.add(kind)
            self._show_helpers(view)
        run_bg(self.app, lambda: client.request_helper(iid, kind), done,
               lambda e: self.winfo_exists() and self.helpers_label.configure(
                   text=f"❌ {getattr(e, 'message', e)}", fg=T.RED))

    def refresh_helpers(self):
        client = getattr(self.app, "client", None)
        if self._server_id and client is not None and self.helpers_label is not None:
            iid = self._server_id
            run_bg(self.app, lambda: client.get_incident(iid), self._show_helpers, lambda e: None)

    def _show_helpers(self, view):
        if not self.winfo_exists() or self.helpers_label is None:
            return
        requested = set(self._helper_kinds) | set(view.get("helper_requests") or [])   # לפי השרת (גם אחרי הפעלה מחדש)
        self.helpers_label.configure(**self.helpers_summary(view.get("helpers") or [], requested))

    @staticmethod
    def helpers_summary(helpers, requested=()):
        """מה קורה עם הבקשות - רק לפי מה שהשרת החזיר (לא 'מישהו בדרך' בלי אישור אמיתי)."""
        lines, kinds_seen = [], set()
        for h in helpers:
            kinds_seen.add(h["kind"])
            if h["state"] == "accepted":
                who = h["display_name"] if h["kind"] == "authority_liaison" else "מתנדב/ת"
                lines.append(f"✅ {h['kind_label']}: {who} איתך" +
                             (f"\n   {h['last_action_label']}" if h.get("last_action_label") else ""))
        for kind in ("authority_liaison", "remote_support"):
            mine = [h for h in helpers if h["kind"] == kind]
            if any(h["state"] == "accepted" for h in mine):
                continue
            if any(h["state"] == "notified" for h in mine):
                lines.append(f"⏳ {mine[0]['kind_label']}: נשלח למתנדבים, ממתינים שמישהו יקבל")
            elif any(h["state"] == "done" for h in mine):
                lines.append(f"✔️ {mine[0]['kind_label']}: המתנדב/ת סיים/ה")
            elif kind in requested and kind not in kinds_seen:
                lines.append("⚠️ אין כרגע מתנדבים זמינים לזה. בסכנה מיידית: 100 / 101")
        if not lines:
            return {"text": "", "fg": T.TEXT_SECONDARY}
        bad = any(l.startswith("⚠️") for l in lines)
        return {"text": "\n".join(lines), "fg": T.RED if bad else (T.GREEN if lines[0].startswith("✅") else T.TEXT_SECONDARY)}

    @staticmethod
    def help_summary(status):
        """סיכום רגוע של מי מטפל - בלי דירוג סכנה (זה מוצג רק למגיבים)."""
        if not status.get("server_id"):
            return "ההתראה עוד לא אושרה בשרת.\nהתקשר/י בעצמך: 100 / 101"
        acc = [r for r in status.get("recipients", []) if r.get("state") == "accepted"]
        if acc:
            return "✅ " + ", ".join(r.get("display_name", "") for r in acc) + "\nבדרך אליך / מטפלים באירוע"
        if status.get("total"):
            return f"📨 {status['total']} אנשים קיבלו את ההתראה.\nממתינים שמישהו יאשר שהוא מטפל."
        return "אין כרגע מי שקיבל את ההתראה.\nהתקשר/י בעצמך: 100 / 101"

    def _send_manual_location(self):
        text = T.entry_text(self.manual_loc_var.get()).strip()
        if len(text) < 2:
            self.manual_loc_status.configure(text="כתבו כתובת, תיאור או קישור", fg=T.RED)
            return
        self.manual_loc_btn.configure(state="disabled")
        self.manual_loc_status.configure(text="מאתר ושולח...", fg=T.TEXT_SECONDARY)

        box = {}

        def work():   # חיפוש כתובת = רשת; לא חוסמים את המסך. התוצאה נאספת מה-thread הראשי (Tk לא thread-safe)
            try:
                box["res"] = self.engine.set_manual_location(text)
            except Exception as exc:  # noqa: BLE001 - מוצג למשתמש/ת
                box["res"] = {"available": False, "error": str(exc)}

        def poll():
            if not self.winfo_exists():
                return
            if "res" in box:
                self._manual_done(box["res"])
            else:
                self.after(100, poll)
        threading.Thread(target=work, daemon=True).start()
        self.after(100, poll)

    def _manual_done(self, res):
        if not self.winfo_exists():
            return
        self.manual_loc_btn.configure(state="normal")
        if res.get("error"):
            self.manual_loc_status.configure(text=f"❌ {res['error']}", fg=T.RED)
        elif res.get("available"):
            self.manual_loc_status.configure(text=f"✅ נשלח: {res.get('display', '')}", fg=T.GREEN)
        else:
            self.manual_loc_status.configure(text="⚠️ הכתובת לא אותרה במפה - הטקסט נשלח לאנשי הקשר כהודעה",
                                             fg=T.YELLOW)

    def update_location(self, loc):
        if not loc or not loc.get("available"):
            self.location_label.configure(text="📍 מיקום לא זמין — אין קואורדינטות מאומתות. כתבו את המיקום בצד ימין")
            return
        if str(loc.get("source", "")).startswith("manual"):
            self.location_label.configure(text=f"📍 מיקום שהוזן ידנית: {loc.get('display') or loc.get('manual_text', '')}",
                                          fg=T.TEXT)
            if HAS_MAP_WIDGET and self.map_widget is not None:
                try:
                    self.map_widget.set_position(loc["lat"], loc["lon"])
                    if self._user_marker is None:
                        self._user_marker = map_hidpi.me_marker(self.map_widget, loc["lat"], loc["lon"], "הוזן ידנית")
                    else:
                        self._user_marker.set_position(loc["lat"], loc["lon"])
                except Exception:  # noqa: BLE001
                    pass
            return
        if loc.get("source") == "windows_location" and not loc.get("is_precise"):
            # שירות המיקום של Windows (Wi-Fi): טוב בהרבה מ-IP, אבל לא GPS - נאמר במפורש, עם הדיוק
            acc = loc.get("accuracy_m_estimate")
            self.location_label.configure(
                text=f"📍 מיקום לפי Wi-Fi (Windows) · ±{acc} מ׳ - לא GPS. אם זה לא המקום, כתבו כתובת בצד ימין",
                fg=T.TEXT)
            if HAS_MAP_WIDGET and self.map_widget is not None:
                try:
                    self.map_widget.set_position(loc["lat"], loc["lon"])
                    if self._user_marker is None:
                        self._user_marker = map_hidpi.me_marker(self.map_widget, loc["lat"], loc["lon"], f"Wi-Fi ±{acc} מ׳")
                    else:
                        self._user_marker.set_position(loc["lat"], loc["lon"])
                except Exception:  # noqa: BLE001
                    pass
            return
        if loc.get("is_precise"):
            accuracy_est = loc.get("accuracy_m_estimate")
            accuracy_text = f"GPS · אומדן ±{accuracy_est} מ׳" if accuracy_est else "GPS · דיוק לא ידוע"
            self.location_label.configure(
                text=f"📍 {loc.get('city', 'GPS')} | {loc['lat']:.5f}, {loc['lon']:.5f} ({accuracy_text})"
            )
            if HAS_MAP_WIDGET and self.map_widget is not None:
                try:
                    self.map_widget.set_position(loc["lat"], loc["lon"])
                    if self._user_marker is None:
                        self._user_marker = map_hidpi.me_marker(self.map_widget, loc["lat"], loc["lon"], "מיקום GPS")
                    else:
                        self._user_marker.set_position(loc["lat"], loc["lon"])
                except Exception as e:
                    self.engine.log(f"⚠️ שגיאת עדכון מיקום במפה: {e}")
        else:
            # Do not plot an IP centroid as if it were the user's live position.
            self.location_label.configure(
                text=f"⚠️ {loc.get('city', 'אזור לא ידוע')} | מיקום IP משוער בלבד — GPS לא זמין. "
                     "כתבו את המיקום בצד ימין"
            )
            if hasattr(self, "manual_loc_entry"):
                self.manual_loc_entry.configure(highlightbackground=T.YELLOW)

    def update_route(self, route_info):
        result = route_info.get("result")
        if not result or not result.get("place"):
            reason = route_info.get("reason")
            self.route_text_label.configure(
                text=(f"⚠️ {reason}" if reason else "⚠️ לא נמצא מקום בטוח מוכר בסביבה הקרובה")
            )
            return

        place = result["place"]
        route = result.get("route")
        distance_txt = f"{place['distance_m']:.0f} מטר אווירי"
        text = f"{place['type_label']}: {place['name']}\n{distance_txt}"
        if place.get("fallback_note"):
            text += f"\n{place['fallback_note']}"
        if route_info.get("manual"):
            # לא GPS: המסלול מתחיל בנקודה שנמצאה לכתובת - אם היא לא בדיוק איפה שאת/ה, המסלול יוסט בהתאם
            acc = route_info.get("accuracy_m")
            text = f"📝 מחושב מהכתובת שכתבת{f' (דיוק ~{acc} מ׳)' if acc else ''}\n" + text

        if route:
            minutes = route["duration_s"] / 60
            text += f"\n🚶 כ-{route['distance_m']:.0f} מ' הליכה (~{minutes:.0f} דק')"
        elif route_info.get("refining"):
            text += "\n⏳ מחשב מסלול הליכה..."
        else:
            text += "\n⚠️ לא הצלחנו לחשב מסלול הליכה מדויק (בעיית רשת/שירות?) - הקו הישר על המפה, מנסה שוב"
        if route_info.get("refining"):
            text += "\n🔄 בודק ברשת אם יש מקום קרוב יותר..."
        self.route_text_label.configure(text=text)

        if HAS_MAP_WIDGET and self.map_widget is not None:
            try:
                # מסלול חדש (למשל אחרי שהוזנה כתובת) מחליף את הקודם - לא משאירים קו ישן על המפה
                for old in (self._dest_marker, getattr(self, "_route_path", None)):
                    if old is not None:
                        old.delete()
                self._dest_marker = map_hidpi.place_marker(self.map_widget, place["lat"], place["lon"], place["name"])
                self._route_path = None
                origin = route_info.get("origin") or {}
                if route and route.get("points"):
                    self._route_path = self.map_widget.set_path(route["points"], color=T.BLUE, width=T.px(5))
                elif origin.get("lat") is not None:
                    # בלי מסלול הליכה (עדיין / אין רשת): קו ישר לכיוון היעד - עדיף על כלום
                    self._route_path = self.map_widget.set_path([(origin["lat"], origin["lon"]),
                                                                 (place["lat"], place["lon"])], color=T.ROUTE_ALT,
                                                                 width=T.px(3))
                else:
                    # אין מסלול הליכה מדויק - לפחות ממרכזים את שתי הנקודות במבט אחד
                    self.map_widget.fit_bounding_box(
                        (place["lat"], place["lon"]), (place["lat"], place["lon"])
                    )
            except Exception as e:
                self.engine.log(f"⚠️ שגיאת עדכון מסלול במפה: {e}")

    def _try_cancel(self):
        password = self.password_var.get()
        success = self.engine.cancel_with_password(password)
        if not success:
            self.error_label.configure(text="סיסמה שגויה - נסה שוב")
            self.password_var.set("")


class FeedbackWindow(tk.Toplevel):
    """מסך דירוג בסיום אירוע - Feedback Loop לאימון האלגוריתם."""

    def __init__(self, master, engine: LifeGuardEngine):
        super().__init__(master)
        self.engine = engine
        self.title("דירוג אירוע")
        self.geometry("400x300")
        self.configure(bg=T.BG)
        self.attributes("-topmost", True)
        self.protocol("WM_DELETE_WINDOW", lambda: None)

        tk.Label(self, text="האירוע הסתיים.\nעזור לנו לשפר - איך היית מדרג אותו?",
                 font=T.F(12), fg=T.TEXT, bg=T.BG, justify="center").pack(pady=24)

        options = [
            ("🔴 אירוע אמת", "true_event"),
            ("🟡 תחושת סכנה", "felt_danger"),
            ("⚪ התראת שווא", "false_alarm"),
        ]
        for text, value in options:
            T.big_button(self, text, lambda v=value: self._submit(v), size=12, bold=False, pady=8,
                         width=20).pack(pady=4)

    def _submit(self, rating):
        self.engine.submit_feedback(rating)
        self.destroy()


def main():
    # לחיצה על התראת Windows מפעילה: main.py --open "lifeguard://open?incident=inc_..." (קלט לא אמין -
    # parse_open_arg מאמת בקפדנות ומחזיר {} לכל דבר אחר)
    open_target = agent_bridge.parse_open_arg(sys.argv)
    if open_target and agent_bridge.is_app_running():
        return  # האפליקציה כבר פתוחה - לא מפעילים מופע שני מלחיצה על התראה ישנה
    try:
        agent_bridge.register_protocol()  # HKCU, בלי הרשאות מנהל
    except OSError:
        pass
    # חדות: מצהירים DPI-aware *לפני* יצירת Tk (אחרת Windows מותח את החלון כתמונה - טקסט מטושטש)
    T.enable_dpi_awareness()
    T.apply_theme(appearance.load_theme_setting(None))
    T.set_reduced_motion(appearance.load_reduce_motion(None))
    root = tk.Tk()
    root.title("LifeGuard Engine")
    root.geometry("560x760")
    root.configure(bg=T.BG)

    def on_login_success(username, password=None):
        LifeGuardApp(root, username, password, open_target=open_target)

    LoginWindow(root, on_login_success)
    root.mainloop()


if __name__ == "__main__":
    try:
        main()
    except Exception:
        import traceback
        print("\n" + "=" * 60)
        print("התוכנה נתקלה בשגיאה ולא הצליחה לרוץ. פרטי השגיאה המלאים:")
        print("=" * 60)
        traceback.print_exc()
        print("=" * 60)
        input("\nלחץ Enter כדי לסגור את החלון...")
