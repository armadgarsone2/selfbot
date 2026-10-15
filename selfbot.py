#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Selfbot v2 — duel entry (round 2)
Improved Telegram selfbot. All original commands kept working, plus:
  * persistent state (tasks, ignored chats, antidelete, bio, afk, schedule)
  * previously-advertised-but-missing commands implemented
    (.ریستارت .تست .سنگ کاغذ قیچی)
  * new: .پاکسازی .حساب .اذان .افک .زمانبندی .آمار
  * bounded LRU message cache (no memory leak)
  * FloodWait handling + real logging (no silent failures)
  * graceful restart, single-instance lock, systemd unit included
  * credentials from env/.env only — nothing hardcoded
  * safe calculator (AST-based, no eval, absurd magnitudes rejected)
"""

import asyncio
import ast
import fcntl
import json
import logging
import math
import operator
import os
import random
import re
import sys
import time
import unicodedata
import urllib.parse
import urllib.request
from collections import OrderedDict
from datetime import datetime
from pathlib import Path

import jdatetime
from telethon import TelegramClient, events
from telethon.errors import FloodWaitError
from telethon.tl.functions.account import UpdateProfileRequest


# ---------- unicode font styles ----------
def _fmap(ub, lb, db=None):
    m = {}
    for i in range(26):
        m[chr(65 + i)] = chr(ub + i)
        m[chr(97 + i)] = chr(lb + i)
    if db is not None:
        for i in range(10):
            m[chr(48 + i)] = chr(db + i)
    return m

_FONT_TABLES = {
    "bold": _fmap(0x1D400, 0x1D41A, 0x1D7CE),
    "italic": _fmap(0x1D434, 0x1D44E),
    "bolditalic": _fmap(0x1D468, 0x1D482),
    "mono": _fmap(0x1D670, 0x1D68A, 0x1D7F6),
    "double": _fmap(0x1D538, 0x1D552, 0x1D7D8),
    "full": _fmap(0xFF21, 0xFF41, 0xFF10),
    "fraktur": _fmap(0x1D504, 0x1D51E),
    "circle": _fmap(0x24B6, 0x24D0),
}
_FONT_TABLES["circle"].update({str(i): chr(0x245F + i) for i in range(1, 10)})
_FONT_TABLES["circle"]["0"] = chr(0x24EA)

FONT_STYLES = list(_FONT_TABLES) + ["kashida", "overline"]


def stylize(text, style):
    """Apply a unicode font style. Latin chars get mapped; Persian passes
    through for math fonts, kashida/overline work on Persian too."""
    if style in _FONT_TABLES:
        t = _FONT_TABLES[style]
        return "".join(t.get(c, c) for c in text)
    if style == "kashida":
        # ــ between Persian/Arabic letters
        out = []
        for c in text:
            out.append(c)
            if "\u0600" <= c <= "\u06FF" and c != " ":
                out.append("ـ")
        return "".join(out).rstrip("ـ")
    if style == "overline":
        return "".join(c + "\u0305" if c != " " else c for c in text)
    return text


# ---------- clock emojis (one per half hour, index 0 = 12:00) ----------
CLOCKS = ["🕛", "🕧", "🕐", "🕜", "🕑", "🕝", "🕒", "🕞", "🕓", "🕟",
          "🕔", "🕥", "🕕", "🕡", "🕖", "🕢", "🕗", "🕣", "🕘", "🕤",
          "🕙", "🕥", "🕚", "🕦"]


# ---------- random bio quotes (Persian) ----------
BIO_QUOTES = [
    "سکوت، بلندترین فریاده",
    "من همونم که فکر می‌کنی نیستم",
    "زندگی کوتاهه، پینگت پایین باشه",
    "تو تاریکی هم می‌شه ستاره بود",
    "حرف زیاده، عمل کمه",
    "آروم ولی خطرناک",
    "دنیا رو از پنجره‌ی خودم می‌بینم",
    "کم‌حرف، پرمعنی",
    "جایی که ترس تموم می‌شه، من شروع می‌شم",
    "نه قهرمانم نه ضدقهرمان؛ خودمم",
    "وقت طلاست، منم طلا",
    "بازی رو جدی بگیر، ولی نه اون‌قدر که ببازی",
    "ساده زندگی کن، عمیق فکر کن",
    "هر روز یه شروع تازه‌ست",
    "موفقیت شیرین‌ترین انتقامه",
    "خودت باش، بقیه گرفته شدن",
    "تو سکوت قدرت هست",
    "رویاهام از ترس‌هام بزرگ‌ترن",
    "من نویسنده‌ی داستان خودمم",
    "کمتر بگو، بیشتر نشون بده",
    "آسمون حد نیست، شروعه",
    "با قلب بازی کن، با عقل ببر",
    "گذشته درسه، نه خونه",
    "انرژی مثبت، وایب منفی صفر",
    "تو دنیای خودم پادشاهم",
    "حرف‌هامو با عملم ثابت می‌کنم",
]

# ---------------- config ----------------
BASE_DIR = Path(__file__).resolve().parent


def _load_dotenv():
    """Load BASE_DIR/.env into os.environ (never overrides real env)."""
    p = BASE_DIR / ".env"
    if not p.is_file():
        return
    for line in p.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line and not line.startswith("#") and "=" in line:
            k, v = line.split("=", 1)
            os.environ.setdefault(k.strip(), v.strip().strip("'\""))


_load_dotenv()

API_ID = os.environ.get("API_ID")
API_HASH = os.environ.get("API_HASH")
SESSION = os.environ.get("SELFBOT_SESSION", str(BASE_DIR / "duel_session.session"))
STATE_FILE = BASE_DIR / "selfbot_state.json"
LOG_FILE = BASE_DIR / "selfbot.log"

DEFAULT_STATE = {
    "tasks": {},            # name -> {keyword, button, delay}
    "ignored_chats": [],    # exempt from antidelete
    "antidelete": None,     # None=auto, True/False=forced
    "antiedit": None,
    "time_bio": False,
    "base_bio": "",
    "afk": False,
    "afk_msg": "در دسترس نیستم، بعداً جواب میدم 🙏",
    "scheduled": [],        # [{id, chat_id, text, at}]
    "stats": {"messages": 0, "commands": 0},
}

HELP = """
📖 **راهنمای سلف v2**
`.پنل` | `.پینگ` | `.تاریخ` | `.آمار` | `.تست`
`.شیر یا خط` | `.تاس` | `.عشق [نام]` | `.سنگ کاغذ قیچی [سنگ/کاغذ/قیچی]`
`.سیو` (ریپلای) | `.اسم [نام]` | `.بیو [متن]` | `.بیو رندم` | `.تایم بیو روشن/خاموش`
`.فونت اسم [استایل] [متن]` | `.فونت بیو [استایل] [متن]` | `.فونت [استایل] [متن]` | `.فونت لیست`
`.آنتی دیلیت روشن/خاموش` | `.آنتی ادیت روشن/خاموش`
`.اسپم [تعداد] [متن]` | `.حذف [تعداد]` | `.پاکسازی [تعداد]`
`.ترجمه` (ریپلای) | `.حساب [عبارت]` | `.قیمت ارز` | `.قیمت طلا` | `.اذان [شهر]` | `.ساعت` | `.ساعت رندم`
`.تسک اضافه نام|کلمه|دکمه|تاخیر` | `.تسک حذف نام` | `.تسک لیست`
`.روشن` | `.خاموش` | `.وضعیت`
`.معاف [ایدی]` | `.شامل [ایدی]` | `.ایدی [یوزر]`
`.افک روشن [متن]` | `.افک خاموش`
`.زمانبندی اضافه 10m [متن]` | `.زمانبندی لیست` | `.زمانبندی حذف [ایدی]`
`.ریستارت`
""".strip()

# ---------------- logging ----------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(message)s",
    handlers=[logging.FileHandler(LOG_FILE), logging.StreamHandler()],
)
log = logging.getLogger("selfbot-v2")


# ---------------- state ----------------
def load_state():
    state = json.loads(json.dumps(DEFAULT_STATE))  # deep copy
    try:
        if STATE_FILE.is_file():
            saved = json.loads(STATE_FILE.read_text(encoding="utf-8"))
            for k, v in saved.items():
                if k in state:
                    state[k] = v
    except Exception:
        log.exception("failed to load state, using defaults")
    return state


def save_state(state):
    tmp = STATE_FILE.with_suffix(".tmp")
    tmp.write_text(json.dumps(state, ensure_ascii=False, indent=1),
                   encoding="utf-8")
    tmp.replace(STATE_FILE)


# ---------------- bounded cache ----------------
class LRUCache(OrderedDict):
    """Message cache with a hard size cap — no memory leak."""

    def __init__(self, maxsize=5000):
        super().__init__()
        self.maxsize = maxsize

    def __setitem__(self, key, value):
        if key in self:
            self.move_to_end(key)
        super().__setitem__(key, value)
        while len(self) > self.maxsize:
            self.popitem(last=False)


async def flood_aware(coro):
    """Await a coroutine, surviving Telegram FloodWait."""
    while True:
        try:
            return await coro
        except FloodWaitError as e:
            log.warning("FloodWait: sleeping %ss", e.seconds)
            await asyncio.sleep(e.seconds + 1)


def parse_delay(text):
    """'10m' / '2h' / '30s' -> seconds. Returns None on bad input."""
    m = re.fullmatch(r"(\d+)\s*([smh])", text.strip().lower())
    if not m:
        return None
    return int(m.group(1)) * {"s": 1, "m": 60, "h": 3600}[m.group(2)]


# ---------------- safe calculator ----------------
_CALC_NAMES = {"pi": math.pi, "e": math.e, "abs": abs, "round": round,
               "min": min, "max": max, "sqrt": math.sqrt}
_CALC_OPS = {ast.Add: operator.add, ast.Sub: operator.sub,
             ast.Mult: operator.mul, ast.Div: operator.truediv,
             ast.Mod: operator.mod, ast.Pow: operator.pow,
             ast.USub: operator.neg, ast.UAdd: operator.pos}


def safe_eval(expr):
    """Evaluate a math expression with zero eval() risk.

    Only numbers, whitelisted functions/constants and basic operators.
    Absurd magnitudes (e.g. 9**9**9) are rejected BEFORE computing.
    """
    def _check(v):
        if isinstance(v, (int, float)) and abs(v) > 1e15:
            raise ValueError("عدد خیلی بزرگه")
        return v

    def _eval(node):
        if isinstance(node, ast.Expression):
            return _eval(node.body)
        if isinstance(node, ast.Constant):
            if isinstance(node.value, (int, float)):
                return node.value
            raise ValueError("ثابت مجاز نیست")
        if isinstance(node, ast.BinOp) and type(node.op) in _CALC_OPS:
            left, right = _eval(node.left), _eval(node.right)
            if isinstance(node.op, ast.Pow) and abs(right) > 100:
                raise ValueError("توان خیلی بزرگه")
            return _check(_CALC_OPS[type(node.op)](left, right))
        if isinstance(node, ast.UnaryOp) and type(node.op) in _CALC_OPS:
            return _check(_CALC_OPS[type(node.op)](_eval(node.operand)))
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id in _CALC_NAMES
                and callable(_CALC_NAMES[node.func.id])):
            return _check(_CALC_NAMES[node.func.id](
                *[_eval(a) for a in node.args]))
        if (isinstance(node, ast.Name) and node.id in _CALC_NAMES
                and not callable(_CALC_NAMES[node.id])):
            return _CALC_NAMES[node.id]
        raise ValueError("عبارت مجاز نیست")

    return _eval(ast.parse(expr, mode="eval"))


# ---------------- single instance ----------------
_lock_fd = None


def ensure_single_instance():
    """Exit if another copy is already running (flock auto-releases)."""
    global _lock_fd
    _lock_fd = open(BASE_DIR / "selfbot.lock", "w")
    try:
        fcntl.flock(_lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        _lock_fd.write(str(os.getpid()))
        _lock_fd.flush()
    except OSError:
        sys.exit("❌ another instance is already running")

# ================= SelfBot =================
class SelfBot:
    def __init__(self):
        self.cli = None
        self.msg_cache = LRUCache(maxsize=5000)
        self.state = load_state()
        self.boot_time = time.time()
        self.afk_replied = set()

        # auto-clicker runtime
        self.ac_active = False
        self.ac_target_chat = None
        self.ac_keyword = None
        self.ac_button = None
        self.ac_delay = 1.0

    # ---------- lifecycle ----------
    async def start(self):
        if not API_ID or not API_HASH:
            sys.exit("❌ API_ID / API_HASH must be set (env or .env file).")
        self.cli = TelegramClient(SESSION, int(API_ID), API_HASH)
        await self.cli.connect()
        if not await self.cli.is_user_authorized():
            sys.exit("❌ Session not authorized. Log in first, then run again.")

        me = await self.cli.get_entity("me")
        if not self.state["base_bio"]:
            self.state["base_bio"] = getattr(me, "about", "") or ""
            save_state(self.state)
        log.info("selfbot v2 started as %s (@%s)",
                 me.first_name, me.username or "-")

        self.cli.add_event_handler(self._cmd_handler,
                                   events.NewMessage(outgoing=True))
        self.cli.add_event_handler(self._incoming, events.NewMessage(incoming=True))
        self.cli.add_event_handler(self._antidelete, events.MessageDeleted)
        self.cli.add_event_handler(self._antiedit, events.MessageEdited)

        asyncio.create_task(self._loop_ac())
        asyncio.create_task(self._loop_bio())
        asyncio.create_task(self._loop_schedule())

        await self.cli.run_until_disconnected()

    async def _respond(self, event, text):
        if event.out:
            await flood_aware(event.message.edit(text))
        else:
            await flood_aware(event.reply(text))

    # ---------- watchers ----------
    async def _incoming(self, event):
        try:
            self.state["stats"]["messages"] += 1
            if event.message:
                self.msg_cache[event.message.id] = event.raw_text
            # AFK auto-reply: private chats only, once per chat per AFK session
            if (self.state["afk"] and event.is_private and not event.out
                    and event.chat_id not in self.afk_replied):
                self.afk_replied.add(event.chat_id)
                await flood_aware(event.reply(self.state["afk_msg"]))
            if self.state["stats"]["messages"] % 50 == 0:
                save_state(self.state)
        except Exception:
            log.exception("incoming handler failed")

    async def _antidelete(self, event):
        try:
            if event.chat_id in self.state["ignored_chats"]:
                return
            chat = await event.get_chat()
            is_chan = getattr(chat, "broadcast", False)
            cfg = self.state["antidelete"]
            enabled = cfg if cfg is not None else (is_chan or event.is_private)
            if not enabled:
                return
            for mid in event.deleted_ids:
                txt = self.msg_cache.get(mid, "[مدیا/حذف شده]")
                await flood_aware(self.cli.send_message(
                    "me", f"🗑 حذف پیام:\n{txt}"))
        except Exception:
            log.exception("antidelete failed")

    async def _antiedit(self, event):
        try:
            if not event.message or not event.message.edit_date:
                return
            cfg = self.state["antiedit"]
            enabled = cfg if cfg is not None else event.is_private
            if not enabled:
                return
            old = self.msg_cache.get(event.message.id, "[نامشخص]")
            self.msg_cache[event.message.id] = event.raw_text
            await flood_aware(self.cli.send_message(
                "me", f"✏️ ادیت پیام:\nقبل: {old}\nبعد: {event.raw_text}"))
        except Exception:
            log.exception("antiedit failed")

    # ---------- background loops ----------
    async def _loop_ac(self):
        while True:
            try:
                if self.ac_active and self.ac_target_chat and self.ac_keyword:
                    async for msg in self.cli.iter_messages(
                            self.ac_target_chat, limit=1):
                        if self.ac_keyword in (msg.raw_text or ""):
                            if self.ac_button:
                                await flood_aware(msg.click(text=self.ac_button))
                            else:
                                await flood_aware(msg.click(0))
            except Exception:
                log.exception("autoclick loop failed")
            await asyncio.sleep(self.ac_delay)

    async def _loop_bio(self):
        while True:
            try:
                if self.state["time_bio"]:
                    t = jdatetime.datetime.now().strftime("%H:%M")
                    await flood_aware(self.cli(UpdateProfileRequest(
                        about=f"{self.state['base_bio']} | {t}")))
            except Exception:
                log.exception("bio loop failed")
            await asyncio.sleep(60)

    async def _loop_schedule(self):
        while True:
            try:
                now = time.time()
                due = [s for s in self.state["scheduled"] if s["at"] <= now]
                for s in due:
                    await flood_aware(
                        self.cli.send_message(s["chat_id"], s["text"]))
                    self.state["scheduled"].remove(s)
                    log.info("sent scheduled msg #%s", s["id"])
                if due:
                    save_state(self.state)
            except Exception:
                log.exception("scheduler loop failed")
            await asyncio.sleep(20)

    # ---------- command handler ----------
    async def _cmd_handler(self, event):
        txt = (event.raw_text or "").strip()
        if not txt or not txt.startswith((".", "!", "/")):
            return
        if len(txt) <= 1:  # lone "." / "!" / "/" — not a command, stay silent
            return
        self.state["stats"]["commands"] += 1
        try:
            await self._dispatch(event, txt)
        except Exception:
            log.exception("command failed: %s", txt[:60])
            try:
                await self._respond(event, "❌ خطا در اجرای دستور")
            except Exception:
                log.debug("could not even send the error message")

    def _parse(self, txt):
        body = txt[1:].strip()
        # multi-word commands first
        for mw in ("سنگ کاغذ قیچی", "فونت اسم", "فونت بیو"):
            if body.startswith(mw):
                return mw, body[len(mw):].strip()
        parts = body.split(maxsplit=1)
        return parts[0], (parts[1] if len(parts) > 1 else "")

    async def _dispatch(self, event, txt):
        action, arg = self._parse(txt)
        S = self.state
        R = self._respond

        if action == "پنل":
            tri = lambda v: "🤖 خودکار" if v is None else ("🟢 روشن" if v else "🔴 خاموش")
            bi = lambda b: "🟢 روشن" if b else "🔴 خاموش"
            up = int(time.time() - self.boot_time)
            h, rem = divmod(up, 3600)
            mnt, _ = divmod(rem, 60)
            up_str = f"{h} ساعت و {mnt} دقیقه" if h else f"{mnt} دقیقه"
            st = S["stats"]

            def _tree(items):
                return [("├ " if i < len(items) - 1 else "└ ") + x
                        for i, x in enumerate(items)]

            L = ["🤖 ━━━ سلف‌بات v2 ━━━", ""]
            L += ["🛡 ━ محافظت ━"] + _tree([
                f"🗑 آنتی‌دیلیت : {tri(S['antidelete'])}",
                f"✏️ آنتی‌ادیت : {tri(S['antiedit'])}",
                f"📵 AFK : {bi(S['afk'])}",
            ])
            L += ["", "⚙️ ━ سیستم ━"] + _tree([
                f"🖱 اتوکلیکر : {bi(self.ac_active)}",
                f"📊 پیام‌های امروز : {st['messages']}",
                f"⌨️ دستورات اجرا شده : {st['commands']}",
                f"⏱ آپتایم : {up_str}",
            ])
            L += ["", "📖 ━ دستورات ━", ""]
            cats = [
                ("🎲 ━ سرگرمی ━", [
                    "`.شیر یا خط`", "`.تاس`",
                    "`.عشق [نام]`", "`.سنگ کاغذ قیچی`"]),
                ("👤 ━ پروفایل ━", [
                    "`.اسم [نام]`", "`.بیو [متن]`",
                    "`.بیو رندم`",
                    "`.فونت اسم [استایل|رندم] [متن]`",
                    "`.فونت بیو [استایل|رندم] [متن]`",
                    "`.فونت [استایل|رندم] [متن]`",
                    "`.فونت لیست`",
                    "`.تایم بیو روشن/خاموش`",
                    "`.سیو` — ریپلای روی مدیا"]),
                ("🛡 ━ دستورات محافظت ━", [
                    "`.آنتی دیلیت روشن/خاموش`",
                    "`.آنتی ادیت روشن/خاموش`",
                    "`.معاف [ایدی]`", "`.شامل [ایدی]`"]),
                ("🧹 ━ پیام‌ها ━", [
                    "`.اسپم [تعداد] [متن]`",
                    "`.حذف [تعداد]`", "`.پاکسازی [تعداد]`"]),
                ("🔧 ━ ابزار ━", [
                    "`.ترجمه` — ریپلای روی پیام",
                    "`.حساب [عبارت]`", "`.ایدی [یوزر]`",
                    "`.قیمت ارز`", "`.قیمت طلا`",
                    "`.اذان [شهر]`", "`.ساعت`",
                    "`.ساعت رندم`"]),
                ("🤖 ━ اتوکلیکر ━", [
                    "`.تسک اضافه نام|کلمه|دکمه|تاخیر`",
                    "`.تسک حذف نام`", "`.تسک لیست`",
                    "`.روشن [نام]`", "`.خاموش`", "`.وضعیت`"]),
                ("⏰ ━ زمانبندی و AFK ━", [
                    "`.افک روشن [متن]`", "`.افک خاموش`",
                    "`.زمانبندی اضافه 10m [متن]`",
                    "`.زمانبندی لیست`",
                    "`.زمانبندی حذف [ایدی]`"]),
                ("ℹ️ ━ سیستمی ━", [
                    "`.پینگ`", "`.تاریخ`", "`.آمار`",
                    "`.تست`", "`.ریستارت`"]),
            ]
            for title, items in cats:
                L += [title] + _tree(items) + [""]
            await R(event, "\n".join(L).rstrip())
        elif action in ("دستورات", "راهنما"):
            await R(event, HELP)
        elif action == "پینگ":
            t0 = time.time()
            m = await event.message.edit("🏓 ...")
            dt = (time.time() - t0) * 1000
            await m.edit(f"🏓 پونگ! `{dt:.0f}ms` | {datetime.now():%H:%M:%S}")
        elif action == "آمار":
            up = int(time.time() - self.boot_time)
            h, rem = divmod(up, 3600)
            mnt, sec = divmod(rem, 60)
            st = S["stats"]
            await R(event,
                    f"📊 **آمار سلف**\n⏱ آپتایم: {h}h {mnt}m {sec}s\n"
                    f"📩 پیام‌های دیده‌شده: {st['messages']}\n"
                    f"⌨️ دستورات اجرا شده: {st['commands']}\n"
                    f"💾 کش پیام: {len(self.msg_cache)}/5000")
        elif action == "تست":
            checks = []
            try:
                save_state(S)
                checks.append("💾 ذخیره تنظیمات: ✅")
            except Exception:
                checks.append("💾 ذخیره تنظیمات: ❌")
            checks.append("🔗 اتصال تلگرام: ✅"
                          if self.cli.is_connected() else "🔗 اتصال تلگرام: ❌")
            try:
                await self.cli.get_me()
                checks.append("👤 نشست معتبر: ✅")
            except Exception:
                checks.append("👤 نشست معتبر: ❌")
            self.msg_cache["__t"] = "1"
            checks.append("🧠 کش پیام: ✅"
                          if self.msg_cache.get("__t") == "1" else "🧠 کش: ❌")
            self.msg_cache.pop("__t", None)
            await R(event, "🛠 **تست سلامت**\n" + "\n".join(checks))
        elif action in ("تاریخ", "تقویم"):
            now = jdatetime.datetime.now()
            await R(event, f"📅 {now.strftime('%Y/%m/%d (%A) - %H:%M:%S')}")
        elif action == "شیر":
            await R(event, random.choice(["🪙 شیر آمد!", "🪙 خط آمد!"]))
        elif action == "تاس":
            await R(event, f"🎲 عدد تاس: {random.randint(1, 6)}")
        elif action == "سنگ کاغذ قیچی":
            opts = ["سنگ", "کاغذ", "قیچی"]
            bot = random.choice(opts)
            you = arg if arg in opts else None
            if not you:
                await R(event, f"🤖 من آوردم: **{bot}**\n"
                               "مثال: `.سنگ کاغذ قیچی سنگ`")
                return
            beats = {"سنگ": "قیچی", "قیچی": "کاغذ", "کاغذ": "سنگ"}
            if you == bot:
                res = "🤝 مساوی!"
            elif beats[you] == bot:
                res = "🎉 بردی!"
            else:
                res = "😅 باختی!"
            await R(event, f"تو: {you} | من: {bot}\n{res}")
        elif action == "عشق" and arg:
            await R(event,
                    f"❤️ میزان علاقه به {arg}: {random.randint(30, 100)}% 😍")
        elif action == "سیو" and event.is_reply:
            rep = await event.get_reply_message()
            if rep and rep.media:
                path = await flood_aware(rep.download_media())
                await R(event, f"📥 ذخیره شد: `{path}`")
            else:
                await R(event, "❌ روی یک پیام مدیادار ریپلای کن")
        elif action == "اسم" and arg:
            await flood_aware(self.cli(UpdateProfileRequest(first_name=arg)))
            await R(event, f"✅ نام به «{arg}» تغییر کرد")
        elif action == "بیو" and arg == "رندم":
            q = random.choice(BIO_QUOTES)
            S["base_bio"] = q
            save_state(S)
            await flood_aware(self.cli(UpdateProfileRequest(about=q)))
            await R(event, f"🎲 بیو رندم:\n{q}")
        elif action == "بیو" and arg:
            S["base_bio"] = arg
            save_state(S)
            await flood_aware(self.cli(UpdateProfileRequest(about=arg)))
            await R(event, "✅ بیو تغییر کرد")
        elif action == "فونت":
            if arg == "لیست":
                lines = [f"▸ `{s}` — {stylize('Ali علی', s)}" for s in FONT_STYLES]
                lines.append("▸ `رندم` — یه استایل شانسی")
                await R(event, "🎨 فونت‌ها:\n" + "\n".join(lines))
            else:
                sp = arg.split(maxsplit=1)
                if len(sp) == 2 and (sp[0] in FONT_STYLES or sp[0] == "رندم"):
                    style = random.choice(FONT_STYLES) if sp[0] == "رندم" else sp[0]
                    await R(event, f"🎲 `{style}`\n{stylize(sp[1], style)}")
                else:
                    await R(event, "❓ `.فونت [استایل] [متن]`\n`.فونت لیست` برای دیدن استایل‌ها")
        elif action == "فونت اسم" and arg:
            sp = arg.split(maxsplit=1)
            if len(sp) == 2 and (sp[0] in FONT_STYLES or sp[0] == "رندم"):
                style = random.choice(FONT_STYLES) if sp[0] == "رندم" else sp[0]
                name = stylize(sp[1], style)[:60]
                await flood_aware(self.cli(UpdateProfileRequest(first_name=name)))
                await R(event, f"✅ نام با فونت `{style}`:\n{name}")
            else:
                await R(event, "❓ `.فونت اسم [استایل] [متن]`\n`.فونت لیست` برای دیدن استایل‌ها")
        elif action == "فونت بیو" and arg:
            sp = arg.split(maxsplit=1)
            if len(sp) == 2 and (sp[0] in FONT_STYLES or sp[0] == "رندم"):
                style = random.choice(FONT_STYLES) if sp[0] == "رندم" else sp[0]
                bio = stylize(sp[1], style)[:250]
                S["base_bio"] = bio
                save_state(S)
                await flood_aware(self.cli(UpdateProfileRequest(about=bio)))
                await R(event, f"✅ بیو با فونت `{style}` تغییر کرد")
            else:
                await R(event, "❓ `.فونت بیو [استایل] [متن]`\n`.فونت لیست` برای دیدن استایل‌ها")
        elif action == "ساعت":
            if arg == "رندم":
                clock = random.choice(CLOCKS)
                h, m = random.randint(0, 23), random.choice([0, 30])
                await R(event, f"🎲 {clock} {h:02d}:{m:02d}")
            else:
                now = datetime.now()
                clock = CLOCKS[(now.hour % 12) * 2 + (1 if now.minute >= 30 else 0)]
                await R(event, f"{clock} {now.strftime('%H:%M')}")
        elif action == "تایم" and arg == "بیو روشن":
            S["time_bio"] = True
            save_state(S)
            await R(event, "⏰ تایم بیو روشن شد")
        elif action == "تایم" and arg == "بیو خاموش":
            S["time_bio"] = False
            save_state(S)
            await flood_aware(
                self.cli(UpdateProfileRequest(about=S["base_bio"])))
            await R(event, "⏰ تایم بیو خاموش شد")
        elif action == "آنتی" and arg == "دیلیت روشن":
            S["antidelete"] = True
            save_state(S)
            await R(event, "🛡 آنتی‌دیلیت روشن شد")
        elif action == "آنتی" and arg == "دیلیت خاموش":
            S["antidelete"] = False
            save_state(S)
            await R(event, "🛡 آنتی‌دیلیت خاموش شد")
        elif action == "آنتی" and arg == "ادیت روشن":
            S["antiedit"] = True
            save_state(S)
            await R(event, "✏️ آنتی‌ادیت روشن شد")
        elif action == "آنتی" and arg == "ادیت خاموش":
            S["antiedit"] = False
            save_state(S)
            await R(event, "✏️ آنتی‌ادیت خاموش شد")
        elif action == "اسپم" and arg:
            p = arg.split(maxsplit=1)
            if len(p) == 2 and p[0].isdigit():
                n = min(int(p[0]), 30)
                for _ in range(n):
                    await flood_aware(event.respond(p[1]))
                    await asyncio.sleep(1)
                await R(event, f"✅ {n} پیام ارسال شد")
            else:
                await R(event, "❌ مثال: `.اسپم 5 سلام`")
        elif action == "حذف" and arg.isdigit():
            count = min(int(arg), 100)
            deleted = 0
            async for msg in self.cli.iter_messages(
                    event.chat_id, from_user="me", limit=count + 1):
                if msg.id == event.message.id:
                    continue
                try:
                    await flood_aware(msg.delete())
                    deleted += 1
                except Exception:
                    log.debug("delete failed for msg %s", msg.id)
            await R(event, f"🗑 {deleted} پیام حذف شد")
        elif action == "پاکسازی" and arg.isdigit():
            # like حذف but never touches the command message itself
            count = min(int(arg), 100)
            deleted = 0
            ids = []
            async for msg in self.cli.iter_messages(
                    event.chat_id, from_user="me", limit=count + 1):
                if msg.id != event.message.id:
                    ids.append(msg.id)
            for mid in ids:
                try:
                    await flood_aware(
                        self.cli.delete_messages(event.chat_id, mid))
                    deleted += 1
                except Exception:
                    log.debug("purge failed for msg %s", mid)
            await event.message.delete()
        elif action == "حساب" and arg:
            try:
                res = safe_eval(arg)
                await R(event, f"🧮 نتیجه: `{res}`")
            except Exception as e:
                await R(event, f"❌ خطا در محاسبه: {e}")
        elif action == "ترجمه" and event.is_reply:
            rep = await event.get_reply_message()
            if rep and rep.text:
                q = urllib.parse.quote(rep.text[:1000])
                url = ("https://translate.googleapis.com/translate_a/single"
                       f"?client=gtx&sl=auto&tl=fa&dt=t&q={q}")
                try:
                    res = json.load(urllib.request.urlopen(url, timeout=15))
                    await R(event, f"🌐 ترجمه:\n{res[0][0][0]}")
                except Exception as e:
                    await R(event, f"❌ خطای ترجمه: {e}")
            else:
                await R(event, "❌ روی یک پیام متنی ریپلای کن")
        elif action == "اذان":
            city = arg or "Tehran"
            try:
                url = ("http://api.aladhan.com/v1/timingsByCity?city="
                       f"{urllib.parse.quote(city)}&country=Iran&method=7")
                data = json.load(urllib.request.urlopen(url, timeout=15))
                t = data["data"]["timings"]
                await R(event,
                        f"🕌 اوقات شرعی ({city}):\nطلوع: {t['Sunrise']}\n"
                        f"ظهر: {t['Dhuhr']}\nغروب: {t['Sunset']}\n"
                        f"مغرب: {t['Maghrib']}\nعشا: {t['Isha']}")
            except Exception:
                await R(event, "❌ خطا در دریافت اوقات شرعی")
        elif action in ("قیمت", "ارز", "طلا"):
            # ".قیمت طلا" -> action="قیمت", arg="طلا": check arg too
            is_gold = action == "طلا" or "طلا" in arg
            try:
                key = "geram18" if is_gold else "price_dollar_rl"
                url = ("https://api.tgju.org/v1/market/indicator/"
                       f"summary-table-data/{key}")
                p = json.load(
                    urllib.request.urlopen(url, timeout=15)).get(
                        "data", {}).get("last", "نامشخص")
                label = "طلا ۱۸ عیار" if is_gold else "دلار"
                await R(event, f"💰 قیمت {label}: {p}")
            except Exception:
                log.warning("price fetch failed")
                await R(event, "❌ خطا در دریافت قیمت")
        elif action == "تسک":
            sub = arg.split(maxsplit=1)
            if not sub:
                await R(event, "❌ مثال: `.تسک اضافه نام|کلمه`")
                return
            if sub[0] == "اضافه" and len(sub) > 1:
                parts = [p.strip() for p in sub[1].split("|")]
                if len(parts) >= 2:
                    S["tasks"][parts[0]] = {
                        "keyword": parts[1],
                        "button": parts[2] if len(parts) > 2 else None,
                        "delay": float(parts[3]) if len(parts) > 3 else 1.0,
                    }
                    save_state(S)
                    await R(event, "➕ تسک اضافه شد")
                else:
                    await R(event, "❌ فرمت: `نام|کلمه|دکمه|تاخیر`")
            elif sub[0] == "حذف" and len(sub) > 1:
                S["tasks"].pop(sub[1], None)
                save_state(S)
                await R(event, "🗑 تسک حذف شد")
            elif sub[0] == "لیست":
                if S["tasks"]:
                    lines = [f"- {k}: {v['keyword']}" for k, v in
                             S["tasks"].items()]
                    await R(event, "📋 تسک‌ها:\n" + "\n".join(lines))
                else:
                    await R(event, "📭 لیست خالیه")
        elif action == "روشن":
            name = arg.strip()
            task = S["tasks"].get(name) if name else None
            if task is None and S["tasks"]:
                task = next(iter(S["tasks"].values()))  # default: first
            if task:
                self.ac_active = True
                self.ac_keyword = task["keyword"]
                self.ac_button = task["button"]
                self.ac_delay = task["delay"]
                self.ac_target_chat = event.chat_id
                await R(event, "▶️ اتوکلیکر روشن شد")
            else:
                await R(event, "❌ تسک پیدا نشد. مثال: `.روشن نام_تسک`")
        elif action == "خاموش":
            self.ac_active = False
            await R(event, "⏹ اتوکلیکر خاموش شد")
        elif action == "وضعیت":
            await R(event,
                    f"📊 اتوکلیکر: {'روشن' if self.ac_active else 'خاموش'}\n"
                    f"📋 تسک‌ها: {len(S['tasks'])}\n"
                    f"🛡 آنتی‌دیلیت: {S['antidelete']}\n"
                    f"🔕 معافیت‌ها: {len(S['ignored_chats'])}\n"
                    f"😴 AFK: {'روشن' if S['afk'] else 'خاموش'}\n"
                    f"⏰ زمان‌بندی‌شده‌ها: {len(S['scheduled'])}")
        elif action in ("معاف", "نادیده"):
            target = self._chat_target(event, arg)
            if target not in S["ignored_chats"]:
                S["ignored_chats"].append(target)
                save_state(S)
            await R(event, f"🔕 چت `{target}` معاف شد")
        elif action in ("شامل", "پیگرد"):
            target = self._chat_target(event, arg)
            if target in S["ignored_chats"]:
                S["ignored_chats"].remove(target)
                save_state(S)
            await R(event, f"🔔 چت `{target}` برگشت به پیگرد")
        elif action == "ایدی":
            if event.is_reply and not arg:
                rep = await event.get_reply_message()
                sender = await rep.get_sender()
                uname = (f"@{sender.username}"
                         if getattr(sender, "username", None) else "ندارد")
                await R(event,
                        f"🆔 آیدی کاربر: `{sender.id}`\nیوزرنیم: {uname}")
            elif arg:
                try:
                    ent = await self.cli.get_entity(arg)
                    name = getattr(ent, "title",
                                   getattr(ent, "first_name", ""))
                    await R(event, f"🆔 آیدی: `{ent.id}`\nاسم: {name}")
                except Exception as e:
                    await R(event, f"❌ پیدا نشد: {e}")
            else:
                await R(event, f"🆔 آیدی این چت: `{event.chat_id}`")
        elif action == "افک" and arg.startswith("روشن"):
            S["afk"] = True
            msg = arg[len("روشن"):].strip()
            if msg:
                S["afk_msg"] = msg
            self.afk_replied = set()
            save_state(S)
            await R(event, f"😴 AFK روشن شد\nپیام: {S['afk_msg']}")
        elif action == "افک" and arg == "خاموش":
            S["afk"] = False
            save_state(S)
            await R(event, "😊 AFK خاموش شد")
        elif action == "زمانبندی":
            sub = arg.split(maxsplit=2)
            if not sub:
                await R(event, "❌ مثال: `.زمانبندی اضافه 10m سلام`")
                return
            if sub[0] == "اضافه" and len(sub) == 3:
                secs = parse_delay(sub[1])
                if secs is None:
                    await R(event, "❌ فرمت زمان: `10s` `5m` `2h`")
                    return
                sid = max([s["id"] for s in S["scheduled"]] or [0]) + 1
                S["scheduled"].append({
                    "id": sid, "chat_id": event.chat_id,
                    "text": sub[2], "at": time.time() + secs})
                save_state(S)
                await R(event, f"⏰ زمان‌بندی شد (#{sid}) — {sub[1]} دیگه")
            elif sub[0] == "لیست":
                if S["scheduled"]:
                    lines = []
                    for s in S["scheduled"]:
                        left = int(s["at"] - time.time())
                        lines.append(f"#{s['id']}: {left}s دیگه — "
                                     f"{s['text'][:30]}")
                    await R(event, "⏰ لیست:\n" + "\n".join(lines))
                else:
                    await R(event, "📭 چیزی زمان‌بندی نشده")
            elif sub[0] == "حذف" and len(sub) == 2 and sub[1].isdigit():
                sid = int(sub[1])
                before = len(S["scheduled"])
                S["scheduled"] = [s for s in S["scheduled"]
                                  if s["id"] != sid]
                save_state(S)
                await R(event, "🗑 حذف شد" if len(S["scheduled"]) < before
                        else "❌ پیدا نشد")
            else:
                await R(event, "❌ مثال: `.زمانبندی اضافه 10m سلام`")
        elif action == "ریستارت":
            save_state(S)
            await R(event, "🔄 در حال ریستارت...")
            log.info("restarting on user command")
            await asyncio.sleep(1)
            os.execv(sys.executable, [sys.executable,
                                     str(Path(__file__).resolve())])
        else:
            # unknown command: stay silent (don't spam chats)
            pass

    def _chat_target(self, event, arg):
        a = arg.strip()
        if a.lstrip("-").isdigit():
            return int(a)
        return event.chat_id


def main():
    ensure_single_instance()
    bot = SelfBot()
    try:
        asyncio.run(bot.start())
    except KeyboardInterrupt:
        log.info("stopped by user")
    finally:
        try:
            save_state(bot.state)
        except Exception:
            log.warning("final state save failed")


if __name__ == "__main__":
    main()
