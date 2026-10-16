#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Selfbot v2 — duel entry (round 2 - audited, regressions fixed)
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
import urllib.parse
import urllib.request
from collections import OrderedDict
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

import jdatetime
from telethon import TelegramClient, events
from telethon.errors import FloodWaitError
from telethon.tl.functions.account import UpdateProfileRequest
from telethon.tl.functions.users import GetFullUserRequest

# All displayed times use Tehran timezone (server runs on UTC)
TEHRAN = ZoneInfo("Asia/Tehran")

PERSIAN_WEEKDAYS = {
    "Saturday": "شنبه",
    "Sunday": "یکشنبه",
    "Monday": "دوشنبه",
    "Tuesday": "سه‌شنبه",
    "Wednesday": "چهارشنبه",
    "Thursday": "پنجشنبه",
    "Friday": "جمعه",
}


def tehran_now():
    return datetime.now(TEHRAN)


def tehran_jnow():
    return jdatetime.datetime.now(TEHRAN)


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

# Reverse map to recover plain ASCII characters from stylized text
_REVERSE_FONT_MAP = {}
for _tbl in _FONT_TABLES.values():
    for _orig, _styled in _tbl.items():
        _REVERSE_FONT_MAP[_styled] = _orig

FONT_STYLES = list(_FONT_TABLES) + ["kashida", "overline"]


def unstylize(text):
    """Revert stylized unicode fonts, overlines, and kashidas back to plain text."""
    if not text:
        return ""
    text = text.replace("\u0305", "").replace("ـ", "")
    return "".join(_REVERSE_FONT_MAP.get(c, c) for c in text)


_TIME_RE = re.compile(r"\d{1,2}:\d{2}")


def strip_time_suffix(text):
    """Remove a trailing ' | HH:MM' (in ANY font style) and nothing else.

    Names/bios that legitimately contain ' | ' (e.g. 'Sefidan | CSS') are
    left untouched; only a final segment that *is* a time is removed.
    """
    if not text:
        return ""
    if "|" in text:
        head, _, tail = text.rpartition("|")
        if _TIME_RE.fullmatch(unstylize(tail).strip()):
            return head.rstrip()
    return text.strip()


def clean_base(text):
    """Derive a plain base text from the CURRENT profile (bot-styled):
    strip the time suffix, then revert font styling. Only use this when
    the bot itself may have styled the text — never on user-typed text."""
    return unstylize(strip_time_suffix(text))


def stylize(text, style):
    """Apply a unicode font style. Latin chars get mapped; Persian passes
    through for math fonts, kashida/overline work on Persian too."""
    text = unstylize(text)
    if style in _FONT_TABLES:
        t = _FONT_TABLES[style]
        return "".join(t.get(c, c) for c in text)
    if style == "kashida":
        out = []
        for c in text:
            out.append(c)
            if "\u0600" <= c <= "\u06FF" and c != " ":
                out.append("ـ")
        return "".join(out).rstrip("ـ")
    if style == "overline":
        return "".join(c + "\u0305" if c != " " else c for c in text)
    return text


def compose_with_limit(base_text, font_style, time_suffix, max_len):
    """Safely style base_text and append time_suffix without cutting off the time."""
    suffix = f" | {time_suffix}" if time_suffix else ""
    avail = max(0, max_len - len(suffix))
    styled = stylize(base_text, font_style) if font_style else base_text
    if len(styled) > avail:
        styled = styled[:avail].rstrip("ـ\u0305 ")
    return f"{styled}{suffix}"[:max_len]


# ---------- clock emojis (one per half hour, index 0 = 12:00) ----------
CLOCKS = ["🕛", "🕧", "🕐", "🕜", "🕑", "🕝", "🕒", "🕞", "🕓", "🕟",
          "🕔", "🕠", "🕕", "🕡", "🕖", "🕢", "🕗", "🕣", "🕘", "🕤",
          "🕙", "🕥", "🕚", "🕦"]


def norm_style(s):
    """Normalize a font style name; tolerates [brackets]. Returns a real
    style, picks randomly for 'رندم'/'[رندم]', or None if unknown."""
    s = s.strip().strip("[]").strip()
    if s == "رندم":
        return random.choice(FONT_STYLES)
    return s if s in FONT_STYLES else None


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
    "time_name": False,
    "time_style": "normal",  # font style for time display, or "رندم"
    "random_bio": False,
    "font_name_auto": False,  # auto-rotate name font every 5 min
    "font_bio_auto": False,   # auto-rotate bio font every 5 min
    "font_name_style": "bold",
    "font_bio_style": "bold",
    "base_bio": "",
    "base_name": "",
    "afk": False,
    "afk_msg": "در دسترس نیستم، بعداً جواب میدم 🙏",
    "scheduled": [],        # [{id, chat_id, text, at}]
    "stats": {"messages": 0, "commands": 0},
}

HELP = """
📖 **راهنمای سلف v2**
`.پنل` | `.پینگ` | `.تاریخ` | `.آمار` | `.تست`
`.شیر یا خط` | `.تاس` | `.عشق [نام]` | `.سنگ کاغذ قیچی [سنگ/کاغذ/قیچی]`
`.سیو` (ریپلای) | `.اسم [نام]` | `.بیو [متن]` | `.بیو رندم` | `.تایم بیو روشن/خاموش` | `.تایم اسم روشن/خاموش`
`.فونت اسم [استایل] [متن]` | `.فونت بیو [استایل] [متن]` | `.فونت [استایل] [متن]` | `.فونت لیست`
`.آنتی دیلیت روشن/خاموش` | `.آنتی ادیت روشن/خاموش`
`.اسپم [تعداد] [متن]` | `.حذف [تعداد]` | `.پاکسازی [تعداد]`
`.ترجمه` (ریپلای) | `.دانلود [لینک]` | `.حساب [عبارت]` | `.قیمت ارز` | `.قیمت طلا` | `.اذان [شهر]` | `.ساعت` | `.ساعت رندم`
`.تسک اضافه نام|کلمه|دکمه|تاخیر` | `.تسک حذف نام` | `.تسک لیست`
`.روشن` | `.خاموش` | `.وضعیت`
`.معاف [ایدی]` | `.شامل [ایدی]` | `.ایدی [یوزر]`
`.افک روشن [متن]` | `.افک خاموش`
`.زمانبندی اضافه 10m [متن]` | `.زمانبندی اضافه 14:30 [متن]` | `.زمانبندی تکرار 5m [متن]` | `.زمانبندی لیست` | `.زمانبندی حذف [ایدی]`
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


async def flood_aware(factory):
    """Await a coroutine factory, surviving Telegram FloodWait.
    Takes a zero-arg callable returning a coroutine (e.g. lambda),
    so a fresh coroutine is created on each retry."""
    while True:
        try:
            return await factory()
        except FloodWaitError as e:
            log.warning("FloodWait: sleeping %ss", e.seconds)
            await asyncio.sleep(e.seconds + 1)


def parse_delay(text):
    """'10m' / '2h' / '30s' -> seconds. Returns None on bad input."""
    m = re.fullmatch(r"(\d+)\s*([smh])", text.strip().lower())
    if not m:
        return None
    return int(m.group(1)) * {"s": 1, "m": 60, "h": 3600}[m.group(2)]



def parse_absolute_time(text):
    """'14:30' -> seconds until that time today (or tomorrow if passed).
    Returns None on bad input. Uses Asia/Tehran timezone."""
    m = re.fullmatch(r"(\d{1,2}):(\d{2})", text.strip())
    if not m:
        return None
    hour, minute = int(m.group(1)), int(m.group(2))
    if not (0 <= hour <= 23 and 0 <= minute <= 59):
        return None
    import datetime
    try:
        from zoneinfo import ZoneInfo
        tz = ZoneInfo("Asia/Tehran")
    except Exception:
        tz = None
    now = datetime.datetime.now(tz)
    target = now.replace(hour=hour, minute=minute, second=0, microsecond=0)
    if target <= now:
        target += datetime.timedelta(days=1)
    return (target - now).total_seconds()

def _sync_fetch_json(url, timeout=15):
    """Synchronous JSON fetch with proper User-Agent header."""
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.load(resp)


async def fetch_json(url, timeout=15):
    """Non-blocking JSON fetch via thread pool."""
    return await asyncio.to_thread(_sync_fetch_json, url, timeout)


def _is_youtube_url(url):
    """Check if URL is a YouTube link."""
    host = urllib.parse.urlparse(url).netloc.lower()
    return any(d in host for d in ("youtube.com", "youtu.be", "youtube-nocookie.com"))


def _sync_download_youtube(url, dl_dir):
    """Download YouTube video via yt-dlp. Returns (fpath, fname) or raises."""
    import subprocess
    dl_dir = str(dl_dir)
    # Get best quality under 100MB (720p max to stay reasonable)
    cmd = [
        "yt-dlp",
        "--no-playlist",
        "-f", "best[filesize<100M]/best",
        "--max-filesize", "100M",
        "--extractor-args", "youtube:player_client=android,ios",
        "--user-agent", "Mozilla/5.0 (Linux; Android 14) AppleWebKit/537.36",
        "-o", os.path.join(dl_dir, "%(title).50s [%(id)s].%(ext)s"),
        "--print", "after_move:filepath",
        "--no-warnings",
        url,
    ]
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
    if result.returncode != 0:
        err = result.stderr.strip().split(chr(10))[-1] if result.stderr else "unknown error"
        raise RuntimeError(f"yt-dlp failed: {err[:200]}")
    fpath = result.stdout.strip().split(chr(10))[-1]
    if not fpath or not os.path.exists(fpath):
        raise RuntimeError("yt-dlp produced no file")
    # Check size
    if os.path.getsize(fpath) > 100 * 1024 * 1024:
        os.unlink(fpath)
        raise ValueError("TOO_LARGE")
    return fpath, os.path.basename(fpath)


def _sync_download(url, dl_dir):
    """Synchronous file download. Returns (fpath, fname) or raises.
    Runs in a thread via asyncio.to_thread to avoid blocking the event loop."""
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=60) as resp:
        total = int(resp.headers.get("Content-Length", 0) or 0)
        if total > 100 * 1024 * 1024:
            raise ValueError("TOO_LARGE")
        cd = resp.headers.get("Content-Disposition", "")
        m = re.search(r'filename\*?=(?:UTF-8\'\')?"?([^";\n]+)"?', cd)
        fname = None
        if m:
            fname = urllib.parse.unquote(m.group(1).strip())
        if not fname:
            fname = urllib.parse.unquote(
                urllib.parse.urlparse(url).path.rsplit("/", 1)[-1])
        fname = re.sub(r'[^\w.\-() ]', '_', fname).strip("._ ") or "file"
        if "." not in fname:
            ext = resp.headers.get("Content-Type", "").split("/")[-1].split(";")[0]
            if ext and len(ext) <= 5:
                fname += f".{ext}"
        dl_dir.mkdir(exist_ok=True)
        fpath = dl_dir / fname
        i = 1
        while fpath.exists():
            fpath = dl_dir / f"{fpath.stem}_{i}{fpath.suffix}"
            i += 1
        size = 0
        with open(fpath, "wb") as f:
            while True:
                chunk = resp.read(256 * 1024)
                if not chunk:
                    break
                size += len(chunk)
                if size > 100 * 1024 * 1024:
                    f.close()
                    fpath.unlink(missing_ok=True)
                    raise ValueError("TOO_LARGE")
                f.write(chunk)
        return str(fpath), fname


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
        self.ac_last_clicked_msg = None
        # restore autoclicker from persisted state
        _ac = self.state.get("autoclick") or {}
        if _ac.get("active"):
            self.ac_active = True
            self.ac_target_chat = _ac.get("chat")
            self.ac_keyword = _ac.get("keyword")
            self.ac_button = _ac.get("button")
            self.ac_delay = _ac.get("delay", 1.0)
        self.bio_limit = 70  # 140 for Premium (set in start())

    # ---------- lifecycle ----------
    async def start(self):
        if not API_ID or not API_HASH:
            sys.exit("❌ API_ID / API_HASH must be set (env or .env file).")
        self.cli = TelegramClient(SESSION, int(API_ID), API_HASH)
        await self.cli.connect()
        if not await self.cli.is_user_authorized():
            sys.exit("❌ Session not authorized. Log in first, then run again.")

        me = await self.cli.get_entity("me")
        self.bio_limit = 140 if getattr(me, "premium", False) else 70
        state_changed = False
        if not self.state["base_name"]:
            self.state["base_name"] = strip_time_suffix(me.first_name or "")
            state_changed = True
        if not self.state["base_bio"]:
            try:
                full = await self.cli(GetFullUserRequest("me"))
                raw_bio = (full.full_user.about or "") if full and full.full_user else ""
                self.state["base_bio"] = strip_time_suffix(raw_bio)[:self.bio_limit]
            except Exception:
                self.state["base_bio"] = ""
            state_changed = True
        if state_changed:
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
            return await flood_aware(lambda: event.message.edit(text))
        else:
            return await flood_aware(lambda: event.reply(text))

    # ---------- watchers ----------
    async def _incoming(self, event):
        try:
            self.state["stats"]["messages"] += 1
            if event.message:
                content = event.raw_text or ("[مدیا بدون متن]" if event.message.media else "")
                key = (event.chat_id, event.message.id)
                self.msg_cache[key] = (event.chat_id, event.is_private, content)

            # AFK auto-reply: private chats only, once per chat per AFK session
            if (self.state["afk"] and event.is_private and not event.out
                    and event.chat_id not in self.afk_replied):
                sender = await event.get_sender()
                is_bot = getattr(sender, "bot", False) if sender else False
                if not is_bot:
                    self.afk_replied.add(event.chat_id)
                    await flood_aware(lambda: event.reply(self.state["afk_msg"]))
            if self.state["stats"]["messages"] % 50 == 0:
                save_state(self.state)
        except Exception:
            log.exception("incoming handler failed")

    async def _antidelete(self, event):
        try:
            chat = await event.get_chat() if event.chat_id else None
            is_chan_event = getattr(chat, "broadcast", False) if chat else False

            for mid in event.deleted_ids:
                # Look up message in cache (either by (event.chat_id, mid) or by scanning mid)
                entry_key = None
                entry_val = None
                if event.chat_id is not None and (event.chat_id, mid) in self.msg_cache:
                    entry_key = (event.chat_id, mid)
                    entry_val = self.msg_cache[entry_key]
                elif event.chat_id is None:
                    # Deletions in private chats / basic groups carry no
                    # chat id. Their message ids are unique per account, but
                    # channel/supergroup ids (-100...) are per-channel and
                    # can collide, so never match those; newest entry first.
                    for k, v in reversed(self.msg_cache.items()):
                        if (isinstance(k, tuple) and k[1] == mid
                                and k[0] is not None
                                and k[0] > -1000000000000):
                            entry_key = k
                            entry_val = v
                            break

                # Ignore uncached messages (e.g. our own outgoing deleted messages)
                if not entry_val or not isinstance(entry_val, tuple):
                    continue

                c_id, is_priv, txt = entry_val
                if c_id in self.state["ignored_chats"]:
                    continue

                cfg = self.state["antidelete"]
                enabled = cfg if cfg is not None else (is_chan_event or bool(is_priv))
                if not enabled:
                    continue

                # Remove from cache so duplicate events don't re-trigger
                self.msg_cache.pop(entry_key, None)
                msg_text = txt or "[مدیا/حذف شده]"
                await flood_aware(lambda m=msg_text: self.cli.send_message(
                    "me", f"🗑 حذف پیام:\n{m}"))
        except Exception:
            log.exception("antidelete failed")

    async def _antiedit(self, event):
        try:
            if not event.message or not event.message.edit_date:
                return
            # Skip own outgoing edits to avoid self-notifications
            if event.out:
                return
            if event.chat_id in self.state["ignored_chats"]:
                return
            cfg = self.state["antiedit"]
            enabled = cfg if cfg is not None else event.is_private
            if not enabled:
                return
            key = (event.chat_id, event.message.id)
            val = self.msg_cache.get(key)
            old = val[2] if isinstance(val, tuple) else "[نامشخص]"
            new_txt = event.raw_text or "[مدیا بدون متن]"
            if old == new_txt:
                return
            self.msg_cache[key] = (event.chat_id, event.is_private, new_txt)
            await flood_aware(lambda: self.cli.send_message(
                "me", f"✏️ ادیت پیام:\nقبل: {old}\nبعد: {new_txt}"))
        except Exception:
            log.exception("antiedit failed")

    # ---------- background loops ----------
    async def _loop_ac(self):
        while True:
            try:
                if self.ac_active and self.ac_target_chat and self.ac_keyword:
                    async for msg in self.cli.iter_messages(
                            self.ac_target_chat, limit=1):
                        stamp = (msg.id, msg.edit_date, msg.raw_text)
                        if not msg.buttons or stamp == self.ac_last_clicked_msg:
                            continue
                        # Match keyword in message text OR in any button text
                        btn_texts = [b.text or "" for row in msg.buttons for b in row]
                        kw = self.ac_keyword
                        if kw not in (msg.raw_text or "") and not any(kw in bt for bt in btn_texts):
                            continue
                        clicked = False
                        if self.ac_button:
                            # Fuzzy match: button containing the given text (ignores emoji)
                            for row in msg.buttons:
                                for b in row:
                                    if self.ac_button in (b.text or ""):
                                        await flood_aware(lambda btn=b: btn.click())
                                        clicked = True
                                        break
                                if clicked:
                                    break
                        if not clicked:
                            await flood_aware(lambda m=msg: m.click(0))
                        self.ac_last_clicked_msg = stamp
            except Exception:
                log.exception("autoclick loop failed")
            await asyncio.sleep(self.ac_delay)

    def _styled_time(self, t):
        """Style the time string per time_style setting."""
        ts = self.state.get("time_style", "normal")
        if ts == "رندم":
            ts = random.choice(FONT_STYLES)
        return stylize(t, ts) if ts != "normal" else t

    async def _loop_bio(self):
        while True:
            try:
                t = tehran_jnow().strftime("%H:%M")
                now_ts = time.time()

                # auto random bio every 10 minutes
                if self.state["random_bio"]:
                    last = getattr(self, "_last_random_bio", 0)
                    if now_ts - last >= 600:
                        q = random.choice(BIO_QUOTES)
                        while q == self.state.get("base_bio") and len(BIO_QUOTES) > 1:
                            q = random.choice(BIO_QUOTES)
                        self.state["base_bio"] = q
                        save_state(self.state)
                        self._last_random_bio = now_ts

                # auto-rotate name font every 5 minutes
                if self.state["font_name_auto"]:
                    last = getattr(self, "_last_font_name", 0)
                    if now_ts - last >= 300:
                        cur = self.state.get("font_name_style")
                        new = random.choice(FONT_STYLES)
                        while new == cur and len(FONT_STYLES) > 1:
                            new = random.choice(FONT_STYLES)
                        self.state["font_name_style"] = new
                        save_state(self.state)
                        self._last_font_name = now_ts

                # auto-rotate bio font every 5 minutes
                if self.state["font_bio_auto"]:
                    last = getattr(self, "_last_font_bio", 0)
                    if now_ts - last >= 300:
                        cur = self.state.get("font_bio_style")
                        new = random.choice(FONT_STYLES)
                        while new == cur and len(FONT_STYLES) > 1:
                            new = random.choice(FONT_STYLES)
                        self.state["font_bio_style"] = new
                        save_state(self.state)
                        self._last_font_bio = now_ts

                # compose and apply name: base -> font -> time (max 60 chars)
                if self.state["time_name"] or self.state["font_name_auto"]:
                    base_n = self.state["base_name"]
                    f_style = self.state.get("font_name_style", "bold") if self.state["font_name_auto"] else None
                    t_str = self._styled_time(t) if self.state["time_name"] else None
                    final_name = compose_with_limit(base_n, f_style, t_str, 60)
                    if final_name:
                        await flood_aware(lambda: self.cli(UpdateProfileRequest(
                            first_name=final_name)))

                # compose and apply bio: base -> font -> time (max 70 chars)
                if (self.state["time_bio"] or self.state["font_bio_auto"]
                        or self.state["random_bio"]):
                    base_b = self.state["base_bio"]
                    f_style = self.state.get("font_bio_style", "bold") if self.state["font_bio_auto"] else None
                    t_str = self._styled_time(t) if self.state["time_bio"] else None
                    final_bio = compose_with_limit(base_b, f_style, t_str, self.bio_limit)
                    await flood_aware(lambda: self.cli(UpdateProfileRequest(
                        about=final_bio)))
            except Exception:
                log.exception("bio loop failed")
            await asyncio.sleep(60)

    async def _loop_schedule(self):
        while True:
            try:
                now = time.time()
                due = [s for s in self.state["scheduled"] if s["at"] <= now]
                for s in due:
                    try:
                        await flood_aware(lambda item=s:
                            self.cli.send_message(item["chat_id"], item["text"]))
                        log.info("sent scheduled msg #%s", s["id"])
                        if s.get("repeat"):
                            s["at"] = time.time() + s["repeat"]
                            s.pop("fails", None)
                        else:
                            self.state["scheduled"].remove(s)
                    except Exception as e:
                        log.warning("scheduled msg #%s failed: %s", s["id"], e)
                        s["fails"] = s.get("fails", 0) + 1
                        if s["fails"] >= 3:
                            log.warning("dropping scheduled msg #%s", s["id"])
                            self.state["scheduled"].remove(s)
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
        # multi-word commands first (exact or followed by space)
        for mw in ("سنگ کاغذ قیچی", "شیر یا خط", "فونت اسم", "فونت بیو"):
            if body == mw or body.startswith(mw + " "):
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
                    "`.بیو رندم` — هر ۱۰ دقیقه خودکار",
                    "`.بیو رندم خاموش`",
                    "`.فونت اسم رندم` — چرخش خودکار هر ۵ دقیقه",
                    "`.فونت اسم خاموش`",
                    "`.فونت اسم [استایل] [متن]`",
                    "`.فونت بیو رندم` — چرخش خودکار هر ۵ دقیقه",
                    "`.فونت بیو خاموش`",
                    "`.فونت بیو [استایل] [متن]`",
                    "`.فونت [استایل|رندم] [متن]`",
                    "`.فونت لیست`",
                    "`.تایم بیو روشن/رندم/[استایل]/خاموش`",
                    "`.تایم اسم روشن/رندم/[استایل]/خاموش`",
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
                    "`.دانلود [لینک]`",
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
                    "`.زمانبندی اضافه 14:30 [متن]`",
                    "`.زمانبندی تکرار 5m [متن]`",
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
            await R(event, "🏓 ...")
            dt = (time.time() - t0) * 1000
            await R(event, f"🏓 پونگ! `{dt:.0f}ms` | {tehran_now():%H:%M:%S}")
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
            now = tehran_jnow()
            en_day = now.strftime("%A")
            fa_day = PERSIAN_WEEKDAYS.get(en_day, en_day)
            await R(event, f"📅 {now.strftime('%Y/%m/%d')} ({fa_day}) - {now.strftime('%H:%M:%S')}")
        elif action in ("شیر", "شیر یا خط"):
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
                path = await flood_aware(lambda: rep.download_media())
                await R(event, f"📥 ذخیره شد: `{path}`")
            else:
                await R(event, "❌ روی یک پیام مدیادار ریپلای کن")
        elif action == "اسم" and arg:
            clean_arg = arg.strip()[:60]
            S["base_name"] = clean_arg
            save_state(S)
            await flood_aware(lambda: self.cli(UpdateProfileRequest(first_name=clean_arg)))
            await R(event, f"✅ نام به «{clean_arg}» تغییر کرد")
        elif action == "بیو" and arg == "رندم":
            q = random.choice(BIO_QUOTES)
            S["base_bio"] = q
            S["random_bio"] = True
            save_state(S)
            self._last_random_bio = time.time()
            await flood_aware(lambda: self.cli(UpdateProfileRequest(about=q[:self.bio_limit])))
            await R(event, f"🎲 بیو رندم (هر ۱۰ دقیقه عوض می‌شه):\n{q}\n\nخاموش: `.بیو رندم خاموش`")
        elif action == "بیو" and arg == "رندم خاموش":
            S["random_bio"] = False
            save_state(S)
            await R(event, "🎲 بیو رندم خودکار خاموش شد")
        elif action == "بیو" and arg:
            clean_arg = arg.strip()[:self.bio_limit]
            S["base_bio"] = clean_arg
            S["random_bio"] = False
            save_state(S)
            await flood_aware(lambda: self.cli(UpdateProfileRequest(about=clean_arg)))
            await R(event, "✅ بیو تغییر کرد")
        elif action == "فونت":
            if arg == "لیست":
                lines = [f"▸ `{s}` — {stylize('Ali علی', s)}" for s in FONT_STYLES]
                lines.append("▸ `رندم` — یه استایل شانسی")
                await R(event, "🎨 فونت‌ها:\n" + "\n".join(lines))
            else:
                sp = arg.split(maxsplit=1)
                style = norm_style(sp[0]) if len(sp) == 2 else None
                if style:
                    await R(event, f"🎲 `{style}`\n{stylize(sp[1], style)}")
                else:
                    await R(event, "❓ `.فونت [استایل] [متن]`\n`.فونت لیست` برای دیدن استایل‌ها")
        elif action == "فونت اسم" and arg.strip().strip("[]").strip() == "رندم":
            me = await self.cli.get_me()
            base = clean_base(me.first_name or "") or S.get("base_name", "")
            S["base_name"] = base
            S["font_name_auto"] = True
            S["font_name_style"] = random.choice(FONT_STYLES)
            save_state(S)
            self._last_font_name = 0
            await R(event, "🎲 فونت خودکار اسم روشن شد — هر ۵ دقیقه یه فونت جدید\n"
                           "خاموش: `.فونت اسم خاموش`")
        elif action == "فونت اسم" and arg.strip() == "خاموش":
            S["font_name_auto"] = False
            save_state(S)
            await flood_aware(lambda: self.cli(UpdateProfileRequest(
                first_name=(S["base_name"] or "")[:60] or None)))
            await R(event, "🎲 فونت خودکار اسم خاموش شد")
        elif action == "فونت اسم" and arg:
            sp = arg.split(maxsplit=1)
            style = norm_style(sp[0]) if len(sp) >= 1 else None
            if style and len(sp) == 2:
                base = sp[1].strip()
                S["base_name"] = base
                save_state(S)
                name = stylize(base, style)[:60]
                await flood_aware(lambda: self.cli(UpdateProfileRequest(first_name=name)))
                await R(event, f"✅ نام با فونت `{style}`:\n{name}")
            elif style:
                me = await self.cli.get_me()
                base = clean_base(me.first_name or "") or S.get("base_name", "")
                S["base_name"] = base
                save_state(S)
                name = stylize(base, style)[:60]
                await flood_aware(lambda: self.cli(UpdateProfileRequest(first_name=name)))
                await R(event, f"✅ نام با فونت `{style}`:\n{name}")
            else:
                await R(event, "❓ `.فونت اسم [استایل] [متن]`\n"
                               "`.فونت اسم رندم` برای چرخش خودکار\n"
                               "`.فونت لیست` برای دیدن استایل‌ها")
        elif action == "فونت بیو" and arg.strip().strip("[]").strip() == "رندم":
            try:
                full = await self.cli(GetFullUserRequest("me"))
                cur_bio = clean_base(full.full_user.about or "")
            except Exception:
                cur_bio = ""
            base = cur_bio or S.get("base_bio", "")
            S["base_bio"] = base
            S["font_bio_auto"] = True
            S["font_bio_style"] = random.choice(FONT_STYLES)
            save_state(S)
            self._last_font_bio = 0
            await R(event, "🎲 فونت خودکار بیو روشن شد — هر ۵ دقیقه یه فونت جدید\n"
                           "خاموش: `.فونت بیو خاموش`")
        elif action == "فونت بیو" and arg.strip() == "خاموش":
            S["font_bio_auto"] = False
            save_state(S)
            await flood_aware(lambda: self.cli(UpdateProfileRequest(
                about=(S["base_bio"] or "")[:self.bio_limit])))
            await R(event, "🎲 فونت خودکار بیو خاموش شد")
        elif action == "فونت بیو" and arg:
            sp = arg.split(maxsplit=1)
            style = norm_style(sp[0]) if len(sp) >= 1 else None
            if style and len(sp) == 2:
                base = sp[1].strip()
                S["base_bio"] = base
                save_state(S)
                bio = stylize(base, style)[:self.bio_limit]
                await flood_aware(lambda: self.cli(UpdateProfileRequest(about=bio)))
                await R(event, f"✅ بیو با فونت `{style}` تغییر کرد")
            elif style:
                try:
                    full = await self.cli(GetFullUserRequest("me"))
                    cur_bio = clean_base(full.full_user.about or "")
                except Exception:
                    cur_bio = ""
                base = cur_bio or S.get("base_bio", "")
                S["base_bio"] = base
                save_state(S)
                bio = stylize(base, style)[:self.bio_limit]
                await flood_aware(lambda: self.cli(UpdateProfileRequest(about=bio)))
                await R(event, f"✅ بیو با فونت `{style}` تغییر کرد")
            else:
                await R(event, "❓ `.فونت بیو [استایل] [متن]`\n"
                               "`.فونت بیو رندم` برای چرخش خودکار\n"
                               "`.فونت لیست` برای دیدن استایل‌ها")
        elif action == "ساعت":
            if arg == "رندم":
                clock = random.choice(CLOCKS)
                h, m = random.randint(0, 23), random.choice([0, 30])
                await R(event, f"🎲 {clock} {h:02d}:{m:02d}")
            else:
                now = tehran_now()
                clock = CLOCKS[(now.hour % 12) * 2 + (1 if now.minute >= 30 else 0)]
                await R(event, f"{clock} {now.strftime('%H:%M')}")
        elif action == "تایم" and arg:
            parts = arg.split(maxsplit=1)
            if len(parts) == 2 and parts[0] in ("بیو", "اسم"):
                target, opt = parts
                opt_n = opt.strip().strip("[]").strip()
                is_bio = target == "بیو"
                if opt_n == "خاموش":
                    if is_bio:
                        S["time_bio"] = False
                        save_state(S)
                        await flood_aware(lambda: self.cli(
                            UpdateProfileRequest(about=(S["base_bio"] or "")[:self.bio_limit])))
                    else:
                        S["time_name"] = False
                        save_state(S)
                        await flood_aware(lambda: self.cli(UpdateProfileRequest(
                            first_name=(S["base_name"] or "")[:60] or None)))
                    await R(event, f"⏰ تایم {target} خاموش شد")
                else:
                    if opt_n == "روشن":
                        style = "normal"
                    elif opt_n == "رندم":
                        style = "رندم"
                    else:
                        style = norm_style(opt_n)
                    if not style:
                        await R(event, "❓ استایل نامعتبر — `.فونت لیست` رو ببین")
                        return
                    S["time_style"] = style
                    if is_bio:
                        if not S.get("base_bio"):
                            try:
                                full = await self.cli(GetFullUserRequest("me"))
                                S["base_bio"] = strip_time_suffix(full.full_user.about or "")[:self.bio_limit]
                            except Exception:
                                pass
                        S["time_bio"] = True
                    else:
                        me = await self.cli.get_me()
                        S["base_name"] = (clean_base(me.first_name or "") if S.get("font_name_auto") else strip_time_suffix(me.first_name or "")) or S.get("base_name", "")
                        S["time_name"] = True
                    save_state(S)
                    lbl = {"normal": "معمولی", "رندم": "رندم"}.get(style, style)
                    await R(event, f"⏰ تایم {target} روشن شد (استایل: {lbl})")
            else:
                await R(event, "❓ `.تایم بیو روشن/خاموش` یا `.تایم اسم روشن/خاموش`\n"
                               "استایل هم می‌تونی بدی: `.تایم اسم bold` یا `.تایم بیو رندم`")
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
                text_to_send = p[1]
                for _ in range(n):
                    await flood_aware(lambda: event.respond(text_to_send))
                    await asyncio.sleep(1)
                await R(event, f"✅ {n} پیام ارسال شد")
            else:
                await R(event, "❌ مثال: `.اسپم 5 سلام`")
        elif action == "حذف" and arg.isdigit():
            count = min(int(arg), 100)
            ids = []
            async for msg in self.cli.iter_messages(
                    event.chat_id, from_user="me", limit=count + 1):
                if msg.id == event.message.id:
                    continue
                ids.append(msg.id)
            deleted = 0
            if ids:
                try:
                    await flood_aware(lambda: self.cli.delete_messages(event.chat_id, ids))
                    deleted = len(ids)
                except Exception:
                    log.debug("batch delete failed, falling back to single")
                    for mid in ids:
                        try:
                            await flood_aware(lambda m=mid: self.cli.delete_messages(event.chat_id, m))
                            deleted += 1
                        except Exception:
                            pass
            await R(event, f"🗑 {deleted} پیام حذف شد")
        elif action == "پاکسازی" and arg.isdigit():
            count = min(int(arg), 100)
            ids = [event.message.id]
            async for msg in self.cli.iter_messages(
                    event.chat_id, from_user="me", limit=count + 1):
                if msg.id != event.message.id:
                    ids.append(msg.id)
            try:
                await flood_aware(lambda: self.cli.delete_messages(event.chat_id, ids))
            except Exception:
                log.debug("batch purge failed, falling back to single")
                for mid in ids:
                    try:
                        await flood_aware(lambda m=mid: self.cli.delete_messages(event.chat_id, m))
                    except Exception:
                        pass
        elif action == "حساب" and arg:
            try:
                res = safe_eval(arg)
                await R(event, f"🧮 نتیجه: `{res}`")
            except Exception as e:
                await R(event, f"❌ خطا در محاسبه: {e}")
        elif action == "دانلود" and arg:
            url = arg.strip()
            if not url.startswith(("http://", "https://")):
                url = "https://" + url
            msg = await R(event, "⏳ در حال دانلود...")
            try:
                dl_dir = BASE_DIR / "downloads"
                if _is_youtube_url(url):
                    fpath, fname = await asyncio.to_thread(_sync_download_youtube, url, dl_dir)
                else:
                    fpath, fname = await asyncio.to_thread(_sync_download, url, dl_dir)
                await flood_aware(lambda: self.cli.send_file(
                    event.chat_id, fpath,
                    caption=f"📥 {fname}\n`{url}`"))
                Path(fpath).unlink(missing_ok=True)
                if msg:
                    await flood_aware(lambda: msg.delete())
            except ValueError as e:
                if str(e) == "TOO_LARGE":
                    if msg:
                        await flood_aware(lambda: msg.edit("❌ فایل خیلی بزرگه (حداکثر ۱۰۰ مگ)"))
                else:
                    raise
            except Exception as e:
                log.warning("download failed: %s", e)
                try:
                    if msg:
                        await flood_aware(lambda: msg.edit(f"❌ دانلود نشد: {e}"))
                except Exception:
                    pass
        elif action == "ترجمه" and event.is_reply:
            rep = await event.get_reply_message()
            if rep and rep.text:
                q = urllib.parse.quote(rep.text[:1000])
                url = ("https://translate.googleapis.com/translate_a/single"
                       f"?client=gtx&sl=auto&tl=fa&dt=t&q={q}")
                try:
                    res = await fetch_json(url, timeout=15)
                    translated = "".join(part[0] for part in res[0] if part and part[0])
                    await R(event, f"🌐 ترجمه:\n{translated}")
                except Exception as e:
                    await R(event, f"❌ خطای ترجمه: {e}")
            else:
                await R(event, "❌ روی یک پیام متنی ریپلای کن")
        elif action == "اذان":
            city = arg or "Tehran"
            try:
                url = ("https://api.aladhan.com/v1/timingsByCity?city="
                       f"{urllib.parse.quote(city)}&country=Iran&method=7")
                data = await fetch_json(url, timeout=15)
                t = data["data"]["timings"]
                await R(event,
                        f"🕌 اوقات شرعی ({city}):\nطلوع: {t['Sunrise']}\n"
                        f"ظهر: {t['Dhuhr']}\nغروب: {t['Sunset']}\n"
                        f"مغرب: {t['Maghrib']}\nعشا: {t['Isha']}")
            except Exception:
                await R(event, "❌ خطا در دریافت اوقات شرعی")
        elif action in ("قیمت", "ارز", "طلا"):
            is_gold = action == "طلا" or "طلا" in arg
            try:
                key = "geram18" if is_gold else "price_dollar_rl"
                url = ("https://api.tgju.org/v1/market/indicator/"
                       f"summary-table-data/{key}")
                data = await fetch_json(url, timeout=15)
                p = data.get("data", {}).get("last", "نامشخص")
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
                if len(parts) >= 2 and parts[0] and parts[1]:
                    try:
                        d_val = float(parts[3].rstrip("s")) if len(parts) > 3 and parts[3] else 1.0
                    except ValueError:
                        d_val = 1.0
                    S["tasks"][parts[0]] = {
                        "keyword": parts[1],
                        "button": parts[2] if len(parts) > 2 and parts[2] else None,
                        "delay": max(1.0, d_val),
                    }
                    save_state(S)
                    await R(event, "➕ تسک اضافه شد")
                else:
                    await R(event, "❌ فرمت: `نام|کلمه|دکمه|تاخیر`")
            elif sub[0] == "حذف" and len(sub) > 1:
                S["tasks"].pop(sub[1].strip(), None)
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
            if task is None and not name and S["tasks"]:
                task = next(iter(S["tasks"].values()))
            if task:
                self.ac_active = True
                self.ac_keyword = task["keyword"]
                self.ac_button = task["button"]
                self.ac_delay = max(1.0, float(task.get("delay") or 1.0))
                self.ac_target_chat = event.chat_id
                self.ac_last_clicked_msg = None
                S["autoclick"] = {"active": True, "chat": event.chat_id,
                    "keyword": self.ac_keyword, "button": self.ac_button,
                    "delay": self.ac_delay}
                save_state(S)
                await R(event, "▶️ اتوکلیکر روشن شد")
            else:
                await R(event, "❌ تسک پیدا نشد. مثال: `.روشن نام_تسک`")
        elif action == "خاموش":
            self.ac_active = False
            S["autoclick"] = {"active": False}
            save_state(S)
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
                await R(event, "❌ مثال: `.زمانبندی اضافه 10m سلام` یا `.زمانبندی تکرار 5m سلام`")
                return
            if sub[0] == "اضافه" and len(sub) == 3:
                secs = parse_delay(sub[1])
                if secs is None:
                    secs = parse_absolute_time(sub[1])
                if secs is None:
                    await R(event, "❌ فرمت زمان: `10s` `5m` `2h`")
                    return
                sid = max([s["id"] for s in S["scheduled"]] or [0]) + 1
                S["scheduled"].append({
                    "id": sid, "chat_id": event.chat_id,
                    "text": sub[2], "at": time.time() + secs})
                save_state(S)
                await R(event, f"⏰ زمان‌بندی شد (#{sid}) — {sub[1]} دیگه")
            elif sub[0] == "تکرار" and len(sub) == 3:
                secs = parse_delay(sub[1])
                if secs is None or secs < 60:
                    await R(event, "❌ فرمت:  (حداقل 1 دقیقه)")
                    return
                sid = max([s["id"] for s in S["scheduled"]] or [0]) + 1
                S["scheduled"].append({
                    "id": sid, "chat_id": event.chat_id,
                    "text": sub[2], "at": time.time() + secs,
                    "repeat": secs})
                save_state(S)
                await R(event, f"🔁 تکرار فعال شد (#{sid}) — هر {sub[1]}")
            elif sub[0] == "لیست":
                if S["scheduled"]:
                    lines = []
                    for s in S["scheduled"]:
                        left = max(0, int(s["at"] - time.time()))
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
                await R(event, "❌ مثال: `.زمانبندی اضافه 10m سلام` یا `.زمانبندی تکرار 5m سلام`")
        elif action == "ریستارت":
            save_state(S)
            await R(event, "🔄 در حال ریستارت...")
            log.info("restarting on user command")
            await asyncio.sleep(1)
            global _lock_fd
            if _lock_fd:
                try:
                    fcntl.flock(_lock_fd, fcntl.LOCK_UN)
                    _lock_fd.close()
                except Exception:
                    pass
                _lock_fd = None
            try:
                await self.cli.disconnect()
            except Exception:
                pass
            os.execv(sys.executable, [sys.executable,
                                     str(Path(__file__).resolve())])

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
