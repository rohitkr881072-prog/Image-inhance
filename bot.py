# -*- coding: utf-8 -*-
"""
Photo Studio Pro — Premium Photo Editing Web Application
=========================================================
Single-file production application:
  • aiogram 3.x Telegram bot (passport photo maker — preserved)
  • aiohttp web server with full premium UI
  • Email/password authentication with sessions
  • Premium dashboard with comprehensive photo editor
  • Complete admin panel (access control, bans, maintenance, settings)
  • Pillow-based professional image processing pipeline

Required environment variables:
    BOT_TOKEN   - Telegram bot token from @BotFather
    SECRET_KEY  - Secret key for session tokens (auto-generated if missing)

Optional environment variables:
    WEBAPP_URL  - public HTTPS URL of this service
    OWNER_ID    - numeric Telegram id of the owner (auto-promoted to admin)
    PORT        - HTTP port for the aiohttp server
    DATABASE_PATH - path to SQLite database (default: ./photostudio.db)
    ADMIN_EMAIL - email of the initial admin account (created on first run)
    ADMIN_PASSWORD - password for the initial admin account
"""

import asyncio
import binascii
import hashlib
import hmac
import io
import json
import logging
import math
import os
import re
import secrets
import shutil
import sqlite3
import tempfile
import time
import uuid
import zipfile
from urllib.parse import parse_qsl
from pathlib import Path
from datetime import datetime, timedelta

import numpy as np
from PIL import Image, ImageChops, ImageDraw, ImageEnhance, ImageFilter, ImageOps
from aiohttp import web

from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.exceptions import TelegramAPIError
from aiogram.filters import Command, CommandStart
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
    BufferedInputFile,
    CallbackQuery,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Message,
    WebAppInfo,
)

# Optional advanced background removal
_rembg_remove = None
_REMBG_CHECKED = False
REMBG_AVAILABLE = False
_rembg_session = None


def _load_rembg() -> bool:
    global _rembg_remove, _REMBG_CHECKED, REMBG_AVAILABLE, _rembg_session
    if _REMBG_CHECKED:
        return REMBG_AVAILABLE
    _REMBG_CHECKED = True
    try:
        from rembg import remove, new_session
        _rembg_remove = remove
        try:
            _rembg_session = new_session("u2netp")
        except Exception:
            _rembg_session = None
        REMBG_AVAILABLE = True
    except Exception:
        logging.getLogger("photo-studio").warning(
            "rembg not available - using fallback", exc_info=True)
        _rembg_remove = None
        REMBG_AVAILABLE = False
    return REMBG_AVAILABLE


# --------------------------------------------------------------------------- #
# Configuration
# --------------------------------------------------------------------------- #

BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
WEBAPP_URL = os.getenv("WEBAPP_URL", "").strip().rstrip("/")
OWNER_ID = os.getenv("OWNER_ID", "").strip()
SECRET_KEY = os.getenv("SECRET_KEY", secrets.token_hex(32))
DATABASE_PATH = os.getenv("DATABASE_PATH", "photostudio.db")
ADMIN_EMAIL = os.getenv("ADMIN_EMAIL", "").strip().lower()
ADMIN_PASSWORD = os.getenv("ADMIN_PASSWORD", "").strip()


def _read_port() -> int:
    raw = os.getenv("PORT", "8080").strip()
    try:
        port = int(raw)
    except ValueError:
        return 8080
    return port if 1 <= port <= 65535 else 8080


PORT = _read_port()

DPI = 300
MARGIN_MM = 10.0
SPACING_MM = 1.5
BORDER_RGB = (0, 0, 0)
BORDER_MM = 0.5
RMBG_MAX_SIDE = 1400
USE_REMBG = os.getenv("USE_REMBG", "0").strip() in ("1", "true", "yes")
GENERATION_TIMEOUT = 150
JPEG_QUALITY = 95

MAX_QTY = 500
MAX_IMAGE_BYTES = 25 * 1024 * 1024
MAX_IMAGE_SIDE = 8000

MM_MIN_PAGE, MM_MAX_PAGE = 50.0, 1200.0
MM_MIN_PHOTO, MM_MAX_PHOTO = 10.0, 400.0

PAGE_SIZES = {
    "A4": (210.0, 297.0),
    "A3": (297.0, 420.0),
    "A5": (148.0, 210.0),
    "Letter": (215.9, 279.4),
    "Legal": (215.9, 355.6),
}

PHOTO_SIZES = {
    "25 × 35 mm": (25.0, 35.0),
    "30 × 40 mm": (30.0, 40.0),
    "35 × 45 mm": (35.0, 45.0),
    "2 × 2 inch": (50.8, 50.8),
}

BG_PRESETS = {
    "blue": ("🔵 Blue", (105, 109, 243)),
    "red": ("🔴 Red", (211, 47, 47)),
    "white": ("⚪ White", (255, 255, 255)),
    "green": ("🟢 Green", (46, 125, 50)),
}

HEX_RE = re.compile(r"^#?[0-9a-fA-F]{6}$")
EMAIL_RE = re.compile(r"^[a-zA-Z0-9._%+\-]+@[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,}$")
IMAGE_MIMES = {"image/jpeg", "image/png", "image/webp", "image/bmp", "image/tiff"}

TMP_ROOT = Path(tempfile.gettempdir()) / "photo_studio"
TMP_ROOT.mkdir(parents=True, exist_ok=True)

try:
    GENERATION_CONCURRENCY = max(1, int(os.getenv("GENERATION_CONCURRENCY", "1") or "1"))
except ValueError:
    GENERATION_CONCURRENCY = 1
_generation_semaphore = asyncio.Semaphore(GENERATION_CONCURRENCY)
_started_at = time.time()
_generation_count = 0
log = logging.getLogger("photo-studio")
_bot = None

SESSION_DURATION = 7 * 24 * 3600  # 7 days
PREVIEW_MAX_SIDE = 1200  # preview image max dimension


# --------------------------------------------------------------------------- #
# Database
# --------------------------------------------------------------------------- #

_db_path = DATABASE_PATH


def _db() -> sqlite3.Connection:
    conn = sqlite3.connect(_db_path)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA foreign_keys=ON")
    return conn


def init_db():
    conn = _db()
    try:
        conn.executescript("""
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            email TEXT UNIQUE NOT NULL,
            password_hash TEXT NOT NULL,
            password_salt TEXT NOT NULL,
            display_name TEXT DEFAULT '',
            created_at REAL NOT NULL,
            last_login REAL DEFAULT 0,
            is_active INTEGER DEFAULT 1,
            is_admin INTEGER DEFAULT 0,
            has_bot_access INTEGER DEFAULT 1,
            is_banned INTEGER DEFAULT 0,
            banned_reason TEXT DEFAULT '',
            telegram_id INTEGER DEFAULT NULL
        );

        CREATE TABLE IF NOT EXISTS sessions (
            token TEXT PRIMARY KEY,
            user_id INTEGER NOT NULL,
            created_at REAL NOT NULL,
            expires_at REAL NOT NULL,
            ip_address TEXT DEFAULT '',
            user_agent TEXT DEFAULT '',
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE
        );

        CREATE TABLE IF NOT EXISTS activity_logs (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            action TEXT NOT NULL,
            details TEXT DEFAULT '',
            ip_address TEXT DEFAULT '',
            timestamp REAL NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE SET NULL
        );

        CREATE TABLE IF NOT EXISTS system_settings (
            key TEXT PRIMARY KEY,
            value TEXT NOT NULL,
            updated_at REAL NOT NULL
        );

        CREATE TABLE IF NOT EXISTS usage_stats (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            action TEXT NOT NULL,
            file_count INTEGER DEFAULT 0,
            timestamp REAL NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE
        );

        CREATE INDEX IF NOT EXISTS idx_sessions_user ON sessions(user_id);
        CREATE INDEX IF NOT EXISTS idx_activity_user ON activity_logs(user_id);
        CREATE INDEX IF NOT EXISTS idx_usage_user ON usage_stats(user_id);
        """)
        conn.commit()

        # Default settings
        defaults = {
            "maintenance_mode": "0",
            "maintenance_message": "We are performing scheduled maintenance. Please check back soon.",
            "feature_passport_maker": "1",
            "feature_photo_editor": "1",
            "feature_background_removal": "1",
            "feature_filters": "1",
            "feature_pdf_export": "1",
            "feature_custom_dimensions": "1",
            "feature_batch_printing": "1",
            "max_upload_mb": "25",
            "site_name": "Photo Studio Pro",
            "registration_open": "1",
        }
        for k, v in defaults.items():
            conn.execute(
                "INSERT OR IGNORE INTO system_settings (key, value, updated_at) VALUES (?,?,?)",
                (k, v, time.time()))
        conn.commit()

        # Auto-create admin account
        if ADMIN_EMAIL and ADMIN_PASSWORD:
            row = conn.execute("SELECT id FROM users WHERE email=?", (ADMIN_EMAIL,)).fetchone()
            if row is None:
                salt = secrets.token_hex(16)
                phash = _hash_password(ADMIN_PASSWORD, salt)
                conn.execute(
                    "INSERT INTO users (email, password_hash, password_salt, display_name, "
                    "created_at, is_active, is_admin, has_bot_access) VALUES (?,?,?,?,?,?,1,1)",
                    (ADMIN_EMAIL, phash, salt, "Administrator", time.time(), 1))
                conn.commit()
                log.info("Admin account created: %s", ADMIN_EMAIL)
    finally:
        conn.close()


def _hash_password(password: str, salt: str) -> str:
    return hashlib.pbkdf2_hmac("sha256", password.encode(), salt.encode(), 100000).hex()


def _verify_password(password: str, salt: str, stored_hash: str) -> bool:
    return hmac.compare_digest(_hash_password(password, salt), stored_hash)


def db_get_user_by_email(email: str):
    conn = _db()
    try:
        return conn.execute("SELECT * FROM users WHERE email=?", (email.lower(),)).fetchone()
    finally:
        conn.close()


def db_get_user_by_id(uid: int):
    conn = _db()
    try:
        return conn.execute("SELECT * FROM users WHERE id=?", (uid,)).fetchone()
    finally:
        conn.close()


def db_create_user(email: str, password: str, display_name: str = ""):
    salt = secrets.token_hex(16)
    phash = _hash_password(password, salt)
    conn = _db()
    try:
        cur = conn.execute(
            "INSERT INTO users (email, password_hash, password_salt, display_name, "
            "created_at, is_active, is_admin, has_bot_access) VALUES (?,?,?,?,?,?,0,1)",
            (email.lower(), phash, salt, display_name, time.time()))
        conn.commit()
        return cur.lastrowid
    except sqlite3.IntegrityError:
        return None
    finally:
        conn.close()


def db_update_user(uid: int, **fields):
    allowed = {"display_name", "is_active", "is_admin", "has_bot_access",
               "is_banned", "banned_reason", "last_login", "telegram_id"}
    sets = []
    vals = []
    for k, v in fields.items():
        if k in allowed:
            sets.append(f"{k}=?")
            vals.append(v)
    if not sets:
        return
    vals.append(uid)
    conn = _db()
    try:
        conn.execute(f"UPDATE users SET {','.join(sets)} WHERE id=?", vals)
        conn.commit()
    finally:
        conn.close()


def db_list_users():
    conn = _db()
    try:
        return conn.execute(
            "SELECT * FROM users ORDER BY created_at DESC").fetchall()
    finally:
        conn.close()


def db_create_session(user_id: int, ip: str, ua: str) -> str:
    token = secrets.token_urlsafe(32)
    now = time.time()
    conn = _db()
    try:
        conn.execute(
            "INSERT INTO sessions (token, user_id, created_at, expires_at, ip_address, user_agent) "
            "VALUES (?,?,?,?,?,?)",
            (token, user_id, now, now + SESSION_DURATION, ip, ua[:200]))
        conn.execute("UPDATE users SET last_login=? WHERE id=?", (now, user_id))
        conn.commit()
        return token
    finally:
        conn.close()


def db_get_session(token: str):
    if not token:
        return None
    conn = _db()
    try:
        row = conn.execute(
            "SELECT * FROM sessions WHERE token=? AND expires_at>?",
            (token, time.time())).fetchone()
        if row:
            conn.execute("UPDATE sessions SET expires_at=? WHERE token=?",
                         (time.time() + SESSION_DURATION, token))
            conn.commit()
        return row
    finally:
        conn.close()


def db_delete_session(token: str):
    conn = _db()
    try:
        conn.execute("DELETE FROM sessions WHERE token=?", (token,))
        conn.commit()
    finally:
        conn.close()


def db_log_activity(user_id: int, action: str, details: str = "", ip: str = ""):
    conn = _db()
    try:
        conn.execute(
            "INSERT INTO activity_logs (user_id, action, details, ip_address, timestamp) "
            "VALUES (?,?,?,?,?)",
            (user_id, action, details, ip, time.time()))
        conn.commit()
    finally:
        conn.close()


def db_log_usage(user_id: int, action: str, file_count: int = 0):
    conn = _db()
    try:
        conn.execute(
            "INSERT INTO usage_stats (user_id, action, file_count, timestamp) VALUES (?,?,?,?)",
            (user_id, action, file_count, time.time()))
        conn.commit()
    finally:
        conn.close()


def db_get_setting(key: str, default: str = ""):
    conn = _db()
    try:
        row = conn.execute("SELECT value FROM system_settings WHERE key=?", (key,)).fetchone()
        return row["value"] if row else default
    finally:
        conn.close()


def db_set_setting(key: str, value: str):
    conn = _db()
    try:
        conn.execute(
            "INSERT INTO system_settings (key, value, updated_at) VALUES (?,?,?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value, updated_at=excluded.updated_at",
            (key, value, time.time()))
        conn.commit()
    finally:
        conn.close()


def db_get_all_settings():
    conn = _db()
    try:
        rows = conn.execute("SELECT key, value FROM system_settings").fetchall()
        return {r["key"]: r["value"] for r in rows}
    finally:
        conn.close()


def db_recent_activity(limit=100):
    conn = _db()
    try:
        return conn.execute(
            "SELECT a.*, u.email FROM activity_logs a LEFT JOIN users u ON a.user_id=u.id "
            "ORDER BY a.timestamp DESC LIMIT ?", (limit,)).fetchall()
    finally:
        conn.close()


def db_usage_summary():
    conn = _db()
    try:
        total = conn.execute("SELECT COUNT(*) as c FROM usage_stats").fetchone()["c"]
        by_action = conn.execute(
            "SELECT action, COUNT(*) as c, SUM(file_count) as fc FROM usage_stats GROUP BY action"
        ).fetchall()
        return {"total": total, "by_action": [dict(r) for r in by_action]}
    finally:
        conn.close()


def db_user_count():
    conn = _db()
    try:
        return conn.execute("SELECT COUNT(*) as c FROM users").fetchone()["c"]
    finally:
        conn.close()


def db_active_session_count():
    conn = _db()
    try:
        return conn.execute(
            "SELECT COUNT(*) as c FROM sessions WHERE expires_at>?",
            (time.time(),)).fetchone()["c"]
    finally:
        conn.close()


# --------------------------------------------------------------------------- #
# Helpers
# --------------------------------------------------------------------------- #

def verify_init_data(init_data: str):
    try:
        if not init_data or not BOT_TOKEN:
            return None
        pairs = dict(parse_qsl(init_data, keep_blank_values=True))
        their_hash = pairs.pop("hash", "")
        check = "\n".join(f"{k}={v}" for k, v in sorted(pairs.items()))
        secret = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
        mine = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(mine, their_hash):
            return None
        if time.time() - int(pairs.get("auth_date", "0")) > 86400:
            return None
        return int(json.loads(pairs["user"])["id"])
    except Exception:
        return None


def mm_to_px(mm: float, dpi: int = DPI) -> int:
    return max(1, int(round(mm / 25.4 * dpi)))


def unit_to_mm(value: float, unit: str) -> float:
    if unit == "cm":
        return value * 10.0
    if unit == "inch":
        return value * 25.4
    return value


def parse_float(text: str):
    try:
        v = float(text.strip().replace(",", "."))
        if math.isfinite(v):
            return v
    except (ValueError, AttributeError):
        pass
    return None


def parse_hex_color(text: str):
    if not text:
        return None
    t = text.strip()
    if not HEX_RE.match(t):
        return None
    t = t.lstrip("#")
    return (int(t[0:2], 16), int(t[2:4], 16), int(t[4:6], 16))


def rgb_to_hex(rgb) -> str:
    return "#{:02X}{:02X}{:02X}".format(*rgb)


def user_dir(user_id) -> Path:
    key = str(user_id)
    d = TMP_ROOT / key
    d.mkdir(parents=True, exist_ok=True)
    return d


def cleanup_dir(path: Path) -> None:
    try:
        if path.is_dir():
            shutil.rmtree(path, ignore_errors=True)
    except Exception:
        pass


def compute_grid(page_w_mm, page_h_mm, pw_mm, ph_mm):
    printable_w = page_w_mm - 2 * MARGIN_MM
    printable_h = page_h_mm - 2 * MARGIN_MM
    if pw_mm > printable_w or ph_mm > printable_h:
        return None
    cols = int((printable_w + SPACING_MM) // (pw_mm + SPACING_MM))
    rows = int((printable_h + SPACING_MM) // (ph_mm + SPACING_MM))
    if cols < 1 or rows < 1:
        return None
    return cols, rows


# --------------------------------------------------------------------------- #
# Image processing
# --------------------------------------------------------------------------- #

def load_image(data: bytes) -> Image.Image:
    if len(data) > MAX_IMAGE_BYTES:
        raise ValueError("Image file is too large (max 25 MB).")
    img = Image.open(io.BytesIO(data))
    img = ImageOps.exif_transpose(img)
    img.load()
    if max(img.size) > MAX_IMAGE_SIDE:
        raise ValueError("Image dimensions are too large.")
    if img.mode not in ("RGB", "RGBA"):
        img = img.convert("RGB")
    return img


def _ensure_rgb(img: Image.Image) -> Image.Image:
    if img.mode == "RGBA":
        bg = Image.new("RGB", img.size, (255, 255, 255))
        bg.paste(img, mask=img.getchannel("A"))
        return bg
    return img.convert("RGB") if img.mode != "RGB" else img


# --- Adjustments (factor 1.0 = no change) ---

def adj_brightness(img: Image.Image, factor: float) -> Image.Image:
    factor = max(0.0, min(3.0, factor))
    if abs(factor - 1.0) < 0.001:
        return img
    return ImageEnhance.Brightness(img).enhance(factor)


def adj_contrast(img: Image.Image, factor: float) -> Image.Image:
    factor = max(0.0, min(3.0, factor))
    if abs(factor - 1.0) < 0.001:
        return img
    return ImageEnhance.Contrast(img).enhance(factor)


def adj_saturation(img: Image.Image, factor: float) -> Image.Image:
    factor = max(0.0, min(3.0, factor))
    if abs(factor - 1.0) < 0.001:
        return img
    return ImageEnhance.Color(img).enhance(factor)


def adj_sharpness(img: Image.Image, factor: float) -> Image.Image:
    factor = max(0.0, min(5.0, factor))
    if abs(factor - 1.0) < 0.001:
        return img
    return ImageEnhance.Sharpness(img).enhance(factor)


def adj_exposure(img: Image.Image, stops: float) -> Image.Image:
    """Adjust exposure in stops (-3 to +3). Uses gamma correction for natural results."""
    stops = max(-3.0, min(3.0, stops))
    if abs(stops) < 0.01:
        return img
    gamma = 1.0 / (2.0 ** stops)
    gamma = max(0.1, min(10.0, gamma))
    arr = np.asarray(img).astype(np.float32) / 255.0
    arr = np.clip(arr ** gamma, 0.0, 1.0)
    return Image.fromarray((arr * 255).astype(np.uint8), img.mode)


def adj_temperature(img: Image.Image, warmth: float) -> Image.Image:
    """Warmth: -100 (cool) to +100 (warm). 0 = neutral."""
    warmth = max(-100.0, min(100.0, warmth)) / 100.0
    if abs(warmth) < 0.01:
        return img
    arr = np.asarray(img).astype(np.float32)
    r_shift = warmth * 30
    b_shift = -warmth * 30
    arr[..., 0] = np.clip(arr[..., 0] + r_shift, 0, 255)
    arr[..., 2] = np.clip(arr[..., 2] + b_shift, 0, 255)
    return Image.fromarray(arr.astype(np.uint8), img.mode)


def adj_tint(img: Image.Image, tint: float) -> Image.Image:
    """Tint: -100 (green) to +100 (magenta). 0 = neutral."""
    tint = max(-100.0, min(100.0, tint)) / 100.0
    if abs(tint) < 0.01:
        return img
    arr = np.asarray(img).astype(np.float32)
    g_shift = -tint * 25
    arr[..., 1] = np.clip(arr[..., 1] + g_shift, 0, 255)
    return Image.fromarray(arr.astype(np.uint8), img.mode)


def adj_color_balance(img: Image.Image, r: float, g: float, b: float) -> Image.Image:
    """Per-channel balance: -100 to +100 for each channel."""
    arr = np.asarray(img).astype(np.float32)
    shifts = [max(-100, min(100, r)), max(-100, min(100, g)), max(-100, min(100, b))]
    for i in range(3):
        arr[..., i] = np.clip(arr[..., i] + shifts[i], 0, 255)
    return Image.fromarray(arr.astype(np.uint8), img.mode)


def adj_skin_tone(img: Image.Image, warmth: float, smoothness: float) -> Image.Image:
    """Enhance skin tones naturally. warmth: -50..50, smoothness: 0..100."""
    warmth = max(-50.0, min(50.0, warmth)) / 50.0
    smoothness = max(0.0, min(100.0, smoothness)) / 100.0
    arr = np.asarray(img).astype(np.float32)

    # Detect skin-tone pixels (warm, moderate saturation, not too dark/light)
    r, g, b = arr[..., 0], arr[..., 1], arr[..., 2]
    skin_mask = (
        (r > 95) & (g > 40) & (b > 20) &
        (r > g) & (r > b) &
        (r - g > 12) &
        (np.maximum(r, np.maximum(g, b)) - np.minimum(r, np.minimum(g, b)) > 12)
    ).astype(np.float32)

    if warmth != 0:
        warmth_arr = np.zeros_like(arr)
        warmth_arr[..., 0] = warmth * 18
        warmth_arr[..., 2] = -warmth * 12
        arr += warmth_arr * skin_mask[..., None]
        arr = np.clip(arr, 0, 255)

    if smoothness > 0:
        smoothed = Image.fromarray(arr.astype(np.uint8), img.mode).filter(
            ImageFilter.SMOOTH_MORE)
        # Bilateral-like: blend smoothed with original only on skin
        sm_arr = np.asarray(smoothed).astype(np.float32)
        blend = skin_mask * smoothness * 0.6
        arr = arr * (1 - blend[..., None]) + sm_arr * blend[..., None]

    return Image.fromarray(np.clip(arr, 0, 255).astype(np.uint8), img.mode)


def adj_vignette(img: Image.Image, strength: float) -> Image.Image:
    """Vignette: 0 (none) to 100 (strong)."""
    strength = max(0.0, min(100.0, strength)) / 100.0
    if strength < 0.01:
        return img
    w, h = img.size
    arr = np.asarray(img).astype(np.float32)
    Y, X = np.ogrid[:h, :w]
    cx, cy = w / 2, h / 2
    dist = np.sqrt(((X - cx) / cx) ** 2 + ((Y - cy) / cy) ** 2)
    mask = np.clip(1.0 - dist * strength * 0.9, 0.0, 1.0)
    arr *= mask[..., None]
    return Image.fromarray(np.clip(arr, 0, 255).astype(np.uint8), img.mode)


def adj_gamma(img: Image.Image, gamma: float) -> Image.Image:
    gamma = max(0.1, min(10.0, gamma))
    arr = np.asarray(img).astype(np.float32) / 255.0
    arr = np.clip(arr ** (1.0 / gamma), 0.0, 1.0)
    return Image.fromarray((arr * 255).astype(np.uint8), img.mode)


def auto_enhance(img: Image.Image) -> Image.Image:
    """Auto-enhance: auto-contrast + mild saturation + mild sharpen + auto-levels."""
    img = ImageOps.autocontrast(img, cutoff=1)
    img = ImageEnhance.Color(img).enhance(1.08)
    img = ImageEnhance.Sharpness(img).enhance(1.15)
    img = ImageEnhance.Contrast(img).enhance(1.05)
    return img


def denoise_image(img: Image.Image, strength: float = 1.0) -> Image.Image:
    """Reduce noise while preserving edges."""
    strength = max(0.0, min(2.0, strength))
    if strength < 0.01:
        return img
    if strength >= 1.5:
        return img.filter(ImageFilter.MedianFilter(size=3))
    return img.filter(ImageFilter.SMOOTH_MORE)


# --- Filters ---

FILTERS = {
    "original": None,
    "auto_enhance": "auto_enhance",
    "vivid": "vivid",
    "warm": "warm",
    "cool": "cool",
    "vintage": "vintage",
    "sepia": "sepia",
    "bw": "bw",
    "noir": "noir",
    "fade": "fade",
    "dramatic": "dramatic",
    "soft_glow": "soft_glow",
    "matte": "matte",
    "chrome": "chrome",
}


def apply_filter(img: Image.Image, name: str) -> Image.Image:
    if name == "original" or name not in FILTERS or FILTERS[name] is None:
        return img
    arr = np.asarray(img).astype(np.float32)
    r, g, b = arr[..., 0], arr[..., 1], arr[..., 2]

    if name == "vivid":
        img = ImageEnhance.Color(img).enhance(1.35)
        img = ImageEnhance.Contrast(img).enhance(1.12)
        img = ImageEnhance.Sharpness(img).enhance(1.1)
        return img
    elif name == "warm":
        arr2 = arr.copy()
        arr2[..., 0] = np.clip(arr2[..., 0] + 15, 0, 255)
        arr2[..., 2] = np.clip(arr2[..., 2] - 12, 0, 255)
        img = Image.fromarray(arr2.astype(np.uint8), img.mode)
        return ImageEnhance.Color(img).enhance(1.1)
    elif name == "cool":
        arr2 = arr.copy()
        arr2[..., 0] = np.clip(arr2[..., 0] - 10, 0, 255)
        arr2[..., 2] = np.clip(arr2[..., 2] + 15, 0, 255)
        img = Image.fromarray(arr2.astype(np.uint8), img.mode)
        return ImageEnhance.Color(img).enhance(1.08)
    elif name == "vintage":
        # sepia-ish + vignette + fade
        tr = 0.393 * r + 0.769 * g + 0.189 * b
        tg = 0.349 * r + 0.686 * g + 0.168 * b
        tb = 0.272 * r + 0.534 * g + 0.131 * b
        arr2 = np.stack([tr, tg, tb], axis=-1)
        arr2 = np.clip(arr2 * 0.85 + 30, 0, 255)  # fade/lift
        img = Image.fromarray(arr2.astype(np.uint8), img.mode)
        return adj_vignette(img, 35)
    elif name == "sepia":
        tr = 0.393 * r + 0.769 * g + 0.189 * b
        tg = 0.349 * r + 0.686 * g + 0.168 * b
        tb = 0.272 * r + 0.534 * g + 0.131 * b
        arr2 = np.stack([tr, tg, tb], axis=-1)
        return Image.fromarray(np.clip(arr2, 0, 255).astype(np.uint8), img.mode)
    elif name == "bw":
        gray = 0.299 * r + 0.587 * g + 0.114 * b
        arr2 = np.stack([gray, gray, gray], axis=-1)
        img = Image.fromarray(arr2.astype(np.uint8), img.mode)
        return ImageEnhance.Contrast(img).enhance(1.1)
    elif name == "noir":
        gray = 0.299 * r + 0.587 * g + 0.114 * b
        arr2 = np.stack([gray, gray, gray], axis=-1)
        img = Image.fromarray(arr2.astype(np.uint8), img.mode)
        img = ImageEnhance.Contrast(img).enhance(1.4)
        return adj_vignette(img, 50)
    elif name == "fade":
        arr2 = arr * 0.82 + 40
        img = Image.fromarray(np.clip(arr2, 0, 255).astype(np.uint8), img.mode)
        return ImageEnhance.Contrast(img).enhance(0.9)
    elif name == "dramatic":
        img = ImageEnhance.Contrast(img).enhance(1.3)
        img = ImageEnhance.Color(img).enhance(1.15)
        img = ImageEnhance.Sharpness(img).enhance(1.2)
        return adj_vignette(img, 40)
    elif name == "soft_glow":
        bright = ImageEnhance.Brightness(img).enhance(1.05)
        blur = bright.filter(ImageFilter.GaussianBlur(3))
        blur = ImageEnhance.Brightness(blur).enhance(1.3)
        return ImageChops.screen(img, blur)
    elif name == "matte":
        arr2 = arr * 0.88 + 25
        img = Image.fromarray(np.clip(arr2, 0, 255).astype(np.uint8), img.mode)
        return ImageEnhance.Contrast(img).enhance(0.92)
    elif name == "chrome":
        img = ImageEnhance.Color(img).enhance(0.7)
        img = ImageEnhance.Contrast(img).enhance(1.2)
        return adj_temperature(img, 10)
    return img


# --- Crop / Resize / Rotate / Flip ---

def crop_image(img: Image.Image, x: int, y: int, w: int, h: int) -> Image.Image:
    x = max(0, x)
    y = max(0, y)
    w = max(1, min(w, img.width - x))
    h = max(1, min(h, img.height - y))
    return img.crop((x, y, x + w, y + h))


def crop_to_ratio(img: Image.Image, ratio: float) -> Image.Image:
    w, h = img.size
    cur = w / h
    if abs(cur - ratio) < 1e-3:
        return img
    if cur > ratio:
        new_w = int(round(h * ratio))
        x0 = (w - new_w) // 2
        return img.crop((x0, 0, x0 + new_w, h))
    new_h = int(round(w / ratio))
    y0 = int(round((h - new_h) * 0.30))
    y0 = max(0, min(h - new_h, y0))
    return img.crop((0, y0, w, y0 + new_h))


def resize_image(img: Image.Image, width: int, height: int) -> Image.Image:
    width = max(1, min(width, MAX_IMAGE_SIDE))
    height = max(1, min(height, MAX_IMAGE_SIDE))
    return img.resize((width, height), Image.LANCZOS)


def rotate_image(img: Image.Image, degrees: float) -> Image.Image:
    if degrees == 0:
        return img
    rotated = img.rotate(-degrees, expand=True, fillcolor=(255, 255, 255))
    return rotated


def flip_image(img: Image.Image, direction: str) -> Image.Image:
    if direction == "horizontal":
        return ImageOps.mirror(img)
    elif direction == "vertical":
        return ImageOps.flip(img)
    return img


# --- Background ---

def _bg_mask_from_border(small: Image.Image):
    arr = np.asarray(small).astype(np.float32)
    h, w, _ = arr.shape
    b = max(3, min(h, w) // 50)
    border = np.concatenate([
        arr[:b, :, :].reshape(-1, 3),
        arr[:, :b, :].reshape(-1, 3),
        arr[:, -b:, :].reshape(-1, 3),
    ])
    ref = np.median(border, axis=0)
    spread = np.sqrt(((border - ref) ** 2).sum(axis=1))
    tol = float(np.clip(np.percentile(spread, 90) * 1.6 + 18, 30, 80))
    dist = np.sqrt(((arr - ref) ** 2).sum(axis=2))
    cand = dist < tol
    seed = np.zeros_like(cand)
    seed[:b, :] = True
    seed[:, :b] = True
    seed[:, -b:] = True
    seed &= cand
    try:
        from scipy import ndimage
        lab, _n = ndimage.label(cand)
        keep = np.unique(lab[seed])
        keep = keep[keep != 0]
        bg = np.isin(lab, keep)
    except Exception:
        cur = Image.fromarray((seed * 255).astype(np.uint8), "L")
        cmask = Image.fromarray((cand * 255).astype(np.uint8), "L")
        prev = -1
        for _ in range(400):
            cur = ImageChops.multiply(cur.filter(ImageFilter.MaxFilter(9)), cmask)
            tot = int(np.asarray(cur).sum())
            if tot == prev:
                break
            prev = tot
        bg = np.asarray(cur) > 127
    return dist, tol, bg


def _builtin_bg_replace(img: Image.Image, rgb):
    k = min(1.0, 1100 / max(img.size))
    small = img if k >= 1 else img.resize(
        (max(1, int(img.width * k)), max(1, int(img.height * k))), Image.BILINEAR)
    dist, tol, bg = _bg_mask_from_border(small)
    frac = float(bg.mean())
    if frac < 0.06 or frac > 0.85:
        return img, False
    if float(bg[int(bg.shape[0] * 0.8):, :].mean()) > 0.45:
        return img, False
    bgimg = Image.fromarray((bg * 255).astype(np.uint8), "L")
    band = bgimg.filter(ImageFilter.MaxFilter(7))
    band_np = (np.asarray(band) > 127) & (~bg)
    fg = np.ones_like(dist, dtype=np.float32)
    fg[bg] = 0.0
    soft = np.clip((dist - tol) / (tol * 1.2), 0.0, 1.0)
    fg[band_np] = soft[band_np]
    alpha = Image.fromarray((fg * 255).astype(np.uint8), "L")
    alpha = alpha.filter(ImageFilter.GaussianBlur(1.2))
    if alpha.size != img.size:
        alpha = alpha.resize(img.size, Image.BICUBIC)
    new_bg = Image.new("RGB", img.size, rgb)
    return Image.composite(img, new_bg, alpha), True


def _rembg_replace(img: Image.Image, rgb):
    small = img
    if max(img.size) > RMBG_MAX_SIDE:
        k = RMBG_MAX_SIDE / max(img.size)
        small = img.resize((max(1, int(img.width * k)),
                           max(1, int(img.height * k))), Image.LANCZOS)
    kw = {"session": _rembg_session} if _rembg_session else {}
    out = _rembg_remove(small, **kw)
    if isinstance(out, bytes):
        out = Image.open(io.BytesIO(out))
    alpha = out.convert("RGBA").getchannel("A")
    if alpha.size != img.size:
        alpha = alpha.resize(img.size, Image.LANCZOS)
    alpha = alpha.filter(ImageFilter.GaussianBlur(0.8))
    return Image.composite(img, Image.new("RGB", img.size, rgb), alpha)


def replace_background(img: Image.Image, rgb):
    if USE_REMBG and _load_rembg():
        try:
            return _rembg_replace(img, rgb), None
        except Exception:
            log.warning("rembg failed; using built-in method", exc_info=True)
    try:
        out, ok = _builtin_bg_replace(img, rgb)
        if ok:
            return out, None
        return img, ("⚠️ Background could not be detected automatically. "
                     "Original background kept.")
    except Exception:
        log.warning("built-in background replace failed", exc_info=True)
        return img, "⚠️ Background change failed. Original background kept."


def remove_background(img: Image.Image) -> Image.Image:
    """Return RGBA image with transparent background."""
    if USE_REMBG and _load_rembg():
        try:
            small = img
            if max(img.size) > RMBG_MAX_SIDE:
                k = RMBG_MAX_SIDE / max(img.size)
                small = img.resize((max(1, int(img.width * k)),
                                   max(1, int(img.height * k))), Image.LANCZOS)
            kw = {"session": _rembg_session} if _rembg_session else {}
            out = _rembg_remove(small, **kw)
            if isinstance(out, bytes):
                out = Image.open(io.BytesIO(out))
            rgba = out.convert("RGBA")
            if rgba.size != img.size:
                rgba = rgba.resize(img.size, Image.LANCZOS)
            return rgba
        except Exception:
            pass
    # Fallback: detect bg, make transparent
    k = min(1.0, 1100 / max(img.size))
    small = img if k >= 1 else img.resize(
        (max(1, int(img.width * k)), max(1, int(img.height * k))), Image.BILINEAR)
    dist, tol, bg = _bg_mask_from_border(small)
    fg = np.ones_like(dist, dtype=np.float32)
    fg[bg] = 0.0
    soft = np.clip((dist - tol) / (tol * 1.2), 0.0, 1.0)
    alpha = Image.fromarray((fg * 255).astype(np.uint8), "L")
    if alpha.size != img.size:
        alpha = alpha.resize(img.size, Image.BICUBIC)
    alpha = alpha.filter(ImageFilter.GaussianBlur(1.0))
    rgba = img.convert("RGBA")
    rgba.putalpha(alpha)
    return rgba


# --- Export ---

def export_image(img: Image.Image, fmt: str, quality: int = 95) -> bytes:
    buf = io.BytesIO()
    fmt = fmt.lower()
    if fmt in ("jpg", "jpeg"):
        out = _ensure_rgb(img)
        out.save(buf, "JPEG", quality=max(1, min(100, quality)),
                 subsampling=0, optimize=True)
    elif fmt == "png":
        out = img if img.mode in ("RGBA", "RGB") else img.convert("RGB")
        out.save(buf, "PNG", optimize=True)
    elif fmt == "webp":
        out = _ensure_rgb(img)
        out.save(buf, "WEBP", quality=max(1, min(100, quality)))
    elif fmt == "bmp":
        _ensure_rgb(img).save(buf, "BMP")
    elif fmt == "tiff":
        _ensure_rgb(img).save(buf, "TIFF")
    else:
        _ensure_rgb(img).save(buf, "JPEG", quality=95)
    return buf.getvalue()


def compress_image(img: Image.Image, quality: int) -> bytes:
    return export_image(img, "jpg", quality)


# --- Apply a chain of operations ---

def apply_operations(img: Image.Image, ops: list) -> Image.Image:
    """Apply an ordered list of operation dicts to an image."""
    for op in ops:
        t = op.get("op")
        if t == "brightness":
            img = adj_brightness(img, op.get("factor", 1.0))
        elif t == "contrast":
            img = adj_contrast(img, op.get("factor", 1.0))
        elif t == "saturation":
            img = adj_saturation(img, op.get("factor", 1.0))
        elif t == "sharpness":
            img = adj_sharpness(img, op.get("factor", 1.0))
        elif t == "exposure":
            img = adj_exposure(img, op.get("stops", 0.0))
        elif t == "temperature":
            img = adj_temperature(img, op.get("value", 0.0))
        elif t == "tint":
            img = adj_tint(img, op.get("value", 0.0))
        elif t == "color_balance":
            img = adj_color_balance(img, op.get("r", 0), op.get("g", 0), op.get("b", 0))
        elif t == "skin_tone":
            img = adj_skin_tone(img, op.get("warmth", 0), op.get("smoothness", 0))
        elif t == "vignette":
            img = adj_vignette(img, op.get("value", 0))
        elif t == "gamma":
            img = adj_gamma(img, op.get("value", 1.0))
        elif t == "filter":
            img = apply_filter(img, op.get("name", "original"))
        elif t == "auto_enhance":
            img = auto_enhance(img)
        elif t == "denoise":
            img = denoise_image(img, op.get("strength", 1.0))
        elif t == "crop":
            img = crop_image(img, op.get("x", 0), op.get("y", 0),
                            op.get("w", img.width), op.get("h", img.height))
        elif t == "crop_ratio":
            img = crop_to_ratio(img, op.get("ratio", 1.0))
        elif t == "resize":
            img = resize_image(img, op.get("w", img.width), op.get("h", img.height))
        elif t == "rotate":
            img = rotate_image(img, op.get("degrees", 0))
        elif t == "flip":
            img = flip_image(img, op.get("direction", "horizontal"))
        elif t == "background":
            rgb = parse_hex_color(op.get("hex", "#FFFFFF"))
            img, _ = replace_background(img, rgb)
        elif t == "remove_bg":
            img = remove_background(img)
    return img


def make_preview(img: Image.Image) -> Image.Image:
    """Downscale for fast preview."""
    w, h = img.size
    if max(w, h) > PREVIEW_MAX_SIDE:
        k = PREVIEW_MAX_SIDE / max(w, h)
        return img.resize((max(1, int(w * k)), max(1, int(h * k))), Image.LANCZOS)
    return img


# --- Passport photo generation (preserved from original) ---

def build_passport_photo(img: Image.Image, bg_rgb, pw_mm, ph_mm):
    note = None
    if bg_rgb is not None:
        img, note = replace_background(img, bg_rgb)
    img = crop_to_ratio(img, pw_mm / ph_mm)
    target = (mm_to_px(pw_mm), mm_to_px(ph_mm))
    if img.size != target:
        img = img.resize(target, Image.LANCZOS)
    return img, note


def build_sheet(photo: Image.Image, page_w_mm, page_h_mm,
                pw_mm, ph_mm, count) -> Image.Image:
    grid = compute_grid(page_w_mm, page_h_mm, pw_mm, ph_mm)
    if grid is None:
        raise ValueError("Selected photo size does not fit on the selected page.")
    cols, _rows = grid
    count = max(1, min(count, cols * _rows))
    W, H = mm_to_px(page_w_mm), mm_to_px(page_h_mm)
    pw, ph = photo.size
    sp = mm_to_px(SPACING_MM)
    margin = mm_to_px(MARGIN_MM)
    border = max(2, mm_to_px(BORDER_MM))
    sheet = Image.new("RGB", (W, H), (255, 255, 255))
    draw = ImageDraw.Draw(sheet)
    for i in range(count):
        row, col = divmod(i, cols)
        x = margin + col * (pw + sp)
        y = margin + row * (ph + sp)
        sheet.paste(photo, (x, y))
        draw.rectangle([x, y, x + pw - 1, y + ph - 1],
                       outline=BORDER_RGB, width=border)
    return sheet


def generate_files(image_bytes: bytes, page_w_mm: float, page_h_mm: float,
                   bg_rgb, pw_mm: float, ph_mm: float, qty: int, fmt: str):
    img = load_image(image_bytes)
    grid = compute_grid(page_w_mm, page_h_mm, pw_mm, ph_mm)
    if grid is None:
        raise ValueError(
            "Selected photo size does not fit on the selected page. "
            "Please choose a smaller photo size or a bigger page.")
    cols, rows = grid
    capacity = cols * rows
    pages = math.ceil(qty / capacity)
    passport, note = build_passport_photo(img, bg_rgb, pw_mm, ph_mm)
    sheets = []
    remaining = qty
    for _ in range(pages):
        take = min(capacity, remaining)
        sheets.append(build_sheet(passport, page_w_mm, page_h_mm, pw_mm, ph_mm, take))
        remaining -= take
    stamp = time.strftime("%Y%m%d-%H%M%S")
    uid = uuid.uuid4().hex[:6]
    base = f"passport_photos_{stamp}_{uid}"
    files = []

    def to_jpeg(sheet, name):
        buf = io.BytesIO()
        sheet.save(buf, "JPEG", quality=JPEG_QUALITY, subsampling=0,
                   dpi=(DPI, DPI), optimize=True)
        files.append((name, buf.getvalue()))

    def to_png(sheet, name):
        buf = io.BytesIO()
        sheet.save(buf, "PNG", dpi=(DPI, DPI))
        files.append((name, buf.getvalue()))

    def to_pdf():
        buf = io.BytesIO()
        first, rest = sheets[0], sheets[1:]
        first.save(buf, "PDF", resolution=float(DPI), save_all=True,
                   append_images=rest)
        files.append((f"{base}.pdf", buf.getvalue()))

    if fmt in ("pdf", "pdf_jpg", "pdf_png"):
        to_pdf()
    if fmt in ("jpg", "pdf_jpg"):
        for i, s in enumerate(sheets, 1):
            to_jpeg(s, f"{base}_p{i}.jpg")
    if fmt in ("png", "pdf_png"):
        for i, s in enumerate(sheets, 1):
            to_png(s, f"{base}_p{i}.png")
    return files, pages, note


# --------------------------------------------------------------------------- #
# Telegram Bot (preserved passport-photo flow)
# --------------------------------------------------------------------------- #

class Flow(StatesGroup):
    page_custom_w = State()
    page_custom_h = State()
    page_custom_u = State()
    bg_custom_hex = State()
    ps_custom_w = State()
    ps_custom_h = State()
    ps_custom_u = State()
    qty_custom = State()


def _rows(*btns_per_row):
    return [[InlineKeyboardButton(text=t, callback_data=c) for t, c in row]
            for row in btns_per_row if row]


def kb_page():
    rows = _rows([("A4", "pg:A4"), ("A3", "pg:A3"), ("A5", "pg:A5")],
                 [("Letter", "pg:Letter"), ("Legal", "pg:Legal")],
                 [("📐 Custom Size", "pg:custom")])
    rows.append([InlineKeyboardButton(text="❌ Cancel", callback_data="flow:cancel")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def kb_unit(prefix, back_cb):
    rows = _rows([("mm", f"{prefix}:mm"), ("cm", f"{prefix}:cm"),
                  ("inch", f"{prefix}:inch")])
    rows.append([InlineKeyboardButton(text="⬅️ Back", callback_data=back_cb)])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def kb_bg():
    rows = _rows([("🔵 Blue", "bg:blue"), ("🔴 Red", "bg:red")],
                 [("⚪ White", "bg:white"), ("🟢 Green", "bg:green")],
                 [("🟣 Custom (HEX)", "bg:custom"), ("⏭ Skip", "bg:skip")])
    rows.append([InlineKeyboardButton(text="⬅️ Back", callback_data="nav:page")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def kb_photo_size():
    rows = _rows([("25 × 35 mm", "ps:25x35"), ("30 × 40 mm", "ps:30x40")],
                 [("35 × 45 mm", "ps:35x45"), ("2 × 2 inch", "ps:2x2")],
                 [("📐 Custom", "ps:custom")])
    rows.append([InlineKeyboardButton(text="⬅️ Back", callback_data="nav:bg")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def kb_qty():
    rows = _rows([("1", "qt:1"), ("2", "qt:2"), ("3", "qt:3"), ("4", "qt:4")],
                 [("6", "qt:6"), ("8", "qt:8"), ("10", "qt:10"), ("12", "qt:12")],
                 [("🔢 Custom", "qt:custom")])
    rows.append([InlineKeyboardButton(text="⬅️ Back", callback_data="nav:ps")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def kb_fmt():
    rows = _rows([("📄 PDF", "fm:pdf")],
                 [("🖼 JPEG", "fm:jpg"), ("🖼 PNG", "fm:png")],
                 [("📄 PDF + JPEG", "fm:pdf_jpg"),
                  ("📄 PDF + PNG", "fm:pdf_png")])
    rows.append([InlineKeyboardButton(text="⬅️ Back", callback_data="nav:qty")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def kb_summary():
    return InlineKeyboardMarkup(inline_keyboard=_rows(
        [("✅ Generate", "sum:generate")],
        [("✏️ Change Settings", "sum:change"), ("❌ Cancel", "flow:cancel")],
    ))


def kb_change():
    rows = _rows(
        [("📄 Page Size", "chg:page"), ("🎨 Background", "chg:bg")],
        [("📐 Photo Size", "chg:ps"), ("🖼 Quantity", "chg:qty")],
        [("📦 Output Format", "chg:fmt")])
    rows.append([InlineKeyboardButton(text="⬅️ Back to Summary",
                                      callback_data="nav:summary")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def kb_fit_error():
    rows = _rows(
        [("📐 Change Photo Size", "chg:ps"), ("📄 Change Page", "chg:page")],
        [("🖼 Change Quantity", "chg:qty")],
        [("❌ Cancel", "flow:cancel")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def kb_main_menu():
    rows = [[InlineKeyboardButton(text="📸 Create Passport Photos",
                                  callback_data="menu:create")]]
    if WEBAPP_URL:
        rows.append([InlineKeyboardButton(
            text="📱 Open Photo Maker",
            web_app=WebAppInfo(url=WEBAPP_URL))])
    return InlineKeyboardMarkup(inline_keyboard=rows)


router = Router()

WELCOME = (
    "👋 <b>Passport Photo Maker</b>\n\n"
    "Send me any photo and I'll turn it into a professional, print-ready "
    "passport photo sheet (PDF / JPEG / PNG, 300 DPI).\n\n"
    "Use the menu below to begin."
)

HELP_TEXT = (
    "ℹ️ <b>How to use</b>\n\n"
    "1️⃣ Tap <b>📸 Create Passport Photos</b> or simply send a photo.\n"
    "2️⃣ Choose the <b>page size</b> (A4/A3/A5/Letter/Legal/Custom).\n"
    "3️⃣ Optionally <b>change the background</b> (Blue/Red/White/Green/HEX/Skip).\n"
    "4️⃣ Select the <b>passport photo size</b> (e.g. 35 × 45 mm).\n"
    "5️⃣ Choose <b>how many photos</b> you need.\n"
    "6️⃣ Pick the <b>output format</b> (PDF/JPEG/PNG) and press <b>Generate</b>.\n\n"
    "🖨 Output is print-ready at <b>300 DPI</b> with exact physical sizes.\n"
    "Commands: /start • /help • /cancel"
)

PAGE_PROMPT = "📄 <b>SELECT PAGE SIZE</b>"
BG_PROMPT = "🎨 <b>CHANGE BACKGROUND?</b>"
PS_PROMPT = "📐 <b>SELECT PASSPORT PHOTO SIZE</b>"
QTY_PROMPT = "🖼 <b>HOW MANY PHOTOS?</b>"
FMT_PROMPT = "📦 <b>SELECT OUTPUT FORMAT</b>"


async def safe_edit(cq: CallbackQuery, text: str, kb=None):
    try:
        await cq.message.edit_text(text, reply_markup=kb)
    except TelegramAPIError:
        try:
            await cq.message.answer(text, reply_markup=kb)
        except TelegramAPIError:
            pass


async def get_data_photo_path(state: FSMContext):
    data = await state.get_data()
    p = data.get("img_path")
    if not p:
        return None, data
    path = Path(p)
    try:
        path.resolve().relative_to(TMP_ROOT.resolve())
    except ValueError:
        return None, data
    if not path.is_file():
        return None, data
    return path, data


async def summary_text(state: FSMContext) -> str:
    data = await state.get_data()
    page_name = data.get("page_name", "Custom")
    pw, ph = data.get("page_w", 0), data.get("page_h", 0)
    psw, psh = data.get("ps_w", 0), data.get("ps_h", 0)
    qty = data.get("qty", 0)
    fmt = data.get("fmt", "pdf")
    bg_name = data.get("bg_name", "Skip (original)")
    fmt_names = {"pdf": "PDF", "jpg": "JPEG", "png": "PNG",
                 "pdf_jpg": "PDF + JPEG", "pdf_png": "PDF + PNG"}
    lines = [
        "✅ <b>PHOTO READY</b>\n",
        f"📄 Page: {page_name} ({pw:g} × {ph:g} mm)",
        f"📐 Photo Size: {psw:g} × {psh:g} mm",
        f"🖼 Quantity: {qty}",
        f"🎨 Background: {bg_name}",
        f"📦 Format: {fmt_names.get(fmt, fmt)}",
        f"🖨 Quality: {DPI} DPI",
    ]
    grid = compute_grid(pw, ph, psw, psh)
    if grid is None:
        lines.append("\n⚠️ <b>This photo size does not fit on the selected "
                     "page.</b> Use ✏️ Change Settings to pick a smaller "
                     "photo size or a bigger page.")
    else:
        cols, rows = grid
        capacity = cols * rows
        if qty > capacity:
            pages = math.ceil(qty / capacity)
            lines.append(f"\n🗒 Layout: {cols} × {rows} per page → "
                         f"<b>{pages} pages</b> will be generated.")
        else:
            lines.append(f"\n🗒 Layout: {cols} × {rows} grid on 1 page.")
    return "\n".join(lines)


async def show_summary(cq_or_msg, state: FSMContext):
    text = await summary_text(state)
    kb = kb_summary()
    if isinstance(cq_or_msg, CallbackQuery):
        await safe_edit(cq_or_msg, text, kb)
    else:
        await cq_or_msg.answer(text, reply_markup=kb)


async def after_setting_selected(cq_or_msg, state: FSMContext, next_step: str):
    data = await state.get_data()
    editing = data.get("editing", False)
    if editing:
        await state.update_data(editing=False)
        await show_summary(cq_or_msg, state)
        return
    prompts = {"bg": (BG_PROMPT, kb_bg()), "ps": (PS_PROMPT, kb_photo_size()),
               "qty": (QTY_PROMPT, kb_qty()), "fmt": (FMT_PROMPT, kb_fmt())}
    text, kb = prompts[next_step]
    if isinstance(cq_or_msg, CallbackQuery):
        await safe_edit(cq_or_msg, text, kb)
    else:
        await cq_or_msg.answer(text, reply_markup=kb)


@router.message(CommandStart())
async def cmd_start(message: Message, state: FSMContext):
    await state.clear()
    await message.answer(WELCOME, reply_markup=kb_main_menu())


@router.message(Command("help"))
async def cmd_help(message: Message):
    await message.answer(HELP_TEXT, reply_markup=kb_main_menu())


@router.message(Command("cancel"))
async def cmd_cancel(message: Message, state: FSMContext):
    await state.clear()
    cleanup_dir(user_dir(message.from_user.id))
    await message.answer("❌ Cancelled. Temporary files removed.",
                         reply_markup=kb_main_menu())


@router.callback_query(F.data == "menu:create")
async def cb_menu_create(cq: CallbackQuery, state: FSMContext):
    await state.clear()
    await safe_edit(cq, "📸 Send me your photo now — as a <b>photo</b> or as an "
                        "<b>image file/document</b>. I'll use the highest "
                        "available quality.")
    await cq.answer()


@router.callback_query(F.data == "flow:cancel")
async def cb_flow_cancel(cq: CallbackQuery, state: FSMContext):
    await state.clear()
    cleanup_dir(user_dir(cq.from_user.id))
    await safe_edit(cq, "❌ Cancelled. Temporary files removed.")
    await cq.message.answer(WELCOME, reply_markup=kb_main_menu())
    await cq.answer()


async def _intake(message: Message, state: FSMContext, file_id: str, fname: str):
    status = await message.answer("⏳ Downloading your photo…")
    try:
        tg_file = await message.bot.get_file(file_id)
        if tg_file.file_size and tg_file.file_size > MAX_IMAGE_BYTES:
            await status.edit_text("⚠️ Image is too large (max 25 MB). "
                                   "Please send a smaller file.")
            return
        buf = await message.bot.download_file(tg_file.file_path)
        data = buf.read()
        try:
            img = load_image(data)
            img.close()
        except Exception:
            await status.edit_text(
                "⚠️ This doesn't look like a valid image. Please send a "
                "clear JPEG/PNG photo.")
            return
        d = user_dir(message.from_user.id)
        path = d / f"orig_{uuid.uuid4().hex[:8]}.bin"
        path.write_bytes(data)
        await state.clear()
        await state.update_data(img_path=str(path), img_name=fname)
        await status.edit_text("✅ Photo received!")
        await message.answer(PAGE_PROMPT, reply_markup=kb_page())
    except TelegramAPIError:
        log.warning("telegram download failed", exc_info=True)
        await status.edit_text("⚠️ Couldn't download the file from Telegram. "
                               "Please try sending it again.")
    except Exception:
        log.exception("photo intake failed")
        await status.edit_text("⚠️ Something went wrong while reading your "
                               "photo. Please try again.")


@router.message(F.photo)
async def on_photo(message: Message, state: FSMContext):
    biggest = message.photo[-1]
    await _intake(message, state, biggest.file_id, "photo.jpg")


@router.message(F.document)
async def on_document(message: Message, state: FSMContext):
    doc = message.document
    mime = (doc.mime_type or "").lower()
    name = doc.file_name or "image"
    if not (mime in IMAGE_MIMES or mime.startswith("image/")):
        await message.answer("⚠️ Please send an <b>image</b> file "
                             "(JPEG/PNG/etc.).")
        return
    if doc.file_size and doc.file_size > MAX_IMAGE_BYTES:
        await message.answer("⚠️ Image is too large (max 25 MB).")
        return
    await _intake(message, state, doc.file_id, name)


@router.callback_query(F.data.startswith("nav:"))
async def cb_nav(cq: CallbackQuery, state: FSMContext):
    target = cq.data.split(":", 1)[1]
    prompts = {"page": (PAGE_PROMPT, kb_page()), "bg": (BG_PROMPT, kb_bg()),
               "ps": (PS_PROMPT, kb_photo_size()), "qty": (QTY_PROMPT, kb_qty()),
               "fmt": (FMT_PROMPT, kb_fmt())}
    if target == "summary":
        await show_summary(cq, state)
    elif target in prompts:
        text, kb = prompts[target]
        await safe_edit(cq, text, kb)
    await cq.answer()


@router.callback_query(F.data.startswith("chg:"))
async def cb_change(cq: CallbackQuery, state: FSMContext):
    await state.update_data(editing=True)
    await cb_nav(cq, state)


@router.callback_query(F.data == "sum:change")
async def cb_sum_change(cq: CallbackQuery, state: FSMContext):
    await safe_edit(cq, "✏️ <b>Which setting do you want to change?</b>",
                    kb_change())
    await cq.answer()


async def _need_photo(cq: CallbackQuery, state: FSMContext) -> bool:
    path, _ = await get_data_photo_path(state)
    if path is None:
        await safe_edit(cq, "⌛ Your session expired. Please send the photo "
                            "again to start over.", kb_main_menu())
        await cq.answer()
        return True
    return False


@router.callback_query(F.data.startswith("pg:"))
async def cb_page(cq: CallbackQuery, state: FSMContext):
    if await _need_photo(cq, state):
        return
    val = cq.data.split(":", 1)[1]
    if val == "custom":
        await state.set_state(Flow.page_custom_w)
        await safe_edit(cq, "📐 Enter the page <b>width</b> (a number, e.g. "
                            "<code>210</code>). You'll choose the unit next.")
    else:
        w, h = PAGE_SIZES[val]
        await state.update_data(page_w=w, page_h=h, page_name=val)
        await after_setting_selected(cq, state, "bg")
    await cq.answer()


@router.message(Flow.page_custom_w)
async def msg_page_w(message: Message, state: FSMContext):
    v = parse_float(message.text or "")
    if v is None or v <= 0:
        await message.answer("⚠️ Please enter a valid positive number for the "
                             "page width (e.g. <code>210</code>).")
        return
    await state.update_data(tmp_page_w=v)
    await state.set_state(Flow.page_custom_h)
    await message.answer("📐 Now enter the page <b>height</b> (e.g. "
                         "<code>297</code>).")


@router.message(Flow.page_custom_h)
async def msg_page_h(message: Message, state: FSMContext):
    v = parse_float(message.text or "")
    if v is None or v <= 0:
        await message.answer("⚠️ Please enter a valid positive number for the "
                             "page height (e.g. <code>297</code>).")
        return
    await state.update_data(tmp_page_h=v)
    await state.set_state(Flow.page_custom_u)
    await message.answer("📏 Select the <b>unit</b>:",
                         reply_markup=kb_unit("pgu", "nav:page"))


@router.callback_query(F.data.startswith("pgu:"))
async def cb_page_unit(cq: CallbackQuery, state: FSMContext):
    unit = cq.data.split(":", 1)[1]
    data = await state.get_data()
    w_mm = unit_to_mm(data.get("tmp_page_w", 0), unit)
    h_mm = unit_to_mm(data.get("tmp_page_h", 0), unit)
    if not (MM_MIN_PAGE <= w_mm <= MM_MAX_PAGE and
            MM_MIN_PAGE <= h_mm <= MM_MAX_PAGE):
        await safe_edit(cq, "⚠️ Those dimensions look unreasonable "
                            f"({w_mm:g} × {h_mm:g} mm). Page sides must be "
                            f"between {MM_MIN_PAGE:g} and {MM_MAX_PAGE:g} mm. "
                            "Please try again.", kb_page())
        await state.set_state(None)
        await cq.answer()
        return
    await state.update_data(page_w=w_mm, page_h=h_mm,
                            page_name=f"Custom {w_mm:g}×{h_mm:g} mm")
    await state.set_state(None)
    await after_setting_selected(cq, state, "bg")
    await cq.answer()


@router.callback_query(F.data.startswith("bg:"))
async def cb_bg(cq: CallbackQuery, state: FSMContext):
    if await _need_photo(cq, state):
        return
    val = cq.data.split(":", 1)[1]
    if val == "custom":
        await state.set_state(Flow.bg_custom_hex)
        await safe_edit(cq, "🟣 Send the background color as a <b>HEX code</b>, "
                            "e.g. <code>#FFFFFF</code>.")
    elif val == "skip":
        await state.update_data(bg=None, bg_name="Skip (original)")
        await after_setting_selected(cq, state, "ps")
    else:
        name, rgb = BG_PRESETS[val]
        await state.update_data(bg=rgb_to_hex(rgb), bg_name=name)
        await after_setting_selected(cq, state, "ps")
    await cq.answer()


@router.message(Flow.bg_custom_hex)
async def msg_bg_hex(message: Message, state: FSMContext):
    rgb = parse_hex_color(message.text or "")
    if rgb is None:
        await message.answer("⚠️ Invalid HEX color. Send it like "
                             "<code>#FFFFFF</code> (6 hex digits).")
        return
    await state.update_data(bg=rgb_to_hex(rgb), bg_name=f"Custom {rgb_to_hex(rgb)}")
    await state.set_state(None)
    await after_setting_selected(message, state, "ps")


_PS_CB = {"25x35": "25 × 35 mm", "30x40": "30 × 40 mm",
          "35x45": "35 × 45 mm", "2x2": "2 × 2 inch"}


@router.callback_query(F.data.startswith("ps:"))
async def cb_ps(cq: CallbackQuery, state: FSMContext):
    if await _need_photo(cq, state):
        return
    val = cq.data.split(":", 1)[1]
    if val == "custom":
        await state.set_state(Flow.ps_custom_w)
        await safe_edit(cq, "📐 Enter the photo <b>width</b> (a number, e.g. "
                            "<code>35</code>).")
    else:
        name = _PS_CB[val]
        w, h = PHOTO_SIZES[name]
        await state.update_data(ps_w=w, ps_h=h, ps_name=name)
        await after_setting_selected(cq, state, "qty")
    await cq.answer()


@router.message(Flow.ps_custom_w)
async def msg_ps_w(message: Message, state: FSMContext):
    v = parse_float(message.text or "")
    if v is None or v <= 0:
        await message.answer("⚠️ Please enter a valid positive number for the "
                             "photo width (e.g. <code>35</code>).")
        return
    await state.update_data(tmp_ps_w=v)
    await state.set_state(Flow.ps_custom_h)
    await message.answer("📐 Now enter the photo <b>height</b> (e.g. "
                         "<code>45</code>).")


@router.message(Flow.ps_custom_h)
async def msg_ps_h(message: Message, state: FSMContext):
    v = parse_float(message.text or "")
    if v is None or v <= 0:
        await message.answer("⚠️ Please enter a valid positive number for the "
                             "photo height (e.g. <code>45</code>).")
        return
    await state.update_data(tmp_ps_h=v)
    await state.set_state(Flow.ps_custom_u)
    await message.answer("📏 Select the <b>unit</b>:",
                         reply_markup=kb_unit("psu", "nav:ps"))


@router.callback_query(F.data.startswith("psu:"))
async def cb_ps_unit(cq: CallbackQuery, state: FSMContext):
    unit = cq.data.split(":", 1)[1]
    data = await state.get_data()
    w_mm = unit_to_mm(data.get("tmp_ps_w", 0), unit)
    h_mm = unit_to_mm(data.get("tmp_ps_h", 0), unit)
    if not (MM_MIN_PHOTO <= w_mm <= MM_MAX_PHOTO and
            MM_MIN_PHOTO <= h_mm <= MM_MAX_PHOTO):
        await safe_edit(cq, "⚠️ Those photo dimensions look unreasonable. "
                            "Please try again.", kb_photo_size())
        await state.set_state(None)
        await cq.answer()
        return
    await state.update_data(ps_w=w_mm, ps_h=h_mm,
                            ps_name=f"{w_mm:g} × {h_mm:g} mm")
    await state.set_state(None)
    await after_setting_selected(cq, state, "qty")
    await cq.answer()


@router.callback_query(F.data.startswith("qt:"))
async def cb_qty(cq: CallbackQuery, state: FSMContext):
    if await _need_photo(cq, state):
        return
    val = cq.data.split(":", 1)[1]
    if val == "custom":
        await state.set_state(Flow.qty_custom)
        await safe_edit(cq, f"🔢 Enter how many photos you need (1–{MAX_QTY}).")
    else:
        try:
            qty = int(val)
        except ValueError:
            await cq.answer("Invalid quantity.")
            return
        if not (1 <= qty <= MAX_QTY):
            await cq.answer("Invalid quantity.")
            return
        await state.update_data(qty=qty)
        await after_setting_selected(cq, state, "fmt")
    await cq.answer()


@router.message(Flow.qty_custom)
async def msg_qty(message: Message, state: FSMContext):
    text = (message.text or "").strip()
    if not text.isdigit():
        await message.answer(f"⚠️ Please enter a whole number between 1 and "
                             f"{MAX_QTY} (e.g. <code>5</code>).")
        return
    qty = int(text)
    if not (1 <= qty <= MAX_QTY):
        await message.answer(f"⚠️ Quantity must be between 1 and {MAX_QTY}. "
                             "Try again.")
        return
    await state.update_data(qty=qty)
    await state.set_state(None)
    await after_setting_selected(message, state, "fmt")


@router.callback_query(F.data.startswith("fm:"))
async def cb_fmt(cq: CallbackQuery, state: FSMContext):
    if await _need_photo(cq, state):
        return
    val = cq.data.split(":", 1)[1]
    if val not in ("pdf", "jpg", "png", "pdf_jpg", "pdf_png"):
        await cq.answer("Invalid format.")
        return
    await state.update_data(fmt=val)
    await show_summary(cq, state)
    await cq.answer()


@router.callback_query(F.data == "sum:generate")
async def cb_generate(cq: CallbackQuery, state: FSMContext):
    path, data = await get_data_photo_path(state)
    if path is None:
        await safe_edit(cq, "⌛ Your session expired or the photo was cleaned "
                            "up. Please send it again to start over.",
                        kb_main_menu())
        await cq.answer()
        return
    required = ("page_w", "page_h", "ps_w", "ps_h", "qty", "fmt")
    if any(k not in data for k in required):
        await safe_edit(cq, "⚠️ Some settings are missing. Let's go through "
                            "them again.", kb_page())
        await cq.answer()
        return
    page_w, page_h = data["page_w"], data["page_h"]
    ps_w, ps_h = data["ps_w"], data["ps_h"]
    qty, fmt = data["qty"], data["fmt"]
    bg_hex = data.get("bg")
    bg_rgb = parse_hex_color(bg_hex) if bg_hex else None
    grid = compute_grid(page_w, page_h, ps_w, ps_h)
    if grid is None:
        await safe_edit(cq,
            "⚠️ <b>Selected photo size does not fit on the selected page.</b>\n"
            "I won't shrink photos — your print size would be wrong. "
            "Please adjust one of these:", kb_fit_error())
        await cq.answer()
        return
    await safe_edit(cq, "⏳ <b>Processing your photo…</b>\nThis can take a "
                        "moment, especially with background removal.")
    await cq.answer()
    note = None
    try:
        image_bytes = path.read_bytes()
        loop = asyncio.get_running_loop()
        files, pages, note = await asyncio.wait_for(
            loop.run_in_executor(
                None, generate_files, image_bytes, page_w, page_h,
                bg_rgb, ps_w, ps_h, qty, fmt),
            timeout=GENERATION_TIMEOUT)
    except asyncio.TimeoutError:
        log.error("generation timed out")
        await cq.message.answer(
            "⚠️ Processing took too long. Please try again, or choose "
            "<b>Skip</b> for the background.", reply_markup=kb_summary())
        return
    except ValueError as exc:
        await cq.message.answer(f"⚠️ {exc}", reply_markup=kb_summary())
        return
    except BaseException as exc:
        if isinstance(exc, asyncio.CancelledError):
            raise
        log.exception("generation failed")
        await cq.message.answer("⚠️ Sorry, something went wrong while "
                                "generating your files. Please try again.",
                                reply_markup=kb_summary())
        return
    try:
        caption = (f"🖨 Done! {qty} photo(s), {pages} page(s), "
                   f"{ps_w:g} × {ps_h:g} mm @ {DPI} DPI.")
        if note:
            await cq.message.answer(note)
        for fname, blob in files:
            await cq.message.answer_document(
                BufferedInputFile(blob, filename=fname), caption=caption)
        await cq.message.answer("✅ All files sent! Send another photo "
                                "anytime to make a new sheet.",
                                reply_markup=kb_main_menu())
    except TelegramAPIError:
        log.warning("failed to send output files", exc_info=True)
        await cq.message.answer("⚠️ Files were generated but couldn't be "
                                "sent (they may be too large for Telegram). "
                                "Try fewer pages or a different format.")
    finally:
        await state.clear()
        cleanup_dir(user_dir(cq.from_user.id))


@router.message()
async def fallback_message(message: Message):
    await message.answer("Send me a <b>photo</b> to create a passport photo "
                         "sheet, or use /start.", reply_markup=kb_main_menu())


@router.callback_query()
async def fallback_callback(cq: CallbackQuery):
    await cq.answer("That action is no longer available. Send a photo or use "
                    "/start to begin again.", show_alert=False)


# --------------------------------------------------------------------------- #
# Premium Web UI (embedded HTML/CSS/JS)
# --------------------------------------------------------------------------- #

APP_HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=5">
<meta name="theme-color" content="#e11d2a">
<title>Photo Studio Pro — Premium Photo Editor</title>
<style>
/* ===== Design System ===== */
:root{
  --red:#e11d2a;--red-d:#b31520;--red-l:#ff3b4a;--red-50:#fff1f2;--red-100:#ffe1e3;
  --bg:#0e0f13;--bg-2:#16181f;--card:#1c1f29;--card-2:#232734;--card-hi:#2a2f3d;
  --line:#2d3242;--line-2:#3a4053;
  --txt:#f4f6fb;--txt-2:#c7ccd9;--mut:#8a92a6;--mut-2:#6b7286;
  --ok:#34d399;--ok-bg:rgba(52,211,153,.12);--warn:#fbbf24;--err:#f87171;
  --blue:#5b8def;--shadow:0 8px 30px rgba(0,0,0,.4);
  --radius:14px;--radius-sm:10px;--radius-lg:20px;
  --red-grad:linear-gradient(135deg,#ff2d3d 0%,#e11d2a 50%,#b31520 100%);
  --red-soft:linear-gradient(135deg,#fff1f2 0%,#ffe1e3 100%);
}
*{box-sizing:border-box;margin:0;padding:0}
html,body{height:100%}
body{font-family:'Inter',system-ui,-apple-system,'Segoe UI',Roboto,sans-serif;background:var(--bg);color:var(--txt);-webkit-font-smoothing:antialiased;overflow-x:hidden}
a{color:var(--red-l);text-decoration:none}
button{font-family:inherit;cursor:pointer;border:none;outline:none}
input,select,textarea{font-family:inherit;outline:none}
::-webkit-scrollbar{width:10px;height:10px}
::-webkit-scrollbar-track{background:var(--bg)}
::-webkit-scrollbar-thumb{background:var(--line);border-radius:6px}
::-webkit-scrollbar-thumb:hover{background:var(--line-2)}

/* ===== Auth ===== */
.auth-wrap{min-height:100vh;display:grid;grid-template-columns:1fr 1fr;background:var(--bg)}
.auth-hero{position:relative;overflow:hidden;background:var(--red-grad);display:flex;align-items:center;justify-content:center;padding:48px}
.auth-hero::before{content:"";position:absolute;inset:0;background:radial-gradient(circle at 30% 20%,rgba(255,255,255,.15),transparent 50%),radial-gradient(circle at 70% 80%,rgba(0,0,0,.2),transparent 50%)}
.auth-hero-content{position:relative;z-index:1;color:#fff;max-width:420px}
.auth-hero-content h1{font-size:42px;font-weight:800;line-height:1.1;margin-bottom:16px;letter-spacing:-.5px}
.auth-hero-content p{font-size:17px;opacity:.92;line-height:1.6;margin-bottom:32px}
.auth-feat{display:flex;flex-direction:column;gap:14px}
.auth-feat div{display:flex;align-items:center;gap:12px;font-size:15px;opacity:.95}
.auth-feat .ic{width:38px;height:38px;border-radius:10px;background:rgba(255,255,255,.18);display:flex;align-items:center;justify-content:center;font-size:18px;flex-shrink:0;backdrop-filter:blur(8px)}
.auth-panel{display:flex;align-items:center;justify-content:center;padding:32px}
.auth-card{width:100%;max-width:400px}
.auth-logo{display:flex;align-items:center;gap:12px;margin-bottom:32px}
.auth-logo .mark{width:48px;height:48px;border-radius:14px;background:var(--red-grad);display:flex;align-items:center;justify-content:center;font-size:24px;box-shadow:0 6px 20px rgba(225,29,42,.4)}
.auth-logo .txt{font-size:22px;font-weight:800;letter-spacing:-.3px}
.auth-logo .txt span{color:var(--red-l)}
.auth-card h2{font-size:26px;font-weight:700;margin-bottom:6px}
.auth-card .sub{color:var(--mut);font-size:15px;margin-bottom:28px}
.field{margin-bottom:18px}
.field label{display:block;font-size:13px;font-weight:600;color:var(--txt-2);margin-bottom:7px}
.field input{width:100%;padding:14px 16px;border-radius:var(--radius-sm);border:1.5px solid var(--line);background:var(--bg-2);color:var(--txt);font-size:15px;transition:.15s}
.field input:focus{border-color:var(--red);box-shadow:0 0 0 3px rgba(225,29,42,.15)}
.field input::placeholder{color:var(--mut-2)}
.field .pw-wrap{position:relative}
.field .pw-toggle{position:absolute;right:14px;top:50%;transform:translateY(-50%);background:none;color:var(--mut);font-size:18px;padding:4px}
.btn-red{width:100%;padding:15px;border-radius:var(--radius-sm);background:var(--red-grad);color:#fff;font-size:16px;font-weight:700;transition:.15s;box-shadow:0 6px 18px rgba(225,29,42,.35)}
.btn-red:hover{transform:translateY(-1px);box-shadow:0 8px 24px rgba(225,29,42,.45)}
.btn-red:active{transform:translateY(0)}
.btn-red:disabled{opacity:.6;cursor:not-allowed;transform:none}
.auth-switch{text-align:center;margin-top:22px;font-size:14px;color:var(--mut)}
.auth-switch a{font-weight:600}
.auth-err{background:rgba(248,113,113,.1);border:1px solid rgba(248,113,113,.3);color:var(--err);padding:12px 14px;border-radius:var(--radius-sm);font-size:14px;margin-bottom:18px;display:none}
.auth-err.show{display:block}
.auth-ok{background:var(--ok-bg);border:1px solid rgba(52,211,153,.3);color:var(--ok);padding:12px 14px;border-radius:var(--radius-sm);font-size:14px;margin-bottom:18px;display:none}
.auth-ok.show{display:block}
.divider{display:flex;align-items:center;gap:12px;margin:22px 0;color:var(--mut-2);font-size:13px}
.divider::before,.divider::after{content:"";flex:1;height:1px;background:var(--line)}

/* ===== App Shell ===== */
.app{display:flex;min-height:100vh}
.sidebar{width:248px;background:var(--bg-2);border-right:1px solid var(--line);display:flex;flex-direction:column;position:fixed;top:0;left:0;bottom:0;z-index:50;transition:transform .25s}
.sidebar-brand{padding:22px 20px;display:flex;align-items:center;gap:11px;border-bottom:1px solid var(--line)}
.sidebar-brand .mark{width:40px;height:40px;border-radius:11px;background:var(--red-grad);display:flex;align-items:center;justify-content:center;font-size:20px;box-shadow:0 4px 14px rgba(225,29,42,.4)}
.sidebar-brand .name{font-size:18px;font-weight:800;letter-spacing:-.2px}
.sidebar-brand .name span{color:var(--red-l)}
.nav{flex:1;padding:14px 12px;overflow-y:auto}
.nav-section{font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:.8px;color:var(--mut-2);padding:18px 12px 8px}
.nav-item{display:flex;align-items:center;gap:12px;padding:11px 14px;border-radius:var(--radius-sm);color:var(--txt-2);font-size:14.5px;font-weight:500;cursor:pointer;transition:.12s;margin-bottom:2px}
.nav-item:hover{background:var(--card);color:var(--txt)}
.nav-item.active{background:rgba(225,29,42,.14);color:var(--red-l);font-weight:600}
.nav-item .ic{width:22px;text-align:center;font-size:17px}
.nav-badge{margin-left:auto;background:var(--red);color:#fff;font-size:11px;font-weight:700;padding:2px 7px;border-radius:8px}
.sidebar-foot{padding:14px;border-top:1px solid var(--line)}
.user-chip{display:flex;align-items:center;gap:10px;padding:10px 12px;border-radius:var(--radius-sm);cursor:pointer;transition:.12s}
.user-chip:hover{background:var(--card)}
.user-avatar{width:36px;height:36px;border-radius:10px;background:var(--red-grad);display:flex;align-items:center;justify-content:center;font-size:15px;font-weight:700;color:#fff;flex-shrink:0}
.user-info{flex:1;min-width:0}
.user-info .nm{font-size:14px;font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.user-info .em{font-size:12px;color:var(--mut);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.user-menu{position:absolute;bottom:70px;left:14px;right:14px;background:var(--card);border:1px solid var(--line);border-radius:var(--radius-sm);box-shadow:var(--shadow);padding:6px;display:none;z-index:60}
.user-menu.show{display:block}
.user-menu button{display:flex;align-items:center;gap:10px;width:100%;padding:10px 12px;border-radius:8px;background:none;color:var(--txt-2);font-size:14px;text-align:left}
.user-menu button:hover{background:var(--card-2);color:var(--txt)}

.main{flex:1;margin-left:248px;min-width:0;display:flex;flex-direction:column;min-height:100vh}
.topbar{height:64px;background:var(--bg-2);border-bottom:1px solid var(--line);display:flex;align-items:center;padding:0 24px;gap:16px;position:sticky;top:0;z-index:40;backdrop-filter:blur(10px)}
.topbar .menu-btn{display:none;background:none;color:var(--txt);font-size:22px;padding:6px}
.topbar h1{font-size:20px;font-weight:700;flex:1}
.topbar .tb-actions{display:flex;align-items:center;gap:12px}
.tb-pill{display:flex;align-items:center;gap:7px;padding:7px 13px;border-radius:20px;background:var(--card);font-size:13px;color:var(--txt-2);font-weight:500}
.tb-pill .dot{width:8px;height:8px;border-radius:50%;background:var(--ok)}
.tb-pill.warn .dot{background:var(--warn)}
.tb-pill.err .dot{background:var(--err)}
.content{flex:1;padding:28px 24px;max-width:1400px;width:100%}
.page{display:none;animation:fade .25s ease}
.page.on{display:block}
@keyframes fade{from{opacity:0;transform:translateY(8px)}to{opacity:1;transform:translateY(0)}}
@keyframes spin{to{transform:rotate(360deg)}}

/* ===== Cards / Grid ===== */
.card{background:var(--card);border:1px solid var(--line);border-radius:var(--radius);padding:20px}
.card-head{display:flex;align-items:center;justify-content:space-between;margin-bottom:16px}
.card-head h3{font-size:17px;font-weight:700}
.card-sub{color:var(--mut);font-size:13.5px;margin-top:-8px;margin-bottom:16px}
.stat-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(200px,1fr));gap:16px;margin-bottom:24px}
.stat{background:var(--card);border:1px solid var(--line);border-radius:var(--radius);padding:20px;position:relative;overflow:hidden}
.stat::before{content:"";position:absolute;top:0;left:0;right:0;height:3px;background:var(--red-grad)}
.stat .ic{width:44px;height:44px;border-radius:12px;background:rgba(225,29,42,.12);display:flex;align-items:center;justify-content:center;font-size:22px;margin-bottom:14px}
.stat .lbl{font-size:13px;color:var(--mut);font-weight:500;margin-bottom:4px}
.stat .val{font-size:30px;font-weight:800;letter-spacing:-.5px}
.stat .trend{font-size:12.5px;color:var(--ok);margin-top:6px;font-weight:600}
.tool-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(220px,1fr));gap:16px}
.tool-card{background:var(--card);border:1px solid var(--line);border-radius:var(--radius);padding:22px;cursor:pointer;transition:.18s;position:relative;overflow:hidden}
.tool-card:hover{border-color:var(--red);transform:translateY(-3px);box-shadow:0 10px 28px rgba(0,0,0,.3)}
.tool-card::after{content:"";position:absolute;bottom:0;left:0;right:0;height:0;background:var(--red-grad);transition:.18s}
.tool-card:hover::after{height:3px}
.tool-card .ic{width:52px;height:52px;border-radius:14px;background:rgba(225,29,42,.1);display:flex;align-items:center;justify-content:center;font-size:26px;margin-bottom:14px;transition:.18s}
.tool-card:hover .ic{background:var(--red-grad);box-shadow:0 6px 18px rgba(225,29,42,.4)}
.tool-card h4{font-size:16.5px;font-weight:700;margin-bottom:5px}
.tool-card p{font-size:13px;color:var(--mut);line-height:1.5}
.tool-card .lock{position:absolute;top:14px;right:14px;font-size:16px;color:var(--mut-2)}

/* ===== Buttons ===== */
.btn{padding:11px 20px;border-radius:var(--radius-sm);font-size:14.5px;font-weight:600;transition:.15s;display:inline-flex;align-items:center;gap:8px}
.btn-primary{background:var(--red-grad);color:#fff;box-shadow:0 4px 14px rgba(225,29,42,.3)}
.btn-primary:hover{transform:translateY(-1px);box-shadow:0 6px 20px rgba(225,29,42,.4)}
.btn-ghost{background:var(--card-2);color:var(--txt-2);border:1px solid var(--line)}
.btn-ghost:hover{background:var(--card-hi);color:var(--txt)}
.btn-sm{padding:8px 14px;font-size:13px}
.btn:disabled{opacity:.5;cursor:not-allowed;transform:none!important}

/* ===== Editor ===== */
.editor-wrap{display:grid;grid-template-columns:300px 1fr 280px;gap:16px;height:calc(100vh - 64px - 56px);min-height:560px}
.editor-side{background:var(--card);border:1px solid var(--line);border-radius:var(--radius);overflow-y:auto;max-height:100%}
.editor-side h4{font-size:14px;font-weight:700;padding:16px 16px 10px;color:var(--txt-2);position:sticky;top:0;background:var(--card);z-index:5;border-bottom:1px solid var(--line)}
.tool-tabs{display:flex;gap:2px;padding:8px;border-bottom:1px solid var(--line);position:sticky;top:0;background:var(--card);z-index:10;overflow-x:auto}
.tool-tab{flex:1;padding:10px 8px;border-radius:8px;background:none;color:var(--mut);font-size:13px;font-weight:600;white-space:nowrap;transition:.12s;text-align:center}
.tool-tab:hover{background:var(--card-2);color:var(--txt-2)}
.tool-tab.active{background:rgba(225,29,42,.15);color:var(--red-l)}
.tool-panel{padding:16px;display:none}
.tool-panel.on{display:block}
.ctrl{margin-bottom:18px}
.ctrl-lbl{display:flex;justify-content:space-between;align-items:center;font-size:13px;font-weight:600;color:var(--txt-2);margin-bottom:8px}
.ctrl-val{font-size:12px;color:var(--mut);background:var(--bg-2);padding:2px 8px;border-radius:6px}
.slider{width:100%;-webkit-appearance:none;appearance:none;height:6px;border-radius:4px;background:var(--line);outline:none}
.slider::-webkit-slider-thumb{-webkit-appearance:none;width:18px;height:18px;border-radius:50%;background:var(--red);cursor:pointer;box-shadow:0 2px 6px rgba(0,0,0,.4);border:2px solid #fff}
.slider::-moz-range-thumb{width:18px;height:18px;border-radius:50%;background:var(--red);cursor:pointer;border:2px solid #fff}
.ctrl-row{display:grid;grid-template-columns:1fr 1fr;gap:10px;margin-bottom:14px}
.ctrl-row .ctrl{margin-bottom:0}
.seg{display:flex;gap:4px;background:var(--bg-2);border-radius:10px;padding:4px;margin-bottom:14px}
.seg button{flex:1;padding:8px;border-radius:7px;background:none;color:var(--mut);font-size:13px;font-weight:600;transition:.12s}
.seg button.active{background:var(--card-hi);color:var(--red-l);box-shadow:0 1px 4px rgba(0,0,0,.2)}
.filter-grid{display:grid;grid-template-columns:1fr 1fr;gap:10px}
.filter-cell{cursor:pointer;border-radius:10px;overflow:hidden;border:2px solid transparent;transition:.15s;position:relative}
.filter-cell.active{border-color:var(--red)}
.filter-cell img{width:100%;aspect-ratio:1;object-fit:cover;display:block}
.filter-cell .fn{position:absolute;bottom:0;left:0;right:0;background:linear-gradient(transparent,rgba(0,0,0,.8));color:#fff;font-size:11px;font-weight:600;padding:14px 8px 6px;text-align:center;text-transform:capitalize}
.canvas-area{background:var(--card);border:1px solid var(--line);border-radius:var(--radius);display:flex;flex-direction:column;overflow:hidden}
.canvas-toolbar{display:flex;align-items:center;gap:8px;padding:12px 16px;border-bottom:1px solid var(--line);flex-wrap:wrap}
.canvas-stage{flex:1;display:flex;align-items:center;justify-content:center;background:repeating-conic-gradient(#1a1d26 0% 25%,#16181f 0% 50%) 50%/24px 24px;position:relative;overflow:hidden;min-height:300px}
#editorCanvas{max-width:100%;max-height:100%;border-radius:6px;box-shadow:0 4px 24px rgba(0,0,0,.5)}
.canvas-empty{position:absolute;text-align:center;color:var(--mut)}
.canvas-empty .big{font-size:56px;margin-bottom:12px;opacity:.4}
.canvas-empty p{font-size:15px;margin-bottom:6px}
.canvas-empty small{font-size:13px;color:var(--mut-2)}
.canvas-status{display:flex;align-items:center;justify-content:space-between;padding:10px 16px;border-top:1px solid var(--line);font-size:12.5px;color:var(--mut)}
.history-side{background:var(--card);border:1px solid var(--line);border-radius:var(--radius);overflow-y:auto;max-height:100%}
.history-item{display:flex;align-items:center;gap:10px;padding:10px 14px;border-bottom:1px solid var(--line);font-size:13px;cursor:pointer;transition:.12s}
.history-item:hover{background:var(--card-2)}
.history-item.current{background:rgba(225,29,42,.1);border-left:3px solid var(--red)}
.history-item .ic{font-size:16px;opacity:.7}
.export-opts{padding:16px}
.exp-fmt{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-bottom:14px}
.exp-fmt button{padding:10px;border-radius:8px;background:var(--bg-2);border:1.5px solid var(--line);color:var(--txt-2);font-size:13px;font-weight:600;transition:.12s}
.exp-fmt button.active{border-color:var(--red);background:rgba(225,29,42,.1);color:var(--red-l)}
.exp-q{margin-bottom:14px}
.dz{border:2px dashed var(--line-2);border-radius:14px;padding:40px 20px;text-align:center;color:var(--mut);cursor:pointer;transition:.15s}
.dz:hover,.dz.over{border-color:var(--red);background:rgba(225,29,42,.04);color:var(--red-l)}
.dz .big{font-size:48px;margin-bottom:12px;opacity:.5}
.dz p{font-size:15px;margin-bottom:4px}
.dz small{font-size:13px;color:var(--mut-2)}

/* ===== Tables ===== */
.tbl-wrap{overflow-x:auto;border-radius:var(--radius);border:1px solid var(--line)}
table.tbl{width:100%;border-collapse:collapse;background:var(--card);font-size:14px}
table.tbl th{background:var(--card-2);padding:13px 16px;text-align:left;font-size:12px;font-weight:700;text-transform:uppercase;letter-spacing:.5px;color:var(--mut);border-bottom:1px solid var(--line);white-space:nowrap}
table.tbl td{padding:13px 16px;border-bottom:1px solid var(--line);color:var(--txt-2)}
table.tbl tr:hover td{background:rgba(255,255,255,.02)}
table.tbl tr:last-child td{border-bottom:none}
.badge{display:inline-flex;align-items:center;gap:5px;padding:3px 10px;border-radius:20px;font-size:12px;font-weight:600}
.badge.ok{background:var(--ok-bg);color:var(--ok)}
.badge.bad{background:rgba(248,113,113,.12);color:var(--err)}
.badge.warn{background:rgba(251,191,36,.12);color:var(--warn)}
.badge.mut{background:var(--bg-2);color:var(--mut)}
.badge.admin{background:rgba(225,29,42,.12);color:var(--red-l)}
.row-act{display:flex;gap:6px}
.row-act button{padding:7px 10px;border-radius:7px;background:var(--card-2);color:var(--txt-2);font-size:12px;font-weight:600;border:1px solid var(--line);transition:.12s}
.row-act button:hover{background:var(--card-hi)}
.row-act button.danger:hover{background:rgba(248,113,113,.15);color:var(--err);border-color:rgba(248,113,113,.3)}
.row-act button.ok-btn:hover{background:rgba(52,211,153,.15);color:var(--ok);border-color:rgba(52,211,153,.3)}

/* ===== Toggle ===== */
.toggle{position:relative;width:42px;height:24px;display:inline-block}
.toggle input{display:none}
.toggle .track{position:absolute;inset:0;background:var(--line);border-radius:14px;transition:.2s}
.toggle .thumb{position:absolute;top:3px;left:3px;width:18px;height:18px;border-radius:50%;background:#fff;transition:.2s;box-shadow:0 1px 3px rgba(0,0,0,.3)}
.toggle input:checked+.track{background:var(--red)}
.toggle input:checked+.track+.thumb{transform:translateX(18px)}

/* ===== Forms ===== */
.form-row{display:grid;grid-template-columns:1fr 1fr;gap:16px;margin-bottom:16px}
.form-row.full{grid-template-columns:1fr}
.form-field label{display:block;font-size:13px;font-weight:600;color:var(--txt-2);margin-bottom:7px}
.form-field input,.form-field select,.form-field textarea{width:100%;padding:11px 14px;border-radius:var(--radius-sm);border:1.5px solid var(--line);background:var(--bg-2);color:var(--txt);font-size:14px;transition:.15s}
.form-field input:focus,.form-field select:focus,.form-field textarea:focus{border-color:var(--red);box-shadow:0 0 0 3px rgba(225,29,42,.12)}
.form-field textarea{resize:vertical;min-height:80px}

/* ===== Maintenance banner ===== */
.maint-banner{background:linear-gradient(90deg,rgba(251,191,36,.15),rgba(251,191,36,.05));border:1px solid rgba(251,191,36,.3);border-radius:var(--radius);padding:14px 18px;display:flex;align-items:center;gap:12px;margin-bottom:20px;color:var(--warn);font-size:14px;font-weight:600}

/* ===== Toast ===== */
#toast{position:fixed;bottom:24px;right:24px;z-index:200;display:flex;flex-direction:column;gap:10px}
.toast{background:var(--card);border:1px solid var(--line);border-left:4px solid var(--red);border-radius:var(--radius-sm);padding:14px 18px;min-width:280px;box-shadow:var(--shadow);display:flex;align-items:center;gap:12px;font-size:14px;animation:slideIn .25s ease;max-width:380px}
.toast.ok{border-left-color:var(--ok)}
.toast.err{border-left-color:var(--err)}
.toast.warn{border-left-color:var(--warn)}
.toast .ic{font-size:18px}
.toast .msg{flex:1}
.toast .x{color:var(--mut);background:none;font-size:16px;padding:2px}
@keyframes slideIn{from{opacity:0;transform:translateX(40px)}to{opacity:1;transform:translateX(0)}}

/* ===== Spinner ===== */
.spinner{width:22px;height:22px;border:2.5px solid var(--line);border-top-color:var(--red);border-radius:50%;animation:spin .7s linear infinite;display:inline-block;vertical-align:middle}
.overlay-spin{position:absolute;inset:0;background:rgba(14,15,19,.7);display:flex;align-items:center;justify-content:center;z-index:30;flex-direction:column;gap:14px;color:var(--txt-2);font-size:14px;backdrop-filter:blur(4px);border-radius:var(--radius)}

/* ===== Modal ===== */
.modal-bg{position:fixed;inset:0;background:rgba(0,0,0,.65);z-index:100;display:flex;align-items:center;justify-content:center;padding:20px;backdrop-filter:blur(4px);display:none}
.modal-bg.show{display:flex}
.modal{background:var(--card);border:1px solid var(--line);border-radius:var(--radius-lg);padding:28px;max-width:480px;width:100%;box-shadow:var(--shadow);animation:modalIn .2s ease}
@keyframes modalIn{from{opacity:0;transform:scale(.95)}to{opacity:1;transform:scale(1)}}
.modal h3{font-size:20px;font-weight:700;margin-bottom:6px}
.modal p{color:var(--mut);font-size:14px;margin-bottom:20px}
.modal .acts{display:flex;gap:10px;justify-content:flex-end;margin-top:20px}

/* ===== Empty state ===== */
.empty{text-align:center;padding:48px 20px;color:var(--mut)}
.empty .big{font-size:48px;opacity:.4;margin-bottom:14px}
.empty h4{font-size:17px;color:var(--txt-2);margin-bottom:6px}
.empty p{font-size:14px}

/* ===== Responsive ===== */
@media(max-width:1100px){.editor-wrap{grid-template-columns:260px 1fr 240px}}
@media(max-width:900px){
  .sidebar{transform:translateX(-100%)}
  .sidebar.open{transform:translateX(0)}
  .main{margin-left:0}
  .topbar .menu-btn{display:block}
  .auth-wrap{grid-template-columns:1fr}
  .auth-hero{display:none}
  .editor-wrap{grid-template-columns:1fr;grid-template-rows:auto 1fr auto;height:auto}
  .editor-side,.history-side{max-height:260px}
}
@media(max-width:600px){
  .content{padding:18px 14px}
  .topbar{padding:0 14px}
  .stat-grid{grid-template-columns:1fr}
  .form-row{grid-template-columns:1fr}
  .tb-pill .lbl{display:none}
}
.scrim{position:fixed;inset:0;background:rgba(0,0,0,.5);z-index:45;display:none}
.scrim.show{display:block}
</style>
</head>
<body>
<!-- AUTH VIEW -->
<div id="authView" class="auth-wrap">
  <div class="auth-hero">
    <div class="auth-hero-content">
      <h1>Photo Studio<br>Pro</h1>
      <p>A premium, professional photo editing studio in your browser. Crop, enhance, retouch, and export print-ready photos — all in one place.</p>
      <div class="auth-feat">
        <div><span class="ic">✨</span> Pro-grade adjustments &amp; filters</div>
        <div><span class="ic">🖨</span> Print-ready passport &amp; A4 layouts</div>
        <div><span class="ic">🔒</span> Private — auto-deletes your uploads</div>
      </div>
    </div>
  </div>
  <div class="auth-panel">
    <div class="auth-card">
      <div class="auth-logo">
        <div class="mark">📸</div>
        <div class="txt">Photo<span>Studio</span></div>
      </div>
      <div id="authForm">
        <h2 id="authTitle">Welcome back</h2>
        <p class="sub" id="authSub">Sign in to access your studio.</p>
        <div class="auth-err" id="authErr"></div>
        <div class="auth-ok" id="authOk"></div>
        <form id="loginForm">
          <div class="field">
            <label>Email</label>
            <input type="email" id="loginEmail" placeholder="you@example.com" required autocomplete="email">
          </div>
          <div class="field">
            <label>Password</label>
            <div class="pw-wrap">
              <input type="password" id="loginPw" placeholder="••••••••" required autocomplete="current-password">
              <button type="button" class="pw-toggle" onclick="togglePw('loginPw',this)">👁</button>
            </div>
          </div>
          <button type="submit" class="btn-red" id="loginBtn">Sign In →</button>
        </form>
        <form id="registerForm" style="display:none">
          <div class="field">
            <label>Display Name</label>
            <input type="text" id="regName" placeholder="Your name" autocomplete="name">
          </div>
          <div class="field">
            <label>Email</label>
            <input type="email" id="regEmail" placeholder="you@example.com" required autocomplete="email">
          </div>
          <div class="field">
            <label>Password</label>
            <div class="pw-wrap">
              <input type="password" id="regPw" placeholder="At least 8 characters" required minlength="8" autocomplete="new-password">
              <button type="button" class="pw-toggle" onclick="togglePw('regPw',this)">👁</button>
            </div>
          </div>
          <button type="submit" class="btn-red" id="regBtn">Create Account →</button>
        </form>
        <div class="auth-switch" id="authSwitch">
          Don't have an account? <a href="#" onclick="showRegister();return false">Create one</a>
        </div>
      </div>
    </div>
  </div>
</div>

<!-- APP VIEW -->
<div id="appView" style="display:none">
<div class="scrim" id="scrim" onclick="closeSidebar()"></div>
<div class="app">
  <aside class="sidebar" id="sidebar">
    <div class="sidebar-brand">
      <div class="mark">📸</div>
      <div class="name">Photo<span>Studio</span></div>
    </div>
    <nav class="nav" id="navList">
      <div class="nav-section">Main</div>
      <div class="nav-item active" data-page="dashboard"><span class="ic">📊</span> Dashboard</div>
      <div class="nav-item" data-page="editor"><span class="ic">🎨</span> Photo Editor</div>
      <div class="nav-item" data-page="passport"><span class="ic">📄</span> Passport Maker</div>
      <div class="nav-section">Account</div>
      <div class="nav-item" data-page="myactivity"><span class="ic">🕐</span> My Activity</div>
      <div class="nav-item" data-page="settings"><span class="ic">⚙️</span> Settings</div>
      <div class="nav-section" id="adminNavSection" style="display:none">Administration</div>
      <div class="nav-item" data-page="admin-users" id="adminUsersNav" style="display:none"><span class="ic">👥</span> Users</div>
      <div class="nav-item" data-page="admin-activity" id="adminActNav" style="display:none"><span class="ic">📈</span> Activity Log</div>
      <div class="nav-item" data-page="admin-features" id="adminFeatNav" style="display:none"><span class="ic">🧩</span> Features</div>
      <div class="nav-item" data-page="admin-settings" id="adminSetNav" style="display:none"><span class="ic">🔧</span> System</div>
    </nav>
    <div class="sidebar-foot">
      <div style="position:relative">
        <div class="user-chip" id="userChip" onclick="toggleUserMenu()">
          <div class="user-avatar" id="userAvatar">U</div>
          <div class="user-info">
            <div class="nm" id="userName">User</div>
            <div class="em" id="userEmail">user@email.com</div>
          </div>
          <span style="color:var(--mut)">⌄</span>
        </div>
        <div class="user-menu" id="userMenu">
          <button onclick="goPage('settings')"><span>⚙️</span> Account Settings</button>
          <button onclick="logout()"><span style="color:var(--err)">⏻</span> <span style="color:var(--err)">Sign Out</span></button>
        </div>
      </div>
    </div>
  </aside>

  <main class="main">
    <div class="topbar">
      <button class="menu-btn" onclick="openSidebar()">☰</button>
      <h1 id="pageTitle">Dashboard</h1>
      <div class="tb-actions">
        <div class="tb-pill" id="statusPill"><span class="dot"></span><span class="lbl">All Systems Operational</span></div>
      </div>
    </div>
    <div class="content">

      <!-- DASHBOARD -->
      <div class="page on" id="page-dashboard">
        <div id="dashMaintBanner"></div>
        <div class="stat-grid">
          <div class="stat"><div class="ic">🖼</div><div class="lbl">Total Edits</div><div class="val" id="statEdits">0</div></div>
          <div class="stat"><div class="ic">📄</div><div class="lbl">Passport Sheets</div><div class="val" id="statPassports">0</div></div>
          <div class="stat"><div class="ic">📤</div><div class="lbl">Files Exported</div><div class="val" id="statExports">0</div></div>
          <div class="stat"><div class="ic">📅</div><div class="lbl">Member Since</div><div class="val" id="statSince" style="font-size:18px">—</div></div>
        </div>
        <div class="card">
          <div class="card-head"><h3>Quick Tools</h3></div>
          <p class="card-sub">Jump straight into your workflow.</p>
          <div class="tool-grid">
            <div class="tool-card" onclick="goPage('editor')"><div class="ic">🎨</div><h4>Photo Editor</h4><p>Full adjustment suite: brightness, contrast, exposure, color, filters &amp; more.</p></div>
            <div class="tool-card" onclick="startPassportEditor()"><div class="ic">📄</div><h4>Passport Maker</h4><p>Generate print-ready passport photo sheets at 300 DPI.</p></div>
            <div class="tool-card" onclick="goPage('editor');setTimeout(()=>{if(document.getElementById('fileInput'))document.getElementById('fileInput').click()},300)"><div class="ic">✨</div><h4>Quick Enhance</h4><p>Auto-enhance any photo with one click — perfect for printing.</p></div>
            <div class="tool-card" onclick="goPage('editor');setTimeout(()=>{if(document.getElementById('fileInput'))document.getElementById('fileInput').click()},300)"><div class="ic">✂️</div><h4>Crop &amp; Resize</h4><p>Smart crop to any aspect ratio or custom dimensions.</p></div>
          </div>
        </div>
      </div>

      <!-- PHOTO EDITOR -->
      <div class="page" id="page-editor">
        <div id="editorMaintBanner"></div>
        <div class="editor-wrap">
          <div class="editor-side">
            <div class="dz" id="dz" onclick="document.getElementById('fileInput').click()">
              <div class="big">📁</div>
              <p>Upload an image</p>
              <small>JPG, PNG, WEBP — up to 25 MB</small>
            </div>
            <input type="file" id="fileInput" accept="image/*" style="display:none">
            <div class="tool-tabs">
              <button class="tool-tab active" data-tab="adjust">Adjust</button>
              <button class="tool-tab" data-tab="filters">Filters</button>
              <button class="tool-tab" data-tab="crop">Crop</button>
              <button class="tool-tab" data-tab="bg">Background</button>
              <button class="tool-tab" data-tab="export">Export</button>
            </div>
            <div class="tool-panel on" id="panel-adjust">
              <div class="ctrl"><div class="ctrl-lbl"><span>⚡ Auto Enhance</span></div><button class="btn btn-primary btn-sm" style="width:100%" onclick="applyAutoEnhance()">✨ Auto Enhance Photo</button></div>
              <div class="ctrl"><div class="ctrl-lbl"><span>Brightness</span><span class="ctrl-val" id="vBrightness">100%</span></div><input type="range" class="slider" id="brightness" min="0" max="200" value="100" oninput="onAdjust()"></div>
              <div class="ctrl"><div class="ctrl-lbl"><span>Contrast</span><span class="ctrl-val" id="vContrast">100%</span></div><input type="range" class="slider" id="contrast" min="0" max="200" value="100" oninput="onAdjust()"></div>
              <div class="ctrl"><div class="ctrl-lbl"><span>Exposure</span><span class="ctrl-val" id="vExposure">0</span></div><input type="range" class="slider" id="exposure" min="-200" max="200" value="0" oninput="onAdjust()"></div>
              <div class="ctrl"><div class="ctrl-lbl"><span>Sharpness</span><span class="ctrl-val" id="vSharpness">100%</span></div><input type="range" class="slider" id="sharpness" min="0" max="300" value="100" oninput="onAdjust()"></div>
              <div class="ctrl"><div class="ctrl-lbl"><span>Saturation</span><span class="ctrl-val" id="vSaturation">100%</span></div><input type="range" class="slider" id="saturation" min="0" max="200" value="100" oninput="onAdjust()"></div>
              <div class="ctrl"><div class="ctrl-lbl"><span>Temperature</span><span class="ctrl-val" id="vTemp">0</span></div><input type="range" class="slider" id="temperature" min="-100" max="100" value="0" oninput="onAdjust()"></div>
              <div class="ctrl"><div class="ctrl-lbl"><span>Tint</span><span class="ctrl-val" id="vTint">0</span></div><input type="range" class="slider" id="tint" min="-100" max="100" value="0" oninput="onAdjust()"></div>
            </div>
            <div class="tool-panel" id="panel-filters">
              <div class="filter-grid" id="filterGrid"></div>
            </div>
            <div class="tool-panel" id="panel-crop">
              <div class="seg" id="flipSeg">
                <button onclick="doFlip('horizontal')">↔ Flip H</button>
                <button onclick="doFlip('vertical')">↕ Flip V</button>
              </div>
              <div class="ctrl"><div class="ctrl-lbl"><span>Rotate</span><span class="ctrl-val" id="vRotate">0°</span></div><input type="range" class="slider" id="rotate" min="-180" max="180" value="0" oninput="document.getElementById('vRotate').textContent=this.value+'°'"></div>
              <div style="display:flex;gap:8px;margin-bottom:14px"><button class="btn btn-ghost btn-sm" style="flex:1" onclick="doRotate(-90)">⟲ -90°</button><button class="btn btn-ghost btn-sm" style="flex:1" onclick="doRotate(90)">⟳ 90°</button></div>
              <h4 style="font-size:13px;color:var(--mut);margin-bottom:10px">Crop to Aspect Ratio</h4>
              <div class="seg" id="ratioSeg">
                <button data-r="0" class="active">Free</button>
                <button data-r="1">1:1</button>
                <button data-r="1.7778">16:9</button>
                <button data-r="1.3333">4:3</button>
                <button data-r="0.75">3:4</button>
                <button data-r="0.6667">2:3</button>
              </div>
              <div class="ctrl"><div class="ctrl-lbl"><span>Custom Size (px)</span></div>
                <div class="ctrl-row">
                  <div class="form-field"><input type="number" id="resizeW" placeholder="Width" min="1"></div>
                  <div class="form-field"><input type="number" id="resizeH" placeholder="Height" min="1"></div>
                </div>
                <button class="btn btn-ghost btn-sm" style="width:100%" onclick="doResize()">Apply Resize</button>
              </div>
            </div>
            <div class="tool-panel" id="panel-bg">
              <p style="font-size:13px;color:var(--mut);margin-bottom:14px">Replace or remove the photo background automatically.</p>
              <div class="ctrl"><div class="ctrl-lbl"><span>Replace Background Color</span></div>
                <div style="display:grid;grid-template-columns:repeat(4,1fr);gap:8px;margin-bottom:10px">
                  <div onclick="setBgColor('#1e69f3')" style="height:36px;border-radius:8px;background:#1e69f3;cursor:pointer;border:2px solid var(--line)"></div>
                  <div onclick="setBgColor('#d33f3f')" style="height:36px;border-radius:8px;background:#d33f3f;cursor:pointer;border:2px solid var(--line)"></div>
                  <div onclick="setBgColor('#ffffff')" style="height:36px;border-radius:8px;background:#ffffff;cursor:pointer;border:2px solid var(--line)"></div>
                  <div onclick="setBgColor('#2e7d32')" style="height:36px;border-radius:8px;background:#2e7d32;cursor:pointer;border:2px solid var(--line)"></div>
                </div>
                <div class="form-field"><input type="text" id="bgHex" placeholder="#FFFFFF" maxlength="7"><button class="btn btn-primary btn-sm" style="width:100%;margin-top:8px" onclick="applyBgReplace()">Replace Background</button></div>
              </div>
              <hr style="border:none;border-top:1px solid var(--line);margin:16px 0">
              <button class="btn btn-ghost btn-sm" style="width:100%" onclick="applyRemoveBg()">🗑 Remove Background (Transparent)</button>
            </div>
            <div class="tool-panel" id="panel-export">
              <div class="export-opts">
                <h4 style="font-size:13px;color:var(--mut);margin-bottom:10px">Export Format</h4>
                <div class="exp-fmt" id="expFmt">
                  <button data-f="jpg" class="active">JPG</button>
                  <button data-f="png">PNG</button>
                  <button data-f="webp">WEBP</button>
                  <button data-f="bmp">BMP</button>
                </div>
                <div class="exp-q">
                  <div class="ctrl-lbl"><span>Quality</span><span class="ctrl-val" id="vExpQ">95</span></div>
                  <input type="range" class="slider" id="expQuality" min="10" max="100" value="95" oninput="document.getElementById('vExpQ').textContent=this.value">
                </div>
                <button class="btn btn-primary" style="width:100%" onclick="exportImage()">⬇ Download Image</button>
                <hr style="border:none;border-top:1px solid var(--line);margin:16px 0">
                <h4 style="font-size:13px;color:var(--mut);margin-bottom:10px">Compress Image</h4>
                <button class="btn btn-ghost btn-sm" style="width:100%" onclick="compressImage()">🗜 Compress (smart quality)</button>
              </div>
            </div>
          </div>
          <div class="canvas-area">
            <div class="canvas-toolbar">
              <button class="btn btn-ghost btn-sm" id="undoBtn" onclick="undo()" disabled>↩ Undo</button>
              <button class="btn btn-ghost btn-sm" id="redoBtn" onclick="redo()" disabled>↪ Redo</button>
              <button class="btn btn-ghost btn-sm" onclick="resetAll()">↺ Reset</button>
              <button class="btn btn-ghost btn-sm" onclick="toggleBeforeAfter()" id="baBtn">👁 Before/After</button>
              <div style="flex:1"></div>
              <button class="btn btn-ghost btn-sm" onclick="document.getElementById('fileInput').click()">📂 New Image</button>
            </div>
            <div class="canvas-stage" id="canvasStage">
              <canvas id="editorCanvas" style="display:none"></canvas>
              <div class="canvas-empty" id="canvasEmpty">
                <div class="big">🖼</div>
                <p>No image loaded</p>
                <small>Upload an image to start editing</small>
              </div>
              <div class="overlay-spin" id="processingSpin" style="display:none"><div class="spinner"></div><div id="processingMsg">Processing…</div></div>
            </div>
            <div class="canvas-status">
              <span id="imgInfo">—</span>
              <span id="zoomInfo">100%</span>
            </div>
          </div>
          <div class="history-side">
            <h4 style="padding:16px;font-size:14px;font-weight:700;border-bottom:1px solid var(--line)">History</h4>
            <div id="historyList">
              <div class="empty" style="padding:24px 12px"><p style="font-size:13px">Edits will appear here</p></div>
            </div>
          </div>
        </div>
      </div>

      <!-- PASSPORT MAKER -->
      <div class="page" id="page-passport">
        <div id="passportMaintBanner"></div>
        <div class="card" style="margin-bottom:20px">
          <div class="card-head"><h3>📄 Passport Photo Maker</h3></div>
          <p class="card-sub">Upload a photo and generate print-ready sheets at 300 DPI with exact physical sizes.</p>
          <div class="dz" id="psDz" onclick="document.getElementById('psFileInput').click()">
            <div class="big">📁</div><p>Upload a photo</p><small>JPG, PNG — up to 25 MB</small>
          </div>
          <input type="file" id="psFileInput" accept="image/*" style="display:none">
          <div id="psForm" style="display:none">
            <img id="psPreview" style="max-width:200px;border-radius:10px;margin:14px 0;display:block">
            <div class="form-row">
              <div class="form-field"><label>Page Size</label><select id="psPage"><option value="A4">A4 (210×297mm)</option><option value="A3">A3</option><option value="A5">A5</option><option value="Letter">Letter</option><option value="Legal">Legal</option><option value="custom">Custom</option></select></div>
              <div class="form-field"><label>Photo Size</label><select id="psPhoto"><option value="25x35">25×35 mm</option><option value="30x40">30×40 mm</option><option value="35x45" selected>35×45 mm</option><option value="2x2">2×2 inch</option><option value="custom">Custom</option></select></div>
            </div>
            <div class="form-row" id="psCustomPage" style="display:none">
              <div class="form-field"><label>Page W (mm)</label><input type="number" id="psPW" placeholder="210"></div>
              <div class="form-field"><label>Page H (mm)</label><input type="number" id="psPH" placeholder="297"></div>
            </div>
            <div class="form-row" id="psCustomPhoto" style="display:none">
              <div class="form-field"><label>Photo W (mm)</label><input type="number" id="psPhW" placeholder="35"></div>
              <div class="form-field"><label>Photo H (mm)</label><input type="number" id="psPhH" placeholder="45"></div>
            </div>
            <div class="form-row">
              <div class="form-field"><label>Background</label><select id="psBg"><option value="skip">Keep original</option><option value="blue">Blue</option><option value="red">Red</option><option value="white">White</option><option value="green">Green</option><option value="custom">Custom HEX</option></select></div>
              <div class="form-field"><label>Quantity</label><input type="number" id="psQty" value="8" min="1" max="500"></div>
            </div>
            <div class="form-field" id="psBgHex" style="display:none;margin-bottom:16px"><label>Background HEX</label><input type="text" id="psHex" placeholder="#FFFFFF" maxlength="7"></div>
            <div class="form-row full"><div class="form-field"><label>Output Format</label><select id="psFmt"><option value="pdf">PDF</option><option value="jpg">JPEG</option><option value="png">PNG</option><option value="pdf_jpg">PDF + JPEG</option><option value="pdf_png">PDF + PNG</option></select></div></div>
            <button class="btn btn-primary" id="psGenBtn" onclick="generatePassport()">🖨 Generate Print Sheet</button>
            <div id="psResult"></div>
          </div>
        </div>
      </div>

      <!-- MY ACTIVITY -->
      <div class="page" id="page-myactivity">
        <div class="card">
          <div class="card-head"><h3>🕐 My Activity</h3></div>
          <p class="card-sub">Your recent actions on the platform.</p>
          <div class="tbl-wrap"><table class="tbl"><thead><tr><th>Action</th><th>Files</th><th>When</th></tr></thead><tbody id="myActBody"><tr><td colspan="3" class="empty">No activity yet.</td></tr></tbody></table></div>
        </div>
      </div>

      <!-- SETTINGS -->
      <div class="page" id="page-settings">
        <div class="card" style="max-width:600px">
          <div class="card-head"><h3>⚙️ Account Settings</h3></div>
          <div class="form-row full"><div class="form-field"><label>Display Name</label><input type="text" id="setName" placeholder="Your name"></div></div>
          <div class="form-row full"><div class="form-field"><label>Email</label><input type="email" id="setEmail" readonly style="opacity:.6"></div></div>
          <hr style="border:none;border-top:1px solid var(--line);margin:20px 0">
          <h4 style="font-size:15px;margin-bottom:14px">Change Password</h4>
          <div class="form-row full"><div class="form-field"><label>Current Password</label><input type="password" id="setCurPw" placeholder="Current password"></div></div>
          <div class="form-row"><div class="form-field"><label>New Password</label><input type="password" id="setNewPw" placeholder="New password"></div><div class="form-field"><label>Confirm</label><input type="password" id="setConfPw" placeholder="Confirm"></div></div>
          <div style="display:flex;gap:10px;margin-top:8px"><button class="btn btn-primary" onclick="saveSettings()">Save Changes</button><button class="btn btn-ghost" onclick="changePassword()">Update Password</button></div>
        </div>
      </div>

      <!-- ADMIN: USERS -->
      <div class="page" id="page-admin-users">
        <div class="stat-grid">
          <div class="stat"><div class="ic">👥</div><div class="lbl">Total Users</div><div class="val" id="admTotalUsers">0</div></div>
          <div class="stat"><div class="ic">✅</div><div class="lbl">Active Users</div><div class="val" id="admActiveUsers">0</div></div>
          <div class="stat"><div class="ic">🚫</div><div class="lbl">Banned Users</div><div class="val" id="admBannedUsers">0</div></div>
          <div class="stat"><div class="ic">🔐</div><div class="lbl">Active Sessions</div><div class="val" id="admSessions">0</div></div>
        </div>
        <div class="card">
          <div class="card-head"><h3>👥 User Management</h3><button class="btn btn-primary btn-sm" onclick="loadAdminUsers()">↻ Refresh</button></div>
          <p class="card-sub">Manage access, bans, and permissions for all users.</p>
          <div class="tbl-wrap"><table class="tbl"><thead><tr><th>User</th><th>Joined</th><th>Last Login</th><th>Status</th><th>Bot Access</th><th>Actions</th></tr></thead><tbody id="admUsersBody"><tr><td colspan="6" class="empty">Loading…</td></tr></tbody></table></div>
        </div>
      </div>

      <!-- ADMIN: ACTIVITY -->
      <div class="page" id="page-admin-activity">
        <div class="card">
          <div class="card-head"><h3>📈 System Activity Log</h3><button class="btn btn-primary btn-sm" onclick="loadAdminActivity()">↻ Refresh</button></div>
          <p class="card-sub">Recent platform-wide activity.</p>
          <div class="tbl-wrap"><table class="tbl"><thead><tr><th>User</th><th>Action</th><th>Details</th><th>IP</th><th>When</th></tr></thead><tbody id="admActBody"><tr><td colspan="5" class="empty">Loading…</td></tr></tbody></table></div>
        </div>
      </div>

      <!-- ADMIN: FEATURES -->
      <div class="page" id="page-admin-features">
        <div class="card" style="max-width:640px">
          <div class="card-head"><h3>🧩 Feature Toggles</h3></div>
          <p class="card-sub">Enable or disable features across the platform.</p>
          <div id="featList"></div>
          <button class="btn btn-primary" style="margin-top:16px" onclick="saveFeatures()">Save Feature Settings</button>
        </div>
      </div>

      <!-- ADMIN: SETTINGS -->
      <div class="page" id="page-admin-settings">
        <div class="card" style="max-width:640px">
          <div class="card-head"><h3>🔧 System Settings</h3></div>
          <div class="form-row full"><div class="form-field"><label>Site Name</label><input type="text" id="setSiteName"></div></div>
          <div class="form-row full"><div class="form-field"><label>Max Upload Size (MB)</label><input type="number" id="setMaxUpload" min="1" max="100"></div></div>
          <div class="form-row"><div class="form-field"><label>Registration Open</label><div style="padding-top:6px"><label class="toggle"><input type="checkbox" id="setRegOpen"><span class="track"></span><span class="thumb"></span></label></div></div><div class="form-field"><label>Maintenance Mode</label><div style="padding-top:6px"><label class="toggle"><input type="checkbox" id="setMaint"><span class="track"></span><span class="thumb"></span></label></div></div></div>
          <div class="form-row full"><div class="form-field"><label>Maintenance Message</label><textarea id="setMaintMsg" placeholder="Message shown to users during maintenance"></textarea></div></div>
          <button class="btn btn-primary" style="margin-top:8px" onclick="saveSystemSettings()">Save System Settings</button>
        </div>
      </div>

    </div>
  </main>
</div>
</div>

<div id="toast"></div>
<div class="modal-bg" id="modalBg" onclick="if(event.target===this)closeModal()"><div class="modal" id="modalBox"></div></div>

<script>
const API = "/api";
let TOKEN = localStorage.getItem("ps_token") || "";
let USER = null;
let currentImage = null;
let originalImage = null;
let history = [];
let historyIdx = -1;
let showingBefore = false;
let currentFilter = "original";
let exportFmt = "jpg";

// ===== Toast =====
function toast(msg, type="info", dur=3500){
  const c = document.getElementById("toast");
  const t = document.createElement("div");
  t.className = "toast "+type;
  const icons = {ok:"✅",err:"❌",warn:"⚠️",info:"ℹ️"};
  t.innerHTML = `<span class="ic">${icons[type]||"ℹ️"}</span><span class="msg">${esc(msg)}</span><button class="x" onclick="this.parentElement.remove()">✕</button>`;
  c.appendChild(t);
  setTimeout(()=>{t.style.opacity="0";t.style.transform="translateX(40px)";setTimeout(()=>t.remove(),300)},dur);
}
function esc(s){return String(s).replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]))}

// ===== Auth =====
function showLogin(){
  document.getElementById("authTitle").textContent="Welcome back";
  document.getElementById("authSub").textContent="Sign in to access your studio.";
  document.getElementById("loginForm").style.display="block";
  document.getElementById("registerForm").style.display="none";
  document.getElementById("authSwitch").innerHTML=`Don't have an account? <a href="#" onclick="showRegister();return false">Create one</a>`;
  hideAuthMsg();
}
function showRegister(){
  document.getElementById("authTitle").textContent="Create your account";
  document.getElementById("authSub").textContent="Start editing like a pro in seconds.";
  document.getElementById("loginForm").style.display="none";
  document.getElementById("registerForm").style.display="block";
  document.getElementById("authSwitch").innerHTML=`Already have an account? <a href="#" onclick="showLogin();return false">Sign in</a>`;
  hideAuthMsg();
}
function hideAuthMsg(){document.getElementById("authErr").classList.remove("show");document.getElementById("authOk").classList.remove("show")}
function authErr(m){const e=document.getElementById("authErr");e.textContent=m;e.classList.add("show")}
function authOkMsg(m){const e=document.getElementById("authOk");e.textContent=m;e.classList.add("show")}
function togglePw(id,btn){const i=document.getElementById(id);i.type=i.type==="password"?"text":"password";btn.textContent=i.type==="password"?"👁":"🙈"}

document.getElementById("loginForm").addEventListener("submit",async e=>{
  e.preventDefault();
  const btn=document.getElementById("loginBtn");
  btn.disabled=true;btn.textContent="Signing in…";
  try{
    const r=await fetch(API+"/auth/login",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({email:document.getElementById("loginEmail").value,password:document.getElementById("loginPw").value})});
    const d=await r.json();
    if(!r.ok){authErr(d.error||"Login failed.");btn.disabled=false;btn.textContent="Sign In →";return}
    TOKEN=d.token;localStorage.setItem("ps_token",TOKEN);
    await initApp();
  }catch(err){authErr("Network error. Please try again.");btn.disabled=false;btn.textContent="Sign In →"}
});

document.getElementById("registerForm").addEventListener("submit",async e=>{
  e.preventDefault();
  const btn=document.getElementById("regBtn");
  btn.disabled=true;btn.textContent="Creating…";
  try{
    const r=await fetch(API+"/auth/register",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({email:document.getElementById("regEmail").value,password:document.getElementById("regPw").value,display_name:document.getElementById("regName").value})});
    const d=await r.json();
    if(!r.ok){authErr(d.error||"Registration failed.");btn.disabled=false;btn.textContent="Create Account →";return}
    TOKEN=d.token;localStorage.setItem("ps_token",TOKEN);
    await initApp();
  }catch(err){authErr("Network error. Please try again.");btn.disabled=false;btn.textContent="Create Account →"}
});

async function initApp(){
  try{
    const r=await fetch(API+"/auth/me",{headers:authHdr()});
    if(!r.ok){logout();return}
    USER=await r.json();
    showApp();
  }catch{logout()}
}
function authHdr(){return{"Authorization":"Bearer "+TOKEN}}

function logout(){TOKEN="";USER=null;localStorage.removeItem("ps_token");document.getElementById("appView").style.display="none";document.getElementById("authView").style.display="grid";showLogin()}

function showApp(){
  document.getElementById("authView").style.display="none";
  document.getElementById("appView").style.display="block";
  document.getElementById("userName").textContent=USER.display_name||USER.email;
  document.getElementById("userEmail").textContent=USER.email;
  document.getElementById("userAvatar").textContent=(USER.display_name||USER.email)[0].toUpperCase();
  const isAdmin=USER.is_admin==1;
  document.getElementById("adminNavSection").style.display=isAdmin?"block":"none";
  ["adminUsersNav","adminActNav","adminFeatNav","adminSetNav"].forEach(id=>document.getElementById(id).style.display=isAdmin?"flex":"none");
  loadDashboard();
  checkMaintenance();
}

// ===== Navigation =====
function goPage(p){
  document.querySelectorAll(".nav-item").forEach(n=>n.classList.remove("active"));
  const item=document.querySelector(`.nav-item[data-page="${p}"]`);
  if(item)item.classList.add("active");
  document.querySelectorAll(".page").forEach(pg=>pg.classList.remove("on"));
  document.getElementById("page-"+p).classList.add("on");
  const titles={dashboard:"Dashboard",editor:"Photo Editor",passport:"Passport Maker",myactivity:"My Activity",settings:"Account Settings","admin-users":"User Management","admin-activity":"Activity Log","admin-features":"Feature Toggles","admin-settings":"System Settings"};
  document.getElementById("pageTitle").textContent=titles[p]||"Dashboard";
  closeSidebar();
  if(p==="dashboard")loadDashboard();
  if(p==="myactivity")loadMyActivity();
  if(p==="admin-users")loadAdminUsers();
  if(p==="admin-activity")loadAdminActivity();
  if(p==="admin-features")loadFeatures();
  if(p==="admin-settings")loadSystemSettings();
}
document.querySelectorAll(".nav-item").forEach(n=>n.addEventListener("click",()=>goPage(n.dataset.page)));
function openSidebar(){document.getElementById("sidebar").classList.add("open");document.getElementById("scrim").classList.add("show")}
function closeSidebar(){document.getElementById("sidebar").classList.remove("open");document.getElementById("scrim").classList.remove("show")}
function toggleUserMenu(){document.getElementById("userMenu").classList.toggle("show")}
document.addEventListener("click",e=>{if(!e.target.closest("#userChip")&&!e.target.closest("#userMenu"))document.getElementById("userMenu").classList.remove("show")});

// ===== Dashboard =====
async function loadDashboard(){
  try{
    const r=await fetch(API+"/stats",{headers:authHdr()});
    if(r.ok){
      const d=await r.json();
      document.getElementById("statEdits").textContent=d.edits||0;
      document.getElementById("statPassports").textContent=d.passports||0;
      document.getElementById("statExports").textContent=d.exports||0;
      document.getElementById("statSince").textContent=d.member_since||"—";
    }
  }catch{}
}

// ===== Maintenance check =====
async function checkMaintenance(){
  try{
    const r=await fetch(API+"/settings/public");
    if(r.ok){
      const d=await r.json();
      if(d.maintenance_mode==="1"&&!USER.is_admin){
        const banner=`<div class="maint-banner"><span>🔧</span><span>${esc(d.maintenance_message||"System under maintenance.")}</span></div>`;
        ["dashMaintBanner","editorMaintBanner","passportMaintBanner"].forEach(id=>{const el=document.getElementById(id);if(el)el.innerHTML=banner});
      }
    }
  }catch{}
}

// ===== Editor =====
const fileInput=document.getElementById("fileInput");
const dz=document.getElementById("dz");
fileInput.addEventListener("change",e=>{if(e.target.files[0])loadEditorImage(e.target.files[0])});
["dragover","dragenter"].forEach(ev=>dz.addEventListener(ev,e=>{e.preventDefault();dz.classList.add("over")}));
["dragleave","drop"].forEach(ev=>dz.addEventListener(ev,e=>{e.preventDefault();dz.classList.remove("over")}));
dz.addEventListener("drop",e=>{if(e.dataTransfer.files[0])loadEditorImage(e.dataTransfer.files[0])});

function loadEditorImage(file){
  if(file.size>25*1024*1024){toast("File too large (max 25 MB).","err");return}
  const reader=new FileReader();
  reader.onload=async e=>{
    showProcessing("Loading image…");
    try{
      const fd=new FormData();
      fd.append("image",file);
      const r=await fetch(API+"/editor/upload",{method:"POST",headers:authHdr(),body:fd});
      if(!r.ok){const d=await r.json().catch(()=>({}));toast(d.error||"Upload failed.","err");hideProcessing();return}
      const d=await r.json();
      currentImage=d.url;
      originalImage=d.url;
      history=[];historyIdx=-1;
      pushHistory("Upload");
      await renderCanvas(d.url);
      document.getElementById("canvasEmpty").style.display="none";
      document.getElementById("editorCanvas").style.display="block";
      document.getElementById("imgInfo").textContent=`${d.width} × ${d.height}px`;
      toast("Image loaded!","ok");
    }catch(err){toast("Failed to load image.","err")}
    hideProcessing();
  };
  reader.readAsDataURL(file);
}

async function renderCanvas(url){
  return new Promise((resolve,reject)=>{
    const img=new Image();
    img.onload=()=>{
      const c=document.getElementById("editorCanvas");
      const stage=document.getElementById("canvasStage");
      const maxW=stage.clientWidth-40,maxH=stage.clientHeight-40;
      let w=img.width,h=img.height;
      const k=Math.min(maxW/w,maxH/h,1);
      w=Math.round(w*k);h=Math.round(h*k);
      c.width=w;c.height=h;
      const ctx=c.getContext("2d");
      ctx.drawImage(img,0,0,w,h);
      resolve();
    };
    img.onerror=reject;
    img.src=url;
  });
}

function showProcessing(msg){document.getElementById("processingMsg").textContent=msg||"Processing…";document.getElementById("processingSpin").style.display="flex"}
function hideProcessing(){document.getElementById("processingSpin").style.display="none"}

// Tool tabs
document.querySelectorAll(".tool-tab").forEach(t=>t.addEventListener("click",()=>{
  document.querySelectorAll(".tool-tab").forEach(x=>x.classList.remove("active"));
  document.querySelectorAll(".tool-panel").forEach(x=>x.classList.remove("on"));
  t.classList.add("active");
  document.getElementById("panel-"+t.dataset.tab).classList.add("on");
  if(t.dataset.tab==="filters")renderFilters();
}));

// Adjustments
function onAdjust(){
  document.getElementById("vBrightness").textContent=document.getElementById("brightness").value+"%";
  document.getElementById("vContrast").textContent=document.getElementById("contrast").value+"%";
  document.getElementById("vExposure").textContent=document.getElementById("exposure").value;
  document.getElementById("vSharpness").textContent=document.getElementById("sharpness").value+"%";
  document.getElementById("vSaturation").textContent=document.getElementById("saturation").value+"%";
  document.getElementById("vTemp").textContent=document.getElementById("temperature").value;
  document.getElementById("vTint").textContent=document.getElementById("tint").value;
}
let adjustTimer=null;
["brightness","contrast","exposure","sharpness","saturation","temperature","tint"].forEach(id=>{
  document.getElementById(id).addEventListener("change",()=>{clearTimeout(adjustTimer);adjustTimer=setTimeout(commitAdjust,300)});
});

async function commitAdjust(){
  if(!currentImage)return;
  showProcessing("Applying adjustments…");
  const ops=[
    {op:"brightness",factor:parseFloat(document.getElementById("brightness").value)/100},
    {op:"contrast",factor:parseFloat(document.getElementById("contrast").value)/100},
    {op:"exposure",stops:parseFloat(document.getElementById("exposure").value)/100},
    {op:"sharpness",factor:parseFloat(document.getElementById("sharpness").value)/100},
    {op:"saturation",factor:parseFloat(document.getElementById("saturation").value)/100},
    {op:"temperature",value:parseFloat(document.getElementById("temperature").value)},
    {op:"tint",value:parseFloat(document.getElementById("tint").value)},
  ];
  try{
    const r=await fetch(API+"/editor/process",{method:"POST",headers:{...authHdr(),"Content-Type":"application/json"},body:JSON.stringify({image:currentImage,ops})});
    if(!r.ok){toast("Adjustment failed.","err");hideProcessing();return}
    const d=await r.json();
    currentImage=d.url;
    pushHistory("Adjust");
    await renderCanvas(d.url);
  }catch{toast("Processing failed.","err")}
  hideProcessing();
}

function applyAutoEnhance(){
  if(!currentImage){toast("Upload an image first.","warn");return}
  processOps([{op:"auto_enhance"}],"Auto Enhance");
}

async function processOps(ops,label){
  if(!currentImage)return;
  showProcessing(label+"…");
  try{
    const r=await fetch(API+"/editor/process",{method:"POST",headers:{...authHdr(),"Content-Type":"application/json"},body:JSON.stringify({image:currentImage,ops})});
    if(!r.ok){toast(label+" failed.","err");hideProcessing();return}
    const d=await r.json();
    currentImage=d.url;
    pushHistory(label);
    await renderCanvas(d.url);
    toast(label+" applied!","ok");
  }catch{toast(label+" failed.","err")}
  hideProcessing();
}

// Filters
const FILTERS=["original","auto_enhance","vivid","warm","cool","vintage","sepia","bw","noir","fade","dramatic","soft_glow","matte","chrome"];
async function renderFilters(){
  const grid=document.getElementById("filterGrid");
  if(grid.children.length>0)return;
  if(!currentImage){grid.innerHTML='<div class="empty" style="grid-column:1/-1"><p style="font-size:13px">Upload an image first</p></div>';return}
  showProcessing("Generating filter previews…");
  try{
    const r=await fetch(API+"/editor/filters",{method:"POST",headers:{...authHdr(),"Content-Type":"application/json"},body:JSON.stringify({image:currentImage})});
    if(!r.ok){hideProcessing();return}
    const d=await r.json();
    grid.innerHTML="";
    FILTERS.forEach(f=>{
      const cell=document.createElement("div");
      cell.className="filter-cell"+(f===currentFilter?" active":"");
      cell.innerHTML=`<img src="${d.previews[f]}" alt="${f}"><div class="fn">${f.replace(/_/g," ")}</div>`;
      cell.onclick=()=>{
        document.querySelectorAll(".filter-cell").forEach(x=>x.classList.remove("active"));
        cell.classList.add("active");
        currentFilter=f;
        processOps([{op:"filter",name:f}],"Filter: "+f);
      };
      grid.appendChild(cell);
    });
  }catch{}
  hideProcessing();
}

// Crop / Flip / Rotate
document.querySelectorAll("#ratioSeg button").forEach(b=>b.addEventListener("click",()=>{
  document.querySelectorAll("#ratioSeg button").forEach(x=>x.classList.remove("active"));
  b.classList.add("active");
  if(!currentImage)return;
  const r=parseFloat(b.dataset.r);
  if(r>0)processOps([{op:"crop_ratio",ratio:r}],"Crop "+b.textContent);
}));
function doFlip(dir){if(currentImage)processOps([{op:"flip",direction:dir}],"Flip "+dir)}
function doRotate(deg){if(currentImage)processOps([{op:"rotate",degrees:deg}],"Rotate "+deg+"°")}
function doResize(){
  if(!currentImage){toast("Upload an image first.","warn");return}
  const w=parseInt(document.getElementById("resizeW").value),h=parseInt(document.getElementById("resizeH").value);
  if(!w||!h||w<1||h<1){toast("Enter valid dimensions.","warn");return}
  processOps([{op:"resize",w:w,h:h}],"Resize to "+w+"×"+h);
}

// Background
function setBgColor(hex){document.getElementById("bgHex").value=hex}
function applyBgReplace(){
  if(!currentImage){toast("Upload an image first.","warn");return}
  const hex=document.getElementById("bgHex").value.trim();
  if(!/^#?[0-9a-fA-F]{6}$/.test(hex)){toast("Invalid HEX color.","err");return}
  processOps([{op:"background",hex:hex.startsWith("#")?hex:"#"+hex}],"Background Replace");
}
function applyRemoveBg(){if(currentImage)processOps([{op:"remove_bg"}],"Remove Background")}

// Export
document.querySelectorAll("#expFmt button").forEach(b=>b.addEventListener("click",()=>{
  document.querySelectorAll("#expFmt button").forEach(x=>x.classList.remove("active"));
  b.classList.add("active");exportFmt=b.dataset.f;
}));
async function exportImage(){
  if(!currentImage){toast("Upload an image first.","warn");return}
  showProcessing("Exporting…");
  try{
    const q=parseInt(document.getElementById("expQuality").value);
    const r=await fetch(API+"/editor/export",{method:"POST",headers:{...authHdr(),"Content-Type":"application/json"},body:JSON.stringify({image:currentImage,format:exportFmt,quality:q})});
    if(!r.ok){toast("Export failed.","err");hideProcessing();return}
    const blob=await r.blob();
    const cd=r.headers.get("Content-Disposition")||"";
    const m=cd.match(/filename="?([^";]+)"?/);
    const name=m?m[1]:"export."+exportFmt;
    const a=document.createElement("a");
    a.href=URL.createObjectURL(blob);a.download=name;document.body.appendChild(a);a.click();a.remove();
    toast("Image exported!","ok");
  }catch{toast("Export failed.","err")}
  hideProcessing();
}
async function compressImage(){
  if(!currentImage){toast("Upload an image first.","warn");return}
  showProcessing("Compressing…");
  try{
    const r=await fetch(API+"/editor/export",{method:"POST",headers:{...authHdr(),"Content-Type":"application/json"},body:JSON.stringify({image:currentImage,format:"jpg",quality:75})});
    if(!r.ok){toast("Compression failed.","err");hideProcessing();return}
    const blob=await r.blob();
    const a=document.createElement("a");a.href=URL.createObjectURL(blob);a.download="compressed.jpg";document.body.appendChild(a);a.click();a.remove();
    toast("Image compressed & downloaded!","ok");
  }catch{toast("Compression failed.","err")}
  hideProcessing();
}

// History
function pushHistory(label){
  history=history.slice(0,historyIdx+1);
  history.push({label,url:currentImage});
  historyIdx=history.length-1;
  renderHistory();
}
function renderHistory(){
  const list=document.getElementById("historyList");
  if(history.length===0){list.innerHTML='<div class="empty" style="padding:24px 12px"><p style="font-size:13px">Edits will appear here</p></div>';return}
  list.innerHTML="";
  history.forEach((h,i)=>{
    const item=document.createElement("div");
    item.className="history-item"+(i===historyIdx?" current":"");
    item.innerHTML=`<span class="ic">${i===0?"📁":"✏️"}</span><span>${esc(h.label)}</span>`;
    item.onclick=()=>{historyIdx=i;currentImage=h.url;renderCanvas(h.url);renderHistory()};
    list.appendChild(item);
  });
  document.getElementById("undoBtn").disabled=historyIdx<=0;
  document.getElementById("redoBtn").disabled=historyIdx>=history.length-1;
}
function undo(){if(historyIdx>0){historyIdx--;currentImage=history[historyIdx].url;renderCanvas(currentImage);renderHistory()}}
function redo(){if(historyIdx<history.length-1){historyIdx++;currentImage=history[historyIdx].url;renderCanvas(currentImage);renderHistory()}}
function resetAll(){
  if(!originalImage)return;
  currentImage=originalImage;history=[{label:"Upload",url:originalImage}];historyIdx=0;
  ["brightness","contrast","saturation","sharpness"].forEach(id=>document.getElementById(id).value=100);
  ["exposure","temperature","tint","rotate"].forEach(id=>document.getElementById(id).value=0);
  onAdjust();
  renderCanvas(currentImage);renderHistory();
  toast("Reset to original.","ok");
}
function toggleBeforeAfter(){
  if(!originalImage||!currentImage)return;
  showingBefore=!showingBefore;
  document.getElementById("baBtn").textContent=showingBefore?"👁 Showing Original":"👁 Before/After";
  renderCanvas(showingBefore?originalImage:currentImage);
}

// ===== Passport Maker =====
const psFileInput=document.getElementById("psFileInput");
const psDz=document.getElementById("psDz");
let psFile=null,psUploadUrl=null;
psFileInput.addEventListener("change",e=>{if(e.target.files[0])loadPassportImage(e.target.files[0])});
["dragover","dragenter"].forEach(ev=>psDz.addEventListener(ev,e=>{e.preventDefault();psDz.classList.add("over")}));
psDz.addEventListener("drop",e=>{e.preventDefault();psDz.classList.remove("over");if(e.dataTransfer.files[0])loadPassportImage(e.dataTransfer.files[0])});

async function loadPassportImage(file){
  if(file.size>25*1024*1024){toast("File too large.","err");return}
  showProcessing("Uploading…");
  try{
    const fd=new FormData();fd.append("image",file);
    const r=await fetch(API+"/editor/upload",{method:"POST",headers:authHdr(),body:fd});
    if(!r.ok){toast("Upload failed.","err");hideProcessing();return}
    const d=await r.json();
    psUploadUrl=d.url;psFile=file;
    document.getElementById("psPreview").src=d.url;
    document.getElementById("psForm").style.display="block";
    document.getElementById("psDz").style.display="none";
  }catch{toast("Upload failed.","err")}
  hideProcessing();
}
document.getElementById("psPage").addEventListener("change",e=>{document.getElementById("psCustomPage").style.display=e.target.value==="custom"?"grid":"none"});
document.getElementById("psPhoto").addEventListener("change",e=>{document.getElementById("psCustomPhoto").style.display=e.target.value==="custom"?"grid":"none"});
document.getElementById("psBg").addEventListener("change",e=>{document.getElementById("psBgHex").style.display=e.target.value==="custom"?"block":"none"});

async function generatePassport(){
  if(!psUploadUrl){toast("Upload a photo first.","warn");return}
  const btn=document.getElementById("psGenBtn");
  btn.disabled=true;btn.textContent="⏳ Generating…";
  try{
    const payload={
      image:psUploadUrl,
      page:document.getElementById("psPage").value,
      page_w:parseFloat(document.getElementById("psPW").value)||null,
      page_h:parseFloat(document.getElementById("psPH").value)||null,
      ps:document.getElementById("psPhoto").value,
      ps_w:parseFloat(document.getElementById("psPhW").value)||null,
      ps_h:parseFloat(document.getElementById("psPhH").value)||null,
      bg:document.getElementById("psBg").value,
      hex:document.getElementById("psHex").value,
      qty:parseInt(document.getElementById("psQty").value)||8,
      fmt:document.getElementById("psFmt").value,
    };
    const r=await fetch(API+"/passport/generate",{method:"POST",headers:{...authHdr(),"Content-Type":"application/json"},body:JSON.stringify(payload)});
    if(!r.ok){const d=await r.json().catch(()=>({}));toast(d.error||"Generation failed.","err");btn.disabled=false;btn.textContent="🖨 Generate Print Sheet";return}
    const blob=await r.blob();
    const cd=r.headers.get("Content-Disposition")||"";
    const m=cd.match(/filename="?([^";]+)"?/);
    const name=m?m[1]:(payload.fmt==="pdf"?"passport.pdf":"passport.zip");
    const a=document.createElement("a");a.href=URL.createObjectURL(blob);a.download=name;document.body.appendChild(a);a.click();a.remove();
    document.getElementById("psResult").innerHTML=`<div class="badge ok" style="margin-top:14px">✅ Downloaded: ${esc(name)}</div>`;
    toast("Print sheet generated!","ok");
  }catch{toast("Generation failed.","err")}
  btn.disabled=false;btn.textContent="🖨 Generate Print Sheet";
}
function startPassportEditor(){goPage("passport")}

// ===== My Activity =====
async function loadMyActivity(){
  try{
    const r=await fetch(API+"/my/activity",{headers:authHdr()});
    if(!r.ok)return;
    const d=await r.json();
    const body=document.getElementById("myActBody");
    if(d.length===0){body.innerHTML='<tr><td colspan="3" class="empty">No activity yet.</td></tr>';return}
    body.innerHTML=d.map(a=>`<tr><td>${esc(a.action)}</td><td>${a.file_count||0}</td><td>${timeAgo(a.timestamp)}</td></tr>`).join("");
  }catch{}
}

// ===== Settings =====
async function loadSettings(){
  if(USER){document.getElementById("setName").value=USER.display_name||"";document.getElementById("setEmail").value=USER.email||""}
}
async function saveSettings(){
  try{
    const r=await fetch(API+"/account/update",{method:"POST",headers:{...authHdr(),"Content-Type":"application/json"},body:JSON.stringify({display_name:document.getElementById("setName").value})});
    if(r.ok){toast("Settings saved.","ok");USER.display_name=document.getElementById("setName").value;document.getElementById("userName").textContent=USER.display_name||USER.email;document.getElementById("userAvatar").textContent=(USER.display_name||USER.email)[0].toUpperCase()}
    else{const d=await r.json().catch(()=>({}));toast(d.error||"Failed to save.","err")}
  }catch{toast("Network error.","err")}
}
async function changePassword(){
  const cur=document.getElementById("setCurPw").value,nw=document.getElementById("setNewPw").value,cf=document.getElementById("setConfPw").value;
  if(!cur||!nw){toast("Fill in all password fields.","warn");return}
  if(nw.length<8){toast("Password must be at least 8 characters.","warn");return}
  if(nw!==cf){toast("Passwords don't match.","err");return}
  try{
    const r=await fetch(API+"/account/password",{method:"POST",headers:{...authHdr(),"Content-Type":"application/json"},body:JSON.stringify({current_password:cur,new_password:nw})});
    if(r.ok){toast("Password updated.","ok");document.getElementById("setCurPw").value="";document.getElementById("setNewPw").value="";document.getElementById("setConfPw").value=""}
    else{const d=await r.json().catch(()=>({}));toast(d.error||"Failed to update.","err")}
  }catch{toast("Network error.","err")}
}

// ===== Admin =====
async function loadAdminUsers(){
  try{
    const r=await fetch(API+"/admin/users",{headers:authHdr()});
    if(!r.ok)return;
    const d=await r.json();
    document.getElementById("admTotalUsers").textContent=d.users.length;
    document.getElementById("admActiveUsers").textContent=d.users.filter(u=>u.is_active&&!u.is_banned).length;
    document.getElementById("admBannedUsers").textContent=d.users.filter(u=>u.is_banned).length;
    document.getElementById("admSessions").textContent=d.active_sessions;
    const body=document.getElementById("admUsersBody");
    body.innerHTML=d.users.map(u=>`<tr>
      <td><div style="font-weight:600">${esc(u.display_name||u.email)}</div><div style="font-size:12px;color:var(--mut)">${esc(u.email)}</div>${u.is_admin?'<span class="badge admin" style="margin-top:4px">ADMIN</span>':''}</td>
      <td>${new Date(u.created_at*1000).toLocaleDateString()}</td>
      <td>${u.last_login?timeAgo(u.last_login):"—"}</td>
      <td>${u.is_banned?'<span class="badge bad">Banned</span>':u.is_active?'<span class="badge ok">Active</span>':'<span class="badge mut">Inactive</span>'}</td>
      <td>${u.has_bot_access?'<span class="badge ok">✓ Granted</span>':'<span class="badge bad">✕ Revoked</span>'}</td>
      <td><div class="row-act">
        <button onclick="toggleBotAccess(${u.id})" class="${u.has_bot_access?'danger':'ok-btn'}">${u.has_bot_access?'Revoke':'Grant'}</button>
        <button onclick="toggleBan(${u.id})" class="${u.is_banned?'ok-btn':'danger'}">${u.is_banned?'Unban':'Ban'}</button>
        <button onclick="toggleAdmin(${u.id})" class="${u.is_admin?'danger':''}">${u.is_admin?'Remove Admin':'Make Admin'}</button>
      </div></td>
    </tr>`).join("");
  }catch{}
}
async function toggleBotAccess(uid){
  const r=await fetch(API+"/admin/toggle-bot",{method:"POST",headers:{...authHdr(),"Content-Type":"application/json"},body:JSON.stringify({user_id:uid})});
  if(r.ok){toast("Bot access updated.","ok");loadAdminUsers()}else toast("Failed.","err")
}
async function toggleBan(uid){
  const reason=prompt("Reason for ban/unban (optional):")||"";
  const r=await fetch(API+"/admin/toggle-ban",{method:"POST",headers:{...authHdr(),"Content-Type":"application/json"},body:JSON.stringify({user_id:uid,reason})});
  if(r.ok){toast("Ban status updated.","ok");loadAdminUsers()}else toast("Failed.","err")
}
async function toggleAdmin(uid){
  if(!confirm("Change admin status for this user?"))return;
  const r=await fetch(API+"/admin/toggle-admin",{method:"POST",headers:{...authHdr(),"Content-Type":"application/json"},body:JSON.stringify({user_id:uid})});
  if(r.ok){toast("Admin status updated.","ok");loadAdminUsers()}else toast("Failed.","err")
}
async function loadAdminActivity(){
  try{
    const r=await fetch(API+"/admin/activity",{headers:authHdr()});
    if(!r.ok)return;
    const d=await r.json();
    const body=document.getElementById("admActBody");
    if(d.length===0){body.innerHTML='<tr><td colspan="5" class="empty">No activity logged.</td></tr>';return}
    body.innerHTML=d.map(a=>`<tr><td>${esc(a.email||"—")}</td><td>${esc(a.action)}</td><td style="font-size:13px">${esc(a.details||"")}</td><td style="font-size:12px">${esc(a.ip_address||"")}</td><td>${timeAgo(a.timestamp)}</td></tr>`).join("");
  }catch{}
}
async function loadFeatures(){
  try{
    const r=await fetch(API+"/admin/features",{headers:authHdr()});
    if(!r.ok)return;
    const d=await r.json();
    const list=document.getElementById("featList");
    const labels={
      feature_passport_maker:"Passport Photo Maker",feature_photo_editor:"Photo Editor",
      feature_background_removal:"Background Removal",feature_filters:"Filters & Presets",
      feature_pdf_export:"PDF Export",feature_custom_dimensions:"Custom Dimensions",
      feature_batch_printing:"Batch Printing"};
    list.innerHTML=Object.entries(d).map(([k,v])=>{
      const lbl=labels[k]||k;const on=v==="1";
      return `<div style="display:flex;align-items:center;justify-content:space-between;padding:14px 0;border-bottom:1px solid var(--line)"><div><div style="font-weight:600;font-size:14px">${lbl}</div><div style="font-size:12px;color:var(--mut)">${k}</div></div><label class="toggle"><input type="checkbox" data-k="${k}" ${on?"checked":""}><span class="track"></span><span class="thumb"></span></label></div>`;
    }).join("");
  }catch{}
}
async function saveFeatures(){
  const feats={};
  document.querySelectorAll("#featList input[type=checkbox]").forEach(c=>feats[c.dataset.k]=c.checked?"1":"0");
  try{
    const r=await fetch(API+"/admin/features",{method:"PUT",headers:{...authHdr(),"Content-Type":"application/json"},body:JSON.stringify(feats)});
    if(r.ok)toast("Features saved.","ok");else toast("Failed.","err");
  }catch{toast("Network error.","err")}
}
async function loadSystemSettings(){
  try{
    const r=await fetch(API+"/admin/settings",{headers:authHdr()});
    if(!r.ok)return;
    const d=await r.json();
    document.getElementById("setSiteName").value=d.site_name||"";
    document.getElementById("setMaxUpload").value=d.max_upload_mb||25;
    document.getElementById("setRegOpen").checked=d.registration_open==="1";
    document.getElementById("setMaint").checked=d.maintenance_mode==="1";
    document.getElementById("setMaintMsg").value=d.maintenance_message||"";
  }catch{}
}
async function saveSystemSettings(){
  const data={
    site_name:document.getElementById("setSiteName").value,
    max_upload_mb:document.getElementById("setMaxUpload").value,
    registration_open:document.getElementById("setRegOpen").checked?"1":"0",
    maintenance_mode:document.getElementById("setMaint").checked?"1":"0",
    maintenance_message:document.getElementById("setMaintMsg").value,
  };
  try{
    const r=await fetch(API+"/admin/settings",{method:"PUT",headers:{...authHdr(),"Content-Type":"application/json"},body:JSON.stringify(data)});
    if(r.ok){toast("System settings saved.","ok");checkMaintenance()}else toast("Failed.","err");
  }catch{toast("Network error.","err")}
}

// ===== Modal =====
function showModal(html){document.getElementById("modalBox").innerHTML=html;document.getElementById("modalBg").classList.add("show")}
function closeModal(){document.getElementById("modalBg").classList.remove("show")}

// ===== Utils =====
function timeAgo(ts){
  if(!ts)return "—";
  const d=Date.now()/1000-ts;
  if(d<60)return "just now";
  if(d<3600)return Math.floor(d/60)+"m ago";
  if(d<86400)return Math.floor(d/3600)+"h ago";
  if(d<604800)return Math.floor(d/86400)+"d ago";
  return new Date(ts*1000).toLocaleDateString();
}

// ===== Init =====
if(TOKEN)initApp();
</script>
</body>
</html>
"""


# --------------------------------------------------------------------------- #
# Web server middleware & helpers
# --------------------------------------------------------------------------- #

def _client_ip(request: web.Request) -> str:
    fwd = request.headers.get("X-Forwarded-For", "")
    if fwd:
        return fwd.split(",")[0].strip()[:100]
    return request.remote or ""


def _get_session_user(request: web.Request):
    """Return user row for the Bearer token in the request, or None."""
    auth = request.headers.get("Authorization", "")
    if not auth.startswith("Bearer "):
        return None
    token = auth[7:].strip()
    if not token:
        return None
    sess = db_get_session(token)
    if sess is None:
        return None
    user = db_get_user_by_id(sess["user_id"])
    return user


def _require_user(request: web.Request):
    user = _get_session_user(request)
    if user is None:
        return None, web.json_response({"error": "Not authenticated."}, status=401)
    if user["is_banned"]:
        return None, web.json_response({"error": "Your account has been banned."}, status=403)
    return user, None


def _require_admin(request: web.Request):
    user, err = _require_user(request)
    if err is not None:
        return None, err
    if not user["is_admin"]:
        return None, web.json_response({"error": "Admin access required."}, status=403)
    return user, None


def _require_feature(key: str):
    """Return a decorator-style check; used inline below."""

    def check():
        return db_get_setting(key, "1") == "1"

    return check


def _json_error(msg: str, status: int = 400) -> web.Response:
    return web.json_response({"error": msg}, status=status)


def _user_dict(u) -> dict:
    return {
        "id": u["id"],
        "email": u["email"],
        "display_name": u["display_name"] or "",
        "is_admin": u["is_admin"],
        "is_active": u["is_active"],
        "has_bot_access": u["has_bot_access"],
        "is_banned": u["is_banned"],
        "created_at": u["created_at"],
        "last_login": u["last_login"],
    }


def _store_uploaded_image(data: bytes, uid: int) -> str:
    """Save an uploaded image under a per-user session directory and return a
    relative token used to refer back to it via /api/editor/image/<token>."""
    # Validate
    load_image(data).close()
    d = user_dir(f"web_{uid}")
    token = secrets.token_urlsafe(16)
    # Detect format from content
    ext = "jpg"
    try:
        with Image.open(io.BytesIO(data)) as im:
            fmt = (im.format or "").lower()
            if fmt in ("png", "webp", "bmp", "tiff"):
                ext = fmt
    except Exception:
        pass
    path = d / f"{token}.{ext}"
    path.write_bytes(data)
    return token


def _resolve_image_token(token: str, uid: int) -> Path:
    """Resolve a token back to a file path; verify ownership."""
    if not token or "/" in token or ".." in token:
        raise ValueError("Invalid image token.")
    d = user_dir(f"web_{uid}")
    # Find a file matching the token prefix
    for p in d.iterdir():
        if p.is_file() and p.name.startswith(token):
            try:
                p.resolve().relative_to(TMP_ROOT.resolve())
            except ValueError:
                continue
            return p
    raise ValueError("Image not found.")


# In-memory index of editor preview URLs -> (uid, token)
# Used so /api/editor/process can accept the preview URL or a raw token.
def _url_to_token(url: str) -> str:
    if not url:
        return ""
    if url.startswith("/api/editor/image/"):
        return url.rsplit("/", 1)[-1]
    # fallback: assume it's already a token
    return url


# --------------------------------------------------------------------------- #
# Auth endpoints
# --------------------------------------------------------------------------- #

async def http_auth_register(request: web.Request) -> web.Response:
    try:
        body = await request.json()
    except Exception:
        return _json_error("Invalid request body.", 400)
    email = (body.get("email") or "").strip().lower()
    password = (body.get("password") or "").strip()
    display_name = (body.get("display_name") or "").strip()[:80]
    if not EMAIL_RE.match(email or ""):
        return _json_error("Please enter a valid email address.", 400)
    if len(password) < 8:
        return _json_error("Password must be at least 8 characters.", 400)
    if db_get_setting("registration_open", "1") != "1":
        return _json_error("Registration is currently closed.", 403)
    uid = db_create_user(email, password, display_name)
    if uid is None:
        return _json_error("An account with this email already exists.", 409)
    db_log_activity(uid, "register", ip=_client_ip(request))
    token = db_create_session(uid, _client_ip(request), request.headers.get("User-Agent", ""))
    user = db_get_user_by_id(uid)
    return web.json_response({"token": token, "user": _user_dict(user)})


async def http_auth_login(request: web.Request) -> web.Response:
    try:
        body = await request.json()
    except Exception:
        return _json_error("Invalid request body.", 400)
    email = (body.get("email") or "").strip().lower()
    password = (body.get("password") or "").strip()
    user = db_get_user_by_email(email)
    if user is None or not _verify_password(password, user["password_salt"], user["password_hash"]):
        return _json_error("Invalid email or password.", 401)
    if user["is_banned"]:
        return _json_error("Your account has been banned. Contact support.", 403)
    token = db_create_session(user["id"], _client_ip(request), request.headers.get("User-Agent", ""))
    db_log_activity(user["id"], "login", ip=_client_ip(request))
    return web.json_response({"token": token, "user": _user_dict(user)})


async def http_auth_me(request: web.Request) -> web.Response:
    user, err = _require_user(request)
    if err is not None:
        return err
    return web.json_response(_user_dict(user))


async def http_auth_logout(request: web.Request) -> web.Response:
    auth = request.headers.get("Authorization", "")
    if auth.startswith("Bearer "):
        db_delete_session(auth[7:].strip())
    return web.json_response({"ok": True})


# --------------------------------------------------------------------------- #
# Account endpoints
# --------------------------------------------------------------------------- #

async def http_account_update(request: web.Request) -> web.Response:
    user, err = _require_user(request)
    if err is not None:
        return err
    try:
        body = await request.json()
    except Exception:
        return _json_error("Invalid request body.", 400)
    name = (body.get("display_name") or "").strip()[:80]
    db_update_user(user["id"], display_name=name)
    db_log_activity(user["id"], "update_profile", ip=_client_ip(request))
    return web.json_response({"ok": True, "user": _user_dict(db_get_user_by_id(user["id"]))})


async def http_account_password(request: web.Request) -> web.Response:
    user, err = _require_user(request)
    if err is not None:
        return err
    try:
        body = await request.json()
    except Exception:
        return _json_error("Invalid request body.", 400)
    cur = body.get("current_password") or ""
    new = body.get("new_password") or ""
    if not _verify_password(cur, user["password_salt"], user["password_hash"]):
        return _json_error("Current password is incorrect.", 400)
    if len(new) < 8:
        return _json_error("New password must be at least 8 characters.", 400)
    salt = secrets.token_hex(16)
    phash = _hash_password(new, salt)
    conn = _db()
    try:
        conn.execute("UPDATE users SET password_hash=?, password_salt=? WHERE id=?",
                     (phash, salt, user["id"]))
        conn.commit()
    finally:
        conn.close()
    db_log_activity(user["id"], "change_password", ip=_client_ip(request))
    return web.json_response({"ok": True})


async def http_my_activity(request: web.Request) -> web.Response:
    user, err = _require_user(request)
    if err is not None:
        return err
    conn = _db()
    try:
        rows = conn.execute(
            "SELECT action, file_count, timestamp FROM usage_stats WHERE user_id=? "
            "ORDER BY timestamp DESC LIMIT 100", (user["id"],)).fetchall()
    finally:
        conn.close()
    return web.json_response([dict(r) for r in rows])


async def http_stats(request: web.Request) -> web.Response:
    user, err = _require_user(request)
    if err is not None:
        return err
    conn = _db()
    try:
        rows = conn.execute(
            "SELECT action, COUNT(*) as c FROM usage_stats WHERE user_id=? GROUP BY action",
            (user["id"],)).fetchall()
    finally:
        conn.close()
    counts = {r["action"]: r["c"] for r in rows}
    return web.json_response({
        "edits": counts.get("editor", 0),
        "passports": counts.get("passport", 0),
        "exports": counts.get("export", 0),
        "member_since": datetime.fromtimestamp(user["created_at"]).strftime("%b %Y"),
    })


# --------------------------------------------------------------------------- #
# Public settings
# --------------------------------------------------------------------------- #

async def http_settings_public(request: web.Request) -> web.Response:
    return web.json_response({
        "maintenance_mode": db_get_setting("maintenance_mode", "0"),
        "maintenance_message": db_get_setting("maintenance_message", ""),
        "site_name": db_get_setting("site_name", "Photo Studio Pro"),
        "registration_open": db_get_setting("registration_open", "1"),
    })


# --------------------------------------------------------------------------- #
# Editor endpoints
# --------------------------------------------------------------------------- #

async def http_editor_upload(request: web.Request) -> web.Response:
    user, err = _require_user(request)
    if err is not None:
        return err
    if db_get_setting("feature_photo_editor", "1") != "1":
        return _json_error("Photo editor is currently disabled.", 403)
    try:
        reader = await request.multipart()
        data = None
        async for part in reader:
            if part.name == "image":
                data = await part.read(decode=False)
                break
        if not data:
            return _json_error("No image provided.", 400)
        if len(data) > MAX_IMAGE_BYTES:
            return _json_error("File too large (max 25 MB).", 400)
        try:
            img = load_image(data)
            w, h = img.size
            img.close()
        except ValueError as exc:
            return _json_error(str(exc), 400)
        except Exception:
            return _json_error("Invalid image file.", 400)
        token = _store_uploaded_image(data, user["id"])
        db_log_usage(user["id"], "editor")
        return web.json_response({
            "url": f"/api/editor/image/{token}",
            "width": w,
            "height": h,
        })
    except Exception:
        log.exception("editor upload failed")
        return _json_error("Upload failed.", 500)


async def http_editor_image(request: web.Request) -> web.Response:
    user, err = _require_user(request)
    if err is not None:
        return err
    token = request.match_info.get("token", "")
    try:
        path = _resolve_image_token(token, user["id"])
    except ValueError:
        return _json_error("Image not found.", 404)
    data = path.read_bytes()
    ct = "image/jpeg"
    if path.suffix.lower() == ".png":
        ct = "image/png"
    elif path.suffix.lower() == ".webp":
        ct = "image/webp"
    elif path.suffix.lower() == ".bmp":
        ct = "image/bmp"
    return web.Response(body=data, content_type=ct,
                        headers={"Cache-Control": "private, max-age=3600"})


def _load_token_image(url: str, uid: int) -> Image.Image:
    token = _url_to_token(url)
    path = _resolve_image_token(token, uid)
    return load_image(path.read_bytes())


async def http_editor_process(request: web.Request) -> web.Response:
    user, err = _require_user(request)
    if err is not None:
        return err
    if db_get_setting("feature_photo_editor", "1") != "1":
        return _json_error("Photo editor is currently disabled.", 403)
    try:
        body = await request.json()
    except Exception:
        return _json_error("Invalid request body.", 400)
    image_url = body.get("image")
    ops = body.get("ops") or []
    if not image_url or not isinstance(ops, list):
        return _json_error("Image and operations are required.", 400)
    if len(ops) > 50:
        return _json_error("Too many operations in one request.", 400)
    try:
        img = _load_token_image(image_url, user["id"])
    except ValueError:
        return _json_error("Image not found. Please re-upload.", 404)
    except Exception:
        return _json_error("Could not load the image.", 400)

    # Limit heavy operations for safety
    has_bg = any(op.get("op") in ("background", "remove_bg") for op in ops)
    loop = asyncio.get_running_loop()

    def _run():
        return apply_operations(img, ops)

    try:
        async with _generation_semaphore:
            result = await asyncio.wait_for(
                loop.run_in_executor(None, _run),
                timeout=GENERATION_TIMEOUT)
    except asyncio.TimeoutError:
        return _json_error("Processing took too long. Try fewer operations.", 504)
    except ValueError as exc:
        return _json_error(str(exc), 400)
    except Exception:
        log.exception("editor process failed")
        return _json_error("Processing failed.", 500)

    # Save result and return new URL
    token = secrets.token_urlsafe(16)
    d = user_dir(f"web_{user['id']}")
    out_path = d / f"{token}.png"
    # Determine mode for saving
    save_img = result
    if result.mode == "RGBA":
        save_img = result
    else:
        save_img = result.convert("RGB")
    buf = io.BytesIO()
    save_img.save(buf, "PNG", optimize=True)
    out_path.write_bytes(buf.getvalue())
    db_log_usage(user["id"], "editor")
    return web.json_response({"url": f"/api/editor/image/{token}",
                              "width": result.width,
                              "height": result.height})


async def http_editor_filters(request: web.Request) -> web.Response:
    user, err = _require_user(request)
    if err is not None:
        return err
    if db_get_setting("feature_filters", "1") != "1":
        return _json_error("Filters are currently disabled.", 403)
    try:
        body = await request.json()
    except Exception:
        return _json_error("Invalid request body.", 400)
    image_url = body.get("image")
    if not image_url:
        return _json_error("Image is required.", 400)
    try:
        img = _load_token_image(image_url, user["id"])
    except ValueError:
        return _json_error("Image not found.", 404)
    except Exception:
        return _json_error("Could not load the image.", 400)

    # Make small previews for each filter
    preview = make_preview(img)
    filter_names = ["original", "auto_enhance", "vivid", "warm", "cool",
                    "vintage", "sepia", "bw", "noir", "fade", "dramatic",
                    "soft_glow", "matte", "chrome"]
    previews = {}
    loop = asyncio.get_running_loop()

    def _gen():
        out = {}
        for f in filter_names:
            try:
                filtered = apply_filter(preview, f)
                buf = io.BytesIO()
                filtered.convert("RGB").save(buf, "JPEG", quality=80)
                out[f] = "data:image/jpeg;base64," + binascii.b2a_base64(
                    buf.getvalue()).decode().strip()
            except Exception:
                out[f] = ""
        return out

    try:
        previews = await loop.run_in_executor(None, _gen)
    except Exception:
        log.exception("filter preview failed")
        return _json_error("Failed to generate filter previews.", 500)
    return web.json_response({"previews": previews})


async def http_editor_export(request: web.Request) -> web.Response:
    user, err = _require_user(request)
    if err is not None:
        return err
    try:
        body = await request.json()
    except Exception:
        return _json_error("Invalid request body.", 400)
    image_url = body.get("image")
    fmt = (body.get("format") or "jpg").lower()
    quality = int(body.get("quality", 95))
    if not image_url:
        return _json_error("Image is required.", 400)
    if fmt not in ("jpg", "jpeg", "png", "webp", "bmp"):
        return _json_error("Unsupported format.", 400)
    try:
        img = _load_token_image(image_url, user["id"])
    except ValueError:
        return _json_error("Image not found.", 404)
    except Exception:
        return _json_error("Could not load the image.", 400)

    loop = asyncio.get_running_loop()

    def _run():
        return export_image(img, fmt, quality)

    try:
        data = await loop.run_in_executor(None, _run)
    except Exception:
        log.exception("export failed")
        return _json_error("Export failed.", 500)

    db_log_usage(user["id"], "export")
    ext = "jpg" if fmt in ("jpg", "jpeg") else fmt
    fname = f"export_{int(time.time())}.{ext}"
    ct = {"jpg": "image/jpeg", "jpeg": "image/jpeg", "png": "image/png",
          "webp": "image/webp", "bmp": "image/bmp"}.get(fmt, "application/octet-stream")
    return web.Response(body=data, content_type=ct,
                        headers={"Content-Disposition": f'attachment; filename="{fname}"'})


# --------------------------------------------------------------------------- #
# Passport maker endpoint (web)
# --------------------------------------------------------------------------- #

API_PAGE_DIMS = dict(PAGE_SIZES)
API_PS_DIMS = {"25x35": (25.0, 35.0), "30x40": (30.0, 40.0),
               "35x45": (35.0, 45.0), "2x2": (50.8, 50.8)}
API_BG = {k: rgb_to_hex(v[1]) for k, v in BG_PRESETS.items()}


async def http_passport_generate(request: web.Request) -> web.Response:
    user, err = _require_user(request)
    if err is not None:
        return err
    if db_get_setting("feature_passport_maker", "1") != "1":
        return _json_error("Passport maker is currently disabled.", 403)
    try:
        body = await request.json()
    except Exception:
        return _json_error("Invalid request body.", 400)
    image_url = body.get("image")
    if not image_url:
        return _json_error("Image is required.", 400)
    page_key = str(body.get("page", "A4"))
    if page_key in API_PAGE_DIMS:
        page_w, page_h = API_PAGE_DIMS[page_key]
    elif page_key == "custom":
        page_w = parse_float(str(body.get("page_w", "")))
        page_h = parse_float(str(body.get("page_h", "")))
        if (page_w is None or page_h is None or
                not (MM_MIN_PAGE <= page_w <= MM_MAX_PAGE) or
                not (MM_MIN_PAGE <= page_h <= MM_MAX_PAGE)):
            return _json_error("Invalid custom page size.", 400)
    else:
        return _json_error("Invalid page size.", 400)

    bg_key = str(body.get("bg", "skip"))
    if bg_key == "skip":
        bg_rgb = None
    elif bg_key in API_BG:
        bg_rgb = parse_hex_color(API_BG[bg_key])
    elif bg_key == "custom":
        bg_rgb = parse_hex_color(str(body.get("hex", "")))
        if bg_rgb is None:
            return _json_error("Invalid HEX background color.", 400)
    else:
        return _json_error("Invalid background option.", 400)

    ps_key = str(body.get("ps", "35x45"))
    if ps_key in API_PS_DIMS:
        ps_w, ps_h = API_PS_DIMS[ps_key]
    elif ps_key == "custom":
        ps_w = parse_float(str(body.get("ps_w", "")))
        ps_h = parse_float(str(body.get("ps_h", "")))
        if (ps_w is None or ps_h is None or
                not (MM_MIN_PHOTO <= ps_w <= MM_MAX_PHOTO) or
                not (MM_MIN_PHOTO <= ps_h <= MM_MAX_PHOTO)):
            return _json_error("Invalid custom photo size.", 400)
    else:
        return _json_error("Invalid photo size.", 400)

    try:
        qty = int(body.get("qty", 8))
    except (TypeError, ValueError):
        return _json_error("Invalid quantity.", 400)
    if not (1 <= qty <= MAX_QTY):
        return _json_error("Quantity must be 1–500.", 400)

    fmt = str(body.get("fmt", "pdf"))
    if fmt not in ("pdf", "jpg", "png", "pdf_jpg", "pdf_png"):
        return _json_error("Invalid output format.", 400)

    try:
        img = _load_token_image(image_url, user["id"])
        # Re-encode to bytes for generate_files
        buf = io.BytesIO()
        img.convert("RGB").save(buf, "JPEG", quality=98)
        image_bytes = buf.getvalue()
    except ValueError:
        return _json_error("Image not found.", 404)
    except Exception:
        return _json_error("Could not load the image.", 400)

    loop = asyncio.get_running_loop()
    try:
        async with _generation_semaphore:
            files, pages, note = await asyncio.wait_for(
                loop.run_in_executor(
                    None, generate_files, image_bytes, page_w, page_h,
                    bg_rgb, ps_w, ps_h, qty, fmt),
                timeout=GENERATION_TIMEOUT)
    except asyncio.TimeoutError:
        return _json_error("Processing took too long. Try again or skip the background.",
                           504)
    except ValueError as exc:
        return _json_error(str(exc), 400)
    except Exception:
        log.exception("passport generate failed")
        return _json_error("Generation failed.", 500)

    db_log_usage(user["id"], "passport", len(files))

    # If single file, return it directly; else zip
    if len(files) == 1:
        fname, blob = files[0]
        ct = "application/pdf" if fname.endswith(".pdf") else (
            "image/jpeg" if fname.endswith(".jpg") else "image/png")
        return web.Response(body=blob, content_type=ct,
                            headers={"Content-Disposition": f'attachment; filename="{fname}"'})
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
        for fname, blob in files:
            zf.writestr(fname, blob)
    return web.Response(body=buf.getvalue(), content_type="application/zip",
                        headers={"Content-Disposition": 'attachment; filename="passport_photos.zip"'})


# --------------------------------------------------------------------------- #
# Admin endpoints
# --------------------------------------------------------------------------- #

async def http_admin_users(request: web.Request) -> web.Response:
    user, err = _require_admin(request)
    if err is not None:
        return err
    users = db_list_users()
    return web.json_response({
        "users": [_user_dict(u) for u in users],
        "active_sessions": db_active_session_count(),
    })


async def http_admin_toggle_bot(request: web.Request) -> web.Response:
    user, err = _require_admin(request)
    if err is not None:
        return err
    try:
        body = await request.json()
    except Exception:
        return _json_error("Invalid request.", 400)
    target_id = int(body.get("user_id", 0))
    target = db_get_user_by_id(target_id)
    if target is None:
        return _json_error("User not found.", 404)
    db_update_user(target_id, has_bot_access=0 if target["has_bot_access"] else 1)
    db_log_activity(user["id"], "toggle_bot_access",
                    details=f"user={target_id}", ip=_client_ip(request))
    return web.json_response({"ok": True})


async def http_admin_toggle_ban(request: web.Request) -> web.Response:
    user, err = _require_admin(request)
    if err is not None:
        return err
    try:
        body = await request.json()
    except Exception:
        return _json_error("Invalid request.", 400)
    target_id = int(body.get("user_id", 0))
    reason = (body.get("reason") or "")[:200]
    target = db_get_user_by_id(target_id)
    if target is None:
        return _json_error("User not found.", 404)
    if target["is_admin"]:
        return _json_error("Cannot ban an admin.", 400)
    new_ban = 0 if target["is_banned"] else 1
    db_update_user(target_id, is_banned=new_ban, banned_reason=reason,
                   is_active=0 if new_ban else 1)
    db_log_activity(user["id"], "toggle_ban",
                    details=f"user={target_id} reason={reason}", ip=_client_ip(request))
    return web.json_response({"ok": True})


async def http_admin_toggle_admin(request: web.Request) -> web.Response:
    user, err = _require_admin(request)
    if err is not None:
        return err
    try:
        body = await request.json()
    except Exception:
        return _json_error("Invalid request.", 400)
    target_id = int(body.get("user_id", 0))
    target = db_get_user_by_id(target_id)
    if target is None:
        return _json_error("User not found.", 404)
    if target["id"] == user["id"]:
        return _json_error("Cannot change your own admin status.", 400)
    db_update_user(target_id, is_admin=0 if target["is_admin"] else 1)
    db_log_activity(user["id"], "toggle_admin",
                    details=f"user={target_id}", ip=_client_ip(request))
    return web.json_response({"ok": True})


async def http_admin_activity(request: web.Request) -> web.Response:
    user, err = _require_admin(request)
    if err is not None:
        return err
    rows = db_recent_activity(200)
    return web.json_response([dict(r) for r in rows])


async def http_admin_features_get(request: web.Request) -> web.Response:
    user, err = _require_admin(request)
    if err is not None:
        return err
    settings = db_get_all_settings()
    feats = {k: v for k, v in settings.items() if k.startswith("feature_")}
    return web.json_response(feats)


async def http_admin_features_put(request: web.Request) -> web.Response:
    user, err = _require_admin(request)
    if err is not None:
        return err
    try:
        body = await request.json()
    except Exception:
        return _json_error("Invalid request.", 400)
    for k, v in body.items():
        if k.startswith("feature_"):
            db_set_setting(k, "1" if v in (True, "1", 1) else "0")
    db_log_activity(user["id"], "update_features", ip=_client_ip(request))
    return web.json_response({"ok": True})


async def http_admin_settings_get(request: web.Request) -> web.Response:
    user, err = _require_admin(request)
    if err is not None:
        return err
    s = db_get_all_settings()
    return web.json_response({
        "site_name": s.get("site_name", ""),
        "max_upload_mb": s.get("max_upload_mb", "25"),
        "registration_open": s.get("registration_open", "1"),
        "maintenance_mode": s.get("maintenance_mode", "0"),
        "maintenance_message": s.get("maintenance_message", ""),
    })


async def http_admin_settings_put(request: web.Request) -> web.Response:
    user, err = _require_admin(request)
    if err is not None:
        return err
    try:
        body = await request.json()
    except Exception:
        return _json_error("Invalid request.", 400)
    if "site_name" in body:
        db_set_setting("site_name", str(body["site_name"])[:100])
    if "max_upload_mb" in body:
        try:
            mb = int(body["max_upload_mb"])
            if 1 <= mb <= 100:
                db_set_setting("max_upload_mb", str(mb))
        except (TypeError, ValueError):
            pass
    if "registration_open" in body:
        db_set_setting("registration_open", "1" if body["registration_open"] in (True, "1", 1) else "0")
    if "maintenance_mode" in body:
        db_set_setting("maintenance_mode", "1" if body["maintenance_mode"] in (True, "1", 1) else "0")
    if "maintenance_message" in body:
        db_set_setting("maintenance_message", str(body["maintenance_message"])[:500])
    db_log_activity(user["id"], "update_system_settings", ip=_client_ip(request))
    return web.json_response({"ok": True})


# --------------------------------------------------------------------------- #
# Mini App API (preserved for Telegram users)
# --------------------------------------------------------------------------- #

async def http_mini_generate(request: web.Request) -> web.Response:
    try:
        reader = await request.multipart()
        photo_bytes = None
        payload = None
        init_data = ""
        async for part in reader:
            if part.name == "initData":
                init_data = (await part.read(decode=False)).decode("utf-8", "ignore")
            elif part.name == "photo":
                photo_bytes = await part.read(decode=False)
            elif part.name == "payload":
                try:
                    payload = json.loads((await part.read(decode=False)).decode("utf-8"))
                except Exception:
                    payload = None
        if not photo_bytes or not isinstance(payload, dict):
            return _json_error("Photo and settings are required.", 400)

        page_key = str(payload.get("page", ""))
        if page_key in API_PAGE_DIMS:
            page_w, page_h = API_PAGE_DIMS[page_key]
        elif page_key == "custom":
            page_w = parse_float(str(payload.get("page_w", "")))
            page_h = parse_float(str(payload.get("page_h", "")))
            if (page_w is None or page_h is None or
                    not (MM_MIN_PAGE <= page_w <= MM_MAX_PAGE) or
                    not (MM_MIN_PAGE <= page_h <= MM_MAX_PAGE)):
                return _json_error("Invalid custom page size.", 400)
        else:
            return _json_error("Invalid page size.", 400)

        bg_key = str(payload.get("bg", "skip"))
        if bg_key == "skip":
            bg_rgb = None
        elif bg_key in API_BG:
            bg_rgb = parse_hex_color(API_BG[bg_key])
        elif bg_key == "custom":
            bg_rgb = parse_hex_color(str(payload.get("hex", "")))
            if bg_rgb is None:
                return _json_error("Invalid HEX background color.", 400)
        else:
            return _json_error("Invalid background option.", 400)

        ps_key = str(payload.get("ps", ""))
        if ps_key in API_PS_DIMS:
            ps_w, ps_h = API_PS_DIMS[ps_key]
        elif ps_key == "custom":
            ps_w = parse_float(str(payload.get("ps_w", "")))
            ps_h = parse_float(str(payload.get("ps_h", "")))
            if (ps_w is None or ps_h is None or
                    not (MM_MIN_PHOTO <= ps_w <= MM_MAX_PHOTO) or
                    not (MM_MIN_PHOTO <= ps_h <= MM_MAX_PHOTO)):
                return _json_error("Invalid custom photo size.", 400)
        else:
            return _json_error("Invalid photo size.", 400)

        try:
            qty = int(payload.get("qty"))
        except (TypeError, ValueError):
            return _json_error("Invalid quantity.", 400)
        if not (1 <= qty <= MAX_QTY):
            return _json_error("Quantity must be 1–500.", 400)

        fmt = str(payload.get("fmt", ""))
        if fmt not in ("pdf", "jpg", "png", "pdf_jpg", "pdf_png"):
            return _json_error("Invalid output format.", 400)

        try:
            image_bytes = photo_bytes
            load_image(image_bytes).close()
        except Exception:
            return _json_error("The uploaded file is not a valid image.", 400)

        loop = asyncio.get_running_loop()
        try:
            async with _generation_semaphore:
                files, pages, note = await asyncio.wait_for(
                    loop.run_in_executor(
                        None, generate_files, image_bytes, page_w, page_h,
                        bg_rgb, ps_w, ps_h, qty, fmt),
                    timeout=GENERATION_TIMEOUT)
            global _generation_count
            _generation_count += 1
        except asyncio.TimeoutError:
            return _json_error("Processing took too long.", 504)
        except ValueError as exc:
            return _json_error(str(exc), 400)

        uid = verify_init_data(init_data)
        if uid and _bot is not None:
            try:
                caption = (f"🖨 Done! {qty} photo(s), {pages} page(s), "
                           f"{ps_w:g} × {ps_h:g} mm @ {DPI} DPI.")
                if note:
                    await _bot.send_message(uid, note)
                for fname, blob in files:
                    await _bot.send_document(
                        uid, BufferedInputFile(blob, filename=fname),
                        caption=caption)
                return web.json_response({"sent": True, "files": len(files)})
            except Exception:
                log.warning("mini app: sending to chat failed; falling back",
                            exc_info=True)

        def _ctype(name):
            n = name.lower()
            if n.endswith(".pdf"):
                return "application/pdf"
            if n.endswith(".jpg") or n.endswith(".jpeg"):
                return "image/jpeg"
            if n.endswith(".png"):
                return "image/png"
            return "application/octet-stream"

        if len(files) == 1:
            fname, blob = files[0]
            return web.Response(
                body=blob,
                headers={"Content-Disposition": f'attachment; filename="{fname}"',
                         "Content-Type": _ctype(fname)})

        buf = io.BytesIO()
        with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
            for fname, blob in files:
                zf.writestr(fname, blob)
        return web.Response(
            body=buf.getvalue(),
            headers={"Content-Disposition": 'attachment; filename="passport_photos.zip"',
                     "Content-Type": "application/zip"})
    except Exception:
        log.exception("mini app generate failed")
        return _json_error("Something went wrong while generating.", 500)


# --------------------------------------------------------------------------- #
# Web server plumbing
# --------------------------------------------------------------------------- #

async def http_index(request: web.Request) -> web.Response:
    return web.Response(text=APP_HTML, content_type="text/html")


async def http_favicon(request: web.Request) -> web.Response:
    return web.Response(status=204)


async def http_info(request: web.Request) -> web.Response:
    return web.json_response({
        "service": "photo-studio-pro",
        "version": "3.0",
        "uptime_seconds": round(time.time() - _started_at, 1),
        "telegram_configured": bool(BOT_TOKEN),
        "rembg_enabled": USE_REMBG,
        "generation_concurrency": GENERATION_CONCURRENCY,
        "generations_completed": _generation_count,
        "users": db_user_count(),
        "maintenance_mode": db_get_setting("maintenance_mode", "0") == "1",
    })


async def http_health(request: web.Request) -> web.Response:
    return web.json_response({"ok": True, "service": "photo-studio-pro"})


async def start_web_server() -> web.AppRunner:
    app = web.Application(client_max_size=MAX_IMAGE_BYTES + 5 * 1024 * 1024)
    # Public
    app.router.add_get("/", http_index)
    app.router.add_get("/health", http_health)
    app.router.add_get("/healthz", http_health)
    app.router.add_get("/api/info", http_info)
    app.router.add_get("/api/settings/public", http_settings_public)
    app.router.add_get("/favicon.ico", http_favicon)
    # Auth
    app.router.add_post("/api/auth/register", http_auth_register)
    app.router.add_post("/api/auth/login", http_auth_login)
    app.router.add_get("/api/auth/me", http_auth_me)
    app.router.add_post("/api/auth/logout", http_auth_logout)
    # Account
    app.router.add_post("/api/account/update", http_account_update)
    app.router.add_post("/api/account/password", http_account_password)
    app.router.add_get("/api/my/activity", http_my_activity)
    app.router.add_get("/api/stats", http_stats)
    # Editor
    app.router.add_post("/api/editor/upload", http_editor_upload)
    app.router.add_get("/api/editor/image/{token}", http_editor_image)
    app.router.add_post("/api/editor/process", http_editor_process)
    app.router.add_post("/api/editor/filters", http_editor_filters)
    app.router.add_post("/api/editor/export", http_editor_export)
    # Passport
    app.router.add_post("/api/passport/generate", http_passport_generate)
    # Admin
    app.router.add_get("/api/admin/users", http_admin_users)
    app.router.add_post("/api/admin/toggle-bot", http_admin_toggle_bot)
    app.router.add_post("/api/admin/toggle-ban", http_admin_toggle_ban)
    app.router.add_post("/api/admin/toggle-admin", http_admin_toggle_admin)
    app.router.add_get("/api/admin/activity", http_admin_activity)
    app.router.add_get("/api/admin/features", http_admin_features_get)
    app.router.add_put("/api/admin/features", http_admin_features_put)
    app.router.add_get("/api/admin/settings", http_admin_settings_get)
    app.router.add_put("/api/admin/settings", http_admin_settings_put)
    # Telegram Mini App (preserved)
    app.router.add_post("/api/generate", http_mini_generate)
    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, "0.0.0.0", PORT)
    await site.start()
    log.info("HTTP server listening on port %s", PORT)
    return runner


# --------------------------------------------------------------------------- #
# Entrypoint
# --------------------------------------------------------------------------- #

async def main() -> None:
    init_db()
    runner = await start_web_server()
    if not BOT_TOKEN:
        log.error("BOT_TOKEN is not set; running in web-only mode. "
                  "Set BOT_TOKEN to enable Telegram polling.")
        try:
            await asyncio.Event().wait()
        finally:
            await runner.cleanup()
        return

    bot = Bot(token=BOT_TOKEN,
              default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    global _bot
    _bot = bot
    dp = Dispatcher(storage=MemoryStorage())
    dp.include_router(router)
    try:
        await bot.delete_webhook(drop_pending_updates=True)
        await asyncio.sleep(5)
        log.info("Bot started (rembg enabled: %s)", USE_REMBG)
        await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())
    finally:
        await runner.cleanup()
        await bot.session.close()


if __name__ == "__main__":
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s %(name)s: %(message)s")
    try:
        asyncio.run(main())
    except (KeyboardInterrupt, SystemExit):
        pass
