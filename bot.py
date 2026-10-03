# -*- coding: utf-8 -*-
"""
Telegram Passport Photo Printing Bot
====================================
Single-file production bot: aiogram 3.x + Pillow + numpy + optional rembg
background removal + embedded Telegram Mini App served via aiohttp.

Required environment variables:
    BOT_TOKEN   - Telegram bot token from @BotFather

Optional environment variables:
    WEBAPP_URL  - public HTTPS URL of this service (Railway domain). If set,
                  the "Open Photo Maker" Mini App button is shown.
    OWNER_ID    - numeric Telegram id of the owner (reserved, optional)
    PORT        - HTTP port for the aiohttp server (Railway provides it)
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
import shutil
import tempfile
import time
import uuid
import zipfile
from urllib.parse import parse_qsl
from pathlib import Path
import sqlite3
import secrets
import base64
from datetime import datetime, timezone
from email.utils import parseaddr

import numpy as np
from PIL import Image, ImageChops, ImageDraw, ImageFilter, ImageOps
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

# Optional advanced background removal. It is loaded lazily so Render can bind
# its HTTP port immediately instead of waiting for the ONNX model at boot.
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
            # u2netp = small model (~4 MB), safe for 512 MB Render instances
            _rembg_session = new_session("u2netp")
        except Exception:
            _rembg_session = None
        REMBG_AVAILABLE = True
    except Exception:
        logging.getLogger("passport-bot").warning(
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
def _read_port() -> int:
    raw = os.getenv("PORT", "8080").strip()
    try:
        port = int(raw)
    except ValueError:
        logging.getLogger("passport-bot").warning("Invalid PORT=%r; using 8080", raw)
        return 8080
    return port if 1 <= port <= 65535 else 8080


PORT = _read_port()

DPI = 300                      # print quality
MARGIN_MM = 10.0               # page margin (top / left / right / bottom)
SPACING_MM = 1.5               # small gap between photos (tight row layout)
BORDER_RGB = (0, 0, 0)         # black border around each photo
BORDER_MM = 0.5                # border thickness (drawn INSIDE photo size)
RMBG_MAX_SIDE = 1400           # downscale before rembg -> avoids Render OOM
# rembg (AI cut-out) is OPT-IN: set env USE_REMBG=1 only on instances with
# >= 1 GB RAM. By default a fast, memory-safe built-in method is used, so the
# bot can never hang or crash while changing the background.
USE_REMBG = os.getenv("USE_REMBG", "0").strip() in ("1", "true", "yes")
GENERATION_TIMEOUT = 150       # seconds before the bot gives up and reports
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
IMAGE_MIMES = {"image/jpeg", "image/png", "image/webp", "image/bmp", "image/tiff"}

TMP_ROOT = Path(tempfile.gettempdir()) / "passport_photo_bot"
TMP_ROOT.mkdir(parents=True, exist_ok=True)

# Protect the public Mini App endpoint from accidental overload on small Render instances.
try:
    GENERATION_CONCURRENCY = max(1, int(os.getenv("GENERATION_CONCURRENCY", "1") or "1"))
except ValueError:
    GENERATION_CONCURRENCY = 1
_generation_semaphore = asyncio.Semaphore(GENERATION_CONCURRENCY)
_started_at = time.time()
_generation_count = 0
log = logging.getLogger("passport-bot")
_bot = None  # set in main(); used by the Mini App to deliver files in chat


def verify_init_data(init_data: str):
    """Validate Telegram WebApp initData (HMAC). Returns user id or None."""
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

# --------------------------------------------------------------------------- #
# Small helpers
# --------------------------------------------------------------------------- #

def mm_to_px(mm: float, dpi: int = DPI) -> int:
    return max(1, int(round(mm / 25.4 * dpi)))


def unit_to_mm(value: float, unit: str) -> float:
    if unit == "cm":
        return value * 10.0
    if unit == "inch":
        return value * 25.4
    return value  # mm


def parse_float(text: str):
    try:
        v = float(text.strip().replace(",", "."))
        if math.isfinite(v):
            return v
    except (ValueError, AttributeError):
        pass
    return None


def parse_hex_color(text: str):
    """Return (r, g, b) for '#RRGGBB' / 'RRGGBB', else None."""
    if not text:
        return None
    t = text.strip()
    if not HEX_RE.match(t):
        return None
    t = t.lstrip("#")
    return (int(t[0:2], 16), int(t[2:4], 16), int(t[4:6], 16))


def rgb_to_hex(rgb) -> str:
    return "#{:02X}{:02X}{:02X}".format(*rgb)


def user_dir(user_id: int) -> Path:
    d = TMP_ROOT / str(user_id)
    d.mkdir(parents=True, exist_ok=True)
    return d


def cleanup_user(user_id: int) -> None:
    try:
        shutil.rmtree(TMP_ROOT / str(user_id), ignore_errors=True)
    except Exception:
        log.warning("cleanup failed for user %s", user_id)


def compute_grid(page_w_mm, page_h_mm, pw_mm, ph_mm):
    """Dynamic layout: how many columns/rows of pw x ph photos fit inside the
    printable area. Returns (cols, rows) or None if even one photo can't fit."""
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
# Image processing (shared by Telegram bot AND Mini App API)
# --------------------------------------------------------------------------- #

def load_image(data: bytes) -> Image.Image:
    if len(data) > MAX_IMAGE_BYTES:
        raise ValueError("Image file is too large (max 25 MB).")
    img = Image.open(io.BytesIO(data))
    img = ImageOps.exif_transpose(img)
    img.load()
    if max(img.size) > MAX_IMAGE_SIDE:
        raise ValueError("Image dimensions are too large.")
    if img.mode in ("RGBA", "LA", "P", "CMYK", "I;16", "I", "F", "L"):
        img = img.convert("RGB")
    elif img.mode != "RGB":
        img = img.convert("RGB")
    return img


def _bg_mask_from_border(small: Image.Image):
    """Return (dist, bg_mask) for a small RGB image.
    bg_mask = pixels similar to the border colour AND connected to the border
    (so a similar colour inside the person is NOT removed)."""
    arr = np.asarray(small).astype(np.float32)
    h, w, _ = arr.shape
    b = max(3, min(h, w) // 50)
    border = np.concatenate([
        arr[:b, :, :].reshape(-1, 3),
        arr[:, :b, :].reshape(-1, 3),
        arr[:, -b:, :].reshape(-1, 3),
    ])  # top + left + right edges (bottom usually holds the shoulders)
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
        # scipy-free flood fill by repeated dilation inside the candidate mask
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
    """Memory-safe background replacement (no AI model). Returns (img, ok)."""
    k = min(1.0, 1100 / max(img.size))
    small = img if k >= 1 else img.resize(
        (max(1, int(img.width * k)), max(1, int(img.height * k))), Image.BILINEAR)
    dist, tol, bg = _bg_mask_from_border(small)
    frac = float(bg.mean())
    if frac < 0.06 or frac > 0.85:
        return img, False  # background not plain enough -> do not damage photo
    # Safety: the lower part of a passport photo is the person's clothes.
    # If most of it was classified as "background" (e.g. white shirt on white
    # wall), the cut-out is unreliable -> keep the original instead of
    # painting the clothes with the new colour.
    if float(bg[int(bg.shape[0] * 0.8):, :].mean()) > 0.45:
        return img, False

    bgimg = Image.fromarray((bg * 255).astype(np.uint8), "L")
    # soft edge band: pixels just outside the bg region that still look
    # partly like the old background get partial transparency (kills halos)
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
    """Replace the photo background with rgb. Never raises.
    Returns (image, note) where note is a warning string or None."""
    if USE_REMBG and _load_rembg():
        try:
            return _rembg_replace(img, rgb), None
        except Exception:
            log.warning("rembg failed; using built-in method", exc_info=True)
    try:
        out, ok = _builtin_bg_replace(img, rgb)
        if ok:
            return out, None
        return img, ("⚠️ Background could not be detected automatically "
                     "(it is not a plain colour). Original background kept.")
    except Exception:
        log.warning("built-in background replace failed", exc_info=True)
        return img, "⚠️ Background change failed. Original background kept."


def crop_to_ratio(img: Image.Image, ratio: float) -> Image.Image:
    """Aspect-ratio-preserving intelligent crop (never stretches).
    Keeps the upper part of the frame so the head/face is not cut off."""
    w, h = img.size
    cur = w / h
    if abs(cur - ratio) < 1e-3:
        return img
    if cur > ratio:  # too wide -> crop sides, centered
        new_w = int(round(h * ratio))
        x0 = (w - new_w) // 2
        return img.crop((x0, 0, x0 + new_w, h))
    # too tall -> crop from bottom with an upper bias to protect the head
    new_h = int(round(w / ratio))
    y0 = int(round((h - new_h) * 0.30))
    y0 = max(0, min(h - new_h, y0))
    return img.crop((0, y0, w, y0 + new_h))


def build_passport_photo(img: Image.Image, bg_rgb, pw_mm, ph_mm):
    """Returns (photo, note)."""
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
    """Render one print sheet: clean white page, dynamically computed grid,
    centered, evenly spaced, thin consistent borders. Never overflows."""
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

    # Page is exactly the selected size; photos start at the TOP-LEFT.
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
                   bg_rgb, pw_mm: float, ph_mm: float,
                   qty: int, fmt: str):
    """Full pipeline shared by bot & Mini App.
    Returns (list_of_(filename, bytes), num_pages). Raises ValueError on
    invalid input that can't be produced."""
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
        sheets.append(build_sheet(passport, page_w_mm, page_h_mm,
                                  pw_mm, ph_mm, take))
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
# FSM states
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

# --------------------------------------------------------------------------- #
# Keyboards
# --------------------------------------------------------------------------- #

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

# --------------------------------------------------------------------------- #
# Bot handlers
# --------------------------------------------------------------------------- #

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
    # Path-traversal guard: only files inside our tmp root are acceptable.
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
    bg = data.get("bg")
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


async def after_setting_selected(cq_or_msg, state: FSMContext,
                                 next_step: str):
    """If the user came from ✏️ Change Settings, jump straight back to the
    summary; otherwise continue the normal forward flow."""
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


# ----- /start, /help, /cancel -------------------------------------------- #

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
    cleanup_user(message.from_user.id)
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
    cleanup_user(cq.from_user.id)
    await safe_edit(cq, "❌ Cancelled. Temporary files removed.")
    await cq.message.answer(WELCOME, reply_markup=kb_main_menu())
    await cq.answer()


# ----- photo intake ------------------------------------------------------- #

async def _intake(message: Message, state: FSMContext, file_id: str,
                  fname: str):
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
            img = load_image(data)  # validate early, keep original bytes
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
    biggest = message.photo[-1]  # highest available quality
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


# ----- navigation (Back buttons) ------------------------------------------ #

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
    await cb_nav(cq, state)  # reuse the same prompts


@router.callback_query(F.data == "sum:change")
async def cb_sum_change(cq: CallbackQuery, state: FSMContext):
    await safe_edit(cq, "✏️ <b>Which setting do you want to change?</b>",
                    kb_change())
    await cq.answer()


# ----- step 1: page size --------------------------------------------------- #

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


# ----- step 2: background -------------------------------------------------- #

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


# ----- step 3: passport photo size ------------------------------------------ #

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

# ----- step 4: quantity ----------------------------------------------------- #

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


# ----- step 5: output format ------------------------------------------------ #

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


# ----- generate --------------------------------------------------------------- #

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
    except BaseException as exc:  # never leave the user without an answer
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
        cleanup_user(cq.from_user.id)


# ----- catch-all for stray input --------------------------------------------- #

@router.message()
async def fallback_message(message: Message):
    await message.answer("Send me a <b>photo</b> to create a passport photo "
                         "sheet, or use /start.", reply_markup=kb_main_menu())


@router.callback_query()
async def fallback_callback(cq: CallbackQuery):
    await cq.answer("That action is no longer available. Send a photo or use "
                    "/start to begin again.", show_alert=False)

# --------------------------------------------------------------------------- #
# Telegram Mini App (all HTML/CSS/JS embedded right here)
# --------------------------------------------------------------------------- #


# --------------------------------------------------------------------------- #
# Premium web application: authentication, admin controls, photo editor
# --------------------------------------------------------------------------- #

DB_PATH = Path(os.getenv("DATABASE_PATH", str(Path(tempfile.gettempdir()) / "photo_maker.sqlite3")))
SESSION_DAYS = int(os.getenv("SESSION_DAYS", "7"))
ADMIN_EMAIL = os.getenv("ADMIN_EMAIL", "").strip().lower()
ADMIN_PASSWORD = os.getenv("ADMIN_PASSWORD", "")
SECURE_COOKIES = os.getenv("SECURE_COOKIES", "1").strip().lower() not in ("0", "false", "no")
MAX_EXPORT_BYTES = 50 * 1024 * 1024

FEATURE_DEFAULTS = {
    "editor": True, "passport": True, "background": True, "pdf": True,
    "a4_print": True, "enhance": True, "compression": True,
}

def db():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA foreign_keys=ON")
    return conn

def hash_password(password: str, salt: bytes | None = None) -> str:
    salt = salt or secrets.token_bytes(16)
    digest = hashlib.scrypt(password.encode("utf-8"), salt=salt, n=2**14, r=8, p=1, dklen=32)
    return "scrypt$" + base64.urlsafe_b64encode(salt).decode() + "$" + base64.urlsafe_b64encode(digest).decode()

def verify_password(password: str, stored: str) -> bool:
    try:
        _, s, d = stored.split("$", 2)
        salt = base64.urlsafe_b64decode(s.encode())
        expected = base64.urlsafe_b64decode(d.encode())
        actual = hashlib.scrypt(password.encode("utf-8"), salt=salt, n=2**14, r=8, p=1, dklen=32)
        return hmac.compare_digest(actual, expected)
    except Exception:
        return False

def valid_email(email: str) -> bool:
    email = email.strip().lower()
    if len(email) > 254 or " " in email or email.count("@") != 1:
        return False
    local, domain = email.rsplit("@", 1)
    return bool(local and "." in domain and len(domain) >= 3)

def init_db():
    conn = db()
    conn.executescript("""
    CREATE TABLE IF NOT EXISTS users(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        email TEXT UNIQUE NOT NULL,
        password_hash TEXT NOT NULL,
        role TEXT NOT NULL DEFAULT 'user',
        bot_access INTEGER NOT NULL DEFAULT 0,
        banned INTEGER NOT NULL DEFAULT 0,
        created_at TEXT NOT NULL,
        last_login TEXT,
        usage_count INTEGER NOT NULL DEFAULT 0
    );
    CREATE TABLE IF NOT EXISTS sessions(
        token_hash TEXT PRIMARY KEY,
        user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
        csrf TEXT NOT NULL,
        created_at TEXT NOT NULL,
        expires_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS activity(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER,
        email TEXT,
        action TEXT NOT NULL,
        meta TEXT,
        ip TEXT,
        created_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS settings(
        key TEXT PRIMARY KEY,
        value TEXT NOT NULL
    );
    """)
    for k, v in FEATURE_DEFAULTS.items():
        conn.execute("INSERT OR IGNORE INTO settings(key,value) VALUES(?,?)", (f"feature:{k}", "1" if v else "0"))
    conn.execute("INSERT OR IGNORE INTO settings(key,value) VALUES('maintenance','0')")
    conn.execute("INSERT OR IGNORE INTO settings(key,value) VALUES('maintenance_message','We are performing a short maintenance update. Please try again soon.')")
    conn.commit()
    if ADMIN_EMAIL and ADMIN_PASSWORD:
        row = conn.execute("SELECT id FROM users WHERE email=?", (ADMIN_EMAIL,)).fetchone()
        now = datetime.now(timezone.utc).isoformat()
        if row:
            conn.execute("UPDATE users SET role='admin', password_hash=? WHERE id=?",
                         (hash_password(ADMIN_PASSWORD), row["id"]))
        else:
            conn.execute("""INSERT INTO users(email,password_hash,role,bot_access,created_at)
                            VALUES(?,?,?,?,?)""",
                         (ADMIN_EMAIL, hash_password(ADMIN_PASSWORD), "admin", 1, now))
        conn.commit()
    conn.close()

init_db()

def setting(key, default=None):
    conn = db()
    row = conn.execute("SELECT value FROM settings WHERE key=?", (key,)).fetchone()
    conn.close()
    return (row["value"] if row else default)

def set_setting(key, value):
    conn = db()
    conn.execute("INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                 (key, str(value)))
    conn.commit()
    conn.close()

def log_activity(user_id, email, action, meta="", ip=""):
    conn = db()
    conn.execute("INSERT INTO activity(user_id,email,action,meta,ip,created_at) VALUES(?,?,?,?,?,?)",
                 (user_id, email, action, meta[:1000], ip[:120], datetime.now(timezone.utc).isoformat()))
    conn.commit()
    conn.close()

def create_session(user_id, ip):
    raw = secrets.token_urlsafe(48)
    token_hash = hashlib.sha256(raw.encode()).hexdigest()
    csrf = secrets.token_urlsafe(24)
    now = datetime.now(timezone.utc)
    exp = now.timestamp() + SESSION_DAYS * 86400
    expires = datetime.fromtimestamp(exp, timezone.utc).isoformat()
    conn = db()
    conn.execute("INSERT INTO sessions(token_hash,user_id,csrf,created_at,expires_at) VALUES(?,?,?,?,?)",
                 (token_hash, user_id, csrf, now.isoformat(), expires))
    conn.commit()
    conn.close()
    return raw, csrf

def current_user(request):
    token = request.cookies.get("session")
    if not token:
        return None
    th = hashlib.sha256(token.encode()).hexdigest()
    conn = db()
    row = conn.execute("""SELECT u.*,s.csrf,s.expires_at FROM sessions s
                          JOIN users u ON u.id=s.user_id WHERE s.token_hash=?""", (th,)).fetchone()
    if not row:
        conn.close(); return None
    try:
        expired = datetime.fromisoformat(row["expires_at"]) < datetime.now(timezone.utc)
    except Exception:
        expired = True
    if expired or row["banned"]:
        conn.execute("DELETE FROM sessions WHERE token_hash=?", (th,))
        conn.commit(); conn.close()
        return None
    conn.close()
    return row

def csrf_ok(request, user):
    return user is not None and request.headers.get("X-CSRF-Token", "") == user["csrf"]

def json_error(message, status=400):
    return web.json_response({"ok": False, "error": message}, status=status)

def require_user(request):
    u = current_user(request)
    if not u:
        return None, json_error("Please login to continue.", 401)
    if str(setting("maintenance", "0")) == "1" and u["role"] != "admin":
        return None, json_error(setting("maintenance_message", "Maintenance in progress."), 503)
    return u, None

def require_admin(request):
    u, err = require_user(request)
    if err:
        return None, err
    if u["role"] != "admin":
        return None, json_error("Admin access required.", 403)
    return u, None

async def read_json(request):
    try:
        return await request.json()
    except Exception:
        return None

async def http_health(request):
    return web.json_response({"ok": True, "service": "photoforge"})

async def http_favicon(request):
    return web.Response(status=204)

async def http_index(request):
    return web.Response(text=PREMIUM_HTML, content_type="text/html", charset="utf-8",
                        headers={"Cache-Control": "no-store"})

async def http_auth_me(request):
    u = current_user(request)
    if not u:
        return web.json_response({"authenticated": False})
    return web.json_response({"authenticated": True, "csrf": u["csrf"],
                              "user": {"id":u["id"],"email":u["email"],"role":u["role"],
                                       "bot_access":bool(u["bot_access"]), "usage_count":u["usage_count"]},
                              "maintenance": setting("maintenance","0") == "1"})

async def http_register(request):
    if setting("maintenance","0") == "1":
        return json_error(setting("maintenance_message"), 503)
    data = await read_json(request)
    if not isinstance(data, dict):
        return json_error("Invalid request.")
    email = str(data.get("email","")).strip().lower()
    password = str(data.get("password",""))
    if not valid_email(email):
        return json_error("Enter a valid email address.")
    if len(password) < 8:
        return json_error("Password must be at least 8 characters.")
    conn = db()
    try:
        now = datetime.now(timezone.utc).isoformat()
        cur = conn.execute("""INSERT INTO users(email,password_hash,role,created_at)
                              VALUES(?,?,?,?,?)""",
                           (email,hash_password(password),"user",now))
        uid = cur.lastrowid
        conn.commit()
    except sqlite3.IntegrityError:
        conn.close()
        return json_error("An account with this email already exists.", 409)
    conn.close()
    token, csrf = create_session(uid, request.remote or "")
    log_activity(uid,email,"register","",request.remote or "")
    resp = web.json_response({"ok":True,"user":{"email":email,"role":"user"},"csrf":csrf})
    resp.set_cookie("session",token,max_age=SESSION_DAYS*86400,httponly=True,samesite="Lax",
                    secure=SECURE_COOKIES,path="/")
    return resp

async def http_login(request):
    if setting("maintenance","0") == "1":
        return json_error(setting("maintenance_message"), 503)
    data = await read_json(request)
    email = str(data.get("email","")).strip().lower() if isinstance(data,dict) else ""
    password = str(data.get("password","")) if isinstance(data,dict) else ""
    conn = db()
    row = conn.execute("SELECT * FROM users WHERE email=?", (email,)).fetchone()
    if not row or not verify_password(password,row["password_hash"]):
        conn.close()
        return json_error("Invalid email or password.", 401)
    if row["banned"]:
        conn.close()
        return json_error("This account has been banned.", 403)
    now = datetime.now(timezone.utc).isoformat()
    conn.execute("UPDATE users SET last_login=? WHERE id=?", (now,row["id"]))
    conn.commit(); conn.close()
    token, csrf = create_session(row["id"],request.remote or "")
    log_activity(row["id"],email,"login","",request.remote or "")
    resp = web.json_response({"ok":True,"csrf":csrf})
    resp.set_cookie("session",token,max_age=SESSION_DAYS*86400,httponly=True,samesite="Lax",
                    secure=SECURE_COOKIES,path="/")
    return resp

async def http_logout(request):
    u = current_user(request)
    if u:
        token = request.cookies.get("session")
        conn=db(); conn.execute("DELETE FROM sessions WHERE token_hash=?",
                                (hashlib.sha256(token.encode()).hexdigest(),)); conn.commit(); conn.close()
        log_activity(u["id"],u["email"],"logout","",request.remote or "")
    resp=web.json_response({"ok":True})
    resp.del_cookie("session",path="/")
    return resp

def process_adjustments(img, a):
    img = img.convert("RGB")
    arr = np.asarray(img).astype(np.float32) / 255.0
    brightness = float(a.get("brightness",0))
    contrast = float(a.get("contrast",0))
    exposure = float(a.get("exposure",0))
    saturation = float(a.get("saturation",0))
    warmth = float(a.get("warmth",0))
    tint = float(a.get("tint",0))
    if exposure:
        arr *= 2.0 ** (exposure / 100.0)
    if brightness:
        arr += brightness / 100.0
    if contrast:
        factor = (259.0*(contrast+255.0))/(255.0*(259.0-contrast))
        arr = (arr-0.5)*factor + 0.5
    if saturation:
        lum = arr[...,0]*0.2126 + arr[...,1]*0.7152 + arr[...,2]*0.0722
        arr = lum[...,None] + (arr-lum[...,None])*(1+saturation/100.0)
    if warmth:
        arr[...,0] += warmth/300.0
        arr[...,2] -= warmth/300.0
    if tint:
        arr[...,1] += tint/350.0
        arr[...,0] += tint/500.0
    arr=np.clip(arr,0,1)
    out=Image.fromarray((arr*255+0.5).astype(np.uint8),"RGB")
    sharp=float(a.get("sharpness",0))
    if sharp > 0:
        out=out.filter(ImageFilter.UnsharpMask(radius=1.2,percent=int(min(250,sharp*2.2)),threshold=3))
    denoise=float(a.get("denoise",0))
    if denoise > 0:
        out=out.filter(ImageFilter.MedianFilter(size=3))
    return out

def apply_crop(img, crop):
    if not isinstance(crop,dict): return img
    try:
        x=max(0,int(float(crop.get("x",0))))
        y=max(0,int(float(crop.get("y",0))))
        w=max(1,int(float(crop.get("w",img.width))))
        h=max(1,int(float(crop.get("h",img.height))))
        x=min(x,img.width-1); y=min(y,img.height-1)
        w=min(w,img.width-x); h=min(h,img.height-y)
        return img.crop((x,y,x+w,y+h))
    except Exception:
        return img

def apply_editor_ops(img, payload):
    img=ImageOps.exif_transpose(img).convert("RGB")
    img=apply_crop(img,payload.get("crop"))
    rot=int(payload.get("rotation",0)) % 360
    if rot in (90,180,270):
        img=img.rotate(-rot,expand=True,resample=Image.Resampling.BICUBIC)
    if payload.get("flip_h"): img=ImageOps.mirror(img)
    if payload.get("flip_v"): img=ImageOps.flip(img)
    img=process_adjustments(img,payload.get("adjustments",{}))
    bg=payload.get("background")
    if isinstance(bg,dict) and bg.get("mode")=="solid":
        rgb=parse_hex_color(str(bg.get("color","#FFFFFF")))
        if rgb:
            img,_=replace_background(img,rgb)
    return img

def export_image(img, fmt, quality=95, dpi=300):
    b=io.BytesIO()
    fmt=fmt.lower()
    if fmt in ("jpg","jpeg"):
        img.save(b,"JPEG",quality=max(40,min(100,int(quality))),subsampling=0,optimize=True,dpi=(dpi,dpi))
        return b.getvalue(),"image/jpeg","edited.jpg"
    if fmt=="png":
        img.save(b,"PNG",optimize=True,dpi=(dpi,dpi))
        return b.getvalue(),"image/png","edited.png"
    raise ValueError("Unsupported image format.")

def build_print_pdf(img, page_w_mm, page_h_mm, pw_mm, ph_mm, qty, quality=95):
    sheet=build_sheet(img,page_w_mm,page_h_mm,pw_mm,ph_mm,qty)
    b=io.BytesIO()
    sheet.save(b,"PDF",resolution=float(DPI))
    return b.getvalue(),"application/pdf","photo-sheet.pdf"

async def http_editor_process(request):
    u, err = require_user(request)
    if err: return err
    if not csrf_ok(request,u): return json_error("Security token expired. Refresh and try again.",403)
    if setting("feature:editor","1")!="1": return json_error("The editor is currently disabled.",503)
    try:
        reader=await request.multipart()
        photo=None; payload={}
        async for part in reader:
            if part.name=="photo":
                photo=await part.read(decode=False)
            elif part.name=="payload":
                try: payload=json.loads((await part.read(decode=False)).decode())
                except Exception: payload={}
        if not photo: return json_error("No image was uploaded.")
        img=load_image(photo)
        out=apply_editor_ops(img,payload)
        mode=str(payload.get("export","jpg")).lower()
        quality=int(payload.get("quality",95))
        dpi=int(payload.get("dpi",300))
        if mode=="pdf":
            page=payload.get("page",{})
            ps=payload.get("photo_size",{})
            pdf,ct,name=build_print_pdf(out,float(page.get("w",210)),float(page.get("h",297)),
                                        float(ps.get("w",35)),float(ps.get("h",45)),
                                        max(1,min(MAX_QTY,int(payload.get("qty",1)))))
            blob,ct,name=pdf,ct,name
        else:
            blob,ct,name=export_image(out,mode,quality,dpi)
        if len(blob)>MAX_EXPORT_BYTES: return json_error("Export is too large. Reduce dimensions or quality.")
        conn=db()
        conn.execute("UPDATE users SET usage_count=usage_count+1 WHERE id=?",(u["id"],)); conn.commit(); conn.close()
        log_activity(u["id"],u["email"],"export",json.dumps({"format":mode,"bytes":len(blob)}),request.remote or "")
        return web.Response(body=blob,content_type=ct,headers={
            "Content-Disposition":f'attachment; filename="{name}"',
            "Cache-Control":"no-store",
            "X-Image-Dimensions":f"{out.width}x{out.height}"
        })
    except ValueError as e:
        return json_error(str(e))
    except Exception:
        log.exception("editor processing failed")
        return json_error("Image processing failed. Please try again.",500)


async def http_print_process(request):
    u, err = require_user(request)
    if err: return err
    if not csrf_ok(request,u): return json_error("Security token expired. Refresh and try again.",403)
    if setting("feature:a4_print","1")!="1" or setting("feature:passport","1")!="1":
        return json_error("Print Studio is currently disabled.",503)
    try:
        reader=await request.multipart()
        photo=None; payload={}
        async for part in reader:
            if part.name=="photo": photo=await part.read(decode=False)
            elif part.name=="payload":
                try: payload=json.loads((await part.read(decode=False)).decode())
                except Exception: payload={}
        if not photo: return json_error("No image was uploaded.")
        img=apply_editor_ops(load_image(photo),payload)
        page=payload.get("page",{})
        ps=payload.get("photo_size",{})
        pw=float(page.get("w",210)); ph=float(page.get("h",297))
        sw=float(ps.get("w",35)); sh=float(ps.get("h",45))
        qty=max(1,min(MAX_QTY,int(payload.get("qty",1))))
        if not (MM_MIN_PAGE<=pw<=MM_MAX_PAGE and MM_MIN_PAGE<=ph<=MM_MAX_PAGE):
            return json_error("Invalid page dimensions.")
        if not (MM_MIN_PHOTO<=sw<=MM_MAX_PHOTO and MM_MIN_PHOTO<=sh<=MM_MAX_PHOTO):
            return json_error("Invalid photo dimensions.")
        grid=compute_grid(pw,ph,sw,sh)
        if grid is None:
            return json_error("The selected photo size does not fit on this page.")
        pages=math.ceil(qty/(grid[0]*grid[1]))
        sheet=build_sheet(img,pw,ph,sw,sh,qty)
        fmt=str(payload.get("export","pdf")).lower()
        if fmt=="pdf":
            b=io.BytesIO(); sheet.save(b,"PDF",resolution=float(DPI))
            blob,ct,name=b.getvalue(),"application/pdf","photo-sheet.pdf"
        else:
            blob,ct,name=export_image(sheet,fmt,int(payload.get("quality",95)),DPI)
        if len(blob)>MAX_EXPORT_BYTES: return json_error("Export is too large.")
        conn=db(); conn.execute("UPDATE users SET usage_count=usage_count+1 WHERE id=?",(u["id"],)); conn.commit(); conn.close()
        log_activity(u["id"],u["email"],"print_export",json.dumps({"format":fmt,"qty":qty,"pages":pages}),request.remote or "")
        return web.Response(body=blob,content_type=ct,headers={"Content-Disposition":f'attachment; filename="{name}"',"Cache-Control":"no-store"})
    except Exception:
        log.exception("print processing failed")
        return json_error("Print generation failed. Please check the dimensions and try again.",500)

async def http_admin_users(request):
    u,err=require_admin(request)
    if err:return err
    conn=db()
    rows=conn.execute("""SELECT id,email,role,bot_access,banned,created_at,last_login,usage_count
                         FROM users ORDER BY created_at DESC""").fetchall()
    conn.close()
    return web.json_response({"users":[dict(r) for r in rows]})

async def http_admin_user_update(request):
    u,err=require_admin(request)
    if err:return err
    if not csrf_ok(request,u): return json_error("Invalid security token.",403)
    try: uid=int(request.match_info["id"])
    except: return json_error("Invalid user id.")
    data=await read_json(request)
    if not isinstance(data,dict): return json_error("Invalid request.")
    fields={}
    for k in ("bot_access","banned"):
        if k in data: fields[k]=1 if bool(data[k]) else 0
    if "role" in data and data["role"] in ("user","admin"): fields["role"]=data["role"]
    if not fields:return json_error("Nothing to update.")
    conn=db()
    sets=",".join(f"{k}=?" for k in fields)
    conn.execute(f"UPDATE users SET {sets} WHERE id=?",(*fields.values(),uid)); conn.commit()
    row=conn.execute("SELECT email FROM users WHERE id=?",(uid,)).fetchone()
    if fields.get("banned")==1: conn.execute("DELETE FROM sessions WHERE user_id=?",(uid,)); conn.commit()
    conn.close()
    log_activity(u["id"],u["email"],"admin_user_update",json.dumps({"target":uid,"changes":fields}),request.remote or "")
    return web.json_response({"ok":True,"email":row["email"] if row else None})

async def http_admin_activity(request):
    u,err=require_admin(request)
    if err:return err
    conn=db()
    rows=conn.execute("SELECT * FROM activity ORDER BY id DESC LIMIT 200").fetchall()
    conn.close()
    return web.json_response({"activity":[dict(r) for r in rows]})

async def http_admin_settings(request):
    u,err=require_admin(request)
    if err:return err
    if request.method=="GET":
        features={k.split(":",1)[1]: setting(k,"0")=="1" for k in [f"feature:{x}" for x in FEATURE_DEFAULTS]}
        return web.json_response({"maintenance":setting("maintenance","0")=="1",
                                  "maintenance_message":setting("maintenance_message",""),
                                  "features":features})
    if not csrf_ok(request,u): return json_error("Invalid security token.",403)
    data=await read_json(request)
    if not isinstance(data,dict): return json_error("Invalid request.")
    if "maintenance" in data:set_setting("maintenance","1" if data["maintenance"] else "0")
    if "maintenance_message" in data:set_setting("maintenance_message",str(data["maintenance_message"])[:500])
    if isinstance(data.get("features"),dict):
        for k,v in data["features"].items():
            if k in FEATURE_DEFAULTS:set_setting(f"feature:{k}","1" if v else "0")
    log_activity(u["id"],u["email"],"admin_settings",json.dumps(data),request.remote or "")
    return web.json_response({"ok":True})

async def http_admin_info(request):
    u,err=require_admin(request)
    if err:return err
    conn=db()
    users=conn.execute("SELECT COUNT(*) c FROM users").fetchone()["c"]
    active=conn.execute("SELECT COUNT(*) c FROM users WHERE banned=0").fetchone()["c"]
    exports=conn.execute("SELECT COALESCE(SUM(usage_count),0) c FROM users").fetchone()["c"]
    conn.close()
    return web.json_response({"users":users,"active_users":active,"exports":exports,
                              "uptime_seconds":round(time.time()-_started_at,1),
                              "rembg":REMBG_AVAILABLE or USE_REMBG})

PREMIUM_HTML = r"""<!doctype html>
<html lang="en"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<title>PhotoForge — Professional Photo Editor</title>
<style>
:root{--bg:#08090c;--panel:#11131a;--panel2:#171a22;--line:#272b36;--text:#f7f7f8;--muted:#9da3af;--red:#e11d2e;--red2:#ff4050;--redbg:#2a0e13;--green:#36d399;--shadow:0 20px 60px #0009}
*{box-sizing:border-box}html,body{margin:0;min-height:100%;background:radial-gradient(900px 500px at 20% -10%,#3b0d14 0,#08090c 55%);color:var(--text);font-family:Inter,ui-sans-serif,system-ui,-apple-system,Segoe UI,Roboto,Arial}
button,input,select{font:inherit}button{cursor:pointer}.hidden{display:none!important}.app{min-height:100vh}.auth{min-height:100vh;display:grid;place-items:center;padding:22px}.auth-card{width:min(430px,100%);background:#101219e8;border:1px solid var(--line);border-radius:28px;padding:30px;box-shadow:var(--shadow);backdrop-filter:blur(20px)}
.logo{display:flex;align-items:center;gap:12px;font-weight:800;font-size:22px}.logo-mark{width:40px;height:40px;border-radius:13px;background:linear-gradient(135deg,var(--red2),#9d0918);display:grid;place-items:center;box-shadow:0 10px 30px #e11d2e44}.eyebrow{color:#ff7180;font-size:12px;text-transform:uppercase;letter-spacing:.14em;font-weight:800;margin:25px 0 8px}.auth h1{font-size:32px;margin:0 0 8px}.muted{color:var(--muted)}.tabs{display:flex;background:#0a0b0f;border:1px solid var(--line);padding:4px;border-radius:13px;margin:22px 0 16px}.tabs button{flex:1;border:0;background:transparent;color:var(--muted);padding:11px;border-radius:10px}.tabs button.on{background:#242832;color:#fff}.field{margin:12px 0}.field label{display:block;font-size:12px;color:#b7bcc7;margin:0 0 7px}.field input,.field select{width:100%;padding:13px 14px;border:1px solid var(--line);border-radius:12px;background:#0b0d12;color:#fff;outline:none}.field input:focus{border-color:#e11d2e88;box-shadow:0 0 0 3px #e11d2e1b}.primary{width:100%;padding:14px;border:0;border-radius:13px;background:linear-gradient(135deg,var(--red2),var(--red));color:#fff;font-weight:800;box-shadow:0 12px 30px #e11d2e33}.danger{background:#341017;color:#ff9aa4;border:1px solid #62202a}.appbar{height:68px;border-bottom:1px solid var(--line);background:#0b0d11dd;backdrop-filter:blur(16px);display:flex;align-items:center;justify-content:space-between;padding:0 max(18px,calc((100vw - 1400px)/2));position:sticky;top:0;z-index:20}.user-pill{display:flex;align-items:center;gap:10px}.avatar{width:34px;height:34px;border-radius:11px;background:var(--redbg);display:grid;place-items:center;color:#ff7a86;font-weight:800}.layout{max-width:1400px;margin:auto;padding:22px;display:grid;grid-template-columns:230px 1fr;gap:22px}.side{background:#0e1016;border:1px solid var(--line);border-radius:20px;padding:12px;height:max-content;position:sticky;top:90px}.side button{width:100%;text-align:left;background:transparent;color:#aeb4bf;border:0;padding:12px;border-radius:11px;margin:2px 0}.side button.on,.side button:hover{background:#241116;color:#fff}.content{min-width:0}.hero{display:flex;justify-content:space-between;gap:20px;align-items:flex-start;margin:5px 0 20px}.hero h1{font-size:32px;margin:0 0 5px}.cards{display:grid;grid-template-columns:repeat(4,1fr);gap:14px}.card{background:linear-gradient(180deg,#151820,#101218);border:1px solid var(--line);border-radius:18px;padding:18px;box-shadow:0 10px 30px #0002}.stat .num{font-size:26px;font-weight:850;margin-top:6px}.stat .label{font-size:12px;color:var(--muted)}.upload{border:1px dashed #3a404d;border-radius:20px;min-height:280px;display:grid;place-items:center;text-align:center;padding:28px;background:radial-gradient(400px 200px at 50% 0,#33101855,transparent)}.upload-icon{font-size:40px}.tool-grid{display:grid;grid-template-columns:repeat(3,1fr);gap:12px}.tool{background:#151820;border:1px solid var(--line);border-radius:15px;padding:15px;text-align:left;color:#fff}.tool:hover{border-color:#e11d2e77;transform:translateY(-1px)}.tool b{display:block;margin-bottom:5px}.tool span{font-size:12px;color:var(--muted)}.editor{display:grid;grid-template-columns:minmax(0,1fr) 330px;gap:16px}.canvas-card{background:#0c0e13;border:1px solid var(--line);border-radius:20px;padding:15px;min-height:500px;display:grid;place-items:center}.stage{width:100%;height:min(65vh,680px);display:grid;place-items:center;background:repeating-conic-gradient(#151820 0 25%,#101218 0 50%) 50%/24px 24px;border-radius:14px;overflow:hidden}.stage canvas{max-width:100%;max-height:100%;object-fit:contain}.controls{display:grid;gap:12px}.range{display:grid;grid-template-columns:1fr 46px;gap:8px;align-items:center}.range input[type=range]{width:100%;accent-color:var(--red2)}.range output{font-size:11px;color:#c8ccd4;text-align:right}.toolbar{display:flex;gap:8px;flex-wrap:wrap}.toolbar button{border:1px solid var(--line);background:#151820;color:#fff;border-radius:10px;padding:9px 11px}.toolbar button:hover{border-color:#e11d2e66}.bottom{display:flex;gap:10px;margin-top:12px}.bottom>*{flex:1}.table-wrap{overflow:auto}.table{width:100%;border-collapse:collapse;font-size:13px}.table th,.table td{padding:11px;border-bottom:1px solid var(--line);text-align:left;white-space:nowrap}.switch{display:flex;align-items:center;justify-content:space-between;padding:10px 0}.switch input{accent-color:var(--red)}.toast{position:fixed;right:18px;bottom:18px;background:#161920;border:1px solid #343945;border-radius:13px;padding:13px 15px;box-shadow:var(--shadow);z-index:50}.modal{position:fixed;inset:0;background:#000a;display:grid;place-items:center;padding:18px;z-index:40}.modal-card{width:min(560px,100%);max-height:90vh;overflow:auto;background:#11141a;border:1px solid var(--line);border-radius:22px;padding:20px}.progress{height:5px;background:#242832;border-radius:99px;overflow:hidden}.progress i{display:block;height:100%;width:0;background:var(--red2);transition:.2s}.badge{font-size:11px;padding:4px 8px;border-radius:99px;background:#252932;color:#cdd2dc}.badge.red{background:#351118;color:#ff9aa4}.badge.green{background:#0d2c22;color:#76e4bb}
@media(max-width:1000px){.layout{grid-template-columns:1fr}.side{position:static;display:flex;overflow:auto}.side button{min-width:max-content}.cards{grid-template-columns:repeat(2,1fr)}.editor{grid-template-columns:1fr}.controls{grid-template-columns:1fr 1fr}.controls .wide{grid-column:1/-1}}
@media(max-width:600px){.layout{padding:14px}.appbar{padding:0 14px}.hero{display:block}.hero h1{font-size:26px}.cards{grid-template-columns:1fr 1fr}.tool-grid{grid-template-columns:1fr 1fr}.controls{grid-template-columns:1fr}.auth-card{padding:22px}.stage{height:52vh}.user-pill .email{display:none}}
</style></head>
<body><div id="root"></div><div id="toast" class="toast hidden"></div>
<script>
const $=s=>document.querySelector(s), root=$("#root");
let me=null,csrf="",file=null,img=null,canvas=null,ctx=null,history=[],future=[],active="editor";
const defaults={brightness:0,contrast:0,exposure:0,saturation:0,sharpness:0,warmth:0,tint:0,denoise:0};
let adj={...defaults},rotation=0,flipH=false,flipV=false,crop=null;
function toast(m){const t=$("#toast");t.textContent=m;t.classList.remove("hidden");setTimeout(()=>t.classList.add("hidden"),2800)}
async function api(url,opt={}){opt.headers={...(opt.headers||{}),"Content-Type":"application/json"};if(csrf)opt.headers["X-CSRF-Token"]=csrf;const r=await fetch(url,opt);let d={};try{d=await r.json()}catch{}if(!r.ok)throw Error(d.error||"Request failed");return d}
async function boot(){try{const d=await fetch("/api/auth/me",{cache:"no-store"}).then(r=>r.json());if(d.authenticated){me=d.user;csrf=d.csrf;renderApp()}else renderAuth()}catch(e){renderAuth()}}
function renderAuth(mode="login"){root.innerHTML=`<main class="auth"><section class="auth-card">
<div class="logo"><div class="logo-mark">✦</div>PhotoForge</div><div class="eyebrow">Professional photo studio</div><h1>${mode==="login"?"Welcome back":"Create your account"}</h1><p class="muted">Secure workspace for high-quality editing, passport photos and print-ready exports.</p>
<div class="tabs"><button class="${mode==="login"?"on":""}" onclick="renderAuth('login')">Login</button><button class="${mode==="register"?"on":""}" onclick="renderAuth('register')">Create Account</button></div>
<form onsubmit="authSubmit(event,'${mode}')"><div class="field"><label>Email / Gmail</label><input id="email" type="email" autocomplete="email" required placeholder="you@gmail.com"></div>
<div class="field"><label>Password</label><input id="password" type="password" minlength="8" autocomplete="${mode==="login"?"current-password":"new-password"}" required placeholder="Minimum 8 characters"></div>
${mode==="register"?'<div class="field"><label>Confirm password</label><input id="password2" type="password" minlength="8" required placeholder="Repeat password"></div>':''}
<button class="primary" type="submit">${mode==="login"?"Login securely":"Create account"}</button></form>
<p class="muted" style="font-size:11px;margin-top:18px">Your editing files are processed temporarily and are designed to be removed after processing.</p></section></main>`}
async function authSubmit(e,mode){e.preventDefault();const email=$("#email").value.trim(),password=$("#password").value;if(mode==="register"&&password!==$("#password2").value)return toast("Passwords do not match");try{const d=await api("/api/auth/"+mode,{method:"POST",body:JSON.stringify({email,password})});csrf=d.csrf;const m=await fetch("/api/auth/me").then(r=>r.json());me=m.user;csrf=m.csrf;renderApp();toast(mode==="login"?"Welcome back":"Account created")}catch(e){toast(e.message)}}
function renderApp(){root.innerHTML=`<header class="appbar"><div class="logo"><div class="logo-mark">✦</div>PhotoForge</div><div class="user-pill"><div class="avatar">${me.email[0].toUpperCase()}</div><span class="email">${me.email}</span>${me.role==="admin"?'<span class="badge red">ADMIN</span>':''}<button class="toolbar" style="border:0;background:transparent;color:#bbb" onclick="logout()">↪</button></div></header>
<div class="layout"><nav class="side"><button class="on" onclick="showPanel('editor',this)">✦ Editor</button><button onclick="showPanel('prints',this)">▣ Print Studio</button>${me.role==="admin"?'<button onclick="showPanel(\'admin\',this)">⚙ Admin Panel</button>':''}</nav><main class="content" id="panel"></main></div>`;showPanel("editor",document.querySelector(".side button"))}
function showPanel(name,btn){active=name;document.querySelectorAll(".side button").forEach(x=>x.classList.remove("on"));if(btn)btn.classList.add("on");if(name==="admin")renderAdmin();else if(name==="prints")renderPrints();else renderEditor()}
function renderChooser(){panel.innerHTML=`<div class="hero"><div><div class="eyebrow" style="margin-top:0">New image</div><h1>What would you like to do?</h1><p class="muted">Choose a focused workflow or open the complete professional editor.</p></div></div>
<section class="card"><div class="tool-grid">
<button class="tool" onclick="openEditor()"><b>✦ Full Editor</b><span>All professional adjustments</span></button>
<button class="tool" onclick="openEditor()"><b>✂ Crop & Resize</b><span>Precise framing and dimensions</span></button>
<button class="tool" onclick="openEditor()"><b>✨ Enhance Quality</b><span>Natural sharpness and clarity</span></button>
<button class="tool" onclick="openEditor()"><b>🎨 Adjust Colors</b><span>Exposure, saturation, warmth</span></button>
<button class="tool" onclick="openEditor()"><b>🪄 Background</b><span>Clean solid-color backgrounds</span></button>
<button class="tool" onclick="showPanel('prints',document.querySelectorAll('.side button')[1])"><b>▣ Passport / A4</b><span>Print-ready photo layouts</span></button>
</div></section>
<div class="card"><div class="toolbar"><button onclick="deleteWorkspace()">Delete uploaded image</button><span class="muted" style="font-size:12px">Your source stays local until an export is requested.</span></div></div>`}
function renderEditor(){
if(!file){
 panel.innerHTML=`<div class="hero"><div><div class="eyebrow" style="margin-top:0">Creative workspace</div><h1>Photo Editor</h1><p class="muted">Upload an image to start.</p></div></div>
 <section class="card upload" onclick="document.getElementById('fileInput').click()"><div><div class="upload-icon">⌁</div><h2>Upload an image</h2><p class="muted">JPG, PNG, WEBP • up to 25 MB</p><button class="primary" style="width:auto;margin-top:16px">Choose image</button></div><input id="fileInput" type="file" accept="image/*" hidden onchange="loadFile(this.files[0])"></section>`;
 return;
}
panel.innerHTML=`<div class="hero"><div><div class="eyebrow" style="margin-top:0">Creative workspace</div><h1>Photo Editor</h1><p class="muted">Natural enhancement, precise crop and print-ready export.</p></div><span class="badge">High quality • 300 DPI</span></div>
<section class="editor"><div><div class="card"><div class="toolbar"><button onclick="snapshot();rotation=(rotation+90)%360;draw()">↻ Rotate</button><button onclick="snapshot();flipH=!flipH;draw()">⇋ Flip H</button><button onclick="snapshot();flipV=!flipV;draw()">⇵ Flip V</button><button onclick="undo()">↶ Undo</button><button onclick="redo()">↷ Redo</button><button onclick="resetEdit()">Reset</button><button onclick="document.getElementById('fileInput').click()">Replace</button><input id="fileInput" type="file" accept="image/*" hidden onchange="loadFile(this.files[0])"></div></div>
<div class="canvas-card"><div class="stage"><canvas id="canvas"></canvas></div></div>
<div class="bottom"><button class="primary" onclick="exportNow('jpg')">Export JPG</button><button class="primary" onclick="exportNow('png')">Export PNG</button><button class="primary" onclick="exportNow('pdf')">Create PDF</button><button class="danger" onclick="deleteWorkspace()">Delete</button></div></div>
<aside class="controls"><div class="card"><h3>Adjustments</h3>${range("brightness","Brightness",-100,100)}${range("contrast","Contrast",-100,100)}${range("exposure","Exposure",-100,100)}${range("saturation","Saturation",-100,100)}${range("sharpness","Sharpness",0,100)}${range("warmth","Warmth",-100,100)}${range("tint","Tint",-100,100)}${range("denoise","Soft Denoise",0,100)}</div>
<div class="card"><h3>Background</h3><select id="bgColor"><option value="">Keep original</option><option value="#FFFFFF">White</option><option value="#1565C0">Blue</option><option value="#D32F2F">Red</option><option value="#2E7D32">Green</option></select><p class="muted" style="font-size:11px;margin-top:8px">Best for plain, clean backgrounds. Original is kept if detection is unsafe.</p></div>
<div class="card"><h3>Export quality</h3><div class="field"><label>JPG quality</label><input id="quality" type="range" min="60" max="100" value="95" oninput="document.getElementById('qv').textContent=this.value"></div><span class="badge" id="qv">95</span></div></aside></section>`;
canvas=document.getElementById("canvas");ctx=canvas.getContext("2d");draw()
}
function range(k,label,min,max){return `<div class="field"><label>${label}</label><div class="range"><input type="range" min="${min}" max="${max}" value="${adj[k]}" oninput="adj['${k}']=+this.value;draw()"><output>${adj[k]}</output></div></div>`}
function loadFile(f){if(!f)return;if(f.size>25*1024*1024)return toast("Image is too large (25 MB max)");file=f;const r=new FileReader();r.onload=()=>{img=new Image();img.onload=()=>{adj={...defaults};rotation=0;flipH=flipV=false;history=[];future=[];renderChooser();};img.src=r.result};r.readAsDataURL(f)}
function openEditor(){renderEditor()}
function deleteWorkspace(){file=null;img=null;canvas=null;ctx=null;history=[];future=[];adj={...defaults};rotation=0;flipH=flipV=false;renderEditor();toast("Workspace cleared and local image removed")}
function snapshot(){history.push(JSON.stringify({adj,rotation,flipH,flipV}));if(history.length>30)history.shift();future=[]}
function undo(){if(!history.length)return;future.push(JSON.stringify({adj,rotation,flipH,flipV}));Object.assign(window,{});let s=JSON.parse(history.pop());adj=s.adj;rotation=s.rotation;flipH=s.flipH;flipV=s.flipV;renderEditor()}
function redo(){if(!future.length)return;history.push(JSON.stringify({adj,rotation,flipH,flipV}));let s=JSON.parse(future.pop());adj=s.adj;rotation=s.rotation;flipH=s.flipH;flipV=s.flipV;renderEditor()}
function resetEdit(){snapshot();adj={...defaults};rotation=0;flipH=flipV=false;draw()}
function draw(){if(!img||!canvas)return;let max=1400,scale=Math.min(1,max/img.width,max/img.height);let w=Math.round(img.width*scale),h=Math.round(img.height*scale);canvas.width=w;canvas.height=h;ctx.save();ctx.clearRect(0,0,w,h);ctx.translate(w/2,h/2);ctx.rotate(rotation*Math.PI/180);ctx.scale(flipH?-1:1,flipV?-1:1);ctx.filter=`brightness(${100+adj.brightness}%) contrast(${100+adj.contrast}%) saturate(${100+adj.saturation}%)`;ctx.drawImage(img,-w/2,-h/2,w,h);ctx.restore();document.querySelectorAll(".range output").forEach((o,i)=>o.textContent=Object.values(adj)[i])}
async function exportNow(fmt){if(!file)return;const fd=new FormData();fd.append("photo",file);const payload={export:fmt,quality:+$("#quality").value,rotation,flip_h:flipH,flip_v:flipV,adjustments:adj,background:{mode:$("#bgColor").value?"solid":"none",color:$("#bgColor").value}};fd.append("payload",JSON.stringify(payload));const r=await fetch("/api/editor/process",{method:"POST",headers:{"X-CSRF-Token":csrf},body:fd});if(!r.ok){let d=await r.json().catch(()=>({}));return toast(d.error||"Export failed")}const blob=await r.blob();const a=document.createElement("a");a.href=URL.createObjectURL(blob);a.download=r.headers.get("Content-Disposition")?.match(/filename="([^"]+)/)?.[1]||`edited.${fmt}`;a.click();URL.revokeObjectURL(a.href);toast("Export complete")}
function renderPrints(){panel.innerHTML=`<div class="hero"><div><div class="eyebrow" style="margin-top:0">Print Studio</div><h1>Passport & A4 layouts</h1><p class="muted">Exact physical sizes, automatic arrangement and high-quality output.</p></div></div>
<section class="card"><div class="field"><label>Photo</label><input id="printFile" type="file" accept="image/*" onchange="printFile=this.files[0]"></div>
<div class="tool-grid"><button class="tool" onclick="setPrintSize(35,45)"><b>35 × 45 mm</b><span>Passport</span></button><button class="tool" onclick="setPrintSize(25,35)"><b>25 × 35 mm</b><span>ID photo</span></button><button class="tool" onclick="setPrintSize(50.8,50.8)"><b>2 × 2 inch</b><span>Square</span></button></div>
<div class="cards" style="margin-top:14px"><div class="field"><label>Page width (mm)</label><input id="pageW" type="number" value="210" min="50"></div><div class="field"><label>Page height (mm)</label><input id="pageH" type="number" value="297" min="50"></div><div class="field"><label>Photo width (mm)</label><input id="photoW" type="number" value="35" min="10"></div><div class="field"><label>Photo height (mm)</label><input id="photoH" type="number" value="45" min="10"></div><div class="field"><label>Quantity</label><input id="qty" type="number" value="8" min="1" max="500"></div><div class="field"><label>Format</label><select id="printFmt"><option value="pdf">PDF</option><option value="jpg">JPG</option><option value="png">PNG</option></select></div></div>
<div class="bottom"><button class="primary" onclick="generatePrint()">Generate print sheet</button><button class="danger" onclick="showPanel('editor',document.querySelector('.side button'))">Back to editor</button></div></section>`}
let printFile=null;
function setPrintSize(w,h){$("#photoW").value=w;$("#photoH").value=h}
async function generatePrint(){if(!printFile)return toast("Choose a photo first");const fd=new FormData();fd.append("photo",printFile);fd.append("payload",JSON.stringify({page:{w:+$("#pageW").value,h:+$("#pageH").value},photo_size:{w:+$("#photoW").value,h:+$("#photoH").value},qty:+$("#qty").value,export:$("#printFmt").value}));const r=await fetch("/api/print/process",{method:"POST",headers:{"X-CSRF-Token":csrf},body:fd});if(!r.ok){const d=await r.json().catch(()=>({}));return toast(d.error||"Print generation failed")}const blob=await r.blob(),fmt=$("#printFmt").value,a=document.createElement("a");a.href=URL.createObjectURL(blob);a.download=`photo-sheet.${fmt}`;a.click();URL.revokeObjectURL(a.href);toast("Print sheet generated")}
async function renderAdmin(){panel.innerHTML=`<div class="hero"><div><div class="eyebrow" style="margin-top:0">Control center</div><h1>Admin Panel</h1><p class="muted">Manage access, features, maintenance and activity.</p></div></div><div class="cards" id="adminStats"></div><div class="card" style="margin-top:14px"><h3>System controls</h3><div id="settingsBox"></div></div><div class="card" style="margin-top:14px"><h3>Users & permissions</h3><div class="table-wrap"><table class="table"><thead><tr><th>User</th><th>Role</th><th>Bot</th><th>Status</th><th>Usage</th><th>Actions</th></tr></thead><tbody id="users"></tbody></table></div></div><div class="card" style="margin-top:14px"><h3>Recent activity</h3><div class="table-wrap"><table class="table"><thead><tr><th>Time</th><th>User</th><th>Action</th><th>IP</th></tr></thead><tbody id="activity"></tbody></table></div></div>`;loadAdmin()}
async function loadAdmin(){try{const [s,u,a,st]=await Promise.all([api("/api/admin/info"),api("/api/admin/users"),api("/api/admin/activity"),api("/api/admin/settings")]);$("#adminStats").innerHTML=`<div class="card stat"><div class="label">Users</div><div class="num">${s.users}</div></div><div class="card stat"><div class="label">Active</div><div class="num">${s.active_users}</div></div><div class="card stat"><div class="label">Exports</div><div class="num">${s.exports}</div></div><div class="card stat"><div class="label">Uptime</div><div class="num">${Math.floor(s.uptime_seconds/3600)}h</div></div>`;$("#settingsBox").innerHTML=`<div class="switch"><span>Maintenance mode</span><input type="checkbox" ${st.maintenance?"checked":""} onchange="saveSettings()"></div><div class="field"><label>Maintenance message</label><input id="maintMsg" value="${esc(st.maintenance_message)}"></div>${Object.entries(st.features).map(([k,v])=>`<div class="switch"><span>${k}</span><input data-feature="${k}" type="checkbox" ${v?"checked":""}></div>`).join("")}<button class="primary" style="width:auto;margin-top:8px" onclick="saveSettings()">Save system settings</button>`;$("#users").innerHTML=u.users.map(x=>`<tr><td>${esc(x.email)}</td><td><span class="badge">${x.role}</span></td><td>${x.bot_access?"<span class='badge green'>Allowed</span>":"<span class='badge'>Off</span>"}</td><td>${x.banned?"<span class='badge red'>Banned</span>":"<span class='badge green'>Active</span>"}</td><td>${x.usage_count}</td><td><button class="toolbar" onclick="userAction(${x.id},'bot_access',${!x.bot_access})">${x.bot_access?"Revoke bot":"Give bot"}</button><button class="toolbar" onclick="userAction(${x.id},'banned',${!x.banned})">${x.banned?"Unban":"Ban"}</button></td></tr>`).join("");$("#activity").innerHTML=a.activity.map(x=>`<tr><td>${new Date(x.created_at).toLocaleString()}</td><td>${esc(x.email||"—")}</td><td>${esc(x.action)}</td><td>${esc(x.ip||"—")}</td></tr>`).join("")}catch(e){toast(e.message)}}
async function userAction(id,key,val){try{await api("/api/admin/users/"+id,{method:"PATCH",body:JSON.stringify({[key]:val})});toast("Permission updated");loadAdmin()}catch(e){toast(e.message)}}
async function saveSettings(){const f={};document.querySelectorAll("[data-feature]").forEach(x=>f[x.dataset.feature]=x.checked);const maintenance=document.querySelector("#settingsBox input[type=checkbox]").checked;try{await api("/api/admin/settings",{method:"PATCH",body:JSON.stringify({maintenance,maintenance_message:$("#maintMsg").value,features:f})});toast("System settings saved");}catch(e){toast(e.message)}}
function esc(s){return String(s??"").replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#039;"}[c]))}
async function logout(){await api("/api/auth/logout",{method:"POST"}).catch(()=>{});me=null;csrf="";renderAuth("login")}
boot();
</script></body></html>"""

async def http_info_v2(request):
    return web.json_response({
        "service":"photoforge","version":"3.0","uptime_seconds":round(time.time()-_started_at,1),
        "telegram_configured":bool(BOT_TOKEN),"maintenance":setting("maintenance","0")=="1",
        "generations_completed":_generation_count
    })

async def start_web_server() -> web.AppRunner:
    app=web.Application(client_max_size=MAX_IMAGE_BYTES + 2*1024*1024)
    app.router.add_get("/",http_index)
    app.router.add_get("/health",http_health)
    app.router.add_get("/healthz",http_health)
    app.router.add_get("/api/info",http_info_v2)
    app.router.add_get("/api/auth/me",http_auth_me)
    app.router.add_post("/api/auth/register",http_register)
    app.router.add_post("/api/auth/login",http_login)
    app.router.add_post("/api/auth/logout",http_logout)
    app.router.add_post("/api/editor/process",http_editor_process)
    app.router.add_post("/api/print/process",http_print_process)
    app.router.add_get("/api/admin/info",http_admin_info)
    app.router.add_get("/api/admin/users",http_admin_users)
    app.router.add_patch("/api/admin/users/{id}",http_admin_user_update)
    app.router.add_get("/api/admin/activity",http_admin_activity)
    app.router.add_get("/api/admin/settings",http_admin_settings)
    app.router.add_patch("/api/admin/settings",http_admin_settings)
    app.router.add_get("/favicon.ico",http_favicon)
    runner=web.AppRunner(app); await runner.setup()
    site=web.TCPSite(runner,"0.0.0.0",PORT); await site.start()
    log.info("Premium web server listening on port %s",PORT)
    return runner

# --------------------------------------------------------------------------- #
# Entrypoint
# --------------------------------------------------------------------------- #

async def main() -> None:
    runner=await start_web_server()
    if not BOT_TOKEN:
        log.error("BOT_TOKEN is not set; running in web-only mode.")
        try: await asyncio.Event().wait()
        finally: await runner.cleanup()
        return
    bot=Bot(token=BOT_TOKEN,default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    global _bot
    _bot=bot
    dp=Dispatcher(storage=MemoryStorage())
    dp.include_router(router)
    try:
        await bot.delete_webhook(drop_pending_updates=True)
        await asyncio.sleep(2)
        log.info("Bot started (rembg enabled: %s)",USE_REMBG)
        await dp.start_polling(bot,allowed_updates=dp.resolve_used_update_types())
    finally:
        await runner.cleanup(); await bot.session.close()

if __name__=="__main__":
    logging.basicConfig(level=logging.INFO,format="%(asctime)s %(levelname)s %(name)s: %(message)s")
    try: asyncio.run(main())
    except (KeyboardInterrupt,SystemExit): pass
