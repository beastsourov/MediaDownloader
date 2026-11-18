import os
import re
import time
import asyncio
import logging
import shutil
import subprocess
import threading
import uuid
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path

import aiohttp
from dotenv import load_dotenv
import yt_dlp

from telegram import (
    Update,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
)
from telegram.constants import ParseMode, ChatAction
from telegram.helpers import escape_markdown
from telegram.ext import (
    Application,
    ApplicationBuilder,
    CommandHandler,
    CallbackQueryHandler,
    MessageHandler,
    ContextTypes,
    filters,
)
from telegram.error import TelegramError, TimedOut, NetworkError

# =====================================================================
# CONFIGURATION
# =====================================================================

load_dotenv()  # Load BOT_TOKEN from a local .env file

BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()

# Render sets PORT automatically for Web Services.
PORT = os.getenv("PORT")

# Folder where media is temporarily downloaded before being sent
DOWNLOAD_DIR = Path("downloads")
DOWNLOAD_DIR.mkdir(exist_ok=True)

# Telegram bot API upload limit is 50 MB.
SAFE_UPLOAD_SIZE = 49 * 1024 * 1024   # anything above this gets split
SPLIT_TARGET_SIZE = 44 * 1024 * 1024  # target size of each part

# Longest YouTube video (in minutes) the bot will accept.
MAX_DURATION_SECONDS = int(os.getenv("MAX_VIDEO_MINUTES", "120")) * 60

# How many downloads may run at the same time
DOWNLOAD_SLOTS = asyncio.Semaphore(int(os.getenv("MAX_CONCURRENT_DOWNLOADS", "2")))

# Large uploads need generous timeouts
UPLOAD_TIMEOUTS = dict(read_timeout=600, write_timeout=600, connect_timeout=30, pool_timeout=30)

# How often (in seconds) the progress message is allowed to be edited.
PROGRESS_EDIT_INTERVAL = 3

DESKTOP_USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)

# ---------------------------------------------------------------------
# COOKIES
# ---------------------------------------------------------------------
# YouTube blocks datacenter IPs (like Render) unless a logged-in
# cookies.txt is supplied. The cookies are NEVER written in this file.
# Provide them on Render in ONE of these ways:
#   1) Secret File named  cookies.txt   (best; lands in /etc/secrets/)
#   2) Environment variable named  COOKIES_TXT  (whole file contents)
COOKIES_FILE = Path("cookies.txt")


def _prepare_cookies() -> None:
    """Create ./cookies.txt from a Render Secret File or COOKIES_TXT env var."""
    secret = Path("/etc/secrets/cookies.txt")
    env_text = os.getenv("COOKIES_TXT", "").strip()
    try:
        if secret.exists():
            shutil.copy2(secret, COOKIES_FILE)
        elif env_text:
            COOKIES_FILE.write_text(env_text.replace("\\n", "\n") + "\n", encoding="utf-8")
    except Exception as exc:
        print(f"Could not prepare cookies: {exc}")


_prepare_cookies()


def _setup_ffmpeg() -> Path | None:
    """
    Locate ffmpeg (needed to merge HD video+audio streams and to split big
    files). Uses a system ffmpeg if present, otherwise the static binary
    shipped by the `imageio-ffmpeg` pip package.
    """
    exe = shutil.which("ffmpeg")
    if not exe:
        try:
            import imageio_ffmpeg
            exe = imageio_ffmpeg.get_ffmpeg_exe()
        except Exception:
            return None
    bin_dir = Path("bin")
    bin_dir.mkdir(exist_ok=True)
    link = bin_dir / "ffmpeg"
    try:
        if link.is_symlink() or link.exists():
            link.unlink()
        link.symlink_to(Path(exe).resolve())
    except OSError:
        shutil.copy2(exe, link)
        link.chmod(0o755)
    return link


FFMPEG_EXE: Path | None = _setup_ffmpeg()

# Logging setup
logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO,
)
logging.getLogger("httpx").setLevel(logging.WARNING)
logger = logging.getLogger("MediaDownloaderBot")

if COOKIES_FILE.exists():
    logger.info("cookies.txt found (%d bytes) - will be used by yt-dlp", COOKIES_FILE.stat().st_size)
else:
    logger.info("No cookies.txt found - YouTube may block this server")


# =====================================================================
# PLATFORM DETECTION
# =====================================================================

PLATFORM_PATTERNS = {
    "YouTube": re.compile(r"(youtube\.com|youtu\.be)", re.IGNORECASE),
    "Instagram": re.compile(r"instagram\.com", re.IGNORECASE),
    "Facebook": re.compile(
        r"((m|mbasic|web|touch|beta)\.facebook\.com|facebook\.com|fb\.watch)",
        re.IGNORECASE,
    ),
    "TikTok": re.compile(r"((vm|vt|m)\.tiktok\.com|tiktok\.com)", re.IGNORECASE),
    "X (Twitter)": re.compile(r"(twitter\.com|x\.com)", re.IGNORECASE),
    "Threads": re.compile(r"threads\.net", re.IGNORECASE),
    "Likee": re.compile(r"likee\.(video|com)", re.IGNORECASE),
    "Snapchat": re.compile(r"snapchat\.com", re.IGNORECASE),
    "WhatsApp": re.compile(r"whatsapp\.(com|net)", re.IGNORECASE),
}

REDIRECT_DOMAINS = re.compile(
    r"(vm\.tiktok\.com|vt\.tiktok\.com|fb\.watch|mbasic\.facebook\.com)",
    re.IGNORECASE,
)

URL_REGEX = re.compile(r"(https?://[^\s]+)", re.IGNORECASE)

DIRECT_MEDIA_EXTENSIONS = (
    ".mp4", ".mov", ".mkv", ".webm", ".3gp",
    ".jpg", ".jpeg", ".png", ".gif", ".webp",
    ".mp3", ".m4a", ".ogg", ".pdf",
)


def detect_platform(url: str) -> str:
    """Return a human-readable platform name detected from the URL."""
    for name, pattern in PLATFORM_PATTERNS.items():
        if pattern.search(url):
            return name
    return "Direct Link"


def extract_url(text: str) -> str | None:
    """Pull the first http(s) URL out of a block of text, if any."""
    if not text:
        return None
    match = URL_REGEX.search(text)
    return match.group(1) if match else None


async def resolve_redirect(url: str) -> str:
    """Follow short/redirect links to their final canonical URL."""
    if not REDIRECT_DOMAINS.search(url):
        return url

    headers = {"User-Agent": DESKTOP_USER_AGENT}
    try:
        timeout = aiohttp.ClientTimeout(total=10)
        async with aiohttp.ClientSession(timeout=timeout, headers=headers) as session:
            async with session.get(url, allow_redirects=True) as resp:
                final_url = str(resp.url)
                if final_url:
                    logger.info("Resolved redirect link %s -> %s", url, final_url)
                    return final_url
    except Exception as exc:
        logger.info("Could not resolve redirect for %s (%s); using original URL", url, exc)

    return url


# =====================================================================
# PROGRESS TRACKING
# =====================================================================

class ProgressState:
    """Passes download progress from yt-dlp's thread to the async updater."""

    def __init__(self):
        self.percent: float = 0.0
        self.status: str = "starting"  # starting | downloading | processing | finished | error
        self.speed: str = ""
        self.eta: str = ""
        self.filename: str = ""

    def update_from_ytdlp(self, d: dict) -> None:
        status = d.get("status")
        if status == "downloading":
            self.status = "downloading"
            total = d.get("total_bytes") or d.get("total_bytes_estimate")
            downloaded = d.get("downloaded_bytes", 0)
            if total:
                self.percent = downloaded / total * 100
            self.speed = d.get("_speed_str", "").strip()
            self.eta = d.get("_eta_str", "").strip()
        elif status == "finished":
            self.status = "finished"
            self.percent = 100.0
            self.filename = d.get("filename", "")
        elif status == "error":
            self.status = "error"


def make_progress_bar(percent: float, width: int = 18) -> str:
    """Render a simple text-based progress bar."""
    percent = max(0.0, min(100.0, percent))
    filled = int(width * percent / 100)
    bar = "█" * filled + "░" * (width - filled)
    return f"[{bar}] {percent:5.1f}%"


async def progress_updater(
    message,
    state: ProgressState,
    platform: str,
    stop_event: asyncio.Event,
) -> None:
    """Periodically edits the status message until `stop_event` is set."""
    last_text = ""
    while not stop_event.is_set():
        try:
            if state.status == "downloading":
                text = (
                    f"⬇️ *Downloading from {platform}*\n\n"
                    f"`{make_progress_bar(state.percent)}`\n"
                    f"Speed: `{state.speed or 'N/A'}`  |  ETA: `{state.eta or 'N/A'}`"
                )
            elif state.status == "processing":
                text = "⚙️ *Processing video...*"
            elif state.status == "finished":
                text = f"✅ *Download complete!* Preparing to upload...\n\n`{make_progress_bar(100)}`"
            else:
                text = f"🔄 *Fetching info from {platform}...*"

            if text != last_text:
                await message.edit_text(text, parse_mode=ParseMode.MARKDOWN)
                last_text = text
        except TelegramError:
            pass
        except Exception as exc:  # pragma: no cover - defensive
            logger.debug("Progress updater non-fatal error: %s", exc)

        try:
            await asyncio.wait_for(stop_event.wait(), timeout=PROGRESS_EDIT_INTERVAL)
        except asyncio.TimeoutError:
            continue


# =====================================================================
# DOWNLOAD LOGIC
# =====================================================================

def _base_ydl_opts() -> dict:
    """Options shared by every yt-dlp call (info lookup and download)."""
    opts = {
        "noplaylist": True,
        "quiet": True,
        "no_warnings": True,
        "restrictfilenames": True,
        "retries": 5,
        "socket_timeout": 30,
        "http_headers": {"User-Agent": DESKTOP_USER_AGENT},
        "extractor_retries": 3,
    }
    # Use the logged-in cookies if available (needed on Render for YouTube).
    if COOKIES_FILE.exists():
        opts["cookiefile"] = str(COOKIES_FILE)
    return opts


def build_format(quality: str) -> str:
    """
    Turn a quality choice into a yt-dlp format selector.
      "audio"   -> audio only
      "360"...  -> best video up to that height (+ best audio)
      "auto"    -> best single pre-merged file
    """
    if quality == "audio":
        return "bestaudio[ext=m4a]/bestaudio/best"
    if quality.isdigit():
        h = int(quality)
        if FFMPEG_EXE:
            return (
                f"bv*[height<={h}][ext=mp4]+ba[ext=m4a]"
                f"/bv*[height<={h}]+ba"
                f"/b[height<={h}][ext=mp4]/b[height<={h}]/best"
            )
        return f"b[height<={h}][ext=mp4]/b[height<={h}]/best"
    return "best[ext=mp4]/best"


def _extract_info(url: str) -> dict:
    """Blocking: fetch video metadata (title, duration, formats) only."""
    with yt_dlp.YoutubeDL({**_base_ydl_opts(), "skip_download": True}) as ydl:
        info = ydl.extract_info(url, download=False)
    if info and info.get("entries"):
        info = next((e for e in info["entries"] if e), info)
    return info


def _run_ytdlp_download(
    url: str, out_dir: Path, state: ProgressState, quality: str = "auto"
) -> tuple[Path, float | None]:
    """Blocking yt-dlp download. Returns (file path, duration or None)."""
    ydl_opts = {
        **_base_ydl_opts(),
        "format": build_format(quality),
        "outtmpl": str(out_dir / "%(title).80s.%(ext)s"),
        "progress_hooks": [state.update_from_ytdlp],
    }
    if FFMPEG_EXE:
        ydl_opts["ffmpeg_location"] = str(FFMPEG_EXE.parent)
        ydl_opts["merge_output_format"] = "mp4"

    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
        info = ydl.extract_info(url, download=True)
        if "entries" in info and info["entries"]:
            info = info["entries"][0]

        path = None
        downloads = info.get("requested_downloads") or []
        if downloads and downloads[0].get("filepath"):
            path = Path(downloads[0]["filepath"])
        if path is None or not path.exists():
            path = Path(ydl.prepare_filename(info))
        if not path.exists():
            files = [f for f in out_dir.iterdir() if f.is_file()]
            if files:
                path = max(files, key=lambda f: f.stat().st_size)
        return path, info.get("duration")


async def download_via_ytdlp(
    url: str, out_dir: Path, state: ProgressState, quality: str = "auto"
) -> tuple[Path, float | None]:
    """Async wrapper that runs the blocking yt-dlp download in a thread."""
    return await asyncio.to_thread(_run_ytdlp_download, url, out_dir, state, quality)


async def download_direct_link(url: str, out_dir: Path, state: ProgressState) -> Path:
    """Fallback downloader for plain direct media links."""
    state.status = "downloading"

    name_guess = url.split("?")[0].rstrip("/").split("/")[-1] or "file"
    if "." not in name_guess:
        name_guess += ".bin"
    dest_path = out_dir / name_guess

    timeout = aiohttp.ClientTimeout(total=None, sock_connect=30, sock_read=60)
    async with aiohttp.ClientSession(timeout=timeout) as session:
        async with session.get(url) as resp:
            resp.raise_for_status()
            total = int(resp.headers.get("Content-Length", 0))
            downloaded = 0

            with open(dest_path, "wb") as f:
                async for chunk in resp.content.iter_chunked(1024 * 256):
                    f.write(chunk)
                    downloaded += len(chunk)
                    if total:
                        state.percent = downloaded / total * 100

    state.status = "finished"
    state.percent = 100.0
    return dest_path


async def is_direct_media_url(url: str) -> bool:
    """Heuristic check: does this URL point straight at a media file?"""
    lowered = url.split("?")[0].lower()
    if lowered.endswith(DIRECT_MEDIA_EXTENSIONS):
        return True
    try:
        timeout = aiohttp.ClientTimeout(total=10)
        async with aiohttp.ClientSession(timeout=timeout) as session:
            async with session.head(url, allow_redirects=True) as resp:
                content_type = resp.headers.get("Content-Type", "")
                return content_type.startswith(("video/", "image/", "audio/"))
    except Exception:
        return False


async def download_media(
    url: str, out_dir: Path, state: ProgressState, quality: str = "auto"
) -> tuple[Path, float | None]:
    """Master download dispatcher. Returns (file path, duration or None)."""
    url = await resolve_redirect(url)

    try:
        return await download_via_ytdlp(url, out_dir, state, quality)
    except Exception as ytdlp_error:
        logger.info("yt-dlp could not handle URL, trying direct download: %s", ytdlp_error)
        if await is_direct_media_url(url):
            return await download_direct_link(url, out_dir, state), None

        raise friendly_download_error(ytdlp_error) from ytdlp_error


def friendly_download_error(exc: Exception) -> Exception:
    """Turn common yt-dlp failures into a clearer message for the user."""
    text = str(exc).lower()
    if "not a bot" in text or "sign in to confirm" in text:
        return RuntimeError(
            "YouTube is blocking this server ('confirm you're not a bot'). "
            "Your cookies may be missing or expired - export a fresh "
            "cookies.txt and update the Render Secret File."
        )
    if "login" in text or "rate-limit" in text or "private" in text:
        return RuntimeError(
            "This content requires a logged-in session to access (common for "
            "Instagram/Facebook Reels). Add a browser-exported 'cookies.txt' "
            "as a Render Secret File to enable access to this kind of link."
        )
    return exc


# =====================================================================
# LONG VIDEO SUPPORT: SIZE ESTIMATES + SPLITTING INTO TELEGRAM-SIZED PARTS
# =====================================================================

QUALITY_HEIGHTS = (360, 480, 720)


def is_youtube_short(url: str) -> bool:
    return "/shorts/" in url.lower()


def format_duration(seconds: float | int | None) -> str:
    if not seconds:
        return "unknown"
    seconds = int(seconds)
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"


def estimate_size(info: dict, quality: str) -> int | None:
    """Rough size in bytes of the file a quality choice would produce."""
    formats = info.get("formats") or []
    duration = info.get("duration") or 0

    def size_of(f: dict) -> int | None:
        s = f.get("filesize") or f.get("filesize_approx")
        if s:
            return int(s)
        tbr = f.get("tbr")
        if tbr and duration:
            return int(tbr * 1000 / 8 * duration)
        return None

    audio = [
        f for f in formats
        if f.get("vcodec") in (None, "none") and f.get("acodec") not in (None, "none")
    ]
    m4a = [f for f in audio if f.get("ext") == "m4a"]
    audio_sizes = [s for s in (size_of(f) for f in (m4a or audio)) if s]
    best_audio = max(audio_sizes) if audio_sizes else 0

    if quality == "audio":
        return best_audio or None

    h = int(quality)
    video = [
        f for f in formats
        if f.get("vcodec") not in (None, "none") and f.get("height") and f["height"] <= h
    ]
    if not video:
        return None
    best = max(video, key=lambda f: (f["height"], f.get("tbr") or 0))
    v_size = size_of(best)
    if not v_size:
        return None
    has_audio = best.get("acodec") not in (None, "none")
    return v_size + (0 if has_audio else best_audio)


def _ffmpeg_duration(path: Path) -> float | None:
    """Read a media file's duration by parsing `ffmpeg -i` output."""
    if not FFMPEG_EXE:
        return None
    result = subprocess.run(
        [str(FFMPEG_EXE), "-hide_banner", "-i", str(path)],
        capture_output=True, text=True,
    )
    m = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", result.stderr)
    if not m:
        return None
    return int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))


def split_file(path: Path, out_dir: Path, duration: float | None = None) -> list[Path]:
    """
    Blocking: split a media file into parts that each fit under Telegram's
    50 MB bot upload limit, using `-c copy` (no re-encoding).
    """
    size = path.stat().st_size
    if size <= SAFE_UPLOAD_SIZE:
        return [path]
    if not FFMPEG_EXE:
        raise RuntimeError(
            "The file is larger than Telegram's 50MB limit and ffmpeg is not "
            "available to split it. Add `imageio-ffmpeg` to requirements.txt."
        )

    duration = _ffmpeg_duration(path) or duration
    if not duration:
        raise RuntimeError("Could not read the video length, so it cannot be split.")

    ext = path.suffix
    seg_seconds = duration * SPLIT_TARGET_SIZE / size
    for _attempt in range(4):
        for old in out_dir.glob(f"part_*{ext}"):
            old.unlink()
        cmd = [
            str(FFMPEG_EXE), "-hide_banner", "-loglevel", "error", "-y",
            "-i", str(path),
            "-map", "0:v?", "-map", "0:a?",
            "-c", "copy",
            "-f", "segment",
            "-segment_time", str(int(max(seg_seconds, 5))),
            "-reset_timestamps", "1",
            str(out_dir / f"part_%03d{ext}"),
        ]
        result = subprocess.run(cmd, capture_output=True, text=True)
        parts = sorted(out_dir.glob(f"part_*{ext}"))
        if result.returncode != 0 or not parts:
            raise RuntimeError(f"Splitting failed: {result.stderr.strip()[:200]}")
        if all(p.stat().st_size <= SAFE_UPLOAD_SIZE for p in parts):
            path.unlink(missing_ok=True)  # free disk space
            return parts
        seg_seconds *= 0.75

    raise RuntimeError("Could not split the file into parts small enough for Telegram.")


async def send_media_file(bot, chat_id: int, path: Path, caption: str) -> None:
    """Upload one file to the chat using the most suitable Telegram method."""
    ext = path.suffix.lower()
    kwargs = dict(caption=caption, parse_mode=ParseMode.MARKDOWN, **UPLOAD_TIMEOUTS)
    with open(path, "rb") as media_file:
        if ext in (".jpg", ".jpeg", ".png", ".webp"):
            await bot.send_photo(chat_id, media_file, **kwargs)
        elif ext in (".mp3", ".m4a", ".ogg"):
            await bot.send_audio(chat_id, media_file, **kwargs)
        elif ext in (".mp4", ".mov", ".mkv", ".webm", ".3gp"):
            await bot.send_video(chat_id, media_file, supports_streaming=True, **kwargs)
        else:
            await bot.send_document(chat_id, media_file, **kwargs)


# =====================================================================
# TELEGRAM HANDLERS
# =====================================================================

WELCOME_MESSAGE = (
    "👋 *Welcome to the Universal Media Downloader Bot!*\n\n"
    "Send me a link from any of the platforms below and I'll fetch the "
    "highest quality media for you, straight into this chat. 🎬📥\n\n"
    "*Supported platforms:*\n"
    "▫️ YouTube (Long videos & Shorts)\n"
    "▫️ Instagram (Reels & Posts)\n"
    "▫️ Facebook (Videos & Reels)\n"
    "▫️ TikTok\n"
    "▫️ X (Twitter)\n"
    "▫️ Threads\n"
    "▫️ Likee\n"
    "▫️ Snapchat (Public)\n"
    "▫️ WhatsApp (Direct/Public media links)\n\n"
    "Just paste a link below to get started! 🚀"
)

HELP_MESSAGE = (
    "🛠 *How to use this bot:*\n\n"
    "1️⃣ Copy a link from any supported platform.\n"
    "2️⃣ Paste it here in the chat.\n"
    "3️⃣ Wait while I download it — you'll see a live progress bar.\n"
    "4️⃣ Receive your media file right here!\n\n"
    "🎬 *YouTube:* you can pick 360p / 480p / 720p or audio only.\n"
    "📦 Telegram bots can only upload 50MB per file, so bigger videos are "
    "automatically split into several parts (lower quality = fewer parts)."
)


def main_keyboard() -> InlineKeyboardMarkup:
    """Build the inline keyboard shown on the welcome message."""
    buttons = [
        [
            InlineKeyboardButton("ℹ️ Help", callback_data="help"),
            InlineKeyboardButton("📋 Supported Sites", callback_data="platforms"),
        ],
    ]
    return InlineKeyboardMarkup(buttons)


async def start_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.message.reply_text(
        WELCOME_MESSAGE,
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=main_keyboard(),
        disable_web_page_preview=True,
    )


async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.message.reply_text(HELP_MESSAGE, parse_mode=ParseMode.MARKDOWN)


async def button_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Handle inline keyboard button presses."""
    query = update.callback_query
    await query.answer()
    data = query.data or ""

    if data == "help":
        await query.message.reply_text(HELP_MESSAGE, parse_mode=ParseMode.MARKDOWN)
    elif data == "platforms":
        platforms_text = "📋 *Supported Platforms:*\n\n" + "\n".join(
            f"▫️ {name}" for name in PLATFORM_PATTERNS.keys()
        )
        await query.message.reply_text(platforms_text, parse_mode=ParseMode.MARKDOWN)
    elif data.startswith(("dl|", "cancel|")):
        action, token, *rest = data.split("|")
        pending = context.user_data.get("pending", {})
        request = pending.pop(token, None)

        if request is None:
            await query.message.edit_text(
                "⌛ This request has expired. Please send the link again."
            )
            return
        if action == "cancel":
            await query.message.edit_text("❌ Cancelled.")
            return

        quality = rest[0] if rest else "auto"
        await query.message.edit_text("⏳ Preparing download...")
        await process_download(
            context, query.message.chat_id, query.message,
            request["url"], "YouTube", quality,
        )


async def ask_quality(message, context: ContextTypes.DEFAULT_TYPE, url: str) -> None:
    """
    For regular (long) YouTube videos: look up the video, then let the user
    pick a quality. Big files are split into parts automatically.
    """
    status = await message.reply_text("🔎 Fetching video info...")
    try:
        info = await asyncio.to_thread(_extract_info, url)
    except Exception as exc:
        logger.info("Info lookup failed for %s: %s", url, exc)
        error_text = str(friendly_download_error(exc)).replace("`", "'")[:300]
        await status.edit_text(f"❌ Could not read this video.\n\n{error_text}")
        return

    if info.get("is_live"):
        await status.edit_text("⚠️ Live streams are not supported.")
        return

    duration = info.get("duration") or 0
    if duration > MAX_DURATION_SECONDS:
        await status.edit_text(
            f"⚠️ This video is too long ({format_duration(duration)}). "
            f"The limit is {MAX_DURATION_SECONDS // 60} minutes."
        )
        return

    heights_available = [f["height"] for f in info.get("formats") or [] if f.get("height")]
    max_height = max(heights_available) if heights_available else 10_000
    offered = [h for h in QUALITY_HEIGHTS if h <= max_height] or [QUALITY_HEIGHTS[0]]

    def label(icon: str, name: str, quality: str) -> str:
        size = estimate_size(info, quality)
        if not size:
            return f"{icon} {name}"
        text = f"{icon} {name} · ~{size / (1024 * 1024):.0f} MB"
        if size > SAFE_UPLOAD_SIZE:
            text += f" ({-(-size // SPLIT_TARGET_SIZE)} parts)"
        return text

    token = uuid.uuid4().hex[:8]
    pending = context.user_data.setdefault("pending", {})
    while len(pending) >= 20:  # keep memory use small
        pending.pop(next(iter(pending)))
    pending[token] = {"url": url}

    rows = [
        [InlineKeyboardButton(label("🎬", f"{h}p", str(h)), callback_data=f"dl|{token}|{h}")]
        for h in offered
    ]
    rows.append([InlineKeyboardButton(label("🎵", "Audio only", "audio"), callback_data=f"dl|{token}|audio")])
    rows.append([InlineKeyboardButton("❌ Cancel", callback_data=f"cancel|{token}")])

    title = escape_markdown(str(info.get("title") or "Video")[:100], version=1)
    await status.edit_text(
        f"🎬 *{title}*\n"
        f"⏱ Duration: `{format_duration(duration)}`\n\n"
        "Choose a quality. Files over 50MB are sent in several parts.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=InlineKeyboardMarkup(rows),
    )


async def process_download(
    context: ContextTypes.DEFAULT_TYPE,
    chat_id: int,
    status_message,
    url: str,
    platform: str,
    quality: str = "auto",
) -> None:
    """Download `url`, split it if it is too big, and upload it to the chat."""
    job_dir = DOWNLOAD_DIR / f"{chat_id}_{int(time.time() * 1000)}"
    job_dir.mkdir(parents=True, exist_ok=True)

    state = ProgressState()
    stop_event = asyncio.Event()
    updater_task = asyncio.create_task(
        progress_updater(status_message, state, platform, stop_event)
    )

    try:
        async with DOWNLOAD_SLOTS:  # limit simultaneous downloads
            await context.bot.send_chat_action(chat_id=chat_id, action=ChatAction.UPLOAD_VIDEO)
            file_path, duration = await download_media(url, job_dir, state, quality)

        stop_event.set()
        await updater_task

        if not file_path.exists():
            raise FileNotFoundError("Downloaded file could not be located on disk.")

        if file_path.stat().st_size > SAFE_UPLOAD_SIZE:
            await status_message.edit_text(
                "✂️ *Large file — splitting into parts...*", parse_mode=ParseMode.MARKDOWN
            )
            parts = await asyncio.to_thread(split_file, file_path, job_dir, duration)
        else:
            parts = [file_path]

        total = len(parts)
        for i, part in enumerate(parts, start=1):
            await status_message.edit_text(
                f"📤 *Uploading to Telegram...* ({i}/{total})", parse_mode=ParseMode.MARKDOWN
            )
            caption = f"✅ Downloaded from *{platform}*"
            if total > 1:
                caption += f"\n📦 Part {i}/{total}"
            await send_media_file(context.bot, chat_id, part, caption)
            part.unlink(missing_ok=True)  # free disk space as we go

        await status_message.delete()

    except (TimedOut, NetworkError) as net_err:
        logger.warning("Network error while handling %s: %s", url, net_err)
        await status_message.edit_text(
            "🌐 *Network error occurred.* Please try again in a moment.",
            parse_mode=ParseMode.MARKDOWN,
        )
    except Exception as exc:
        logger.exception("Failed to process URL %s", url)
        error_text = str(exc).replace("`", "'")
        if len(error_text) > 300:
            error_text = error_text[:300] + "..."
        await status_message.edit_text(
            f"❌ *Download failed for {platform}.*\n\n`{error_text}`\n\n"
            "This may be a private/unavailable post, an unsupported link, "
            "or a temporary platform restriction.",
            parse_mode=ParseMode.MARKDOWN,
        )
    finally:
        stop_event.set()
        if not updater_task.done():
            try:
                await updater_task
            except Exception:
                pass
        shutil.rmtree(job_dir, ignore_errors=True)


async def handle_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """
    Main message handler: finds a link in the incoming message.
    Regular YouTube videos -> ask for a quality first.
    Everything else -> download straight away.
    """
    message = update.message
    if message is None or not message.text:
        return

    url = extract_url(message.text)
    if not url:
        await message.reply_text(
            "🤔 I couldn't find a valid link in your message.\n"
            "Please send a direct link from a supported platform.",
        )
        return

    platform = detect_platform(url)

    if platform == "YouTube" and not is_youtube_short(url):
        await ask_quality(message, context, url)
        return

    status_message = await message.reply_text(
        f"🔎 *Detected platform:* {platform}\n⏳ Preparing download...",
        parse_mode=ParseMode.MARKDOWN,
    )
    await process_download(context, message.chat_id, status_message, url, platform, "auto")


async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Global error handler to catch anything unhandled elsewhere."""
    logger.error("Unhandled exception: %s", context.error, exc_info=context.error)
    if isinstance(update, Update) and update.effective_message:
        try:
            await update.effective_message.reply_text(
                "⚠️ An unexpected error occurred. Please try again."
            )
        except Exception:
            pass


# =====================================================================
# KEEP-ALIVE WEB SERVER (for Render's free Web Service tier)
# =====================================================================

class _KeepAliveHandler(BaseHTTPRequestHandler):
    def do_GET(self):  # noqa: N802
        self.send_response(200)
        self.send_header("Content-Type", "text/plain")
        self.end_headers()
        self.wfile.write(b"Bot is alive and running.")

    def log_message(self, format, *args):  # noqa: A002
        pass


def start_keep_alive_server() -> None:
    """Start the keep-alive HTTP server if a PORT has been provided."""
    if not PORT:
        return

    def _serve():
        server = HTTPServer(("0.0.0.0", int(PORT)), _KeepAliveHandler)
        logger.info("Keep-alive web server listening on port %s", PORT)
        server.serve_forever()

    thread = threading.Thread(target=_serve, daemon=True)
    thread.start()


# =====================================================================
# APPLICATION ENTRY POINT
# =====================================================================

def build_application() -> Application:
    """Construct and configure the python-telegram-bot Application."""
    if not BOT_TOKEN:
        raise RuntimeError(
            "BOT_TOKEN is missing. Create a '.env' file next to bot.py containing:\n"
            "    BOT_TOKEN=your_telegram_bot_token_here"
        )

    app = ApplicationBuilder().token(BOT_TOKEN).concurrent_updates(True).build()

    app.add_handler(CommandHandler("start", start_command))
    app.add_handler(CommandHandler("help", help_command))
    app.add_handler(CallbackQueryHandler(button_callback))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_message))
    app.add_error_handler(error_handler)

    return app


def main() -> None:
    """Entry point: build the bot and start polling for updates."""
    logger.info("Starting Telegram Universal Media Downloader Bot...")
    start_keep_alive_server()
    application = build_application()
    application.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)


if __name__ == "__main__":
    main()
