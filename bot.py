
import os
import re
import sys
import json
import html as html_lib
import importlib.util
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
    InputMediaPhoto,
    InputMediaVideo,
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
from telegram.error import TelegramError, TimedOut, NetworkError, BadRequest

# =====================================================================
# CONFIGURATION
# =====================================================================

load_dotenv()  # Load BOT_TOKEN from a local .env file

BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()

# Render (and similar free hosting platforms) only allow *Web Services*
# on the free tier, and a Web Service must bind to a port so Render's
# health check passes. This env var is automatically set by Render;
# it will be absent when running locally in Pydroid 3, in which case
# the keep-alive server below simply never starts.
PORT = os.getenv("PORT")

# Folder where media is temporarily downloaded before being sent
DOWNLOAD_DIR = Path("downloads")
DOWNLOAD_DIR.mkdir(exist_ok=True)

# Telegram bot API upload limit for standard (non-local) servers is 50 MB.
# Files bigger than SAFE_UPLOAD_SIZE are automatically split into parts of
# roughly SPLIT_TARGET_SIZE each (a bit of headroom because parts cut
# without re-encoding never come out at exactly the requested size).
SAFE_UPLOAD_SIZE = 49 * 1024 * 1024   # anything above this gets split
SPLIT_TARGET_SIZE = 44 * 1024 * 1024  # target size of each part

# Longest YouTube video (in minutes) the bot will accept. Free hosting has
# limited disk/CPU, so very long videos are refused. Override on Render
# with an environment variable named MAX_VIDEO_MINUTES.
MAX_DURATION_SECONDS = int(os.getenv("MAX_VIDEO_MINUTES", "120")) * 60

# How many downloads may run at the same time (free plan = small CPU/RAM)
DOWNLOAD_SLOTS = asyncio.Semaphore(int(os.getenv("MAX_CONCURRENT_DOWNLOADS", "2")))

# Large uploads need generous timeouts (python-telegram-bot's defaults of
# a few seconds would abort a big upload).
UPLOAD_TIMEOUTS = dict(read_timeout=600, write_timeout=600, connect_timeout=30, pool_timeout=30)

# How often (in seconds) the progress message is allowed to be edited.
# Telegram rate-limits message edits, so we throttle updates.
PROGRESS_EDIT_INTERVAL = 3

# Many "Lite" app share links (Facebook Lite, TikTok Lite, mobile
# Instagram) get blocked or served a stripped-down page when requests
# arrive without a normal desktop browser User-Agent. Sending one makes
# extraction far more reliable.
DESKTOP_USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)

# Optional cookies file (Netscape format, exported from a logged-in
# browser session) placed next to bot.py. Instagram and Facebook
# increasingly require a logged-in session to view Reels/videos, even
# ones that are technically public. If this file exists it is used
# automatically; if not, the bot just proceeds without it (some public
# content will still work fine without cookies).
COOKIES_FILE = Path("cookies.txt")


def _prepare_cookies() -> None:
    """
    Create ./cookies.txt from a Render Secret File or a COOKIES_TXT env var
    (the cookies are never stored in this source file). On Render use ONE of:
      1) Secret File named  cookies.txt   (lands in /etc/secrets/)
      2) Environment variable  COOKIES_TXT  (the whole file contents)
    """
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
    shipped by the `imageio-ffmpeg` pip package -- this works on Render's
    free plan where you can't apt-install anything. Returns None when no
    ffmpeg can be found (the bot then falls back to single-file formats and
    cannot split large files).
    """
    exe = shutil.which("ffmpeg")
    if not exe:
        try:
            import imageio_ffmpeg
            exe = imageio_ffmpeg.get_ffmpeg_exe()
        except Exception:
            return None
    # yt-dlp looks for a binary literally named "ffmpeg", so expose it
    # under that name in a local folder.
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
# Silence overly chatty libraries
logging.getLogger("httpx").setLevel(logging.WARNING)
logger = logging.getLogger("MediaDownloaderBot")

if COOKIES_FILE.exists():
    logger.info("cookies.txt found (%d bytes) - will be used by yt-dlp / gallery-dl", COOKIES_FILE.stat().st_size)
else:
    logger.info("No cookies.txt found - YouTube / Instagram may block this server")


# =====================================================================
# PLATFORM DETECTION
# =====================================================================

# Regex patterns used to recognize which platform a link belongs to.
# These are used only for display purposes ("Detected: YouTube" etc.)
# yt-dlp itself decides internally whether it can actually extract media.
PLATFORM_PATTERNS = {
    "YouTube": re.compile(r"(youtube\.com|youtu\.be)", re.IGNORECASE),
    # Instagram share links are the same domain regardless of the app
    # (regular or Lite), so a single pattern covers both.
    "Instagram": re.compile(r"instagram\.com", re.IGNORECASE),
    # Facebook Lite / mobile shares commonly use m., mbasic., web., or
    # the fb.watch short-link domain instead of plain facebook.com.
    "Facebook": re.compile(
        r"((m|mbasic|web|touch|beta)\.facebook\.com|facebook\.com|fb\.watch)",
        re.IGNORECASE,
    ),
    # TikTok Lite shares are frequently shortened links on vm./vt./m.
    # subdomains rather than the full www.tiktok.com URL.
    "TikTok": re.compile(r"((vm|vt|m)\.tiktok\.com|tiktok\.com)", re.IGNORECASE),
    "X (Twitter)": re.compile(r"(twitter\.com|x\.com)", re.IGNORECASE),
    "Threads": re.compile(r"threads\.(net|com)", re.IGNORECASE),
    "Likee": re.compile(r"likee\.(video|com)", re.IGNORECASE),
    "Snapchat": re.compile(r"snapchat\.com", re.IGNORECASE),
    "WhatsApp": re.compile(r"whatsapp\.(com|net)", re.IGNORECASE),
}

# Short/redirect-style link domains that need to be resolved to their
# final canonical URL before being handed to yt-dlp. "Lite" versions of
# apps (Facebook Lite, TikTok Lite) frequently generate share links on
# these shortened domains, and yt-dlp's extractors sometimes expect the
# fully-resolved URL rather than the short one.
REDIRECT_DOMAINS = re.compile(
    r"(vm\.tiktok\.com|vt\.tiktok\.com|fb\.watch|mbasic\.facebook\.com)",
    re.IGNORECASE,
)

# A generic URL matcher used to pull the first link out of any message
URL_REGEX = re.compile(r"(https?://[^\s]+)", re.IGNORECASE)

# File extensions considered "direct media" for the raw-download fallback
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
    """
    Follow short/redirect links (e.g. vm.tiktok.com, fb.watch,
    mbasic.facebook.com) to their final canonical URL.

    "Lite" apps (Facebook Lite, TikTok Lite) very often generate these
    shortened share links, and some extractors fail on the short form
    even though they work fine once the link is resolved. If anything
    goes wrong here we simply fall back to the original URL so the
    download attempt can still proceed.
    """
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
    """
    Small thread-safe-ish container used to pass download progress
    from yt-dlp's synchronous progress_hook (which runs in a worker
    thread) to the async task that periodically edits the Telegram
    status message.
    """

    def __init__(self):
        self.percent: float = 0.0
        self.status: str = "starting"  # starting | downloading | processing | finished | error
        self.speed: str = ""
        self.eta: str = ""
        self.filename: str = ""

    def update_from_ytdlp(self, d: dict) -> None:
        """Called synchronously by yt-dlp on its download thread."""
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
    """
    Background task that periodically edits the status message with
    the latest download progress until `stop_event` is set.
    """
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
            # Ignore "message not modified" and transient edit failures
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
        # A normal desktop User-Agent avoids the stripped-down / blocked
        # responses that "Lite" app share links (Facebook Lite, TikTok
        # Lite, mobile Instagram) sometimes trigger.
        "http_headers": {"User-Agent": DESKTOP_USER_AGENT},
        "extractor_retries": 3,
    }
    # If the user has provided a browser-exported cookies.txt, use it.
    # Needed for Instagram/Facebook Reels, and very often for YouTube too
    # when the bot runs on a datacenter IP (Render) -- YouTube then asks
    # "Sign in to confirm you're not a bot".
    if COOKIES_FILE.exists():
        opts["cookiefile"] = str(COOKIES_FILE)
    return opts


def build_format(quality: str) -> str:
    """
    Turn a quality choice into a yt-dlp format selector.
      "audio"   -> audio only
      "360"...  -> best video up to that height (+ best audio)
      "auto"    -> best single pre-merged file (original behaviour)
    HD YouTube streams come as separate video + audio files, so merging
    them needs ffmpeg. Without ffmpeg we fall back to single-file formats.
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


# ---------------------------------------------------------------------
# File types
# ---------------------------------------------------------------------
PHOTO_EXTS = (".jpg", ".jpeg", ".png", ".webp")
VIDEO_EXTS = (".mp4", ".mov", ".mkv", ".webm", ".3gp", ".m4v")
AUDIO_EXTS = (".mp3", ".m4a", ".ogg", ".aac", ".opus")
MEDIA_EXTS = PHOTO_EXTS + VIDEO_EXTS + AUDIO_EXTS + (".gif",)

MAX_PHOTO_SIZE = 10 * 1024 * 1024  # Telegram refuses photos above 10 MB
MAX_POST_FILES = 20                # max photos/videos taken from one post

# Sites where gallery-dl is used as a helper for photo posts / carousels
GALLERY_DL_PLATFORMS = ("Instagram", "TikTok", "X (Twitter)", "Threads")
GALLERY_DL_OK = importlib.util.find_spec("gallery_dl") is not None


def collect_media_files(out_dir: Path) -> list[Path]:
    """All photos/videos in `out_dir`, in the order they were downloaded."""
    files = [f for f in out_dir.iterdir() if f.is_file() and f.suffix.lower() in MEDIA_EXTS]
    # Photo posts (TikTok slideshows...) come with a background-music track:
    # skip it when there are photos/videos.
    visual = [f for f in files if f.suffix.lower() not in AUDIO_EXTS]
    if visual:
        files = visual
    return sorted(files, key=lambda f: f.stat().st_mtime_ns)[:MAX_POST_FILES]


def _clear_dir(out_dir: Path) -> None:
    """Remove leftovers of a failed attempt before trying the next method."""
    for f in out_dir.iterdir():
        if f.is_file():
            f.unlink(missing_ok=True)


def _run_ytdlp_download(
    url: str, out_dir: Path, state: ProgressState, quality: str = "auto"
) -> tuple[list[Path], float | None]:
    """
    Blocking yt-dlp download (run inside a worker thread).
    Returns (list of downloaded files, duration in seconds or None).
    A post with several videos (Instagram carousel) gives several files.
    """
    ydl_opts = {
        **_base_ydl_opts(),
        "format": build_format(quality),
        "outtmpl": str(out_dir / "%(title).60s_%(id)s.%(ext)s"),
        "progress_hooks": [state.update_from_ytdlp],
        "playlist_items": f"1-{MAX_POST_FILES}",
    }
    if FFMPEG_EXE:
        ydl_opts["ffmpeg_location"] = str(FFMPEG_EXE.parent)
        ydl_opts["merge_output_format"] = "mp4"

    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
        info = ydl.extract_info(url, download=True)

    duration = None
    if info and not info.get("entries"):
        duration = info.get("duration")

    files = collect_media_files(out_dir)
    if not files:
        raise RuntimeError("yt-dlp finished but no media file was found.")
    return files, duration


async def download_via_ytdlp(
    url: str, out_dir: Path, state: ProgressState, quality: str = "auto"
) -> tuple[list[Path], float | None]:
    """Async wrapper that runs the blocking yt-dlp download in a thread."""
    return await asyncio.to_thread(_run_ytdlp_download, url, out_dir, state, quality)


# ---------------------------------------------------------------------
# gallery-dl: photo posts and mixed photo+video posts
# (Instagram posts/carousels, TikTok photo slideshows, X image tweets)
# ---------------------------------------------------------------------

async def download_via_gallery_dl(url: str, out_dir: Path, state: ProgressState) -> list[Path]:
    """Download every photo/video of a post with the gallery-dl tool."""
    state.status = "downloading"
    state.percent = 0.0

    cmd = [
        sys.executable, "-m", "gallery_dl",
        "-D", str(out_dir),             # put files straight into out_dir
        "--range", f"1-{MAX_POST_FILES}",
        "-o", "audio=false",            # no separate music file for TikTok
    ]
    if COOKIES_FILE.exists():
        cmd += ["--cookies", str(COOKIES_FILE)]
    cmd.append(url)

    proc = await asyncio.create_subprocess_exec(
        *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
    )
    try:
        _out, err = await asyncio.wait_for(proc.communicate(), timeout=300)
    except asyncio.TimeoutError:
        proc.kill()
        raise RuntimeError("gallery-dl timed out.")

    files = collect_media_files(out_dir)
    if not files:
        message = err.decode("utf-8", "ignore").strip()[-300:] or "gallery-dl found no media."
        raise RuntimeError(message)

    state.status = "finished"
    state.percent = 100.0
    return files


# ---------------------------------------------------------------------
# Threads (threads.net / threads.com): yt-dlp has no extractor for it, so
# we read the public post page and pick the media out of its embedded JSON.
# ---------------------------------------------------------------------

def _threads_items_from_post(post: dict) -> list[tuple[str, str]]:
    items: list[tuple[str, str]] = []
    for node in post.get("carousel_media") or [post]:
        videos = node.get("video_versions") or []
        if videos and videos[0].get("url"):
            items.append(("video", videos[0]["url"]))
            continue
        candidates = (node.get("image_versions2") or {}).get("candidates") or []
        if candidates and candidates[0].get("url"):
            items.append(("image", candidates[0]["url"]))
    return items


def parse_threads_media(page: str, url: str) -> list[tuple[str, str]]:
    """Return [("video"|"image", media_url), ...] for the post in `url`."""
    match = re.search(r"/(?:post|t)/([A-Za-z0-9_-]+)", url)
    code = match.group(1) if match else None

    posts: list[dict] = []

    def walk(node) -> None:
        if isinstance(node, dict):
            has_media = any(k in node for k in ("video_versions", "image_versions2", "carousel_media"))
            if has_media and (code is None or node.get("code") == code):
                posts.append(node)
                return
            for value in node.values():
                walk(value)
        elif isinstance(node, list):
            for value in node:
                walk(value)

    for blob in re.findall(r"<script[^>]*type=\"application/json\"[^>]*>(.*?)</script>", page, re.S):
        if "video_versions" not in blob and "image_versions2" not in blob and "carousel_media" not in blob:
            continue
        try:
            walk(json.loads(blob))
        except ValueError:
            continue

    items: list[tuple[str, str]] = []
    for post in posts:
        for item in _threads_items_from_post(post):
            if item not in items:
                items.append(item)

    if not items:  # fallback: the page's preview meta tags
        for kind, prop in (("video", "og:video"), ("image", "og:image")):
            m = re.search(rf'<meta[^>]+property="{prop}"[^>]+content="([^"]+)"', page)
            if m:
                items.append((kind, html_lib.unescape(m.group(1))))
                break
    return items[:MAX_POST_FILES]


async def download_threads(url: str, out_dir: Path, state: ProgressState) -> list[Path]:
    """Download the photos/videos of a public Threads post."""
    state.status = "downloading"
    state.percent = 0.0
    headers = {
        "User-Agent": DESKTOP_USER_AGENT,
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
    }
    timeout = aiohttp.ClientTimeout(total=None, sock_connect=30, sock_read=60)
    async with aiohttp.ClientSession(timeout=timeout, headers=headers) as session:
        async with session.get(url, allow_redirects=True) as resp:
            resp.raise_for_status()
            page = await resp.text()

        media = parse_threads_media(page, url)
        if not media:
            raise RuntimeError(
                "No photo or video found in this Threads post (it may be "
                "text-only, private, or Threads is asking for a login)."
            )

        files: list[Path] = []
        for index, (kind, media_url) in enumerate(media, start=1):
            dest = out_dir / f"threads_{index:02d}{'.mp4' if kind == 'video' else '.jpg'}"
            async with session.get(media_url) as resp:
                resp.raise_for_status()
                with open(dest, "wb") as f:
                    async for chunk in resp.content.iter_chunked(1024 * 256):
                        f.write(chunk)
            files.append(dest)
            state.percent = index / len(media) * 100

    state.status = "finished"
    state.percent = 100.0
    return files


async def download_direct_link(url: str, out_dir: Path, state: ProgressState) -> Path:
    """
    Fallback downloader for plain direct media links (used for WhatsApp
    media links, public Snapchat CDN links, or any raw file URL that
    yt-dlp does not recognize as a supported site).
    """
    state.status = "downloading"

    # Derive a reasonably sensible filename from the URL
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
    # Try a lightweight HEAD request to inspect the content type
    try:
        timeout = aiohttp.ClientTimeout(total=10)
        async with aiohttp.ClientSession(timeout=timeout) as session:
            async with session.head(url, allow_redirects=True) as resp:
                content_type = resp.headers.get("Content-Type", "")
                return content_type.startswith(("video/", "image/", "audio/"))
    except Exception:
        return False


def prefers_gallery_dl(url: str, platform: str) -> bool:
    """
    Posts that may contain photos go to gallery-dl first (yt-dlp only knows
    videos). Reels and normal TikTok videos stay with yt-dlp first.
    """
    lowered = url.lower()
    if platform == "TikTok":
        return "/photo/" in lowered
    if platform == "Instagram":
        return not any(part in lowered for part in ("/reel/", "/reels/"))
    return False


_AUTH_HINTS = re.compile(
    r"not a bot|sign in to confirm|login|log in|rate-limit|401|403|private|cookies",
    re.IGNORECASE,
)


def pick_error(errors: list[tuple[str, Exception]]) -> Exception:
    """
    The most useful error to show. Priority: a login/cookie problem, then
    anything reported by gallery-dl / the Threads reader (yt-dlp's own
    "No video formats found" is just noise for photo posts), then the last.
    """
    for _name, exc in errors:
        if _AUTH_HINTS.search(str(exc)):
            return exc
    for name, exc in errors:
        if name != "use_ytdlp":
            return exc
    return errors[-1][1]


async def download_media(
    url: str, out_dir: Path, state: ProgressState, quality: str = "auto"
) -> tuple[list[Path], float | None]:
    """
    Master download dispatcher. Returns (list of files, duration or None).
    Tries, in a sensible order for the site: yt-dlp (videos), a Threads
    reader, gallery-dl (photos / carousels) and finally a plain HTTP
    download for direct file links.
    """
    # Short share links (vm.tiktok.com, fb.watch...) -> final URL first.
    url = await resolve_redirect(url)
    platform = detect_platform(url)

    async def use_ytdlp():
        return await download_via_ytdlp(url, out_dir, state, quality)

    async def use_gallery_dl():
        return await download_via_gallery_dl(url, out_dir, state), None

    async def use_threads():
        return await download_threads(url, out_dir, state), None

    attempts = [use_ytdlp]
    if platform == "Threads":
        attempts.append(use_threads)
    if platform in GALLERY_DL_PLATFORMS and GALLERY_DL_OK:
        if prefers_gallery_dl(url, platform):
            attempts.insert(0, use_gallery_dl)
        else:
            attempts.append(use_gallery_dl)

    errors: list[tuple[str, Exception]] = []
    if platform in GALLERY_DL_PLATFORMS and not GALLERY_DL_OK:
        errors.append(("missing_gallery_dl", RuntimeError(
            "Photo posts need the 'gallery-dl' package, which is not installed. "
            "Add `gallery-dl` to requirements.txt and redeploy."
        )))
    for attempt in attempts:
        _clear_dir(out_dir)  # drop leftovers of a failed attempt
        state.status = "starting"
        state.percent = 0.0
        try:
            return await attempt()
        except Exception as exc:
            logger.info("%s failed for %s: %s", attempt.__name__, url, exc)
            errors.append((attempt.__name__, exc))

    _clear_dir(out_dir)
    if await is_direct_media_url(url):
        return [await download_direct_link(url, out_dir, state)], None

    raise friendly_download_error(pick_error(errors))


def friendly_download_error(exc: Exception) -> Exception:
    """Turn common yt-dlp failures into a clearer message for the user."""
    text = str(exc).lower()
    if "not a bot" in text or "sign in to confirm" in text:
        return RuntimeError(
            "YouTube is blocking this server ('confirm you're not a bot'). "
            "Your cookies may be missing or expired - export a fresh "
            "cookies.txt and update the Render Secret File."
        )
    if "login" in text or "log in" in text or "rate-limit" in text or "private" in text:
        return RuntimeError(
            "This content requires a logged-in session to access (common for "
            "Instagram/Facebook posts). Add a browser-exported 'cookies.txt' "
            "as a Render Secret File to enable access to this kind of link."
        )
    if "no video formats found" in text or "no video in this post" in text:
        return RuntimeError(
            "This post has no video (it is probably a photo post) and the photo "
            "downloader could not fetch it. Instagram usually needs a logged-in "
            "'cookies.txt' that contains instagram.com cookies - see the bot setup notes."
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


def split_file(
    path: Path, out_dir: Path, duration: float | None = None, prefix: str = "part"
) -> list[Path]:
    """
    Blocking: split a media file into parts that each fit under Telegram's
    50 MB bot upload limit. Uses `-c copy` (no re-encoding), so it is fast
    and lossless, and each part plays on its own. Cuts land on keyframes,
    so if any part still comes out too big we retry with shorter segments.
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
        for old in out_dir.glob(f"{prefix}_*{ext}"):
            old.unlink()
        cmd = [
            str(FFMPEG_EXE), "-hide_banner", "-loglevel", "error", "-y",
            "-i", str(path),
            "-map", "0:v?", "-map", "0:a?",
            "-c", "copy",
            "-f", "segment",
            "-segment_time", str(int(max(seg_seconds, 5))),
            "-reset_timestamps", "1",
            str(out_dir / f"{prefix}_%03d{ext}"),
        ]
        result = subprocess.run(cmd, capture_output=True, text=True)
        parts = sorted(out_dir.glob(f"{prefix}_*{ext}"))
        if result.returncode != 0 or not parts:
            raise RuntimeError(f"Splitting failed: {result.stderr.strip()[:200]}")
        if all(p.stat().st_size <= SAFE_UPLOAD_SIZE for p in parts):
            path.unlink(missing_ok=True)  # free disk space
            return parts
        seg_seconds *= 0.75  # some part was too big -> use shorter segments

    raise RuntimeError("Could not split the file into parts small enough for Telegram.")


async def safe_edit(message, text: str) -> None:
    """Edit a status message; ignore Telegram errors (e.g. 'not modified')."""
    try:
        await message.edit_text(text, parse_mode=ParseMode.MARKDOWN)
    except TelegramError:
        pass


def _kind(path: Path) -> str:
    """How a file should be sent: photo | video | audio | animation | document."""
    ext = path.suffix.lower()
    if ext in PHOTO_EXTS and path.stat().st_size <= MAX_PHOTO_SIZE:
        return "photo"
    if ext in VIDEO_EXTS:
        return "video"
    if ext in AUDIO_EXTS:
        return "audio"
    if ext == ".gif":
        return "animation"
    return "document"


async def _send_single(bot, chat_id: int, path: Path, caption: str | None) -> None:
    """Upload one file with the most suitable Telegram method."""
    kind = _kind(path)
    kwargs = dict(caption=caption, parse_mode=ParseMode.MARKDOWN, **UPLOAD_TIMEOUTS)
    try:
        with open(path, "rb") as media_file:
            if kind == "photo":
                await bot.send_photo(chat_id, media_file, **kwargs)
            elif kind == "video":
                await bot.send_video(chat_id, media_file, supports_streaming=True, **kwargs)
            elif kind == "audio":
                await bot.send_audio(chat_id, media_file, **kwargs)
            elif kind == "animation":
                await bot.send_animation(chat_id, media_file, **kwargs)
            else:
                await bot.send_document(chat_id, media_file, **kwargs)
    except BadRequest:
        if kind not in ("photo", "video"):
            raise
        # e.g. photo with odd dimensions -> send it as a plain file instead
        with open(path, "rb") as media_file:
            await bot.send_document(chat_id, media_file, **kwargs)


async def _send_album(bot, chat_id: int, paths: list[Path], caption: str | None) -> None:
    """Send up to 10 photos/videos together as one Telegram album."""
    handles = []
    try:
        media = []
        for index, path in enumerate(paths):
            handle = open(path, "rb")
            handles.append(handle)
            cap = caption if index == 0 else None
            if _kind(path) == "photo":
                media.append(InputMediaPhoto(handle, caption=cap, parse_mode=ParseMode.MARKDOWN))
            else:
                media.append(InputMediaVideo(
                    handle, caption=cap, parse_mode=ParseMode.MARKDOWN, supports_streaming=True
                ))
        await bot.send_media_group(chat_id, media, **UPLOAD_TIMEOUTS)
    finally:
        for handle in handles:
            handle.close()


async def deliver_files(
    bot, chat_id: int, status_message, files: list[Path], platform: str, duration: float | None
) -> None:
    """
    Send downloaded files to the chat. Several photos/videos of one post go
    out as albums; videos over 50MB are split into parts first.
    """
    base_caption = f"✅ Downloaded from *{platform}*"

    # 1) split anything too big for Telegram
    items: list[tuple[Path, str | None]] = []
    for index, f in enumerate(files):
        if f.stat().st_size > SAFE_UPLOAD_SIZE:
            if f.suffix.lower() not in VIDEO_EXTS + AUDIO_EXTS:
                raise RuntimeError(f"{f.name} is larger than Telegram's 50MB limit.")
            await safe_edit(status_message, "✂️ *Large file — splitting into parts...*")
            parts = await asyncio.to_thread(
                split_file, f, f.parent, duration if len(files) == 1 else None, f"p{index}"
            )
            items += [(p, f"📦 Part {i}/{len(parts)}") for i, p in enumerate(parts, start=1)]
        else:
            items.append((f, None))

    # 2) upload
    total = len(items)
    sent = 0
    first = True
    buffer: list[Path] = []

    async def flush() -> None:
        nonlocal sent, first, buffer
        if not buffer:
            return
        batch, buffer = buffer, []
        await safe_edit(status_message, f"📤 *Uploading to Telegram...* ({sent + len(batch)}/{total})")
        caption = base_caption if first else None
        if len(batch) == 1:
            await _send_single(bot, chat_id, batch[0], caption)
        else:
            try:
                await _send_album(bot, chat_id, batch, caption)
            except TimedOut:
                raise  # it may have been sent already -> do not send twice
            except TelegramError as exc:
                logger.info("Album failed (%s); sending files one by one", exc)
                for index, path in enumerate(batch):
                    await _send_single(bot, chat_id, path, caption if index == 0 else None)
        first = False
        sent += len(batch)
        for path in batch:
            path.unlink(missing_ok=True)  # free disk space as we go

    for path, label in items:
        if label is None and _kind(path) in ("photo", "video"):
            buffer.append(path)
            if len(buffer) == 10:  # Telegram album limit
                await flush()
            continue
        await flush()
        await safe_edit(status_message, f"📤 *Uploading to Telegram...* ({sent + 1}/{total})")
        caption = base_caption + (f"\n{label}" if label else "") if (label or first) else None
        await _send_single(bot, chat_id, path, caption)
        first = False
        sent += 1
        path.unlink(missing_ok=True)
    await flush()


# =====================================================================
# TELEGRAM HANDLERS
# =====================================================================

WELCOME_MESSAGE = (
    "👋 *Welcome to the Universal Media Downloader Bot!*\n\n"
    "Send me a link from any of the platforms below and I'll fetch the "
    "highest quality media for you, straight into this chat. 🎬📥\n\n"
    "*Supported platforms:*\n"
    "▫️ YouTube (Long videos & Shorts)\n"
    "▫️ Instagram (Reels, Posts & Photos)\n"
    "▫️ Facebook (Videos & Reels)\n"
    "▫️ TikTok (Videos & Photo posts)\n"
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
    "🖼 *Photos:* Instagram / TikTok / X photo posts and carousels (photos + videos) are sent as albums.\n"
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
    """Handle the /start command with a beautiful welcome message."""
    await update.message.reply_text(
        WELCOME_MESSAGE,
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=main_keyboard(),
        disable_web_page_preview=True,
    )


async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Handle the /help command."""
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
    pick a quality. Big files are split into parts automatically, so even
    hour-long videos work -- lower quality simply means fewer parts.
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

    # Only offer heights the video actually has (always at least one)
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
    # Unique working folder per request to avoid filename collisions
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
            files, duration = await download_media(url, job_dir, state, quality)

        # Stop the progress updater now that the download has finished
        stop_event.set()
        await updater_task

        await deliver_files(context.bot, chat_id, status_message, files, platform, duration)

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
        # Clean up downloaded files to save storage space
        shutil.rmtree(job_dir, ignore_errors=True)


async def handle_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """
    Main message handler: finds a link in the incoming message.
    Regular YouTube videos -> ask for a quality first.
    Everything else (Shorts, Reels, TikTok, ...) -> download straight away.
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
#
# Render's free plan only supports "Web Services", which must respond
# on a port for Render's health check to consider the deploy healthy.
# Our bot itself only does Telegram polling and doesn't need a port --
# so this tiny HTTP server exists purely to satisfy that requirement.
#
# It does nothing but reply "OK" to any GET request. Pair this with an
# external uptime pinger (e.g. UptimeRobot / cron-job.org) hitting the
# service URL every 5-10 minutes so Render doesn't spin it down after
# 15 minutes of inactivity.
#
# This block is inert when PORT is not set (e.g. running locally on
# Pydroid 3), so it never interferes with normal local use.

class _KeepAliveHandler(BaseHTTPRequestHandler):
    def do_GET(self):  # noqa: N802 (required method name from base class)
        self.send_response(200)
        self.send_header("Content-Type", "text/plain")
        self.end_headers()
        self.wfile.write(b"Bot is alive and running.")

    def log_message(self, format, *args):  # noqa: A002
        # Silence the default per-request console logging (keep-alive
        # pings would otherwise spam the log every few minutes).
        pass


def start_keep_alive_server() -> None:
    """
    Start the keep-alive HTTP server in a background daemon thread if
    a PORT has been provided by the hosting platform (Render sets this
    automatically for Web Services).
    """
    if not PORT:
        return  # Not running on Render (or similar) -- nothing to do

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

    # concurrent_updates lets other users keep using the bot while a long
    # download/upload is running (otherwise everyone waits in one queue).
    app = ApplicationBuilder().token(BOT_TOKEN).concurrent_updates(True).build()

    app.add_handler(CommandHandler("start", start_command))
    app.add_handler(CommandHandler("help", help_command))
    app.add_handler(CallbackQueryHandler(button_callback))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_message))
    app.add_error_handler(error_handler)

    return app


def log_startup_checks() -> None:
    """Print what is installed, so problems are obvious in the Render logs."""
    logger.info("gallery-dl (photo posts): %s", "installed" if GALLERY_DL_OK else "NOT INSTALLED - add gallery-dl to requirements.txt")
    logger.info("ffmpeg (HD merge / splitting): %s", FFMPEG_EXE if FFMPEG_EXE else "NOT FOUND - add imageio-ffmpeg to requirements.txt")
    logger.info("yt-dlp version: %s", yt_dlp.version.__version__)


def main() -> None:
    """Entry point: build the bot and start polling for updates."""
    logger.info("Starting Telegram Universal Media Downloader Bot...")
    log_startup_checks()
    start_keep_alive_server()
    application = build_application()
    application.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)


if __name__ == "__main__":
    main()
