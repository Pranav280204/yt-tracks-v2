# app.py — YouTube tracker + auth (login, single-device, admin add-user)
import os
import threading
import logging
import time
# near other imports at top of file
import requests
import hashlib
import json
import math
import secrets
import bisect
from datetime import datetime, timedelta, timezone
from io import BytesIO
from urllib.parse import urlparse, parse_qs
from zoneinfo import ZoneInfo
from typing import Optional, Dict, Tuple
from functools import wraps

import pandas as pd
from flask import (
    Flask, render_template, request, redirect, url_for,
    flash, send_file, session, g, make_response, jsonify
)
from googleapiclient.discovery import build
from googleapiclient.errors import HttpError
import psycopg
from psycopg.rows import dict_row
from werkzeug.security import generate_password_hash, check_password_hash

# -----------------------------
# App & logging
# -----------------------------
# -----------------------------
# App & logging
# -----------------------------
app = Flask(__name__)

# Use ONE secret key — fixed & persistent
app.secret_key = os.getenv(
    "FLASK_SECRET_KEY",
    "xW3p7hU2q9L0zA4nD8rK1vS6bC5yT0j"  # fallback used only in local dev
)

app.permanent_session_lifetime = timedelta(days=30)
logging.basicConfig(level=os.getenv("LOG_LEVEL", "INFO"))
log = logging.getLogger("yt-tracker")

IST = ZoneInfo("Asia/Kolkata")


# -----------------------------
# Env & cache TTL
# -----------------------------
API_KEY = os.getenv("YOUTUBE_API_KEY", "")
API_KEYS_RAW = os.getenv("YOUTUBE_API_KEYS", "")
YOUTUBE_API_KEYS = [k.strip() for k in API_KEYS_RAW.split(",") if k.strip()]
if API_KEY and API_KEY not in YOUTUBE_API_KEYS:
    YOUTUBE_API_KEYS.insert(0, API_KEY)
POOLING_INTERVAL = int(os.getenv("POOLING_INTERVAL", "30"))
POSTGRES_URL = os.getenv("DATABASE_URL")
# Reference video id used for 5-min ratio comparison
REF_COMPARE_VIDEO_ID = "YxWlaYCA8MU"
ADMIN_CREATE_SECRET = os.getenv("ADMIN_CREATE_SECRET", "")  # master password for creating users
# MRBeast-specific client (separate API key)
MRBEAST_API_KEY = os.getenv("MRBEAST_API_KEY", "")
MRBEAST_CHANNEL_ID = os.getenv("MRBEAST_CHANNEL_ID", "UCX6OQ3DkcsbYNE6H8uQQuVA")
MR_YT = None
if MRBEAST_API_KEY:
    try:
        MR_YT = build("youtube", "v3", developerKey=MRBEAST_API_KEY, cache_discovery=False)
        log.info("MRBeast YouTube client ready.")
    except Exception as e:
        log.exception("MRBeast YT init failed: %s", e)
# Cache TTL for uploads list (seconds). Default 6 hours to avoid expensive full list every 30m.
MR_UPLOADS_CACHE_TTL = int(os.getenv("MR_UPLOADS_CACHE_TTL", str(6 * 3600)))

# in-memory cache for uploads playlist id / video ids
_mr_uploads_cache = {
    "playlist_id": None,
    "video_ids": None,
    "fetched_at": 0.0
}


def require_admin_secret_from_form(form, redirect_endpoint, **redirect_kwargs):
    """
    Check admin_secret in form against ADMIN_CREATE_SECRET.
    If wrong/missing -> flash + redirect.
    If ok or secret not set -> return None.
    """
    if not ADMIN_CREATE_SECRET:
        # If you haven't set it, don't block (or change this to always block if you prefer).
        return None

    admin_secret = (form.get("admin_secret") or "").strip()
    if admin_secret != ADMIN_CREATE_SECRET:
        flash("Admin password required or incorrect.", "danger")
        return redirect(url_for(redirect_endpoint, **redirect_kwargs))

    return None

CHANNEL_CACHE_TTL = int(os.getenv("CHANNEL_CACHE_TTL", "50"))  # seconds; < sampler interval
if not POSTGRES_URL:
    log.warning("DATABASE_URL not set.")

# YouTube client
YOUTUBE = None
if API_KEY:
    try:
        YOUTUBE = build("youtube", "v3", developerKey=API_KEY, cache_discovery=False)
        log.info("YouTube client ready.")
    except Exception as e:
        log.exception("YouTube init failed: %s", e)

# simple in-memory cache for channel totals (to avoid bursts)
_channel_views_cache: Dict[str, Tuple[Optional[int], float]] = {}
_channel_cache_lock = threading.Lock()
_api_key_lock = threading.Lock()
_api_key_index = 0


def get_rotating_api_key() -> Optional[str]:
    """Return the next YouTube API key in rotation (or None if none configured)."""
    global _api_key_index
    if not YOUTUBE_API_KEYS:
        return None
    with _api_key_lock:
        key = YOUTUBE_API_KEYS[_api_key_index % len(YOUTUBE_API_KEYS)]
        _api_key_index = (_api_key_index + 1) % len(YOUTUBE_API_KEYS)
    return key

def get_channel_total_cached(channel_id: str) -> Optional[int]:
    """Return channel viewCount using cached value if recent; otherwise fetch and update cache."""
    if not channel_id or not YOUTUBE:
        return None
    now_ts = time.time()
    with _channel_cache_lock:
        ent = _channel_views_cache.get(channel_id)
        if ent:
            val, fetched_at = ent
            if now_ts - fetched_at <= CHANNEL_CACHE_TTL:
                return val
    # fetch fresh
    try:
        resp = YOUTUBE.channels().list(part="statistics", id=channel_id, maxResults=1).execute()
        items = resp.get("items", [])
        if not items:
            val = None
        else:
            val = int(items[0].get("statistics", {}).get("viewCount", 0))
    except Exception as e:
        log.exception("Error fetching channel stats for %s: %s", channel_id, e)
        val = None
    with _channel_cache_lock:
        _channel_views_cache[channel_id] = (val, now_ts)
    return val
def get_latest_channel_totals_for(channel_ids: list[str]) -> dict:
    """
    Return dict channel_id -> latest total_views (or None).
    Uses one DB query (DISTINCT ON) which is fast with proper PK/index.
    """
    out: dict = {}
    if not channel_ids:
        return out
    conn = db()
    with conn.cursor() as cur:
        cur.execute("""
          SELECT DISTINCT ON (channel_id) channel_id, total_views
          FROM channel_stats
          WHERE channel_id = ANY(%s)
          ORDER BY channel_id, ts_utc DESC
        """, (channel_ids,))
        for r in cur.fetchall():
            out[r["channel_id"]] = r["total_views"]
    # ensure keys present
    for ch in channel_ids:
        out.setdefault(ch, None)
    return out
    
def _mr_fetch_uploads_playlist_id():
    """Return uploads playlist id for MRBEAST_CHANNEL_ID using MR_YT client."""
    if not MR_YT:
        return None
    try:
        r = MR_YT.channels().list(part="contentDetails", id=MRBEAST_CHANNEL_ID, maxResults=1).execute()
        items = r.get("items", [])
        if not items:
            return None
        return items[0]["contentDetails"]["relatedPlaylists"]["uploads"]
    except Exception as e:
        log.exception("Failed to get uploads playlist id: %s", e)
        return None


def _mr_get_all_video_ids(use_cache=True):
    """
    Return list of all video ids from the uploads playlist.
    Uses in-memory cache for MR_UPLOADS_CACHE_TTL seconds to avoid hitting playlistItems each half-hour.
    """
    now_ts = time.time()
    # return cached if fresh
    if use_cache and _mr_uploads_cache.get("video_ids") and (now_ts - _mr_uploads_cache.get("fetched_at", 0) <= MR_UPLOADS_CACHE_TTL):
        return list(_mr_uploads_cache["video_ids"])

    playlist_id = _mr_uploads_cache.get("playlist_id")
    if not playlist_id:
        playlist_id = _mr_fetch_uploads_playlist_id()
        _mr_uploads_cache["playlist_id"] = playlist_id

    if not playlist_id:
        return []

    video_ids = []
    next_tok = None
    try:
        while True:
            resp = MR_YT.playlistItems().list(
                part="contentDetails",
                playlistId=playlist_id,
                maxResults=50,
                pageToken=next_tok,
                fields="nextPageToken,items(contentDetails/videoId)"
            ).execute()
            for it in resp.get("items", []):
                vid = it.get("contentDetails", {}).get("videoId")
                if vid:
                    video_ids.append(vid)
            next_tok = resp.get("nextPageToken")
            if not next_tok:
                break
            # slight polite pause
            time.sleep(0.08)
    except Exception as e:
        log.exception("Error fetching playlist items for MrBeast: %s", e)
        # still cache whatever we got, but mark time so we retry soon
    # update cache
    _mr_uploads_cache["video_ids"] = video_ids
    _mr_uploads_cache["fetched_at"] = now_ts
    return video_ids


def _mr_sum_views_for_video_ids(video_ids: list[str]):
    """
    Sum viewCounts for the provided list of video_ids in chunks of 50.
    Returns integer total or None if nothing found.
    """
    if not MR_YT or not video_ids:
        return None
    total = 0
    try:
        for i in range(0, len(video_ids), 50):
            chunk = video_ids[i:i + 50]
            resp = MR_YT.videos().list(part="statistics", id=",".join(chunk), maxResults=50,
                                       fields="items/statistics(viewCount)").execute()
            for it in resp.get("items", []):
                try:
                    vc = int(it.get("statistics", {}).get("viewCount", 0) or 0)
                except Exception:
                    vc = 0
                total += vc
            time.sleep(0.08)
    except Exception as e:
        log.exception("Error summing video stats for MrBeast: %s", e)
        return None
    return total
def current_half_hour_utc_from_ist():
    """
    Return the exact :00 or :30 IST boundary converted to UTC
    """
    now_ist = datetime.now(IST).replace(second=0, microsecond=0)
    minute = 0 if now_ist.minute < 30 else 30
    snapped_ist = now_ist.replace(minute=minute)
    return snapped_ist.astimezone(timezone.utc)

    
def get_latest_sample_per_video(video_ids: list[str]) -> dict:
    """
    Return dict video_id -> row {video_id, ts_utc, views} for the latest ts_utc per video.
    Uses DISTINCT ON(video_id) ORDER BY video_id, ts_utc DESC.
    """
    out: dict = {}
    if not video_ids:
        return out
    conn = db()
    with conn.cursor() as cur:
        cur.execute("""
          SELECT DISTINCT ON (video_id) video_id, ts_utc, views
          FROM views
          WHERE video_id = ANY(%s)
          ORDER BY video_id, ts_utc DESC
        """, (video_ids,))
        for r in cur.fetchall():
            out[r["video_id"]] = r
    # ensure all ids exist
    for vid in video_ids:
        out.setdefault(vid, None)
    return out
# -----------------------------
# DB connection (psycopg3)
# -----------------------------
_db = None
_db_lock = threading.Lock()

def db():
    global _db
    with _db_lock:
        if _db is None or _db.closed:
            _db = psycopg.connect(
                POSTGRES_URL,
                autocommit=True,
                row_factory=dict_row,
                connect_timeout=5,
                options="-c statement_timeout=15000",
                keepalives=1,
                keepalives_idle=30,
                keepalives_interval=10,
                keepalives_count=5,
            )
        return _db

def init_db():
    conn = db()
    with conn.cursor() as cur:
        # Users for auth ----------------------------------
        cur.execute("""
        CREATE TABLE IF NOT EXISTS users (
          id SERIAL PRIMARY KEY,
          username TEXT UNIQUE NOT NULL,
          password_hash TEXT NOT NULL,
          current_session_token TEXT
        );
        """)

        cur.execute("""
        ALTER TABLE users
        ADD COLUMN IF NOT EXISTS is_active BOOLEAN NOT NULL DEFAULT TRUE;
        """)
                # Channel snapshots ----------------------------------
        cur.execute("""
        CREATE TABLE IF NOT EXISTS channel_stats (
          channel_id TEXT NOT NULL,
          ts_utc TIMESTAMPTZ NOT NULL,
          total_views BIGINT,
          source TEXT,
          PRIMARY KEY (channel_id, ts_utc)
        );
        """)

        # in case this was added after older runs, ensure column exists
        cur.execute("""
        ALTER TABLE channel_stats
        ADD COLUMN IF NOT EXISTS source TEXT;
        """)

        cur.execute("""
        ALTER TABLE users
        ADD COLUMN IF NOT EXISTS device_token TEXT;
        """)

        cur.execute("""
        ALTER TABLE users
        ADD COLUMN IF NOT EXISTS device_ua TEXT;
        """)

        cur.execute("""
        ALTER TABLE users
        ADD COLUMN IF NOT EXISTS device_info TEXT;
        """)

        # Videos ----------------------------------
        cur.execute("""
        CREATE TABLE IF NOT EXISTS video_list (
          video_id    TEXT PRIMARY KEY,
          name        TEXT NOT NULL,
          is_tracking BOOLEAN NOT NULL DEFAULT TRUE
        );
        """)
                # Thumbnail tracking columns
        cur.execute("""
        ALTER TABLE video_list
        ADD COLUMN IF NOT EXISTS thumbnail_url TEXT;
        """)
        cur.execute("""
        ALTER TABLE video_list
        ADD COLUMN IF NOT EXISTS thumbnail_hash TEXT;
        """)
        cur.execute("""
        ALTER TABLE video_list
        ADD COLUMN IF NOT EXISTS thumbnail_prev_url TEXT;
        """)
        cur.execute("""
        ALTER TABLE video_list
        ADD COLUMN IF NOT EXISTS thumbnail_changed BOOLEAN NOT NULL DEFAULT FALSE;
        """)
        cur.execute("""
        ALTER TABLE video_list
        ADD COLUMN IF NOT EXISTS thumbnail_changed_at TIMESTAMPTZ;
        """)

        # Notifications table for events (thumbnail changes etc)
        cur.execute("""
        CREATE TABLE IF NOT EXISTS notifications (
          id SERIAL PRIMARY KEY,
          video_id TEXT REFERENCES video_list(video_id) ON DELETE CASCADE,
          ts_utc TIMESTAMPTZ NOT NULL,
          type TEXT NOT NULL,
          data JSONB,
          is_read BOOLEAN NOT NULL DEFAULT FALSE
        );
        """)

        # ➕ NEW COLUMNS FOR COMPARISON FEATURE
        cur.execute("""
        ALTER TABLE video_list
        ADD COLUMN IF NOT EXISTS compare_video_id TEXT;
        """)

        cur.execute("""
        ALTER TABLE video_list
        ADD COLUMN IF NOT EXISTS compare_offset_days INTEGER;
        """)

        cur.execute("""
        CREATE TABLE IF NOT EXISTS comparison_configs (
          id SERIAL PRIMARY KEY,
          video_id TEXT NOT NULL REFERENCES video_list(video_id) ON DELETE CASCADE,
          compare_video_id TEXT NOT NULL,
          compare_offset_days INTEGER NOT NULL,
          column_name TEXT NOT NULL,
          created_at TIMESTAMPTZ NOT NULL DEFAULT now()
        );
        """)
        cur.execute("""
        CREATE INDEX IF NOT EXISTS idx_comparison_configs_video
        ON comparison_configs (video_id);
        """)
        cur.execute("""
        CREATE UNIQUE INDEX IF NOT EXISTS idx_comparison_configs_unique_colname
        ON comparison_configs (video_id, column_name);
        """)

        cur.execute("""
        ALTER TABLE video_list
        ADD COLUMN IF NOT EXISTS is_deleted BOOLEAN NOT NULL DEFAULT FALSE;
        """)

        # View samples ----------------------------------
        cur.execute("""
        CREATE TABLE IF NOT EXISTS views (
          video_id  TEXT NOT NULL,
          ts_utc    TIMESTAMPTZ NOT NULL,
          date_ist  DATE NOT NULL,
          views     BIGINT NOT NULL,
          likes     BIGINT,
          comments  BIGINT,
          PRIMARY KEY (video_id, ts_utc),
          FOREIGN KEY (video_id) REFERENCES video_list(video_id) ON DELETE CASCADE
        );
        """)

        # ensure comments column exists (for migrations)
        cur.execute("""
        ALTER TABLE views
        ADD COLUMN IF NOT EXISTS comments BIGINT;
        """)

        # indexes to speed up video detail queries
        cur.execute("""
        CREATE INDEX IF NOT EXISTS idx_views_video_ts
        ON views (video_id, ts_utc DESC);
        """)


        # Targets ----------------------------------
        cur.execute("""
        CREATE TABLE IF NOT EXISTS targets (
          id           SERIAL PRIMARY KEY,
          video_id     TEXT NOT NULL REFERENCES video_list(video_id) ON DELETE CASCADE,
          target_views BIGINT NOT NULL,
          target_ts    TIMESTAMPTZ NOT NULL,
          note         TEXT
        );
        """)

        # Channel snapshots ----------------------------------
        cur.execute("""
        CREATE TABLE IF NOT EXISTS channel_stats (
          channel_id TEXT NOT NULL,
          ts_utc TIMESTAMPTZ NOT NULL,
          total_views BIGINT,
          PRIMARY KEY (channel_id, ts_utc)
        );
        """)

    log.info("DB schema ready.")




# -----------------------------
# Auth helpers
# -----------------------------
def get_current_user():
    uid = session.get("user_id")
    token = session.get("session_token")
    if not uid or not token:
        return None

    conn = db()
    with conn.cursor() as cur:
        cur.execute(
            "SELECT id, username, current_session_token, is_active "
            "FROM users WHERE id=%s",
            (uid,)
        )
        u = cur.fetchone()

    # If user doesn’t exist, token changed, or user is deactivated → logout immediately
    if (
        not u
        or not u["current_session_token"]
        or u["current_session_token"] != token
        or not u["is_active"]       # 👈 NEW: deactivated user triggers logout
    ):
        session.clear()
        return None

    return u


@app.before_request
def load_user():
    # runs every request; store user in g
    g.user = get_current_user()

@app.context_processor
def inject_user():
    # make current_user available in templates
    return {"current_user": getattr(g, "user", None)}

def login_required(f):
    @wraps(f)
    def wrapper(*args, **kwargs):
        if not g.get("user"):
            flash("Please log in.", "warning")
            return redirect(url_for("login", next=request.path))
        return f(*args, **kwargs)
    return wrapper

# -----------------------------
# YouTube helpers
# -----------------------------
def extract_video_id(link: str) -> str | None:
    try:
        u = urlparse(link.strip())
        host = (u.netloc or "").lower()
        if "youtu.be" in host:
            return u.path.strip("/").split("/")[0] or None
        if "youtube.com" in host or "m.youtube.com" in host:
            if u.path == "/watch":
                qs = parse_qs(u.query)
                return (qs.get("v") or [None])[0]
            parts = u.path.strip("/").split("/")
            if len(parts) >= 2 and parts[0] in {"shorts", "live"}:
                return parts[1]
        return None
    except Exception:
        return None

def fetch_title(video_id: str) -> str:
    if not YOUTUBE:
        return "Unknown"
    try:
        r = YOUTUBE.videos().list(part="snippet", id=video_id, maxResults=1).execute()
        items = r.get("items", [])
        return (items[0]["snippet"]["title"] if items else "Unknown")[:140] or "Unknown"
    except Exception as e:
        log.exception("Title fetch error: %s", e)
        return "Unknown"

# Add near the other globals
_channel_id_cache: Dict[str, Tuple[Optional[str], float]] = {}
_CHANNEL_ID_CACHE_TTL = 60.0  # seconds
# in-memory short cache for built video display (to reduce repeated heavy work)
_video_display_cache: Dict[str, Tuple[dict, float]] = {}
_video_display_cache_lock = threading.Lock()
_VIDEO_DISPLAY_CACHE_TTL = 5  # seconds; tune this
# maximum number of days of samples to fetch for display (reduce to speed up)
_MAX_DISPLAY_DAYS = 14
def invalidate_video_cache(video_id: str):
    """Remove a cached build_video_display result for a video_id (no-op if missing)."""
    try:
        with _video_display_cache_lock:
            _video_display_cache.pop(video_id, None)
    except Exception:
        # be resilient to concurrency issues
        log.exception("invalidate_video_cache error for %s", video_id)

def fetch_channel_id_for_videos(video_ids: list[str]) -> dict:
    """
    Bulk fetch snippet.channelId for up to 50 video_ids.
    Uses short in-memory cache to avoid repeated API calls during bursts.
    Returns map: video_id -> channel_id (may be None).
    """
    out: dict = {}
    if not video_ids:
        return out

    # first consult cache for each id
    now_ts = time.time()
    to_fetch = []
    for vid in video_ids:
        ent = _channel_id_cache.get(vid)
        if ent:
            val, fetched_at = ent
            if now_ts - fetched_at <= _CHANNEL_ID_CACHE_TTL:
                out[vid] = val
                continue
        # not cached or stale
        to_fetch.append(vid)

    # if no API available or nothing to fetch, return what we have
    if (not YOUTUBE) or (not to_fetch):
        # ensure all requested keys exist in out
        for vid in video_ids:
            out.setdefault(vid, None)
        return out

    # fetch in chunks of 50
    try:
        for i in range(0, len(to_fetch), 50):
            chunk = to_fetch[i:i+50]
            r = YOUTUBE.videos().list(part="snippet", id=",".join(chunk), maxResults=50).execute()
            for it in r.get("items", []):
                vid = it["id"]
                ch = it.get("snippet", {}).get("channelId")
                out[vid] = ch
                _channel_id_cache[vid] = (ch, now_ts)
            # mark any missing items as None and cache them
            for ch_vid in chunk:
                if ch_vid not in out:
                    out[ch_vid] = None
                    _channel_id_cache[ch_vid] = (None, now_ts)
    except Exception as e:
        log.exception("fetch_channel_id_for_videos error: %s", e)
        # fallback: ensure all requested keys present
        for vid in video_ids:
            out.setdefault(vid, None)

    # ensure all original video_ids exist in output
    for vid in video_ids:
        out.setdefault(vid, None)
    return out

# --- paste near other "sleep_until_next_..." and "current_half_hour_utc_from_ist" helpers ---
def sleep_until_next_10min_IST():
    """
    Sleep until the next 10-minute boundary in IST (e.g. :00, :10, :20, ...).
    """
    now_ist = datetime.now(IST).replace(microsecond=0)
    next_min = ((now_ist.minute // 10) + 1) * 10
    if next_min >= 60:
        next_tick = now_ist.replace(minute=0, second=0) + timedelta(hours=1)
    else:
        next_tick = now_ist.replace(minute=next_min, second=0)
    secs = (next_tick - now_ist).total_seconds()
    if secs > 0:
        time.sleep(secs)

def current_10min_utc_from_ist():
    """
    Return a timezone-aware UTC datetime snapped to the current 10-minute IST bucket start.
    Example: 10:17 IST -> snaps to 10:10:00 IST -> converted to UTC
    """
    now_ist = datetime.now(IST).replace(second=0, microsecond=0)
    minute = (now_ist.minute // 10) * 10
    snapped_ist = now_ist.replace(minute=minute, second=0)
    return snapped_ist.astimezone(timezone.utc)

def fetch_stats_batch(video_ids: list[str]) -> dict:
    if not YOUTUBE or not video_ids:
        return {}
    out = {}
    try:
        for i in range(0, len(video_ids), 50):
            chunk = video_ids[i:i + 50]
            r = YOUTUBE.videos().list(
                part="statistics",
                id=",".join(chunk),
                maxResults=50
            ).execute()
            for it in r.get("items", []):
                vid = it["id"]
                st = it.get("statistics", {})
                views = int(st.get("viewCount", "0") or 0)
                like_raw = st.get("likeCount")
                likes = int(like_raw) if like_raw is not None else None
                comment_raw = st.get("commentCount")
                comments = int(comment_raw) if comment_raw is not None else None
                out[vid] = {"views": views, "likes": likes, "comments": comments}
    except HttpError as e:
        log.error("YouTube (stats) error: %s", e)
    except Exception as e:
        log.exception("Stats fetch error: %s", e)
    return out
def fetch_thumbnail_hash_for_video(video_id: str) -> tuple[str | None, str | None]:
    """
    Try common YouTube thumbnail URLs (maxresdefault -> hqdefault -> sddefault).
    Returns (url, sha1_hex) or (None, None) if not available.
    """
    urls = [
        f"https://i.ytimg.com/vi/{video_id}/maxresdefault.jpg",
        f"https://i.ytimg.com/vi/{video_id}/hqdefault.jpg",
        f"https://i.ytimg.com/vi/{video_id}/sddefault.jpg",
    ]
    for u in urls:
        try:
            r = requests.get(u, timeout=6)
            if r.status_code == 200 and r.content:
                h = hashlib.sha1(r.content).hexdigest()
                return u, h
        except Exception:
            # network/timeout -- try next
            continue
    return None, None


def check_thumbnail_change(video_id: str, force: bool = False) -> bool:
    """
    Check thumbnail for `video_id`. If hash differs from stored value, update video_list and
    create a notifications row. Returns True if a change was detected and recorded.
    Throttle: unless force=True, skip check if thumbnail_changed_at is within last 24 hours
    and we already have a thumbnail_hash (reduces frequent downloads).
    """
    try:
        conn = db()
        nowu = now_utc()
        with conn.cursor() as cur:
            cur.execute(
                "SELECT thumbnail_hash, thumbnail_changed_at, thumbnail_url FROM video_list WHERE video_id=%s",
                (video_id,)
            )
            r = cur.fetchone()
            if not r:
                return False

            prev_hash = r.get("thumbnail_hash")
            prev_changed_at = r.get("thumbnail_changed_at")
            prev_url = r.get("thumbnail_url")

            if not force and prev_hash:
                # if we recently checked, skip (24h)
                if prev_changed_at:
                    try:
                        if (nowu - prev_changed_at).total_seconds() < 24 * 3600:
                            return False
                    except Exception:
                        pass

        # actually fetch thumbnail bytes & hash
        new_url, new_hash = fetch_thumbnail_hash_for_video(video_id)
        if not new_url or not new_hash:
            return False

        # compare & update if different
        with conn.cursor() as cur:
            if prev_hash != new_hash:
                # store previous url, new url/hash, mark changed
                cur.execute(
                    """
                    UPDATE video_list
                    SET thumbnail_prev_url = %s,
                        thumbnail_url = %s,
                        thumbnail_hash = %s,
                        thumbnail_changed = TRUE,
                        thumbnail_changed_at = %s
                    WHERE video_id = %s
                    """,
                    (prev_url, new_url, new_hash, nowu, video_id)
                )
                # insert notification
                payload = {"prev_url": prev_url, "new_url": new_url}
                cur.execute(
                    "INSERT INTO notifications (video_id, ts_utc, type, data) VALUES (%s, %s, %s, %s)",
                    (video_id, nowu, "thumbnail_changed", json.dumps(payload))
                )
                log.info("Thumbnail changed for %s (prev=%s new=%s)", video_id, prev_url, new_url)
                return True

    except Exception as e:
        log.exception("check_thumbnail_change error for %s: %s", video_id, e)
    return False

# -----------------------------
# Storage helpers
# -----------------------------
def now_utc():
    return datetime.now(timezone.utc).replace(microsecond=0)

def safe_store(video_id: str, stats: dict):
    tsu = now_utc()
    date_ist = tsu.astimezone(IST).date()
    conn = db()
    with conn.cursor() as cur:
        # remove existing exact-timestamp row (we keep one-per-ts)
        cur.execute("DELETE FROM views WHERE video_id=%s AND ts_utc=%s", (video_id, tsu))

        likes_val = stats.get("likes")
        comments_val = stats.get("comments")

        cur.execute(
            "INSERT INTO views (video_id, ts_utc, date_ist, views, likes, comments) VALUES (%s, %s, %s, %s, %s, %s)",
            (video_id, tsu, date_ist, int(stats.get("views", 0)), likes_val, comments_val)
        )

    # Ensure any cached display for this video is invalidated so the UI will reload fresh data
    invalidate_video_cache(video_id)



def interpolate_at(rows: list[dict], target_ts: datetime, key="views") -> Optional[float]:
    """
    Interpolate numeric value at target_ts from chronological rows (with ts_utc and key).
    Returns None if target is before first or after last row.
    """
    if not rows:
        return None
    # exact
    for r in rows:
        if r["ts_utc"] == target_ts:
            return float(r[key] if key in r else r["views"])
    prev = None
    for r in rows:
        if r["ts_utc"] < target_ts:
            prev = r
            continue
        if r["ts_utc"] > target_ts and prev is not None:
            t0 = prev["ts_utc"].timestamp()
            v0 = float(prev[key] if key in prev else prev["views"])
            t1 = r["ts_utc"].timestamp()
            v1 = float(r[key] if key in r else r["views"])
            if t1 == t0:
                return v1
            frac = (target_ts.timestamp() - t0) / (t1 - t0)
            return v0 + frac * (v1 - v0)
        if prev is None:
            return None
    return None

def _time_to_seconds(time_str: str) -> int:
    h, m, s = [int(x) for x in time_str.split(":")]
    return h * 3600 + m * 60 + s


def find_closest_tpl(prev_map: dict, time_part: str, tolerance_seconds: int = 10):
    if not prev_map:
        return None
    target_secs = _time_to_seconds(time_part)
    best = None
    best_delta = None
    for k, tpl in prev_map.items():
        try:
            s = _time_to_seconds(k)
        except Exception:
            continue
        delta = abs(target_secs - s)
        if best is None or delta < best_delta:
            best = tpl
            best_delta = delta
    if best is not None and best_delta is not None and best_delta <= tolerance_seconds:
        return best
    return None

def find_closest_prev(prev_map: dict, time_part: str, max_earlier_seconds: int = 300):
    """
    From prev_map (time_str -> tpl), return the tuple whose time is the closest
    earlier-or-equal to time_part, but only if it is within max_earlier_seconds
    earlier. If exact match exists, returns it. If none found, returns None.

    Example: time_part="22:30:00", will prefer "22:30:00" if present,
    otherwise "22:25:00" (or "22:26/22:27/...") if within max_earlier_seconds.
    """
    if not prev_map:
        return None
    try:
        target_secs = _time_to_seconds(time_part)
    except Exception:
        return None

    # exact
    if time_part in prev_map:
        return prev_map[time_part]

    best = None
    best_delta = None
    for k, tpl in prev_map.items():
        try:
            s = _time_to_seconds(k)
        except Exception:
            continue
        # only consider earlier-or-equal times
        if s > target_secs:
            continue
        delta = target_secs - s
        if delta <= max_earlier_seconds:
            if best is None or delta < best_delta:
                best = tpl
                best_delta = delta
    return best

def process_gains(rows_asc: list[dict]):
    """
    rows_asc: chronological list of dicts with keys ts_utc (aware datetime), views (int),
              optionally likes, comments

    Returns list of tuples:
      (ts_ist_str, views, gain_5min, hourly_views_gain, hourly_likes_gain, gain_24h,
       daily_views_gain, gain_24h_midpoint_ist_str, likes_val, comments_val)

    hourly_likes_gain may be None when likes are missing or interpolation isn't possible.
    """
    out = []
    n = len(rows_asc)
    if n == 0:
        return out

    ts_list = [r["ts_utc"].timestamp() for r in rows_asc]  # floats seconds
    views_list = [int(r["views"]) for r in rows_asc]

    # build likes list preserving None for missing/invalid likes
    likes_list = []
    for r in rows_asc:
        lk = r.get("likes")
        if lk is None:
            likes_list.append(None)
        else:
            try:
                likes_list.append(int(lk))
            except Exception:
                likes_list.append(None)

    first_ts = rows_asc[0]["ts_utc"]
    first_ts_epoch = first_ts.timestamp()

    def _estimate_midpoint_ts_for_24h_window(end_idx: int, start_ts: float, start_views: float, end_views: int):
        """
        Approximate timestamp when views crossed halfway point between start_views and end_views
        within [start_ts, end_ts]. Uses linear interpolation on sampled segments.
        """
        end_ts = ts_list[end_idx]
        if end_ts <= start_ts:
            return None

        target_views = start_views + ((float(end_views) - float(start_views)) / 2.0)

        prev_t = start_ts
        prev_v = float(start_views)

        for seg_idx in range(end_idx + 1):
            seg_t = ts_list[seg_idx]
            if seg_t <= start_ts:
                continue
            if seg_t > end_ts:
                seg_t = end_ts
                seg_v = float(end_views)
            else:
                seg_v = float(views_list[seg_idx])

            v_min = min(prev_v, seg_v)
            v_max = max(prev_v, seg_v)
            if v_min <= target_views <= v_max:
                if seg_v == prev_v:
                    mid_ts = prev_t
                else:
                    frac = (target_views - prev_v) / (seg_v - prev_v)
                    mid_ts = prev_t + frac * (seg_t - prev_t)
                return datetime.fromtimestamp(mid_ts, tz=timezone.utc)

            prev_t = seg_t
            prev_v = seg_v
            if seg_t >= end_ts:
                break

        return None

    for i, r in enumerate(rows_asc):
        ts_utc = r["ts_utc"]
        ts_ist = ts_utc.astimezone(IST).strftime("%Y-%m-%d %H:%M:%S")
        views = views_list[i]

        # gain in last 5 minutes (previous sample)
        gain_5min = None if i == 0 else views - views_list[i - 1]

        # ---------- hourly gain (views) ----------
        target_h_ts = (ts_utc - timedelta(hours=1)).timestamp()
        hourly_views = None
        pos = bisect.bisect_right(ts_list, target_h_ts, 0, i + 1)
        prev_idx = pos - 1
        next_idx = pos if pos <= i else None

        if prev_idx >= 0 and next_idx is not None:
            t0 = ts_list[prev_idx]; v0 = views_list[prev_idx]
            t1 = ts_list[next_idx]; v1 = views_list[next_idx]
            if t1 == t0:
                ref_val = v1
            else:
                frac = (target_h_ts - t0) / (t1 - t0)
                ref_val = v0 + frac * (v1 - v0)
            try:
                hourly_views = views - int(round(ref_val))
            except Exception:
                hourly_views = None
        elif prev_idx >= 0:
            try:
                hourly_views = views - views_list[prev_idx]
            except Exception:
                hourly_views = None
        else:
            hourly_views = None

        # ---------- hourly likes gain (interpolated when possible) ----------
        likes_val = likes_list[i]
        hourly_likes = None
        try:
            if likes_val is not None:
                # try interpolation similar to views
                if prev_idx >= 0 and next_idx is not None:
                    l0 = likes_list[prev_idx]
                    l1 = likes_list[next_idx]
                    if l0 is not None and l1 is not None:
                        t0 = ts_list[prev_idx]; t1 = ts_list[next_idx]
                        if t1 == t0:
                            ref_likes = l1
                        else:
                            frac = (target_h_ts - t0) / (t1 - t0)
                            ref_likes = l0 + frac * (l1 - l0)
                        hourly_likes = likes_val - int(round(ref_likes))
                    elif l0 is not None:
                        # fallback to previous known likes (no interpolation)
                        hourly_likes = likes_val - l0
                    else:
                        hourly_likes = None
                elif prev_idx >= 0:
                    l0 = likes_list[prev_idx]
                    if l0 is not None:
                        hourly_likes = likes_val - l0
        except Exception:
            hourly_likes = None

        # ---------- 24h gain (views) ----------
        target_d_ts = (ts_utc - timedelta(days=1)).timestamp()
        posd = bisect.bisect_right(ts_list, target_d_ts, 0, i + 1)
        prev_idx_d = posd - 1
        next_idx_d = posd if posd <= i else None

        gain_24h_midpoint_ist = None

        if prev_idx_d >= 0 and next_idx_d is not None:
            t0 = ts_list[prev_idx_d]; v0 = views_list[prev_idx_d]
            t1 = ts_list[next_idx_d]; v1 = views_list[next_idx_d]
            if t1 == t0:
                ref_day = v1
            else:
                frac = (target_d_ts - t0) / (t1 - t0)
                ref_day = v0 + frac * (v1 - v0)
            try:
                gain_24h = views - int(round(ref_day))
                midpoint_ts_utc = _estimate_midpoint_ts_for_24h_window(i, target_d_ts, ref_day, views)
                if midpoint_ts_utc is not None:
                    gain_24h_midpoint_ist = midpoint_ts_utc.astimezone(IST).strftime("%Y-%m-%d %H:%M:%S")
            except Exception:
                gain_24h = None
                gain_24h_midpoint_ist = None
        elif prev_idx_d >= 0:
            try:
                gain_24h = views - views_list[prev_idx_d]
                midpoint_ts_utc = _estimate_midpoint_ts_for_24h_window(i, ts_list[prev_idx_d], views_list[prev_idx_d], views)
                if midpoint_ts_utc is not None:
                    gain_24h_midpoint_ist = midpoint_ts_utc.astimezone(IST).strftime("%Y-%m-%d %H:%M:%S")
            except Exception:
                gain_24h = None
                gain_24h_midpoint_ist = None
        else:
            gain_24h = None
            gain_24h_midpoint_ist = None

        # ---------- daily views gain (anchored to first sample time) ----------
        # Day boundary repeats every 24h from first_ts (video added timestamp).
        # Example: first_ts 22:30 => cycles are [22:30, 22:29:59] each day.
        daily_views_gain = None
        try:
            elapsed = max(0.0, ts_list[i] - first_ts_epoch)
            cycle_idx = int(elapsed // 86400)
            cycle_start_ts = first_ts_epoch + (cycle_idx * 86400)

            pos_cycle = bisect.bisect_right(ts_list, cycle_start_ts, 0, i + 1)
            prev_idx_cycle = pos_cycle - 1
            next_idx_cycle = pos_cycle if pos_cycle <= i else None

            ref_views = None
            if prev_idx_cycle >= 0 and next_idx_cycle is not None:
                v0 = views_list[prev_idx_cycle]
                v1 = views_list[next_idx_cycle]
                t0 = ts_list[prev_idx_cycle]
                t1 = ts_list[next_idx_cycle]
                if t1 == t0:
                    ref_views = v1
                else:
                    frac = (cycle_start_ts - t0) / (t1 - t0)
                    ref_views = v0 + frac * (v1 - v0)
            elif prev_idx_cycle >= 0:
                ref_views = views_list[prev_idx_cycle]

            if ref_views is not None:
                daily_views_gain = views - int(round(ref_views))
        except Exception:
            daily_views_gain = None

        comments_val = r.get("comments")

        out.append((
            ts_ist,
            views,
            gain_5min,
            hourly_views,       # hourly views gain
            hourly_likes,       # <-- NEW hourly likes gain
            gain_24h,
            daily_views_gain,
            gain_24h_midpoint_ist,
            r.get("likes"),
            comments_val
        ))

    return out


def format_signed_hms_diff(current_ts: datetime, previous_ts: datetime):
    """Format current_ts - previous_ts as [sign]HH:MM:SS."""
    delta_seconds = int((current_ts - previous_ts).total_seconds())
    sign = "-" if delta_seconds < 0 else ""
    total = abs(delta_seconds)
    hours = total // 3600
    minutes = (total % 3600) // 60
    seconds = total % 60
    return f"{sign}{hours:02d}:{minutes:02d}:{seconds:02d}"


# -----------------------------
# Background sampler + channel snapshots
# -----------------------------
_sampler_started = False
_sampler_lock = threading.Lock()

def sleep_until_next_5min_IST():
    now_ist = datetime.now(IST).replace(microsecond=0)
    next_min = ((now_ist.minute // 5) + 1) * 5
    if next_min >= 60:
        next_tick = now_ist.replace(minute=0, second=0) + timedelta(hours=1)
    else:
        next_tick = now_ist.replace(minute=next_min, second=0)
    time.sleep(max(1, (next_tick - now_ist).total_seconds()))
def sleep_until_next_half_hour_utc():
    """
    Sleep until the next :00 or :30 boundary in UTC (aligned).
    """
    now = datetime.now(timezone.utc).replace(microsecond=0)
    if now.minute < 30:
        next_tick = now.replace(minute=30, second=0)
    else:
        # next hour at :00
        next_tick = (now.replace(minute=0, second=0) + timedelta(hours=1))
    secs = (next_tick - now).total_seconds()
    if secs > 0:
        time.sleep(secs)

def sampler_loop():
    """
    Every 5-min tick:
      - fetch stats for tracked videos and store into views
      - fetch channel ids for those videos, get channel totals and insert into channel_stats
    """
    log.info("Sampler loop started (aligned to IST 5-min).")
    while True:
        try:
            sleep_until_next_5min_IST()
            tsu = now_utc()
            conn = db()
            with conn.cursor() as cur:
                cur.execute("SELECT video_id FROM video_list WHERE is_tracking=TRUE AND is_deleted=FALSE ORDER BY video_id")
                vids = [r["video_id"] for r in cur.fetchall()]

            if not vids:
                continue

            stats_map = fetch_stats_batch(vids)
            # store per-video stats
            for vid in vids:
                st = stats_map.get(vid)
                if st:
                    safe_store(vid, st)
                    # best-effort thumbnail change check (non-blocking by guarding exceptions & throttle)
                    try:
                        # check_thumbnail_change is throttled (24h) unless force=True
                        check_thumbnail_change(vid)
                    except Exception:
                        log.exception("Thumbnail check failed for %s", vid)

            # channel snapshots
            if YOUTUBE:
                ch_map = fetch_channel_id_for_videos(vids)
                unique_chs = {ch for ch in ch_map.values() if ch}
                ch_totals = {}
                for ch in unique_chs:
                    try:
                        total = get_channel_total_cached(ch)
                        ch_totals[ch] = total
                    except Exception:
                        ch_totals[ch] = None
                with conn.cursor() as cur:
                    for ch, total in ch_totals.items():
                        try:
                            cur.execute(
                                "INSERT INTO channel_stats (channel_id, ts_utc, total_views) VALUES (%s, %s, %s) ON CONFLICT DO NOTHING",
                                (ch, tsu, total)
                            )
                        except Exception:
                            log.exception("Insert channel_stats failed for %s", ch)
        except Exception as e:
            log.exception("Sampler error: %s", e)
            time.sleep(5)
# Add this helper (or replace if you already have a similar one)
def sleep_until_next_half_hour_IST():
    """
    Sleep until the next :00 or :30 boundary in IST (aligned).
    """
    now_ist = datetime.now(IST).replace(microsecond=0)
    if now_ist.minute < 30:
        next_tick = now_ist.replace(minute=30, second=0)
    else:
        next_tick = (now_ist.replace(minute=0, second=0) + timedelta(hours=1))
    secs = (next_tick - now_ist).total_seconds()
    if secs > 0:
        time.sleep(secs)

# Replace your existing mrbeast_sampler_loop with this version
def mrbeast_sampler_loop():
    """
    MRBeast sampler — ONLY uploads-playlist SUM logic
    - Runs every IST half-hour (:00 / :30)
    - Skips duplicate half-hour buckets
    - Skips unchanged totals
    - Writes channel_stats with source='uploads_sum'
    """
    log.info("MrBeast sampler started (IST half-hour, uploads-sum only).")

    client = MR_YT if MR_YT else YOUTUBE
    if not client:
        log.warning("No YouTube client for MrBeast sampler.")
        return

    # warm cache
    try:
        _mr_get_all_video_ids(use_cache=True)
    except Exception:
        pass

    while True:
        try:
            sleep_until_next_half_hour_IST()
            tsu = current_half_hour_utc_from_ist()
            now_ist = tsu.astimezone(IST)

            video_ids = _mr_get_all_video_ids(use_cache=True)
            if not video_ids:
                log.warning("MrBeast sampler: no video IDs.")
                continue

            total = _mr_sum_views_for_video_ids(video_ids)
            if total is None:
                log.warning("MrBeast sampler: total is None.")
                continue

            conn = db()
            with conn.cursor() as cur:
                # get last snapshot
                cur.execute(
                    "SELECT ts_utc, total_views FROM channel_stats "
                    "WHERE channel_id=%s AND source='uploads_sum' "
                    "ORDER BY ts_utc DESC LIMIT 1",
                    (MRBEAST_CHANNEL_ID,)
                )
                last = cur.fetchone()

                skip = False
                if last:
                    last_ts = last["ts_utc"]
                    last_total = last["total_views"]

                    last_ist = last_ts.astimezone(IST)

                    # same half-hour bucket → skip
                    if (
                        last_ist.hour == now_ist.hour
                        and (last_ist.minute // 30) == (now_ist.minute // 30)
                    ):
                        skip = True

                    # unchanged total → skip
                    if last_total == total:
                        skip = True

                if skip:
                    log.debug("MrBeast sampler: skipped duplicate / unchanged snapshot.")
                    continue

                cur.execute(
                    """
                    INSERT INTO channel_stats (channel_id, ts_utc, total_views, source)
                    VALUES (%s, %s, %s, %s)
                    ON CONFLICT DO NOTHING
                    """,
                    (MRBEAST_CHANNEL_ID, tsu, total, "uploads_sum")
                )

                log.info(
                    "MrBeast snapshot stored: ts=%s total=%s",
                    tsu.isoformat(),
                    total
                )

        except Exception as e:
            log.exception("MrBeast sampler error: %s", e)
            time.sleep(5)

def mrbeast_10min_sampler_loop():
    """
    Background loop — every IST 10-minute boundary:
      - fetch uploads list (cached) and sum viewCounts for all videos
      - insert into channel_stats with source='uploads_sum_10min'
      - skip if same 10-min bucket as last snapshot or if total unchanged
    """
    log.info("MrBeast 10-min sampler started (IST 10-min uploads-sum).")
    client = MR_YT if MR_YT else YOUTUBE
    if not client:
        log.warning("No YouTube client available for MrBeast 10-min sampler.")
        return

    # warm cache
    try:
        _mr_get_all_video_ids(use_cache=True)
    except Exception:
        pass

    while True:
        try:
            sleep_until_next_10min_IST()
            tsu = current_10min_utc_from_ist()
            now_ist = tsu.astimezone(IST)

            # get video ids (try cached)
            video_ids = _mr_get_all_video_ids(use_cache=True)
            if not video_ids:
                # try aggressive non-cached fetch once
                video_ids = _mr_get_all_video_ids(use_cache=False)
                if not video_ids:
                    log.warning("MrBeast 10-min sampler: no video IDs.")
                    continue

            total = _mr_sum_views_for_video_ids(video_ids)
            if total is None:
                log.warning("MrBeast 10-min sampler: total is None.")
                continue

            conn = db()
            with conn.cursor() as cur:
                cur.execute(
                    "SELECT ts_utc, total_views FROM channel_stats "
                    "WHERE channel_id=%s AND source='uploads_sum_10min' "
                    "ORDER BY ts_utc DESC LIMIT 1",
                    (MRBEAST_CHANNEL_ID,)
                )
                last = cur.fetchone()

                skip = False
                if last:
                    last_ts = last["ts_utc"]
                    last_total = last["total_views"]
                    last_ist = last_ts.astimezone(IST)

                    # same 10-min bucket -> skip
                    if (
                        last_ist.hour == now_ist.hour
                        and (last_ist.minute // 10) == (now_ist.minute // 10)
                    ):
                        skip = True

                    # unchanged total -> skip
                    if last_total == total:
                        skip = True

                if skip:
                    log.debug("MrBeast 10-min sampler: skipped duplicate / unchanged snapshot.")
                    continue

                cur.execute(
                    """
                    INSERT INTO channel_stats (channel_id, ts_utc, total_views, source)
                    VALUES (%s, %s, %s, %s)
                    ON CONFLICT DO NOTHING
                    """,
                    (MRBEAST_CHANNEL_ID, tsu, total, "uploads_sum_10min")
                )

                log.info("MrBeast 10-min snapshot stored: ts=%s total=%s", tsu.isoformat(), total)

        except Exception as e:
            log.exception("MrBeast 10-min sampler error: %s", e)
            time.sleep(5)


def start_background():
    global _sampler_started
    with _sampler_lock:
        if not _sampler_started:
            t = threading.Thread(target=sampler_loop, daemon=True, name="yt-sampler")
            t.start()
            log.info("Background sampler started.")
            # start MRBeast sampler if configured
               # start MRBeast sampler if configured
            if (MR_YT or YOUTUBE) and MRBEAST_CHANNEL_ID:
                t2 = threading.Thread(target=mrbeast_sampler_loop, daemon=True, name="mrbeast-sampler")
                t2.start()
                log.info("MRBeast sampler thread started.")

             # start 10-min uploads-sum sampler
                t3 = threading.Thread(target=mrbeast_10min_sampler_loop, daemon=True, name="mrbeast-10min-sampler")
                t3.start()
                log.info("MRBeast 10-min sampler thread started.")

            _sampler_started = True


# -----------------------------
# Helper: build display data for one video
# -----------------------------
# -----------------------------
# Helper: build display data for one video
# -----------------------------
def build_video_display(vid: str):
    """
    Build display data for a video:
     - fetches only recent rows (bounded window)
     - uses process_gains (bisect-based)
     - caches results for a short TTL
     - also fetches a fixed reference video (REF_COMPARE_VIDEO_ID) to compute a per-row
       5-minute ratio against that reference video's 5-min gain.

    Returns dict suitable for templates (same shape as earlier code).
    """
    nowu = now_utc()

    # try short in-memory cache
    with _video_display_cache_lock:
        ent = _video_display_cache.get(vid)
        if ent:
            cached_obj, fetched_at = ent
            if time.time() - fetched_at <= _VIDEO_DISPLAY_CACHE_TTL:
                return cached_obj

    conn = db()
    with conn.cursor() as cur:
        cur.execute(
            "SELECT video_id, name, is_tracking, thumbnail_url, thumbnail_prev_url, thumbnail_changed, thumbnail_changed_at "
            "FROM video_list WHERE video_id=%s AND is_deleted=FALSE",
            (vid,)
        )
        vrow = cur.fetchone()
        if not vrow:
            return None

        # compute earliest timestamp to fetch (+2 days margin for interpolation)
        start_utc = (nowu - timedelta(days=_MAX_DISPLAY_DAYS + 2))

        # fetch rows for main video in window (chronological)
        cur.execute(
            "SELECT ts_utc, views, likes, comments FROM views WHERE video_id=%s AND ts_utc >= %s ORDER BY ts_utc ASC",
            (vid, start_utc)
        )
        all_rows = cur.fetchall()

        # fetch reference video rows (for 5-min ratio)
        ref_rows = None
        try:
            cur.execute(
                "SELECT ts_utc, views, likes, comments FROM views WHERE video_id=%s AND ts_utc >= %s ORDER BY ts_utc ASC",
                (REF_COMPARE_VIDEO_ID, start_utc)
            )
            ref_rows = cur.fetchall()
        except Exception:
            ref_rows = None

    # prepare outputs
    daily = {}
    latest_views = None
    latest_ts = None
    latest_ts_iso = None
    latest_ts_ist = None
    compare_meta = None

    if all_rows:
        # processed_all is chronological list of tuples from process_gains
        processed_all = process_gains(all_rows)
        midpoint_by_epoch = {}
        midpoint_epochs = []
        for tpl in processed_all:
            if len(tpl) <= 7 or tpl[7] is None:
                continue
            try:
                ep = int(datetime.fromisoformat(tpl[0]).replace(tzinfo=IST).timestamp())
            except Exception:
                continue
            midpoint_by_epoch[ep] = tpl[7]
            midpoint_epochs.append(ep)
        midpoint_epochs.sort()

        # build grouped maps for main video
        grouped = {}
        for tpl in processed_all:
            ts_ist = tpl[0]  # "YYYY-MM-DD HH:MM:SS"
            date_str = ts_ist.split(" ")[0]
            grouped.setdefault(date_str, []).append(tpl)

        # processed ref rows into date/time map if available
        ref_time_map = {}
        if ref_rows:
            ref_processed = process_gains(ref_rows)
            for rtpl in ref_processed:
                r_ts = rtpl[0]
                r_date, r_time = r_ts.split(" ")
                ref_time_map.setdefault(r_date, {})[r_time] = rtpl

        # iterate dates newest-first
        dates_sorted = sorted(grouped.keys(), reverse=True)
        for date_str in dates_sorted:
            processed = grouped[date_str]
            display_rows = []

            # track previous likes for same-date chronological samples so we can compute likes gain
            prev_likes_for_date = None

            for tpl in processed:
                # tpl: (ts_ist, views, gain_5m, hourly_views_gain, hourly_likes_gain, gain_24h,
                #       daily_views_gain, gain_24h_midpoint_ist, likes_val, comments_val)
                (ts_ist, views, gain_5m, hourly_views_gain, hourly_likes_gain, gain_24h,
                 daily_views_gain, gain_24h_midpoint_ist, likes_val, comments_val) = tpl
                time_part = ts_ist.split(" ")[1]

                midpoint_diff_24h = None
                if gain_24h_midpoint_ist is not None:
                    try:
                        target_epoch = int((datetime.fromisoformat(ts_ist).replace(tzinfo=IST) - timedelta(days=1)).timestamp())
                        i_mid = bisect.bisect_left(midpoint_epochs, target_epoch)
                        candidate_epochs = []
                        if i_mid < len(midpoint_epochs):
                            candidate_epochs.append(midpoint_epochs[i_mid])
                        if i_mid > 0:
                            candidate_epochs.append(midpoint_epochs[i_mid - 1])
                        prior_midpoint_ist = None
                        if candidate_epochs:
                            best_epoch = min(candidate_epochs, key=lambda e: abs(e - target_epoch))
                            if abs(best_epoch - target_epoch) <= 5:
                                prior_midpoint_ist = midpoint_by_epoch.get(best_epoch)
                        if prior_midpoint_ist is not None:
                            midpoint_diff_24h = format_signed_hms_diff(
                                datetime.fromisoformat(gain_24h_midpoint_ist),
                                datetime.fromisoformat(prior_midpoint_ist),
                            )
                    except Exception:
                        midpoint_diff_24h = None

                # --- 5-min ratio against REF_COMPARE_VIDEO_ID ---
                five_min_ratio = None
                if ref_time_map:
                    ref_map_for_date = ref_time_map.get(date_str, {})
                    ref_match = find_closest_prev(ref_map_for_date, time_part, max_earlier_seconds=300)
                    if not ref_match:
                        prev_ref_map = ref_time_map.get((datetime.fromisoformat(date_str).date() - timedelta(days=1)).isoformat(), {})
                        ref_match = find_closest_prev(prev_ref_map, time_part, max_earlier_seconds=300)
                    if ref_match:
                        try:
                            ref_gain5 = ref_match[2]  # gain_5m of reference stays at index 2
                        except Exception:
                            ref_gain5 = None
                        if gain_5m not in (None,) and ref_gain5 not in (None, 0):
                            try:
                                five_min_ratio = round(gain_5m / ref_gain5, 3)
                            except Exception:
                                five_min_ratio = None

                # ---------- compute likes gain (vs previous sample on same date) ----------
                likes_gain = None
                try:
                    if likes_val is not None and prev_likes_for_date is not None:
                        likes_gain = int(likes_val) - int(prev_likes_for_date)
                except Exception:
                    likes_gain = None
                # update previous likes tracker for next iteration
                prev_likes_for_date = likes_val

                # --- engagement rate computation uses absolute likes/comments (not the gain) ---
                engagement_rate = None
                try:
                    if views and views != 0:
                        likes_n = likes_val or 0
                        comments_n = comments_val or 0
                        engagement_rate = round(((likes_n + comments_n) / float(views)) * 100.0, 3)
                except Exception:
                    engagement_rate = None

                # (ts_ist, views, gain_5m, hourly_views_gain, hourly_likes_gain, gain_24h,
                #  daily_views_gain, gain_24h_midpoint_ist, five_min_ratio,
                #  likes_gain, comments_val, engagement_rate, midpoint_diff_24h)
                display_rows.append((
                    ts_ist, views, gain_5m, hourly_views_gain, hourly_likes_gain, gain_24h,
                    daily_views_gain, gain_24h_midpoint_ist, five_min_ratio,
                    likes_gain, comments_val, engagement_rate, midpoint_diff_24h
                ))

            # newest-first for UI
            daily[date_str] = list(reversed(display_rows))

        # latest summary values
        latest_views = all_rows[-1]["views"]
        latest_ts = all_rows[-1]["ts_utc"]
        latest_ts_iso = latest_ts.isoformat() if latest_ts is not None else None
        latest_ts_ist = latest_ts.astimezone(IST).strftime("%Y-%m-%d %H:%M:%S") if latest_ts is not None else None

    # channel info (same logic but only for this video)
    channel_info = {
        "channel_id": None,
        "channel_total": None,
        "channel_prev_total": None,
        "channel_gain_since_prev": None,
        "channel_gain_24h": None
    }
    if YOUTUBE:
        ch = fetch_channel_id_for_videos([vid]).get(vid)
        if ch:
            channel_info["channel_id"] = ch
            with conn.cursor() as cur:
                cur.execute("SELECT ts_utc, total_views FROM channel_stats WHERE channel_id=%s ORDER BY ts_utc ASC", (ch,))
                rows = cur.fetchall()
            if rows:
                channel_info["channel_total"] = rows[-1]["total_views"]
                if len(rows) > 1:
                    channel_info["channel_prev_total"] = rows[-2]["total_views"]
                    if channel_info["channel_prev_total"] is not None and channel_info["channel_total"] is not None:
                        channel_info["channel_gain_since_prev"] = channel_info["channel_total"] - channel_info["channel_prev_total"]
                target_24 = rows[-1]["ts_utc"] - timedelta(days=1)
                interp = interpolate_at(rows, target_24, key="total_views")
                ref_24 = int(round(interp)) if interp is not None else None
                if ref_24 is not None and channel_info["channel_total"] is not None:
                    channel_info["channel_gain_24h"] = channel_info["channel_total"] - ref_24

    # targets
    with conn.cursor() as cur:
        cur.execute("SELECT id, target_views, target_ts, note FROM targets WHERE video_id=%s ORDER BY target_ts ASC", (vid,))
        target_rows = cur.fetchall()
    targets_display = []
    for t in target_rows:
        tid = t["id"]; t_views = t["target_views"]; t_ts = t["target_ts"]; note = t["note"]
        remaining_views = t_views - (latest_views or 0)
        remaining_seconds = (t_ts - nowu).total_seconds()
        if remaining_views <= 0:
            status = "reached"; req_hr = req_5m = 0
        elif remaining_seconds <= 0:
            status = "overdue"; req_hr = math.ceil(remaining_views); req_5m = math.ceil(req_hr / 12)
        else:
            status = "active"; hrs = max(remaining_seconds / 3600.0, 1 / 3600); req_hr = math.ceil(remaining_views / hrs); req_5m = math.ceil(req_hr / 12)
        targets_display.append({
            "id": tid,
            "target_views": t_views,
            "target_ts_ist": t_ts.astimezone(IST).strftime("%Y-%m-%d %H:%M:%S"),
            "note": note,
            "status": status,
            "required_per_hour": req_hr,
            "required_per_5min": req_5m,
            "remaining_views": remaining_views,
            "remaining_seconds": int(remaining_seconds)
        })

    compare_meta = None

    result = {
        "video_id": vrow["video_id"],
        "name": vrow["name"],
        "is_tracking": bool(vrow["is_tracking"]),
        "daily": daily,
        "targets": targets_display,
        "latest_views": latest_views,
        "latest_ts": latest_ts,
        "latest_ts_iso": latest_ts_iso,
        "latest_ts_ist": latest_ts_ist,
        "channel_info": channel_info,
        "compare_meta": compare_meta,
        "thumbnail_url": vrow.get("thumbnail_url"),
        "thumbnail_prev_url": vrow.get("thumbnail_prev_url"),
        "thumbnail_changed": bool(vrow.get("thumbnail_changed")),
        "thumbnail_changed_at": vrow.get("thumbnail_changed_at")
    }

    # cache it
    with _video_display_cache_lock:
        _video_display_cache[vid] = (result, time.time())

    return result


# -----------------------------
# Auth routes
# -----------------------------
@app.route("/login", methods=["GET", "POST"])
def login():
    # if already logged in, send to home
    if g.get("user"):
        return redirect(url_for("home"))

    if request.method == "POST":
        username = (request.form.get("username") or "").strip()
        password = request.form.get("password") or ""
        next_url = request.args.get("next") or url_for("home")

        if not username or not password:
            flash("Enter username and password.", "warning")
            return redirect(url_for("login", next=next_url))

        conn = db()
        with conn.cursor() as cur:
            cur.execute(
                "SELECT id, username, password_hash, current_session_token, "
                "is_active, device_token, device_ua, device_info "
                "FROM users WHERE username=%s",
                (username,)
            )
            user = cur.fetchone()

        # invalid username/password
        if not user or not check_password_hash(user["password_hash"], password):
            flash("Invalid credentials.", "danger")
            return redirect(url_for("login", next=next_url))

        # deactivated user
        if not user["is_active"]:
            flash("Your account is deactivated. Contact admin at 1944pranav@gmail.com.", "danger")
            return redirect(url_for("login", next=next_url))

        # ---------- Device lock: mix of cookie token + fingerprint ----------
        ua_now = request.headers.get("User-Agent", "") or ""
        cookie_device = request.cookies.get("device_token")
        stored_device = user.get("device_token")
        stored_ua = (user.get("device_ua") or "")

        # simple fingerprint now: just user-agent (can extend later)
        fingerprint_now = ua_now.strip()
        stored_fingerprint = (user.get("device_info") or "").strip()

        def same_device():
            # 1) Strong match: cookie token matches DB
            if stored_device and cookie_device and cookie_device == stored_device:
                return True
            # 2) Fallback: UA / fingerprint match (handles cookie cleared on same device)
            if stored_fingerprint and fingerprint_now and stored_fingerprint == fingerprint_now:
                return True
            # 3) If no device stored yet, we will bind below, so not "same"
            return False

        if stored_device is None:
            # First login: bind current device
            new_device_token = secrets.token_hex(32)
            with conn.cursor() as cur:
                cur.execute(
                    "UPDATE users SET device_token=%s, device_ua=%s, device_info=%s WHERE id=%s",
                    (new_device_token, ua_now, fingerprint_now, user["id"])
                )
            stored_device = new_device_token
        else:
            # Device already bound: ensure this is the same device
            if not same_device():
                flash("Login only allowed from your registered device. Contact admin at 1944pranav@gmail.com to reset.", "danger")
                return redirect(url_for("login", next=next_url))

        # ---------- Session token: latest login wins (on this device) ----------
        session_token = secrets.token_hex(32)
        with conn.cursor() as cur:
            cur.execute(
                "UPDATE users SET current_session_token=%s WHERE id=%s",
                (session_token, user["id"])
            )

        # 👇 IMPORTANT: make session persistent
        session.clear()
        session.permanent = True          # <--- add this line
        session["user_id"] = user["id"]
        session["session_token"] = session_token

        # build response so we can set device cookie
        resp = make_response(redirect(next_url))
        # keep device cookie valid ~1 year
        if stored_device:
            resp.set_cookie("device_token", stored_device, max_age=365*24*3600, httponly=True, samesite="Lax")
        return resp

    # GET
    return render_template("login.html")



# -----------------------------
# Stats helpers & routes
# -----------------------------
from zoneinfo import ZoneInfo as _ZoneInfo
EST = _ZoneInfo("America/New_York")

def format_millions(n: Optional[int]) -> str:
    if n is None:
        return "—"
    return f"{n/1_000_000:.2f}M"

def format_count(n: Optional[int]) -> str:
    if n is None:
        return "—"
    # if >=1000 show K for compactness, but keep comma if <100k
    if abs(n) >= 1000:
        # round to nearest thousand for UI compactness (e.g. 150000 -> 150k)
        return f"{int(round(n/1000.0)):,}k"
    return f"{n:,}"

def fetch_daily_gains(video_id: str):
    """
    Returns list of dicts ordered newest-first:
      [{"ist_date": "2025-11-28", "daily_gain": 1234567, "end_views": 56048445}, ...]

    Daily gain is:
      value_at(D @ 22:30 IST) - value_at((D-1) @ 22:30 IST)

    It automatically figures out the available IST date range from the data and
    computes for every date in [first_IST_date, latest_IST_date].
    """
    conn = db()
    with conn.cursor() as cur:
        cur.execute(
            "SELECT MIN(ts_utc) AS first_ts, MAX(ts_utc) AS latest_ts "
            "FROM views WHERE video_id=%s",
            (video_id,)
        )
        r = cur.fetchone()

    if not r or not r["latest_ts"]:
        return []

    first_ts = r["first_ts"]
    latest_ts = r["latest_ts"]

    # Convert to IST dates
    first_ist_date = first_ts.astimezone(IST).date()
    latest_ist_date = latest_ts.astimezone(IST).date()

    # We need data from (first_ist_date - 1 @22:30) up to (latest_ist_date @22:30),
    # with a 1-hour buffer on both sides so interpolation has neighbors.
    earliest_target_ist = first_ist_date - timedelta(days=1)
    earliest_needed_dt_ist = datetime(
        earliest_target_ist.year, earliest_target_ist.month, earliest_target_ist.day,
        22, 30, tzinfo=IST
    ) - timedelta(hours=1)

    latest_needed_dt_ist = datetime(
        latest_ist_date.year, latest_ist_date.month, latest_ist_date.day,
        22, 30, tzinfo=IST
    ) + timedelta(hours=1)

    fetch_start_utc = earliest_needed_dt_ist.astimezone(timezone.utc)
    fetch_end_utc = latest_needed_dt_ist.astimezone(timezone.utc)

    # Fetch only relevant rows (chronological)
    with conn.cursor() as cur:
        cur.execute(
            "SELECT ts_utc, views FROM views "
            "WHERE video_id=%s AND ts_utc >= %s AND ts_utc <= %s "
            "ORDER BY ts_utc ASC",
            (video_id, fetch_start_utc, fetch_end_utc)
        )
        rows = cur.fetchall()

    rows_asc = [{"ts_utc": rr["ts_utc"], "views": int(rr["views"])} for rr in rows]

    out = []
    # iterate IST dates from latest -> earliest
    d = latest_ist_date
    while d >= first_ist_date:
        # current day 22:30 IST
        target_dt_ist = datetime(d.year, d.month, d.day, 22, 30, tzinfo=IST)
        target_utc = target_dt_ist.astimezone(timezone.utc)

        # previous day 22:30 IST
        prev_dt_ist = target_dt_ist - timedelta(days=1)
        prev_utc = prev_dt_ist.astimezone(timezone.utc)

        # --- interpolate "now" ---
        try:
            val_now = interpolate_at(rows_asc, target_utc, key="views")
        except Exception:
            val_now = None

        if val_now is None:
            # fallback: latest sample <= target_utc
            val_now = None
            for rr in reversed(rows_asc):
                if rr["ts_utc"] <= target_utc:
                    val_now = float(rr["views"])
                    break

        # --- interpolate "prev" ---
        try:
            val_prev = interpolate_at(rows_asc, prev_utc, key="views")
        except Exception:
            val_prev = None

        if val_prev is None:
            # fallback: latest sample <= prev_utc
            val_prev = None
            for rr in reversed(rows_asc):
                if rr["ts_utc"] <= prev_utc:
                    val_prev = float(rr["views"])
                    break

        daily_gain = None
        end_views = None

        if val_now is not None:
            try:
                end_views = int(round(val_now))
            except Exception:
                end_views = None

        if val_now is not None and val_prev is not None:
            try:
                daily_gain = int(round(val_now - val_prev))
            except Exception:
                daily_gain = None

        out.append({
            "ist_date": d.isoformat(),
            "daily_gain": daily_gain,
            "end_views": end_views
        })

        d -= timedelta(days=1)

    # newest-first (we already built it newest-first)
    return out



def fetch_hourly_for_ist_date(video_id: str, date_ist):
    """
    date_ist: datetime.date in IST timezone to analyze.
    Returns list of 24 dicts for hours 0..23:
      [{"hour": 0, "label": "00:00-01:00", "end_views": 12345, "hour_gain": 2345}, ...]
    Uses interpolation at end of each hour (IST) when needed.
    """
    # build day start/end in IST then convert to UTC for DB fetch
    start_ist = datetime(date_ist.year, date_ist.month, date_ist.day, 0, 0, 0, tzinfo=IST)
    end_ist = start_ist + timedelta(days=1)
    start_utc = start_ist.astimezone(timezone.utc)
    end_utc = end_ist.astimezone(timezone.utc)

    conn = db()
    with conn.cursor() as cur:
        cur.execute(
            "SELECT ts_utc, views FROM views WHERE video_id=%s AND ts_utc >= %s AND ts_utc < %s ORDER BY ts_utc ASC",
            (video_id, start_utc, end_utc)
        )
        rows = cur.fetchall()

    # convert rows into list for interpolate_at
    rows_asc = [{"ts_utc": r["ts_utc"], "views": int(r["views"])} for r in rows]

    results = []
    prev_end_views = None
    for h in range(24):
        end_hour_ist = start_ist + timedelta(hours=h+1)
        end_hour_utc = end_hour_ist.astimezone(timezone.utc)

        # try interpolation first
        interp = interpolate_at(rows_asc, end_hour_utc, key="views")
        if interp is not None:
            try:
                end_views = int(round(interp))
            except Exception:
                end_views = None
        else:
            # fallback: latest sample <= end_hour_utc
            end_views = None
            for r in reversed(rows_asc):
                if r["ts_utc"] <= end_hour_utc:
                    end_views = int(r["views"])
                    break

        hour_gain = None
        if end_views is not None and prev_end_views is not None:
            try:
                hour_gain = int(end_views - prev_end_views)
            except Exception:
                hour_gain = None

        # set prev_end_views for next iteration
        if end_views is not None:
            prev_end_views = end_views

        label = f"{(h):02d}:00–{(h+1):02d}:00"
        results.append({
            "hour": h,
            "label": label,
            "end_views": end_views,
            "hour_gain": hour_gain
        })

    return results

# Route: stats page
@app.get("/video/<video_id>/stats")
@login_required
def video_stats(video_id):
    # pick IST date from query param ?date=YYYY-MM-DD else default latest IST date available
    sel_date_str = request.args.get("date")
    conn = db()
    with conn.cursor() as cur:
        cur.execute("SELECT MAX(ts_utc) AS latest_ts FROM views WHERE video_id=%s", (video_id,))
        r = cur.fetchone()
        if not r or not r["latest_ts"]:
            flash("No data available for this video.", "warning")
            return redirect(url_for("video_detail", video_id=video_id))
        latest_ts = r["latest_ts"]
        latest_ist_date = latest_ts.astimezone(IST).date()

    if sel_date_str:
        try:
            sel_date = datetime.fromisoformat(sel_date_str).date()
        except Exception:
            sel_date = latest_ist_date
    else:
        sel_date = latest_ist_date

    daily = fetch_daily_gains(video_id)
    hourly = fetch_hourly_for_ist_date(video_id, sel_date)

    with conn.cursor() as cur:
        cur.execute("""
            SELECT DISTINCT ((ts_utc AT TIME ZONE 'UTC') AT TIME ZONE 'Asia/Kolkata')::date AS ist_date
            FROM views WHERE video_id=%s ORDER BY ist_date DESC
        """, (video_id,))
        date_rows = cur.fetchall()
    ist_dates = [r["ist_date"].isoformat() for r in date_rows]

    return render_template(
        "video_stats.html",
        video_id=video_id,
        daily=daily,
        hourly=hourly,
        selected_date=sel_date.isoformat(),
        ist_dates=ist_dates
    )

@app.get("/logout")
@login_required
def logout():
    conn = db()
    with conn.cursor() as cur:
        cur.execute("UPDATE users SET current_session_token=NULL WHERE id=%s", (g.user["id"],))
    session.clear()
    flash("Logged out.", "info")
    return redirect(url_for("login"))


@app.route("/admin/users", methods=["GET", "POST"])
def admin_users():
    """
    Admin page:
      - Step 1: Ask for admin password (ADMIN_CREATE_SECRET) on a separate gate page.
      - Step 2: After unlocked (session['admin_ok'] = True), allow:
          * Create users
          * Activate / deactivate users
          * Reset device lock for a user
          * Force logout a user
    """
    conn = db()

    if request.method == "POST":
        action = request.form.get("action") or ""

        # 1) Unlock admin mode (from admin_gate.html)
        if action == "unlock":
            admin_secret = (request.form.get("admin_secret") or "").strip()

            if not ADMIN_CREATE_SECRET:
                flash("ADMIN_CREATE_SECRET not configured on server.", "danger")
                return render_template("admin_gate.html")

            if admin_secret != ADMIN_CREATE_SECRET:
                flash("Invalid admin password.", "danger")
                return render_template("admin_gate.html")

            # mark admin session as unlocked
            session["admin_ok"] = True
            flash("Admin mode unlocked.", "success")
            return redirect(url_for("admin_users"))

        # For all other actions, require unlocked admin session
        if not session.get("admin_ok"):
            flash("Admin access required.", "danger")
            return render_template("admin_gate.html")

        # 2) CREATE USER
        if action == "create":
            username = (request.form.get("username") or "").strip()
            password = request.form.get("password") or ""

            if not username or not password:
                flash("Enter username and password.", "warning")
                return redirect(url_for("admin_users"))

            pw_hash = generate_password_hash(password)
            try:
                with conn.cursor() as cur:
                    cur.execute(
                        "INSERT INTO users (username, password_hash, is_active) "
                        "VALUES (%s, %s, TRUE)",
                        (username, pw_hash)
                    )
                flash(f"User '{username}' created.", "success")
            except Exception as e:
                log.exception("Create user failed: %s", e)
                flash("Could not create user (maybe username already exists).", "danger")

        # 3) TOGGLE ACTIVE (activate / deactivate)
        elif action == "toggle_active":
            try:
                user_id = int(request.form.get("user_id") or "0")
                new_state = request.form.get("new_state")  # "1" or "0"
            except ValueError:
                flash("Invalid user id.", "danger")
                return redirect(url_for("admin_users"))

            is_active = True if new_state == "1" else False
            try:
                with conn.cursor() as cur:
                    cur.execute(
                        "UPDATE users SET is_active=%s WHERE id=%s",
                        (is_active, user_id)
                    )
                flash(("Activated" if is_active else "Deactivated") + f" user id {user_id}.", "info")
            except Exception as e:
                log.exception("Toggle active failed: %s", e)
                flash("Could not update user status.", "danger")

        # 4) RESET DEVICE (clear device lock)
        elif action == "reset_device":
            try:
                user_id = int(request.form.get("user_id") or "0")
            except ValueError:
                flash("Invalid user id.", "danger")
                return redirect(url_for("admin_users"))

            try:
                with conn.cursor() as cur:
                    cur.execute("""
                        UPDATE users
                        SET device_token = NULL,
                            device_ua = NULL,
                            device_info = NULL
                        WHERE id = %s
                    """, (user_id,))
                flash(f"Device lock reset for user id {user_id}.", "info")
            except Exception as e:
                log.exception("Reset device failed: %s", e)
                flash("Could not reset device.", "danger")

        # 5) FORCE LOGOUT (invalidate current session token)
        elif action == "force_logout":
            try:
                user_id = int(request.form.get("user_id") or "0")
            except ValueError:
                flash("Invalid user id.", "danger")
                return redirect(url_for("admin_users"))

            try:
                with conn.cursor() as cur:
                    cur.execute(
                        "UPDATE users SET current_session_token = NULL WHERE id = %s",
                        (user_id,)
                    )
                flash(f"User id {user_id} has been logged out.", "info")
            except Exception as e:
                log.exception("Force logout failed: %s", e)
                flash("Could not log out user.", "danger")

        return redirect(url_for("admin_users"))

    # ---------- GET ----------
    # If admin mode not unlocked yet -> show gate page
    if not session.get("admin_ok"):
        return render_template("admin_gate.html")

    # If unlocked, show full user list
    with conn.cursor() as cur:
        cur.execute("""
            SELECT
              id,
              username,
              is_active,
              (current_session_token IS NOT NULL) AS is_logged_in
            FROM users
            ORDER BY username
        """)
        users = cur.fetchall()

    return render_template("admin_users.html", users=users)




# -----------------------------
# Routes (protected)
# -----------------------------
@app.get("/healthz")
def healthz():
    return "ok", 200

@app.get("/")
@login_required
def home():
    t0 = time.time()
    conn = db()
    with conn.cursor() as cur:
        cur.execute("SELECT video_id, name, is_tracking FROM video_list WHERE is_deleted=FALSE ORDER BY name")
        videos = cur.fetchall()
    t_db_videos = time.time()

    video_ids = [v["video_id"] for v in videos]
    vids = []

    # 1) fetch channel ids (may use in-memory API cache)
    ch_map = fetch_channel_id_for_videos(video_ids) if YOUTUBE and video_ids else {}
    t_ch_map = time.time()

    # 2) batch-read latest channel totals from DB (fast)
    unique_chs = sorted({ch for ch in ch_map.values() if ch})
    channel_totals = get_latest_channel_totals_for(unique_chs) if unique_chs else {}
    t_ch_totals = time.time()

    # 3) batch-read latest view sample per video
    latest_samples = get_latest_sample_per_video(video_ids) if video_ids else {}
    t_latest_samples = time.time()

    for v in videos:
        vid = v["video_id"]
        thumb = f"https://i.ytimg.com/vi/{vid}/hqdefault.jpg"
        short_title = v["name"] if len(v["name"]) <= 60 else v["name"][:57] + "..."
        channel_id = ch_map.get(vid)
        channel_total = channel_totals.get(channel_id) if channel_id else None

        latest = latest_samples.get(vid)
        latest_views = latest["views"] if latest else None
        latest_ts = latest["ts_utc"] if latest else None
        latest_ts_ist = latest_ts.astimezone(IST).strftime("%Y-%m-%d %H:%M:%S") if latest_ts else None

        vids.append({
            "video_id": vid,
            "name": v["name"],
            "short_title": short_title,
            "thumbnail": thumb,
            "is_tracking": bool(v["is_tracking"]),
            "channel_total_cached": channel_total,
            "latest_views": latest_views,
            "latest_ts": latest_ts,
            "latest_ts_ist": latest_ts_ist
        })

    t_end = time.time()
    # Optional timing logs to help you measure improvements
    log.info("home timings: db_videos=%.3fs ch_map=%.3fs ch_totals=%.3fs latest_samples=%.3fs total=%.3fs",
             t_db_videos - t0, t_ch_map - t_db_videos, t_ch_totals - t_ch_map, t_latest_samples - t_ch_totals, t_end - t0)

    return render_template("home.html", videos=vids)


@app.get("/home/json")
@login_required
def home_json():
    conn = db()
    with conn.cursor() as cur:
        cur.execute("SELECT video_id FROM video_list WHERE is_deleted=FALSE ORDER BY name")
        video_rows = cur.fetchall()

    video_ids = [v["video_id"] for v in video_rows]
    latest_samples = get_latest_sample_per_video(video_ids) if video_ids else {}

    payload = []
    for vid in video_ids:
        latest = latest_samples.get(vid)
        latest_views = latest["views"] if latest else None
        latest_ts = latest["ts_utc"] if latest else None
        latest_ts_ist = latest_ts.astimezone(IST).strftime("%Y-%m-%d %H:%M:%S") if latest_ts else None
        payload.append({
            "video_id": vid,
            "latest_views": latest_views,
            "latest_ts_ist": latest_ts_ist
        })

    return jsonify({"videos": payload})

@app.get("/mrbeast_sum")
@login_required
def mrbeast_sum_stats():
    """
    Shows MRBeast channel total views from uploads-sum (10-minute sampler).
    Route: /mrbeast_sum
    """
    if not MRBEAST_CHANNEL_ID:
        flash("MRBeast channel not configured.", "warning")
        return redirect(url_for("home"))

    conn = db()
    with conn.cursor() as cur:
        # prefer the uploads_sum_10min source first
        cur.execute(
            """
            SELECT ts_utc, total_views, source
            FROM channel_stats
            WHERE channel_id=%s AND source='uploads_sum_10min'
            ORDER BY ts_utc DESC
            LIMIT 240
            """,
            (MRBEAST_CHANNEL_ID,)
        )
        rows = cur.fetchall()

        # fallback to any rows if none
        if not rows:
            cur.execute(
                """
                SELECT ts_utc, total_views, source
                FROM channel_stats
                WHERE channel_id=%s
                ORDER BY ts_utc DESC
                LIMIT 240
                """,
                (MRBEAST_CHANNEL_ID,)
            )
            rows = cur.fetchall()

    out = []
    prev_total = None
    for r in rows:
        total = r["total_views"]
        delta = None
        if prev_total is not None and total is not None:
            try:
                delta = total - prev_total
            except Exception:
                delta = None
        out.append({
            "ts_utc": r["ts_utc"],
            "ts_ist": r["ts_utc"].astimezone(IST).strftime("%Y-%m-%d %H:%M:%S"),
            "total": total,
            "delta": delta,
            "source": r.get("source")
        })
        prev_total = total

    return render_template(
        "mrbeast.html",  # reuse same template for display consistency
        samples=out,
        channel_id=MRBEAST_CHANNEL_ID,
        enabled=bool(MR_YT or YOUTUBE)
    )

    
@app.get("/mrbeast")
@login_required
def mrbeast_stats():
    """
    Shows MRBeast channel total views (prefers uploads_sum snapshots; falls back to legacy rows).
    """
    if not MRBEAST_CHANNEL_ID:
        flash("MRBeast channel not configured.", "warning")
        return redirect(url_for("home"))

    conn = db()
    with conn.cursor() as cur:
        # 1) try uploads_sum first
        cur.execute(
            """
            SELECT ts_utc, total_views, source
            FROM channel_stats
            WHERE channel_id=%s AND source='uploads_sum'
            ORDER BY ts_utc DESC
            LIMIT 240
            """,
            (MRBEAST_CHANNEL_ID,)
        )
        rows = cur.fetchall()

        # 2) if none found, fallback to any legacy/NULL source rows
        if not rows:
            cur.execute(
                """
                SELECT ts_utc, total_views, source
                FROM channel_stats
                WHERE channel_id=%s
                ORDER BY ts_utc DESC
                LIMIT 240
                """,
                (MRBEAST_CHANNEL_ID,)
            )
            rows = cur.fetchall()

    out = []
    prev_total = None
    # rows are newest-first already; compute delta vs previous row in that order
    for r in rows:
        total = r["total_views"]
        delta = None
        if prev_total is not None and total is not None:
            try:
                delta = total - prev_total
            except Exception:
                delta = None

        out.append({
            "ts_utc": r["ts_utc"],
            "ts_ist": r["ts_utc"].astimezone(IST).strftime("%Y-%m-%d %H:%M:%S"),
            "total": total,
            "delta": delta,
            "source": r.get("source")
        })
        prev_total = total

    # enable flag if any client available (keeps UI same)
    return render_template(
        "mrbeast.html",
        samples=out,
        channel_id=MRBEAST_CHANNEL_ID,
        enabled=bool(MR_YT or YOUTUBE)
    )



@app.get("/video/<video_id>")
@login_required
def video_detail(video_id):
    info = build_video_display(video_id)
    if info is None:
        flash("Video not found.", "warning")
        return redirect(url_for("home"))
    # prefer DB-stored thumbnail (seeded earlier). Fallback to ytimg hqdefault.
    info["thumbnail"] = info.get("thumbnail_url") or f"https://i.ytimg.com/vi/{video_id}/hqdefault.jpg"

# also pass change flags through to template (these keys already set by build_video_display)
    info["thumbnail_changed"] = info.get("thumbnail_changed", False)
    info["thumbnail_changed_at"] = info.get("thumbnail_changed_at")
    info["thumbnail_prev_url"] = info.get("thumbnail_prev_url")
    info["pooling_interval"] = POOLING_INTERVAL

    return render_template("video_detail.html", v=info)
    
@app.get("/video/<video_id>/json")
@login_required
def video_detail_json(video_id):
    """
    Return minimal JSON for the video used by the frontend to update live values.
    Use lightweight queries to keep polling fast without rebuilding full display data.
    """
    conn = db()
    with conn.cursor() as cur:
        cur.execute(
            "SELECT thumbnail_url, thumbnail_prev_url, thumbnail_changed FROM video_list WHERE video_id=%s AND is_deleted=FALSE",
            (video_id,)
        )
        vrow = cur.fetchone()
        if not vrow:
            return jsonify({"error": "not found"}), 404
        cur.execute(
            "SELECT ts_utc, views FROM views WHERE video_id=%s ORDER BY ts_utc DESC LIMIT 1",
            (video_id,)
        )
        latest = cur.fetchone()

    latest_ts = latest["ts_utc"] if latest else None
    latest_views = latest["views"] if latest else None
    latest_ts_iso = latest_ts.isoformat() if latest_ts is not None else None
    latest_ts_ist = latest_ts.astimezone(IST).strftime("%Y-%m-%d %H:%M:%S") if latest_ts is not None else None

    # resolve thumbnail the same way video_detail route does
    thumbnail = vrow.get("thumbnail_url") or f"https://i.ytimg.com/vi/{video_id}/hqdefault.jpg"

    return jsonify({
        "video_id": video_id,
        "latest_views": latest_views,
        "latest_ts_iso": latest_ts_iso,
        "latest_ts_ist": latest_ts_ist,
        "thumbnail_changed": bool(vrow.get("thumbnail_changed", False)),
        "thumbnail_url": thumbnail
    })


@app.get("/video/<video_id>/live_views")
@login_required
def video_live_views(video_id):
    api_key = get_rotating_api_key()
    if not api_key:
        return jsonify({"error": "api_key_missing"}), 503
    try:
        resp = requests.get(
            "https://www.googleapis.com/youtube/v3/videos",
            params={
                "part": "statistics",
                "id": video_id,
                "key": api_key,
                "fields": "items(statistics/viewCount)"
            },
            timeout=10
        )
        resp.raise_for_status()
        data = resp.json()
        items = data.get("items", [])
        if not items:
            return jsonify({"video_id": video_id, "live_views": None})
        view_count = items[0].get("statistics", {}).get("viewCount")
        live_views = int(view_count) if view_count is not None else None
        return jsonify({"video_id": video_id, "live_views": live_views})
    except requests.RequestException as exc:
        log.warning("Live view fetch failed for %s: %s", video_id, exc)
        return jsonify({"error": "fetch_failed"}), 502


@app.post("/video/<video_id>/refresh")
@login_required
def refresh_video_rows(video_id):
    invalidate_video_cache(video_id)
    flash("Rows refreshed from the database.", "success")
    return redirect(url_for("video_detail", video_id=video_id))

@app.get("/video/<video_id>/rows")
@login_required
def video_rows_json(video_id):
    invalidate_video_cache(video_id)
    info = build_video_display(video_id)
    if info is None:
        return jsonify({"error": "not found"}), 404
    days_html = render_template("_video_day_blocks.html", daily=info["daily"])
    dates = list(info["daily"].keys())
    return jsonify({
        "dates": dates,
        "days_html": days_html,
        "latest_ts_iso": info.get("latest_ts_iso"),
        "latest_ts_ist": info.get("latest_ts_ist")
    })


@app.post("/add_video")
@login_required
def add_video():
    link = (request.form.get("link") or "").strip()
    if not link:
        flash("Paste a YouTube link.", "warning")
        return redirect(url_for("home"))
    video_id = extract_video_id(link)
    if not video_id:
        flash("Invalid YouTube link.", "danger")
        return redirect(url_for("home"))

    title = fetch_title(video_id)
    stats = fetch_stats_batch([video_id]).get(video_id)
    if not stats:
        flash("Could not fetch stats (check API key/quota/video).", "danger")
        return redirect(url_for("home"))

    # fixed: ensure conn is created regardless of above branch
    conn = db()
    with conn.cursor() as cur:
        cur.execute("""
            INSERT INTO video_list (video_id, name, is_tracking, is_deleted)
            VALUES (%s, %s, TRUE, FALSE)
            ON CONFLICT (video_id) DO UPDATE SET name=EXCLUDED.name, is_tracking=TRUE, is_deleted=FALSE
        """, (video_id, title))

    # try to fetch & store thumbnail hash (best-effort)
    try:
        thumb_url, thumb_hash = fetch_thumbnail_hash_for_video(video_id)
        if thumb_url and thumb_hash:
            with conn.cursor() as cur:
                cur.execute(
                    "UPDATE video_list SET thumbnail_url=%s, thumbnail_hash=%s WHERE video_id=%s",
                    (thumb_url, thumb_hash, video_id)
                )
    except Exception:
        log.exception("Thumbnail seed failed for %s", video_id)

    safe_store(video_id, stats)
    flash(f"Now tracking: {title}", "success")
    return redirect(url_for("video_detail", video_id=video_id))


@app.post("/add_target/<video_id>")
@login_required
def add_target(video_id):
    tv = request.form.get("target_views", "").strip()
    tts = request.form.get("target_ts", "").strip()
    note = (request.form.get("note") or "").strip()
    if not tv or not tts:
        flash("Fill target views and target time.", "warning")
        return redirect(url_for("video_detail", video_id=video_id))
    try:
        target_views = int(tv)
        local_dt = datetime.fromisoformat(tts)
        target_ts_utc = local_dt.replace(tzinfo=IST).astimezone(timezone.utc)
    except Exception:
        flash("Invalid input.", "danger")
        return redirect(url_for("video_detail", video_id=video_id))
    conn = db()
    with conn.cursor() as cur:
        cur.execute("INSERT INTO targets (video_id, target_views, target_ts, note) VALUES (%s, %s, %s, %s)",
                    (video_id, target_views, target_ts_utc, note))
    flash("Target added.", "success")
    return redirect(url_for("video_detail", video_id=video_id))
@app.get("/remove_target/<int:target_id>")
@login_required
def remove_target(target_id):
    conn = db()
    with conn.cursor() as cur:
        cur.execute("SELECT video_id FROM targets WHERE id=%s", (target_id,))
        r = cur.fetchone()
        if not r:
            flash("Target not found.", "warning")
            return redirect(url_for("home"))
        vid = r["video_id"]
        cur.execute("DELETE FROM targets WHERE id=%s", (target_id,))
    flash("Target removed.", "info")
    return redirect(url_for("video_detail", video_id=vid))

@app.route("/stop_tracking/<video_id>", methods=("GET", "POST"))
def stop_tracking(video_id):
    """
    Toggle tracking state. Accepts GET (link) and POST (form with optional admin_secret).
    If ADMIN_CREATE_SECRET is set, require either session['admin_ok'] or the posted admin_secret.
    """
    conn = db()

    # If this is a POST from the UI, optionally require admin password (unless admin already unlocked)
    if request.method == "POST":
        # if admin mode already unlocked in session, skip password check
        if not session.get("admin_ok"):
            admin_secret = (request.form.get("admin_secret") or "").strip()
            if not ADMIN_CREATE_SECRET:
                flash("Admin password not configured on server.", "danger")
                return redirect(url_for("video_detail", video_id=video_id))
            if admin_secret != ADMIN_CREATE_SECRET:
                flash("Incorrect admin password.", "danger")
                return redirect(url_for("video_detail", video_id=video_id))

    # Toggle tracking state
    with conn.cursor() as cur:
        cur.execute("SELECT is_tracking, name FROM video_list WHERE video_id=%s AND is_deleted=FALSE", (video_id,))
        row = cur.fetchone()
        if not row:
            flash("Video not found.", "warning")
            return redirect(url_for("home"))
        new_state = not bool(row["is_tracking"])
        cur.execute("UPDATE video_list SET is_tracking=%s WHERE video_id=%s", (new_state, video_id))
        flash(("Resumed" if new_state else "Paused") + f" tracking: {row['name']}", "info")

    # Redirect back to the video detail page (or index if you prefer)
    return redirect(url_for("video_detail", video_id=video_id))


@app.post("/remove_video/<video_id>")
@login_required
def remove_video(video_id):
    # ✅ Require admin password to remove any video
    admin_secret = (request.form.get("admin_secret") or "").strip()
    if ADMIN_CREATE_SECRET and admin_secret != ADMIN_CREATE_SECRET:
        flash("Admin password required or incorrect to remove videos.", "danger")
        return redirect(url_for("video_detail", video_id=video_id))

    conn = db()
    with conn.cursor() as cur:
        cur.execute("SELECT name FROM video_list WHERE video_id=%s AND is_deleted=FALSE", (video_id,))
        row = cur.fetchone()
        if not row:
            flash("Video not found.", "warning")
            return redirect(url_for("home"))
        name = row["name"]
        cur.execute("UPDATE video_list SET is_tracking=FALSE, is_deleted=TRUE WHERE video_id=%s", (video_id,))
        flash(f"Removed '{name}' from active tracking. Historical data was preserved.", "success")
    return redirect(url_for("home"))



@app.get("/export/<video_id>")
@login_required
def export_video(video_id):
    """
    Export all stored rows for a video into Excel.
    Columns (in this order):
      Time (IST), Views, Gain (5 min), Hourly Gain (views), Hourly Likes Gain,
      Gain (24 h), Daily Gain (views), 24h Midpoint Time, Midpoint Δ vs 24h ago,
      Likes, Comments, Engagement Rate (%)
    """
    info = build_video_display(video_id)
    if info is None:
        flash("Video not found.", "warning")
        return redirect(url_for("home"))

    rows_for_df = []
    # dates sorted ascending so export is chronological (oldest first)
    dates = sorted(info["daily"].keys())
    for date in dates:
        # info["daily"][date] is newest-first in UI; reverse to earliest-first
        day_rows = list(reversed(info["daily"][date]))

        for tpl in day_rows:
            # tpl canonical shape:
            # (ts, views, gain5, hourly_views_gain, hourly_likes_gain, gain24, daily_views_gain,
            #  midpoint_24h, five_min_ratio, likes_gain, comments_val, engagement_rate, midpoint_diff_24h)
            ts = tpl[0]
            views = tpl[1] if len(tpl) > 1 else None

            # defaults
            gain5 = hourly_views_gain = hourly_likes_gain = gain24 = daily_views_gain = midpoint_24h = five_min_ratio = likes_gain = comments = engagement_rate = midpoint_diff_24h = None

            rest = list(tpl[2:])  # remaining fields after ts and views

            # Map rest by position when present
            # expected order for rest: gain5, hourly_views_gain, hourly_likes_gain, gain24, daily_views_gain, midpoint_24h, five_min_ratio, likes_gain, comments, engagement_rate, midpoint_diff_24h
            vals = rest + [None] * (11 - len(rest))
            (gain5, hourly_views_gain, hourly_likes_gain, gain24, daily_views_gain, midpoint_24h, five_min_ratio, likes_gain, comments, engagement_rate, midpoint_diff_24h) = vals[:11]

            eng_str = ""
            if engagement_rate is not None:
                try:
                    eng_str = f"{float(engagement_rate):.3f}"
                except Exception:
                    eng_str = str(engagement_rate)

            rows_for_df.append({
                "Time (IST)": ts,
                "Views": views if views is not None else "",
                "Gain (5 min)": gain5 if gain5 is not None else "",
                "Hourly Gain (views)": hourly_views_gain if hourly_views_gain is not None else "",
                "Hourly Likes Gain": hourly_likes_gain if hourly_likes_gain is not None else "",
                "Gain (24 h)": gain24 if gain24 is not None else "",
                "Daily Gain (views)": daily_views_gain if daily_views_gain is not None else "",
                "24h Midpoint Time": midpoint_24h if midpoint_24h is not None else "",
                "Midpoint Δ vs 24h ago": midpoint_diff_24h if midpoint_diff_24h is not None else "",
                "Likes": likes_gain if likes_gain is not None else "",
                "Comments": comments if comments is not None else "",
                "Engagement Rate (%)": eng_str
            })

    # Build dataframe
    df_views = pd.DataFrame(rows_for_df)

    # Targets sheet (same as before)
    conn = db()
    with conn.cursor() as cur:
        cur.execute("SELECT id, target_views, target_ts, note FROM targets WHERE video_id=%s ORDER BY target_ts ASC", (video_id,))
        target_rows = cur.fetchall()

    nowu = now_utc()
    targets_rows_for_df = []
    for t in target_rows:
        tid = t["id"]
        t_views = t["target_views"]
        t_ts = t["target_ts"]
        note = t["note"]
        latest_views = info.get("latest_views")
        remaining_views = t_views - (latest_views or 0)
        remaining_seconds = (t_ts - nowu).total_seconds()
        if remaining_views <= 0:
            status = "Reached"
            req_hr = 0
            req_5m = 0
        elif remaining_seconds <= 0:
            status = "Overdue"
            req_hr = math.ceil(remaining_views)
            req_5m = math.ceil(req_hr / 12)
        else:
            status = "Active"
            hrs = max(remaining_seconds / 3600.0, 1/3600)
            req_hr = math.ceil(remaining_views / hrs)
            req_5m = math.ceil(req_hr / 12)
        targets_rows_for_df.append({
            "Target ID": tid,
            "Target views": t_views,
            "Target time (IST)": t_ts.astimezone(IST).strftime("%Y-%m-%d %H:%M:%S"),
            "Status": status,
            "Remaining views": remaining_views,
            "Required / hr": req_hr,
            "Required / 5min": req_5m,
            "Note": note
        })

    df_targets = pd.DataFrame(targets_rows_for_df)

    # Write to Excel
    bio = BytesIO()
    with pd.ExcelWriter(bio, engine="openpyxl") as writer:
        # ensure column order in file by creating DataFrame with exact keys in order above
        cols_order = [
            "Time (IST)", "Views", "Gain (5 min)", "Hourly Gain (views)", "Hourly Likes Gain",
            "Gain (24 h)", "Daily Gain (views)", "24h Midpoint Time", "Midpoint Δ vs 24h ago", "Likes", "Comments", "Engagement Rate (%)"
        ]
        # if df_views lacks any column (edge case), create them to preserve order
        for c in cols_order:
            if c not in df_views.columns:
                df_views[c] = ""
        df_views[cols_order].to_excel(writer, index=False, sheet_name="Views")

        if not df_targets.empty:
            df_targets.to_excel(writer, index=False, sheet_name="Targets")

    bio.seek(0)
    safe = "".join(c for c in info["name"] if c.isalnum() or c in " _-").rstrip() or "export"
    return send_file(
        bio,
        as_attachment=True,
        download_name=f"{safe}_views.xlsx",
        mimetype="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"
    )



# Bootstrap
init_db()
start_background()

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.getenv("PORT", "5000")))
