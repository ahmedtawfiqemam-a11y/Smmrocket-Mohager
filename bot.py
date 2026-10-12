#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Telegram bot for SMM Rocket's Telegram services.

Configuration is read from environment variables:
  TELEGRAM_BOT_TOKEN
  SMMROCKET_API_KEY
  OWNER_TELEGRAM_ID

Runtime data is stored in bot.sqlite3.
"""

from __future__ import annotations

import asyncio
import copy
import html
import json
import logging
import os
import re
import sqlite3
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
from datetime import datetime
from decimal import Decimal, InvalidOperation, ROUND_CEILING, ROUND_HALF_UP
from typing import Any
from zoneinfo import ZoneInfo

from flask import Flask, jsonify
from waitress import serve


BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
SMM_API_KEY = os.getenv("SMMROCKET_API_KEY", "").strip()
try:
    OWNER_ID = int(os.getenv("OWNER_TELEGRAM_ID", "0").strip() or "0")
except ValueError:
    OWNER_ID = 0
CO_OWNER_IDS: set[int] = set()
BOT_USERNAME = ""
BOT_ID = 0
SUBSCRIPTION_CACHE: dict[int, tuple[float, bool]] = {}

SMM_API_URL = "https://smmrocket.shop/api/v2"
DB_PATH = os.getenv(
    "BOT_DB_PATH", os.path.join(os.path.dirname(os.path.abspath(__file__)), "bot.sqlite3")
)
POLL_TIMEOUT = 25
SERVICE_CACHE_SECONDS = 300
STATE_TTL_SECONDS = 1800
CENT = Decimal("0.01")
ZERO = Decimal("0")

logging.basicConfig(
    level=os.getenv("LOG_LEVEL", "INFO").upper(),
    format="%(asctime)s %(levelname)s %(message)s",
)
log = logging.getLogger("smmrocket-bot")
app = Flask(__name__)
BOT_READY = threading.Event()
BOT_FAILED = threading.Event()


@app.get("/")
def index():
    return "Telegram bot web server is running. Health: /healthz", 200


@app.get("/healthz")
def healthcheck():
    if BOT_FAILED.is_set():
        return jsonify({"status": "error", "bot": "not_connected"}), 503
    bot_status = "ready" if BOT_READY.is_set() else "starting"
    return jsonify({"status": bot_status}), 200


# The IDs are from a public Telegram Premium emoji catalogue. The bot asks
# Telegram for each sticker's real alt emoji before using it in message text.
# Source: https://github.com/Zulut30/premium-telegram-emoji
PREMIUM_EMOJI = {
    "check": ("5206607081334906820", "✅"),
    "cross": ("5210952531676504517", "❌"),
    "bell": ("5458603043203327669", "🔔"),
    "plus": ("5397916757333654639", "➕"),
    "star": ("5438496463044752972", "⭐"),
    "settings": ("5341715473882955310", "⚙️"),
    "lock": ("5296369303661067030", "🔒"),
    "pin": ("5397782960512444700", "📌"),
    "like": ("5337080053119336309", "👍"),
    "fire": ("5424972470023104089", "🔥"),
    "free": ("5406756500108501710", "🆓"),
    "loading": ("5386367538735104399", "⏳"),
    "calendar": ("5413879192267805083", "📅"),
    "wallet": ("5769403330761593044", "👛"),
    "heart": ("5994453058656931434", "❤️"),
    "warning": ("5431445849026611010", "⚠️"),
    "shield": ("5197288647275071607", "🛡️"),
    "telegram": ("5206208353751024833", "✈️"),
    "info": ("5323442290708985472", "ℹ️"),
}
AVAILABLE_EMOJI_IDS: set[str] = set()
EMOJI_ALT: dict[str, str] = {}


PERMISSIONS: dict[str, str] = {
    "use_services": "استخدام الخدمات",
    "free_orders": "تنفيذ طلبات مجانية على حساب المالك",
    "ban_users": "حظر وفك حظر المستخدمين",
    "manage_balance": "تعديل أرصدة المستخدمين",
    "view_orders": "مشاهدة الطلبات",
    "manage_services": "إظهار الخدمات أو إخفاؤها",
    "view_feedback": "استلام الشكاوى والتقييمات",
    "receive_order_notifications": "استلام تفاصيل إشعارات الطلبات",
    "manage_settings": "تعديل إعدادات التسعير والتواصل",
}

TELEGRAM_TERMS = (
    "telegram",
    "تيليجرام",
    "تليجرام",
    "تلجرام",
    "تلغرام",
    "تلغريام",
)

VALID_TG_LINK = re.compile(
    r"^(?:https?://)?(?:www\.)?(?:t\.me|telegram\.me|telegram\.dog)/"
    r"(?:\+?[A-Za-z0-9_-]{3,}|joinchat/[A-Za-z0-9_-]+|c/\d+/\d+)"
    r"(?:/\d+)?(?:\?[A-Za-z0-9_=&%-]*)?$",
    re.IGNORECASE,
)
VALID_USERNAME = re.compile(r"^@?[A-Za-z][A-Za-z0-9_]{4,31}$")


class TelegramAPIError(Exception):
    pass


class SMMAPIError(Exception):
    pass


def now_ts() -> int:
    return int(time.time())


def is_private_chat(chat: Any) -> bool:
    return isinstance(chat, dict) and str(chat.get("type") or "") == "private"


def e(value: Any) -> str:
    return html.escape(str(value if value is not None else ""), quote=True)


def d(value: Any, default: Decimal = ZERO) -> Decimal:
    try:
        return Decimal(str(value))
    except (InvalidOperation, TypeError, ValueError):
        return default


def ceil_cent(value: Decimal) -> Decimal:
    return value.quantize(CENT, rounding=ROUND_CEILING)


def fmt_points(value: Any) -> str:
    value = d(value).quantize(CENT)
    return f"{value:.2f}".rstrip("0").rstrip(".")


def fmt_usd(value: Any) -> str:
    return f"{d(value).quantize(CENT):.2f}"


def money_text(value: Any) -> str:
    return fmt_points(value) + " نقطة"


def em(name: str) -> str:
    emoji_id, fallback = PREMIUM_EMOJI.get(name, ("", ""))
    alt = EMOJI_ALT.get(emoji_id, fallback)
    if emoji_id in AVAILABLE_EMOJI_IDS:
        return f'<tg-emoji emoji-id="{e(emoji_id)}">{e(alt)}</tg-emoji>'
    return e(fallback)


def _strip_premium_tags(text: str) -> str:
    return re.sub(r'<tg-emoji\b[^>]*>(.*?)</tg-emoji>', r"\1", text, flags=re.DOTALL)


def _strip_keyboard_icons(markup: Any) -> Any:
    cleaned = copy.deepcopy(markup)
    if isinstance(cleaned, dict):
        for value in cleaned.values():
            if isinstance(value, list):
                for row in value:
                    if isinstance(row, list):
                        for button in row:
                            if isinstance(button, dict):
                                button.pop("icon_custom_emoji_id", None)
            elif isinstance(value, dict):
                _strip_keyboard_icons(value)
    return cleaned


def button(
    text: str,
    callback: str | None = None,
    *,
    url: str | None = None,
    style: str = "primary",
    icon: str | None = None,
) -> dict[str, Any]:
    item: dict[str, Any] = {"text": text}
    if callback is not None:
        item["callback_data"] = callback
    if url is not None:
        item["url"] = url
    if style in ("primary", "success", "danger"):
        item["style"] = style
    if icon and icon in PREMIUM_EMOJI:
        emoji_id = PREMIUM_EMOJI[icon][0]
        if emoji_id in AVAILABLE_EMOJI_IDS:
            item["icon_custom_emoji_id"] = emoji_id
    return item


def keyboard(*rows: list[dict[str, Any]]) -> dict[str, Any]:
    return {"inline_keyboard": [row for row in rows if row]}


def _request_json(url: str, payload: dict[str, Any], timeout: int) -> Any:
    body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    req = urllib.request.Request(
        url,
        data=body,
        headers={"Content-Type": "application/json", "User-Agent": "SMMRocketTelegramBot/1.0"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as response:
            raw = response.read().decode("utf-8", errors="replace")
    except urllib.error.HTTPError as exc:
        raw = exc.read().decode("utf-8", errors="replace")
        try:
            parsed = json.loads(raw)
            message = str(parsed.get("description", "Telegram HTTP error"))
        except (json.JSONDecodeError, AttributeError):
            message = f"Telegram HTTP {exc.code}"
        raise TelegramAPIError(message[:500]) from None
    except (urllib.error.URLError, TimeoutError, OSError) as exc:
        # Do not include a request URL here: it contains the bot token.
        raise TelegramAPIError(f"Telegram network error: {type(exc).__name__}") from None
    try:
        return json.loads(raw)
    except json.JSONDecodeError:
        raise TelegramAPIError("Telegram returned an invalid JSON response") from None


async def _telegram_raw(method: str, payload: dict[str, Any]) -> Any:
    url = f"https://api.telegram.org/bot{BOT_TOKEN}/{method}"
    result = await asyncio.to_thread(_request_json, url, payload, 40 if method == "getUpdates" else 30)
    if not isinstance(result, dict) or not result.get("ok"):
        description = result.get("description", "Telegram request failed") if isinstance(result, dict) else "Telegram request failed"
        raise TelegramAPIError(str(description)[:500])
    return result.get("result")


def _contains_custom_features(payload: dict[str, Any]) -> bool:
    if "<tg-emoji" in str(payload.get("text", "")):
        return True
    return "icon_custom_emoji_id" in json.dumps(payload.get("reply_markup", {}), ensure_ascii=False)


def _is_custom_feature_error(error: TelegramAPIError) -> bool:
    message = str(error).casefold()
    return any(
        marker in message
        for marker in ("tg-emoji", "tg_emoji", "custom emoji", "custom_emoji", "icon_custom_emoji_id")
    )


async def tg(method: str, payload: dict[str, Any]) -> Any:
    try:
        return await _telegram_raw(method, payload)
    except TelegramAPIError as exc:
        if not _contains_custom_features(payload) or not _is_custom_feature_error(exc):
            raise
        fallback = copy.deepcopy(payload)
        if isinstance(fallback.get("text"), str):
            fallback["text"] = _strip_premium_tags(fallback["text"])
        if "reply_markup" in fallback:
            fallback["reply_markup"] = _strip_keyboard_icons(fallback["reply_markup"])
        return await _telegram_raw(method, fallback)


def db_connect() -> sqlite3.Connection:
    con = sqlite3.connect(DB_PATH, timeout=30)
    con.row_factory = sqlite3.Row
    con.execute("PRAGMA busy_timeout=30000")
    con.execute("PRAGMA foreign_keys=ON")
    return con


def init_db() -> None:
    with db_connect() as con:
        con.executescript(
            """
            CREATE TABLE IF NOT EXISTS users (
                user_id INTEGER PRIMARY KEY,
                username TEXT NOT NULL DEFAULT '',
                first_name TEXT NOT NULL DEFAULT '',
                balance TEXT NOT NULL DEFAULT '0',
                banned INTEGER NOT NULL DEFAULT 0,
                created_at INTEGER NOT NULL,
                updated_at INTEGER NOT NULL,
                started_at INTEGER NOT NULL DEFAULT 0,
                registered_at INTEGER NOT NULL DEFAULT 0
            );
            CREATE TABLE IF NOT EXISTS admins (
                user_id INTEGER PRIMARY KEY,
                permissions TEXT NOT NULL DEFAULT '[]',
                added_at INTEGER NOT NULL
            );
            CREATE TABLE IF NOT EXISTS settings (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS states (
                user_id INTEGER PRIMARY KEY,
                step TEXT NOT NULL,
                data TEXT NOT NULL,
                expires_at INTEGER NOT NULL
            );
            CREATE TABLE IF NOT EXISTS services_cache (
                service_id TEXT PRIMARY KEY,
                service_json TEXT NOT NULL,
                updated_at INTEGER NOT NULL
            );
            CREATE TABLE IF NOT EXISTS service_overrides (
                service_id TEXT PRIMARY KEY,
                enabled INTEGER NOT NULL,
                changed_by INTEGER NOT NULL,
                changed_at INTEGER NOT NULL
            );
            CREATE TABLE IF NOT EXISTS orders (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                service_id TEXT NOT NULL,
                service_name TEXT NOT NULL,
                target TEXT NOT NULL,
                quantity INTEGER NOT NULL DEFAULT 1,
                estimated_usd TEXT NOT NULL,
                estimated_points TEXT NOT NULL,
                charged_points TEXT NOT NULL,
                free_order INTEGER NOT NULL DEFAULT 0,
                api_order_id TEXT,
                status TEXT NOT NULL,
                request_json TEXT NOT NULL,
                created_at INTEGER NOT NULL,
                updated_at INTEGER NOT NULL
            );
            CREATE INDEX IF NOT EXISTS orders_user_created ON orders(user_id, created_at DESC);
            CREATE TABLE IF NOT EXISTS ledger (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                amount TEXT NOT NULL,
                reason TEXT NOT NULL,
                reference TEXT UNIQUE,
                created_at INTEGER NOT NULL
            );
            CREATE TABLE IF NOT EXISTS payments (
                payload TEXT PRIMARY KEY,
                user_id INTEGER NOT NULL,
                stars INTEGER NOT NULL,
                points TEXT NOT NULL,
                status TEXT NOT NULL,
                telegram_charge_id TEXT,
                created_at INTEGER NOT NULL,
                paid_at INTEGER
            );
            CREATE TABLE IF NOT EXISTS refills (
                refill_id TEXT PRIMARY KEY,
                order_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                status TEXT NOT NULL DEFAULT 'Pending',
                created_at INTEGER NOT NULL,
                updated_at INTEGER NOT NULL
            );
            CREATE TABLE IF NOT EXISTS ratings (
                user_id INTEGER PRIMARY KEY,
                rating INTEGER NOT NULL,
                created_at INTEGER NOT NULL,
                username TEXT NOT NULL DEFAULT '',
                first_name TEXT NOT NULL DEFAULT ''
            );
            CREATE TABLE IF NOT EXISTS complaints (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                message TEXT NOT NULL,
                created_at INTEGER NOT NULL,
                status TEXT NOT NULL DEFAULT 'new'
            );
            CREATE TABLE IF NOT EXISTS mandatory_channels (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                chat_id TEXT NOT NULL UNIQUE,
                title TEXT NOT NULL,
                invite_url TEXT NOT NULL,
                added_by INTEGER NOT NULL,
                added_at INTEGER NOT NULL
            );
            CREATE TABLE IF NOT EXISTS referrals (
                referred_user_id INTEGER PRIMARY KEY,
                referrer_user_id INTEGER NOT NULL,
                status TEXT NOT NULL DEFAULT 'pending',
                created_at INTEGER NOT NULL,
                registered_at INTEGER NOT NULL DEFAULT 0,
                reward_points TEXT NOT NULL DEFAULT '0'
            );
            CREATE INDEX IF NOT EXISTS referrals_referrer_status
                ON referrals(referrer_user_id,status);
            """
        )
        user_columns = {
            str(row["name"]) for row in con.execute("PRAGMA table_info(users)").fetchall()
        }
        if "started_at" not in user_columns:
            con.execute("ALTER TABLE users ADD COLUMN started_at INTEGER NOT NULL DEFAULT 0")
            con.execute(
                "UPDATE users SET started_at=created_at "
                "WHERE started_at=0 AND TRIM(first_name)<>''"
            )
        if "registered_at" not in user_columns:
            con.execute("ALTER TABLE users ADD COLUMN registered_at INTEGER NOT NULL DEFAULT 0")
            con.execute("UPDATE users SET registered_at=started_at WHERE started_at>0")
        con.execute(
            "INSERT OR IGNORE INTO settings(key,value) VALUES('points_per_usd','25')"
        )
        con.execute(
            "INSERT OR IGNORE INTO settings(key,value) VALUES('stars_per_point','3')"
        )
        con.execute(
            "INSERT OR IGNORE INTO settings(key,value) VALUES('proof_url','')"
        )
        con.execute(
            "INSERT OR IGNORE INTO settings(key,value) VALUES('developer_contact','')"
        )
        registration_migration = con.execute(
            "SELECT value FROM settings WHERE key='registration_backfill_v1'"
        ).fetchone()
        if not registration_migration:
            con.execute(
                """
                UPDATE users SET registered_at=started_at
                WHERE registered_at=0 AND started_at>0
                  AND NOT EXISTS (
                      SELECT 1 FROM referrals
                      WHERE referrals.referred_user_id=users.user_id
                        AND referrals.status='pending'
                  )
                """
            )
            con.execute(
                "INSERT INTO settings(key,value) VALUES('registration_backfill_v1','1')"
            )
        con.execute("UPDATE states SET step='review' WHERE step='review_checking'")
        con.commit()


def get_setting(key: str, default: str = "") -> str:
    with db_connect() as con:
        row = con.execute("SELECT value FROM settings WHERE key=?", (key,)).fetchone()
    return str(row["value"]) if row else default


def set_setting(key: str, value: str) -> None:
    with db_connect() as con:
        con.execute(
            "INSERT INTO settings(key,value) VALUES(?,?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (key, value),
        )
        con.commit()


def load_co_owners() -> None:
    raw_ids = ",".join(
        value.strip()
        for value in (
            get_setting("co_owner_ids"),
            os.getenv("CO_OWNER_TELEGRAM_IDS", ""),
        )
        if value.strip()
    )
    co_owner_ids: set[int] = set()
    for raw_id in raw_ids.split(","):
        raw_id = raw_id.strip()
        if not raw_id:
            continue
        try:
            user_id = int(raw_id)
        except ValueError:
            raise RuntimeError("Invalid co-owner ID stored in bot settings.") from None
        if user_id <= 0:
            raise RuntimeError("Invalid co-owner ID stored in bot settings.")
        if user_id != OWNER_ID:
            co_owner_ids.add(user_id)
    CO_OWNER_IDS.clear()
    CO_OWNER_IDS.update(co_owner_ids)


def is_owner(user_id: int) -> bool:
    return user_id == OWNER_ID or user_id in CO_OWNER_IDS


def points_per_usd() -> Decimal:
    rate = d(get_setting("points_per_usd", "25"), Decimal("25"))
    return rate if rate > ZERO else Decimal("25")


def stars_per_point() -> int:
    try:
        value = int(get_setting("stars_per_point", "3"))
    except ValueError:
        value = 3
    return value if value > 0 else 3


def ensure_user(user: dict[str, Any], *, mark_started: bool = False) -> bool:
    uid = int(user["id"])
    timestamp = now_ts()
    first_name = " ".join(
        part for part in (user.get("first_name", ""), user.get("last_name", "")) if part
    )
    with db_connect() as con:
        con.execute("BEGIN IMMEDIATE")
        existing = con.execute(
            "SELECT started_at FROM users WHERE user_id=?", (uid,)
        ).fetchone()
        is_first_start = bool(
            mark_started and (existing is None or int(existing["started_at"] or 0) == 0)
        )
        if existing is None:
            con.execute(
                """
                INSERT INTO users(user_id,username,first_name,created_at,updated_at,started_at)
                VALUES(?,?,?,?,?,?)
                """,
                (
                    uid,
                    user.get("username", "") or "",
                    first_name,
                    timestamp,
                    timestamp,
                    timestamp if mark_started else 0,
                ),
            )
        else:
            con.execute(
                """
                UPDATE users SET username=?,first_name=?,updated_at=?,
                    started_at=CASE WHEN started_at=0 AND ? THEN ? ELSE started_at END
                WHERE user_id=?
                """,
                (user.get("username", "") or "", first_name, timestamp,
                 1 if mark_started else 0, timestamp, uid),
            )
        con.commit()
    return is_first_start


def user_row(user_id: int) -> sqlite3.Row | None:
    with db_connect() as con:
        return con.execute("SELECT * FROM users WHERE user_id=?", (user_id,)).fetchone()


def user_balance(user_id: int) -> Decimal:
    row = user_row(user_id)
    return d(row["balance"]) if row else ZERO


def is_registered(user_id: int) -> bool:
    row = user_row(user_id)
    return bool(row and int(row["registered_at"] or 0) > 0)


def mandatory_channels() -> list[sqlite3.Row]:
    with db_connect() as con:
        return con.execute(
            "SELECT id,chat_id,title,invite_url FROM mandatory_channels ORDER BY id"
        ).fetchall()


async def has_required_subscriptions(user_id: int, *, force: bool = False) -> bool:
    channels = mandatory_channels()
    if not channels:
        SUBSCRIPTION_CACHE.pop(user_id, None)
        return True
    cached = SUBSCRIPTION_CACHE.get(user_id)
    now = time.monotonic()
    if not force and cached and cached[0] > now:
        return cached[1]

    for channel in channels:
        member = await tg(
            "getChatMember",
            {"chat_id": channel["chat_id"], "user_id": user_id},
        )
        if not isinstance(member, dict):
            raise TelegramAPIError("تعذّر التحقق من الاشتراك في القنوات المطلوبة.")
        status = str(member.get("status") or "")
        subscribed = status in ("creator", "administrator", "member") or (
            status == "restricted" and bool(member.get("is_member"))
        )
        if not subscribed:
            SUBSCRIPTION_CACHE[user_id] = (now + 5, False)
            return False

    SUBSCRIPTION_CACHE[user_id] = (now + 30, True)
    return True


def mark_user_registered(user_id: int) -> tuple[int | None, Decimal]:
    """Register a user once and atomically apply any pending referral reward."""
    timestamp = now_ts()
    reward = referral_reward_points()
    with db_connect() as con:
        con.execute("BEGIN IMMEDIATE")
        user = con.execute(
            "SELECT registered_at FROM users WHERE user_id=?", (user_id,)
        ).fetchone()
        if not user or int(user["registered_at"] or 0) > 0:
            con.commit()
            return None, ZERO

        con.execute(
            "UPDATE users SET registered_at=?,updated_at=? WHERE user_id=?",
            (timestamp, timestamp, user_id),
        )
        referral = con.execute(
            """
            SELECT referrer_user_id,status FROM referrals
            WHERE referred_user_id=?
            """,
            (user_id,),
        ).fetchone()
        if not referral or str(referral["status"]) != "pending":
            con.commit()
            return None, ZERO

        referrer_id = int(referral["referrer_user_id"])
        add_ledger(
            con,
            referrer_id,
            reward,
            f"مكافأة إحالة المستخدم {user_id}",
            f"referral:{user_id}",
        )
        con.execute(
            """
            UPDATE referrals
            SET status='rewarded',registered_at=?,reward_points=?
            WHERE referred_user_id=? AND status='pending'
            """,
            (timestamp, precise_points_text(reward), user_id),
        )
        con.commit()
    return referrer_id, reward


def referral_summary(user_id: int) -> tuple[int, int, Decimal]:
    with db_connect() as con:
        rows = con.execute(
            "SELECT status,reward_points FROM referrals WHERE referrer_user_id=?",
            (user_id,),
        ).fetchall()
    registered = sum(1 for row in rows if row["status"] == "rewarded")
    pending = sum(1 for row in rows if row["status"] == "pending")
    earned = sum(
        (d(row["reward_points"]) for row in rows if row["status"] == "rewarded"),
        ZERO,
    )
    return registered, pending, earned


def required_channel_keyboard() -> dict[str, Any]:
    rows = [
        [button(f"اشترك في {str(channel['title'])[:42]}", url=str(channel["invite_url"]),
                style="primary", icon="telegram")]
        for channel in mandatory_channels()
    ]
    rows.append([button("تحققت من الاشتراك", "check_subscriptions", style="success", icon="check")])
    return keyboard(*rows)


async def show_required_channels(
    chat_id: int,
    *,
    callback: dict[str, Any] | None = None,
    verification_error: bool = False,
) -> None:
    text = (
        f"{em('lock')} <b>الاشتراك في القنوات مطلوب</b>\n\n"
        "• اشترك في كل القنوات الظاهرة، ثم اضغط «تحققت من الاشتراك».\n"
        "• لن يكتمل تسجيلك عبر رابط الدعوة ولن تُصرف مكافأة الإحالة حتى يتم التحقق."
    )
    if verification_error:
        text += (
            "\n\n• تعذّر التحقق الآن. على المالك التأكد من أن البوت مشرف في القنوات، "
            "ثم أعد المحاولة."
        )
    markup = required_channel_keyboard()
    if callback:
        await edit_message(callback, text, markup)
    else:
        await send_message(chat_id, text, markup)


async def notify_referrer_registration(
    user: dict[str, Any],
    referrer_id: int,
    reward: Decimal,
) -> None:
    name = " ".join(
        part for part in (user.get("first_name", ""), user.get("last_name", "")) if part
    ) or "مستخدم جديد"
    username = f" (@{e(user['username'])})" if user.get("username") else ""
    try:
        await send_message(
            referrer_id,
            f"{em('check')} <b>سُجّل مستخدم جديد من رابط دعوتك</b>\n\n"
            f"• المستخدم: <b>{e(name)}</b>{username}\n"
            "• أكمل الاشتراك في القنوات المطلوبة وتم تسجيله.\n"
            f"• مكافأتك: <b>0.5 نجمة</b> "
            f"(<b>{fmt_points(reward)} نقطة</b>) أُضيفت إلى رصيدك.",
        )
    except TelegramAPIError as exc:
        log.info("Referral notification delivery failed (%s)", str(exc)[:160])


async def require_user_access(
    user: dict[str, Any],
    chat_id: int,
    *,
    callback: dict[str, Any] | None = None,
    force_check: bool = False,
) -> bool:
    user_id = int(user["id"])
    if is_owner(user_id):
        if not is_registered(user_id):
            try:
                subscribed = await has_required_subscriptions(
                    user_id, force=force_check
                )
            except TelegramAPIError:
                subscribed = False
            if subscribed:
                referrer_id, reward = mark_user_registered(user_id)
                if referrer_id is not None:
                    await notify_referrer_registration(user, referrer_id, reward)
        return True
    try:
        subscribed = await has_required_subscriptions(user_id, force=force_check)
    except TelegramAPIError as exc:
        log.info("Required-channel check failed: %s", str(exc)[:160])
        await show_required_channels(
            chat_id, callback=callback, verification_error=True
        )
        return False
    if not subscribed:
        await show_required_channels(chat_id, callback=callback)
        return False
    if not is_registered(user_id):
        referrer_id, reward = mark_user_registered(user_id)
        if referrer_id is not None:
            await notify_referrer_registration(user, referrer_id, reward)
    return True


def parse_required_channel_input(raw: str) -> tuple[str, str | None] | None:
    parts = raw.strip().split()
    if not parts or len(parts) > 2:
        return None
    channel_ref = parts[0]
    if channel_ref.startswith("@"):
        if not VALID_USERNAME.fullmatch(channel_ref[1:]):
            return None
    elif not re.fullmatch(r"-100\d{6,}", channel_ref):
        return None

    invite_url = normalize_link(parts[1]) if len(parts) == 2 else None
    if len(parts) == 2 and not invite_url:
        return None
    if channel_ref.startswith("-100") and not invite_url:
        return None
    return channel_ref, invite_url


async def add_required_channel(raw: str, added_by: int) -> tuple[str, str]:
    parsed = parse_required_channel_input(raw)
    if not parsed:
        raise ValueError(
            "صيغة غير صحيحة. أرسل @username للقناة العامة، أو "
            "-100... ورابط الدعوة للقناة الخاصة."
        )
    channel_ref, invite_url = parsed
    chat = await tg("getChat", {"chat_id": channel_ref})
    if not isinstance(chat, dict) or str(chat.get("type") or "") not in ("channel", "supergroup"):
        raise ValueError("المعرّف لا يشير إلى قناة أو مجموعة بث صالحة.")
    actual_chat_id = str(chat.get("id") or "")
    if not actual_chat_id:
        raise ValueError("لم أتمكن من قراءة معرّف القناة.")

    if BOT_ID <= 0:
        raise ValueError("تعذّر تحديد حساب البوت؛ أعد تشغيله ثم حاول مجدداً.")
    bot_member = await tg(
        "getChatMember", {"chat_id": actual_chat_id, "user_id": BOT_ID}
    )
    if not isinstance(bot_member, dict) or str(bot_member.get("status") or "") not in (
        "creator", "administrator"
    ):
        raise ValueError("يجب إضافة البوت مشرفاً في القناة قبل تفعيل الاشتراك الإجباري.")

    username = str(chat.get("username") or "").strip()
    if not invite_url and username:
        invite_url = f"https://t.me/{username}"
    if not invite_url:
        raise ValueError("أرسل رابط دعوة صالحاً للقناة الخاصة.")
    title = str(chat.get("title") or username or actual_chat_id)
    with db_connect() as con:
        exists = con.execute(
            "SELECT 1 FROM mandatory_channels WHERE chat_id=?", (actual_chat_id,)
        ).fetchone()
        count = int(con.execute("SELECT COUNT(*) FROM mandatory_channels").fetchone()[0])
        if not exists and count >= 25:
            raise ValueError("الحد الأقصى هو 25 قناة اشتراك إجباري.")
        con.execute(
            """
            INSERT INTO mandatory_channels(chat_id,title,invite_url,added_by,added_at)
            VALUES(?,?,?,?,?)
            ON CONFLICT(chat_id) DO UPDATE SET
                title=excluded.title,invite_url=excluded.invite_url,
                added_by=excluded.added_by,added_at=excluded.added_at
            """,
            (actual_chat_id, title, invite_url, added_by, now_ts()),
        )
        con.commit()
    SUBSCRIPTION_CACHE.clear()
    return title, actual_chat_id


def remove_required_channel(channel_row_id: int) -> bool:
    with db_connect() as con:
        cursor = con.execute(
            "DELETE FROM mandatory_channels WHERE id=?", (channel_row_id,)
        )
        con.commit()
    if cursor.rowcount:
        SUBSCRIPTION_CACHE.clear()
        return True
    return False


def record_pending_referral(referred_user_id: int, referrer_user_id: int) -> bool:
    if referred_user_id <= 0 or referrer_user_id <= 0 or referred_user_id == referrer_user_id:
        return False
    with db_connect() as con:
        con.execute("BEGIN IMMEDIATE")
        referred = con.execute(
            "SELECT registered_at FROM users WHERE user_id=?", (referred_user_id,)
        ).fetchone()
        if referred and int(referred["registered_at"] or 0) > 0:
            con.commit()
            return False
        referrer = con.execute(
            "SELECT registered_at FROM users WHERE user_id=?", (referrer_user_id,)
        ).fetchone()
        if not is_owner(referrer_user_id) and (
            not referrer or int(referrer["registered_at"] or 0) <= 0
        ):
            con.commit()
            return False
        cursor = con.execute(
            """
            INSERT OR IGNORE INTO referrals(
                referred_user_id,referrer_user_id,status,created_at
            ) VALUES(?,?, 'pending', ?)
            """,
            (referred_user_id, referrer_user_id, now_ts()),
        )
        con.commit()
        return cursor.rowcount == 1


def referral_reward_points() -> Decimal:
    return (Decimal("0.5") / Decimal(stars_per_point())).quantize(
        Decimal("0.00000001"), rounding=ROUND_HALF_UP
    )


def precise_points_text(value: Any) -> str:
    number = d(value)
    return format(number.normalize(), "f") if number else "0"


def is_banned(user_id: int) -> bool:
    if is_owner(user_id):
        return False
    row = user_row(user_id)
    return bool(row and row["banned"])


def admin_permissions(user_id: int) -> set[str]:
    if is_owner(user_id):
        return set(PERMISSIONS)
    with db_connect() as con:
        row = con.execute("SELECT permissions FROM admins WHERE user_id=?", (user_id,)).fetchone()
    if not row:
        return set()
    try:
        return {p for p in json.loads(row["permissions"]) if p in PERMISSIONS}
    except (json.JSONDecodeError, TypeError):
        return set()


def is_admin(user_id: int) -> bool:
    if is_owner(user_id):
        return True
    with db_connect() as con:
        return con.execute("SELECT 1 FROM admins WHERE user_id=?", (user_id,)).fetchone() is not None


def has_perm(user_id: int, permission: str) -> bool:
    return is_owner(user_id) or permission in admin_permissions(user_id)


def save_state(user_id: int, step: str, data: dict[str, Any]) -> None:
    with db_connect() as con:
        con.execute(
            "INSERT INTO states(user_id,step,data,expires_at) VALUES(?,?,?,?) "
            "ON CONFLICT(user_id) DO UPDATE SET step=excluded.step,data=excluded.data,expires_at=excluded.expires_at",
            (user_id, step, json.dumps(data, ensure_ascii=False), now_ts() + STATE_TTL_SECONDS),
        )
        con.commit()


def read_state(user_id: int) -> tuple[str, dict[str, Any]] | None:
    with db_connect() as con:
        row = con.execute("SELECT step,data,expires_at FROM states WHERE user_id=?", (user_id,)).fetchone()
        if not row:
            return None
        if row["expires_at"] < now_ts():
            con.execute("DELETE FROM states WHERE user_id=?", (user_id,))
            con.commit()
            return None
    try:
        return str(row["step"]), json.loads(row["data"])
    except (json.JSONDecodeError, TypeError):
        return None


def claim_review_state(user_id: int) -> dict[str, Any] | None:
    with db_connect() as con:
        con.execute("BEGIN IMMEDIATE")
        row = con.execute(
            "SELECT data,expires_at FROM states WHERE user_id=? AND step='review'",
            (user_id,),
        ).fetchone()
        if not row or int(row["expires_at"]) < now_ts():
            if row:
                con.execute("DELETE FROM states WHERE user_id=?", (user_id,))
            con.commit()
            return None
        try:
            data = json.loads(row["data"])
        except (json.JSONDecodeError, TypeError):
            con.execute("DELETE FROM states WHERE user_id=?", (user_id,))
            con.commit()
            return None
        if not isinstance(data, dict):
            con.execute("DELETE FROM states WHERE user_id=?", (user_id,))
            con.commit()
            return None
        con.execute(
            "UPDATE states SET step='review_checking',expires_at=? WHERE user_id=?",
            (now_ts() + STATE_TTL_SECONDS, user_id),
        )
        con.commit()
        return data


def clear_state(user_id: int) -> None:
    with db_connect() as con:
        con.execute("DELETE FROM states WHERE user_id=?", (user_id,))
        con.commit()


def _smm_request_sync(fields: dict[str, Any]) -> Any:
    request_fields = {"key": SMM_API_KEY, **fields}
    data = urllib.parse.urlencode(request_fields).encode("utf-8")
    req = urllib.request.Request(
        SMM_API_URL,
        data=data,
        headers={"Content-Type": "application/x-www-form-urlencoded", "User-Agent": "SMMRocketTelegramBot/1.0"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=30) as response:
            raw = response.read().decode("utf-8", errors="replace")
    except urllib.error.HTTPError as exc:
        raw = exc.read().decode("utf-8", errors="replace")
        try:
            parsed = json.loads(raw)
            message = str(parsed.get("error", parsed.get("message", "SMM Rocket HTTP error")))
        except (json.JSONDecodeError, AttributeError):
            message = f"SMM Rocket HTTP {exc.code}"
        if exc.code >= 500:
            message = f"SMM Rocket HTTP {exc.code}: {message}"
        raise SMMAPIError(message[:400]) from None
    except (urllib.error.URLError, TimeoutError, OSError) as exc:
        raise SMMAPIError(f"SMM Rocket network error: {type(exc).__name__}") from None
    try:
        parsed = json.loads(raw)
    except json.JSONDecodeError:
        raise SMMAPIError("SMM Rocket returned invalid JSON") from None
    if isinstance(parsed, dict) and parsed.get("error"):
        raise SMMAPIError(str(parsed["error"])[:400])
    return parsed


async def smm(fields: dict[str, Any]) -> Any:
    return await asyncio.to_thread(_smm_request_sync, fields)


def service_is_telegram(
    service: dict[str, Any],
    overrides: dict[str, int] | None = None,
) -> bool:
    service_id = str(service.get("service", ""))
    if overrides is not None and service_id in overrides:
        return bool(overrides[service_id])
    if overrides is None:
        with db_connect() as con:
            row = con.execute(
                "SELECT enabled FROM service_overrides WHERE service_id=?", (service_id,)
            ).fetchone()
        if row is not None:
            return bool(row["enabled"])
    name = str(service.get("name", "") or "").casefold()
    explicit_tg = any(term in name for term in TELEGRAM_TERMS)
    other_platforms = (
        "instagram", "youtube", "tiktok", "facebook", "twitter", "x.com",
        "discord", "linkedin", "twitch", "vk.com", "reddit",
        "انستجرام", "انستغرام", "يوتيوب", "تيك توك", "فيسبوك", "فيس بوك",
    )
    if not explicit_tg and any(platform in name for platform in other_platforms):
        return False
    text = " ".join(
        str(service.get(field, "") or "")
        for field in ("category", "name", "desc", "description")
    ).casefold()
    return any(term in text for term in TELEGRAM_TERMS)


async def load_services(force: bool = False) -> list[dict[str, Any]]:
    if not force:
        with db_connect() as con:
            newest = con.execute("SELECT MAX(updated_at) AS updated_at FROM services_cache").fetchone()
            if newest and newest["updated_at"] and now_ts() - int(newest["updated_at"]) < SERVICE_CACHE_SECONDS:
                rows = con.execute("SELECT service_json FROM services_cache").fetchall()
                try:
                    return [json.loads(row["service_json"]) for row in rows]
                except json.JSONDecodeError:
                    pass
    result = await smm({"action": "services"})
    if not isinstance(result, list):
        raise SMMAPIError("خدمة services لم تُرجع قائمة خدمات صالحة.")
    parsed = [item for item in result if isinstance(item, dict) and item.get("service") is not None]
    with db_connect() as con:
        con.execute("DELETE FROM services_cache")
        con.executemany(
            "INSERT INTO services_cache(service_id,service_json,updated_at) VALUES(?,?,?)",
            [
                (str(item["service"]), json.dumps(item, ensure_ascii=False), now_ts())
                for item in parsed
            ],
        )
        con.commit()
    return parsed


async def telegram_services(force: bool = False) -> list[dict[str, Any]]:
    services = await load_services(force)
    with db_connect() as con:
        rows = con.execute("SELECT service_id,enabled FROM service_overrides").fetchall()
    overrides = {str(row["service_id"]): int(row["enabled"]) for row in rows}
    return [s for s in services if service_is_telegram(s, overrides)]


def cached_service(service_id: str) -> dict[str, Any] | None:
    with db_connect() as con:
        row = con.execute(
            "SELECT service_json FROM services_cache WHERE service_id=?", (str(service_id),)
        ).fetchone()
    if not row:
        return None
    try:
        return json.loads(row["service_json"])
    except json.JSONDecodeError:
        return None


def add_ledger(
    con: sqlite3.Connection,
    user_id: int,
    amount: Decimal,
    reason: str,
    reference: str | None,
) -> bool:
    try:
        con.execute(
            "INSERT INTO ledger(user_id,amount,reason,reference,created_at) VALUES(?,?,?,?,?)",
            (user_id, str(amount), reason, reference, now_ts()),
        )
        current = con.execute("SELECT balance FROM users WHERE user_id=?", (user_id,)).fetchone()
        if not current:
            con.execute(
                "INSERT INTO users(user_id,created_at,updated_at) VALUES(?,?,?)",
                (user_id, now_ts(), now_ts()),
            )
            balance = ZERO
        else:
            balance = d(current["balance"])
        con.execute(
            "UPDATE users SET balance=?,updated_at=? WHERE user_id=?",
            (str(balance + amount), now_ts(), user_id),
        )
        return True
    except sqlite3.IntegrityError:
        return False


def quote_message_intro(text: str) -> str:
    if not text or not text.strip():
        return text
    if re.match(r"^\s*<blockquote(?:\s[^>]*)?>", text, flags=re.IGNORECASE):
        return text

    leading_newlines = len(text) - len(text.lstrip("\n"))
    body = text[leading_newlines:]
    first_line, separator, remainder = body.partition("\n")
    if not first_line.strip() or "<blockquote" in first_line.casefold():
        return text
    return (
        text[:leading_newlines]
        + f"<blockquote>{first_line}</blockquote>"
        + separator
        + remainder
    )


async def send_message(
    chat_id: int,
    text: str,
    reply_markup: dict[str, Any] | None = None,
    *,
    reply_to: int | None = None,
    disable_preview: bool = True,
) -> Any:
    if int(chat_id) <= 0:
        log.info("Skipped sending a message outside a private chat.")
        return None
    text = quote_message_intro(text)
    payload: dict[str, Any] = {
        "chat_id": chat_id,
        "text": text,
        "parse_mode": "HTML",
        "disable_web_page_preview": disable_preview,
    }
    if reply_markup:
        payload["reply_markup"] = reply_markup
    if reply_to is not None:
        payload["reply_to_message_id"] = reply_to
        payload["allow_sending_without_reply"] = True
    return await tg("sendMessage", payload)


async def edit_message(
    callback: dict[str, Any],
    text: str,
    reply_markup: dict[str, Any] | None = None,
) -> None:
    text = quote_message_intro(text)
    message = callback.get("message") or {}
    chat = message.get("chat") or {}
    if (
        not is_private_chat(chat)
        or int(chat.get("id") or 0) <= 0
        or not message.get("message_id")
    ):
        log.info("Skipped editing a message outside a private chat.")
        return
    payload: dict[str, Any] = {
        "chat_id": chat["id"],
        "message_id": message["message_id"],
        "text": text,
        "parse_mode": "HTML",
        "disable_web_page_preview": True,
    }
    if reply_markup:
        payload["reply_markup"] = reply_markup
    try:
        await tg("editMessageText", payload)
    except TelegramAPIError as exc:
        if "message is not modified" not in str(exc).lower():
            await send_message(int(chat["id"]), text, reply_markup)


async def answer_callback(callback_id: str, text: str = "", alert: bool = False) -> None:
    try:
        await tg(
            "answerCallbackQuery",
            {"callback_query_id": callback_id, "text": text[:180], "show_alert": alert},
        )
    except TelegramAPIError as exc:
        log.info("Could not answer callback: %s", str(exc)[:160])


async def prime_custom_emojis() -> None:
    global AVAILABLE_EMOJI_IDS, EMOJI_ALT
    ids = list(dict.fromkeys(value[0] for value in PREMIUM_EMOJI.values()))
    try:
        stickers = await tg("getCustomEmojiStickers", {"custom_emoji_ids": ids})
        if not isinstance(stickers, list):
            return
        for sticker in stickers:
            if not isinstance(sticker, dict):
                continue
            emoji_id = str(sticker.get("custom_emoji_id", ""))
            if emoji_id:
                AVAILABLE_EMOJI_IDS.add(emoji_id)
                if sticker.get("emoji"):
                    EMOJI_ALT[emoji_id] = str(sticker["emoji"])
        log.info("Validated %d premium emoji IDs", len(AVAILABLE_EMOJI_IDS))
    except TelegramAPIError as exc:
        # Unicode fallback remains usable when the bot cannot use custom emoji.
        log.info("Premium emoji unavailable; using Unicode fallback (%s)", str(exc)[:160])


def owner_or_permission(user_id: int, permission: str) -> bool:
    return is_owner(user_id) or has_perm(user_id, permission)


def user_label(user_id: int) -> str:
    row = user_row(user_id)
    if not row:
        return f"<code>{user_id}</code>"
    name = e(row["first_name"] or "مستخدم")
    username = f" (@{e(row['username'])})" if row["username"] else ""
    return f"{name}{username} — <code>{user_id}</code>"


async def notification_recipients(permission: str) -> list[int]:
    recipients = [OWNER_ID, *sorted(CO_OWNER_IDS)]
    with db_connect() as con:
        rows = con.execute("SELECT user_id FROM admins").fetchall()
    for row in rows:
        uid = int(row["user_id"])
        if uid not in recipients and has_perm(uid, permission):
            recipients.append(uid)
    return recipients


async def notify(
    text: str,
    permission: str = "receive_order_notifications",
) -> None:
    recipients = await notification_recipients(permission)
    for recipient in recipients:
        try:
            await send_message(recipient, text)
        except TelegramAPIError as exc:
            # In particular, the owner/admin must open the bot once before DMs work.
            log.info("Notification delivery failed (%s)", str(exc)[:160])


async def notify_owners(text: str) -> None:
    recipients = sorted({owner_id for owner_id in [OWNER_ID, *CO_OWNER_IDS] if owner_id > 0})
    for owner_id in recipients:
        try:
            await send_message(owner_id, text)
        except TelegramAPIError as exc:
            log.info("Owner notification delivery failed (%s)", str(exc)[:160])


def cairo_datetime(timestamp: int) -> str:
    return datetime.fromtimestamp(timestamp, ZoneInfo("Africa/Cairo")).strftime("%Y-%m-%d %H:%M:%S")


async def notify_new_user(user: dict[str, Any]) -> None:
    user_id = int(user["id"])
    row = user_row(user_id)
    if not row:
        return
    with db_connect() as con:
        total = int(
            con.execute("SELECT COUNT(*) FROM users WHERE started_at > 0").fetchone()[0]
        )
    name = " ".join(
        part for part in (user.get("first_name", ""), user.get("last_name", "")) if part
    ) or str(row["first_name"] or "غير معروف")
    username = str(user.get("username") or row["username"] or "")
    username_label = f"@{e(username)}" if username else "غير متاح"
    entered_at = int(row["started_at"] or now_ts())
    text = (
        f"{em('bell')} <b>دخل مستخدم جديد إلى البوت</b>\n\n"
        f"• الاسم: <b>{e(name)}</b>\n"
        f"• اليوزر: {username_label}\n"
        f"• الآيدي: <code>{user_id}</code>\n"
        f"• وقت الدخول: <b>{e(cairo_datetime(entered_at))}</b> بتوقيت القاهرة\n"
        f"• العدد الكلي للمستخدمين: <b>{total}</b>"
    )
    await notify_owners(text)


def home_text(user_id: int) -> str:
    row = user_row(user_id)
    name = e((row["first_name"] if row else "") or "صديقنا")
    return (
        f"<blockquote>أهلًا وسهلًا بك يا {name} {em('telegram')}</blockquote>\n\n"
        f"• اختر القسم المناسب، وستظهر خدمات Telegram فقط {em('check')}\n"
        f"• رصيدك الحالي: <b>{money_text(user_balance(user_id))}</b> {em('wallet')}\n"
        f"• راجع الخدمة والرابط والكمية والتكلفة قبل التأكيد {em('info')}"
    )


def home_keyboard(user_id: int) -> dict[str, Any]:
    rows: list[list[dict[str, Any]]] = [
        [button("قسم خدمات الرشق", "services", style="success", icon="telegram")],
        [
            button("إضافة رصيد", "wallet", style="success", icon="plus"),
            button("طلباتي", "myorders", style="primary", icon="calendar"),
        ],
        [
            button("قناة الإثباتات", "proof", style="primary", icon="check"),
            button("قيّم البوت", "rate", style="primary", icon="star"),
        ],
        [button("دعوة صديق ومكافآتي", "referrals", style="success", icon="plus")],
        [
            button("طلب نسخه - المطور @dev_mido", "developer", style="primary", icon="settings"),
            button("إرسال شكوى", "complaint", style="danger", icon="warning"),
        ],
    ]
    if is_admin(user_id):
        rows.append([button("لوحة الإدارة", "admin", style="primary", icon="shield")])
    rows.append([button("تحديث القائمة", "home", style="primary", icon="loading")])
    return keyboard(*rows)


async def show_home(chat_id: int, user_id: int, edit: dict[str, Any] | None = None) -> None:
    text = home_text(user_id)
    markup = home_keyboard(user_id)
    if edit:
        await edit_message(edit, text, markup)
    else:
        await send_message(chat_id, text, markup)


async def show_referrals(
    chat_id: int,
    user_id: int,
    callback: dict[str, Any] | None = None,
) -> None:
    registered, pending, earned = referral_summary(user_id)
    if not BOT_USERNAME:
        text = f"{em('warning')} رابط الدعوة غير متاح الآن؛ أعد المحاولة بعد قليل."
        markup = keyboard([button("الرئيسية", "home", icon="telegram")])
    else:
        link = f"https://t.me/{BOT_USERNAME}?start=ref_{user_id}"
        share_url = (
            "https://t.me/share/url?"
            + urllib.parse.urlencode(
                {"url": link, "text": "انضم إلى البوت عبر رابط دعوتي"}
            )
        )
        text = (
            f"{em('plus')} <b>دعوة الأصدقاء</b>\n\n"
            "• أرسل رابطك إلى صديقك.\n"
            "• تُسجّل الإحالة بعد أن يشترك صديقك في كل القنوات المطلوبة ويضغط التحقق.\n"
            "• مكافأتك <b>0.5 نجمة</b> عن كل تسجيل مكتمل، وتُضاف إلى رصيد النقاط.\n\n"
            f"• رابط دعوتك:\n<code>{e(link)}</code>\n\n"
            f"• تسجيلات مكتملة: <b>{registered}</b>\n"
            f"• بانتظار إكمال الاشتراك: <b>{pending}</b>\n"
            f"• إجمالي المكافآت: <b>{fmt_points(earned)} نقطة</b>"
        )
        markup = keyboard(
            [button("مشاركة رابط الدعوة", url=share_url, style="success", icon="telegram")],
            [button("الرئيسية", "home", icon="telegram")],
        )
    if callback:
        await edit_message(callback, text, markup)
    else:
        await send_message(chat_id, text, markup)


def cancel_keyboard() -> dict[str, Any]:
    return keyboard([button("إلغاء", "cancel_state", style="danger", icon="cross")])


async def show_services(chat_id: int, edit: dict[str, Any] | None = None) -> None:
    try:
        services = await telegram_services()
    except SMMAPIError as exc:
        message = (
            f"{em('warning')} تعذّر جلب الخدمات الآن.\n\n"
            f"• {e(str(exc))}\n"
            "• أعد المحاولة بعد قليل، أو أبلغ المالك إذا استمر العطل."
        )
        if edit:
            await edit_message(edit, message, keyboard([button("الرئيسية", "home", icon="telegram")]))
        else:
            await send_message(chat_id, message, keyboard([button("الرئيسية", "home", icon="telegram")]))
        return

    categories = sorted({str(s.get("category") or "خدمات Telegram") for s in services}, key=str.casefold)
    if not services:
        text = (
            f"{em('info')} لم أجد خدمات Telegram في قائمة API الحالية.\n\n"
            "• يجري تصفية الخدمات حسب اسمها ووصفها وتصنيفها.\n"
            "• إذا كانت خدمة Telegram غير ظاهرة، يستطيع المالك مراجعة رقمها وإظهارها من لوحة الإدارة."
        )
        markup = keyboard([button("تحديث الخدمات", "services_refresh", style="success", icon="loading")],
                          [button("الرئيسية", "home", icon="telegram")])
        if edit:
            await edit_message(edit, text, markup)
        else:
            await send_message(chat_id, text, markup)
        return

    rows: list[list[dict[str, Any]]] = []
    for idx, category in enumerate(categories):
        count = sum(1 for s in services if str(s.get("category") or "خدمات Telegram") == category)
        rows.append([
            button(f"{category[:45]} · {count}", f"cat:{idx}", style="primary", icon="telegram")
        ])
    rows.append([button("الرئيسية", "home", icon="telegram")])
    text = (
        f"{em('telegram')} <b>خدمات Telegram المتاحة</b>\n\n"
        f"• عدد الخدمات المطابقة: <b>{len(services)}</b>\n"
        "• اختر التصنيف لعرض الخدمات والأسعار والحدود."
    )
    markup = keyboard(*rows)
    if edit:
        await edit_message(edit, text, markup)
    else:
        await send_message(chat_id, text, markup)


async def show_category(chat_id: int, callback: dict[str, Any], category_index: int) -> None:
    services = await telegram_services()
    categories = sorted({str(s.get("category") or "خدمات Telegram") for s in services}, key=str.casefold)
    if category_index < 0 or category_index >= len(categories):
        await edit_message(callback, "تغيّرت قائمة التصنيفات. حدّثها ثم اختر من جديد.",
                           keyboard([button("تحديث الخدمات", "services_refresh", style="success", icon="loading")]))
        return
    category = categories[category_index]
    selected = [s for s in services if str(s.get("category") or "خدمات Telegram") == category]
    page_size = 8
    pages = max(1, (len(selected) + page_size - 1) // page_size)
    rows: list[list[dict[str, Any]]] = []
    start = 0
    for service in selected[start:start + page_size]:
        name = str(service.get("name") or "خدمة")[:45]
        sid = str(service["service"])
        rows.append([button(f"#{sid} · {name}", f"svc:{sid}", style="primary", icon="telegram")])
    if pages > 1:
        rows.append([button("المزيد", f"catpage:{category_index}:1", style="primary", icon="plus")])
    rows.append([button("رجوع للتصنيفات", "services", icon="telegram")])
    text = (
        f"{em('telegram')} <b>{e(category)}</b>\n\n"
        f"• عدد الخدمات في هذا التصنيف: <b>{len(selected)}</b>\n"
        "• اختر خدمة لقراءة وصفها وحدودها وتكلفتها."
    )
    await edit_message(callback, text, keyboard(*rows))


async def show_category_page(chat_id: int, callback: dict[str, Any], cat_index: int, page: int) -> None:
    services = await telegram_services()
    categories = sorted({str(s.get("category") or "خدمات Telegram") for s in services}, key=str.casefold)
    if cat_index < 0 or cat_index >= len(categories):
        await show_services(chat_id, callback)
        return
    category = categories[cat_index]
    selected = [s for s in services if str(s.get("category") or "خدمات Telegram") == category]
    page_size = 8
    pages = max(1, (len(selected) + page_size - 1) // page_size)
    page = max(0, min(page, pages - 1))
    subset = selected[page * page_size:(page + 1) * page_size]
    rows = [
        [button(f"#{s['service']} · {str(s.get('name') or 'خدمة')[:45]}",
                f"svc:{s['service']}", style="primary", icon="telegram")]
        for s in subset
    ]
    nav: list[dict[str, Any]] = []
    if page > 0:
        nav.append(button("السابق", f"catpage:{cat_index}:{page-1}", icon="telegram"))
    if page + 1 < pages:
        nav.append(button("التالي", f"catpage:{cat_index}:{page+1}", icon="plus"))
    if nav:
        rows.append(nav)
    rows.append([button("رجوع للتصنيفات", "services", icon="telegram")])
    text = f"{em('telegram')} <b>{e(category)}</b>\n• صفحة {page+1} من {pages} — اختر الخدمة."
    await edit_message(callback, text, keyboard(*rows))


def service_type(service: dict[str, Any]) -> str:
    return str(service.get("type") or "Default").strip().casefold()


def service_rate(service: dict[str, Any]) -> Decimal:
    rate = d(service.get("rate"))
    return rate if rate >= ZERO else ZERO


def service_min_max(service: dict[str, Any]) -> tuple[int, int]:
    try:
        minimum = int(str(service.get("min", "1")).replace(",", ""))
    except ValueError:
        minimum = 1
    try:
        maximum = int(str(service.get("max", "999999999")).replace(",", ""))
    except ValueError:
        maximum = 999999999
    return max(1, minimum), max(max(1, minimum), maximum)


def order_target(draft: dict[str, Any]) -> str:
    return str(draft.get("username") or draft.get("link") or "")


def estimate_usd(service: dict[str, Any], draft: dict[str, Any]) -> Decimal:
    rate = service_rate(service)
    typ = service_type(service)
    if "package" in typ:
        return rate.quantize(Decimal("0.000001"), rounding=ROUND_CEILING)
    quantity = max(1, int(draft.get("quantity", 1)))
    if "subscription" in typ:
        quantity = max(1, int(draft.get("max", quantity)))
        quantity *= max(1, int(draft.get("posts", 1)))
    if int(draft.get("runs", 1)) > 1:
        quantity *= int(draft["runs"])
    return (rate * Decimal(quantity) / Decimal(1000)).quantize(
        Decimal("0.000001"), rounding=ROUND_CEILING
    )


def estimate_points(service: dict[str, Any], draft: dict[str, Any]) -> Decimal:
    return ceil_cent(estimate_usd(service, draft) * points_per_usd())


def normalize_link(raw: str) -> str | None:
    value = raw.strip()
    if not value:
        return None
    if not re.match(r"^https?://", value, re.IGNORECASE):
        value = "https://" + value
    if not VALID_TG_LINK.fullmatch(value):
        return None
    return value


def build_review_text(service: dict[str, Any], draft: dict[str, Any], free: bool) -> str:
    cost_usd = estimate_usd(service, draft)
    cost_points = estimate_points(service, draft)
    typ = str(service.get("type") or "Default")
    target = e(order_target(draft))
    quantity = int(draft.get("quantity", 1))
    quantity_line = (
        f"• الكمية: <b>{quantity}</b>\n"
        if "package" not in service_type(service)
        else "• نوع الطلب: <b>باقة ثابتة</b>\n"
    )
    if "subscription" in service_type(service):
        quantity_line = (
            f"• الحد الأدنى: <b>{int(draft.get('min', 0))}</b>\n"
            f"• الحد الأعلى: <b>{int(draft.get('max', 0))}</b>\n"
            f"• عدد المنشورات: <b>{int(draft.get('posts', 1))}</b>\n"
        )
    if "comments" in service_type(service):
        quantity_line = f"• عدد التعليقات: <b>{quantity}</b>\n"
    if "poll" in service_type(service):
        quantity_line += f"• رقم خيار التصويت: <b>{int(draft.get('answer_number', 1))}</b>\n"
    if int(draft.get("runs", 1)) > 1:
        quantity_line += f"• عدد الدفعات: <b>{int(draft['runs'])}</b> — كل {int(draft.get('interval', 0))} دقيقة\n"
    desc = str(service.get("desc") or service.get("description") or "لا يوجد وصف إضافي.")
    text = (
        f"{em('info')} <b>راجع تفاصيل طلبك قبل التأكيد</b>\n\n"
        f"• الخدمة: <b>{e(service.get('name') or 'Telegram')}</b> "
        f"(<code>{e(service.get('service'))}</code>)\n"
        f"• النوع: <b>{e(typ)}</b>\n"
        f"• الهدف: <code>{target}</code>\n"
        f"{quantity_line}"
        f"• التكلفة التقديرية: <b>{fmt_points(cost_points)} نقطة</b> "
        f"(على سعر API الحالي: ${fmt_usd(cost_usd)})\n"
        f"• السعر محسوب على أساس <b>{fmt_points(points_per_usd())} نقطة لكل 1 USD</b>.\n"
    )
    if free:
        text += "• الطلب مجاني للمستخدم؛ تكلفة API ستُخصم من رصيد حساب الموقع.\n"
    else:
        text += f"• رصيدك الحالي: <b>{money_text(user_balance(int(draft.get('user_id', 0))))}</b>\n"
    # Keep panel-provided descriptions separate from the request summary and escape them.
    return text + f"\n• وصف الخدمة: {e(desc[:500])}"


async def show_service_detail(chat_id: int, callback: dict[str, Any], service_id: str) -> None:
    service = cached_service(service_id)
    if not service or not service_is_telegram(service):
        await edit_message(
            callback,
            "• هذه الخدمة لم تعد متاحة ضمن خدمات Telegram.",
            keyboard([button("تحديث الخدمات", "services_refresh", style="success", icon="loading")]),
        )
        return
    minimum, maximum = service_min_max(service)
    desc = str(service.get("desc") or service.get("description") or "لا يوجد وصف.")
    text = (
        f"{em('telegram')} <b>{e(service.get('name') or 'خدمة Telegram')}</b>\n\n"
        f"• رقم الخدمة: <code>{e(service_id)}</code>\n"
        f"• التصنيف: <b>{e(service.get('category') or 'Telegram')}</b>\n"
        f"• النوع: <b>{e(service.get('type') or 'Default')}</b>\n"
        f"• السعر: <b>${fmt_usd(service.get('rate', 0))}</b> لكل 1000 وحدة "
        f"(الباقات الثابتة بسعر الباقة)\n"
        f"• الحد الأدنى: <b>{minimum}</b> — الحد الأعلى: <b>{maximum}</b>\n"
        f"• تعويض: <b>{'متاح' if service.get('refill') else 'غير متاح'}</b> · "
        f"إلغاء: <b>{'متاح' if service.get('cancel') else 'غير متاح'}</b>\n\n"
        f"• وصف الخدمة:\n{e(desc[:700])}\n\n"
        "• التكلفة النهائية قد تختلف قليلاً حسب قيمة charge التي يعيدها الموقع بعد قبول الطلب."
    )
    markup = keyboard(
        [button("بدء الطلب", f"begin:{service_id}", style="success", icon="plus")],
        [button("رجوع", "services", icon="telegram")],
    )
    await edit_message(callback, text, markup)


async def prompt_order(chat_id: int, user_id: int, service: dict[str, Any]) -> None:
    typ = service_type(service)
    minimum, maximum = service_min_max(service)
    draft = {"user_id": user_id, "service_id": str(service["service"]), "service": service, "runs": 1}
    if "subscription" in typ:
        step = "sub_username"
        prompt = "• أرسل اسم المستخدم العام لقناة Telegram بهذا الشكل: <code>@channel</code>."
    elif "comments" in typ:
        step = "target"
        draft["next_after_target"] = "comments"
        prompt = "• أرسل رابط منشور أو قناة Telegram المستهدفة."
    else:
        step = "target"
        draft["next_after_target"] = "quantity"
        prompt = "• أرسل رابط قناة أو منشور Telegram المستهدف."
    draft["min"] = minimum
    draft["max_limit"] = maximum
    save_state(user_id, step, draft)
    await send_message(chat_id, f"{em('telegram')} <b>بدء طلب {e(service.get('name') or 'الخدمة')}</b>\n\n"
                       f"{prompt}\n• أرسل /cancel لإلغاء الخطوات.", cancel_keyboard())


def parse_positive_int(raw: str, maximum: int = 2_000_000_000) -> int | None:
    try:
        value = int(raw.strip().replace(",", ""))
    except ValueError:
        return None
    if value < 1 or value > maximum:
        return None
    return value


def parse_panel_user_id(raw: str) -> int | None:
    value = raw.strip()
    if not value.isdecimal():
        return None
    try:
        user_id = int(value)
    except ValueError:
        return None
    return user_id if 0 < user_id <= 9_223_372_036_854_775_807 else None


async def continue_order_input(message: dict[str, Any], state: tuple[str, dict[str, Any]]) -> None:
    user = message["from"]
    user_id = int(user["id"])
    chat_id = int(message["chat"]["id"])
    text = str(message.get("text") or "").strip()
    step, draft = state
    service = draft.get("service") or cached_service(str(draft.get("service_id", "")))
    if not service:
        clear_state(user_id)
        await send_message(chat_id, "• انتهت صلاحية بيانات الخدمة؛ افتح الخدمة وابدأ من جديد.")
        return
    typ = service_type(service)

    if step in ("target", "sub_username"):
        if "subscription" in typ:
            username = text.lstrip("@")
            if not VALID_USERNAME.fullmatch(username):
                await send_message(chat_id, "• أرسل اسم مستخدم عام صالحاً، مثل <code>@channel_name</code>.")
                return
            draft["username"] = "@" + username
            save_state(user_id, "sub_min", draft)
            await send_message(chat_id, f"• أرسل الحد الأدنى للاشتراك ({draft['min']}–{draft['max_limit']}).",
                               cancel_keyboard())
            return
        link = normalize_link(text)
        if not link:
            await send_message(chat_id, "• أرسل رابط Telegram صالحاً يبدأ بـ <code>t.me/</code> أو <code>telegram.me/</code>.")
            return
        draft["link"] = link
        if "package" in typ:
            await present_order_review(chat_id, user_id, draft)
            return
        next_step = str(draft.pop("next_after_target", "quantity"))
        save_state(user_id, next_step, draft)
        if next_step == "comments":
            await send_message(chat_id,
                               f"• أرسل التعليقات، كل تعليق في سطر مستقل.\n"
                               f"• المطلوب بين {draft['min']} و{draft['max_limit']} تعليقاً.",
                               cancel_keyboard())
        else:
            await send_message(chat_id,
                               f"• أرسل الكمية المطلوبة بين {draft['min']} و{draft['max_limit']}.",
                               cancel_keyboard())
        return

    if step == "quantity":
        quantity = parse_positive_int(text, int(draft.get("max_limit", 2_000_000_000)))
        if quantity is None or quantity < int(draft.get("min", 1)):
            await send_message(chat_id,
                               f"• أدخل كمية صحيحة بين {draft['min']} و{draft['max_limit']}.")
            return
        draft["quantity"] = quantity
        if "poll" in typ:
            save_state(user_id, "poll_answer", draft)
            await send_message(chat_id, "• أرسل رقم اختيار التصويت (رقم موجب).", cancel_keyboard())
            return
        if service.get("dripfeed"):
            save_state(user_id, "drip_choice", draft)
            await send_message(
                chat_id,
                "• هل تريد تنفيذ الطلب مباشرة أم تقسيمه إلى دفعات؟",
                keyboard(
                    [button("تنفيذ مباشر", "drip:no", style="success", icon="check"),
                     button("تقسيم إلى دفعات", "drip:yes", style="primary", icon="calendar")],
                    [button("إلغاء", "cancel_state", style="danger", icon="cross")],
                ),
            )
            return
        await present_order_review(chat_id, user_id, draft)
        return

    if step == "comments":
        comments = [line.strip() for line in text.splitlines() if line.strip()]
        if not int(draft.get("min", 1)) <= len(comments) <= int(draft.get("max_limit", 999999)):
            await send_message(chat_id,
                               f"• عدد التعليقات هو {len(comments)}؛ أرسل بين {draft['min']} و{draft['max_limit']} تعليقاً.")
            return
        if any(len(comment) > 500 for comment in comments):
            await send_message(chat_id, "• لا يزيد أي تعليق عن 500 حرف. أرسل القائمة من جديد.")
            return
        draft["comments"] = comments
        draft["quantity"] = len(comments)
        await present_order_review(chat_id, user_id, draft)
        return

    if step == "poll_answer":
        answer = parse_positive_int(text, 1000)
        if answer is None:
            await send_message(chat_id, "• أرسل رقم اختيار صحيحاً.")
            return
        draft["answer_number"] = answer
        await present_order_review(chat_id, user_id, draft)
        return

    if step in ("sub_min", "sub_max", "sub_posts", "sub_old_posts"):
        if step in ("sub_posts", "sub_old_posts") and text in ("-", "تخطي", "skip"):
            value = 1 if step == "sub_posts" else 0
        else:
            value = parse_positive_int(text, int(draft.get("max_limit", 2_000_000_000)))
            if value is None:
                await send_message(chat_id, "• أرسل رقماً صحيحاً موجباً، أو أرسل <code>-</code> لتخطي الحقل الاختياري.")
                return
        if step == "sub_min":
            if value < int(draft["min"]) or value > int(draft["max_limit"]):
                await send_message(chat_id, f"• الحد الأدنى يجب أن يكون بين {draft['min']} و{draft['max_limit']}.")
                return
            draft["min"] = value
            save_state(user_id, "sub_max", draft)
            await send_message(chat_id, f"• أرسل الحد الأعلى للاشتراك ({value}–{draft['max_limit']}).",
                               cancel_keyboard())
            return
        if step == "sub_max":
            if value < int(draft["min"]) or value > int(draft["max_limit"]):
                await send_message(chat_id, f"• الحد الأعلى يجب أن يكون من {draft['min']} إلى {draft['max_limit']}.")
                return
            draft["max"] = value
            save_state(user_id, "sub_posts", draft)
            await send_message(chat_id, "• أرسل عدد المنشورات الجديدة، أو <code>-</code> لاستخدام منشور واحد.",
                               cancel_keyboard())
            return
        if step == "sub_posts":
            if text in ("-", "تخطي", "skip"):
                draft.pop("posts", None)
            else:
                draft["posts"] = value
            save_state(user_id, "sub_old_posts", draft)
            await send_message(chat_id, "• أرسل عدد المنشورات السابقة، أو <code>-</code> لتخطيها.",
                               cancel_keyboard())
            return
        if value:
            draft["old_posts"] = value
        save_state(user_id, "sub_delay", draft)
        rows = [[button(f"{minutes} دقيقة", f"subdelay:{minutes}", style="primary", icon="calendar")
                 for minutes in (0, 5, 10)]]
        rows.append([button(f"{minutes} دقيقة", f"subdelay:{minutes}", style="primary", icon="calendar")
                     for minutes in (15, 30, 60, 90)])
        rows.append([button("إلغاء", "cancel_state", style="danger", icon="cross")])
        await send_message(chat_id, "• اختر فترة التأخير بين الإضافات.", keyboard(*rows))
        return

    if step == "sub_expiry":
        if text not in ("-", "تخطي", "skip"):
            if not re.fullmatch(r"\d{1,2}/\d{1,2}/\d{4}", text):
                await send_message(chat_id, "• أدخل التاريخ بصيغة <code>يوم/شهر/سنة</code> أو أرسل <code>-</code>.")
                return
            try:
                time.strptime(text, "%d/%m/%Y")
            except ValueError:
                await send_message(chat_id, "• التاريخ غير صالح. استخدم يوماً وشهراً صحيحين، أو أرسل <code>-</code>.")
                return
            draft["expiry"] = text
        else:
            draft.pop("expiry", None)
        await present_order_review(chat_id, user_id, draft)
        return

    if step == "drip_runs":
        runs = parse_positive_int(text, 100000)
        if runs is None:
            await send_message(chat_id, "• أرسل عدداً صحيحاً للدفعات.")
            return
        draft["runs"] = runs
        save_state(user_id, "drip_interval", draft)
        rows = [[button(f"{minutes} د", f"dripinterval:{minutes}", style="primary", icon="calendar")
                 for minutes in (5, 10, 15, 30)]]
        rows.append([button(f"{minutes} دقيقة", f"dripinterval:{minutes}", style="primary", icon="calendar")
                     for minutes in (60, 90)])
        await send_message(chat_id, "• اختر الفاصل الزمني بين الدفعات.", keyboard(*rows))
        return

    await send_message(chat_id, "• هذه الخطوة غير صالحة. أرسل /cancel ثم أعد المحاولة.")


async def present_order_review(
    chat_id: int,
    user_id: int,
    draft: dict[str, Any],
    edit_callback: dict[str, Any] | None = None,
    notice: str = "",
) -> None:
    service = draft.get("service") or cached_service(str(draft.get("service_id", "")))
    if not service:
        clear_state(user_id)
        await send_message(chat_id, "• لم أتمكن من استعادة الخدمة؛ ابدأ الطلب من جديد.")
        return
    draft["service"] = service
    draft["user_id"] = user_id
    draft["reviewed_points"] = str(estimate_points(service, draft))
    draft["reviewed_points_per_usd"] = str(points_per_usd())
    save_state(user_id, "review", draft)
    free_allowed = is_owner(user_id) or (is_admin(user_id) and has_perm(user_id, "free_orders"))
    if is_admin(user_id) and not has_perm(user_id, "use_services"):
        clear_state(user_id)
        await send_message(chat_id, "• لا تملك صلاحية تنفيذ الطلبات. اطلب من المالك تفعيل صلاحية «استخدام الخدمات».")
        return
    if free_allowed:
        markup = keyboard(
            [button("تأكيد مدفوع", "order:paid", style="success", icon="check"),
             button("تنفيذ مجاني على حساب المالك", "order:free", style="primary", icon="free")],
            [button("إلغاء", "cancel_state", style="danger", icon="cross")],
        )
        text = (
            build_review_text(service, draft, False)
            + "\n• يمكنك اختيار التنفيذ المجاني على حساب المالك إذا رغبت."
        )
    else:
        markup = keyboard(
            [button("تأكيد الطلب", "order:paid", style="success", icon="check")],
            [button("إلغاء", "cancel_state", style="danger", icon="cross")],
        )
        text = build_review_text(service, draft, False)
    if notice:
        text = f"{em('warning')} {e(notice)}\n\n{text}"
    if edit_callback:
        await edit_message(edit_callback, text, markup)
    else:
        await send_message(chat_id, text, markup)


def api_order_fields(service: dict[str, Any], draft: dict[str, Any]) -> dict[str, Any]:
    fields: dict[str, Any] = {
        "action": "add",
        "service": str(service["service"]),
    }
    typ = service_type(service)
    if "subscription" in typ:
        fields["username"] = str(draft["username"]).lstrip("@")
        fields["min"] = int(draft["min"])
        fields["max"] = int(draft["max"])
        fields["delay"] = int(draft.get("delay", 0))
        if "posts" in draft:
            fields["posts"] = int(draft.get("posts", 1))
        if int(draft.get("old_posts", 0)) > 0:
            fields["old_posts"] = int(draft["old_posts"])
        if draft.get("expiry"):
            fields["expiry"] = str(draft["expiry"])
    else:
        fields["link"] = str(draft["link"])
        if "package" in typ:
            return fields
        if "comments" in typ:
            fields["comments"] = "\n".join(str(line) for line in draft["comments"])
        else:
            fields["quantity"] = int(draft["quantity"])
        if "poll" in typ:
            fields["answer_number"] = int(draft["answer_number"])
        if int(draft.get("runs", 1)) > 1:
            fields["runs"] = int(draft["runs"])
            fields["interval"] = int(draft["interval"])
    return fields


def create_order_and_reserve(
    user_id: int,
    service: dict[str, Any],
    draft: dict[str, Any],
    free: bool,
) -> tuple[int | None, Decimal]:
    estimated_usd = estimate_usd(service, draft)
    estimated_points = estimate_points(service, draft)
    charged = ZERO if free else estimated_points
    target = order_target(draft)
    quantity = int(draft.get("quantity", draft.get("max", 1)))
    with db_connect() as con:
        con.execute("BEGIN IMMEDIATE")
        row = con.execute("SELECT balance,banned FROM users WHERE user_id=?", (user_id,)).fetchone()
        if not row:
            con.execute(
                "INSERT INTO users(user_id,created_at,updated_at) VALUES(?,?,?)",
                (user_id, now_ts(), now_ts()),
            )
            balance = ZERO
        else:
            if row["banned"] and not is_owner(user_id):
                con.rollback()
                return None, ZERO
            balance = d(row["balance"])
        if not free and balance < charged:
            con.rollback()
            return None, balance
        cursor = con.execute(
            """
            INSERT INTO orders(
                user_id,service_id,service_name,target,quantity,estimated_usd,
                estimated_points,charged_points,free_order,status,request_json,created_at,updated_at
            ) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)
            """,
            (
                user_id,
                str(service["service"]),
                str(service.get("name") or ""),
                target,
                quantity,
                str(estimated_usd),
                str(estimated_points),
                str(charged),
                1 if free else 0,
                "submitting",
                json.dumps(api_order_fields(service, draft), ensure_ascii=False),
                now_ts(),
                now_ts(),
            ),
        )
        order_id = int(cursor.lastrowid)
        if charged > ZERO:
            add_ledger(
                con,
                user_id,
                -charged,
                f"حجز تكلفة طلب Telegram #{order_id}",
                f"order:{order_id}:debit",
            )
        con.commit()
    return order_id, balance


def update_order(
    order_id: int,
    *,
    status: str | None = None,
    api_order_id: str | None = None,
) -> None:
    with db_connect() as con:
        fields = ["updated_at=?"]
        values: list[Any] = [now_ts()]
        if status is not None:
            fields.append("status=?")
            values.append(status)
        if api_order_id is not None:
            fields.append("api_order_id=?")
            values.append(str(api_order_id))
        values.append(order_id)
        con.execute(f"UPDATE orders SET {','.join(fields)} WHERE id=?", values)
        con.commit()


def get_order(order_id: int) -> sqlite3.Row | None:
    with db_connect() as con:
        return con.execute("SELECT * FROM orders WHERE id=?", (order_id,)).fetchone()


def refund_order_reservation(order: sqlite3.Row, reason: str) -> Decimal:
    charged = d(order["charged_points"])
    if charged <= ZERO:
        return ZERO
    with db_connect() as con:
        con.execute("BEGIN IMMEDIATE")
        done = add_ledger(
            con,
            int(order["user_id"]),
            charged,
            reason,
            f"order:{int(order['id'])}:refund",
        )
        con.commit()
    return charged if done else ZERO


async def reconcile_order_cost(order: sqlite3.Row, actual_usd: Decimal) -> None:
    order_id = int(order["id"])
    actual_usd = max(ZERO, actual_usd)
    actual_points = ceil_cent(actual_usd * points_per_usd())
    difference = ZERO
    inserted = False
    with db_connect() as con:
        con.execute("BEGIN IMMEDIATE")
        current = con.execute(
            "SELECT user_id,charged_points,free_order FROM orders WHERE id=?",
            (order_id,),
        ).fetchone()
        if not current:
            con.rollback()
            return
        if int(current["free_order"]):
            con.execute(
                "UPDATE orders SET estimated_usd=?,updated_at=? WHERE id=?",
                (str(actual_usd), now_ts(), order_id),
            )
            con.commit()
            return
        previous_points = d(current["charged_points"])
        difference = previous_points - actual_points
        if difference != ZERO:
            reference = f"order:{order_id}:reconcile:{previous_points:.2f}:{actual_points:.2f}"
            inserted = add_ledger(
                con,
                int(current["user_id"]),
                difference,
                f"تسوية تكلفة طلب Telegram #{order_id}",
                reference,
            )
            if not inserted:
                con.rollback()
                return
        con.execute(
            "UPDATE orders SET charged_points=?,estimated_usd=?,updated_at=? WHERE id=?",
            (str(actual_points), str(actual_usd), now_ts(), order_id),
        )
        con.commit()
    if inserted and difference < ZERO:
        await notify(
            f"{em('warning')} احتاجت تسوية طلب إلى خصم إضافي.\n"
            f"• الطلب المحلي: <code>{order_id}</code>\n"
            f"• المستخدم: {user_label(int(order['user_id']))}\n"
            f"• الرصيد الإضافي المطلوب: <b>{money_text(-difference)}</b>\n"
            "• قد يصبح رصيد المستخدم سالباً حتى يشحنه.",
            "receive_order_notifications",
        )


def order_notification_text(order: sqlite3.Row, state: str, extra: str = "") -> str:
    status_ar = {
        "started": "بدأ إرسال الطلب إلى API",
        "submitted": "قُبل الطلب وأُنشئ لدى الموقع",
        "failed": "رفض الموقع الطلب",
        "uncertain": "نتيجة الإرسال غير مؤكدة وتحتاج مراجعة",
    }.get(state, state)
    api_order_line = (
        f"• رقم طلب الموقع: <code>{e(order['api_order_id'])}</code>\n"
        if order["api_order_id"]
        else ""
    )
    extra_line = f"• ملاحظة: {e(extra)}" if extra else ""
    return (
        f"{em('bell')} <b>{e(status_ar)}</b>\n\n"
        f"• الطلب المحلي: <code>{int(order['id'])}</code>\n"
        f"• المستخدم: {user_label(int(order['user_id']))}\n"
        f"• الخدمة: <b>{e(order['service_name'])}</b> "
        f"(<code>{e(order['service_id'])}</code>)\n"
        f"• الهدف: <code>{e(order['target'])}</code>\n"
        f"• الكمية: <b>{int(order['quantity'])}</b>\n"
        f"• تكلفة API التقديرية: <b>${fmt_usd(order['estimated_usd'])}</b>\n"
        f"• نقاط المستخدم: <b>{fmt_points(order['charged_points'])}</b>"
        f"{' — على حساب المالك' if int(order['free_order']) else ''}\n"
        f"• حالة البوت: <b>{e(order['status'])}</b>\n"
        f"{api_order_line}{extra_line}"
    )


async def submit_order(
    user_id: int,
    chat_id: int,
    free: bool,
    callback: dict[str, Any] | None = None,
) -> None:
    current = read_state(user_id)
    if current and current[0] == "review_checking":
        await send_message(chat_id, "• يجري التحقق من السعر أو تنفيذ الطلب؛ انتظر قليلاً قبل إعادة المحاولة.")
        return
    if not current or current[0] != "review":
        await send_message(chat_id, "• انتهت صلاحية التأكيد. افتح الخدمة وابدأ الطلب من جديد.")
        return
    if is_admin(user_id) and not has_perm(user_id, "use_services"):
        await send_message(chat_id, "• لا تملك صلاحية تنفيذ الطلبات.")
        return
    if free and not (is_owner(user_id) or (is_admin(user_id) and has_perm(user_id, "free_orders"))):
        await send_message(chat_id, "• ليس لديك صلاحية تنفيذ طلب مجاني.")
        return

    draft = claim_review_state(user_id)
    if draft is None:
        await send_message(chat_id, "• بدأ فحص آخر لهذا الطلب بالفعل؛ انتظر ثم افتح الطلبات.")
        return
    service = draft.get("service") or cached_service(str(draft.get("service_id", "")))
    if not service or not service_is_telegram(service):
        clear_state(user_id)
        await send_message(chat_id, "• لم تعد هذه الخدمة متاحة ضمن قائمة Telegram.")
        return

    try:
        services = await load_services(force=True)
    except SMMAPIError as exc:
        save_state(user_id, "review", draft)
        await send_message(
            chat_id,
            f"{em('warning')} تعذّر التحقق من السعر الحالي؛ لم يُرسل الطلب.\n"
            f"• التفاصيل: {e(exc)}\n• حاول التأكيد مرة أخرى بعد عودة الاتصال.",
        )
        return
    fresh_service = next(
        (item for item in services if str(item.get("service")) == str(draft.get("service_id"))),
        None,
    )
    if not fresh_service or not service_is_telegram(fresh_service):
        clear_state(user_id)
        if callback:
            await edit_message(
                callback,
                "• لم تعد هذه الخدمة متاحة ضمن خدمات Telegram.",
                keyboard([button("الخدمات", "services", style="primary", icon="telegram")]),
            )
        else:
            await send_message(chat_id, "• لم تعد هذه الخدمة متاحة ضمن خدمات Telegram.")
        return

    old_service = service
    old_type = service_type(old_service)
    new_type = service_type(fresh_service)
    if old_type != new_type:
        clear_state(user_id)
        if callback:
            await edit_message(
                callback,
                "• غيّر الموقع نوع الخدمة أثناء تجهيز الطلب؛ ابدأ طلباً جديداً لمراجعة الحقول.",
                keyboard([button("الخدمات", "services", style="primary", icon="telegram")]),
            )
        else:
            await send_message(chat_id, "• غيّر الموقع نوع الخدمة؛ ابدأ طلباً جديداً لمراجعة الحقول.")
        return

    if "subscription" in new_type:
        min_allowed, max_allowed = service_min_max(fresh_service)
        valid_limits = (
            min_allowed <= int(draft.get("min", 0)) <= int(draft.get("max", 0)) <= max_allowed
        )
    elif "package" in new_type:
        valid_limits = True
    else:
        min_allowed, max_allowed = service_min_max(fresh_service)
        quantity = int(draft.get("quantity", 0))
        valid_limits = min_allowed <= quantity <= max_allowed
    if not valid_limits:
        clear_state(user_id)
        if callback:
            await edit_message(
                callback,
                f"• تغيّرت حدود الخدمة إلى {min_allowed}–{max_allowed}؛ ابدأ الطلب مجدداً.",
                keyboard([button("الخدمات", "services", style="primary", icon="telegram")]),
            )
        else:
            await send_message(
                chat_id, f"• تغيّرت حدود الخدمة إلى {min_allowed}–{max_allowed}؛ ابدأ الطلب مجدداً."
            )
        return

    old_signature = tuple(
        str(old_service.get(key, ""))
        for key in ("name", "type", "rate", "min", "max", "dripfeed", "refill", "cancel")
    )
    new_signature = tuple(
        str(fresh_service.get(key, ""))
        for key in ("name", "type", "rate", "min", "max", "dripfeed", "refill", "cancel")
    )
    current_points = estimate_points(fresh_service, draft)
    review_is_stale = (
        old_signature != new_signature
        or current_points != d(draft.get("reviewed_points"), ZERO)
        or points_per_usd() != d(draft.get("reviewed_points_per_usd"), ZERO)
    )
    draft["service"] = fresh_service
    if review_is_stale:
        await present_order_review(
            chat_id,
            user_id,
            draft,
            edit_callback=callback,
            notice="تحدّث سعر الخدمة أو بياناتها. راجع الملخص ثم أكّد من جديد.",
        )
        return
    service = fresh_service
    draft["service"] = service
    save_state(user_id, "review", draft)

    order_id, balance_or_current = create_order_and_reserve(user_id, service, draft, free)
    if order_id is None:
        if balance_or_current == ZERO and is_banned(user_id):
            clear_state(user_id)
            await send_message(chat_id, "• لا يمكن تنفيذ الطلب لأن الحساب محظور.")
        else:
            save_state(user_id, "review", draft)
            await send_message(
                chat_id,
                f"{em('warning')} رصيدك غير كافٍ.\n"
                f"• الرصيد الحالي: <b>{money_text(balance_or_current)}</b>\n"
                f"• التكلفة المطلوبة: <b>{money_text(estimate_points(service, draft))}</b>\n"
                "• أضف رصيداً ثم أعد المحاولة.",
                keyboard([button("إضافة رصيد", "wallet", style="success", icon="plus")],
                         [button("الرئيسية", "home", icon="telegram")]),
            )
            return
        return

    clear_state(user_id)
    order = get_order(order_id)
    await notify(order_notification_text(order, "started"))
    await send_message(
        chat_id,
        f"{em('loading')} استلمت طلبك، وأرسله الآن إلى موقع الخدمات.\n"
        f"• رقم المتابعة: <code>{order_id}</code>\n"
        f"• حالة الطلب ستظهر في «طلباتي».",
    )

    try:
        payload = json.loads(order["request_json"])
        response = await smm(payload)
        if not isinstance(response, dict) or response.get("order") is None:
            raise SMMAPIError("لم يُرجع الموقع رقم الطلب المتوقع.")
        api_order_id = str(response["order"])
    except SMMAPIError as exc:
        message = str(exc)
        lower_message = message.casefold()
        uncertain = (
            "network error" in lower_message
            or "timeout" in lower_message
            or "invalid json" in lower_message
            or "http 5" in lower_message
            or "لم يُرجع الموقع رقم الطلب" in message
        )
        if uncertain:
            update_order(order_id, status="uncertain")
            order = get_order(order_id)
            await notify(order_notification_text(order, "uncertain", message))
            await send_message(
                chat_id,
                f"{em('warning')} لم يصلنا تأكيد نهائي من الموقع.\n"
                f"• أوقفنا إعادة الإرسال لتجنب تكرار الطلب.\n"
                f"• رقم المتابعة: <code>{order_id}</code>\n"
                "• راجع «طلباتي» لاحقاً، وتواصل مع الإدارة إذا بقيت الحالة معلّقة.",
            )
            return
        refunded = refund_order_reservation(order, f"استرداد طلب مرفوض #{order_id}")
        update_order(order_id, status="failed")
        order = get_order(order_id)
        await notify(order_notification_text(order, "failed", message))
        await send_message(
            chat_id,
            f"{em('cross')} لم يقبل موقع الخدمات الطلب.\n"
            f"• التفاصيل: {e(message)}\n"
            f"• أُعيد إلى رصيدك: <b>{money_text(refunded)}</b>\n"
            f"• رقم المتابعة: <code>{order_id}</code>",
        )
        return
    except Exception as exc:
        log.exception("Unexpected order submission failure (local order %s)", order_id)
        update_order(order_id, status="uncertain")
        order = get_order(order_id)
        await notify(order_notification_text(order, "uncertain", type(exc).__name__))
        await send_message(
            chat_id,
            f"{em('warning')} حدث عطل غير متوقع أثناء إرسال الطلب.\n"
            f"• لم نعد إرسال الطلب كي لا يتكرر.\n"
            f"• رقم المتابعة: <code>{order_id}</code>\n"
            "• ستراجع الإدارة حالة الطلب قبل أي استرداد.",
        )
        return

    update_order(order_id, status="Submitted", api_order_id=api_order_id)
    order = get_order(order_id)
    actual_charge = None
    try:
        status_result = await smm({"action": "status", "order": api_order_id})
        if (
            isinstance(status_result, dict)
            and status_result.get("charge") is not None
            and str(status_result.get("currency") or "USD").upper() == "USD"
        ):
            actual_charge = d(status_result["charge"], ZERO)
    except SMMAPIError:
        pass
    if actual_charge is not None and actual_charge >= ZERO:
        await reconcile_order_cost(order, actual_charge)
    order = get_order(order_id)
    await notify(order_notification_text(order, "submitted"))
    await send_message(
        chat_id,
        f"{em('check')} تم قبول طلبك لدى الموقع.\n\n"
        f"• رقم المتابعة: <code>{order_id}</code>\n"
        f"• رقم الطلب في الموقع: <code>{e(api_order_id)}</code>\n"
        f"• الخدمة: <b>{e(order['service_name'])}</b>\n"
        f"• المبلغ المحسوب: <b>{money_text(order['charged_points'])}</b>\n"
        "• يمكنك متابعة الحالة أو طلب التعويض/الإلغاء من زر «طلباتي».",
        keyboard([button("عرض طلباتي", "myorders", style="primary", icon="calendar")],
                 [button("الرئيسية", "home", icon="telegram")]),
    )


async def show_wallet(chat_id: int, user_id: int, edit: dict[str, Any] | None = None) -> None:
    ratio = stars_per_point()
    stars = [ratio * amount for amount in (5, 10, 25, 50, 100)]
    rows = [
        [
            button(f"{amount} نجمة", f"stars:{amount}", style="success", icon="star")
            for amount in stars[:3]
        ],
        [
            button(f"{amount} نجمة", f"stars:{amount}", style="success", icon="star")
            for amount in stars[3:]
        ],
        [button("الرئيسية", "home", icon="telegram")],
    ]
    text = (
        f"{em('wallet')} <b>إضافة رصيد عبر Telegram Stars</b>\n\n"
        f"• رصيدك الحالي: <b>{money_text(user_balance(user_id))}</b>\n"
        f"• سعر التحويل الحالي: <b>{ratio} نجوم = نقطة واحدة</b>.\n"
        "• مثال الإعداد الافتراضي: <b>15 نجمة = 5 نقاط</b>.\n"
        "• الفاتورة والدفع يكتملان داخل Telegram، ويُضاف الرصيد بعد تأكيد Telegram للدفع."
    )
    if edit:
        await edit_message(edit, text, keyboard(*rows))
    else:
        await send_message(chat_id, text, keyboard(*rows))


async def create_star_invoice(chat_id: int, user_id: int, stars: int) -> None:
    if int(chat_id) <= 0:
        log.info("Skipped creating a Stars invoice outside a private chat.")
        return
    ratio = stars_per_point()
    if stars < 1 or stars % ratio:
        await send_message(chat_id, "• قيمة النجوم غير صالحة. افتح صفحة الرصيد واختر مبلغاً من القائمة.")
        return
    points = Decimal(stars // ratio)
    payload = "stars-" + uuid.uuid4().hex
    with db_connect() as con:
        con.execute(
            "INSERT INTO payments(payload,user_id,stars,points,status,created_at) VALUES(?,?,?,?,?,?)",
            (payload, user_id, stars, str(points), "pending", now_ts()),
        )
        con.commit()
    try:
        await tg(
            "sendInvoice",
            {
                "chat_id": chat_id,
                "title": f"إضافة {fmt_points(points)} نقطة",
                "description": f"شحن رصيد {fmt_points(points)} نقطة في بوت خدمات Telegram.",
                "payload": payload,
                "currency": "XTR",
                "prices": [{"label": f"{fmt_points(points)} نقطة", "amount": stars}],
                "provider_token": "",
                "start_parameter": "stars_credit",
            },
        )
    except TelegramAPIError as exc:
        with db_connect() as con:
            con.execute("UPDATE payments SET status='invoice_error' WHERE payload=?", (payload,))
            con.commit()
        await send_message(chat_id, f"{em('warning')} تعذّر إنشاء فاتورة Stars: {e(exc)}")


async def handle_pre_checkout(query: dict[str, Any]) -> None:
    payload = str(query.get("invoice_payload") or "")
    user_id = int((query.get("from") or {}).get("id", 0))
    amount = int(query.get("total_amount", 0))
    currency = str(query.get("currency") or "")
    with db_connect() as con:
        row = con.execute("SELECT * FROM payments WHERE payload=?", (payload,)).fetchone()
    valid = bool(
        row
        and row["status"] == "pending"
        and int(row["user_id"]) == user_id
        and int(row["stars"]) == amount
        and currency == "XTR"
        and not is_banned(user_id)
    )
    request: dict[str, Any] = {"pre_checkout_query_id": query["id"], "ok": valid}
    if not valid:
        request["error_message"] = "تعذّر التحقق من الفاتورة. أعد فتح صفحة الرصيد وحاول مرة أخرى."
    await tg("answerPreCheckoutQuery", request)


async def handle_successful_payment(message: dict[str, Any]) -> None:
    payment = message.get("successful_payment") or {}
    user_id = int((message.get("from") or {}).get("id", 0))
    payload = str(payment.get("invoice_payload") or "")
    charge_id = str(payment.get("telegram_payment_charge_id") or "")
    with db_connect() as con:
        con.execute("BEGIN IMMEDIATE")
        row = con.execute("SELECT * FROM payments WHERE payload=?", (payload,)).fetchone()
        if not row:
            con.rollback()
            await notify(
                f"{em('warning')} وصل دفع Stars لا يطابق فاتورة مسجلة.\n"
                f"• المستخدم: <code>{user_id}</code>\n"
                f"• الحمولة: <code>{e(payload)}</code>\n"
                f"• معرّف عملية Telegram: <code>{e(charge_id)}</code>",
                "receive_order_notifications",
            )
            return
        if (
            int(row["user_id"]) != user_id
            or int(row["stars"]) != int(payment.get("total_amount", 0))
            or str(payment.get("currency") or "") != "XTR"
        ):
            con.rollback()
            await notify(
                f"{em('warning')} اختلاف بيانات دفعة Stars عن الفاتورة.\n"
                f"• المستخدم: <code>{user_id}</code>\n"
                f"• مرجع الفاتورة: <code>{e(payload)}</code>\n"
                f"• لم يُضف الرصيد تلقائياً؛ يلزم فحص العملية.",
                "receive_order_notifications",
            )
            return
        if row["status"] == "paid":
            con.rollback()
            return
        points = d(row["points"])
        inserted = add_ledger(
            con,
            user_id,
            points,
            f"شحن Telegram Stars ({int(row['stars'])} نجمة)",
            f"stars:{charge_id or payload}",
        )
        if not inserted:
            con.rollback()
            await notify(
                f"{em('warning')} تم منع إضافة رصيد مكرر لدفعة Stars.\n"
                f"• الفاتورة: <code>{e(payload)}</code>",
                "receive_order_notifications",
            )
            return
        con.execute(
            "UPDATE payments SET status='paid',telegram_charge_id=?,paid_at=? WHERE payload=?",
            (charge_id, now_ts(), payload),
        )
        con.commit()
    await send_message(
        int(message["chat"]["id"]),
        f"{em('check')} تم تأكيد الدفع وإضافة الرصيد.\n"
        f"• المبلغ: <b>{int(payment['total_amount'])} نجمة</b>\n"
        f"• المضاف: <b>{money_text(points)}</b>\n"
        f"• رصيدك الآن: <b>{money_text(user_balance(user_id))}</b>",
    )
    await notify(
        f"{em('bell')} <b>تم شحن رصيد المستخدم عبر Stars</b>\n\n"
        f"• المستخدم: {user_label(user_id)}\n"
        f"• المدفوع: <b>{int(payment['total_amount'])} نجمة</b>\n"
        f"• النقاط المضافة: <b>{money_text(points)}</b>\n"
        f"• معرّف دفعة Telegram: <code>{e(charge_id or 'غير متاح')}</code>\n"
        f"• الفاتورة: <code>{e(payload)}</code>",
    )


async def show_my_orders(chat_id: int, user_id: int, callback: dict[str, Any] | None = None) -> None:
    if is_admin(user_id) and not has_perm(user_id, "view_orders"):
        # Users can always see only their own orders. This restriction applies
        # only to the wider admin order list, not this personal view.
        pass
    with db_connect() as con:
        rows = con.execute(
            "SELECT * FROM orders WHERE user_id=? ORDER BY id DESC LIMIT 10", (user_id,)
        ).fetchall()
    if not rows:
        text = f"{em('info')} لم تُسجل لك طلبات بعد."
        markup = keyboard([button("الخدمات", "services", style="success", icon="telegram")],
                          [button("الرئيسية", "home", icon="telegram")])
    else:
        text = f"{em('calendar')} <b>آخر طلباتك</b>\n\n"
        buttons: list[list[dict[str, Any]]] = []
        for row in rows:
            text += (
                f"• <b>#{int(row['id'])}</b> — {e(row['service_name'])}\n"
                f"  الحالة: <code>{e(row['status'])}</code> · "
                f"المبلغ: <b>{money_text(row['charged_points'])}</b>\n"
            )
            buttons.append([button(f"تفاصيل الطلب #{int(row['id'])}", f"orderinfo:{int(row['id'])}",
                                   style="primary", icon="info")])
        buttons.append([button("الرئيسية", "home", icon="telegram")])
        markup = keyboard(*buttons)
    if callback:
        await edit_message(callback, text, markup)
    else:
        await send_message(chat_id, text, markup)


async def show_order_detail(chat_id: int, user_id: int, callback: dict[str, Any], order_id: int) -> None:
    row = get_order(order_id)
    if not row:
        await send_message(chat_id, "• لم أجد هذا الطلب.")
        return
    if int(row["user_id"]) != user_id and not has_perm(user_id, "view_orders"):
        await send_message(chat_id, "• هذا الطلب لا يخص حسابك.")
        return
    lines = (
        f"{em('info')} <b>تفاصيل الطلب #{order_id}</b>\n\n"
        f"• الخدمة: <b>{e(row['service_name'])}</b> (<code>{e(row['service_id'])}</code>)\n"
        f"• الهدف: <code>{e(row['target'])}</code>\n"
        f"• الكمية: <b>{int(row['quantity'])}</b>\n"
        f"• الحالة: <b>{e(row['status'])}</b>\n"
        f"• التكلفة: <b>{money_text(row['charged_points'])}</b>\n"
        f"• رقم طلب الموقع: <code>{e(row['api_order_id'] or 'لم يصدر بعد')}</code>\n"
        f"• أُنشئ: <code>{time.strftime('%Y-%m-%d %H:%M UTC', time.gmtime(int(row['created_at'])))}</code>"
    )
    buttons: list[list[dict[str, Any]]] = [
        [button("تحديث الحالة", f"status:{order_id}", style="primary", icon="loading")]
    ]
    try:
        original = json.loads(row["request_json"])
        service = cached_service(str(row["service_id"])) or {}
    except json.JSONDecodeError:
        original, service = {}, {}
    status = str(row["status"]).casefold()
    if row["api_order_id"] and service.get("refill") and status not in ("completed", "canceled", "cancelled"):
        buttons.append([button("طلب تعويض", f"refill:{order_id}", style="success", icon="check")])
    if row["api_order_id"] and service.get("cancel") and status not in ("completed", "canceled", "cancelled"):
        buttons.append([button("طلب إلغاء", f"cancelorder:{order_id}", style="danger", icon="cross")])
    with db_connect() as con:
        refill = con.execute(
            "SELECT refill_id,status FROM refills WHERE order_id=? ORDER BY created_at DESC LIMIT 1",
            (order_id,),
        ).fetchone()
    if refill:
        lines += (
            f"\n• آخر تعويض: <code>{e(refill['refill_id'])}</code> — "
            f"<b>{e(refill['status'])}</b>"
        )
        buttons.append([
            button(
                "تحديث حالة التعويض",
                f"refillstatus:{refill['refill_id']}",
                style="primary",
                icon="loading",
            )
        ])
    buttons.append([button("رجوع لطلباتي", "myorders", icon="calendar")])
    await edit_message(callback, lines, keyboard(*buttons))


async def refresh_order_status(chat_id: int, user_id: int, callback: dict[str, Any], order_id: int) -> None:
    row = get_order(order_id)
    if not row or (int(row["user_id"]) != user_id and not has_perm(user_id, "view_orders")):
        await send_message(chat_id, "• لا يمكن الوصول لهذا الطلب.")
        return
    if not row["api_order_id"]:
        await send_message(chat_id, "• لم يصدر رقم طلب من الموقع حتى الآن.")
        return
    try:
        result = await smm({"action": "status", "order": str(row["api_order_id"])})
    except SMMAPIError as exc:
        await send_message(chat_id, f"{em('warning')} تعذّر تحديث الحالة: {e(exc)}")
        return
    if isinstance(result, dict):
        status = str(result.get("status") or "غير معروف")
        update_order(order_id, status=status)
        if (
            result.get("charge") is not None
            and str(result.get("currency") or "USD").upper() == "USD"
        ):
            actual_charge = d(result["charge"], ZERO)
            if actual_charge >= ZERO:
                await reconcile_order_cost(get_order(order_id), actual_charge)
        details = (
            f"• الحالة: <b>{e(status)}</b>\n"
            f"• المتبقي: <b>{e(result.get('remains', 'غير متاح'))}</b>\n"
            f"• العدد عند البدء: <b>{e(result.get('start_count', 'غير متاح'))}</b>\n"
            f"• التكلفة التي أبلغ بها الموقع: <b>{e(result.get('charge', 'غير متاح'))} {e(result.get('currency', ''))}</b>"
        )
        await send_message(chat_id, f"{em('info')} تحديث الطلب <code>#{order_id}</code>\n\n{details}")
    else:
        await send_message(chat_id, "• أرجع الموقع صيغة حالة غير متوقعة.")


async def request_refill(chat_id: int, user_id: int, callback: dict[str, Any], order_id: int) -> None:
    row = get_order(order_id)
    if not row or (int(row["user_id"]) != user_id and not has_perm(user_id, "view_orders")):
        await send_message(chat_id, "• لا يمكن الوصول لهذا الطلب.")
        return
    if not row["api_order_id"]:
        await send_message(chat_id, "• لا يوجد رقم طلب لدى الموقع لهذا الطلب.")
        return
    with db_connect() as con:
        prior = con.execute(
            "SELECT status FROM refills WHERE order_id=? ORDER BY created_at DESC LIMIT 1",
            (order_id,),
        ).fetchone()
    if prior and str(prior["status"]).casefold() not in ("rejected", "failed"):
        await send_message(
            chat_id,
            f"{em('info')} يوجد طلب تعويض سابق بحالة <b>{e(prior['status'])}</b>.\n"
            "• حدّث حالته قبل إرسال طلب آخر.",
        )
        return
    try:
        result = await smm({"action": "refill", "order": str(row["api_order_id"])})
    except SMMAPIError as exc:
        await send_message(chat_id, f"{em('warning')} تعذّر إرسال طلب التعويض: {e(exc)}")
        return
    refill_id = result.get("refill", "قيد المعالجة") if isinstance(result, dict) else "قيد المعالجة"
    if isinstance(refill_id, dict) and refill_id.get("error"):
        await send_message(chat_id, f"{em('warning')} رفض الموقع طلب التعويض: {e(refill_id['error'])}")
        return
    message = result.get("message", "") if isinstance(result, dict) else ""
    if str(refill_id) != "قيد المعالجة":
        with db_connect() as con:
            con.execute(
                "INSERT OR IGNORE INTO refills(refill_id,order_id,user_id,status,created_at,updated_at) "
                "VALUES(?,?,?,?,?,?)",
                (str(refill_id), order_id, int(row["user_id"]), "Pending", now_ts(), now_ts()),
            )
            con.commit()
    await notify(
        f"{em('bell')} أرسل المستخدم طلب تعويض.\n"
        f"• المستخدم: {user_label(int(row['user_id']))}\n"
        f"• الطلب المحلي: <code>#{order_id}</code> · طلب الموقع: <code>{e(row['api_order_id'])}</code>\n"
        f"• رقم التعويض: <code>{e(refill_id)}</code>",
    )
    await send_message(chat_id, f"{em('check')} تم إرسال طلب التعويض.\n• رقم التعويض: <code>{e(refill_id)}</code>\n"
                               f"{'• ' + e(message) if message else ''}")


async def refresh_refill_status(
    chat_id: int,
    user_id: int,
    refill_id: str,
) -> None:
    with db_connect() as con:
        row = con.execute("SELECT * FROM refills WHERE refill_id=?", (refill_id,)).fetchone()
    if not row or (int(row["user_id"]) != user_id and not has_perm(user_id, "view_orders")):
        await send_message(chat_id, "• لا يمكن الوصول إلى حالة هذا التعويض.")
        return
    try:
        result = await smm({"action": "refill_status", "refill": refill_id})
    except SMMAPIError as exc:
        await send_message(chat_id, f"{em('warning')} تعذّر تحديث حالة التعويض: {e(exc)}")
        return
    status = str(result.get("status", "غير معروف")) if isinstance(result, dict) else "غير معروف"
    with db_connect() as con:
        con.execute(
            "UPDATE refills SET status=?,updated_at=? WHERE refill_id=?",
            (status, now_ts(), refill_id),
        )
        con.commit()
    await send_message(
        chat_id,
        f"{em('info')} حالة التعويض <code>{e(refill_id)}</code>: <b>{e(status)}</b>",
    )


async def cancel_remote_order(chat_id: int, user_id: int, callback: dict[str, Any], order_id: int) -> None:
    row = get_order(order_id)
    if not row or (int(row["user_id"]) != user_id and not has_perm(user_id, "view_orders")):
        await send_message(chat_id, "• لا يمكن الوصول لهذا الطلب.")
        return
    if not row["api_order_id"]:
        await send_message(chat_id, "• لا يوجد رقم طلب لدى الموقع لإرسال طلب إلغاء.")
        return
    if str(row["status"]).casefold() == "cancel requested":
        await send_message(chat_id, "• سبق إرسال طلب إلغاء لهذا الطلب؛ حدّث الحالة بدلاً من تكراره.")
        return
    try:
        result = await smm({"action": "cancel", "order": str(row["api_order_id"])})
    except SMMAPIError as exc:
        await send_message(chat_id, f"{em('warning')} تعذّر إرسال طلب الإلغاء: {e(exc)}")
        return
    status = result.get("status", "قيد المحاولة") if isinstance(result, dict) else "قيد المحاولة"
    message = result.get("message", "") if isinstance(result, dict) else ""
    update_order(order_id, status="Cancel requested")
    await notify(
        f"{em('bell')} أرسل المستخدم طلب إلغاء.\n"
        f"• المستخدم: {user_label(int(row['user_id']))}\n"
        f"• الطلب المحلي: <code>#{order_id}</code> · طلب الموقع: <code>{e(row['api_order_id'])}</code>\n"
        f"• النتيجة: <code>{e(status)}</code>",
    )
    await send_message(chat_id, f"{em('info')} نتيجة طلب الإلغاء: <b>{e(status)}</b>\n"
                               f"{'• ' + e(message) if message else ''}")


async def show_proof(chat_id: int, callback: dict[str, Any] | None = None) -> None:
    proof_url = get_setting("proof_url", "").strip()
    if proof_url:
        text = (
            f"{em('check')} <b>قناة الإثباتات والتقييمات</b>\n\n"
            "• افتح القناة لمشاهدة المنشورات والتجارب المتاحة.\n"
            "• استخدم زر التقييم إذا رغبت في مشاركة رأيك."
        )
        markup = keyboard(
            [button("فتح قناة الإثباتات", url=proof_url, style="primary", icon="telegram")],
            [button("الرئيسية", "home", icon="telegram")],
        )
    else:
        text = (
            f"{em('info')} لم يضف المالك رابط قناة الإثباتات بعد.\n\n"
            "• يمكنك متابعة البوت أو إرسال شكوى من القائمة الرئيسية."
        )
        markup = keyboard([button("الرئيسية", "home", icon="telegram")])
    if callback:
        await edit_message(callback, text, markup)
    else:
        await send_message(chat_id, text, markup)


async def show_developer(chat_id: int, callback: dict[str, Any] | None = None) -> None:
    contact = get_setting("developer_contact", "").strip()
    text = (
        f"{em('settings')} <b>طلب نسخة والتواصل مع المطوّر</b>\n\n"
        "• لطلب نسخة من البوت أو الاستفسار عن التطوير، استخدم وسيلة التواصل المحددة أدناه.\n"
        "• إذا لم يظهر زر التواصل، أرسل طلبك عبر «إرسال شكوى» وسيراجعه المالك."
    )
    rows: list[list[dict[str, Any]]] = []
    if contact.startswith("@") and VALID_USERNAME.fullmatch(contact[1:]):
        rows.append([button("التواصل مع المطوّر", url="https://t.me/" + contact[1:],
                            style="primary", icon="telegram")])
    elif contact.startswith("https://"):
        rows.append([button("التواصل مع المطوّر", url=contact, style="primary", icon="telegram")])
    rows.append([button("إرسال طلب للمالك", "complaint", style="success", icon="plus")])
    rows.append([button("الرئيسية", "home", icon="telegram")])
    if callback:
        await edit_message(callback, text, keyboard(*rows))
    else:
        await send_message(chat_id, text, keyboard(*rows))


async def begin_complaint(chat_id: int, user_id: int) -> None:
    save_state(user_id, "complaint", {})
    await send_message(
        chat_id,
        f"{em('info')} اكتب الشكوى أو الملاحظة في رسالة واحدة.\n\n"
        "• لا ترسل كلمات مرور أو بيانات دفع.\n"
        "• استخدم /cancel إذا أردت الإلغاء.",
        cancel_keyboard(),
    )


async def save_complaint(message: dict[str, Any]) -> None:
    user = message["from"]
    user_id = int(user["id"])
    chat_id = int(message["chat"]["id"])
    body = str(message.get("text") or "").strip()
    if not body:
        await send_message(chat_id, "• أرسل نصاً مكتوباً للشكوى، أو أرسل /cancel.")
        return
    if len(body) > 3500:
        await send_message(chat_id, "• اختصر الشكوى إلى 3500 حرف كحد أقصى.")
        return
    clear_state(user_id)
    with db_connect() as con:
        cursor = con.execute(
            "INSERT INTO complaints(user_id,message,created_at) VALUES(?,?,?)",
            (user_id, body, now_ts()),
        )
        complaint_id = int(cursor.lastrowid)
        con.commit()
    await send_message(
        chat_id,
        f"{em('check')} شكراً لمشاركتك ملاحظتك.\n"
        "• احتفظنا بها لمراجعتها، ويمكنك العودة للقائمة الرئيسية.",
        keyboard([button("الرئيسية", "home", icon="telegram")]),
    )
    await notify(
        f"{em('bell')} <b>شكوى أو ملاحظة جديدة</b>\n\n"
        f"• رقم الرسالة: <code>#{complaint_id}</code>\n"
        f"• المرسل: {user_label(user_id)}\n"
        f"• النص:\n{e(body)}",
        "view_feedback",
    )


async def show_rating(chat_id: int, callback: dict[str, Any] | None = None) -> None:
    rows = [
        [button(f"{n} نجمة", f"rate:{n}", style="primary", icon="star") for n in (1, 2, 3)],
        [button(f"{n} نجمة", f"rate:{n}", style="success", icon="star") for n in (4, 5)],
        [button("الرئيسية", "home", icon="telegram")],
    ]
    text = (
        f"{em('star')} <b>قيّم تجربتك مع البوت</b>\n\n"
        "• اختر عدداً من النجوم من 1 إلى 5.\n"
        "• يمكنك إغلاق هذه الصفحة دون إرسال تقييم."
    )
    if callback:
        await edit_message(callback, text, keyboard(*rows))
    else:
        await send_message(chat_id, text, keyboard(*rows))


async def save_rating(user: dict[str, Any], rating: int) -> None:
    uid = int(user["id"])
    ensure_user(user)
    full_name = " ".join(
        part for part in (user.get("first_name", ""), user.get("last_name", "")) if part
    ) or "غير محدد"
    with db_connect() as con:
        con.execute(
            """
            INSERT INTO ratings(user_id,rating,created_at,username,first_name)
            VALUES(?,?,?,?,?)
            ON CONFLICT(user_id) DO UPDATE SET
                rating=excluded.rating,created_at=excluded.created_at,
                username=excluded.username,first_name=excluded.first_name
            """,
            (uid, rating, now_ts(), user.get("username", "") or "", full_name),
        )
        con.commit()
    await notify(
        f"{em('star')} <b>تقييم جديد</b>\n\n"
        f"• الاسم: {e(full_name)}\n"
        f"• اليوزر: @{e(user.get('username') or 'غير متاح')}\n"
        f"• المعرّف: <code>{uid}</code>\n"
        f"• التقييم: <b>{rating} من 5 نجوم</b>",
        "view_feedback",
    )


def admin_panel_keyboard(user_id: int) -> dict[str, Any]:
    rows: list[list[dict[str, Any]]] = []
    if has_perm(user_id, "view_orders"):
        rows.append([button("آخر الطلبات", "adminorders", style="primary", icon="calendar")])
    if has_perm(user_id, "view_feedback"):
        rows.append([button("الشكاوى والتقييمات", "adminfeedback", style="primary", icon="info")])
    if has_perm(user_id, "manage_services"):
        rows.append([button("إدارة الخدمات", "panelservices", style="primary", icon="telegram")])
    if has_perm(user_id, "manage_settings"):
        rows.append([button("إعدادات البوت", "adminsettings", style="primary", icon="settings")])
    if has_perm(user_id, "ban_users") or has_perm(user_id, "manage_balance"):
        rows.append([button("إدارة المستخدمين", "panelusers", style="primary", icon="shield")])
    if is_owner(user_id):
        rows.append([button("إدارة المديرين والصلاحيات", "admins", style="primary", icon="shield")])
    rows.append([button("حالة الاتصال والرصيد", "panelstatus", style="primary", icon="info")])
    rows.append([button("شرح لوحة الإدارة", "adminhelp", style="primary", icon="info")])
    rows.append([button("الرئيسية", "home", icon="telegram")])
    return keyboard(*rows)


async def show_admin_panel(chat_id: int, user_id: int, callback: dict[str, Any] | None = None) -> None:
    if not is_admin(user_id):
        text = "• لوحة الإدارة متاحة للمالك والمديرين المعتمدين فقط."
        if callback:
            await edit_message(callback, text, keyboard([button("الرئيسية", "home", icon="telegram")]))
        else:
            await send_message(chat_id, text)
        return
    text = (
        f"{em('shield')} <b>لوحة الإدارة</b>\n\n"
        f"• حسابك: {'المالك' if is_owner(user_id) else 'مدير'}\n"
        f"• صلاحياتك: <b>{len(admin_permissions(user_id))}</b>\n"
        "• اختر الإجراء الذي تملكه صلاحياته."
    )
    markup = admin_panel_keyboard(user_id)
    if callback:
        await edit_message(callback, text, markup)
    else:
        await send_message(chat_id, text, markup)


async def show_user_management(
    chat_id: int,
    user_id: int,
    callback: dict[str, Any] | None = None,
) -> None:
    rows: list[list[dict[str, Any]]] = []
    if has_perm(user_id, "ban_users"):
        rows.extend([
            [button("حظر مستخدم", "panelban", style="danger", icon="cross"),
             button("فك الحظر", "panelunban", style="success", icon="check")],
        ])
    if has_perm(user_id, "manage_balance"):
        rows.append([button("إضافة نقاط لمستخدم", "panelcredit", style="primary", icon="wallet")])
    rows.append([button("لوحة الإدارة", "admin", icon="shield")])
    text = (
        f"{em('shield')} <b>إدارة المستخدمين</b>\n\n"
        "• اختر الإجراء، ثم أدخل معرّف المستخدم واتبع التعليمات."
    )
    markup = keyboard(*rows)
    if callback:
        await edit_message(callback, text, markup)
    else:
        await send_message(chat_id, text, markup)


async def show_service_management(
    chat_id: int,
    user_id: int,
    callback: dict[str, Any] | None = None,
) -> None:
    if not has_perm(user_id, "manage_services"):
        text = "• لا تملك صلاحية إدارة الخدمات."
        if callback:
            await edit_message(callback, text, keyboard([button("لوحة الإدارة", "admin", icon="shield")]))
        else:
            await send_message(chat_id, text)
        return
    text = (
        f"{em('telegram')} <b>إدارة الخدمات</b>\n\n"
        "• أظهر خدمة Telegram راجعتها وتأكدت من ملاءمتها.\n"
        "• أخفِ خدمة من القائمة إذا لم تعد مناسبة.\n"
        "• سيُطلب منك رقم الخدمة الموجود في قائمة SMM Rocket."
    )
    markup = keyboard(
        [button("إظهار خدمة", "panelservice:allow", style="success", icon="check"),
         button("إخفاء خدمة", "panelservice:block", style="danger", icon="cross")],
        [button("مزامنة الخدمات", "panelservices_refresh", style="primary", icon="loading")],
        [button("لوحة الإدارة", "admin", icon="shield")],
    )
    if callback:
        await edit_message(callback, text, markup)
    else:
        await send_message(chat_id, text, markup)


async def begin_panel_input(
    chat_id: int,
    user_id: int,
    step: str,
    prompt: str,
    data: dict[str, Any] | None = None,
) -> None:
    save_state(user_id, step, data or {})
    await send_message(chat_id, prompt, cancel_keyboard())


async def show_admin_list(chat_id: int, callback: dict[str, Any]) -> None:
    if not is_owner(int(callback["from"]["id"])):
        await edit_message(
            callback,
            "• إدارة المديرين للمالك فقط.",
            keyboard([button("الرئيسية", "home", icon="telegram")]),
        )
        return
    with db_connect() as con:
        rows = con.execute("SELECT user_id FROM admins ORDER BY added_at DESC").fetchall()
    rows = [row for row in rows if not is_owner(int(row["user_id"]))]
    buttons = [
        [button(f"مدير {row['user_id']}", f"adminselect:{int(row['user_id'])}",
                style="primary", icon="shield")]
        for row in rows
    ]
    buttons.append([button("إضافة مدير", "adminadd", style="success", icon="plus")])
    buttons.append([button("رجوع", "admin", icon="telegram")])
    text = (
        f"{em('shield')} <b>المديرون</b>\n\n"
        f"• عدد المديرين: <b>{len(rows)}</b>\n"
        "• أضف مديراً من الزر أدناه، ثم افتح اسمه لاختيار صلاحياته.\n"
        "• المدير الجديد لا يحصل على صلاحيات تلقائياً."
    )
    await edit_message(callback, text, keyboard(*buttons))


async def show_admin_permissions(chat_id: int, callback: dict[str, Any], admin_id: int) -> None:
    if not is_owner(int(callback["from"]["id"])):
        await edit_message(
            callback,
            "• تعديل الصلاحيات للمالك فقط.",
            keyboard([button("الرئيسية", "home", icon="telegram")]),
        )
        return
    if is_owner(admin_id):
        await edit_message(
            callback,
            "• المالك لا تُدار صلاحياته من قائمة المديرين.",
            keyboard([button("رجوع", "admins", icon="telegram")]),
        )
        return
    with db_connect() as con:
        row = con.execute("SELECT permissions FROM admins WHERE user_id=?", (admin_id,)).fetchone()
    if not row:
        await edit_message(callback, "• هذا المدير غير موجود.", keyboard([button("رجوع", "admins", icon="telegram")]))
        return
    try:
        active = set(json.loads(row["permissions"]))
    except (json.JSONDecodeError, TypeError):
        active = set()
    rows: list[list[dict[str, Any]]] = []
    for key, label in PERMISSIONS.items():
        enabled = key in active
        mark = "✓" if enabled else "×"
        rows.append([
            button(f"{mark} {label}", f"admperm:{admin_id}:{key}",
                   style="success" if enabled else "danger",
                   icon="check" if enabled else "cross")
        ])
    rows.append([button("حذف المدير", f"admremove:{admin_id}", style="danger", icon="cross")])
    rows.append([button("رجوع لقائمة المديرين", "admins", icon="telegram")])
    text = (
        f"{em('settings')} <b>صلاحيات المدير {admin_id}</b>\n\n"
        "• اضغط على الصلاحية لتفعيلها أو إيقافها.\n"
        "• لا يمكن للمدير منح نفسه صلاحيات أو إدارة المديرين الآخرين."
    )
    await edit_message(callback, text, keyboard(*rows))


def admin_order_lines(limit: int = 15) -> str:
    with db_connect() as con:
        rows = con.execute("SELECT * FROM orders ORDER BY id DESC LIMIT ?", (limit,)).fetchall()
    if not rows:
        return "• لا توجد طلبات حتى الآن."
    lines = [f"{em('calendar')} <b>آخر {len(rows)} طلباً</b>\n"]
    for row in rows:
        status = str(row["status"] or "").strip()
        status_label = {
            "pending": "قيد الانتظار",
            "submitted": "تم الإرسال",
            "processing": "قيد التنفيذ",
            "in progress": "قيد التنفيذ",
            "completed": "مكتمل",
            "partial": "مكتمل جزئياً",
            "canceled": "ملغي",
            "cancelled": "ملغي",
            "cancel requested": "تم طلب الإلغاء",
            "failed": "فشل",
            "uncertain": "يحتاج إلى مراجعة",
        }.get(status.casefold(), status)
        lines.append(
            f"• <b>#{int(row['id'])}</b> — {e(row['service_name'])} · "
            f"<b>{e(status_label)}</b>\n"
            f"  المستخدم: {user_label(int(row['user_id']))} · "
            f"الموقع: <code>{e(row['api_order_id'] or 'قيد الإرسال')}</code>\n"
        )
    return "\n".join(lines)


async def show_admin_feedback(chat_id: int, user_id: int) -> None:
    if not has_perm(user_id, "view_feedback"):
        await send_message(chat_id, "• لا تملك صلاحية مشاهدة التقييمات والشكاوى.")
        return
    with db_connect() as con:
        complaints = con.execute(
            "SELECT * FROM complaints ORDER BY id DESC LIMIT 10"
        ).fetchall()
        ratings = con.execute(
            "SELECT * FROM ratings ORDER BY created_at DESC LIMIT 10"
        ).fetchall()
    text = f"{em('info')} <b>آخر الشكاوى</b>\n\n"
    if not complaints:
        text += "• لا توجد شكاوى.\n"
    else:
        for item in complaints:
            text += (
                f"• <b>#{int(item['id'])}</b> — {user_label(int(item['user_id']))}\n"
                f"  {e(str(item['message'])[:350])}\n"
            )
    text += "\n" + f"{em('star')} <b>آخر التقييمات</b>\n\n"
    if not ratings:
        text += "• لا توجد تقييمات.\n"
    else:
        for item in ratings:
            user_tag = f"@{e(item['username'])}" if item["username"] else str(item["user_id"])
            text += f"• {e(item['first_name'])} ({user_tag}) — <b>{int(item['rating'])}/5</b>\n"
    await send_message(chat_id, text, keyboard([button("لوحة الإدارة", "admin", icon="shield")]))


async def show_admin_settings(
    chat_id: int,
    user_id: int,
    callback: dict[str, Any] | None = None,
) -> None:
    if not has_perm(user_id, "manage_settings"):
        text = "• لا تملك صلاحية تعديل الإعدادات."
        if callback:
            await edit_message(callback, text, keyboard([button("لوحة الإدارة", "admin", icon="shield")]))
        else:
            await send_message(chat_id, text)
        return
    text = (
        f"{em('settings')} <b>إعدادات البوت</b>\n\n"
        f"• السعر: <b>{fmt_points(points_per_usd())} نقطة لكل دولار أمريكي</b>.\n"
        f"• تحويل نجوم تيليجرام: <b>{stars_per_point()} نجوم لكل نقطة</b>.\n"
        f"• قناة الإثباتات: <code>{e(get_setting('proof_url', '') or 'غير محددة')}</code>\n"
        f"• المطوّر: <code>{e(get_setting('developer_contact', '') or 'غير محدد')}</code>\n\n"
        "• اختر الإعداد الذي تريد تغييره من الأزرار."
    )
    markup = keyboard(
        [button("سعر النقاط", "panelsetting:points", style="primary", icon="wallet"),
         button("تحويل النجوم", "panelsetting:stars", style="primary", icon="star")],
        [button("قناة الإثباتات", "panelsetting:proof", style="primary", icon="check")],
        [button("بيانات المطوّر", "panelsetting:developer", style="primary", icon="settings")],
        [button("قنوات الاشتراك الإجباري", "mandatorychannels", style="primary", icon="lock")],
        [button("لوحة الإدارة", "admin", icon="shield")],
    )
    if callback:
        await edit_message(callback, text, markup)
    else:
        await send_message(chat_id, text, markup)


async def show_mandatory_channel_management(
    chat_id: int,
    user_id: int,
    callback: dict[str, Any] | None = None,
) -> None:
    if not has_perm(user_id, "manage_settings"):
        text = "• لا تملك صلاحية إدارة قنوات الاشتراك الإجباري."
        markup = keyboard([button("لوحة الإدارة", "admin", icon="shield")])
    else:
        channels = mandatory_channels()
        rows = [
            [
                button(
                    f"حذف: {str(channel['title'])[:38]}",
                    f"mandatory_remove:{int(channel['id'])}",
                    style="danger",
                    icon="cross",
                )
            ]
            for channel in channels[:25]
        ]
        rows.append([button("إضافة قناة", "mandatory_add", style="success", icon="plus")])
        rows.append([button("إعدادات البوت", "adminsettings", icon="settings")])
        text = (
            f"{em('lock')} <b>قنوات الاشتراك الإجباري</b>\n\n"
            f"• القنوات الحالية: <b>{len(channels)}</b>\n"
            "• اضغط على اسم القناة لحذفها.\n"
            "• يجب أن يكون البوت مشرفاً كي يتحقق من اشتراك المستخدمين."
        )
        if len(channels) > 25:
            text += "\n• تظهر أول 25 قناة فقط؛ احذف القنوات الظاهرة أو راجع قاعدة البيانات للبقية."
        if not channels:
            text += "\n• لا توجد قنوات مطلوبة حالياً."
        markup = keyboard(*rows)
    if callback:
        await edit_message(callback, text, markup)
    else:
        await send_message(chat_id, text, markup)


async def show_panel_status(chat_id: int, user_id: int) -> None:
    if not is_admin(user_id):
        await send_message(chat_id, "• هذا الإجراء للمديرين فقط.")
        return
    try:
        balance = await smm({"action": "balance"})
        services = await telegram_services(force=True)
        amount = balance.get("balance", "غير متاح") if isinstance(balance, dict) else "غير متاح"
        currency = balance.get("currency", "USD") if isinstance(balance, dict) else "USD"
        currency_label = "دولار أمريكي" if str(currency).upper() == "USD" else str(currency)
        text = (
            f"{em('check')} <b>حالة الاتصال</b>\n\n"
            f"• SMM Rocket: <b>متصل</b>\n"
            f"• الرصيد المتاح: <b>{e(amount)} {e(currency_label)}</b>\n"
            f"• خدمات Telegram الظاهرة: <b>{len(services)}</b>\n"
            f"• سعر التحويل: <b>{fmt_points(points_per_usd())} نقطة لكل دولار أمريكي</b>"
        )
    except SMMAPIError as exc:
        text = f"{em('warning')} تعذّر الاتصال بـ SMM Rocket.\n• التفاصيل: {e(exc)}"
    await send_message(chat_id, text, keyboard([button("لوحة الإدارة", "admin", icon="shield")]))


async def show_admin_help(chat_id: int, user_id: int, callback: dict[str, Any] | None = None) -> None:
    if not is_admin(user_id):
        if callback:
            await edit_message(
                callback,
                "• هذا القسم للمديرين فقط.",
                keyboard([button("الرئيسية", "home", icon="telegram")]),
            )
        else:
            await send_message(chat_id, "• هذا القسم للمديرين فقط.")
        return
    text = (
        f"{em('info')} <b>طريقة استخدام لوحة الإدارة</b>\n\n"
        "• اختر القسم المناسب من لوحة الإدارة للوصول إلى الإجراء.\n"
        "• عند طلب رقم مستخدم أو خدمة، أرسل الرقم في المحادثة ثم اتبع التعليمات.\n"
        "• إدارة المديرين والصلاحيات متاحة للمالك فقط.\n"
        "• لإلغاء أي خطوة جارية، اضغط زر «إلغاء»."
    )
    markup = keyboard([button("لوحة الإدارة", "admin", icon="shield")])
    if callback:
        await edit_message(callback, text, markup)
    else:
        await send_message(chat_id, text, markup)


async def handle_admin_command(message: dict[str, Any], command: str, args: str) -> bool:
    user_id = int(message["from"]["id"])
    chat_id = int(message["chat"]["id"])
    parts = args.split()

    if command in ("admin_add", "admin_remove"):
        if not is_owner(user_id):
            await send_message(chat_id, "• هذا الأمر متاح للمالك فقط.")
            return True
        if not parts or not parts[0].isdigit():
            await send_message(chat_id, f"• الاستخدام: <code>/{command} 123456789</code>")
            return True
        target = parse_panel_user_id(parts[0]) if parts else None
        if target is None or is_owner(target):
            await send_message(chat_id, "• معرّف المستخدم غير صالح.")
            return True
        with db_connect() as con:
            if command == "admin_add":
                con.execute(
                    "INSERT OR IGNORE INTO admins(user_id,permissions,added_at) VALUES(?,?,?)",
                    (target, "[]", now_ts()),
                )
                con.commit()
                await send_message(
                    chat_id,
                    f"{em('check')} تم تسجيل المدير <code>{target}</code> بصلاحيات فارغة.\n"
                    "• افتح «إدارة المديرين والصلاحيات» لمنحه الصلاحيات المطلوبة.",
                )
            else:
                con.execute("DELETE FROM admins WHERE user_id=?", (target,))
                con.commit()
                await send_message(chat_id, f"{em('check')} أُزيل المدير <code>{target}</code>.")
        return True

    if command in ("ban", "unban"):
        if not has_perm(user_id, "ban_users"):
            await send_message(chat_id, "• لا تملك صلاحية حظر المستخدمين.")
            return True
        if not parts or not parts[0].isdigit():
            await send_message(chat_id, f"• الاستخدام: <code>/{command} 123456789 سبب اختياري</code>")
            return True
        target = parse_panel_user_id(parts[0])
        if target is None:
            await send_message(chat_id, "• معرّف المستخدم غير صالح.")
            return True
        if is_owner(target) or (is_admin(target) and not is_owner(user_id)):
            await send_message(chat_id, "• لا يمكن بهذا الأمر حظر المالك أو مدير آخر.")
            return True
        reason = " ".join(parts[1:])[:300] or "بدون سبب مضاف"
        with db_connect() as con:
            con.execute(
                "INSERT OR IGNORE INTO users(user_id,created_at,updated_at) VALUES(?,?,?)",
                (target, now_ts(), now_ts()),
            )
            con.execute(
                "UPDATE users SET banned=?,updated_at=? WHERE user_id=?",
                (1 if command == "ban" else 0, now_ts(), target),
            )
            con.commit()
        result = "حُظر" if command == "ban" else "فُك حظره"
        await send_message(chat_id, f"{em('check')} {result} المستخدم <code>{target}</code>.\n• السبب/الملاحظة: {e(reason)}")
        try:
            await send_message(
                target,
                f"{em('warning')} تم تحديث حالة حسابك في البوت.\n"
                f"• الحالة: <b>{'محظور' if command == 'ban' else 'غير محظور'}</b>.",
            )
        except TelegramAPIError:
            pass
        return True

    if command == "credit":
        if not has_perm(user_id, "manage_balance"):
            await send_message(chat_id, "• لا تملك صلاحية تعديل الأرصدة.")
            return True
        if len(parts) < 2 or not parts[0].isdigit():
            await send_message(chat_id, "• الاستخدام: <code>/credit 123456789 10 سبب</code>")
            return True
        target = parse_panel_user_id(parts[0])
        amount = d(parts[1], Decimal("-1"))
        if target is None or not amount.is_finite() or amount <= ZERO or amount > Decimal("1000000000"):
            await send_message(chat_id, "• أدخل معرّفاً صحيحاً ومبلغ نقاط موجباً.")
            return True
        reason = " ".join(parts[2:])[:180] or "تعديل إداري"
        ensure_user({"id": target})
        with db_connect() as con:
            con.execute("BEGIN IMMEDIATE")
            add_ledger(con, target, amount, f"تعديل إداري: {reason}", f"admin-credit:{uuid.uuid4().hex}")
            con.commit()
        await send_message(
            chat_id,
            f"{em('check')} أُضيفت <b>{money_text(amount)}</b> إلى المستخدم <code>{target}</code>.\n"
            f"• الرصيد الحالي: <b>{money_text(user_balance(target))}</b>",
        )
        try:
            await send_message(target, f"{em('wallet')} أُضيف إلى رصيدك <b>{money_text(amount)}</b>.")
        except TelegramAPIError:
            pass
        return True

    if command == "points":
        if not has_perm(user_id, "manage_settings"):
            await send_message(chat_id, "• لا تملك صلاحية تعديل التسعير.")
            return True
        rate = d(parts[0], ZERO) if parts else ZERO
        if not rate.is_finite() or rate <= ZERO or rate > Decimal("1000000"):
            await send_message(chat_id, "• الاستخدام: <code>/points 25</code> — أدخل رقماً أكبر من صفر.")
            return True
        set_setting("points_per_usd", str(rate))
        await send_message(
            chat_id,
            f"{em('check')} تم ضبط سعر التكلفة على <b>{fmt_points(rate)} نقطة لكل دولار أمريكي</b>.\n"
            "• يؤثر التغيير على الطلبات الجديدة فقط.",
        )
        return True

    if command == "starsrate":
        if not has_perm(user_id, "manage_settings"):
            await send_message(chat_id, "• لا تملك صلاحية تعديل تحويل Stars.")
            return True
        ratio = parse_positive_int(parts[0], 1000) if parts else None
        if ratio is None:
            await send_message(chat_id, "• الاستخدام: <code>/starsrate 3</code> — عدد النجوم لكل نقطة.")
            return True
        set_setting("stars_per_point", str(ratio))
        await send_message(chat_id, f"{em('check')} تم ضبط التحويل على <b>{ratio} نجوم لكل نقطة</b>.")
        return True

    if command == "setproof":
        if not has_perm(user_id, "manage_settings"):
            await send_message(chat_id, "• لا تملك صلاحية تعديل الروابط.")
            return True
        value = args.strip()
        if value == "-":
            set_setting("proof_url", "")
        elif value.startswith("https://") and not any(ch.isspace() for ch in value):
            set_setting("proof_url", value[:500])
        else:
            await send_message(chat_id, "• أرسل رابطاً يبدأ بـ <code>https://</code>، أو أرسل <code>-</code> للمسح.")
            return True
        await send_message(chat_id, f"{em('check')} تم تحديث رابط قناة الإثباتات.")
        return True

    if command == "developer":
        if not has_perm(user_id, "manage_settings"):
            await send_message(chat_id, "• لا تملك صلاحية تعديل بيانات المطوّر.")
            return True
        contact = args.strip()
        if contact == "-":
            set_setting("developer_contact", "")
        elif contact.startswith("@") and VALID_USERNAME.fullmatch(contact[1:]):
            set_setting("developer_contact", contact)
        elif contact.startswith("https://") and not any(ch.isspace() for ch in contact):
            set_setting("developer_contact", contact[:500])
        else:
            await send_message(chat_id, "• أرسل اسم مستخدم يبدأ بـ @ أو رابطاً يبدأ بـ <code>https://</code>، أو أرسل <code>-</code> للمسح.")
            return True
        await send_message(chat_id, f"{em('check')} تم تحديث جهة التواصل مع المطوّر.")
        return True

    if command in ("service_allow", "service_block"):
        if not has_perm(user_id, "manage_services"):
            await send_message(chat_id, "• لا تملك صلاحية إدارة الخدمات.")
            return True
        if not parts:
            await send_message(chat_id, f"• الاستخدام: <code>/{command} رقم_الخدمة</code>")
            return True
        service_id = parts[0]
        try:
            services = await load_services()
        except SMMAPIError as exc:
            await send_message(chat_id, f"{em('warning')} تعذّر فحص الخدمات: {e(exc)}")
            return True
        service = next((s for s in services if str(s.get("service")) == service_id), None)
        if not service:
            await send_message(chat_id, "• لم أجد رقم الخدمة في API الحالي.")
            return True
        enabled = command == "service_allow"
        with db_connect() as con:
            con.execute(
                "INSERT INTO service_overrides(service_id,enabled,changed_by,changed_at) VALUES(?,?,?,?) "
                "ON CONFLICT(service_id) DO UPDATE SET enabled=excluded.enabled,changed_by=excluded.changed_by,changed_at=excluded.changed_at",
                (service_id, 1 if enabled else 0, user_id, now_ts()),
            )
            con.commit()
        await send_message(
            chat_id,
            f"{em('check')} {'أُظهرت' if enabled else 'أُخفيت'} الخدمة "
            f"<b>{e(service.get('name') or service_id)}</b>.\n"
            f"• راجع بنفسك أن الخدمة تخص Telegram قبل إظهارها للمستخدمين.",
        )
        return True

    if command == "balance":
        if not is_admin(user_id):
            await send_message(chat_id, "• هذا الأمر للمديرين فقط.")
            return True
        try:
            result = await smm({"action": "balance"})
            if not isinstance(result, dict):
                raise SMMAPIError("استجابة الرصيد غير متوقعة.")
            await send_message(
                chat_id,
                f"{em('wallet')} <b>رصيد SMM Rocket</b>\n\n"
                f"• الرصيد: <b>{e(result.get('balance', 'غير متاح'))} {e(result.get('currency', 'USD'))}</b>\n"
                f"• خدمات Telegram المطابقة: <b>{len(await telegram_services())}</b>",
            )
        except SMMAPIError as exc:
            await send_message(chat_id, f"{em('warning')} تعذّر قراءة رصيد API: {e(exc)}")
        return True

    if command == "orders":
        if not has_perm(user_id, "view_orders"):
            await send_message(chat_id, "• لا تملك صلاحية مشاهدة الطلبات.")
            return True
        await send_message(chat_id, admin_order_lines(20),
                           keyboard([button("لوحة الإدارة", "admin", icon="shield")]))
        return True

    if command == "feedback":
        await show_admin_feedback(chat_id, user_id)
        return True

    if command in ("help", "adminhelp"):
        if is_admin(user_id):
            await show_admin_help(chat_id, user_id)
        else:
            await send_message(chat_id, "• استخدم /start لعرض الخدمات والرصيد ووسائل التواصل.")
        return True

    return False


async def finish_panel_admin_action(
    message: dict[str, Any],
    command: str,
    args: str,
    section: str,
) -> None:
    user_id = int(message["from"]["id"])
    chat_id = int(message["chat"]["id"])
    clear_state(user_id)
    await handle_admin_command(message, command, args)
    if section == "users":
        await show_user_management(chat_id, user_id)
    elif section == "settings":
        await show_admin_settings(chat_id, user_id)
    elif section == "services":
        await show_service_management(chat_id, user_id)
    else:
        await send_message(
            chat_id,
            "يمكنك متابعة إدارة المديرين من الأزرار التالية.",
            keyboard(
                [button("قائمة المديرين", "admins", style="primary", icon="shield")],
                [button("لوحة الإدارة", "admin", icon="telegram")],
            ),
        )


async def continue_panel_input(
    message: dict[str, Any],
    state: tuple[str, dict[str, Any]],
) -> None:
    user_id = int(message["from"]["id"])
    chat_id = int(message["chat"]["id"])
    step, data = state
    text = str(message.get("text") or "").strip()

    owner_only_steps = {"panel_admin_add_id"}
    permission_for_step = {
        "panel_ban_user_id": "ban_users",
        "panel_ban_reason": "ban_users",
        "panel_unban_user_id": "ban_users",
        "panel_credit_user_id": "manage_balance",
        "panel_credit_amount": "manage_balance",
        "panel_points": "manage_settings",
        "panel_stars": "manage_settings",
        "panel_proof": "manage_settings",
        "panel_developer": "manage_settings",
        "panel_channel_add": "manage_settings",
        "panel_service_id": "manage_services",
    }
    if (step in owner_only_steps and not is_owner(user_id)) or (
        step in permission_for_step and not has_perm(user_id, permission_for_step[step])
    ):
        clear_state(user_id)
        await send_message(chat_id, "• لم تعد تملك صلاحية تنفيذ هذا الإجراء.")
        return
    if not text:
        await send_message(chat_id, "• أرسل قيمة صحيحة للمتابعة، أو ألغِ الخطوة من الزر.")
        return

    if step == "panel_channel_add":
        try:
            title, channel_id = await add_required_channel(text, user_id)
        except (ValueError, TelegramAPIError) as exc:
            await send_message(
                chat_id,
                f"{em('warning')} لم أتمكن من إضافة القناة.\n• {e(exc)}\n"
                "• تأكد من إضافة البوت مشرفاً، ثم أعد إرسال بيانات القناة.",
                cancel_keyboard(),
            )
            return
        clear_state(user_id)
        await send_message(
            chat_id,
            f"{em('check')} تمت إضافة القناة <b>{e(title)}</b> للاشتراك الإجباري.\n"
            f"• المعرّف: <code>{e(channel_id)}</code>",
        )
        await show_mandatory_channel_management(chat_id, user_id)
        return

    if step in ("panel_admin_add_id", "panel_ban_user_id", "panel_unban_user_id",
                "panel_credit_user_id"):
        target = parse_panel_user_id(text)
        if target is None:
            await send_message(chat_id, "• أرسل معرّف مستخدم صحيحاً بالأرقام فقط.")
            return
        if step == "panel_admin_add_id":
            await finish_panel_admin_action(message, "admin_add", str(target), "admins")
        elif step == "panel_ban_user_id":
            save_state(user_id, "panel_ban_reason", {"target": target})
            await send_message(
                chat_id,
                "• أرسل سبب الحظر، أو أرسل <code>-</code> للمتابعة دون سبب.",
                cancel_keyboard(),
            )
        elif step == "panel_unban_user_id":
            await finish_panel_admin_action(message, "unban", str(target), "users")
        else:
            save_state(user_id, "panel_credit_amount", {"target": target})
            await send_message(chat_id, "• أرسل عدد النقاط المراد إضافتها.", cancel_keyboard())
        return

    if step == "panel_ban_reason":
        target = parse_panel_user_id(str(data.get("target", "")))
        if target is None:
            clear_state(user_id)
            await send_message(chat_id, "• انتهت صلاحية الخطوة. ابدأ من لوحة إدارة المستخدمين.")
            return
        reason = "" if text == "-" else text[:300]
        await finish_panel_admin_action(message, "ban", f"{target} {reason}".strip(), "users")
        return

    if step == "panel_credit_amount":
        amount = d(text.replace(",", ""), Decimal("-1"))
        if not amount.is_finite() or amount <= ZERO or amount > Decimal("1000000000"):
            await send_message(chat_id, "• أدخل عدداً موجباً لا يتجاوز مليار نقطة.")
            return
        target = parse_panel_user_id(str(data.get("target", "")))
        if target is None:
            clear_state(user_id)
            await send_message(chat_id, "• انتهت صلاحية الخطوة. ابدأ من لوحة إدارة المستخدمين.")
            return
        await finish_panel_admin_action(message, "credit", f"{target} {amount}", "users")
        return

    if step == "panel_points":
        rate = d(text.replace(",", ""), ZERO)
        if not rate.is_finite() or rate <= ZERO or rate > Decimal("1000000"):
            await send_message(chat_id, "• أدخل قيمة أكبر من صفر ولا تتجاوز مليون نقطة لكل دولار.")
            return
        await finish_panel_admin_action(message, "points", str(rate), "settings")
        return

    if step == "panel_stars":
        ratio = parse_positive_int(text, 1000)
        if ratio is None:
            await send_message(chat_id, "• أدخل عدداً صحيحاً من 1 إلى 1000 نجمة.")
            return
        await finish_panel_admin_action(message, "starsrate", str(ratio), "settings")
        return

    if step == "panel_proof":
        if text != "-" and (
            not text.startswith("https://") or any(ch.isspace() for ch in text)
        ):
            await send_message(chat_id, "• أرسل رابطاً يبدأ بـ <code>https://</code>، أو أرسل <code>-</code> لمسح الرابط.")
            return
        await finish_panel_admin_action(message, "setproof", text, "settings")
        return

    if step == "panel_developer":
        valid_username = text.startswith("@") and bool(VALID_USERNAME.fullmatch(text[1:]))
        valid_url = text.startswith("https://") and not any(ch.isspace() for ch in text)
        if text != "-" and not (valid_username or valid_url):
            await send_message(
                chat_id,
                "• أرسل اسم مستخدم يبدأ بـ @ أو رابطاً يبدأ بـ <code>https://</code>، أو أرسل <code>-</code> لمسح البيانات.",
            )
            return
        await finish_panel_admin_action(message, "developer", text, "settings")
        return

    if step == "panel_service_id":
        if not text.isdecimal():
            await send_message(chat_id, "• أرسل رقم الخدمة بالأرقام فقط.")
            return
        command = str(data.get("command", ""))
        if command not in ("service_allow", "service_block"):
            clear_state(user_id)
            await send_message(chat_id, "• انتهت صلاحية الخطوة. ابدأ من لوحة إدارة الخدمات.")
            return
        await finish_panel_admin_action(message, command, text, "services")
        return

    clear_state(user_id)
    await send_message(chat_id, "• انتهت صلاحية الخطوة. افتح لوحة الإدارة وابدأ من جديد.")


async def handle_message(message: dict[str, Any]) -> None:
    user = message.get("from") or {}
    chat = message.get("chat") or {}
    if not user.get("id") or not chat.get("id"):
        return
    user_id = int(user["id"])
    chat_id = int(chat["id"])
    if not is_private_chat(chat):
        return
    is_first_start = ensure_user(user, mark_started=True)
    if is_first_start:
        await notify_new_user(user)

    if message.get("successful_payment"):
        await handle_successful_payment(message)
        return

    text = str(message.get("text") or "").strip()
    if text.startswith("/"):
        command_text, _, args = text.partition(" ")
        command = command_text.split("@", 1)[0][1:].casefold()
        args = args.strip()
        if command == "start":
            log.info("Received /start command.")
            if is_banned(user_id):
                await send_message(chat_id, f"{em('lock')} لا يمكنك استخدام البوت حالياً.")
                return
            referral_match = re.fullmatch(r"ref_([1-9]\d{0,19})", args)
            if referral_match:
                referrer_id = parse_panel_user_id(referral_match.group(1))
                if referrer_id is not None:
                    record_pending_referral(user_id, referrer_id)
            clear_state(user_id)
            if await require_user_access(user, chat_id, force_check=True):
                await show_home(chat_id, user_id)
                log.info("Sent /start menu.")
            return
        if command == "cancel":
            clear_state(user_id)
            await send_message(chat_id, "• أُلغيت الخطوة الحالية.", keyboard([button("الرئيسية", "home", icon="telegram")]))
            return
        if is_banned(user_id):
            await send_message(chat_id, f"{em('lock')} لا يمكنك استخدام البوت حالياً.")
            return
        if not await require_user_access(user, chat_id):
            return
        if await handle_admin_command(message, command, args):
            return
        await send_message(chat_id, "• لم أتعرف على الأمر. استخدم /start لعرض القائمة.")
        return

    if is_banned(user_id):
        await send_message(chat_id, f"{em('lock')} لا يمكنك استخدام البوت حالياً.")
        return
    if not await require_user_access(user, chat_id):
        return
    state = read_state(user_id)
    if state:
        if state[0].startswith("panel_"):
            await continue_panel_input(message, state)
        elif state[0] == "complaint":
            await save_complaint(message)
        elif state[0] == "review":
            await send_message(chat_id, "• راجع الطلب واضغط زر التأكيد أو الإلغاء أسفل ملخصه.")
        elif state[0] in ("drip_choice", "sub_delay", "drip_interval"):
            await send_message(chat_id, "• اختر أحد الأزرار الظاهرة لإكمال هذه الخطوة.")
        else:
            await continue_order_input(message, state)
        return
    await send_message(chat_id, "• استخدم /start لعرض القائمة الرئيسية.")


async def handle_callback(callback: dict[str, Any]) -> None:
    message = callback.get("message")
    if not isinstance(message, dict) or not is_private_chat(message.get("chat")):
        return
    user = callback.get("from") or {}
    if not user.get("id"):
        return
    user_id = int(user["id"])
    is_first_start = ensure_user(user, mark_started=True)
    if is_first_start:
        await notify_new_user(user)
    callback_id = str(callback.get("id", ""))
    data = str(callback.get("data") or "")
    chat_id = int(message["chat"]["id"])

    if is_banned(user_id):
        await answer_callback(callback_id, "لا يمكنك استخدام البوت حالياً.", True)
        return

    slow_actions = (
        data in (
            "services", "services_refresh", "panelservices_refresh", "panelstatus",
            "check_subscriptions",
        )
        or data.startswith(("order:", "status:", "refill:", "cancelorder:", "stars:"))
    )
    await answer_callback(callback_id, "جارٍ التنفيذ..." if slow_actions else "")

    if data == "check_subscriptions":
        if await require_user_access(
            user, chat_id, callback=callback, force_check=True
        ):
            await show_home(chat_id, user_id, callback)
        return
    if not await require_user_access(user, chat_id, callback=callback):
        return

    if data.startswith("rate:"):
        try:
            rating = int(data.split(":", 1)[1])
        except ValueError:
            rating = 0
        if rating not in range(1, 6):
            await send_message(chat_id, "• اختر تقييماً من 1 إلى 5.")
            return
        await save_rating(user, rating)
        await edit_message(
            callback,
            f"{em('heart')} شكراً لوقتك ومشاركتك رأيك.",
            keyboard([button("الرئيسية", "home", icon="telegram")]),
        )
        return

    if data == "home":
        clear_state(user_id)
        await show_home(chat_id, user_id, callback)
        return
    if data == "referrals":
        await show_referrals(chat_id, user_id, callback)
        return
    if data == "services":
        if is_admin(user_id) and not has_perm(user_id, "use_services"):
            await edit_message(callback, "• لا تملك صلاحية استخدام الخدمات. اطلب من المالك تفعيلها.")
            return
        await show_services(chat_id, callback)
        return
    if data == "services_refresh":
        try:
            await load_services(force=True)
        except SMMAPIError as exc:
            await edit_message(callback, f"{em('warning')} تعذّرت المزامنة: {e(exc)}")
            return
        await show_services(chat_id, callback)
        return
    if data == "panelservices_refresh":
        if not has_perm(user_id, "manage_services"):
            await edit_message(callback, "• لا تملك صلاحية إدارة الخدمات.")
            return
        try:
            await load_services(force=True)
        except SMMAPIError as exc:
            await edit_message(callback, f"{em('warning')} تعذّرت المزامنة: {e(exc)}")
            return
        await show_service_management(chat_id, user_id, callback)
        return
    if data.startswith("catpage:"):
        try:
            _, cat_idx, page = data.split(":", 2)
            await show_category_page(chat_id, callback, int(cat_idx), int(page))
        except (ValueError, SMMAPIError) as exc:
            await edit_message(callback, f"{em('warning')} تعذّر فتح القائمة: {e(exc)}")
        return
    if data.startswith("cat:"):
        try:
            await show_category(chat_id, callback, int(data.split(":", 1)[1]))
        except (ValueError, SMMAPIError) as exc:
            await edit_message(callback, f"{em('warning')} تعذّر فتح التصنيف: {e(exc)}")
        return
    if data.startswith("svc:"):
        await show_service_detail(chat_id, callback, data.split(":", 1)[1])
        return
    if data.startswith("begin:"):
        if is_admin(user_id) and not has_perm(user_id, "use_services"):
            await send_message(chat_id, "• لا تملك صلاحية استخدام الخدمات.")
            return
        sid = data.split(":", 1)[1]
        service = cached_service(sid)
        if not service or not service_is_telegram(service):
            await send_message(chat_id, "• الخدمة لم تعد متاحة. حدّث قائمة الخدمات.")
            return
        await prompt_order(chat_id, user_id, service)
        return
    if data in ("drip:no", "drip:yes"):
        state = read_state(user_id)
        if not state or state[0] != "drip_choice":
            await send_message(chat_id, "• انتهت صلاحية هذه الخطوة. ابدأ طلباً جديداً.")
            return
        draft = state[1]
        if data == "drip:yes":
            save_state(user_id, "drip_runs", draft)
            await send_message(chat_id, "• أرسل عدد الدفعات التي تريدها.", cancel_keyboard())
        else:
            draft["runs"] = 1
            await present_order_review(chat_id, user_id, draft)
        return
    if data.startswith("dripinterval:"):
        state = read_state(user_id)
        if not state or state[0] != "drip_interval":
            await send_message(chat_id, "• انتهت صلاحية هذه الخطوة. ابدأ طلباً جديداً.")
            return
        interval = int(data.split(":", 1)[1])
        if interval not in (5, 10, 15, 30, 60, 90):
            await send_message(chat_id, "• الفترة المحددة غير صالحة.")
            return
        draft = state[1]
        draft["interval"] = interval
        await present_order_review(chat_id, user_id, draft)
        return
    if data.startswith("subdelay:"):
        state = read_state(user_id)
        if not state or state[0] != "sub_delay":
            await send_message(chat_id, "• انتهت صلاحية هذه الخطوة. ابدأ طلباً جديداً.")
            return
        delay = int(data.split(":", 1)[1])
        if delay not in (0, 5, 10, 15, 30, 60, 90):
            await send_message(chat_id, "• فترة التأخير غير صالحة.")
            return
        draft = state[1]
        draft["delay"] = delay
        save_state(user_id, "sub_expiry", draft)
        await send_message(chat_id, "• أرسل تاريخ الانتهاء بصيغة <code>يوم/شهر/سنة</code>، أو أرسل <code>-</code> للتخطي.",
                           cancel_keyboard())
        return
    if data == "order:paid":
        await submit_order(user_id, chat_id, False, callback)
        return
    if data == "order:free":
        await submit_order(user_id, chat_id, True, callback)
        return
    if data == "cancel_state":
        clear_state(user_id)
        await edit_message(callback, "• أُلغيت الخطوة الحالية.", keyboard([button("الرئيسية", "home", icon="telegram")]))
        return
    if data == "wallet":
        await show_wallet(chat_id, user_id, callback)
        return
    if data.startswith("stars:"):
        try:
            await create_star_invoice(chat_id, user_id, int(data.split(":", 1)[1]))
        except ValueError:
            await send_message(chat_id, "• لم أتعرف على قيمة النجوم.")
        return
    if data == "proof":
        await show_proof(chat_id, callback)
        return
    if data == "developer":
        await show_developer(chat_id, callback)
        return
    if data == "complaint":
        await begin_complaint(chat_id, user_id)
        return
    if data == "rate":
        await show_rating(chat_id, callback)
        return
    if data == "myorders":
        await show_my_orders(chat_id, user_id, callback)
        return
    if data.startswith("orderinfo:"):
        try:
            await show_order_detail(chat_id, user_id, callback, int(data.split(":", 1)[1]))
        except ValueError:
            await send_message(chat_id, "• رقم الطلب غير صالح.")
        return
    if data.startswith("status:"):
        try:
            await refresh_order_status(chat_id, user_id, callback, int(data.split(":", 1)[1]))
        except (ValueError, SMMAPIError) as exc:
            await send_message(chat_id, f"{em('warning')} تعذّر تحديث الحالة: {e(exc)}")
        return
    if data.startswith("refill:"):
        try:
            await request_refill(chat_id, user_id, callback, int(data.split(":", 1)[1]))
        except (ValueError, SMMAPIError) as exc:
            await send_message(chat_id, f"{em('warning')} تعذّر إرسال التعويض: {e(exc)}")
        return
    if data.startswith("refillstatus:"):
        await refresh_refill_status(chat_id, user_id, data.split(":", 1)[1])
        return
    if data.startswith("cancelorder:"):
        try:
            await cancel_remote_order(chat_id, user_id, callback, int(data.split(":", 1)[1]))
        except (ValueError, SMMAPIError) as exc:
            await send_message(chat_id, f"{em('warning')} تعذّر إرسال الإلغاء: {e(exc)}")
        return
    if data == "admin":
        await show_admin_panel(chat_id, user_id, callback)
        return
    if data == "panelusers":
        await show_user_management(chat_id, user_id, callback)
        return
    if data == "panelservices":
        await show_service_management(chat_id, user_id, callback)
        return
    if data == "adminadd":
        if not is_owner(user_id):
            await edit_message(callback, "• إضافة مدير متاحة للمالك فقط.")
            return
        await begin_panel_input(
            chat_id,
            user_id,
            "panel_admin_add_id",
            "• أرسل معرّف المستخدم الذي تريد إضافته مديراً. ستختار صلاحياته بعد الإضافة.",
        )
        return
    if data in ("panelban", "panelunban", "panelcredit"):
        if data in ("panelban", "panelunban") and not has_perm(user_id, "ban_users"):
            await edit_message(callback, "• لا تملك صلاحية حظر المستخدمين.")
            return
        if data == "panelcredit" and not has_perm(user_id, "manage_balance"):
            await edit_message(callback, "• لا تملك صلاحية تعديل الأرصدة.")
            return
        steps = {
            "panelban": ("panel_ban_user_id", "• أرسل معرّف المستخدم الذي تريد حظره."),
            "panelunban": ("panel_unban_user_id", "• أرسل معرّف المستخدم الذي تريد فك الحظر عنه."),
            "panelcredit": ("panel_credit_user_id", "• أرسل معرّف المستخدم الذي تريد إضافة نقاط إلى رصيده."),
        }
        step, prompt = steps[data]
        await begin_panel_input(chat_id, user_id, step, prompt)
        return
    if data.startswith("panelsetting:"):
        setting = data.split(":", 1)[1]
        settings = {
            "points": ("panel_points", "• أرسل عدد النقاط المقابل لكل دولار أمريكي واحد."),
            "stars": ("panel_stars", "• أرسل عدد نجوم تيليجرام المطلوب مقابل كل نقطة."),
            "proof": (
                "panel_proof",
                "• أرسل رابطاً يبدأ بـ <code>https://</code> لقناة الإثباتات، أو أرسل <code>-</code> لمسح الرابط.",
            ),
            "developer": (
                "panel_developer",
                "• أرسل اسم مستخدم يبدأ بـ @ أو رابطاً يبدأ بـ <code>https://</code>، أو أرسل <code>-</code> لمسح البيانات.",
            ),
        }
        if setting not in settings:
            await edit_message(callback, "• هذا الإعداد غير معروف.")
            return
        if not has_perm(user_id, "manage_settings"):
            await edit_message(callback, "• لا تملك صلاحية تعديل الإعدادات.")
            return
        step, prompt = settings[setting]
        await begin_panel_input(chat_id, user_id, step, prompt)
        return
    if data.startswith("panelservice:"):
        action = data.split(":", 1)[1]
        commands = {"allow": "service_allow", "block": "service_block"}
        if action not in commands:
            await edit_message(callback, "• هذا الإجراء غير معروف.")
            return
        if not has_perm(user_id, "manage_services"):
            await edit_message(callback, "• لا تملك صلاحية إدارة الخدمات.")
            return
        prompt = (
            "• أرسل رقم الخدمة التي تريد إظهارها بعد مراجعتها."
            if action == "allow"
            else "• أرسل رقم الخدمة التي تريد إخفاءها."
        )
        await begin_panel_input(
            chat_id,
            user_id,
            "panel_service_id",
            prompt,
            {"command": commands[action]},
        )
        return
    if data == "admins":
        await show_admin_list(chat_id, callback)
        return
    if data.startswith("adminselect:"):
        try:
            await show_admin_permissions(chat_id, callback, int(data.split(":", 1)[1]))
        except ValueError:
            await edit_message(callback, "• معرّف المدير غير صالح.")
        return
    if data.startswith("admperm:"):
        if not is_owner(user_id):
            await send_message(chat_id, "• تعديل الصلاحيات للمالك فقط.")
            return
        try:
            _, admin_text, permission = data.split(":", 2)
            target = int(admin_text)
        except ValueError:
            await send_message(chat_id, "• بيانات الصلاحية غير صالحة.")
            return
        if is_owner(target):
            await send_message(chat_id, "• لا يمكن تعديل صلاحيات المالك من قائمة المديرين.")
            return
        if permission not in PERMISSIONS:
            await send_message(chat_id, "• الصلاحية غير معروفة.")
            return
        with db_connect() as con:
            row = con.execute("SELECT permissions FROM admins WHERE user_id=?", (target,)).fetchone()
            if not row:
                await send_message(chat_id, "• المدير غير موجود.")
                return
            try:
                current = set(json.loads(row["permissions"]))
            except (json.JSONDecodeError, TypeError):
                current = set()
            if permission in current:
                current.remove(permission)
            else:
                current.add(permission)
            con.execute(
                "UPDATE admins SET permissions=? WHERE user_id=?",
                (json.dumps(sorted(current)), target),
            )
            con.commit()
        await show_admin_permissions(chat_id, callback, target)
        return
    if data.startswith("admremove:"):
        if not is_owner(user_id):
            await send_message(chat_id, "• إزالة المدير للمالك فقط.")
            return
        try:
            target = int(data.split(":", 1)[1])
        except ValueError:
            await send_message(chat_id, "• معرّف المدير غير صالح.")
            return
        if is_owner(target):
            await send_message(chat_id, "• لا يمكن إزالة المالك من قائمة المديرين.")
            return
        with db_connect() as con:
            con.execute("DELETE FROM admins WHERE user_id=?", (target,))
            con.commit()
        await show_admin_list(chat_id, callback)
        return
    if data == "adminorders":
        if not has_perm(user_id, "view_orders"):
            await send_message(chat_id, "• لا تملك صلاحية مشاهدة الطلبات.")
            return
        await edit_message(callback, admin_order_lines(15),
                           keyboard([button("لوحة الإدارة", "admin", icon="shield")]))
        return
    if data == "adminfeedback":
        if not has_perm(user_id, "view_feedback"):
            await send_message(chat_id, "• لا تملك صلاحية مشاهدة الملاحظات.")
            return
        await show_admin_feedback(chat_id, user_id)
        return
    if data == "adminsettings":
        await show_admin_settings(chat_id, user_id, callback)
        return
    if data == "mandatorychannels":
        await show_mandatory_channel_management(chat_id, user_id, callback)
        return
    if data == "mandatory_add":
        if not has_perm(user_id, "manage_settings"):
            await edit_message(callback, "• لا تملك صلاحية إدارة قنوات الاشتراك الإجباري.")
            return
        await begin_panel_input(
            chat_id,
            user_id,
            "panel_channel_add",
            "• أرسل @username للقناة العامة، أو معرّفاً مثل -1001234567890 ورابط الدعوة للقناة الخاصة.\n"
            "• أضف البوت مشرفاً في القناة أولاً.",
        )
        return
    if data.startswith("mandatory_remove:"):
        if not has_perm(user_id, "manage_settings"):
            await edit_message(callback, "• لا تملك صلاحية إدارة قنوات الاشتراك الإجباري.")
            return
        try:
            channel_row_id = int(data.split(":", 1)[1])
        except ValueError:
            await send_message(chat_id, "• معرّف القناة غير صالح.")
            return
        if not remove_required_channel(channel_row_id):
            await send_message(chat_id, "• القناة غير موجودة أو حُذفت مسبقاً.")
        await show_mandatory_channel_management(chat_id, user_id, callback)
        return
    if data == "panelstatus":
        await show_panel_status(chat_id, user_id)
        return
    if data == "adminhelp":
        await show_admin_help(chat_id, user_id, callback)
        return

    await send_message(chat_id, "• انتهت صلاحية هذا الزر. استخدم /start لفتح القائمة من جديد.")


async def handle_update(update: dict[str, Any]) -> None:
    message = update.get("message")
    if message and not is_private_chat(message.get("chat")):
        return
    callback = update.get("callback_query")
    if callback:
        callback_message = callback.get("message")
        if (
            not isinstance(callback_message, dict)
            or not is_private_chat(callback_message.get("chat"))
        ):
            return
    try:
        if message:
            await handle_message(message)
        elif callback:
            await handle_callback(callback)
        elif update.get("pre_checkout_query"):
            await handle_pre_checkout(update["pre_checkout_query"])
    except TelegramAPIError as exc:
        log.info("Telegram request failed while handling an update: %s", str(exc)[:200])
    except Exception as exc:
        log.exception("Unexpected update handler error (%s)", type(exc).__name__)


async def verify_startup() -> str:
    global BOT_USERNAME, BOT_ID
    missing = []
    if not BOT_TOKEN:
        missing.append("TELEGRAM_BOT_TOKEN")
    if not SMM_API_KEY:
        missing.append("SMMROCKET_API_KEY")
    if OWNER_ID <= 0:
        missing.append("OWNER_TELEGRAM_ID")
    if missing:
        raise RuntimeError(
            "أضف القيم التالية في Replit Secrets قبل التشغيل: " + ", ".join(missing)
        )
    me = await tg("getMe", {})
    BOT_USERNAME = str(me.get("username") or "")
    BOT_ID = int(me.get("id") or 0)
    balance = await smm({"action": "balance"})
    if not isinstance(balance, dict) or balance.get("balance") is None:
        raise SMMAPIError("لم تُرجع API رصيد الحساب؛ راجع مفتاح SMM Rocket.")
    services = await load_services(force=True)
    count = len(await telegram_services())
    await prime_custom_emojis()
    await tg("deleteWebhook", {"drop_pending_updates": False})
    await tg(
        "setMyCommands",
        {
            "commands": [
                {"command": "start", "description": "القائمة الرئيسية"},
                {"command": "cancel", "description": "إلغاء الخطوة الحالية"},
                {"command": "help", "description": "المساعدة"},
            ]
        },
    )
    log.info("Bot @%s connected; SMM Rocket API connected.", BOT_USERNAME or "unknown")
    log.info("Loaded %d services, %d matched Telegram.", len(services), count)
    if count == 0:
        log.warning(
            "No Telegram services matched. Owner can review service IDs and use /service_allow ID."
        )
    return BOT_USERNAME


async def polling_loop() -> None:
    offset = 0
    backoff = 2
    while True:
        try:
            updates = await tg(
                "getUpdates",
                {
                    "offset": offset,
                    "timeout": POLL_TIMEOUT,
                    "allowed_updates": ["message", "callback_query", "pre_checkout_query"],
                },
            )
            backoff = 2
            if not isinstance(updates, list):
                await asyncio.sleep(1)
                continue
            for update in updates:
                offset = max(offset, int(update.get("update_id", 0)) + 1)
                update_type = next(
                    (key for key in ("message", "callback_query", "pre_checkout_query") if key in update),
                    "unknown",
                )
                log.info("Received Telegram update (%s).", update_type)
                await handle_update(update)
        except TelegramAPIError as exc:
            log.error("Polling error: %s", str(exc)[:200])
            await asyncio.sleep(backoff)
            backoff = min(backoff * 2, 30)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            log.exception("Polling loop error (%s)", type(exc).__name__)
            await asyncio.sleep(backoff)
            backoff = min(backoff * 2, 30)


async def main() -> None:
    BOT_READY.clear()
    BOT_FAILED.clear()
    init_db()
    try:
        load_co_owners()
        await verify_startup()
        BOT_READY.set()
        await polling_loop()
    except KeyboardInterrupt:
        log.info("Bot stopped.")
    except (RuntimeError, TelegramAPIError, SMMAPIError) as exc:
        log.error("%s", str(exc))
        BOT_FAILED.set()
        raise


def run_bot_worker() -> None:
    try:
        asyncio.run(main())
    except Exception:
        BOT_READY.clear()
        BOT_FAILED.set()
        log.exception("Telegram bot worker stopped unexpectedly.")


def run_server() -> None:
    raw_port = os.getenv("PORT", "5000")
    try:
        port = int(raw_port)
    except ValueError as exc:
        raise RuntimeError("PORT must be a valid integer.") from exc
    if not 1 <= port <= 65535:
        raise RuntimeError("PORT must be between 1 and 65535.")

    BOT_READY.clear()
    BOT_FAILED.clear()
    worker = threading.Thread(
        target=run_bot_worker,
        name="telegram-bot-polling",
        daemon=True,
    )
    worker.start()
    log.info("Starting Flask health server on 0.0.0.0:%d.", port)
    serve(app, host="0.0.0.0", port=port, threads=4)


if __name__ == "__main__":
    try:
        run_server()
    except KeyboardInterrupt:
        log.info("Web server stopped.")
    except Exception as exc:
        log.exception("Could not start the bot web server: %s", str(exc))
        sys.exit(1)
