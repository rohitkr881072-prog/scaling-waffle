"""
ExamYatra — single-file Telegram study bot.
Run: python bot-2.py

Environment:
  BOT_TOKEN (required)
  ADMIN_IDS=123456,789012
  DATABASE_URL=sqlite+aiosqlite:///./examyatra.db
  GEMINI_API_KEY=... (optional; enables AI tutor, image-question solving and AI test generation)
  GEMINI_MODEL=gemini-2.5-flash
  MAINTENANCE_MODE=false
  MAINTENANCE_MESSAGE=ExamYatra is being updated. Please try again soon.
  SUPPORT_CONTACT=@your_support
  FREE_AI_DAILY_LIMIT=10
  LOG_LEVEL=INFO (optional)
  PORT=10000 (set by the host; health-check server)

Upgrade notes (v2):
  * Centralised Telegram HTML formatter — Gemini Markdown is never shown raw.
  * Persistent Answer Style (Short / Detailed) stored in users.answer_style
    (added through a migration-safe ALTER TABLE, existing rows default to "short").
  * New AI Test Generator (🧪) with persistent sessions (ai_tests / ai_test_questions),
    one-question-at-a-time MCQ interface, result card, answer review and 📜 Test History.
  * New admin feature toggle: /feature aitest on|off
"""
from __future__ import annotations

import asyncio
import base64
import html
import json
import logging
import os
import random
import re
import time
from datetime import datetime, timedelta, timezone
from typing import Any, Awaitable, Callable

import httpx
from aiohttp import web
from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.exceptions import TelegramBadRequest, TelegramForbiddenError, TelegramUnauthorizedError
from aiogram.filters import Command, CommandStart, StateFilter
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.types import (
    BotCommand, CallbackQuery, InlineKeyboardButton, InlineKeyboardMarkup,
    KeyboardButton, Message, ReplyKeyboardMarkup
)
from dotenv import load_dotenv
from sqlalchemy import (
    BigInteger, Boolean, DateTime, Float, ForeignKey, Integer, String, Text,
    UniqueConstraint, select, func, delete, update, inspect as sa_inspect, text as sa_text
)
from sqlalchemy.exc import IntegrityError
from sqlalchemy.ext.asyncio import (
    AsyncAttrs, AsyncSession, async_sessionmaker, create_async_engine
)
from sqlalchemy.orm import DeclarativeBase, Mapped, mapped_column, relationship

load_dotenv()
logging.basicConfig(
    level=getattr(logging, os.getenv("LOG_LEVEL", "INFO").upper(), logging.INFO),
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
)
log = logging.getLogger("examyatra")

BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
DATABASE_URL = os.getenv("DATABASE_URL", "sqlite+aiosqlite:///./examyatra.db").strip()
ADMIN_IDS = {int(x.strip()) for x in os.getenv("ADMIN_IDS", "").split(",") if x.strip().isdigit()}
GEMINI_API_KEY = os.getenv("GEMINI_API_KEY", "").strip()
GEMINI_MODEL = os.getenv("GEMINI_MODEL", "gemini-2.5-flash").strip()
MAINTENANCE_MODE = os.getenv("MAINTENANCE_MODE", "false").lower() in {"1", "true", "yes", "on"}
MAINTENANCE_MESSAGE = os.getenv(
    "MAINTENANCE_MESSAGE", "ExamYatra is being updated. Please try again soon."
).strip()
SUPPORT_CONTACT = os.getenv("SUPPORT_CONTACT", "").strip()
FREE_AI_DAILY_LIMIT = max(1, int(os.getenv("FREE_AI_DAILY_LIMIT", "10")))
MAX_IMAGE_BYTES = 8 * 1024 * 1024
LETTERS = "ABCD"

# Telegram hard limit is 4096 characters; keep a margin for re-opened HTML tags when splitting.
TG_TEXT_LIMIT = 3800
# Answer styles
STYLE_SHORT, STYLE_DETAILED = "short", "detailed"
ANSWER_STYLES = (STYLE_SHORT, STYLE_DETAILED)
# AI test generation limits
AI_TEST_MIN, AI_TEST_MAX = 1, 50
AI_TEST_BATCH = 10            # questions requested per Gemini call
AI_TEST_MAX_CALLS = 14        # hard cap of Gemini calls for one logical test request
AI_TEST_HISTORY_PAGE = 8
AI_TEST_REVIEW_PAGE = 5
AI_TEST_DIFFICULTIES = ("easy", "medium", "hard", "mixed")
COMMON_TEST_TOPICS = [
    "BPSC", "Bihar Police", "SSC", "Railway", "Banking", "UPSC",
    "General Knowledge", "Indian History", "Geography", "Science",
    "Mathematics", "Reasoning", "Current Affairs",
]

class Base(AsyncAttrs, DeclarativeBase):
    pass

def now_utc() -> datetime:
    return datetime.now(timezone.utc).replace(tzinfo=None)

class User(Base):
    __tablename__ = "users"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    telegram_id: Mapped[int] = mapped_column(BigInteger, unique=True, index=True)
    username: Mapped[str | None] = mapped_column(String(64), nullable=True)
    full_name: Mapped[str] = mapped_column(String(160), default="Student")
    joined_at: Mapped[datetime] = mapped_column(DateTime, default=now_utc)
    last_active_at: Mapped[datetime] = mapped_column(DateTime, default=now_utc)
    selected_exam_id: Mapped[int | None] = mapped_column(ForeignKey("exams.id", ondelete="SET NULL"), nullable=True)
    status: Mapped[str] = mapped_column(String(16), default="active")
    access_granted: Mapped[bool] = mapped_column(Boolean, default=True)
    is_admin: Mapped[bool] = mapped_column(Boolean, default=False)
    language: Mapped[str] = mapped_column(String(2), default="en")
    ai_date: Mapped[str] = mapped_column(String(10), default="")
    ai_count: Mapped[int] = mapped_column(Integer, default=0)
    # New in v2 — added to existing databases by ensure_schema() (ALTER TABLE), default "short".
    answer_style: Mapped[str] = mapped_column(String(16), default=STYLE_SHORT, server_default=STYLE_SHORT)

class Exam(Base):
    __tablename__ = "exams"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    name: Mapped[str] = mapped_column(String(100), unique=True)
    active: Mapped[bool] = mapped_column(Boolean, default=True)

class Subject(Base):
    __tablename__ = "subjects"
    __table_args__ = (UniqueConstraint("exam_id", "name"),)
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    exam_id: Mapped[int] = mapped_column(ForeignKey("exams.id", ondelete="CASCADE"), index=True)
    name: Mapped[str] = mapped_column(String(100))

class Question(Base):
    __tablename__ = "questions"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    exam_id: Mapped[int] = mapped_column(ForeignKey("exams.id", ondelete="CASCADE"), index=True)
    subject_id: Mapped[int | None] = mapped_column(ForeignKey("subjects.id", ondelete="SET NULL"), nullable=True)
    text: Mapped[str] = mapped_column(Text)
    explanation: Mapped[str | None] = mapped_column(Text, nullable=True)
    difficulty: Mapped[str] = mapped_column(String(16), default="medium")
    published: Mapped[bool] = mapped_column(Boolean, default=True)
    options: Mapped[list["Option"]] = relationship(
        back_populates="question", cascade="all, delete-orphan", lazy="selectin",
        order_by="Option.position"
    )

class Option(Base):
    __tablename__ = "options"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    question_id: Mapped[int] = mapped_column(ForeignKey("questions.id", ondelete="CASCADE"), index=True)
    position: Mapped[int] = mapped_column(Integer, default=0)
    text: Mapped[str] = mapped_column(Text)
    correct: Mapped[bool] = mapped_column(Boolean, default=False)
    question: Mapped[Question] = relationship(back_populates="options")

class Practice(Base):
    __tablename__ = "practice_attempts"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), index=True)
    question_id: Mapped[int] = mapped_column(ForeignKey("questions.id", ondelete="CASCADE"))
    option_order: Mapped[str] = mapped_column(String(200))
    answered_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    selected_option_id: Mapped[int | None] = mapped_column(Integer, nullable=True)
    is_correct: Mapped[bool | None] = mapped_column(Boolean, nullable=True)
    served_at: Mapped[datetime] = mapped_column(DateTime, default=now_utc)

class Material(Base):
    __tablename__ = "materials"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    exam_id: Mapped[int | None] = mapped_column(ForeignKey("exams.id", ondelete="SET NULL"), nullable=True)
    title: Mapped[str] = mapped_column(String(200))
    url: Mapped[str | None] = mapped_column(String(1000), nullable=True)
    description: Mapped[str | None] = mapped_column(Text, nullable=True)
    published: Mapped[bool] = mapped_column(Boolean, default=True)

class MockTest(Base):
    __tablename__ = "mock_tests"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    exam_id: Mapped[int] = mapped_column(ForeignKey("exams.id", ondelete="CASCADE"))
    title: Mapped[str] = mapped_column(String(160))
    duration: Mapped[int] = mapped_column(Integer, default=20)
    published: Mapped[bool] = mapped_column(Boolean, default=True)

class MockQuestion(Base):
    __tablename__ = "mock_questions"
    __table_args__ = (UniqueConstraint("test_id", "question_id"),)
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    test_id: Mapped[int] = mapped_column(ForeignKey("mock_tests.id", ondelete="CASCADE"), index=True)
    question_id: Mapped[int] = mapped_column(ForeignKey("questions.id", ondelete="CASCADE"))
    position: Mapped[int] = mapped_column(Integer, default=0)

class MockAttempt(Base):
    __tablename__ = "mock_attempts"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), index=True)
    test_id: Mapped[int] = mapped_column(ForeignKey("mock_tests.id", ondelete="CASCADE"))
    started_at: Mapped[datetime] = mapped_column(DateTime, default=now_utc)
    deadline_at: Mapped[datetime] = mapped_column(DateTime)
    status: Mapped[str] = mapped_column(String(16), default="in_progress")
    question_ids: Mapped[str] = mapped_column(Text, default="[]")
    answers_json: Mapped[str] = mapped_column(Text, default="{}")
    score: Mapped[float] = mapped_column(Float, default=0)
    correct: Mapped[int] = mapped_column(Integer, default=0)
    incorrect: Mapped[int] = mapped_column(Integer, default=0)
    unanswered: Mapped[int] = mapped_column(Integer, default=0)

class Setting(Base):
    __tablename__ = "settings"
    key: Mapped[str] = mapped_column(String(80), primary_key=True)
    value: Mapped[str] = mapped_column(Text, default="")

# ----- New in v2: AI-generated test sessions (separate from admin MockTest tables) -----
class AiTest(Base):
    """One AI-generated practice test owned by a single user. Questions are stored as
    immutable snapshots in AiTestQuestion so later changes cannot alter a finished score."""
    __tablename__ = "ai_tests"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), index=True)
    topic: Mapped[str] = mapped_column(String(200))
    requested_count: Mapped[int] = mapped_column(Integer)
    question_count: Mapped[int] = mapped_column(Integer, default=0)
    language: Mapped[str] = mapped_column(String(2), default="en")
    difficulty: Mapped[str] = mapped_column(String(16), default="mixed")
    status: Mapped[str] = mapped_column(String(16), default="in_progress", index=True)  # in_progress|completed|abandoned
    current_index: Mapped[int] = mapped_column(Integer, default=0)
    correct: Mapped[int] = mapped_column(Integer, default=0)
    incorrect: Mapped[int] = mapped_column(Integer, default=0)
    unanswered: Mapped[int] = mapped_column(Integer, default=0)
    score: Mapped[float] = mapped_column(Float, default=0.0)
    accuracy: Mapped[float] = mapped_column(Float, default=0.0)
    created_at: Mapped[datetime] = mapped_column(DateTime, default=now_utc)
    started_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    completed_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)

class AiTestQuestion(Base):
    __tablename__ = "ai_test_questions"
    __table_args__ = (UniqueConstraint("test_id", "position"),)
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    test_id: Mapped[int] = mapped_column(ForeignKey("ai_tests.id", ondelete="CASCADE"), index=True)
    position: Mapped[int] = mapped_column(Integer)
    text: Mapped[str] = mapped_column(Text)
    options_json: Mapped[str] = mapped_column(Text)          # JSON list of exactly 4 strings
    correct_index: Mapped[int] = mapped_column(Integer)      # 0..3
    explanation: Mapped[str | None] = mapped_column(Text, nullable=True)
    difficulty: Mapped[str] = mapped_column(String(16), default="medium")
    selected_index: Mapped[int | None] = mapped_column(Integer, nullable=True)  # student's answer, None = unanswered
    answered_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)

    def options(self) -> list[str]:
        try:
            opts = json.loads(self.options_json)
            return [str(o) for o in opts] if isinstance(opts, list) else []
        except (TypeError, ValueError):
            return []

engine = create_async_engine(DATABASE_URL, pool_pre_ping=True)
Session = async_sessionmaker(engine, expire_on_commit=False)
router = Router()
dp = Dispatcher()
dp.include_router(router)

class AdminFlow(StatesGroup):
    add_exam = State()
    add_question = State()
    broadcast = State()
    material = State()
    mock_test = State()
    api_key = State()
    maintenance_message = State()

class TestFlow(StatesGroup):
    """AI Test Generator setup flow. Topic / count / difficulty live in FSM data, never in callback data."""
    topic = State()
    custom_topic = State()
    count = State()
    custom_count = State()
    difficulty = State()
    generating = State()

# ---- Schema migration (safe for existing SQLite/Postgres databases; never drops anything) ----
# (table, column, DDL fragment appended after "ADD COLUMN <name>")
SCHEMA_ADDITIONS: list[tuple[str, str, str]] = [
    ("users", "answer_style", "VARCHAR(16) NOT NULL DEFAULT 'short'"),
]

async def ensure_schema() -> None:
    """create_all() only creates missing TABLES. Missing COLUMNS on existing tables are added here."""
    async with engine.begin() as conn:
        await conn.run_sync(Base.metadata.create_all)
        def _columns(sync_conn, table: str) -> set[str]:
            return {c["name"] for c in sa_inspect(sync_conn).get_columns(table)}
        for table, column, ddl in SCHEMA_ADDITIONS:
            existing = await conn.run_sync(_columns, table)
            if column not in existing:
                log.info("Migrating: adding column %s.%s", table, column)
                await conn.execute(sa_text(f"ALTER TABLE {table} ADD COLUMN {column} {ddl}"))

def esc(value: Any) -> str:
    return html.escape(str(value or ""))

def is_admin_id(tg_id: int) -> bool:
    return tg_id in ADMIN_IDS

MENU_BUTTONS = {
    "🎯 Select Exam", "❓ Daily Quiz", "🧠 Ask AI Tutor", "📷 Solve Image",
    "🧪 Generate AI Test", "📜 Test History",
    "📝 Mock Tests", "📚 Study Materials", "📊 My Performance", "🏆 Leaderboard",
    "👤 My Profile", "⚙️ Settings", "❔ Help", "🛠 Admin Panel",
}

def main_keyboard(is_admin: bool = False) -> ReplyKeyboardMarkup:
    rows = [
        [KeyboardButton(text="🎯 Select Exam"), KeyboardButton(text="❓ Daily Quiz")],
        [KeyboardButton(text="🧠 Ask AI Tutor"), KeyboardButton(text="📷 Solve Image")],
        [KeyboardButton(text="🧪 Generate AI Test"), KeyboardButton(text="📜 Test History")],
        [KeyboardButton(text="📝 Mock Tests"), KeyboardButton(text="📚 Study Materials")],
        [KeyboardButton(text="📊 My Performance"), KeyboardButton(text="🏆 Leaderboard")],
        [KeyboardButton(text="👤 My Profile"), KeyboardButton(text="⚙️ Settings")],
        [KeyboardButton(text="❔ Help")]
    ]
    if is_admin:
        rows.append([KeyboardButton(text="🛠 Admin Panel")])
    return ReplyKeyboardMarkup(keyboard=rows, resize_keyboard=True, is_persistent=True)

def inline(rows: list[list[tuple[str, str]]]) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=t, callback_data=d) for t, d in row] for row in rows
    ])

async def get_user(session: AsyncSession, tg_user) -> User:
    """Fetch or create a user safely, including simultaneous /start updates."""
    user = (await session.execute(
        select(User).where(User.telegram_id == tg_user.id)
    )).scalar_one_or_none()
    if user is None:
        candidate = User(
            telegram_id=tg_user.id,
            username=tg_user.username,
            full_name=(tg_user.full_name or tg_user.username or "Student")[:160],
            is_admin=is_admin_id(tg_user.id),
            access_granted=True,
            answer_style=STYLE_SHORT,
        )
        session.add(candidate)
        try:
            await session.flush()
            user = candidate
        except IntegrityError:
            # Another simultaneous update may have inserted this Telegram ID.
            # Roll back the failed INSERT and fetch the row that now exists.
            await session.rollback()
            user = (await session.execute(
                select(User).where(User.telegram_id == tg_user.id)
            )).scalar_one_or_none()
            if user is None:
                # Do not hide an unrelated integrity failure.
                raise
    user.username = tg_user.username
    user.full_name = (tg_user.full_name or tg_user.username or "Student")[:160]
    user.last_active_at = now_utc()
    user.is_admin = user.is_admin or is_admin_id(tg_user.id)
    if user.answer_style not in ANSWER_STYLES:
        user.answer_style = STYLE_SHORT
    if user.ai_date != now_utc().date().isoformat():
        user.ai_date = now_utc().date().isoformat()
        user.ai_count = 0
    return user

async def get_setting(session: AsyncSession, key: str, default: str = "") -> str:
    row = await session.get(Setting, key)
    return row.value if row else default

async def set_setting(session: AsyncSession, key: str, value: str) -> None:
    row = await session.get(Setting, key)
    if row:
        row.value = value
    else:
        session.add(Setting(key=key, value=value))

async def feature_enabled(session: AsyncSession, name: str) -> bool:
    return (await get_setting(session, "feature_" + name, "true")).lower() == "true"

FEATURE_NAMES = ("ai", "quiz", "mock", "materials", "aitest")

async def gate(message: Message, user: User, session: AsyncSession) -> bool:
    if user.status == "banned":
        await message.answer("⛔ Your account is blocked. Contact support if you think this is a mistake.")
        return False
    maintenance = (await get_setting(session, "maintenance", str(MAINTENANCE_MODE).lower())).lower() == "true"
    if maintenance and not user.is_admin:
        note = await get_setting(session, "maintenance_message", MAINTENANCE_MESSAGE)
        await message.answer(f"🛠 {esc(note)}")
        return False
    if not user.access_granted and not user.is_admin:
        await message.answer("🔒 Your bot access is currently disabled. Contact the administrator.")
        return False
    return True

async def current_api_key(session: AsyncSession) -> str:
    # Prefer a non-empty key configured through the admin panel; otherwise use Render Environment.
    saved = (await get_setting(session, "gemini_api_key", "")).strip()
    return saved or GEMINI_API_KEY


async def validate_gemini_key(api_key: str) -> tuple[bool, str]:
    """Make a minimal live Gemini request so invalid keys are not saved."""
    if not api_key or len(api_key) < 10:
        return False, "The key looks empty or too short."
    url = f"https://generativelanguage.googleapis.com/v1beta/models/{GEMINI_MODEL}:generateContent"
    payload = {"contents": [{"role": "user", "parts": [{"text": "Reply with the single word OK."}]}],
               "generationConfig": {"temperature": 0, "maxOutputTokens": 5}}
    try:
        async with httpx.AsyncClient(timeout=httpx.Timeout(20.0)) as client:
            response = await client.post(url, params={"key": api_key}, json=payload)
        if response.status_code == 200:
            return True, "Key validated successfully."
        if response.status_code in (400, 401, 403):
            return False, "Google rejected this key or the API is not enabled. Check the key and Gemini API access."
        if response.status_code == 404:
            return False, f"Model '{GEMINI_MODEL}' was not found. Check GEMINI_MODEL in Render Environment."
        if response.status_code == 429:
            return False, "The key reached a quota/rate limit. Try again later or check your Google AI Studio quota."
        return False, f"Google returned HTTP {response.status_code}. Please check the key and try again."
    except httpx.TimeoutException:
        return False, "Validation timed out. Please try again."
    except httpx.HTTPError:
        log.exception("Gemini key validation request failed")
        return False, "Could not reach Google AI. Check the service/network and try again."


# ============================ Gemini client (single low-level call) ============================
class AIError(Exception):
    """Typed AI failure. `code` is one of AI_ERROR_TEXT's keys; never carries secrets."""
    def __init__(self, code: str, detail: str = ""):
        super().__init__(code)
        self.code = code
        self.detail = detail

AI_ERROR_TEXT = {
    "no_key": ("AI features are not configured yet. Ask the admin to open Admin Panel → Gemini API key "
               "and add a valid key. The other bot features can still work."),
    "auth": "AI service authentication failed. Please ask the admin to check GEMINI_API_KEY.",
    "rate_limit": "The AI service is busy or its quota is exhausted. Please try again in a minute.",
    "timeout": "The AI service took too long to respond. Please try again.",
    "network": "Could not reach the AI service. Please try again later.",
    "http": "AI service error. Please try again later.",
    "empty": "I couldn't generate an answer. Please try again.",
    "parse": "I couldn't read the AI response. Please try again.",
}

TUTOR_SYSTEM = (
    "You are ExamYatra, a careful and encouraging tutor for competitive-exam students in India. "
    "Read the question carefully, explain step by step in simple language, state assumptions, "
    "show formulas/calculations when useful, and finish with the final answer. If an image is unclear, "
    "say what cannot be read rather than guessing. Reply in the language used by the student when possible."
)

async def gemini_call(parts: list[dict[str, Any]], api_key: str, *, system: str = TUTOR_SYSTEM,
                      generation_config: dict[str, Any] | None = None, timeout: float = 55.0) -> str:
    """Single Gemini generateContent request. Returns the concatenated text or raises AIError."""
    api_key = (api_key or "").strip()
    if not api_key:
        raise AIError("no_key")
    url = f"https://generativelanguage.googleapis.com/v1beta/models/{GEMINI_MODEL}:generateContent"
    payload: dict[str, Any] = {
        "contents": [{"role": "user", "parts": parts}],
        "generationConfig": generation_config or {"temperature": 0.25, "maxOutputTokens": 2048},
        "systemInstruction": {"parts": [{"text": system}]},
    }
    try:
        async with httpx.AsyncClient(timeout=httpx.Timeout(timeout)) as client:
            response = await client.post(url, params={"key": api_key}, json=payload)
    except httpx.TimeoutException:
        raise AIError("timeout")
    except httpx.HTTPError as e:
        log.warning("Gemini network error: %s", type(e).__name__)
        raise AIError("network")
    if response.status_code >= 400:
        # Never log the key; the URL params are not included in this message.
        log.warning("Gemini API returned %s: %s", response.status_code, response.text[:300])
        if response.status_code in (401, 403):
            raise AIError("auth")
        if response.status_code == 429:
            raise AIError("rate_limit")
        raise AIError("http", str(response.status_code))
    try:
        data = response.json()
        text = "\n".join(p.get("text", "") for p in data["candidates"][0]["content"]["parts"] if p.get("text")).strip()
    except (KeyError, IndexError, TypeError, ValueError):
        raise AIError("parse")
    if not text:
        raise AIError("empty")
    return text

def _image_part(image_bytes: bytes, mime_type: str) -> dict[str, Any]:
    return {"inline_data": {"mime_type": mime_type, "data": base64.b64encode(image_bytes).decode("ascii")}}

async def ai_generate(prompt: str, image_bytes: bytes | None = None, mime_type: str = "image/jpeg",
                      api_key: str | None = None) -> str:
    """Backwards-compatible free-text generation. Errors are returned as friendly text."""
    parts: list[dict[str, Any]] = [{"text": prompt}]
    if image_bytes:
        parts.append(_image_part(image_bytes, mime_type))
    try:
        return await gemini_call(parts, api_key or GEMINI_API_KEY)
    except AIError as e:
        return AI_ERROR_TEXT.get(e.code, AI_ERROR_TEXT["http"])

def parse_json_loose(raw: str) -> Any:
    """Parse model JSON, tolerating ``` fences and leading/trailing prose. Returns None on failure."""
    if not raw:
        return None
    text = raw.strip()
    text = re.sub(r"^```(?:json)?\s*", "", text, flags=re.I)
    text = re.sub(r"\s*```$", "", text)
    try:
        return json.loads(text)
    except ValueError:
        pass
    starts = [i for i in (text.find("{"), text.find("[")) if i >= 0]
    if not starts:
        return None
    start = min(starts)
    end = max(text.rfind("}"), text.rfind("]"))
    if end <= start:
        return None
    try:
        return json.loads(text[start:end + 1])
    except ValueError:
        return None

async def ai_generate_json(prompt: str, schema: dict[str, Any], api_key: str, *,
                           image_bytes: bytes | None = None, mime_type: str = "image/jpeg",
                           system: str = TUTOR_SYSTEM, temperature: float = 0.3,
                           max_tokens: int = 2048, timeout: float = 60.0) -> tuple[Any, str | None]:
    """Structured generation. Returns (parsed_json, None) or (None, error_code)."""
    parts: list[dict[str, Any]] = [{"text": prompt}]
    if image_bytes:
        parts.append(_image_part(image_bytes, mime_type))
    config = {"temperature": temperature, "maxOutputTokens": max_tokens,
              "responseMimeType": "application/json", "responseSchema": schema}
    try:
        raw = await gemini_call(parts, api_key, system=system, generation_config=config, timeout=timeout)
    except AIError as e:
        return None, e.code
    data = parse_json_loose(raw)
    if data is None:
        return None, "parse"
    return data, None


# ============================ Centralised Telegram formatter ============================
_TG_TAGS = ("b", "i", "u", "s", "code", "pre")
_TAG_RE = re.compile(r"<(/?)(b|i|u|s|code|pre)>")

def md_to_html(text: str) -> str:
    """Convert the Markdown Gemini usually produces into Telegram-safe HTML.
    All text is HTML-escaped first; only an allowlist of tags is emitted."""
    text = (text or "").replace("\r\n", "\n").strip()
    blocks: list[str] = []
    text = re.sub(r"```[a-zA-Z0-9_+-]*\n?(.*?)```", lambda m: _block_store(blocks, m.group(1)), text, flags=re.S)
    text = html.escape(text, quote=False)
    # inline code
    text = re.sub(r"`([^`\n]+)`", r"<code>\1</code>", text)
    # bold / italic
    text = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", text, flags=re.S)
    text = re.sub(r"(?<![\w_])__(.+?)__(?![\w_])", r"<b>\1</b>", text, flags=re.S)
    text = re.sub(r"(?<![\w*])\*(?!\s)([^*\n]+?)(?<!\s)\*(?![\w*])", r"<i>\1</i>", text)
    text = re.sub(r"(?<![\w_])_(?!\s)([^_\n]+?)(?<!\s)_(?![\w_])", r"<i>\1</i>", text)
    # headings -> bold line
    text = re.sub(r"^[ \t]{0,3}#{1,6}[ \t]*(.+?)[ \t]*#*[ \t]*$", r"<b>\1</b>", text, flags=re.M)
    text = re.sub(r"<b>\s*<b>(.+?)</b>\s*</b>", r"<b>\1</b>", text, flags=re.S)
    # bullet lists and horizontal rules
    text = re.sub(r"^[ \t]*[-*•][ \t]+", "• ", text, flags=re.M)
    text = re.sub(r"^[ \t]*([-*_])\1{2,}[ \t]*$", "", text, flags=re.M)
    # leftover markers that would otherwise show up raw
    text = re.sub(r"^[ \t]*#{1,6}[ \t]*", "", text, flags=re.M)
    text = text.replace("**", "")
    text = re.sub(r"\n{3,}", "\n\n", text)
    text = re.sub(r"\x00(\d+)\x00", lambda m: blocks[int(m.group(1))], text)
    return text.strip()

def _block_store(blocks: list[str], code: str) -> str:
    blocks.append(f"<pre>{html.escape(code.strip(), quote=False)}</pre>")
    return f"\x00{len(blocks) - 1}\x00"

def html_to_plain(text: str) -> str:
    return html.unescape(re.sub(r"<[^>]+>", "", text or ""))

def clean_plain(text: Any) -> str:
    """Model text -> plain text with no Markdown or HTML markers (for wrapping in our own tags)."""
    return html_to_plain(md_to_html(str(text or ""))).strip()

def split_html(text: str, limit: int = TG_TEXT_LIMIT) -> list[str]:
    """Split HTML text into Telegram-sized chunks without leaving tags open across a boundary."""
    if len(text) <= limit:
        return [text]
    chunks: list[str] = []
    open_tags: list[str] = []
    while text:
        if len(text) <= limit:
            piece, text = text, ""
        else:
            cut = text.rfind("\n\n", 0, limit)
            if cut < limit // 2:
                cut = text.rfind("\n", 0, limit)
            if cut < limit // 2:
                cut = text.rfind(" ", 0, limit)
            if cut < limit // 2:
                cut = limit
            # never cut inside a tag
            lt, gt = text.rfind("<", 0, cut), text.rfind(">", 0, cut)
            if lt > gt:
                cut = lt
            piece, text = text[:cut], text[cut:].lstrip("\n")
        prefix = "".join(f"<{t}>" for t in open_tags)
        for m in _TAG_RE.finditer(piece):
            closing, name = m.group(1), m.group(2)
            if closing:
                if name in open_tags:
                    open_tags.reverse(); open_tags.remove(name); open_tags.reverse()
            else:
                open_tags.append(name)
        suffix = "".join(f"</{t}>" for t in reversed(open_tags))
        chunks.append(prefix + piece + suffix)
    return [c for c in chunks if c.strip()]

async def send_html(message: Message, text: str, reply_markup: InlineKeyboardMarkup | None = None) -> None:
    """Send possibly-long HTML safely. Falls back to plain text if Telegram rejects the markup."""
    chunks = split_html(text or "No response.")
    for i, chunk in enumerate(chunks):
        markup = reply_markup if i == len(chunks) - 1 else None
        try:
            await message.answer(chunk, reply_markup=markup)
        except TelegramBadRequest:
            await message.answer(html_to_plain(chunk), parse_mode=None, reply_markup=markup)

async def safe_edit(message: Message, text: str, reply_markup: InlineKeyboardMarkup | None = None) -> bool:
    """Edit a message; tolerate 'not modified' and fall back to a new message when editing is impossible."""
    try:
        await message.edit_text(text, reply_markup=reply_markup)
        return True
    except TelegramBadRequest as e:
        if "message is not modified" in str(e):
            return True
        try:
            await message.answer(text, reply_markup=reply_markup)
        except TelegramBadRequest:
            await message.answer(html_to_plain(text), parse_mode=None, reply_markup=reply_markup)
        return False

async def answer_long(message: Message, text: str) -> None:
    """Kept for compatibility: formats Markdown-ish text to HTML and sends it safely."""
    await send_html(message, md_to_html(text or "No response."))

def has_devanagari(text: str) -> bool:
    return bool(re.search(r"[\u0900-\u097F]", text or ""))


# ============================ Structured AI answers (Short / Detailed) ============================
ANSWER_SCHEMA = {
    "type": "OBJECT",
    "properties": {
        "question": {"type": "STRING", "description": "The student's question, restated briefly (one line)."},
        "answer": {"type": "STRING", "description": "The direct final answer only, plain text."},
        "explanation": {"type": "STRING", "description": "Short plain-text explanation."},
        "steps": {"type": "ARRAY", "items": {"type": "STRING"}, "description": "Ordered solution steps, plain text."},
    },
    "required": ["answer"],
}

def answer_language(user: User, question_text: str) -> str:
    if user.language == "hi" or has_devanagari(question_text or ""):
        return "hi"
    return "en"

def build_answer_prompt(question_text: str, style: str, lang: str, *, with_image: bool, caption: str = "") -> str:
    lang_name = "Hindi (Devanagari script)" if lang == "hi" else "English"
    if with_image:
        base = ("The attached image contains a student's exam question (possibly with MCQ choices). "
                "Read it carefully and solve it. If the image is unreadable, say so in 'answer'.")
        if caption:
            base += f"\nStudent instructions: {caption[:400]}"
    else:
        base = f"Student question:\n{question_text[:3000]}"
    if style == STYLE_SHORT:
        guide = ("Return ONLY the direct answer in 'answer' (a value, name, option letter + text, or one short sentence; "
                 "max 25 words). Put at most one short sentence in 'explanation'. Leave 'steps' empty. "
                 "Do not add history, background or alternatives.")
    else:
        guide = ("Fill 'question' with a one-line restatement, 'answer' with the direct final answer (max 30 words), "
                 "'steps' with 2-6 short, simple, numbered-worthy steps (each one or two sentences, include formulas or "
                 "an example where relevant), and 'explanation' with one or two sentences of the key concept. "
                 "No introductions, no repeated conclusions.")
    return (f"{base}\n\nAnswer in {lang_name}. Use plain text in every field — no Markdown, no asterisks, no '#' headings, "
            f"no HTML.\n{guide}")

def render_structured_answer(data: dict[str, Any], style: str, lang: str) -> str:
    """Render the parsed JSON answer into Telegram HTML according to the user's style."""
    answer = clean_plain(data.get("answer"))
    explanation = clean_plain(data.get("explanation"))
    question = clean_plain(data.get("question"))
    steps_raw = data.get("steps") if isinstance(data.get("steps"), list) else []
    steps = [clean_plain(s) for s in steps_raw if clean_plain(s)]
    if style == STYLE_SHORT:
        text = f"✅ <b>{esc(answer)}</b>"
        # For complex questions keep one supporting line so the answer still makes sense.
        if explanation and len(answer) < 60 and len(explanation) <= 220 and explanation.lower() != answer.lower():
            text += f"\n\n{esc(explanation)}"
        return text
    q_label, a_label, e_label = (("प्रश्न", "अंतिम उत्तर", "व्याख्या") if lang == "hi"
                                 else ("Question", "Final Answer", "Explanation"))
    parts: list[str] = []
    if question:
        parts.append(f"📘 <b>{q_label}:</b> {esc(question)}")
    parts.append(f"✅ <b>{a_label}:</b> {esc(answer)}")
    body: list[str] = []
    if steps:
        body.append("\n".join(f"{i}. {esc(s)}" for i, s in enumerate(steps, 1)))
    if explanation:
        body.append(esc(explanation))
    if body:
        parts.append(f"<b>{e_label}:</b>\n" + "\n\n".join(body))
    return "\n\n".join(parts)

def render_fallback_answer(raw_text: str, style: str, lang: str) -> str:
    """Used when structured parsing fails: never show raw Markdown."""
    formatted = md_to_html(raw_text)
    if style == STYLE_SHORT:
        # Prefer a line that looks like a final answer; otherwise the last short paragraph.
        plain = html_to_plain(formatted)
        m = re.search(r"(?:final answer|answer|उत्तर)\s*[:：\-]\s*(.+)", plain, re.I)
        if m and m.group(1).strip():
            return f"✅ <b>{esc(m.group(1).strip()[:300])}</b>"
        paragraphs = [p.strip() for p in plain.split("\n\n") if p.strip()]
        if paragraphs:
            return f"✅ <b>{esc(paragraphs[-1][:300])}</b>"
    return formatted

async def check_ai_limit(message: Message, user: User) -> bool:
    if user.is_admin:
        return True
    if user.ai_count >= FREE_AI_DAILY_LIMIT:
        await message.answer(f"Daily AI limit reached ({FREE_AI_DAILY_LIMIT} requests). Try again tomorrow.")
        return False
    user.ai_count += 1
    return True

async def answer_student_question(message: Message, session: AsyncSession, user: User, question_text: str = "",
                                  image_bytes: bytes | None = None, mime_type: str = "image/jpeg",
                                  caption: str = "") -> None:
    """Shared path for AI Tutor, plain text doubts and image questions. One logical request = one AI charge."""
    style = user.answer_style if user.answer_style in ANSWER_STYLES else STYLE_SHORT
    lang = answer_language(user, question_text or caption)
    api_key = await current_api_key(session)
    # Commit the pending user update (AI counter, last_active) before the slow network call so the
    # database is not left in an open write transaction while Gemini responds.
    await session.commit()
    prompt = build_answer_prompt(question_text, style, lang, with_image=bool(image_bytes), caption=caption)
    data, err = await ai_generate_json(prompt, ANSWER_SCHEMA, api_key, image_bytes=image_bytes, mime_type=mime_type,
                                       temperature=0.2, max_tokens=2048)
    if isinstance(data, dict) and clean_plain(data.get("answer")):
        await send_html(message, render_structured_answer(data, style, lang))
        return
    if err in ("no_key", "auth", "rate_limit", "timeout", "network", "http"):
        await message.answer(esc(AI_ERROR_TEXT[err]))
        return
    # Structured output failed to parse: fall back to free text and format it ourselves.
    parts: list[dict[str, Any]] = [{"text": prompt + "\nIf you cannot produce JSON, answer in plain text."}]
    if image_bytes:
        parts.append(_image_part(image_bytes, mime_type))
    try:
        raw = await gemini_call(parts, api_key)
    except AIError as e:
        await message.answer(esc(AI_ERROR_TEXT.get(e.code, AI_ERROR_TEXT["http"])))
        return
    await send_html(message, render_fallback_answer(raw, style, lang))

# ============================ Settings (interactive) ============================
def settings_keyboard(user: User) -> InlineKeyboardMarkup:
    def mark(selected: bool) -> str:
        return " ✅" if selected else ""
    return inline([
        [("⚡ Short Answer" + mark(user.answer_style == STYLE_SHORT), "set:style:short")],
        [("📘 Detailed Answer" + mark(user.answer_style == STYLE_DETAILED), "set:style:detailed")],
        [("🇬🇧 English" + mark(user.language == "en"), "set:lang:en"),
         ("🇮🇳 हिन्दी" + mark(user.language == "hi"), "set:lang:hi")],
        [("🗑 Delete my account", "set:delete")],
        [("🏠 Main Menu", "menu:home")],
    ])

def settings_text(user: User) -> str:
    style = "⚡ Short Answer" if user.answer_style == STYLE_SHORT else "📘 Detailed Answer"
    lang = "English" if user.language == "en" else "हिन्दी"
    return (
        "⚙️ <b>Settings</b>\n\n"
        f"<b>Answer Style:</b> {style}\n"
        "• Short Answer — only the direct answer, highlighted.\n"
        "• Detailed Answer — answer first, then step-by-step explanation.\n\n"
        f"<b>Language:</b> {lang}\n\n"
        "Tap an option to change it. Commands /language en|hi and /delete_me still work."
    )

async def show_settings(message: Message, user: User) -> None:
    await message.answer(settings_text(user), reply_markup=settings_keyboard(user))

@router.callback_query(F.data.startswith("set:"))
async def settings_callback(cb: CallbackQuery, session: AsyncSession, db_user: User):
    parts = cb.data.split(":")
    action = parts[1] if len(parts) > 1 else ""
    if action == "style" and len(parts) == 3 and parts[2] in ANSWER_STYLES:
        db_user.answer_style = parts[2]
        await session.flush()
        label = "⚡ Short Answer" if parts[2] == STYLE_SHORT else "📘 Detailed Answer"
        await cb.answer(f"Saved: {label}")
        await safe_edit(cb.message, settings_text(db_user), settings_keyboard(db_user))
        return
    if action == "lang" and len(parts) == 3 and parts[2] in ("en", "hi"):
        db_user.language = parts[2]
        await session.flush()
        await cb.answer("Language saved")
        await safe_edit(cb.message, settings_text(db_user), settings_keyboard(db_user))
        return
    if action == "delete":
        await cb.answer()
        await safe_edit(cb.message, "⚠️ This permanently deletes your profile and activity. Confirm?",
                        inline([[("🗑 Yes, delete my data", "delete:confirm"), ("Cancel", "delete:cancel")]]))
        return
    await cb.answer("Unknown setting.", show_alert=True)

@router.callback_query(F.data == "menu:home")
async def menu_home(cb: CallbackQuery, db_user: User, state: FSMContext):
    await cb.answer()
    await state.clear()
    await cb.message.answer("📚 ExamYatra main menu", reply_markup=main_keyboard(db_user.is_admin))

async def show_exams(message: Message, session: AsyncSession) -> None:
    exams = list((await session.execute(select(Exam).where(Exam.active.is_(True)).order_by(Exam.name))).scalars())
    if not exams:
        await message.answer("No exam categories have been added yet. Please check back soon.")
        return
    await message.answer("🎯 Choose your target exam:", reply_markup=inline([
        [(e.name, f"exam:{e.id}") for e in exams[i:i+2]] for i in range(0, len(exams), 2)
    ]))

async def send_quiz(message: Message, session: AsyncSession, user: User, subject_id: int | None = None) -> None:
    if not user.selected_exam_id:
        await message.answer("Choose your exam first.", reply_markup=main_keyboard(user.is_admin))
        await show_exams(message, session)
        return
    stmt = select(Question).where(Question.exam_id == user.selected_exam_id, Question.published.is_(True))
    if subject_id:
        stmt = stmt.where(Question.subject_id == subject_id)
    questions = list((await session.execute(stmt)).scalars().all())
    valid = []
    for q in questions:
        await session.refresh(q, attribute_names=["options"])
        if len(q.options) >= 2 and sum(o.correct for o in q.options) == 1:
            valid.append(q)
    if not valid:
        await message.answer("No published questions are available for this exam yet. Ask the admin to add questions.")
        return
    answered = set((await session.execute(
        select(Practice.question_id).where(Practice.user_id == user.id, Practice.answered_at.is_not(None))
    )).scalars())
    fresh = [q for q in valid if q.id not in answered]
    q = random.choice(fresh or valid)
    options = q.options[:]
    random.shuffle(options)
    attempt = Practice(user_id=user.id, question_id=q.id, option_order=",".join(str(o.id) for o in options))
    session.add(attempt)
    await session.flush()
    prompt = f"❓ <b>Daily Practice</b>\n\n{esc(q.text)}"
    prompt += "\n\n" + "\n".join(f"{LETTERS[i] if i < 4 else str(i+1)}) {esc(o.text)}" for i, o in enumerate(options))
    markup = inline([[ (f"{LETTERS[i] if i < 4 else str(i+1)}", f"qa:{attempt.id}:{i}") for i in range(len(options)) ]])
    await message.answer(prompt, reply_markup=markup)

@router.message(CommandStart())
async def start(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    if not await gate(message, db_user, session): return
    await state.clear()
    await message.answer(
        f"👋 Welcome to <b>ExamYatra</b>, {esc(db_user.full_name)}!\n"
        "Prepare • Practice • Progress\n\n"
        "Choose a tool below. You can also send a question photo or type a doubt directly.",
        reply_markup=main_keyboard(db_user.is_admin),
    )
    if not db_user.selected_exam_id:
        await show_exams(message, session)

@router.message(Command("menu"))
async def menu(message: Message, db_user: User, state: FSMContext):
    await state.clear()
    await message.answer("📚 ExamYatra main menu", reply_markup=main_keyboard(db_user.is_admin))

@router.message(Command("help"))
@router.message(F.text == "❔ Help")
async def help_cmd(message: Message):
    support = f"\nSupport: {esc(SUPPORT_CONTACT)}" if SUPPORT_CONTACT else ""
    await message.answer(
        "📌 <b>ExamYatra Help</b>\n"
        "• Select Exam: choose SSC, Railway, Banking, or another exam.\n"
        "• Daily Quiz: practise MCQs and see explanations.\n"
        "• Ask AI Tutor: type any study question.\n"
        "• Solve Image: send a photo/screenshot of a question.\n"
        "• Generate AI Test: create an MCQ test on any exam or topic (1–50 questions).\n"
        "• Test History: review your past AI tests and answers.\n"
        "• Mock Tests: take timed tests created by the admin.\n"
        "• Study Materials: open shared notes and resources.\n"
        "• Performance: view your practice accuracy.\n"
        "• Settings: choose Short or Detailed answers and your language.\n"
        "Commands: /start, /menu, /help, /profile, /cancel" + support
    )

@router.message(F.text == "🎯 Select Exam")
async def select_exam(message: Message, session: AsyncSession, db_user: User):
    await show_exams(message, session)

@router.callback_query(F.data.startswith("exam:"))
async def exam_callback(cb: CallbackQuery, session: AsyncSession, db_user: User):
    try: exam_id = int(cb.data.split(":")[1])
    except (ValueError, IndexError):
        await cb.answer("Invalid exam.", show_alert=True); return
    exam = await session.get(Exam, exam_id)
    if not exam or not exam.active:
        await cb.answer("This exam is not available.", show_alert=True); return
    db_user.selected_exam_id = exam.id
    await cb.answer("Exam saved")
    await safe_edit(cb.message, f"✅ Your selected exam is <b>{esc(exam.name)}</b>.\nNow try Daily Quiz, Mock Tests or Generate AI Test.")

@router.message(F.text == "❓ Daily Quiz")
async def quiz_menu(message: Message, session: AsyncSession, db_user: User):
    if not await gate(message, db_user, session): return
    if not await feature_enabled(session, "quiz"):
        await message.answer("Daily Quiz is temporarily disabled by the administrator."); return
    await send_quiz(message, session, db_user)

@router.callback_query(F.data.startswith("qa:"))
async def quiz_answer(cb: CallbackQuery, session: AsyncSession, db_user: User):
    try: _, aid, pos = cb.data.split(":"); aid, pos = int(aid), int(pos)
    except Exception:
        await cb.answer("Invalid answer button.", show_alert=True); return
    attempt = await session.get(Practice, aid)
    if not attempt or attempt.user_id != db_user.id:
        await cb.answer("Question not found.", show_alert=True); return
    if attempt.answered_at:
        await cb.answer("You have already answered this question.", show_alert=True); return
    if now_utc() - attempt.served_at > timedelta(minutes=10):
        await cb.answer("This question expired. Start another quiz.", show_alert=True); return
    ids = [int(x) for x in attempt.option_order.split(",") if x]
    if not 0 <= pos < len(ids):
        await cb.answer("Invalid option.", show_alert=True); return
    q = await session.get(Question, attempt.question_id)
    await session.refresh(q, attribute_names=["options"])
    chosen = next((o for o in q.options if o.id == ids[pos]), None)
    correct = next((o for o in q.options if o.correct), None)
    if not chosen or not correct:
        await cb.answer("Question data is incomplete.", show_alert=True); return
    attempt.answered_at = now_utc()
    attempt.selected_option_id = chosen.id
    attempt.is_correct = chosen.id == correct.id
    await session.flush()
    lines = [("✅ " if o.id == correct.id else ("❌ " if o.id == chosen.id else "▫️ ")) + esc(o.text) for o in sorted(q.options, key=lambda x:x.position)]
    text = ("✅ <b>Correct!</b>" if attempt.is_correct else "❌ <b>Not quite.</b>")
    text += f"\n\n{esc(q.text)}\n\n" + "\n".join(lines)
    if q.explanation: text += f"\n\n💡 <b>Explanation:</b>\n{esc(q.explanation)}"
    await cb.answer("Correct!" if attempt.is_correct else "Incorrect")
    await safe_edit(cb.message, text, inline([[("➡️ Next question", "quiz:next")]]))

@router.callback_query(F.data == "quiz:next")
async def quiz_next(cb: CallbackQuery, session: AsyncSession, db_user: User):
    await cb.answer()
    await send_quiz(cb.message, session, db_user)

@router.message(F.text == "🧠 Ask AI Tutor")
async def ai_tutor_start(message: Message, state: FSMContext, session: AsyncSession, db_user: User):
    if not await gate(message, db_user, session): return
    if not await feature_enabled(session, "ai"):
        await message.answer("AI tools are temporarily disabled by the administrator."); return
    await state.set_state("ai_tutor")
    style = "short" if db_user.answer_style == STYLE_SHORT else "detailed"
    await message.answer(f"🧠 Send your question as text. Answer style: <b>{style}</b> (change in ⚙️ Settings). Send /cancel to stop.")

@router.message(F.text == "📷 Solve Image")
async def image_help(message: Message, session: AsyncSession, db_user: User):
    if not await gate(message, db_user, session): return
    if not await feature_enabled(session, "ai"):
        await message.answer("AI tools are temporarily disabled by the administrator."); return
    await message.answer("📷 Send a clear photo/screenshot of the question here. I'll read it and solve it. You can also add a caption such as 'solve in Hindi'.")

@router.message(F.photo)
async def photo_question(message: Message, bot: Bot, session: AsyncSession, db_user: User):
    if not await gate(message, db_user, session): return
    if not await feature_enabled(session, "ai"):
        await message.answer("AI tools are temporarily disabled by the administrator."); return
    if not await check_ai_limit(message, db_user): return
    photo = message.photo[-1]
    file = await bot.get_file(photo.file_id)
    if file.file_size and file.file_size > MAX_IMAGE_BYTES:
        await message.answer("This image is too large. Please send a compressed image under 8 MB.")
        return
    stream = await bot.download_file(file.file_path)
    image_bytes = stream.read()
    await message.answer("🔎 Reading the image and solving the question…")
    await answer_student_question(message, session, db_user, image_bytes=image_bytes, mime_type="image/jpeg",
                                  caption=message.caption or "")

@router.message(F.document)
async def document_question(message: Message, bot: Bot, session: AsyncSession, db_user: User):
    if not await feature_enabled(session, "ai"):
        return
    doc = message.document
    if not doc or not (doc.mime_type or "").startswith("image/"):
        return
    if not await gate(message, db_user, session): return
    if not await check_ai_limit(message, db_user): return
    if doc.file_size and doc.file_size > MAX_IMAGE_BYTES:
        await message.answer("This image is too large. Please send a file under 8 MB.")
        return
    f = await bot.get_file(doc.file_id)
    stream = await bot.download_file(f.file_path)
    await message.answer("🔎 Reading the image and solving the question…")
    await answer_student_question(message, session, db_user, image_bytes=stream.read(),
                                  mime_type=doc.mime_type or "image/jpeg", caption=message.caption or "")

@router.message(F.text == "/cancel")
@router.message(Command("cancel"))
async def cancel(message: Message, state: FSMContext, db_user: User):
    await state.clear()
    await message.answer("Cancelled.", reply_markup=main_keyboard(db_user.is_admin))

# Reply-keyboard buttons pressed while the user is inside ANY state: leave the state and act on the button.
@router.message(F.text.in_(MENU_BUTTONS), ~StateFilter(None))
async def menu_button_in_state(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    if await state.get_state() == TestFlow.generating.state:
        await message.answer("⏳ Your test is still being generated. Please wait a moment."); return
    await state.clear()
    if not await gate(message, db_user, session): return
    if not await dispatch_menu(message, session, db_user, state):
        await message.answer("📚 ExamYatra main menu", reply_markup=main_keyboard(db_user.is_admin))

# AI Tutor state: the question typed after "🧠 Ask AI Tutor" (fixes the unreachable StateFilter(None) branch).
@router.message(StateFilter("ai_tutor"), F.text, ~F.text.startswith("/"))
async def ai_tutor_question(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    text = (message.text or "").strip()
    if not text: return
    if not await gate(message, db_user, session): return
    if not await feature_enabled(session, "ai"):
        await state.clear()
        await message.answer("AI tools are temporarily disabled by the administrator."); return
    if not await check_ai_limit(message, db_user): return
    await state.clear()
    await message.answer("🧠 Thinking…")
    await answer_student_question(message, session, db_user, question_text=text)

async def dispatch_menu(message: Message, session: AsyncSession, db_user: User, state: FSMContext) -> bool:
    """Handle reply-keyboard buttons that are not bound to a dedicated handler. Returns True if handled."""
    text = (message.text or "").strip()
    if text == "📝 Mock Tests":
        if not await feature_enabled(session, "mock"):
            await message.answer("Mock Tests are temporarily disabled by the administrator."); return True
        await list_mock_tests(message, session, db_user); return True
    if text == "📚 Study Materials":
        if not await feature_enabled(session, "materials"):
            await message.answer("Study Materials are temporarily disabled by the administrator."); return True
        await list_materials(message, session, db_user); return True
    if text == "📊 My Performance":
        await performance(message, session, db_user); return True
    if text == "🏆 Leaderboard":
        await leaderboard(message, session); return True
    if text in ("👤 My Profile", "/profile"):
        await profile(message, session, db_user); return True
    if text == "⚙️ Settings":
        await show_settings(message, db_user); return True
    if text == "🧪 Generate AI Test":
        await start_test_setup(message, session, db_user, state); return True
    if text == "📜 Test History":
        await show_test_history(message, session, db_user, page=0); return True
    if text == "🎯 Select Exam":
        await show_exams(message, session); return True
    if text == "❓ Daily Quiz":
        await quiz_menu(message, session, db_user); return True
    if text == "🧠 Ask AI Tutor":
        await ai_tutor_start(message, state, session, db_user); return True
    if text == "📷 Solve Image":
        await image_help(message, session, db_user); return True
    if text == "❔ Help":
        await help_cmd(message); return True
    if text == "🛠 Admin Panel":
        await admin_panel(message, db_user); return True
    return False

@router.message(F.text, StateFilter(None), ~F.text.startswith("/"))
async def text_router(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    text = (message.text or "").strip()
    if not text or text.startswith("/"): return
    if not await gate(message, db_user, session): return
    if await dispatch_menu(message, session, db_user, state):
        return
    # Any normal text is treated as a study doubt, so a student can simply type a question.
    if not await feature_enabled(session, "ai"):
        await message.answer("AI tools are temporarily disabled by the administrator."); return
    if not await check_ai_limit(message, db_user): return
    await message.answer("🧠 I'll treat that as a study question…")
    await answer_student_question(message, session, db_user, question_text=text)


# ============================ AI Test Generator — question generation service ============================
TEST_SCHEMA = {
    "type": "ARRAY",
    "items": {
        "type": "OBJECT",
        "properties": {
            "question": {"type": "STRING"},
            "options": {"type": "ARRAY", "items": {"type": "STRING"}},
            "correct_index": {"type": "INTEGER"},
            "explanation": {"type": "STRING"},
            "difficulty": {"type": "STRING"},
        },
        "required": ["question", "options", "correct_index", "explanation"],
    },
}
TEST_SYSTEM = ("You are an expert question setter for Indian competitive examinations. You write accurate, "
               "unambiguous multiple-choice questions with exactly four options and exactly one correct answer. "
               "You output only JSON that matches the requested schema.")

def normalize_question_text(text: str) -> str:
    return re.sub(r"[^\w\u0900-\u097F]+", "", (text or "").lower())

def validate_generated_question(item: Any, seen: set[str]) -> dict[str, Any] | None:
    """Return a clean question dict or None. `seen` holds normalised texts already accepted."""
    if not isinstance(item, dict):
        return None
    text = clean_plain(item.get("question"))
    if not text or len(text) < 5 or len(text) > 900:
        return None
    raw_opts = item.get("options")
    if not isinstance(raw_opts, list) or len(raw_opts) != 4:
        return None
    options = [clean_plain(o)[:300] for o in raw_opts]
    if any(not o for o in options):
        return None
    if len({o.casefold() for o in options}) != 4:
        return None
    ci = item.get("correct_index")
    if isinstance(ci, str) and ci.strip().isdigit():
        ci = int(ci.strip())
    if not isinstance(ci, int) or isinstance(ci, bool) or not 0 <= ci <= 3:
        return None
    explanation = clean_plain(item.get("explanation"))[:700]
    if len(explanation) < 3:
        return None
    key = normalize_question_text(text)
    if not key or key in seen:
        return None
    difficulty = str(item.get("difficulty") or "medium").lower().strip()
    if difficulty not in ("easy", "medium", "hard"):
        difficulty = "medium"
    return {"text": text, "options": options, "correct_index": ci, "explanation": explanation, "difficulty": difficulty}

def build_test_prompt(topic: str, need: int, difficulty: str, lang: str, avoid: list[str]) -> str:
    lang_name = "Hindi (Devanagari script)" if lang == "hi" else "English"
    diff_text = {
        "easy": "easy (basic recall)", "medium": "medium (standard exam level)",
        "hard": "hard (tricky, application-based)", "mixed": "a balanced mix of easy, medium and hard",
    }.get(difficulty, "a balanced mix of easy, medium and hard")
    avoid_text = ""
    if avoid:
        avoid_text = "\nDo NOT repeat or rephrase any of these already-used questions:\n" + "\n".join(f"- {a}" for a in avoid)
    return (
        f"Create exactly {need} multiple-choice questions for: \"{topic}\".\n"
        f"Difficulty: {diff_text}. Language: {lang_name}.\n"
        "Rules:\n"
        "- Each question has exactly 4 distinct, plausible options; exactly one is correct.\n"
        "- correct_index is the 0-based index (0-3) of the correct option. Spread correct answers across positions.\n"
        "- explanation: 1-2 sentences explaining why the correct option is right.\n"
        "- Cover different sub-topics; no duplicate or near-duplicate questions.\n"
        "- Facts must be accurate and exam-relevant. Plain text only: no Markdown, no option letters inside option text.\n"
        "- difficulty: easy, medium or hard."
        f"{avoid_text}\n"
        "Return a JSON array only."
    )

ProgressCallback = Callable[[int, int], Awaitable[None]]

async def generate_test_questions(topic: str, total: int, difficulty: str, lang: str, api_key: str,
                                  progress: ProgressCallback | None = None) -> tuple[list[dict[str, Any]], str | None]:
    """Generate `total` validated questions in sequential batches with bounded retries.
    Returns (questions, None) on success or (partial_questions, error_code) on failure."""
    questions: list[dict[str, Any]] = []
    seen: set[str] = set()
    calls = 0
    idle_rounds = 0        # consecutive calls that added nothing usable
    rate_limit_hits = 0
    while len(questions) < total and calls < AI_TEST_MAX_CALLS:
        need = min(AI_TEST_BATCH, total - len(questions))
        # Ask for a couple of extra questions so that one or two rejects do not force another round trip.
        ask = min(need + 2, AI_TEST_BATCH + 2)
        avoid = [q["text"][:90] for q in questions[-12:]]
        calls += 1
        data, err = await ai_generate_json(
            build_test_prompt(topic, ask, difficulty, lang, avoid), TEST_SCHEMA, api_key,
            system=TEST_SYSTEM, temperature=0.8, max_tokens=8192, timeout=90.0,
        )
        if err in ("no_key", "auth"):
            return questions, err
        if err == "rate_limit":
            rate_limit_hits += 1
            if rate_limit_hits > 2:
                return questions, "rate_limit"
            await asyncio.sleep(4 * rate_limit_hits)
            continue
        if err in ("timeout", "network", "http", "parse", "empty") or not isinstance(data, list):
            idle_rounds += 1
            if idle_rounds >= 3:
                return questions, err or "parse"
            await asyncio.sleep(1.5)
            continue
        added = 0
        for item in data:
            q = validate_generated_question(item, seen)
            if q is None:
                continue
            seen.add(normalize_question_text(q["text"]))
            questions.append(q)
            added += 1
            if len(questions) >= total:
                break
        idle_rounds = 0 if added else idle_rounds + 1
        if idle_rounds >= 3:
            return questions, "parse"
        if progress:
            try:
                await progress(len(questions), total)
            except Exception:
                pass
    if len(questions) < total:
        return questions, "incomplete"
    return questions[:total], None

GENERATION_ERROR_TEXT = {
    "incomplete": "I couldn't build a complete, valid test for this topic right now. Please try again, pick a smaller number of questions, or make the topic more specific.",
    "parse": "The AI returned questions I couldn't validate. Nothing was saved — please try again.",
    "rate_limit": "The AI service is rate-limited at the moment. Please try again in a minute.",
    "timeout": "The AI service took too long. Please try again, maybe with fewer questions.",
    "network": "I couldn't reach the AI service. Please try again later.",
    "http": "The AI service returned an error. Please try again later.",
    "empty": "The AI returned an empty response. Please try again.",
}

# ============================ AI Test Generator — persistence service ============================
async def create_ai_test(session: AsyncSession, user: User, topic: str, requested: int, difficulty: str,
                         lang: str, questions: list[dict[str, Any]]) -> AiTest:
    test = AiTest(user_id=user.id, topic=topic[:200], requested_count=requested, question_count=len(questions),
                  language=lang, difficulty=difficulty, status="in_progress", current_index=0,
                  unanswered=len(questions), started_at=now_utc())
    session.add(test)
    await session.flush()
    for pos, q in enumerate(questions):
        session.add(AiTestQuestion(test_id=test.id, position=pos, text=q["text"], options_json=json.dumps(q["options"], ensure_ascii=False),
                                   correct_index=q["correct_index"], explanation=q["explanation"], difficulty=q["difficulty"]))
    await session.flush()
    return test

async def load_owned_test(session: AsyncSession, test_id: int, user: User) -> AiTest | None:
    test = await session.get(AiTest, test_id)
    if not test or test.user_id != user.id:
        return None
    return test

async def load_test_questions(session: AsyncSession, test: AiTest) -> list[AiTestQuestion]:
    return list((await session.execute(
        select(AiTestQuestion).where(AiTestQuestion.test_id == test.id).order_by(AiTestQuestion.position)
    )).scalars())

async def active_test_for(session: AsyncSession, user: User) -> AiTest | None:
    return (await session.execute(
        select(AiTest).where(AiTest.user_id == user.id, AiTest.status == "in_progress").order_by(AiTest.id.desc()).limit(1)
    )).scalars().first()

def score_from_questions(questions: list[AiTestQuestion]) -> tuple[int, int, int]:
    correct = sum(1 for q in questions if q.selected_index is not None and q.selected_index == q.correct_index)
    answered = sum(1 for q in questions if q.selected_index is not None)
    return correct, answered - correct, len(questions) - answered

async def finalize_ai_test(session: AsyncSession, test: AiTest, questions: list[AiTestQuestion]) -> bool:
    """Score once, from saved answers. Returns False if the test was already finalised."""
    if test.status != "in_progress":
        return False
    correct, incorrect, unanswered = score_from_questions(questions)
    test.correct, test.incorrect, test.unanswered = correct, incorrect, unanswered
    test.score = float(correct)
    attempted = correct + incorrect
    test.accuracy = round(correct / attempted * 100, 1) if attempted else 0.0
    test.status = "completed"
    test.completed_at = now_utc()
    await session.flush()
    return True

# ============================ AI Test Generator — rendering ============================
def difficulty_label(d: str) -> str:
    return {"easy": "Easy", "medium": "Medium", "hard": "Hard", "mixed": "Mixed"}.get(d, d.title())

def button_label(letter: str, text: str, limit: int = 40) -> str:
    text = text.replace("\n", " ").strip()
    return f"{letter}. {text}" if len(text) <= limit else f"{letter}. {text[:limit - 1].rstrip()}…"

def test_title(test: AiTest) -> str:
    return f"🧪 <b>{esc(test.topic)} Practice Test</b>"

def render_question_text(test: AiTest, questions: list[AiTestQuestion], idx: int) -> str:
    q = questions[idx]
    answered = sum(1 for x in questions if x.selected_index is not None)
    opts = q.options()
    lines = [test_title(test), f"Question {idx + 1}/{len(questions)} · {answered}/{len(questions)} answered", "",
             esc(q.text), ""]
    lines += [f"<b>{LETTERS[i]}.</b> {esc(o)}" for i, o in enumerate(opts)]
    if q.selected_index is not None and 0 <= q.selected_index < len(opts):
        lines += ["", f"✔️ Recorded: <b>{LETTERS[q.selected_index]}</b> (tap another option to change it)"]
    return "\n".join(lines)

def question_keyboard(test: AiTest, questions: list[AiTestQuestion], idx: int) -> InlineKeyboardMarkup:
    q = questions[idx]
    rows: list[list[tuple[str, str]]] = []
    for i, o in enumerate(q.options()):
        mark = "✔️ " if q.selected_index == i else ""
        rows.append([(mark + button_label(LETTERS[i], o), f"ta:{test.id}:{idx}:{i}")])   # one option per row
    nav: list[tuple[str, str]] = []
    if idx > 0:
        nav.append(("⬅️ Previous", f"tn:{test.id}:{idx - 1}"))
    if idx < len(questions) - 1:
        nav.append(("Next ➡️" if q.selected_index is not None else "Skip ➡️", f"tn:{test.id}:{idx + 1}"))
    if nav:
        rows.append(nav)
    rows.append([("🏁 Finish Test", f"tf:{test.id}")])
    return inline(rows)

async def show_test_question(message: Message, session: AsyncSession, test: AiTest, idx: int, *, edit: bool) -> None:
    questions = await load_test_questions(session, test)
    if not questions:
        await message.answer("This test has no questions."); return
    idx = max(0, min(idx, len(questions) - 1))
    test.current_index = idx
    text, markup = render_question_text(test, questions, idx), question_keyboard(test, questions, idx)
    if edit:
        await safe_edit(message, text, markup)
    else:
        await message.answer(text, reply_markup=markup)

def result_card(test: AiTest) -> str:
    return (
        "🏁 <b>TEST COMPLETED</b>\n\n"
        f"Topic: {esc(test.topic)}\n"
        f"Difficulty: {difficulty_label(test.difficulty)}\n\n"
        f"Score: <b>{test.correct}/{test.question_count}</b>\n\n"
        f"✅ Correct: {test.correct}\n"
        f"❌ Incorrect: {test.incorrect}\n"
        f"⏭ Unanswered: {test.unanswered}\n\n"
        f"📊 Accuracy: <b>{test.accuracy:.0f}%</b>"
    )

def result_keyboard(test: AiTest) -> InlineKeyboardMarkup:
    return inline([
        [("📖 Review Answers", f"tr:{test.id}:0")],
        [("🔄 Take Another Test", "gt:new"), ("📜 Test History", "th:0")],
        [("🏠 Main Menu", "menu:home")],
    ])

def render_review_page(test: AiTest, questions: list[AiTestQuestion], page: int) -> tuple[str, InlineKeyboardMarkup]:
    pages = max(1, (len(questions) + AI_TEST_REVIEW_PAGE - 1) // AI_TEST_REVIEW_PAGE)
    page = max(0, min(page, pages - 1))
    chunk = questions[page * AI_TEST_REVIEW_PAGE:(page + 1) * AI_TEST_REVIEW_PAGE]
    blocks = [f"📖 <b>Answer Review — {esc(test.topic)}</b> (page {page + 1}/{pages})"]
    for q in chunk:
        opts = q.options()
        correct_txt = f"{LETTERS[q.correct_index]}. {opts[q.correct_index]}" if 0 <= q.correct_index < len(opts) else "—"
        if q.selected_index is None:
            yours = "⏭ Not answered"
        elif q.selected_index == q.correct_index:
            yours = f"✅ {LETTERS[q.selected_index]}. {esc(opts[q.selected_index])}"
        else:
            yours = f"❌ {LETTERS[q.selected_index]}. {esc(opts[q.selected_index])}"
        block = (f"<b>Q{q.position + 1}.</b> {esc(q.text)}\n"
                 f"Your answer: {yours}\n"
                 f"Correct: <b>{esc(correct_txt)}</b>")
        if q.explanation:
            block += f"\n💡 {esc(q.explanation)}"
        blocks.append(block)
    nav: list[tuple[str, str]] = []
    if page > 0:
        nav.append(("⬅️ Previous", f"tr:{test.id}:{page - 1}"))
    if page < pages - 1:
        nav.append(("Next ➡️", f"tr:{test.id}:{page + 1}"))
    rows = ([nav] if nav else []) + [[("📊 Result", f"tv:{test.id}"), ("📜 Test History", "th:0")], [("🏠 Main Menu", "menu:home")]]
    return "\n\n".join(blocks), inline(rows)

# ============================ AI Test Generator — setup flow (FSM) ============================
def topic_keyboard(exams: list[Exam]) -> InlineKeyboardMarkup:
    names_lower = {t.lower() for t in COMMON_TEST_TOPICS}
    buttons: list[tuple[str, str]] = [(t, f"gt:t:{i}") for i, t in enumerate(COMMON_TEST_TOPICS)]
    buttons += [(e.name, f"gt:e:{e.id}") for e in exams if e.name.lower() not in names_lower][:10]
    rows = [buttons[i:i + 2] for i in range(0, len(buttons), 2)]
    rows.append([("✍️ Custom Topic", "gt:c")])
    rows.append([("❌ Cancel", "gt:x")])
    return inline(rows)

def count_keyboard() -> InlineKeyboardMarkup:
    return inline([
        [("5 Questions", "gt:n:5"), ("10 Questions", "gt:n:10")],
        [("20 Questions", "gt:n:20"), ("30 Questions", "gt:n:30")],
        [("50 Questions", "gt:n:50"), ("🔢 Custom Number", "gt:nc")],
        [("⬅️ Back", "gt:bt"), ("❌ Cancel", "gt:x")],
    ])

def difficulty_keyboard(lang: str) -> InlineKeyboardMarkup:
    def mark(v: str) -> str:
        return " ✅" if lang == v else ""
    return inline([
        [("🟢 Easy", "gt:d:easy"), ("🟡 Medium", "gt:d:medium")],
        [("🔴 Hard", "gt:d:hard"), ("🎲 Mixed Difficulty", "gt:d:mixed")],
        [("🇬🇧 English" + mark("en"), "gt:l:en"), ("🇮🇳 हिन्दी" + mark("hi"), "gt:l:hi")],
        [("⬅️ Back", "gt:bn"), ("❌ Cancel", "gt:x")],
    ])

async def aitest_available(message: Message, session: AsyncSession, user: User) -> bool:
    if not await feature_enabled(session, "aitest"):
        await message.answer("🧪 AI Test generation is temporarily disabled by the administrator."); return False
    if not await current_api_key(session):
        await message.answer(esc(AI_ERROR_TEXT["no_key"])); return False
    return True

async def start_test_setup(message: Message, session: AsyncSession, user: User, state: FSMContext) -> None:
    if not await aitest_available(message, session, user):
        return
    await state.clear()
    active = await active_test_for(session, user)
    if active:
        answered = int((await session.execute(select(func.count()).select_from(AiTestQuestion).where(
            AiTestQuestion.test_id == active.id, AiTestQuestion.selected_index.is_not(None)))).scalar_one())
        await message.answer(
            f"You have an unfinished test: <b>{esc(active.topic)}</b> ({answered}/{active.question_count} answered).",
            reply_markup=inline([[("▶️ Resume", f"tn:{active.id}:{active.current_index}")],
                                 [("🗑 Discard and start new", f"gt:discard:{active.id}")],
                                 [("❌ Cancel", "gt:x")]]))
        return
    await show_topic_step(message, session, state, edit=False)

async def show_topic_step(message: Message, session: AsyncSession, state: FSMContext, *, edit: bool) -> None:
    exams = list((await session.execute(select(Exam).where(Exam.active.is_(True)).order_by(Exam.name))).scalars())
    await state.set_state(TestFlow.topic)
    text = ("🧪 <b>Generate AI Test</b>\n\nStep 1/3 — Choose an exam or topic, or tap ✍️ Custom Topic to type your own "
            "(e.g. <i>BPSC — Bihar History</i>, <i>Photosynthesis</i>).")
    if edit:
        await safe_edit(message, text, topic_keyboard(exams))
    else:
        await message.answer(text, reply_markup=topic_keyboard(exams))

async def show_count_step(message: Message, state: FSMContext, *, edit: bool) -> None:
    data = await state.get_data()
    await state.set_state(TestFlow.count)
    text = (f"🧪 <b>Generate AI Test</b>\n\nTopic: <b>{esc(data.get('topic'))}</b>\n\n"
            f"Step 2/3 — How many questions? (1–{AI_TEST_MAX})")
    if edit:
        await safe_edit(message, text, count_keyboard())
    else:
        await message.answer(text, reply_markup=count_keyboard())

async def show_difficulty_step(message: Message, state: FSMContext, *, edit: bool) -> None:
    data = await state.get_data()
    await state.set_state(TestFlow.difficulty)
    lang = data.get("lang", "en")
    text = (f"🧪 <b>Generate AI Test</b>\n\nTopic: <b>{esc(data.get('topic'))}</b>\n"
            f"Questions: <b>{data.get('count')}</b>\n"
            f"Language: <b>{'हिन्दी' if lang == 'hi' else 'English'}</b>\n\n"
            "Step 3/3 — Pick a difficulty to start generating.")
    if edit:
        await safe_edit(message, text, difficulty_keyboard(lang))
    else:
        await message.answer(text, reply_markup=difficulty_keyboard(lang))

@router.message(F.text == "🧪 Generate AI Test")
async def generate_test_button(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    if not await gate(message, db_user, session): return
    await start_test_setup(message, session, db_user, state)

@router.message(F.text == "📜 Test History")
async def test_history_button(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    if not await gate(message, db_user, session): return
    await state.clear()
    await show_test_history(message, session, db_user, page=0)

# Users currently generating a test (guards against duplicate sessions from repeated callbacks).
GENERATING_USERS: set[int] = set()

@router.callback_query(F.data.startswith("gt:"))
async def test_setup_callback(cb: CallbackQuery, session: AsyncSession, db_user: User, state: FSMContext):
    parts = cb.data.split(":")
    action = parts[1] if len(parts) > 1 else ""
    arg = parts[2] if len(parts) > 2 else ""
    if db_user.status == "banned" or (not db_user.access_granted and not db_user.is_admin):
        await cb.answer("Access is not available.", show_alert=True); return
    if action == "x":
        await state.clear(); await cb.answer("Cancelled")
        await safe_edit(cb.message, "❌ Test setup cancelled.")
        return
    if action == "new":
        await cb.answer()
        await start_test_setup(cb.message, session, db_user, state); return
    if action == "discard":
        test = await load_owned_test(session, int(arg), db_user) if arg.isdigit() else None
        if test and test.status == "in_progress":
            test.status = "abandoned"
            await session.flush()
        await cb.answer("Discarded")
        await show_topic_step(cb.message, session, state, edit=True); return
    if not await feature_enabled(session, "aitest"):
        await state.clear(); await cb.answer("AI Test generation is disabled.", show_alert=True); return
    current = await state.get_state()
    if current == TestFlow.generating.state:
        await cb.answer("Your test is still being generated…"); return
    if action == "t" or action == "e":
        if action == "t":
            if not arg.isdigit() or int(arg) >= len(COMMON_TEST_TOPICS):
                await cb.answer("Invalid topic.", show_alert=True); return
            topic = COMMON_TEST_TOPICS[int(arg)]
        else:
            exam = await session.get(Exam, int(arg)) if arg.isdigit() else None
            if not exam or not exam.active:
                await cb.answer("This exam is not available.", show_alert=True); return
            topic = exam.name
        await state.update_data(topic=topic, lang=db_user.language if db_user.language in ("en", "hi") else "en")
        await cb.answer()
        await show_count_step(cb.message, state, edit=True); return
    if action == "c":
        await state.set_state(TestFlow.custom_topic)
        await cb.answer()
        await safe_edit(cb.message, "✍️ Type the exam name, subject or topic for your test.\n"
                                    "Examples: <i>Bihar Police Constable — Indian Constitution</i>, <i>Railway Group D — General Science</i>, "
                                    "<i>Photosynthesis</i>.\n\nSend /cancel to stop.",
                        inline([[("❌ Cancel", "gt:x")]]))
        return
    if action == "bt":
        await cb.answer(); await show_topic_step(cb.message, session, state, edit=True); return
    data = await state.get_data()
    if not data.get("topic"):
        await cb.answer("Please choose a topic first.", show_alert=True)
        await show_topic_step(cb.message, session, state, edit=True); return
    if action == "n":
        if not arg.isdigit() or not AI_TEST_MIN <= int(arg) <= AI_TEST_MAX:
            await cb.answer("Invalid number.", show_alert=True); return
        await state.update_data(count=int(arg))
        await cb.answer()
        await show_difficulty_step(cb.message, state, edit=True); return
    if action == "nc":
        await state.set_state(TestFlow.custom_count)
        await cb.answer()
        await safe_edit(cb.message, f"🔢 Send the number of questions you want ({AI_TEST_MIN}–{AI_TEST_MAX}).\nSend /cancel to stop.",
                        inline([[("⬅️ Back", "gt:bt2"), ("❌ Cancel", "gt:x")]]))
        return
    if action == "bt2":
        await cb.answer(); await show_count_step(cb.message, state, edit=True); return
    if action == "bn":
        await cb.answer(); await show_count_step(cb.message, state, edit=True); return
    if action == "l" and arg in ("en", "hi"):
        await state.update_data(lang=arg)
        await cb.answer("Language set")
        await show_difficulty_step(cb.message, state, edit=True); return
    if action == "d":
        if arg not in AI_TEST_DIFFICULTIES:
            await cb.answer("Invalid difficulty.", show_alert=True); return
        if not data.get("count"):
            await cb.answer("Choose the number of questions first.", show_alert=True)
            await show_count_step(cb.message, state, edit=True); return
        await cb.answer()
        await run_test_generation(cb.message, session, db_user, state, data["topic"], int(data["count"]), arg,
                                  data.get("lang", "en"))
        return
    await cb.answer("Unknown action.", show_alert=True)

@router.message(TestFlow.custom_topic, F.text)
async def custom_topic_input(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    text = re.sub(r"\s+", " ", (message.text or "")).strip()
    if text.startswith("/"):
        await message.answer("Send a topic name, or /cancel to stop."); return
    if len(text) < 2 or len(text) > 120:
        await message.answer("Please send a topic between 2 and 120 characters, or /cancel."); return
    await state.update_data(topic=text, lang=db_user.language if db_user.language in ("en", "hi") else "en")
    await show_count_step(message, state, edit=False)

@router.message(TestFlow.custom_count, F.text)
async def custom_count_input(message: Message, state: FSMContext):
    raw = (message.text or "").strip()
    if raw.startswith("/"):
        await message.answer("Send a number, or /cancel to stop."); return
    if not re.fullmatch(r"\d{1,3}", raw) or not AI_TEST_MIN <= int(raw) <= AI_TEST_MAX:
        await message.answer(f"❗ Please send a whole number between {AI_TEST_MIN} and {AI_TEST_MAX}."); return
    await state.update_data(count=int(raw))
    await show_difficulty_step(message, state, edit=False)

@router.message(TestFlow.topic, F.text)
@router.message(TestFlow.count, F.text)
@router.message(TestFlow.difficulty, F.text)
async def setup_text_nudge(message: Message):
    await message.answer("Please use the buttons above to continue, or send /cancel to stop.")

@router.message(TestFlow.generating)
async def generating_nudge(message: Message):
    await message.answer("⏳ Your test is being generated. Please wait a moment…")

async def run_test_generation(message: Message, session: AsyncSession, user: User, state: FSMContext,
                              topic: str, count: int, difficulty: str, lang: str) -> None:
    if user.id in GENERATING_USERS:
        await message.answer("⏳ A test is already being generated for you. Please wait."); return
    if await active_test_for(session, user):
        await state.clear()
        await message.answer("You already have a test in progress. Open 📜 Test History to resume it."); return
    if not user.is_admin and user.ai_count >= FREE_AI_DAILY_LIMIT:
        await state.clear()
        await message.answer(f"Daily AI limit reached ({FREE_AI_DAILY_LIMIT} requests). Try again tomorrow."); return
    api_key = await current_api_key(session)
    if not api_key:
        await state.clear(); await message.answer(esc(AI_ERROR_TEXT["no_key"])); return
    # One logical test = one AI charge, regardless of internal batches/retries.
    if not user.is_admin:
        user.ai_count += 1
    await state.set_state(TestFlow.generating)
    GENERATING_USERS.add(user.id)
    # Persist the charge now so no write transaction stays open during the slow generation.
    await session.commit()
    progress_msg = await message.answer(f"⏳ Generating your {count}-question practice test on <b>{esc(topic)}</b>…")

    async def progress(done: int, total: int) -> None:
        if total > AI_TEST_BATCH:
            await safe_edit(progress_msg, f"⏳ Generating your {total}-question practice test on <b>{esc(topic)}</b>…\n"
                                          f"Progress: {done}/{total} questions ready")
    try:
        questions, err = await generate_test_questions(topic, count, difficulty, lang, api_key, progress)
    finally:
        GENERATING_USERS.discard(user.id)
        await state.clear()
    if err or len(questions) != count:
        text = AI_ERROR_TEXT.get(err, "") if err in ("no_key", "auth") else GENERATION_ERROR_TEXT.get(err or "incomplete", GENERATION_ERROR_TEXT["incomplete"])
        await safe_edit(progress_msg, "❌ " + esc(text), inline([[("🔄 Try again", "gt:new"), ("🏠 Main Menu", "menu:home")]]))
        return
    test = await create_ai_test(session, user, topic, count, difficulty, lang, questions)
    await safe_edit(progress_msg, f"✅ Your <b>{count}-question</b> test on <b>{esc(topic)}</b> is ready. Good luck!")
    await show_test_question(message, session, test, 0, edit=False)

# ============================ AI Test Generator — answering, finishing, review, history ============================
@router.callback_query(F.data.startswith("ta:"))
async def test_answer_callback(cb: CallbackQuery, session: AsyncSession, db_user: User):
    try:
        _, sid, idx, opt = cb.data.split(":"); sid, idx, opt = int(sid), int(idx), int(opt)
    except Exception:
        await cb.answer("Invalid button.", show_alert=True); return
    test = await load_owned_test(session, sid, db_user)
    if not test:
        await cb.answer("Test not found.", show_alert=True); return
    if test.status != "in_progress":
        await cb.answer("This test is already finished. Open Test History to review it.", show_alert=True); return
    questions = await load_test_questions(session, test)
    if not 0 <= idx < len(questions) or not 0 <= opt < 4 or opt >= len(questions[idx].options()):
        await cb.answer("Invalid option.", show_alert=True); return
    q = questions[idx]
    if q.selected_index == opt:
        await cb.answer(f"Answer {LETTERS[opt]} is already recorded."); return
    q.selected_index = opt
    q.answered_at = now_utc()
    await session.flush()
    answered = sum(1 for x in questions if x.selected_index is not None)
    await cb.answer(f"Recorded {LETTERS[opt]} · {answered}/{len(questions)} answered")
    if answered == len(questions):
        if await finalize_ai_test(session, test, questions):
            await safe_edit(cb.message, result_card(test), result_keyboard(test))
        return
    # Move to the next unanswered question after this one (wrapping), otherwise stay.
    next_idx = next((i for i in list(range(idx + 1, len(questions))) + list(range(0, idx)) if questions[i].selected_index is None), idx)
    test.current_index = next_idx
    await safe_edit(cb.message, render_question_text(test, questions, next_idx), question_keyboard(test, questions, next_idx))

@router.callback_query(F.data.startswith("tn:"))
async def test_nav_callback(cb: CallbackQuery, session: AsyncSession, db_user: User, state: FSMContext):
    try:
        _, sid, idx = cb.data.split(":"); sid, idx = int(sid), int(idx)
    except Exception:
        await cb.answer("Invalid button.", show_alert=True); return
    test = await load_owned_test(session, sid, db_user)
    if not test:
        await cb.answer("Test not found.", show_alert=True); return
    if test.status != "in_progress":
        await cb.answer()
        await safe_edit(cb.message, result_card(test), result_keyboard(test)); return
    await state.clear()
    await cb.answer()
    await show_test_question(cb.message, session, test, idx, edit=True)

@router.callback_query(F.data.startswith("tf:"))
async def test_finish_prompt(cb: CallbackQuery, session: AsyncSession, db_user: User):
    sid = cb.data.split(":")[1]
    test = await load_owned_test(session, int(sid), db_user) if sid.isdigit() else None
    if not test:
        await cb.answer("Test not found.", show_alert=True); return
    if test.status != "in_progress":
        await cb.answer("Already finished."); await safe_edit(cb.message, result_card(test), result_keyboard(test)); return
    questions = await load_test_questions(session, test)
    _, _, unanswered = score_from_questions(questions)
    await cb.answer()
    note = f"\n\n⏭ {unanswered} question(s) are unanswered and will be counted as unanswered (not incorrect)." if unanswered else ""
    await safe_edit(cb.message, f"🏁 Finish <b>{esc(test.topic)}</b> test now?{note}",
                    inline([[("✅ Yes, finish", f"tfc:{test.id}")], [("⬅️ Back to test", f"tn:{test.id}:{test.current_index}")]]))

@router.callback_query(F.data.startswith("tfc:"))
async def test_finish_confirm(cb: CallbackQuery, session: AsyncSession, db_user: User, state: FSMContext):
    sid = cb.data.split(":")[1]
    test = await load_owned_test(session, int(sid), db_user) if sid.isdigit() else None
    if not test:
        await cb.answer("Test not found.", show_alert=True); return
    questions = await load_test_questions(session, test)
    finished_now = await finalize_ai_test(session, test, questions)
    await state.clear()
    await cb.answer("Submitted" if finished_now else "Already submitted")
    await safe_edit(cb.message, result_card(test), result_keyboard(test))

@router.callback_query(F.data.startswith("tv:"))
async def test_view_callback(cb: CallbackQuery, session: AsyncSession, db_user: User):
    sid = cb.data.split(":")[1]
    test = await load_owned_test(session, int(sid), db_user) if sid.isdigit() else None
    if not test:
        await cb.answer("Test not found.", show_alert=True); return
    await cb.answer()
    if test.status == "in_progress":
        await show_test_question(cb.message, session, test, test.current_index, edit=True); return
    if test.status == "abandoned":
        await safe_edit(cb.message, f"This test on <b>{esc(test.topic)}</b> was discarded before completion.",
                        inline([[("📜 Test History", "th:0"), ("🏠 Main Menu", "menu:home")]])); return
    await safe_edit(cb.message, result_card(test), result_keyboard(test))

@router.callback_query(F.data.startswith("tr:"))
async def test_review_callback(cb: CallbackQuery, session: AsyncSession, db_user: User):
    try:
        _, sid, page = cb.data.split(":"); sid, page = int(sid), int(page)
    except Exception:
        await cb.answer("Invalid button.", show_alert=True); return
    test = await load_owned_test(session, sid, db_user)
    if not test:
        await cb.answer("Test not found.", show_alert=True); return
    if test.status != "completed":
        await cb.answer("Finish the test first to review the answers.", show_alert=True); return
    questions = await load_test_questions(session, test)
    text, markup = render_review_page(test, questions, page)
    await cb.answer()
    chunks = split_html(text)
    if len(chunks) == 1:
        await safe_edit(cb.message, text, markup)
    else:
        await send_html(cb.message, text, markup)

async def show_test_history(message: Message, session: AsyncSession, user: User, page: int, *, edit: bool = False) -> None:
    total = int((await session.execute(select(func.count()).select_from(AiTest).where(AiTest.user_id == user.id))).scalar_one())
    if total == 0:
        text = "📜 <b>Test History</b>\n\nYou haven't taken any AI tests yet. Tap 🧪 Generate AI Test to start."
        markup = inline([[("🧪 Generate AI Test", "gt:new")]])
        await (safe_edit(message, text, markup) if edit else message.answer(text, reply_markup=markup)); return
    pages = (total + AI_TEST_HISTORY_PAGE - 1) // AI_TEST_HISTORY_PAGE
    page = max(0, min(page, pages - 1))
    tests = list((await session.execute(
        select(AiTest).where(AiTest.user_id == user.id).order_by(AiTest.id.desc())
        .offset(page * AI_TEST_HISTORY_PAGE).limit(AI_TEST_HISTORY_PAGE)
    )).scalars())
    lines = [f"📜 <b>Test History</b> (page {page + 1}/{pages}, {total} tests)", ""]
    rows: list[list[tuple[str, str]]] = []
    for t in tests:
        date = (t.completed_at or t.created_at).strftime("%d %b %Y")
        if t.status == "completed":
            summary = f"{t.correct}/{t.question_count} · {t.accuracy:.0f}%"
        elif t.status == "in_progress":
            summary = "in progress"
        else:
            summary = "discarded"
        lines.append(f"• <b>{esc(t.topic)}</b> — {date} — {summary}")
        label = f"{t.topic[:28]} · {summary}"
        rows.append([(label, f"tv:{t.id}")])
    nav: list[tuple[str, str]] = []
    if page > 0:
        nav.append(("⬅️ Newer", f"th:{page - 1}"))
    if page < pages - 1:
        nav.append(("Older ➡️", f"th:{page + 1}"))
    if nav:
        rows.append(nav)
    rows.append([("🧪 New Test", "gt:new"), ("🏠 Main Menu", "menu:home")])
    text, markup = "\n".join(lines), inline(rows)
    if edit:
        await safe_edit(message, text, markup)
    else:
        await message.answer(text, reply_markup=markup)

@router.callback_query(F.data.startswith("th:"))
async def test_history_callback(cb: CallbackQuery, session: AsyncSession, db_user: User):
    page = cb.data.split(":")[1]
    await cb.answer()
    await show_test_history(cb.message, session, db_user, int(page) if page.isdigit() else 0, edit=True)


# ============================ Admin mock tests, materials, stats, profile (existing) ============================
async def list_mock_tests(message: Message, session: AsyncSession, user: User):
    if not user.selected_exam_id:
        await message.answer("Select your exam first."); await show_exams(message, session); return
    tests = list((await session.execute(select(MockTest).where(
        MockTest.exam_id == user.selected_exam_id, MockTest.published.is_(True)
    ).order_by(MockTest.id.desc()))).scalars())
    if not tests:
        await message.answer("No mock tests have been published for your exam yet."); return
    await message.answer("📝 Choose a mock test:", reply_markup=inline([
        [(f"{t.title} · {t.duration} min", f"mockinfo:{t.id}")] for t in tests
    ]))

@router.callback_query(F.data.startswith("mockinfo:"))
async def mock_info(cb: CallbackQuery, session: AsyncSession):
    try: tid = int(cb.data.split(":")[1])
    except Exception: await cb.answer("Invalid test."); return
    test = await session.get(MockTest, tid)
    if not test or not test.published:
        await cb.answer("Test unavailable.", show_alert=True); return
    count = int((await session.execute(select(func.count()).select_from(MockQuestion).where(MockQuestion.test_id == tid))).scalar_one())
    await cb.answer()
    await safe_edit(cb.message,
        f"📝 <b>{esc(test.title)}</b>\nQuestions: {count}\nTime limit: {test.duration} minutes\n"
        "The timer starts when you press Start.",
        inline([[("▶️ Start test", f"mockstart:{tid}")]])
    )

@router.callback_query(F.data.startswith("mockstart:"))
async def mock_start(cb: CallbackQuery, session: AsyncSession, db_user: User):
    try: tid = int(cb.data.split(":")[1])
    except Exception: await cb.answer("Invalid test."); return
    test = await session.get(MockTest, tid)
    if not test or not test.published:
        await cb.answer("Test unavailable.", show_alert=True); return
    qids = list((await session.execute(select(MockQuestion.question_id).where(
        MockQuestion.test_id == tid).order_by(MockQuestion.position))).scalars())
    valid = []
    for qid in qids:
        q = await session.get(Question, qid)
        if q and q.published:
            await session.refresh(q, attribute_names=["options"])
            if len(q.options) >= 2 and sum(o.correct for o in q.options) == 1: valid.append(qid)
    if not valid:
        await cb.answer("This test has no valid questions.", show_alert=True); return
    random.shuffle(valid)
    attempt = MockAttempt(
        user_id=db_user.id, test_id=tid, deadline_at=now_utc()+timedelta(minutes=test.duration),
        question_ids=json.dumps(valid), answers_json="{}",
    )
    session.add(attempt); await session.flush()
    await cb.answer("Test started")
    await render_mock_question(cb.message, session, attempt, 0)

async def render_mock_question(message: Message, session: AsyncSession, attempt: MockAttempt, index: int):
    qids = json.loads(attempt.question_ids)
    if now_utc() >= attempt.deadline_at:
        await finish_mock(message, session, attempt)
        return
    if index < 0 or index >= len(qids): index = 0
    q = await session.get(Question, qids[index])
    await session.refresh(q, attribute_names=["options"])
    options = q.options[:]
    random.shuffle(options)
    answers = json.loads(attempt.answers_json)
    lines = [f"{LETTERS[i] if i < 4 else i+1}) {esc(o.text)}" for i,o in enumerate(options)]
    rows = [[(LETTERS[i] if i < 4 else str(i+1), f"mockans:{attempt.id}:{index}:{o.id}") for i,o in enumerate(options)]]
    nav = []
    if index > 0: nav.append(("⬅️ Previous", f"mockgoto:{attempt.id}:{index-1}"))
    if index < len(qids)-1: nav.append(("Next ➡️", f"mockgoto:{attempt.id}:{index+1}"))
    if nav: rows.append(nav)
    rows.append([("📤 Submit test", f"mockfinish:{attempt.id}")])
    selected_id = answers.get(str(q.id))
    selected_txt = next((esc(o.text) for o in q.options if o.id == selected_id), None)
    await message.answer(
        f"📝 <b>{esc((await session.get(MockTest, attempt.test_id)).title)}</b>\n"
        f"Question {index+1}/{len(qids)} · {max(0,int((attempt.deadline_at-now_utc()).total_seconds()//60))} min left\n\n"
        f"{esc(q.text)}\n\n" + "\n".join(lines) +
        (f"\n\nSelected: {selected_txt}" if selected_txt else ""),
        reply_markup=inline(rows)
    )

@router.callback_query(F.data.startswith("mockgoto:"))
async def mock_goto(cb: CallbackQuery, session: AsyncSession, db_user: User):
    try: aid, idx = map(int, cb.data.split(":")[1:])
    except Exception: await cb.answer("Invalid button."); return
    a = await session.get(MockAttempt, aid)
    if not a or a.user_id != db_user.id or a.status != "in_progress":
        await cb.answer("Attempt unavailable.", show_alert=True); return
    await cb.answer()
    await render_mock_question(cb.message, session, a, idx)

@router.callback_query(F.data.startswith("mockans:"))
async def mock_answer(cb: CallbackQuery, session: AsyncSession, db_user: User):
    try: aid, idx, oid = map(int, cb.data.split(":")[1:])
    except Exception: await cb.answer("Invalid button."); return
    a = await session.get(MockAttempt, aid)
    if not a or a.user_id != db_user.id or a.status != "in_progress":
        await cb.answer("Attempt unavailable.", show_alert=True); return
    if now_utc() >= a.deadline_at:
        await finish_mock(cb.message, session, a); await cb.answer("Time is up", show_alert=True); return
    qids = json.loads(a.question_ids)
    if idx >= len(qids): await cb.answer("Invalid question."); return
    q = await session.get(Question, qids[idx]); await session.refresh(q, attribute_names=["options"])
    option = next((o for o in q.options if o.id == oid), None)
    if not option: await cb.answer("Invalid option."); return
    answers = json.loads(a.answers_json); answers[str(q.id)] = oid; a.answers_json = json.dumps(answers)
    await session.flush()
    await cb.answer("Answer saved")
    await render_mock_question(cb.message, session, a, idx)

@router.callback_query(F.data.startswith("mockfinish:"))
async def mock_finish_callback(cb: CallbackQuery, session: AsyncSession, db_user: User):
    try: aid = int(cb.data.split(":")[1])
    except Exception: await cb.answer("Invalid test."); return
    a = await session.get(MockAttempt, aid)
    if not a or a.user_id != db_user.id or a.status != "in_progress":
        await cb.answer("Test already submitted or unavailable.", show_alert=True); return
    await finish_mock(cb.message, session, a)
    await cb.answer("Submitted")

async def finish_mock(message: Message, session: AsyncSession, a: MockAttempt):
    if a.status != "in_progress": return
    answers = json.loads(a.answers_json); qids = json.loads(a.question_ids)
    correct = incorrect = 0
    for qid in qids:
        q = await session.get(Question, qid); await session.refresh(q, attribute_names=["options"])
        chosen = answers.get(str(qid))
        right = next((o.id for o in q.options if o.correct), None)
        if chosen is None: continue
        if chosen == right: correct += 1
        else: incorrect += 1
    a.correct, a.incorrect, a.unanswered = correct, incorrect, len(qids)-correct-incorrect
    a.score = float(correct)
    a.status = "completed"
    await session.flush()
    test = await session.get(MockTest, a.test_id)
    if correct + incorrect:
        text = (f"🏁 <b>Mock test result: {esc(test.title)}</b>\n\n"
                f"Score: <b>{correct}/{len(qids)}</b>\n✅ Correct: {correct}\n❌ Incorrect: {incorrect}\n"
                f"⏭ Unanswered: {a.unanswered}\nAccuracy: {correct/(correct+incorrect)*100:.1f}%")
    else:
        text = f"🏁 <b>Mock test result: {esc(test.title)}</b>\n\nScore: {correct}/{len(qids)}\nNo answers attempted."
    await message.answer(text)

async def list_materials(message: Message, session: AsyncSession, user: User):
    stmt = select(Material).where(Material.published.is_(True))
    if user.selected_exam_id: stmt = stmt.where((Material.exam_id == user.selected_exam_id) | (Material.exam_id.is_(None)))
    materials = list((await session.execute(stmt.order_by(Material.id.desc()).limit(30))).scalars())
    if not materials:
        await message.answer("No study materials are available yet."); return
    for m in materials:
        text = f"📚 <b>{esc(m.title)}</b>"
        if m.description: text += f"\n{esc(m.description)}"
        if m.url: text += f"\n🔗 {esc(m.url)}"
        await message.answer(text)

async def performance(message: Message, session: AsyncSession, user: User):
    total = int((await session.execute(select(func.count()).select_from(Practice).where(Practice.user_id == user.id, Practice.answered_at.is_not(None)))).scalar_one())
    correct = int((await session.execute(select(func.count()).select_from(Practice).where(Practice.user_id == user.id, Practice.answered_at.is_not(None), Practice.is_correct.is_(True)))).scalar_one())
    accuracy = f"{correct/total*100:.1f}%" if total else "—"
    mocks = int((await session.execute(select(func.count()).select_from(MockAttempt).where(MockAttempt.user_id == user.id, MockAttempt.status == "completed"))).scalar_one())
    ai_tests = int((await session.execute(select(func.count()).select_from(AiTest).where(AiTest.user_id == user.id, AiTest.status == "completed"))).scalar_one())
    ai_avg = (await session.execute(select(func.avg(AiTest.accuracy)).where(AiTest.user_id == user.id, AiTest.status == "completed"))).scalar_one()
    ai_line = f"\nAI tests completed: {ai_tests}" + (f" (avg accuracy {float(ai_avg):.0f}%)" if ai_tests and ai_avg is not None else "")
    await message.answer(f"📊 <b>Your Performance</b>\nQuestions answered: {total}\nCorrect: {correct}\nAccuracy: {accuracy}\nMock tests completed: {mocks}{ai_line}")

async def leaderboard(message: Message, session: AsyncSession):
    rows = (await session.execute(
        select(User.full_name, func.count(Practice.id).label("correct_count"))
        .join(Practice, Practice.user_id == User.id)
        .where(Practice.answered_at.is_not(None), Practice.is_correct.is_(True), User.status == "active")
        .group_by(User.id).order_by(func.count(Practice.id).desc()).limit(10)
    )).all()
    if not rows: await message.answer("The leaderboard is empty. Answer some quiz questions to appear here."); return
    text = "🏆 <b>Leaderboard — correct practice answers</b>\n\n"
    text += "\n".join(f"{i}. {esc(name)} — {score}" for i,(name,score) in enumerate(rows,1))
    await message.answer(text)

async def profile(message: Message, session: AsyncSession, user: User):
    exam = await session.get(Exam, user.selected_exam_id) if user.selected_exam_id else None
    style = "Short" if user.answer_style == STYLE_SHORT else "Detailed"
    await message.answer(
        f"👤 <b>My Profile</b>\nName: {esc(user.full_name)}\nTelegram ID: <code>{user.telegram_id}</code>\n"
        f"Exam: {esc(exam.name if exam else 'Not selected')}\nJoined: {user.joined_at:%d %b %Y}\n"
        f"Answer style: {style}\nLanguage: {'हिन्दी' if user.language == 'hi' else 'English'}\n"
        f"Account: {esc(user.status)}\nAI requests today: {user.ai_count}/{FREE_AI_DAILY_LIMIT if not user.is_admin else 'unlimited'}"
    )

@router.message(Command("profile"))
async def profile_command(message: Message, session: AsyncSession, db_user: User):
    await profile(message, session, db_user)

@router.message(Command("settings"))
async def settings_command(message: Message, db_user: User):
    await show_settings(message, db_user)

@router.message(Command("language"))
async def language_command(message: Message, session: AsyncSession, db_user: User):
    parts = (message.text or "").split(maxsplit=1)
    if len(parts) != 2 or parts[1].lower() not in ("en", "hi"):
        await message.answer("Usage: /language en or /language hi"); return
    db_user.language = parts[1].lower()
    await message.answer(f"Language preference saved: {db_user.language}")

@router.message(Command("delete_me"))
async def delete_me(message: Message, session: AsyncSession, db_user: User):
    await message.answer("⚠️ This permanently deletes your profile and activity. Confirm?", reply_markup=inline([
        [("🗑 Yes, delete my data", "delete:confirm"), ("Cancel", "delete:cancel")]
    ]))

@router.callback_query(F.data.startswith("delete:"))
async def delete_callback(cb: CallbackQuery, session: AsyncSession, db_user: User, state: FSMContext):
    if cb.data == "delete:cancel":
        await cb.answer("Cancelled"); await safe_edit(cb.message, "Data deletion cancelled."); return
    await state.clear()
    # Explicit deletes: SQLite does not enforce ON DELETE CASCADE unless foreign keys are enabled.
    test_ids = select(AiTest.id).where(AiTest.user_id == db_user.id)
    await session.execute(delete(AiTestQuestion).where(AiTestQuestion.test_id.in_(test_ids)))
    await session.execute(delete(AiTest).where(AiTest.user_id == db_user.id))
    await session.execute(delete(User).where(User.id == db_user.id))
    await session.flush()
    await cb.answer("Deleted")
    await safe_edit(cb.message, "Your profile and activity have been deleted. Send /start to register again.")

# ------------------------------ Admin tools ------------------------------
def admin_keyboard():
    return inline([
        [("📊 Statistics", "adm:stats"), ("👥 Users", "adm:users")],
        [("➕ Add exam", "adm:addexam"), ("➕ Add question", "adm:addq")],
        [("📚 Add material", "adm:addmat"), ("📝 Create mock", "adm:addmock")],
        [("📣 Broadcast", "adm:broadcast"), ("🛠 Maintenance", "adm:maintenance")],
        [("🔑 Gemini API key", "adm:apikey"), ("⚙️ Features", "adm:features")],
        [("🔐 Access / ban help", "adm:accesshelp")],
    ])

@router.message(F.text == "🛠 Admin Panel")
@router.message(Command("admin"))
async def admin_panel(message: Message, db_user: User):
    if not db_user.is_admin:
        await message.answer("⛔ Admin only."); return
    await message.answer("🛠 <b>ExamYatra Admin Panel</b>\nChoose an action:", reply_markup=admin_keyboard())

def features_keyboard(status: dict[str, str]) -> InlineKeyboardMarkup:
    return inline([[(f"{'🟢' if status[k] == 'true' else '🔴'} {k}", f"adm:feat:{k}")] for k in FEATURE_NAMES]
                  + [[("↩️ Admin menu", "adm:back")]])

@router.callback_query(F.data.startswith("adm:"))
async def admin_callbacks(cb: CallbackQuery, session: AsyncSession, db_user: User, state: FSMContext):
    if not db_user.is_admin:
        await cb.answer("Admin only.", show_alert=True); return
    action = cb.data.split(":",1)[1]
    await cb.answer()
    if action == "stats":
        users = int((await session.execute(select(func.count()).select_from(User))).scalar_one())
        active = int((await session.execute(select(func.count()).select_from(User).where(User.status=="active"))).scalar_one())
        qs = int((await session.execute(select(func.count()).select_from(Question))).scalar_one())
        exams = int((await session.execute(select(func.count()).select_from(Exam).where(Exam.active.is_(True)))).scalar_one())
        ai_tests = int((await session.execute(select(func.count()).select_from(AiTest))).scalar_one())
        await cb.message.answer(f"📊 Stats\nUsers: {users}\nActive: {active}\nQuestions: {qs}\nActive exams: {exams}\nAI tests generated: {ai_tests}")
    elif action == "users":
        rows = list((await session.execute(select(User).order_by(User.joined_at.desc()).limit(30))).scalars())
        if not rows: await cb.message.answer("No users yet."); return
        await cb.message.answer("👥 Latest users:\n" + "\n".join(
            f"{u.telegram_id} | {esc(u.full_name)} | {u.status} | access={u.access_granted}" for u in rows
        ))
    elif action == "addexam":
        await state.set_state(AdminFlow.add_exam)
        await cb.message.answer("Send the new exam name (e.g. SSC CGL). Send /cancel to stop.")
    elif action == "addq":
        exams = list((await session.execute(select(Exam).where(Exam.active.is_(True)))).scalars())
        if not exams: await cb.message.answer("Add an exam first."); return
        await state.update_data(admin_exam_ids=[e.id for e in exams])
        await state.set_state(AdminFlow.add_question)
        await cb.message.answer(
            "Send one question in this format (one message):\n"
            "EXAM: SSC CGL\nSUBJECT: Maths\nQUESTION: 2+2=?\nA: 3\nB: 4\nC: 5\nD: 6\nANSWER: B\nEXPLANATION: Because 2+2=4\n\n"
            "The EXAM name must match an existing exam."
        )
    elif action == "addmat":
        await state.set_state(AdminFlow.material)
        await cb.message.answer("Send material as: Title | https://link | optional description")
    elif action == "addmock":
        await state.set_state(AdminFlow.mock_test)
        await cb.message.answer("Send mock test as: Exam name | Test title | duration_minutes")
    elif action == "broadcast":
        await state.set_state(AdminFlow.broadcast)
        await cb.message.answer("Send the broadcast message. It will be sent to all non-banned users.")
    elif action == "maintenance":
        current = (await get_setting(session, "maintenance", str(MAINTENANCE_MODE).lower())).lower() == "true"
        await cb.message.answer(
            f"Maintenance is currently {'ON' if current else 'OFF'}.",
            reply_markup=inline([[("Turn ON", "adm:maint:on"), ("Turn OFF", "adm:maint:off")],
                                 [("Change message", "adm:maint:msg")]])
        )
    elif action == "maint:on":
        await set_setting(session, "maintenance", "true"); await cb.message.answer("Maintenance mode enabled.")
    elif action == "maint:off":
        await set_setting(session, "maintenance", "false"); await cb.message.answer("Maintenance mode disabled.")
    elif action == "maint:msg":
        await state.set_state(AdminFlow.maintenance_message); await cb.message.answer("Send the maintenance message.")
    elif action == "accesshelp":
        await cb.message.answer(
            "Admin commands:\n"
            "/ban TELEGRAM_ID\n/unban TELEGRAM_ID\n/grant TELEGRAM_ID\n/revoke TELEGRAM_ID\n"
            "/user TELEGRAM_ID\n/feature ai on|off\n/feature quiz on|off\n/feature mock on|off\n"
            "/feature materials on|off\n/feature aitest on|off\n/maintenance on|off\n"
            "For user IDs, use /user or the Users list. Set ADMIN_IDS in hosting environment."
        )
    elif action == "apikey":
        saved = await get_setting(session, "gemini_api_key", "")
        configured = bool(saved or GEMINI_API_KEY)
        source = "Admin panel" if saved else ("Render Environment" if GEMINI_API_KEY else "Not configured")
        await cb.message.answer(
            "🔑 <b>Gemini API configuration</b>\n"
            f"Status: {'Configured' if configured else 'Missing'}\n"
            f"Source: {esc(source)}\n\n"
            "Choose an action. Your key will be validated before saving, and the full key will never be displayed.",
            reply_markup=inline([
                [("➕ Add / replace key", "adm:apikey:set")],
                [("🧪 Test current key", "adm:apikey:test"), ("🗑 Remove saved key", "adm:apikey:remove")],
                [("↩️ Admin menu", "adm:back")]
            ])
        )
    elif action == "apikey:set":
        await state.set_state(AdminFlow.api_key)
        await cb.message.answer("Send the Gemini API key as your next message. It will be validated before saving. Send /cancel to stop.")
    elif action == "apikey:test":
        key = await current_api_key(session)
        if not key:
            await cb.message.answer("No API key is configured yet.")
        else:
            await cb.message.answer("🧪 Validating current key…")
            ok, detail = await validate_gemini_key(key)
            await cb.message.answer(("✅ " if ok else "❌ ") + esc(detail))
    elif action == "apikey:remove":
        await set_setting(session, "gemini_api_key", "")
        await cb.message.answer("Saved API key removed. If GEMINI_API_KEY exists in Render Environment, that key will be used as fallback.")
    elif action == "back":
        await cb.message.answer("🛠 <b>ExamYatra Admin Panel</b>", reply_markup=admin_keyboard())
    elif action == "features":
        status = {k: (await get_setting(session, "feature_" + k, "true")).lower() for k in FEATURE_NAMES}
        await cb.message.answer("⚙️ Feature switches (tap to toggle):", reply_markup=features_keyboard(status))
    elif action.startswith("feat:"):
        name = action.split(":", 1)[1]
        if name not in FEATURE_NAMES:
            await cb.message.answer("Unknown feature."); return
        current = (await get_setting(session, "feature_" + name, "true")).lower() == "true"
        await set_setting(session, "feature_" + name, "false" if current else "true")
        status = {k: (await get_setting(session, "feature_" + k, "true")).lower() for k in FEATURE_NAMES}
        status[name] = "false" if current else "true"
        await safe_edit(cb.message, "⚙️ Feature switches (tap to toggle):", features_keyboard(status))
    else:
        await cb.message.answer("Unknown admin action.")

@router.message(AdminFlow.api_key)
async def admin_save_api_key(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    if not db_user.is_admin:
        await state.clear()
        return
    key = (message.text or "").strip()
    if not key or key.startswith("/"):
        await message.answer("Please send a valid Gemini API key, or /cancel.")
        return
    # Best-effort deletion so the secret is not left visible in the Telegram chat.
    try:
        await message.delete()
    except Exception:
        pass
    await message.answer("🧪 Validating the key with Google…")
    ok, detail = await validate_gemini_key(key)
    if not ok:
        await message.answer("❌ " + esc(detail) + "\nThe key was NOT saved. Send another key or /cancel.")
        return
    await set_setting(session, "gemini_api_key", key)
    await state.clear()
    await message.answer("✅ Gemini API key validated and saved. AI tutor, image solving and AI tests are ready.")

@router.message(AdminFlow.maintenance_message)
async def admin_save_maintenance_message(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    if not db_user.is_admin:
        await state.clear()
        return
    value = (message.text or "").strip()
    if not value:
        await message.answer("Please send a non-empty maintenance message.")
        return
    await set_setting(session, "maintenance_message", value[:1000])
    await state.clear()
    await message.answer("✅ Maintenance message updated.")

@router.message(Command("myid"))
async def my_id(message: Message):
    await message.answer(f"Your Telegram user ID is: <code>{message.from_user.id}</code>\nSet this number in Render as ADMIN_IDS to enable the admin panel.")

@router.message(AdminFlow.add_exam)
async def admin_add_exam(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    if not db_user.is_admin: await state.clear(); return
    name = (message.text or "").strip()[:100]
    if not name: await message.answer("Please send a non-empty name."); return
    exists = (await session.execute(select(Exam).where(func.lower(Exam.name)==name.lower()))).scalar_one_or_none()
    if exists: await message.answer("That exam already exists."); return
    session.add(Exam(name=name))
    await state.clear()
    await message.answer(f"✅ Added exam: {esc(name)}", reply_markup=admin_keyboard())

@router.message(AdminFlow.add_question)
async def admin_add_question(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    if not db_user.is_admin: await state.clear(); return
    raw = message.text or ""
    def field(name):
        m = re.search(rf"^{name}\s*:\s*(.*)$", raw, re.I|re.M)
        return m.group(1).strip() if m else ""
    exam_name, subject_name, qtext = field("EXAM"), field("SUBJECT"), field("QUESTION")
    values = {k: field(k) for k in ("A","B","C","D")}
    ans, explanation = field("ANSWER").upper(), field("EXPLANATION")
    exam = (await session.execute(select(Exam).where(func.lower(Exam.name)==exam_name.lower(), Exam.active.is_(True)))).scalar_one_or_none()
    if not exam or not qtext or any(not values[k] for k in "ABCD") or ans not in LETTERS:
        await message.answer("Format invalid. Check EXAM name, QUESTION, A-D choices, and ANSWER: A/B/C/D."); return
    subject = None
    if subject_name:
        subject = (await session.execute(select(Subject).where(Subject.exam_id==exam.id, func.lower(Subject.name)==subject_name.lower()))).scalar_one_or_none()
        if not subject:
            subject = Subject(exam_id=exam.id, name=subject_name); session.add(subject); await session.flush()
    q = Question(exam_id=exam.id, subject_id=subject.id if subject else None, text=qtext, explanation=explanation or None)
    for i,k in enumerate(LETTERS):
        q.options.append(Option(position=i, text=values[k], correct=(k==ans)))
    session.add(q); await state.clear()
    await message.answer(f"✅ Question added to {esc(exam.name)}.", reply_markup=admin_keyboard())

@router.message(AdminFlow.material)
async def admin_add_material(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    if not db_user.is_admin: await state.clear(); return
    parts = [p.strip() for p in (message.text or "").split("|", 2)]
    if len(parts) < 2 or not parts[0] or not re.match(r"^https?://", parts[1]):
        await message.answer("Use: Title | https://link | optional description"); return
    session.add(Material(title=parts[0][:200], url=parts[1][:1000], description=parts[2] if len(parts)>2 else None))
    await state.clear(); await message.answer("✅ Study material added.")

@router.message(AdminFlow.mock_test)
async def admin_add_mock(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    if not db_user.is_admin: await state.clear(); return
    parts = [p.strip() for p in (message.text or "").split("|")]
    if len(parts) != 3 or not parts[2].isdigit() or int(parts[2]) < 1:
        await message.answer("Use: Exam name | Test title | duration_minutes"); return
    exam = (await session.execute(select(Exam).where(func.lower(Exam.name)==parts[0].lower(), Exam.active.is_(True)))).scalar_one_or_none()
    if not exam: await message.answer("Exam not found. Add/select an existing exam name."); return
    session.add(MockTest(exam_id=exam.id, title=parts[1][:160], duration=int(parts[2])))
    await state.clear(); await message.answer("✅ Mock test created. Add questions to it with /attach_question TEST_ID QUESTION_ID.")

@router.message(AdminFlow.broadcast)
async def admin_broadcast(message: Message, bot: Bot, session: AsyncSession, db_user: User, state: FSMContext):
    if not db_user.is_admin: await state.clear(); return
    text = message.text or message.caption or ""
    if not text:
        await message.answer("Please send a text broadcast."); return
    users = list((await session.execute(select(User).where(User.status != "banned"))).scalars())
    sent = failed = 0
    for u in users:
        try: await bot.send_message(u.telegram_id, esc(text)); sent += 1
        except (TelegramForbiddenError, TelegramBadRequest): failed += 1
        except Exception: failed += 1
        await asyncio.sleep(0.04)
    await state.clear()
    await message.answer(f"📣 Broadcast finished.\nSent: {sent}\nFailed: {failed}")

@router.message(F.text.startswith("/ban "))
async def admin_ban(message: Message, session: AsyncSession, db_user: User):
    if not db_user.is_admin: return
    await admin_user_flag(message, session, "status", "banned")

@router.message(F.text.startswith("/unban "))
async def admin_unban(message: Message, session: AsyncSession, db_user: User):
    if not db_user.is_admin: return
    await admin_user_flag(message, session, "status", "active")

@router.message(F.text.startswith("/grant "))
async def admin_grant(message: Message, session: AsyncSession, db_user: User):
    if not db_user.is_admin: return
    await admin_user_flag(message, session, "access_granted", True)

@router.message(F.text.startswith("/revoke "))
async def admin_revoke(message: Message, session: AsyncSession, db_user: User):
    if not db_user.is_admin: return
    await admin_user_flag(message, session, "access_granted", False)

async def admin_user_flag(message: Message, session: AsyncSession, field: str, value: Any):
    parts = (message.text or "").split()
    if len(parts) != 2 or not parts[1].isdigit():
        await message.answer(f"Usage: {parts[0]} TELEGRAM_ID"); return
    u = (await session.execute(select(User).where(User.telegram_id==int(parts[1])))).scalar_one_or_none()
    if not u: await message.answer("User not found."); return
    setattr(u, field, value)
    await message.answer(f"Updated user {u.telegram_id}: {field}={value}")

@router.message(F.text.startswith("/user "))
async def admin_user_lookup(message: Message, session: AsyncSession, db_user: User):
    if not db_user.is_admin: return
    parts=(message.text or "").split()
    if len(parts)!=2 or not parts[1].isdigit(): await message.answer("Usage: /user TELEGRAM_ID"); return
    u=(await session.execute(select(User).where(User.telegram_id==int(parts[1])))).scalar_one_or_none()
    if not u: await message.answer("User not found."); return
    await message.answer(f"User: {esc(u.full_name)}\nID: <code>{u.telegram_id}</code>\nStatus: {u.status}\nAccess: {u.access_granted}\nJoined: {u.joined_at}")

@router.message(Command("maintenance"))
async def admin_maintenance(message: Message, session: AsyncSession, db_user: User):
    if not db_user.is_admin: await message.answer("Admin only."); return
    parts=(message.text or "").split(maxsplit=1)
    if len(parts)!=2 or parts[1].lower() not in ("on","off"):
        await message.answer("Usage: /maintenance on|off"); return
    await set_setting(session, "maintenance", "true" if parts[1].lower()=="on" else "false")
    await message.answer(f"Maintenance mode {parts[1].upper()}.")

@router.message(Command("feature"))
async def admin_feature(message: Message, session: AsyncSession, db_user: User):
    if not db_user.is_admin: await message.answer("Admin only."); return
    parts=(message.text or "").split()
    if len(parts)!=3 or parts[1].lower() not in FEATURE_NAMES or parts[2].lower() not in ("on","off"):
        await message.answer("Usage: /feature " + "|".join(FEATURE_NAMES) + " on|off"); return
    await set_setting(session, "feature_"+parts[1].lower(), "true" if parts[2].lower()=="on" else "false")
    await message.answer(f"Feature {parts[1]} is {parts[2]}.")

@router.message(Command("attach_question"))
async def admin_attach_question(message: Message, session: AsyncSession, db_user: User):
    if not db_user.is_admin: await message.answer("Admin only."); return
    p=(message.text or "").split()
    if len(p)!=3 or not p[1].isdigit() or not p[2].isdigit():
        await message.answer("Usage: /attach_question TEST_ID QUESTION_ID"); return
    test=await session.get(MockTest,int(p[1])); q=await session.get(Question,int(p[2]))
    if not test or not q: await message.answer("Test or question not found."); return
    exists=(await session.execute(select(MockQuestion).where(MockQuestion.test_id==test.id,MockQuestion.question_id==q.id))).scalar_one_or_none()
    if exists: await message.answer("Question already attached."); return
    session.add(MockQuestion(test_id=test.id,question_id=q.id,position=int((await session.execute(select(func.count()).select_from(MockQuestion).where(MockQuestion.test_id==test.id))).scalar_one())))
    await message.answer("Question attached to mock test.")

@router.message(Command("add_exam"))
async def admin_add_exam_command(message: Message, session: AsyncSession, db_user: User):
    if not db_user.is_admin: await message.answer("Admin only."); return
    name=(message.text or "").partition(" ")[2].strip()
    if not name: await message.answer("Usage: /add_exam SSC CGL"); return
    exists=(await session.execute(select(Exam).where(func.lower(Exam.name)==name.lower()))).scalar_one_or_none()
    if exists: await message.answer("Exam already exists."); return
    session.add(Exam(name=name[:100])); await message.answer(f"Added exam: {esc(name)}")

@router.message(Command("add_material"))
async def admin_add_material_command(message: Message, session: AsyncSession, db_user: User):
    if not db_user.is_admin: await message.answer("Admin only."); return
    p=(message.text or "").partition(" ")[2].split("|",2)
    if len(p)<2 or not re.match(r"^https?://",p[1].strip()):
        await message.answer("Usage: /add_material Title | https://link | optional description"); return
    session.add(Material(title=p[0].strip()[:200],url=p[1].strip()[:1000],description=p[2].strip() if len(p)>2 else None))
    await message.answer("Study material added.")

@router.message(Command("add_question"))
async def admin_add_question_help(message: Message, db_user: User):
    if db_user.is_admin:
        await message.answer("Use Admin Panel → Add question for the guided format.")

# ------------------------------ Infrastructure ------------------------------
async def middleware(handler, event, data):
    tg_user = event.from_user if hasattr(event, "from_user") else None
    if not tg_user:
        return await handler(event, data)
    async with Session() as session:
        user = await get_user(session, tg_user)
        data["session"] = session
        data["db_user"] = user
        try:
            result = await handler(event, data)
            await session.commit()
            return result
        except Exception:
            await session.rollback()
            raise

class DBMiddleware:
    async def __call__(self, handler, event, data):
        return await middleware(handler, event, data)

async def on_error(event):
    log.error("Unhandled update error: %r", event.exception, exc_info=(type(event.exception), event.exception, event.exception.__traceback__))
    try:
        if event.update.callback_query:
            await event.update.callback_query.answer("Something went wrong. Please try again.", show_alert=True)
        elif event.update.message:
            await event.update.message.answer("Something went wrong. Please try again.")
    except Exception:
        pass
    return True

async def seed_default_exams():
    async with Session() as session:
        names = ["SSC", "Railway", "Banking", "Bihar Police", "BPSC", "UPSC", "Teaching Exams"]
        for name in names:
            found = (await session.execute(select(Exam).where(func.lower(Exam.name)==name.lower()))).scalar_one_or_none()
            if not found: session.add(Exam(name=name))
        await session.commit()

async def expiry_loop():
    while True:
        try:
            async with Session() as session:
                attempts = list((await session.execute(select(MockAttempt).where(MockAttempt.status=="in_progress", MockAttempt.deadline_at <= now_utc()))).scalars())
                for attempt in attempts:
                    # Mark expired attempts completed; final result is shown the next time user interacts.
                    attempt.status = "completed"
                await session.commit()
        except Exception:
            log.exception("Mock expiry task failed")
        await asyncio.sleep(30)

async def main():
    if not BOT_TOKEN or ":" not in BOT_TOKEN:
        raise SystemExit("BOT_TOKEN is missing/invalid. Set it in your host's environment variables.")
    await ensure_schema()
    await seed_default_exams()
    if not ADMIN_IDS:
        log.warning("ADMIN_IDS is empty. Set ADMIN_IDS to your Telegram numeric user ID; /admin will otherwise be unavailable.")
    dp.message.middleware(DBMiddleware())
    dp.callback_query.middleware(DBMiddleware())
    dp.errors.register(on_error)
    bot = Bot(BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    await bot.set_my_commands([
        BotCommand(command="start", description="Start ExamYatra"),
        BotCommand(command="menu", description="Show main menu"),
        BotCommand(command="help", description="Help and support"),
        BotCommand(command="profile", description="My profile"),
        BotCommand(command="settings", description="Answer style and language"),
        BotCommand(command="cancel", description="Cancel current action"),
        BotCommand(command="admin", description="Admin panel"),
        BotCommand(command="myid", description="Show your Telegram ID"),
        BotCommand(command="delete_me", description="Delete my data"),
    ])
    expiry_task = asyncio.create_task(expiry_loop())

    # Render Web Services must bind to PORT. This lightweight HTTP server provides
    # / and /health while the Telegram bot continues using long polling.
    async def health(_request):
        return web.json_response({"status": "ok", "service": "ExamYatra"})

    app = web.Application()
    app.router.add_get("/", health)
    app.router.add_get("/health", health)
    runner = web.AppRunner(app)
    await runner.setup()
    port = int(os.getenv("PORT", "10000"))
    site = web.TCPSite(runner, host="0.0.0.0", port=port)
    await site.start()
    log.info("Health server listening on 0.0.0.0:%s", port)

    try:
        me = await bot.get_me()
        log.info("ExamYatra started as @%s", me.username)
        await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types(), close_bot_session=True)
    except TelegramUnauthorizedError:
        log.error("Telegram rejected BOT_TOKEN. Check the token from @BotFather.")
        raise
    finally:
        expiry_task.cancel()
        await runner.cleanup()
        await engine.dispose()

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        log.info("Bot stopped.")
