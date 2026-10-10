from __future__ import annotations

import asyncio
import base64
import html
import io
import json
import logging
import os
import random
import re
import time
import sqlite3
import tempfile
import shutil
from pathlib import Path
from decimal import Decimal
from datetime import datetime, timedelta, timezone, date
from typing import Any, Awaitable, Callable

import httpx
from aiohttp import web
from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode, ChatMemberStatus
from aiogram.exceptions import TelegramBadRequest, TelegramForbiddenError, TelegramUnauthorizedError, TelegramAPIError
from aiogram.filters import Command, CommandStart, StateFilter
from aiogram.dispatcher.event.bases import SkipHandler
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.types import (
    BotCommand, BotCommandScopeChat, BotCommandScopeDefault, BufferedInputFile, CallbackQuery,
    InlineKeyboardButton, InlineKeyboardMarkup, KeyboardButton, Message, ReplyKeyboardMarkup,
    ReplyKeyboardRemove,
)
from dotenv import load_dotenv
from sqlalchemy import (
    BigInteger, Boolean, DateTime, Float, ForeignKey, Integer, String, Text,
    UniqueConstraint, select, func, update, inspect as sa_inspect, text as sa_text, or_, and_
)
from sqlalchemy.exc import IntegrityError
from sqlalchemy.ext.asyncio import AsyncAttrs, AsyncSession, async_sessionmaker, create_async_engine
from sqlalchemy.engine import make_url
from sqlalchemy.orm import DeclarativeBase, Mapped, mapped_column, relationship

load_dotenv()
logging.basicConfig(
    level=getattr(logging, os.getenv("LOG_LEVEL", "INFO").upper(), logging.INFO),
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
)
log = logging.getLogger("examyatra")

# ============================ Configuration ============================
BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
ADMIN_IDS = {int(x.strip()) for x in os.getenv("ADMIN_IDS", "").split(",") if x.strip().isdigit()}
ENV_GEMINI_API_KEY = os.getenv("GEMINI_API_KEY", "").strip()
GEMINI_MODEL = os.getenv("GEMINI_MODEL", "gemini-2.5-flash").strip() or "gemini-2.5-flash"
ENV_MAINTENANCE = os.getenv("MAINTENANCE_MODE", "false").lower() in {"1", "true", "yes", "on"}
ENV_MAINTENANCE_MESSAGE = os.getenv("MAINTENANCE_MESSAGE", "ExamYatra is being updated. Please try again soon.").strip()
ENV_SUPPORT_CONTACT = os.getenv("SUPPORT_CONTACT", "").strip()
MAX_IMAGE_BYTES = 8 * 1024 * 1024
MAX_DB_BACKUP_BYTES = int(os.getenv("MAX_DB_BACKUP_MB", "18")) * 1024 * 1024
DB_BACKUP_LOCK = asyncio.Lock()
LETTERS = "ABCD"
TG_TEXT_LIMIT = 3800
STYLE_SHORT, STYLE_DETAILED = "short", "detailed"
ANSWER_STYLES = (STYLE_SHORT, STYLE_DETAILED)
AI_TEST_MIN, AI_TEST_MAX_HARD = 1, 50
AI_TEST_BATCH = 10
AI_TEST_MAX_CALLS = 14
HISTORY_PAGE = 8
REVIEW_PAGE = 5
ADMIN_PAGE = 10
AI_TEST_DIFFICULTIES = ("easy", "medium", "hard", "mixed")
COMMON_TEST_TOPICS = [
    "BPSC", "Bihar Police", "SSC", "Railway", "Banking", "UPSC",
    "General Knowledge", "Indian History", "Geography", "Science",
    "Mathematics", "Reasoning", "Current Affairs",
]
IST = timezone(timedelta(hours=5, minutes=30))
UTR_MIN, UTR_MAX = 6, 40
BUTTON_LABEL_LIMIT = 48          # longer options get a concise label + "Show full options" toggle
TIERS = ("free", "trial", "premium", "admin")
FEATURE_KEYS = ("ai", "image", "aitest", "quiz", "mock", "materials", "leaderboard", "payments")
LIMIT_KEYS = ("ai_daily", "image_daily", "aitest_daily", "aitest_max_q", "quiz_daily", "mock_daily", "materials")
DEFAULT_POLICIES: dict[str, dict[str, int]] = {
    # -1 = unlimited, 0 = not allowed
    "free":    {"ai_daily": 3,  "image_daily": 1,  "aitest_daily": 1,  "aitest_max_q": 10, "quiz_daily": 10, "mock_daily": 0,  "materials": 0},
    "trial":   {"ai_daily": 10, "image_daily": 5,  "aitest_daily": 3,  "aitest_max_q": 20, "quiz_daily": 50, "mock_daily": 2,  "materials": 1},
    "premium": {"ai_daily": -1, "image_daily": -1, "aitest_daily": -1, "aitest_max_q": 50, "quiz_daily": -1, "mock_daily": -1, "materials": 1},
    "admin":   {"ai_daily": -1, "image_daily": -1, "aitest_daily": -1, "aitest_max_q": 50, "quiz_daily": -1, "mock_daily": -1, "materials": 1},
}
Q_DRAFT, Q_PENDING, Q_APPROVED, Q_REJECTED = "draft", "pending", "approved", "rejected"
Q_STATUSES = (Q_DRAFT, Q_PENDING, Q_APPROVED, Q_REJECTED)
PAY_AWAITING_UTR, PAY_AWAITING_SHOT, PAY_PENDING, PAY_APPROVED, PAY_REJECTED, PAY_CANCELLED = (
    "awaiting_utr", "awaiting_screenshot", "pending_review", "approved", "rejected", "cancelled")
MATERIAL_FORMATS = {"pdf": "📄 PDF", "doc": "📝 Document", "image": "🖼 Image", "link": "🔗 Web Link", "notes": "🗒 Notes"}
DEFAULT_MATERIAL_SUBJECTS = ["General Knowledge", "General Studies", "Indian History", "Indian Geography",
                             "Indian Constitution", "Science", "Mathematics", "Reasoning", "Current Affairs",
                             "Previous-Year Question Papers", "Practice Notes"]


def normalize_database_url(url: str) -> str:
    """Accept the URL formats hosts hand out and map them to async drivers. Never falls back to SQLite silently."""
    url = (url or "").strip()
    if not url:
        return "sqlite+aiosqlite:///./examyatra.db"
    if url.startswith("postgres://"):
        url = "postgresql://" + url[len("postgres://"):]
    if url.startswith("postgresql://"):
        url = "postgresql+asyncpg://" + url[len("postgresql://"):]
    if url.startswith("postgresql+psycopg2://"):
        url = "postgresql+asyncpg://" + url[len("postgresql+psycopg2://"):]
    if url.startswith("sqlite:///"):
        url = "sqlite+aiosqlite:///" + url[len("sqlite:///"):]
    if url.startswith("postgresql+asyncpg://") and "sslmode=" in url:
        # asyncpg does not understand sslmode=; use ssl=require instead.
        url = re.sub(r"sslmode=\w+", "ssl=require", url)
    return url


DATABASE_URL = normalize_database_url(os.getenv("DATABASE_URL", ""))
IS_SQLITE = DATABASE_URL.startswith("sqlite")


def now_utc() -> datetime:
    return datetime.now(timezone.utc).replace(tzinfo=None)


def today_ist() -> str:
    """One consistent daily-reset policy: the calendar day in India Standard Time."""
    return datetime.now(IST).strftime("%Y-%m-%d")


def fmt_dt(dt: datetime | None) -> str:
    if not dt:
        return "—"
    return dt.replace(tzinfo=timezone.utc).astimezone(IST).strftime("%d %b %Y, %H:%M IST")


def fmt_date(dt: datetime | None) -> str:
    if not dt:
        return "—"
    return dt.replace(tzinfo=timezone.utc).astimezone(IST).strftime("%d %b %Y")


# ============================ ORM models ============================
class Base(AsyncAttrs, DeclarativeBase):
    pass


class User(Base):
    __tablename__ = "users"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    telegram_id: Mapped[int] = mapped_column(BigInteger, unique=True, index=True)
    username: Mapped[str | None] = mapped_column(String(64), nullable=True)
    full_name: Mapped[str] = mapped_column(String(160), default="Student")
    joined_at: Mapped[datetime] = mapped_column(DateTime, default=now_utc)
    last_active_at: Mapped[datetime] = mapped_column(DateTime, default=now_utc)
    selected_exam_id: Mapped[int | None] = mapped_column(ForeignKey("exams.id", ondelete="SET NULL"), nullable=True)
    status: Mapped[str] = mapped_column(String(16), default="active")          # active | banned
    access_granted: Mapped[bool] = mapped_column(Boolean, default=True)
    is_admin: Mapped[bool] = mapped_column(Boolean, default=False)
    language: Mapped[str] = mapped_column(String(2), default="en")
    ai_date: Mapped[str] = mapped_column(String(10), default="")               # legacy counters (kept, no longer used)
    ai_count: Mapped[int] = mapped_column(Integer, default=0)
    answer_style: Mapped[str] = mapped_column(String(16), default=STYLE_SHORT, server_default=STYLE_SHORT)
    # v3 — trial & subscription (added by ensure_schema for existing databases)
    trial_started_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    trial_ends_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    trial_status: Mapped[str] = mapped_column(String(16), default="none", server_default="none")   # none|active|expired|revoked
    trial_extended_by_admin: Mapped[int] = mapped_column(Integer, default=0, server_default="0")   # extra days granted
    subscription_status: Mapped[str] = mapped_column(String(16), default="none", server_default="none")  # none|active|expired|revoked
    subscription_expiry: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)         # None + active = lifetime
    current_plan: Mapped[str | None] = mapped_column(String(64), nullable=True)
    channel_verified_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    limit_overrides: Mapped[str] = mapped_column(Text, default="{}", server_default="{}")          # JSON {limit_key: int}
    active_test_id: Mapped[int | None] = mapped_column(Integer, nullable=True)
    notes: Mapped[str | None] = mapped_column(Text, nullable=True)

    def overrides(self) -> dict[str, int]:
        try:
            d = json.loads(self.limit_overrides or "{}")
            return {k: int(v) for k, v in d.items() if k in LIMIT_KEYS}
        except (TypeError, ValueError):
            return {}


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
    # v3 verification workflow. Legacy rows are migrated to "pending" (never auto-approved).
    status: Mapped[str] = mapped_column(String(16), default=Q_PENDING, server_default=Q_PENDING, index=True)
    topic: Mapped[str | None] = mapped_column(String(120), nullable=True)
    source: Mapped[str | None] = mapped_column(String(300), nullable=True)
    reference_url: Mapped[str | None] = mapped_column(String(1000), nullable=True)
    verified_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    verified_by: Mapped[int | None] = mapped_column(BigInteger, nullable=True)
    created_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    text_hash: Mapped[str | None] = mapped_column(String(64), nullable=True, index=True)
    options: Mapped[list["Option"]] = relationship(back_populates="question", cascade="all, delete-orphan",
                                                   lazy="selectin", order_by="Option.position")


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
    # v3 metadata
    subject: Mapped[str | None] = mapped_column(String(100), nullable=True, index=True)
    topic: Mapped[str | None] = mapped_column(String(120), nullable=True)
    language: Mapped[str] = mapped_column(String(2), default="en", server_default="en")
    fmt: Mapped[str] = mapped_column(String(16), default="link", server_default="link")
    file_id: Mapped[str | None] = mapped_column(String(300), nullable=True)
    file_name: Mapped[str | None] = mapped_column(String(200), nullable=True)
    source: Mapped[str | None] = mapped_column(String(300), nullable=True)
    origin: Mapped[str] = mapped_column(String(16), default="admin", server_default="admin")   # admin | ai
    created_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)


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
    """Legacy mock attempts (pre-v3). Kept read-only so old history is preserved; new mock attempts
    run through the unified TestSession engine (AiTest with kind='mock')."""
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


class AiTest(Base):
    """Unified test session. kind='ai' (Gemini-generated practice) or kind='mock' (admin mock test built
    from approved bank questions). Questions are immutable snapshots with the DISPLAYED option order."""
    __tablename__ = "ai_tests"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), index=True)
    topic: Mapped[str] = mapped_column(String(200))
    requested_count: Mapped[int] = mapped_column(Integer)
    question_count: Mapped[int] = mapped_column(Integer, default=0)
    language: Mapped[str] = mapped_column(String(2), default="en")
    difficulty: Mapped[str] = mapped_column(String(16), default="mixed")
    status: Mapped[str] = mapped_column(String(16), default="in_progress", index=True)  # in_progress|completed|abandoned|expired
    current_index: Mapped[int] = mapped_column(Integer, default=0)
    correct: Mapped[int] = mapped_column(Integer, default=0)
    incorrect: Mapped[int] = mapped_column(Integer, default=0)
    unanswered: Mapped[int] = mapped_column(Integer, default=0)
    score: Mapped[float] = mapped_column(Float, default=0.0)
    accuracy: Mapped[float] = mapped_column(Float, default=0.0)
    created_at: Mapped[datetime] = mapped_column(DateTime, default=now_utc)
    started_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    completed_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    # v3
    kind: Mapped[str] = mapped_column(String(8), default="ai", server_default="ai")
    mode: Mapped[str] = mapped_column(String(10), default="practice", server_default="practice")  # practice|exam
    mock_test_id: Mapped[int | None] = mapped_column(Integer, nullable=True)
    deadline_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    chat_id: Mapped[int | None] = mapped_column(BigInteger, nullable=True)
    message_id: Mapped[int | None] = mapped_column(BigInteger, nullable=True)
    show_full: Mapped[bool] = mapped_column(Boolean, default=False, server_default="0")


class AiTestQuestion(Base):
    __tablename__ = "ai_test_questions"
    __table_args__ = (UniqueConstraint("test_id", "position"),)
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    test_id: Mapped[int] = mapped_column(ForeignKey("ai_tests.id", ondelete="CASCADE"), index=True)
    position: Mapped[int] = mapped_column(Integer)
    text: Mapped[str] = mapped_column(Text)
    options_json: Mapped[str] = mapped_column(Text)          # JSON list of exactly 4 strings, in DISPLAYED order
    correct_index: Mapped[int] = mapped_column(Integer)      # index into options_json (displayed order)
    explanation: Mapped[str | None] = mapped_column(Text, nullable=True)
    difficulty: Mapped[str] = mapped_column(String(16), default="medium")
    selected_index: Mapped[int | None] = mapped_column(Integer, nullable=True)
    answered_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    source_question_id: Mapped[int | None] = mapped_column(Integer, nullable=True)   # v3: bank question id for mock tests
    verified: Mapped[bool] = mapped_column(Boolean, default=False, server_default="0")  # v3: admin-approved origin

    def options(self) -> list[str]:
        try:
            opts = json.loads(self.options_json)
            return [str(o) for o in opts] if isinstance(opts, list) else []
        except (TypeError, ValueError):
            return []


class RequiredChannel(Base):
    __tablename__ = "required_channels"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    chat_ref: Mapped[str] = mapped_column(String(120))        # "@username" or numeric id as string
    title: Mapped[str | None] = mapped_column(String(160), nullable=True)
    invite_url: Mapped[str | None] = mapped_column(String(500), nullable=True)
    enabled: Mapped[bool] = mapped_column(Boolean, default=True)
    created_at: Mapped[datetime] = mapped_column(DateTime, default=now_utc)


class PaymentRequest(Base):
    __tablename__ = "payment_requests"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), index=True)
    plan_name: Mapped[str] = mapped_column(String(64))
    amount: Mapped[float] = mapped_column(Float)
    validity_days: Mapped[int] = mapped_column(Integer)       # 0 = lifetime
    status: Mapped[str] = mapped_column(String(24), default=PAY_AWAITING_UTR, index=True)
    utr: Mapped[str | None] = mapped_column(String(64), nullable=True, unique=True)
    screenshot_file_id: Mapped[str | None] = mapped_column(String(300), nullable=True)
    screenshot_meta: Mapped[str | None] = mapped_column(Text, nullable=True)
    created_at: Mapped[datetime] = mapped_column(DateTime, default=now_utc)
    submitted_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    decided_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    decided_by: Mapped[int | None] = mapped_column(BigInteger, nullable=True)
    reject_reason: Mapped[str | None] = mapped_column(Text, nullable=True)
    admin_message_ids: Mapped[str] = mapped_column(Text, default="[]")


class UsageCounter(Base):
    __tablename__ = "usage_counters"
    __table_args__ = (UniqueConstraint("user_id", "day", "feature"),)
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), index=True)
    day: Mapped[str] = mapped_column(String(10), index=True)
    feature: Mapped[str] = mapped_column(String(24))
    count: Mapped[int] = mapped_column(Integer, default=0)


class AuditLog(Base):
    __tablename__ = "audit_logs"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    at: Mapped[datetime] = mapped_column(DateTime, default=now_utc, index=True)
    actor_tg_id: Mapped[int | None] = mapped_column(BigInteger, nullable=True)
    action: Mapped[str] = mapped_column(String(64), index=True)
    target: Mapped[str | None] = mapped_column(String(120), nullable=True)
    details: Mapped[str | None] = mapped_column(Text, nullable=True)


engine = create_async_engine(DATABASE_URL, pool_pre_ping=True)
Session = async_sessionmaker(engine, expire_on_commit=False)
router = Router()
dp = Dispatcher()
dp.include_router(router)


# ============================ FSM states ============================
class AdminFlow(StatesGroup):
    add_exam = State()
    add_question = State()
    edit_question = State()
    search_question = State()
    broadcast = State()
    material_meta = State()
    material_file = State()
    mock_test = State()
    api_key = State()
    maintenance_message = State()
    support_contact = State()
    channel_add = State()
    channel_invite = State()
    user_lookup = State()
    user_action_value = State()
    setting_value = State()
    reject_reason = State()
    db_restore_upload = State()


class TestFlow(StatesGroup):
    topic = State()
    custom_topic = State()
    count = State()
    custom_count = State()
    difficulty = State()
    generating = State()


class PaymentFlow(StatesGroup):
    utr = State()
    screenshot = State()


# ============================ Schema migration ============================
# (table, column, DDL fragment). Only ADD COLUMN — never drop, never recreate. Safe to re-run.
SCHEMA_ADDITIONS: list[tuple[str, str, str]] = [
    ("users", "answer_style", "VARCHAR(16) NOT NULL DEFAULT 'short'"),
    ("users", "trial_started_at", "TIMESTAMP NULL"),
    ("users", "trial_ends_at", "TIMESTAMP NULL"),
    ("users", "trial_status", "VARCHAR(16) NOT NULL DEFAULT 'none'"),
    ("users", "trial_extended_by_admin", "INTEGER NOT NULL DEFAULT 0"),
    ("users", "subscription_status", "VARCHAR(16) NOT NULL DEFAULT 'none'"),
    ("users", "subscription_expiry", "TIMESTAMP NULL"),
    ("users", "current_plan", "VARCHAR(64) NULL"),
    ("users", "channel_verified_at", "TIMESTAMP NULL"),
    ("users", "limit_overrides", "TEXT NOT NULL DEFAULT '{}'"),
    ("users", "active_test_id", "INTEGER NULL"),
    ("users", "notes", "TEXT NULL"),
    ("questions", "status", "VARCHAR(16) NOT NULL DEFAULT 'pending'"),
    ("questions", "topic", "VARCHAR(120) NULL"),
    ("questions", "source", "VARCHAR(300) NULL"),
    ("questions", "reference_url", "VARCHAR(1000) NULL"),
    ("questions", "verified_at", "TIMESTAMP NULL"),
    ("questions", "verified_by", "BIGINT NULL"),
    ("questions", "created_at", "TIMESTAMP NULL"),
    ("questions", "text_hash", "VARCHAR(64) NULL"),
    ("materials", "subject", "VARCHAR(100) NULL"),
    ("materials", "topic", "VARCHAR(120) NULL"),
    ("materials", "language", "VARCHAR(2) NOT NULL DEFAULT 'en'"),
    ("materials", "fmt", "VARCHAR(16) NOT NULL DEFAULT 'link'"),
    ("materials", "file_id", "VARCHAR(300) NULL"),
    ("materials", "file_name", "VARCHAR(200) NULL"),
    ("materials", "source", "VARCHAR(300) NULL"),
    ("materials", "origin", "VARCHAR(16) NOT NULL DEFAULT 'admin'"),
    ("materials", "created_at", "TIMESTAMP NULL"),
    ("ai_tests", "kind", "VARCHAR(8) NOT NULL DEFAULT 'ai'"),
    ("ai_tests", "mode", "VARCHAR(10) NOT NULL DEFAULT 'practice'"),
    ("ai_tests", "mock_test_id", "INTEGER NULL"),
    ("ai_tests", "deadline_at", "TIMESTAMP NULL"),
    ("ai_tests", "chat_id", "BIGINT NULL"),
    ("ai_tests", "message_id", "BIGINT NULL"),
    ("ai_tests", "show_full", "BOOLEAN NOT NULL DEFAULT 0"),
    ("ai_test_questions", "source_question_id", "INTEGER NULL"),
    ("ai_test_questions", "verified", "BOOLEAN NOT NULL DEFAULT 0"),
]


def normalize_question_text(text: str) -> str:
    return re.sub(r"[^\w\u0900-\u097F]+", " ", (text or "").lower()).strip()


def question_hash(text: str) -> str:
    import hashlib
    return hashlib.sha256(normalize_question_text(text).encode("utf-8")).hexdigest()[:40]


async def ensure_schema() -> None:
    """create_all() creates missing TABLES; missing COLUMNS are added with ALTER TABLE. Then one-off data
    back-fills that are idempotent. Nothing is ever dropped."""
    async with engine.begin() as conn:
        await conn.run_sync(Base.metadata.create_all)

        def _columns(sync_conn, table: str) -> set[str]:
            return {c["name"] for c in sa_inspect(sync_conn).get_columns(table)}

        cache: dict[str, set[str]] = {}
        for table, column, ddl in SCHEMA_ADDITIONS:
            if table not in cache:
                cache[table] = await conn.run_sync(_columns, table)
            if column not in cache[table]:
                if not IS_SQLITE:
                    ddl = ddl.replace("DEFAULT 0", "DEFAULT FALSE") if "BOOLEAN" in ddl else ddl
                log.info("Migrating: adding column %s.%s", table, column)
                await conn.execute(sa_text(f"ALTER TABLE {table} ADD COLUMN {column} {ddl}"))
                cache[table].add(column)
    # Data back-fills (idempotent; only touch rows that still have NULL/empty values).
    async with Session() as s:
        await s.execute(update(Question).where(Question.created_at.is_(None)).values(created_at=now_utc()))
        await s.execute(update(Material).where(Material.created_at.is_(None)).values(created_at=now_utc()))
        rows = list((await s.execute(select(Question.id, Question.text).where(Question.text_hash.is_(None)))).all())
        for qid, qtext in rows:
            await s.execute(update(Question).where(Question.id == qid).values(text_hash=question_hash(qtext)))
        # Legacy sessions created before kind/chat tracking existed stay "ai"/"practice" — correct for them.
        await s.commit()
    if IS_SQLITE:
        async with engine.begin() as conn:
            await conn.execute(sa_text("PRAGMA foreign_keys=ON"))



# ============================ Small helpers ============================
def esc(value: Any) -> str:
    return html.escape(str(value if value is not None else ""))


def is_admin_id(tg_id: int) -> bool:
    return tg_id in ADMIN_IDS


def inline(rows: list[list[tuple[str, str]]]) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=t[:64], callback_data=d[:64]) for t, d in row] for row in rows if row
    ])


def url_button_rows(rows: list[list[tuple[str, str, bool]]]) -> InlineKeyboardMarkup:
    """rows of (text, data_or_url, is_url)."""
    kb = []
    for row in rows:
        r = []
        for t, d, is_url in row:
            r.append(InlineKeyboardButton(text=t[:64], url=d) if is_url else InlineKeyboardButton(text=t[:64], callback_data=d[:64]))
        kb.append(r)
    return InlineKeyboardMarkup(inline_keyboard=kb)


def parse_int(value: str, default: int | None = None) -> int | None:
    try:
        return int(str(value).strip())
    except (TypeError, ValueError):
        return default


async def audit(session: AsyncSession, actor: int | None, action: str, target: str | None = None, details: str | None = None) -> None:
    session.add(AuditLog(actor_tg_id=actor, action=action[:64], target=(target or "")[:120] or None, details=details))


# ============================ Settings store (DB-backed, cached) ============================
_SETTINGS_CACHE: dict[str, tuple[float, str | None]] = {}
SETTINGS_TTL = 20.0


async def get_setting(session: AsyncSession, key: str, default: str = "") -> str:
    hit = _SETTINGS_CACHE.get(key)
    if hit and time.monotonic() - hit[0] < SETTINGS_TTL:
        return hit[1] if hit[1] is not None else default
    row = await session.get(Setting, key)
    val = row.value if row else None
    _SETTINGS_CACHE[key] = (time.monotonic(), val)
    return val if val is not None else default


async def set_setting(session: AsyncSession, key: str, value: str) -> None:
    row = await session.get(Setting, key)
    if row:
        row.value = value
    else:
        session.add(Setting(key=key, value=value))
    await session.flush()
    _SETTINGS_CACHE[key] = (time.monotonic(), value)


async def setting_bool(session: AsyncSession, key: str, default: bool) -> bool:
    v = await get_setting(session, key, "")
    if v == "":
        return default
    return v.lower() in {"1", "true", "yes", "on"}


async def setting_int(session: AsyncSession, key: str, default: int) -> int:
    v = parse_int(await get_setting(session, key, ""), None)
    return default if v is None else v


async def setting_float(session: AsyncSession, key: str, default: float) -> float:
    try:
        return float(await get_setting(session, key, "") or default)
    except ValueError:
        return default


async def feature_enabled(session: AsyncSession, key: str) -> bool:
    return await setting_bool(session, f"feature:{key}", True)


async def maintenance_on(session: AsyncSession) -> bool:
    return await setting_bool(session, "maintenance", ENV_MAINTENANCE)


async def support_contact(session: AsyncSession) -> str:
    return (await get_setting(session, "support_contact", ENV_SUPPORT_CONTACT)).strip()


async def current_api_key(session: AsyncSession) -> str:
    return (await get_setting(session, "gemini_api_key", "")).strip() or ENV_GEMINI_API_KEY


def support_rows(contact: str) -> list[list[tuple[str, str, bool]]]:
    """Contact Admin button when a contact is configured (username → t.me link)."""
    if not contact:
        return []
    c = contact.strip()
    if c.startswith("@"):
        return [[("📨 Contact Admin", f"https://t.me/{c[1:]}", True)]]
    if c.startswith("http"):
        return [[("📨 Contact Admin", c, True)]]
    return [[("📨 Contact Admin", "info:contact", False)]]


# ============================ Usage policies & entitlements ============================
async def load_policies(session: AsyncSession) -> dict[str, dict[str, int]]:
    policies = {t: dict(v) for t, v in DEFAULT_POLICIES.items()}
    raw = await get_setting(session, "policies", "")
    if raw:
        try:
            saved = json.loads(raw)
            for tier, limits in saved.items():
                if tier in policies and isinstance(limits, dict):
                    for k, v in limits.items():
                        if k in LIMIT_KEYS:
                            policies[tier][k] = int(v)
        except (TypeError, ValueError):
            log.warning("Ignoring malformed policies setting")
    return policies


async def save_policy(session: AsyncSession, tier: str, key: str, value: int) -> None:
    policies = await load_policies(session)
    policies[tier][key] = value
    await set_setting(session, "policies", json.dumps(policies))


def refresh_entitlements(user: User) -> None:
    """Derive expired states from timestamps. Pure function of stored data; never deletes anything."""
    now = now_utc()
    if user.trial_status == "active" and user.trial_ends_at and user.trial_ends_at <= now:
        user.trial_status = "expired"
    if user.subscription_status == "active" and user.subscription_expiry and user.subscription_expiry <= now:
        user.subscription_status = "expired"


def user_tier(user: User) -> str:
    refresh_entitlements(user)
    if user.is_admin:
        return "admin"
    if user.subscription_status == "active":
        return "premium"
    if user.trial_status == "active":
        return "trial"
    return "free"


TIER_LABEL = {"free": "Free (no active plan)", "trial": "Free Trial", "premium": "Premium", "admin": "Administrator"}


async def effective_limits(session: AsyncSession, user: User) -> dict[str, int]:
    tier = user_tier(user)
    limits = dict((await load_policies(session))[tier])
    limits.update(user.overrides())     # per-user admin overrides take precedence
    return limits


async def usage_today(session: AsyncSession, user: User, feature: str) -> int:
    row = (await session.execute(select(UsageCounter).where(
        UsageCounter.user_id == user.id, UsageCounter.day == today_ist(), UsageCounter.feature == feature))).scalar_one_or_none()
    return row.count if row else 0


async def record_usage(session: AsyncSession, user: User, feature: str, amount: int = 1) -> None:
    day = today_ist()
    row = (await session.execute(select(UsageCounter).where(
        UsageCounter.user_id == user.id, UsageCounter.day == day, UsageCounter.feature == feature))).scalar_one_or_none()
    if row:
        row.count += amount
    else:
        session.add(UsageCounter(user_id=user.id, day=day, feature=feature, count=amount))
    await session.flush()


def limit_text(v: int) -> str:
    return "unlimited" if v < 0 else ("not included" if v == 0 else str(v))


async def check_quota(session: AsyncSession, user: User, limit_key: str, feature: str) -> tuple[bool, str]:
    """Returns (allowed, message). Does NOT charge; call record_usage() after the work succeeded."""
    limits = await effective_limits(session, user)
    cap = limits.get(limit_key, 0)
    if cap < 0:
        return True, ""
    used = await usage_today(session, user, feature)
    if cap == 0 or used >= cap:
        return False, await limit_reached_text(session, user, limit_key, cap, used)
    return True, ""


async def limit_reached_text(session: AsyncSession, user: User, limit_key: str, cap: int, used: int) -> str:
    tier = user_tier(user)
    name = {"ai_daily": "AI Tutor requests", "image_daily": "image solves", "aitest_daily": "AI tests",
            "quiz_daily": "quiz questions", "mock_daily": "mock tests", "materials": "study materials"}.get(limit_key, limit_key)
    if cap == 0:
        head = f"🔒 <b>{esc(name).capitalize()}</b> are not included in your current plan (<i>{TIER_LABEL[tier]}</i>)."
    else:
        head = f"⏳ <b>Daily limit reached</b> — {used}/{cap} {esc(name)} used today (plan: <i>{TIER_LABEL[tier]}</i>).\nCounters reset at midnight IST."
    if tier in ("free", "trial"):
        head += "\n\n💳 Upgrade to <b>Exam Yatra Premium</b> for unlimited usage — open 💳 Subscription."
    return head


# ============================ HTML formatting (Gemini Markdown → Telegram HTML) ============================
_TAG_RE = re.compile(r"<(/?)(b|i|u|s|code|pre|a|tg-spoiler|blockquote)\b[^>]*>")


def md_to_html(text: str) -> str:
    text = (text or "").replace("\r\n", "\n")
    text = re.sub(r"```[a-zA-Z0-9_+-]*\n?(.*?)```", lambda m: f"<pre>{html.escape(m.group(1).strip())}</pre>", text, flags=re.S)
    parts = re.split(r"(<pre>.*?</pre>)", text, flags=re.S)
    out: list[str] = []
    for part in parts:
        if part.startswith("<pre>"):
            out.append(part); continue
        p = html.escape(part)
        p = re.sub(r"`([^`\n]+)`", r"<code>\1</code>", p)
        p = re.sub(r"^\s{0,3}#{1,6}\s*(.+)$", r"<b>\1</b>", p, flags=re.M)
        p = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", p, flags=re.S)
        p = re.sub(r"__(.+?)__", r"<b>\1</b>", p, flags=re.S)
        p = re.sub(r"(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?![\w*])", r"<i>\1</i>", p)
        p = re.sub(r"(?<![\w_])_(?!\s)(.+?)(?<!\s)_(?![\w_])", r"<i>\1</i>", p)
        p = re.sub(r"^\s*[\*\-•]\s+", "• ", p, flags=re.M)
        p = re.sub(r"\n{3,}", "\n\n", p)
        out.append(p)
    return "".join(out).strip()


def html_to_plain(text: str) -> str:
    return html.unescape(re.sub(r"<[^>]+>", "", text or ""))


def clean_plain(value: Any) -> str:
    s = str(value or "").strip()
    s = re.sub(r"```.*?```", "", s, flags=re.S)
    s = re.sub(r"[*_`#]+", "", s)
    return re.sub(r"\s+", " ", s).strip()


def split_html(text: str, limit: int = TG_TEXT_LIMIT) -> list[str]:
    if len(text) <= limit:
        return [text]
    chunks: list[str] = []
    open_tags: list[str] = []
    while text:
        if len(text) <= limit:
            piece, text = text, ""
        else:
            cut = text.rfind("\n\n", 0, limit)
            if cut < limit // 2: cut = text.rfind("\n", 0, limit)
            if cut < limit // 2: cut = text.rfind(" ", 0, limit)
            if cut < limit // 2: cut = limit
            lt, gt = text.rfind("<", 0, cut), text.rfind(">", 0, cut)
            if lt > gt: cut = lt
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


async def send_html(message: Message, text: str, reply_markup: Any = None, protect: bool = False) -> Message | None:
    chunks = split_html(text or "No response.")
    last = None
    for i, chunk in enumerate(chunks):
        markup = reply_markup if i == len(chunks) - 1 else None
        try:
            last = await message.answer(chunk, reply_markup=markup, protect_content=protect)
        except TelegramBadRequest:
            last = await message.answer(html_to_plain(chunk), parse_mode=None, reply_markup=markup, protect_content=protect)
    return last


async def safe_edit(message: Message, text: str, reply_markup: InlineKeyboardMarkup | None = None, protect: bool = False) -> Message:
    """Edit in place; tolerate 'not modified'; fall back to a new message only when editing is impossible."""
    try:
        await message.edit_text(text, reply_markup=reply_markup)
        return message
    except TelegramBadRequest as e:
        if "message is not modified" in str(e):
            return message
        try:
            return await message.answer(text, reply_markup=reply_markup, protect_content=protect)
        except TelegramBadRequest:
            return await message.answer(html_to_plain(text), parse_mode=None, reply_markup=reply_markup, protect_content=protect)


async def try_delete(message: Message | None) -> bool:
    if not message:
        return False
    try:
        await message.delete()
        return True
    except TelegramAPIError:
        return False


def has_devanagari(text: str) -> bool:
    return bool(re.search(r"[\u0900-\u097F]", text or ""))


# ============================ Menus ============================
PRIMARY_BUTTONS = ["🎯 Select Exam", "❓ Daily Quiz", "🧪 Generate AI Test", "📝 Mock Tests",
                   "🧠 Ask AI Tutor", "📷 Solve Image", "📂 More Features"]
SECONDARY_BUTTONS = ["📚 Study Materials", "📊 My Performance", "📜 Test History", "🏆 Leaderboard",
                     "👤 My Profile", "⚙️ Settings", "💳 Subscription", "❔ Help", "🏠 Home"]
MENU_BUTTONS = set(PRIMARY_BUTTONS) | set(SECONDARY_BUTTONS) | {"🛠 Admin Panel"}


def _is_cmd(message: Message) -> bool:
    """Commands and menu buttons are never consumed by an FSM text handler — they skip to the real handler."""
    t = (message.text or "").strip()
    return t.startswith("/") or t in MENU_BUTTONS


def main_keyboard(is_admin: bool = False) -> ReplyKeyboardMarkup:
    rows = [
        [KeyboardButton(text="🎯 Select Exam"), KeyboardButton(text="❓ Daily Quiz")],
        [KeyboardButton(text="🧪 Generate AI Test"), KeyboardButton(text="📝 Mock Tests")],
        [KeyboardButton(text="🧠 Ask AI Tutor"), KeyboardButton(text="📷 Solve Image")],
        [KeyboardButton(text="📂 More Features")],
    ]
    if is_admin:
        rows.append([KeyboardButton(text="🛠 Admin Panel")])
    return ReplyKeyboardMarkup(keyboard=rows, resize_keyboard=True, input_field_placeholder="Type a doubt or pick a tool…")


def more_keyboard(is_admin: bool = False) -> ReplyKeyboardMarkup:
    rows = [
        [KeyboardButton(text="📚 Study Materials"), KeyboardButton(text="📊 My Performance")],
        [KeyboardButton(text="📜 Test History"), KeyboardButton(text="🏆 Leaderboard")],
        [KeyboardButton(text="👤 My Profile"), KeyboardButton(text="⚙️ Settings")],
        [KeyboardButton(text="💳 Subscription"), KeyboardButton(text="❔ Help")],
        [KeyboardButton(text="🏠 Home")],
    ]
    if is_admin:
        rows.insert(4, [KeyboardButton(text="🛠 Admin Panel")])
    return ReplyKeyboardMarkup(keyboard=rows, resize_keyboard=True)


async def show_home(message: Message, user: User, text: str = "🏠 <b>Exam Yatra</b> — main menu") -> None:
    await message.answer(text, reply_markup=main_keyboard(user.is_admin))


# ============================ User registration & trial start ============================
async def get_user(session: AsyncSession, tg_user) -> User:
    """Find or create. The trial starts exactly once: at first registration, if trial is enabled."""
    user = (await session.execute(select(User).where(User.telegram_id == tg_user.id))).scalar_one_or_none()
    if not user:
        user = User(telegram_id=tg_user.id, username=tg_user.username, full_name=(tg_user.full_name or "Student")[:160],
                    is_admin=is_admin_id(tg_user.id))
        session.add(user)
        try:
            await session.flush()
        except IntegrityError:
            # Two updates raced to create the same user; load the row that won.
            await session.rollback()
            user = (await session.execute(select(User).where(User.telegram_id == tg_user.id))).scalar_one()
        else:
            await maybe_start_trial(session, user)
            await audit(session, tg_user.id, "user.register", str(tg_user.id))
    changed = False
    if user.username != tg_user.username:
        user.username = tg_user.username; changed = True
    name = (tg_user.full_name or "Student")[:160]
    if user.full_name != name:
        user.full_name = name; changed = True
    if user.is_admin != is_admin_id(tg_user.id):
        user.is_admin = is_admin_id(tg_user.id); changed = True
    user.last_active_at = now_utc()
    refresh_entitlements(user)
    if changed:
        await session.flush()
    return user


async def maybe_start_trial(session: AsyncSession, user: User) -> bool:
    """Start the trial only for a user who never had one. Never restarts an existing/expired trial."""
    if user.trial_status != "none" or user.trial_started_at is not None:
        return False
    if not await setting_bool(session, "trial_enabled", True):
        return False
    days = max(0, await setting_int(session, "trial_days", 7))
    if days == 0:
        return False
    user.trial_started_at = now_utc()
    user.trial_ends_at = user.trial_started_at + timedelta(days=days)
    user.trial_status = "active"
    await session.flush()
    return True


def trial_days_left(user: User) -> int:
    if user.trial_status != "active" or not user.trial_ends_at:
        return 0
    return max(0, (user.trial_ends_at - now_utc()).days + (1 if (user.trial_ends_at - now_utc()).seconds > 0 else 0))


# ============================ Required channel verification ============================
class MembershipResult:
    def __init__(self) -> None:
        self.missing: list[RequiredChannel] = []
        self.config_errors: list[str] = []

    @property
    def ok(self) -> bool:
        return not self.missing and not self.config_errors


async def required_channels(session: AsyncSession) -> list[RequiredChannel]:
    if not await setting_bool(session, "channel_verification", False):
        return []
    return list((await session.execute(select(RequiredChannel).where(RequiredChannel.enabled.is_(True)).order_by(RequiredChannel.id))).scalars())


def channel_chat_id(ch: RequiredChannel) -> int | str:
    ref = ch.chat_ref.strip()
    return int(ref) if re.fullmatch(r"-?\d+", ref) else (ref if ref.startswith("@") else "@" + ref)


async def check_membership(bot: Bot, session: AsyncSession, user: User) -> MembershipResult:
    """A failed API call is never treated as 'joined'. Missing bot rights produce a config error."""
    res = MembershipResult()
    for ch in await required_channels(session):
        try:
            member = await bot.get_chat_member(channel_chat_id(ch), user.telegram_id)
            status = member.status
            if status in (ChatMemberStatus.MEMBER, ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.CREATOR):
                continue
            if status == ChatMemberStatus.RESTRICTED and getattr(member, "is_member", False):
                continue
            res.missing.append(ch)
        except TelegramForbiddenError:
            res.config_errors.append(f"{ch.chat_ref}: the bot is not an administrator of this channel (member check forbidden).")
        except TelegramBadRequest as e:
            msg = str(e)
            if "chat not found" in msg.lower() or "user not found" in msg.lower() or "member list is inaccessible" in msg.lower():
                res.config_errors.append(f"{ch.chat_ref}: {msg.split(':')[-1].strip()}")
            else:
                res.missing.append(ch)
        except TelegramAPIError as e:
            res.config_errors.append(f"{ch.chat_ref}: Telegram API error ({type(e).__name__}).")
    return res


def join_keyboard(res: MembershipResult) -> InlineKeyboardMarkup:
    rows: list[list[tuple[str, str, bool]]] = []
    for ch in res.missing:
        url = ch.invite_url or (f"https://t.me/{ch.chat_ref.lstrip('@')}" if not re.fullmatch(r"-?\d+", ch.chat_ref) else None)
        if url:
            rows.append([(f"📢 Join {ch.title or ch.chat_ref}", url, True)])
    rows.append([("✅ Verify Membership", "join:verify", False)])
    return url_button_rows(rows)


async def membership_prompt(message: Message, session: AsyncSession, res: MembershipResult, edit: bool = False) -> None:
    if res.config_errors and not res.missing:
        contact = await support_contact(session)
        text = ("⚠️ <b>Channel verification is misconfigured</b>\n\nThe bot cannot check membership right now. "
                "The bot must be an <b>administrator</b> in each required channel.\n\n" +
                "\n".join(f"• {esc(e)}" for e in res.config_errors) +
                "\n\nPlease inform the admin.")
        kb = url_button_rows(support_rows(contact) + [[("🔁 Retry", "join:verify", False)]])
    else:
        text = ("🔒 <b>JOIN REQUIRED CHANNEL</b>\n\nTo use Exam Yatra, please join our official channel"
                + ("s" if len(res.missing) > 1 else "") + ", then tap <b>Verify Membership</b>.")
        if res.config_errors:
            text += "\n\n⚠️ Some channels could not be checked:\n" + "\n".join(f"• {esc(e)}" for e in res.config_errors)
        kb = join_keyboard(res)
    if edit:
        await safe_edit(message, text, kb)
    else:
        await message.answer(text, reply_markup=kb)


@router.callback_query(F.data == "join:verify")
async def join_verify(cb: CallbackQuery, session: AsyncSession, db_user: User, bot: Bot):
    res = await check_membership(bot, session, db_user)
    if res.ok:
        db_user.channel_verified_at = now_utc()
        await session.flush()
        await cb.answer("✅ Membership verified. Welcome!")
        await safe_edit(cb.message, "✅ <b>Membership verified.</b> You can now use Exam Yatra.")
        await show_home(cb.message, db_user)
        return
    await cb.answer("Not verified yet." if res.missing else "Configuration problem — see message.", show_alert=True)
    await membership_prompt(cb.message, session, res, edit=True)


# ============================ Access gate ============================
async def gate(event: Message | CallbackQuery, user: User, session: AsyncSession, bot: Bot | None = None,
               *, require_channel: bool = True) -> bool:
    """Every protected entry point calls this. Order: ban → access → maintenance → channel membership."""
    message = event if isinstance(event, Message) else event.message
    async def deny(text: str, kb: InlineKeyboardMarkup | None = None) -> bool:
        if isinstance(event, CallbackQuery):
            await event.answer(html_to_plain(text)[:190], show_alert=True)
        else:
            await message.answer(text, reply_markup=kb)
        return False
    contact = await support_contact(session)
    if user.status == "banned":
        return await deny("⛔ Your account has been suspended.", url_button_rows(support_rows(contact)) if contact else None)
    if not user.access_granted and not user.is_admin:
        return await deny("⛔ Access to this bot has been revoked for your account.", url_button_rows(support_rows(contact)) if contact else None)
    if not user.is_admin and await maintenance_on(session):
        return await deny("🛠 " + esc(await get_setting(session, "maintenance_message", ENV_MAINTENANCE_MESSAGE)))
    if require_channel and not user.is_admin and bot is not None:
        res = await check_membership(bot, session, user)
        if not res.ok:
            if isinstance(event, CallbackQuery):
                await event.answer("Please join the required channel first.", show_alert=True)
            await membership_prompt(message, session, res)
            return False
    return True



# ============================ Gemini client ============================
class AIError(Exception):
    def __init__(self, code: str, detail: str = ""):
        super().__init__(detail or code)
        self.code, self.detail = code, detail


AI_ERROR_TEXT = {
    "no_key": "🤖 AI features are not configured yet. The administrator needs to add a Gemini API key.",
    "auth": "🤖 The AI service rejected the configured API key. Please inform the admin.",
    "model": "🤖 The configured AI model is unavailable. Please inform the admin.",
    "permission": "🤖 The AI API key lacks permission for this model. Please inform the admin.",
    "quota": "🤖 The AI service quota is exhausted for now. Please try again later.",
    "rate_limit": "🤖 The AI service is busy (rate limited). Please try again in a minute.",
    "timeout": "🤖 The AI service took too long to respond. Please try again.",
    "network": "🤖 I couldn't reach the AI service. Please try again later.",
    "http": "🤖 The AI service returned an error. Please try again later.",
    "parse": "🤖 The AI returned an unexpected response. Please try again.",
    "empty": "🤖 The AI returned an empty response. Please try again.",
    "blocked": "🤖 The AI declined to answer this request.",
}


def mask_key(key: str) -> str:
    return "not set" if not key else (key[:4] + "…" + key[-4:] if len(key) > 10 else "****")


def classify_http_error(status: int, body: str) -> str:
    low = body.lower()
    if status in (401,) or "api key not valid" in low or "api_key_invalid" in low:
        return "auth"
    if status == 403:
        return "permission"
    if status == 404 or ("model" in low and ("not found" in low or "not supported" in low)):
        return "model"
    if status == 429:
        return "quota" if "quota" in low or "exhausted" in low else "rate_limit"
    return "http"


async def gemini_request(payload: dict[str, Any], api_key: str, *, model: str | None = None, timeout: float = 60.0) -> dict[str, Any]:
    if not api_key:
        raise AIError("no_key")
    url = f"https://generativelanguage.googleapis.com/v1beta/models/{model or GEMINI_MODEL}:generateContent"
    try:
        async with httpx.AsyncClient(timeout=httpx.Timeout(timeout, connect=15.0)) as client:
            r = await client.post(url, params={"key": api_key}, json=payload)
    except httpx.TimeoutException as e:
        raise AIError("timeout", str(e))
    except httpx.HTTPError as e:
        raise AIError("network", str(e))
    if r.status_code >= 400:
        code = classify_http_error(r.status_code, r.text[:2000])
        log.warning("Gemini HTTP %s → %s: %s", r.status_code, code, r.text[:300])   # key is never logged
        raise AIError(code, f"HTTP {r.status_code}")
    try:
        return r.json()
    except ValueError:
        raise AIError("parse", "non-JSON body")


def extract_text(data: dict[str, Any]) -> str:
    cands = data.get("candidates") or []
    if not cands:
        if (data.get("promptFeedback") or {}).get("blockReason"):
            raise AIError("blocked")
        raise AIError("empty")
    parts = ((cands[0].get("content") or {}).get("parts") or [])
    text = "".join(p.get("text", "") for p in parts if isinstance(p, dict)).strip()
    if not text:
        raise AIError("empty")
    return text


def _image_part(image_bytes: bytes, mime_type: str) -> dict[str, Any]:
    return {"inline_data": {"mime_type": mime_type, "data": base64.b64encode(image_bytes).decode("ascii")}}


async def gemini_call(parts: list[dict[str, Any]], api_key: str, *, system: str | None = None, temperature: float = 0.4,
                      max_tokens: int = 2048, timeout: float = 60.0, response_schema: dict | None = None) -> str:
    payload: dict[str, Any] = {"contents": [{"role": "user", "parts": parts}],
                               "generationConfig": {"temperature": temperature, "maxOutputTokens": max_tokens}}
    if system:
        payload["systemInstruction"] = {"parts": [{"text": system}]}
    if response_schema:
        payload["generationConfig"]["responseMimeType"] = "application/json"
        payload["generationConfig"]["responseSchema"] = response_schema
    return extract_text(await gemini_request(payload, api_key, timeout=timeout))


def parse_json_loose(text: str) -> Any:
    text = text.strip()
    text = re.sub(r"^```(?:json)?\s*|\s*```$", "", text, flags=re.S).strip()
    try:
        return json.loads(text)
    except ValueError:
        pass
    for opener, closer in (("[", "]"), ("{", "}")):
        a, b = text.find(opener), text.rfind(closer)
        if a != -1 and b > a:
            try:
                return json.loads(text[a:b + 1])
            except ValueError:
                continue
    return None


async def ai_generate_json(prompt: str, schema: dict, api_key: str, *, image_bytes: bytes | None = None, mime_type: str = "image/jpeg",
                           system: str | None = None, temperature: float = 0.3, max_tokens: int = 4096, timeout: float = 60.0) -> tuple[Any, str | None]:
    parts: list[dict[str, Any]] = [{"text": prompt}]
    if image_bytes:
        parts.append(_image_part(image_bytes, mime_type))
    try:
        raw = await gemini_call(parts, api_key, system=system, temperature=temperature, max_tokens=max_tokens, timeout=timeout, response_schema=schema)
    except AIError as e:
        return None, e.code
    data = parse_json_loose(raw)
    return (data, None) if data is not None else (None, "parse")


async def test_api_key(api_key: str) -> tuple[bool, str]:
    """Real round-trip. Distinguishes bad key from bad model name so a valid key is not rejected wrongly."""
    try:
        text = await gemini_call([{"text": "Reply with the single word OK."}], api_key, max_tokens=16, temperature=0.0, timeout=25.0)
        return True, f"Key works with model <code>{esc(GEMINI_MODEL)}</code> (reply: {esc(text[:20])})."
    except AIError as e:
        if e.code in ("model", "permission"):
            # Key authenticated but the model is wrong/unavailable → verify the key against the model list.
            try:
                async with httpx.AsyncClient(timeout=20.0) as client:
                    r = await client.get("https://generativelanguage.googleapis.com/v1beta/models", params={"key": api_key, "pageSize": 50})
                if r.status_code < 400:
                    names = [m.get("name", "").split("/")[-1] for m in r.json().get("models", []) if "generateContent" in m.get("supportedGenerationMethods", [])]
                    return True, (f"Key is valid, but model <code>{esc(GEMINI_MODEL)}</code> is unavailable "
                                  f"({e.code}). Set GEMINI_MODEL to one of: {esc(', '.join(names[:8]))}")
                return False, f"Key rejected while listing models (HTTP {r.status_code})."
            except httpx.HTTPError as ex:
                return False, f"Network problem while validating: {esc(type(ex).__name__)}"
        return False, {"auth": "Authentication failed — the key is invalid.", "quota": "Key accepted but quota is exhausted.",
                       "rate_limit": "Rate limited — try again in a minute.", "timeout": "Timed out contacting Gemini.",
                       "network": "Network error contacting Gemini.", "parse": "Malformed response from Gemini.",
                       "empty": "Empty response from Gemini.", "no_key": "No key supplied."}.get(e.code, f"Error: {esc(e.code)}")


# ============================ AI Tutor / image solving ============================
ANSWER_SCHEMA = {
    "type": "OBJECT",
    "properties": {
        "question": {"type": "STRING"}, "answer": {"type": "STRING"}, "explanation": {"type": "STRING"},
        "steps": {"type": "ARRAY", "items": {"type": "STRING"}},
        "confidence": {"type": "STRING", "description": "high | medium | low"},
    },
    "required": ["answer"],
}


def answer_language(user: User, question_text: str) -> str:
    return "hi" if (user.language == "hi" or has_devanagari(question_text or "")) else "en"


def build_answer_prompt(question_text: str, style: str, lang: str, *, with_image: bool, caption: str = "") -> str:
    lang_name = "Hindi (Devanagari script)" if lang == "hi" else "English"
    if with_image:
        base = ("The attached image contains a student's exam question (possibly with MCQ choices). Read it carefully, "
                "extract the choices if present, and solve it. If the image is unreadable or ambiguous, say so in 'answer' "
                "and set confidence to low. Never invent text that is not visible.")
        if caption:
            base += f"\nStudent instructions: {caption[:400]}"
    else:
        base = f"Student question:\n{question_text[:3000]}"
    if style == STYLE_SHORT:
        guide = ("Return ONLY the direct answer in 'answer' (value, name, option letter + text, or one short sentence; max 25 words). "
                 "At most one short sentence in 'explanation'. Leave 'steps' empty.")
    else:
        guide = ("Fill 'question' with a one-line restatement, 'answer' with the direct final answer (max 30 words), 'steps' with 2-6 "
                 "short solution steps (formulas/examples where relevant) and 'explanation' with one or two sentences of the key concept.")
    return (f"{base}\n\nAnswer in {lang_name}. Plain text in every field — no Markdown, no HTML. If you are not sure of the fact, "
            f"say so and set confidence to 'low' instead of guessing.\n{guide}")


def render_structured_answer(data: dict[str, Any], style: str, lang: str) -> str:
    answer = clean_plain(data.get("answer")); explanation = clean_plain(data.get("explanation"))
    question = clean_plain(data.get("question")); confidence = clean_plain(data.get("confidence")).lower()
    steps_raw = data.get("steps") if isinstance(data.get("steps"), list) else []
    steps = [clean_plain(s) for s in steps_raw if clean_plain(s)]
    note = "\n\n⚠️ <i>Low confidence — please verify this answer from a standard source.</i>" if confidence == "low" else ""
    if style == STYLE_SHORT:
        text = f"✅ <b>{esc(answer)}</b>"
        if explanation and len(answer) < 60 and len(explanation) <= 220 and explanation.lower() != answer.lower():
            text += f"\n\n{esc(explanation)}"
        return text + note
    q_label, a_label, e_label = (("प्रश्न", "अंतिम उत्तर", "व्याख्या") if lang == "hi" else ("Question", "Final Answer", "Explanation"))
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
    return "\n\n".join(parts) + note


def render_fallback_answer(raw_text: str, style: str, lang: str) -> str:
    formatted = md_to_html(raw_text)
    if style == STYLE_SHORT:
        plain = html_to_plain(formatted)
        m = re.search(r"(?:final answer|answer|उत्तर)\s*[:：\-]\s*(.+)", plain, re.I)
        if m and m.group(1).strip():
            return f"✅ <b>{esc(m.group(1).strip()[:300])}</b>"
        paragraphs = [p.strip() for p in plain.split("\n\n") if p.strip()]
        if paragraphs:
            return f"✅ <b>{esc(paragraphs[-1][:300])}</b>"
    return formatted


async def answer_student_question(message: Message, session: AsyncSession, user: User, question_text: str = "",
                                  image_bytes: bytes | None = None, mime_type: str = "image/jpeg", caption: str = "") -> None:
    """Shared path for AI Tutor and image questions. Quota is charged only after a successful AI reply."""
    feature, limit_key = ("image", "image_daily") if image_bytes else ("ai", "ai_daily")
    if not await feature_enabled(session, feature):
        await message.answer("This feature is temporarily disabled by the administrator."); return
    api_key = await current_api_key(session)
    if not api_key:
        await message.answer(AI_ERROR_TEXT["no_key"]); return
    ok, why = await check_quota(session, user, limit_key, feature)
    if not ok:
        await send_html(message, why, url_button_rows([[("💳 Subscription", "sub:open", False)]])); return
    style = user.answer_style if user.answer_style in ANSWER_STYLES else STYLE_SHORT
    lang = answer_language(user, question_text or caption)
    await session.commit()          # don't hold a write transaction open during the network call
    thinking = await message.answer("🤔 Thinking…")
    prompt = build_answer_prompt(question_text, style, lang, with_image=bool(image_bytes), caption=caption)
    data, err = await ai_generate_json(prompt, ANSWER_SCHEMA, api_key, image_bytes=image_bytes, mime_type=mime_type, temperature=0.2, max_tokens=2048)
    # Re-check that the user still may receive the result (ban/revoke during the slow call).
    await session.refresh(user)
    if user.status == "banned" or (not user.access_granted and not user.is_admin):
        await try_delete(thinking); return
    await try_delete(thinking)
    if isinstance(data, dict) and clean_plain(data.get("answer")):
        await record_usage(session, user, feature)
        await send_html(message, render_structured_answer(data, style, lang)); return
    if err in ("no_key", "auth", "model", "permission", "quota", "rate_limit", "timeout", "network", "http", "blocked"):
        await message.answer(AI_ERROR_TEXT[err]); return
    parts: list[dict[str, Any]] = [{"text": prompt + "\nIf you cannot produce JSON, answer in plain text."}]
    if image_bytes:
        parts.append(_image_part(image_bytes, mime_type))
    try:
        raw = await gemini_call(parts, api_key)
    except AIError as e:
        await message.answer(AI_ERROR_TEXT.get(e.code, AI_ERROR_TEXT["http"])); return
    await record_usage(session, user, feature)
    await send_html(message, render_fallback_answer(raw, style, lang))


# ============================ Settings (no account deletion) ============================
def settings_keyboard(user: User) -> InlineKeyboardMarkup:
    def mark(selected: bool) -> str:
        return " ✅" if selected else ""
    return inline([
        [("⚡ Short Answer" + mark(user.answer_style == STYLE_SHORT), "set:style:short")],
        [("📘 Detailed Answer" + mark(user.answer_style == STYLE_DETAILED), "set:style:detailed")],
        [("🇬🇧 English" + mark(user.language == "en"), "set:lang:en"), ("🇮🇳 हिन्दी" + mark(user.language == "hi"), "set:lang:hi")],
        [("🏠 Home", "menu:home")],
    ])


def settings_text(user: User) -> str:
    style = "⚡ Short Answer" if user.answer_style == STYLE_SHORT else "📘 Detailed Answer"
    lang = "English" if user.language == "en" else "हिन्दी"
    return ("⚙️ <b>Settings</b>\n\n"
            f"<b>Answer Style:</b> {style}\n• Short — only the direct answer, highlighted.\n• Detailed — answer first, then steps.\n\n"
            f"<b>Language:</b> {lang}\n\nTap an option to change it.")


@router.callback_query(F.data.startswith("set:"))
async def settings_callback(cb: CallbackQuery, session: AsyncSession, db_user: User):
    parts = cb.data.split(":")
    action, value = (parts[1] if len(parts) > 1 else ""), (parts[2] if len(parts) > 2 else "")
    if action == "open":
        await cb.answer(); await cb.message.answer(settings_text(db_user), reply_markup=settings_keyboard(db_user)); return
    if action == "style" and value in ANSWER_STYLES:
        db_user.answer_style = value
    elif action == "lang" and value in ("en", "hi"):
        db_user.language = value
    else:
        await cb.answer("This option is no longer available.", show_alert=True); return
    await session.flush()
    await cb.answer("Saved")
    await safe_edit(cb.message, settings_text(db_user), settings_keyboard(db_user))


@router.callback_query(F.data == "menu:home")
async def menu_home(cb: CallbackQuery, db_user: User, state: FSMContext):
    await cb.answer()
    cur = await state.get_state()
    if cur and not cur.startswith("PaymentFlow"):      # payment flow is only cancelled explicitly
        await state.clear()
    await show_home(cb.message, db_user)


@router.callback_query(F.data == "info:contact")
async def info_contact(cb: CallbackQuery, session: AsyncSession):
    await cb.answer(f"Support: {await support_contact(session)}", show_alert=True)


# ============================ Question bank: validation ============================
def validate_mcq(text: str, options: list[str], correct_index: int | None, *, explanation: str | None = None,
                 require_explanation: bool = False) -> list[str]:
    """Structural validation shared by admin input, AI generation and publication. Returns a list of problems."""
    problems: list[str] = []
    t = (text or "").strip()
    if len(t) < 8:
        problems.append("question text is empty or too short")
    opts = [(o or "").strip() for o in options]
    if len(opts) != 4:
        problems.append(f"exactly 4 options required (got {len(opts)})")
    if any(not o for o in opts):
        problems.append("one or more options are empty")
    if len({normalize_question_text(o) for o in opts if o}) != len([o for o in opts if o]):
        problems.append("duplicate options")
    if correct_index is None:
        problems.append("correct answer missing")
    elif not (0 <= correct_index < len(opts)):
        problems.append("correct answer index out of range")
    if require_explanation and not (explanation or "").strip():
        problems.append("explanation missing")
    return problems


def question_problems(q: Question) -> list[str]:
    opts = [o.text for o in q.options]
    corrects = [i for i, o in enumerate(q.options) if o.correct]
    problems = validate_mcq(q.text, opts, corrects[0] if len(corrects) == 1 else None)
    if len(corrects) > 1:
        problems.append("more than one option marked correct")
    return problems


def is_servable(q: Question) -> bool:
    return q.status == Q_APPROVED and q.published and not question_problems(q)


async def find_duplicate(session: AsyncSession, text: str, exclude_id: int | None = None) -> Question | None:
    stmt = select(Question).where(Question.text_hash == question_hash(text))
    if exclude_id:
        stmt = stmt.where(Question.id != exclude_id)
    return (await session.execute(stmt.limit(1))).scalars().first()


QUESTION_FORMAT_HELP = (
    "Send the question in this format (one field per line):\n\n"
    "<code>Q: question text\nA: option 1\nB: option 2\nC: option 3\nD: option 4\nANS: B\n"
    "EXP: explanation (optional)\nSUB: subject (optional)\nTOPIC: topic (optional)\nSRC: source/reference (optional)\n"
    "URL: https://reference-link (optional)</code>\n\n"
    "The question is saved as <b>Pending Review</b>; approve it from Question Bank → Review."
)


def parse_question_block(raw: str) -> tuple[dict[str, Any] | None, str]:
    fields: dict[str, str] = {}
    for line in (raw or "").splitlines():
        m = re.match(r"^\s*(Q|A|B|C|D|ANS|EXP|SUB|TOPIC|SRC|URL)\s*[:：]\s*(.*)$", line, re.I)
        if m:
            fields[m.group(1).upper()] = m.group(2).strip()
        elif line.strip() and fields:
            last = list(fields.keys())[-1]
            fields[last] += "\n" + line.strip()
    opts = [fields.get(k, "") for k in "ABCD"]
    ans = fields.get("ANS", "").strip().upper()[:1]
    idx = LETTERS.index(ans) if ans in LETTERS else None
    problems = validate_mcq(fields.get("Q", ""), opts, idx)
    if problems:
        return None, "Rejected: " + "; ".join(problems) + ".\n\n" + QUESTION_FORMAT_HELP
    url = fields.get("URL", "")
    if url and not re.match(r"^https?://", url):
        return None, "Rejected: URL must start with http:// or https://"
    return {"text": fields["Q"].strip(), "options": [o.strip() for o in opts], "correct_index": idx,
            "explanation": fields.get("EXP") or None, "subject": fields.get("SUB") or None,
            "topic": fields.get("TOPIC") or None, "source": fields.get("SRC") or None, "url": url or None}, ""


async def get_or_create_subject(session: AsyncSession, exam_id: int, name: str | None) -> int | None:
    if not name:
        return None
    s = (await session.execute(select(Subject).where(Subject.exam_id == exam_id, func.lower(Subject.name) == name.strip().lower()))).scalar_one_or_none()
    if not s:
        s = Subject(exam_id=exam_id, name=name.strip()[:100]); session.add(s); await session.flush()
    return s.id


async def create_bank_question(session: AsyncSession, exam_id: int, data: dict[str, Any], actor: int) -> tuple[Question | None, str]:
    dup = await find_duplicate(session, data["text"])
    if dup:
        return None, f"Rejected: duplicate of question #{dup.id} ({dup.status})."
    q = Question(exam_id=exam_id, subject_id=await get_or_create_subject(session, exam_id, data.get("subject")),
                 text=data["text"], explanation=data.get("explanation"), status=Q_PENDING, published=True,
                 topic=(data.get("topic") or None), source=(data.get("source") or None), reference_url=data.get("url"),
                 created_at=now_utc(), text_hash=question_hash(data["text"]))
    session.add(q); await session.flush()
    for i, o in enumerate(data["options"]):
        session.add(Option(question_id=q.id, position=i, text=o, correct=(i == data["correct_index"])))
    await session.flush()
    await audit(session, actor, "question.create", str(q.id))
    return q, ""


def render_question_admin(q: Question, exam_name: str = "", subject_name: str = "") -> str:
    status_icon = {Q_APPROVED: "✅", Q_PENDING: "🕒", Q_REJECTED: "❌", Q_DRAFT: "📝"}.get(q.status, "•")
    lines = [f"{status_icon} <b>Question #{q.id}</b> — {esc(q.status)}{'' if q.published else ' (unpublished)'}",
             f"Exam: {esc(exam_name) or q.exam_id} · Subject: {esc(subject_name) or '—'} · Topic: {esc(q.topic) or '—'}", "",
             f"<b>{esc(q.text)}</b>", ""]
    for i, o in enumerate(q.options):
        lines.append(f"{'✔️' if o.correct else '▫️'} {LETTERS[i] if i < 4 else i + 1}. {esc(o.text)}")
    if q.explanation:
        lines += ["", f"💡 {esc(q.explanation)}"]
    if q.source or q.reference_url:
        lines += ["", f"📎 Source: {esc(q.source) or '—'}" + (f"\n🔗 {esc(q.reference_url)}" if q.reference_url else "")]
    if q.verified_at:
        lines.append(f"🕓 Verified {fmt_dt(q.verified_at)} by {q.verified_by}")
    probs = question_problems(q)
    if probs:
        lines += ["", "⚠️ Problems: " + "; ".join(probs)]
    return "\n".join(lines)


# ============================ Daily Quiz (approved questions only) ============================
async def show_exams(message: Message, session: AsyncSession) -> None:
    exams = list((await session.execute(select(Exam).where(Exam.active.is_(True)).order_by(Exam.name))).scalars())
    if not exams:
        await message.answer("No exam categories have been added yet. Please check back soon."); return
    await message.answer("🎯 <b>Choose your target exam:</b>", reply_markup=inline(
        [[(e.name, f"exam:{e.id}") for e in exams[i:i + 2]] for i in range(0, len(exams), 2)]))


@router.callback_query(F.data.startswith("exam:"))
async def choose_exam(cb: CallbackQuery, session: AsyncSession, db_user: User):
    exam = await session.get(Exam, parse_int(cb.data.split(":")[1], 0) or 0)
    if not exam or not exam.active:
        await cb.answer("This exam is no longer available.", show_alert=True); return
    db_user.selected_exam_id = exam.id
    await session.flush()
    await cb.answer(f"Selected: {exam.name}")
    await safe_edit(cb.message, f"🎯 Target exam set to <b>{esc(exam.name)}</b>.\nUse ❓ Daily Quiz, 📝 Mock Tests or 🧪 Generate AI Test to begin.")


async def send_quiz(message: Message, session: AsyncSession, user: User) -> None:
    if not await feature_enabled(session, "quiz"):
        await message.answer("Daily Quiz is temporarily disabled by the administrator."); return
    if not user.selected_exam_id:
        await message.answer("Choose your exam first."); await show_exams(message, session); return
    ok, why = await check_quota(session, user, "quiz_daily", "quiz")
    if not ok:
        await send_html(message, why, url_button_rows([[("💳 Subscription", "sub:open", False)]])); return
    questions = list((await session.execute(select(Question).where(
        Question.exam_id == user.selected_exam_id, Question.status == Q_APPROVED, Question.published.is_(True)))).scalars().all())
    valid = [q for q in questions if is_servable(q)]
    if not valid:
        await message.answer("No verified questions are available for this exam yet. The admin is adding them."); return
    answered = set((await session.execute(select(Practice.question_id).where(Practice.user_id == user.id, Practice.answered_at.is_not(None)))).scalars())
    fresh = [q for q in valid if q.id not in answered]
    q = random.choice(fresh or valid)
    options = q.options[:]
    random.shuffle(options)
    attempt = Practice(user_id=user.id, question_id=q.id, option_order=",".join(str(o.id) for o in options))
    session.add(attempt); await session.flush()
    await record_usage(session, user, "quiz")
    text = f"❓ <b>DAILY QUIZ</b> · ✅ verified question\n\n━━━━━━━━━━━━━━━━━━━━\n\n<b>{esc(q.text)}</b>"
    rows = [[(button_label(LETTERS[i], o.text), f"qa:{attempt.id}:{i}")] for i, o in enumerate(options)]
    rows.append([("⏭ Another question", "quiz:next")])
    await message.answer(text, reply_markup=inline(rows), protect_content=True)


@router.callback_query(F.data == "quiz:next")
async def quiz_next(cb: CallbackQuery, session: AsyncSession, db_user: User, bot: Bot):
    if not await gate(cb, db_user, session, bot): return
    await cb.answer()
    await send_quiz(cb.message, session, db_user)


@router.callback_query(F.data.startswith("qa:"))
async def quiz_answer(cb: CallbackQuery, session: AsyncSession, db_user: User):
    try:
        attempt_id, idx = map(int, cb.data.split(":")[1:])
    except ValueError:
        await cb.answer("Invalid button.", show_alert=True); return
    attempt = await session.get(Practice, attempt_id)
    if not attempt or attempt.user_id != db_user.id:
        await cb.answer("This question belongs to another session.", show_alert=True); return
    if attempt.answered_at is not None:
        await cb.answer("Already answered.", show_alert=False); return
    order = [int(x) for x in attempt.option_order.split(",") if x]
    if not (0 <= idx < len(order)):
        await cb.answer("Invalid option.", show_alert=True); return
    q = await session.get(Question, attempt.question_id)
    chosen = next((o for o in q.options if o.id == order[idx]), None)
    if not chosen:
        await cb.answer("Option no longer exists.", show_alert=True); return
    attempt.selected_option_id = chosen.id
    attempt.is_correct = bool(chosen.correct)
    attempt.answered_at = now_utc()
    await session.flush()
    correct = next((o for o in q.options if o.correct), None)
    verdict = "✅ <b>Correct!</b>" if chosen.correct else f"❌ <b>Incorrect.</b> Correct answer: <b>{esc(correct.text if correct else '—')}</b>"
    text = f"❓ <b>DAILY QUIZ</b>\n\n<b>{esc(q.text)}</b>\n\nYour answer: {esc(chosen.text)}\n{verdict}"
    if q.explanation:
        text += f"\n\n💡 {esc(q.explanation)}"
    await cb.answer("Correct!" if chosen.correct else "Incorrect")
    await safe_edit(cb.message, text, inline([[("⏭ Next question", "quiz:next")], [("🏠 Home", "menu:home")]]), protect=True)



# ============================ AI test generation (strict validation) ============================
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
TEST_SYSTEM = ("You are an expert question setter for Indian competitive exams (SSC, Railway, Banking, BPSC, Bihar Police, UPSC, "
               "teaching exams). Write factually accurate, unambiguous multiple-choice questions with exactly four distinct options "
               "and exactly one correct option. Only use well-established facts; avoid disputed or very recent current-affairs items "
               "unless you are certain. Explanations must justify the correct answer in one to three sentences.")


def build_test_prompt(topic: str, n: int, difficulty: str, lang: str, avoid: list[str]) -> str:
    lang_name = "Hindi (Devanagari script)" if lang == "hi" else "English"
    diff = "a mix of easy, medium and hard" if difficulty == "mixed" else difficulty
    avoid_txt = ("\nDo NOT repeat these questions: " + " | ".join(avoid)) if avoid else ""
    return (f"Create {n} {diff} MCQs on: {topic}. Language: {lang_name}. Return a JSON array; each item has question, options "
            f"(exactly 4 strings), correct_index (0-3), explanation, difficulty (easy|medium|hard).{avoid_txt}")


def validate_generated_question(item: Any, seen: set[str]) -> dict[str, Any] | None:
    if not isinstance(item, dict):
        return None
    text = clean_plain(item.get("question"))
    opts_raw = item.get("options")
    if not isinstance(opts_raw, list):
        return None
    opts = [clean_plain(o) for o in opts_raw]
    try:
        ci = int(item.get("correct_index"))
    except (TypeError, ValueError):
        return None
    explanation = clean_plain(item.get("explanation"))
    if validate_mcq(text, opts, ci, explanation=explanation, require_explanation=True):
        return None
    try:
        text.encode("utf-8"); "".join(opts).encode("utf-8")
    except UnicodeEncodeError:
        return None
    if any(len(o) > 300 for o in opts) or len(text) > 1200:
        return None
    key = normalize_question_text(text)
    if key in seen or any(_near_duplicate(key, s) for s in seen):
        return None
    diff = str(item.get("difficulty") or "medium").lower()
    return {"text": text, "options": opts, "correct_index": ci, "explanation": explanation,
            "difficulty": diff if diff in ("easy", "medium", "hard") else "medium"}


def _near_duplicate(a: str, b: str) -> bool:
    if not a or not b:
        return False
    sa, sb = set(a.split()), set(b.split())
    if len(sa) < 4 or len(sb) < 4:
        return False
    return len(sa & sb) / len(sa | sb) >= 0.85


async def generate_test_questions(topic: str, total: int, difficulty: str, lang: str, api_key: str,
                                  progress: Callable[[int, int], Awaitable[None]] | None = None) -> tuple[list[dict[str, Any]], str | None]:
    questions: list[dict[str, Any]] = []
    seen: set[str] = set()
    calls = idle_rounds = rate_limit_hits = 0
    while len(questions) < total and calls < AI_TEST_MAX_CALLS:
        need = min(AI_TEST_BATCH, total - len(questions))
        ask = min(need + 2, AI_TEST_BATCH + 2)
        avoid = [q["text"][:90] for q in questions[-12:]]
        calls += 1
        data, err = await ai_generate_json(build_test_prompt(topic, ask, difficulty, lang, avoid), TEST_SCHEMA, api_key,
                                           system=TEST_SYSTEM, temperature=0.8, max_tokens=8192, timeout=90.0)
        if err in ("no_key", "auth", "model", "permission", "quota", "blocked"):
            return questions, err
        if err == "rate_limit":
            rate_limit_hits += 1
            if rate_limit_hits > 2:
                return questions, "rate_limit"
            await asyncio.sleep(4 * rate_limit_hits); continue
        if err or not isinstance(data, list):
            idle_rounds += 1
            if idle_rounds >= 3:
                return questions, err or "parse"
            await asyncio.sleep(1.5); continue
        added = 0
        for item in data:
            q = validate_generated_question(item, seen)
            if q is None:
                continue
            seen.add(normalize_question_text(q["text"])); questions.append(q); added += 1
            if len(questions) >= total:
                break
        idle_rounds = 0 if added else idle_rounds + 1
        if idle_rounds >= 3:
            return questions, "parse"
        if progress:
            try: await progress(len(questions), total)
            except Exception: pass
    if len(questions) < total:
        return questions, "incomplete"
    return questions[:total], None


GENERATION_ERROR_TEXT = {
    "incomplete": "I couldn't build a complete, valid test for this topic right now. Try again, pick fewer questions or a more specific topic.",
    "parse": "The AI returned questions I couldn't validate. Nothing was saved — please try again.",
}


# ============================ Unified test engine ============================
def button_label(letter: str, text: str, limit: int = BUTTON_LABEL_LIMIT) -> str:
    text = re.sub(r"\s+", " ", text or "").strip()
    return f"{letter}. {text}" if len(text) <= limit else f"{letter}. {text[:limit - 1].rstrip()}…"


def labels_ambiguous(opts: list[str]) -> bool:
    """True if truncation would make two option buttons look identical or any option is too long."""
    labels = [button_label(LETTERS[i], o) for i, o in enumerate(opts)]
    return len(set(labels)) != len(labels) or any(len(re.sub(r"\s+", " ", o)) > BUTTON_LABEL_LIMIT for o in opts)


async def create_test_session(session: AsyncSession, user: User, *, kind: str, topic: str, questions: list[dict[str, Any]],
                              mode: str, difficulty: str = "mixed", lang: str = "en", requested: int | None = None,
                              mock_test_id: int | None = None, duration_min: int | None = None) -> AiTest:
    """Each question is stored with its DISPLAYED option order; correct_index refers to that order."""
    test = AiTest(user_id=user.id, topic=topic[:200], requested_count=requested or len(questions), question_count=len(questions),
                  language=lang, difficulty=difficulty, status="in_progress", current_index=0, unanswered=len(questions),
                  started_at=now_utc(), kind=kind, mode=mode, mock_test_id=mock_test_id,
                  deadline_at=(now_utc() + timedelta(minutes=duration_min)) if duration_min else None)
    session.add(test); await session.flush()
    for pos, q in enumerate(questions):
        session.add(AiTestQuestion(test_id=test.id, position=pos, text=q["text"], options_json=json.dumps(q["options"], ensure_ascii=False),
                                   correct_index=q["correct_index"], explanation=q.get("explanation"), difficulty=q.get("difficulty", "medium"),
                                   source_question_id=q.get("source_question_id"), verified=bool(q.get("verified"))))
    user.active_test_id = test.id
    await session.flush()
    return test


def shuffled_snapshot(q: Question) -> dict[str, Any]:
    """Snapshot a bank question with a fresh random option order; correct_index follows the shuffle."""
    opts = q.options[:]
    random.shuffle(opts)
    return {"text": q.text, "options": [o.text for o in opts], "correct_index": next(i for i, o in enumerate(opts) if o.correct),
            "explanation": q.explanation, "difficulty": q.difficulty, "source_question_id": q.id, "verified": q.status == Q_APPROVED}


async def load_owned_test(session: AsyncSession, test_id: int, user: User) -> AiTest | None:
    test = await session.get(AiTest, test_id)
    return test if test and test.user_id == user.id else None


async def load_test_questions(session: AsyncSession, test: AiTest) -> list[AiTestQuestion]:
    return list((await session.execute(select(AiTestQuestion).where(AiTestQuestion.test_id == test.id).order_by(AiTestQuestion.position))).scalars())


async def active_test_for(session: AsyncSession, user: User) -> AiTest | None:
    return (await session.execute(select(AiTest).where(AiTest.user_id == user.id, AiTest.status == "in_progress").order_by(AiTest.id.desc()).limit(1))).scalars().first()


def score_from_questions(questions: list[AiTestQuestion]) -> tuple[int, int, int]:
    correct = sum(1 for q in questions if q.selected_index is not None and q.selected_index == q.correct_index)
    answered = sum(1 for q in questions if q.selected_index is not None)
    return correct, answered - correct, len(questions) - answered


async def finalize_test(session: AsyncSession, test: AiTest, questions: list[AiTestQuestion], *, status: str = "completed") -> bool:
    """Score once, only from saved answers. Idempotent."""
    if test.status != "in_progress":
        return False
    correct, incorrect, unanswered = score_from_questions(questions)
    test.correct, test.incorrect, test.unanswered = correct, incorrect, unanswered
    test.score = float(correct)
    attempted = correct + incorrect
    test.accuracy = round(correct / attempted * 100, 1) if attempted else 0.0
    test.status = status
    test.completed_at = now_utc()
    user = await session.get(User, test.user_id)
    if user and user.active_test_id == test.id:
        user.active_test_id = None
    await session.flush()
    return True


def test_expired(test: AiTest) -> bool:
    return bool(test.deadline_at and now_utc() >= test.deadline_at)


def test_header(test: AiTest) -> str:
    icon = "📝" if test.kind == "mock" else "🧪"
    label = "MOCK TEST" if test.kind == "mock" else "AI PRACTICE TEST"
    return f"{icon} <b>{esc(test.topic.upper())}</b> · {label}"


def render_question_text(test: AiTest, questions: list[AiTestQuestion], idx: int) -> str:
    q = questions[idx]
    answered = sum(1 for x in questions if x.selected_index is not None)
    lines = [test_header(test), "", f"Question <b>{idx + 1}</b> of {len(questions)}", f"Answered: {answered}/{len(questions)}"]
    if test.deadline_at:
        left = max(0, int((test.deadline_at - now_utc()).total_seconds()))
        lines.append(f"⏱ Time left: {left // 60:02d}:{left % 60:02d}")
    lines += ["", "━━━━━━━━━━━━━━━━━━━━", "", f"<b>{esc(q.text)}</b>"]
    opts = q.options()
    if test.show_full or labels_ambiguous(opts):
        # Only when a button label would be truncated/ambiguous: show complete options once, in the message.
        lines += ["", "<i>Full options:</i>"] + [f"{LETTERS[i]}. {esc(o)}" for i, o in enumerate(opts)]
    if q.selected_index is not None and 0 <= q.selected_index < len(opts):
        lines += ["", f"✔️ Your answer: <b>{LETTERS[q.selected_index]}</b>"]
    if test.kind == "ai":
        lines += ["", "<i>AI-generated practice question — not an admin-verified exam question.</i>"]
    return "\n".join(lines)


def question_keyboard(test: AiTest, questions: list[AiTestQuestion], idx: int) -> InlineKeyboardMarkup:
    q = questions[idx]
    opts = q.options()
    rows: list[list[tuple[str, str]]] = []
    for i, o in enumerate(opts):
        mark = "✔️ " if q.selected_index == i else ""
        rows.append([(mark + button_label(LETTERS[i], o), f"ta:{test.id}:{idx}:{i}")])
    nav: list[tuple[str, str]] = []
    if idx > 0:
        nav.append(("⬅️ Previous", f"tn:{test.id}:{idx - 1}"))
    if idx < len(questions) - 1:
        nav.append(("Next ➡️" if q.selected_index is not None else "Skip ➡️", f"tn:{test.id}:{idx + 1}"))
    if nav:
        rows.append(nav)
    extra: list[tuple[str, str]] = []
    if any(len(re.sub(r"\s+", " ", o)) > BUTTON_LABEL_LIMIT for o in opts) and not labels_ambiguous(opts):
        extra.append(("🔍 Hide full options" if test.show_full else "🔍 Show full options", f"tx:{test.id}:{idx}"))
    if extra:
        rows.append(extra)
    rows.append([("🏁 Finish Test", f"tf:{test.id}")])
    return inline(rows)


async def show_test_question(bot: Bot, session: AsyncSession, test: AiTest, idx: int, *, message: Message | None = None) -> None:
    """Edit the single active test message; create it only when none exists (no duplicate interfaces)."""
    questions = await load_test_questions(session, test)
    if not questions:
        if message: await message.answer("This test has no questions.")
        return
    if test_expired(test):
        await finalize_test(session, test, questions, status="expired")
        await show_result(bot, session, test, message=message, note="⏰ Time is over — the test was submitted automatically.")
        return
    idx = max(0, min(idx, len(questions) - 1))
    test.current_index = idx
    text, markup = render_question_text(test, questions, idx), question_keyboard(test, questions, idx)
    if test.chat_id and test.message_id:
        try:
            await bot.edit_message_text(text, chat_id=test.chat_id, message_id=test.message_id, reply_markup=markup)
            return
        except TelegramBadRequest as e:
            if "message is not modified" in str(e):
                return
    chat_id = test.chat_id or (message.chat.id if message else None)
    if not chat_id:
        return
    sent = await bot.send_message(chat_id, text, reply_markup=markup, protect_content=True)
    test.chat_id, test.message_id = sent.chat.id, sent.message_id
    await session.flush()


def result_card(test: AiTest) -> str:
    took = ""
    if test.started_at and test.completed_at:
        secs = int((test.completed_at - test.started_at).total_seconds())
        took = f"\n⏱ Time taken: {secs // 60} min {secs % 60} s"
    kind = "Admin-verified questions" if test.kind == "mock" else "AI-generated practice questions"
    return ("🏁 <b>TEST COMPLETED</b>\n\n"
            f"{'📝' if test.kind == 'mock' else '🧪'} {esc(test.topic)}\n<i>{kind}</i>\n\n"
            f"Total questions: {test.question_count}\n✅ Correct: {test.correct}\n❌ Incorrect: {test.incorrect}\n⏭ Unanswered: {test.unanswered}\n\n"
            f"🎯 Score: <b>{test.correct}/{test.question_count}</b>\n📊 Accuracy: <b>{test.accuracy:.0f}%</b>{took}")


def result_keyboard(test: AiTest) -> InlineKeyboardMarkup:
    return inline([
        [("📖 Review Answers", f"tr:{test.id}:0"), ("💡 Explanations", f"tr:{test.id}:0:x")],
        [("🔄 Take Another Test", "gt:new" if test.kind == "ai" else "mock:list"), ("📜 Test History", "th:0")],
        [("🏠 Home", "menu:home")],
    ])


async def show_result(bot: Bot, session: AsyncSession, test: AiTest, *, message: Message | None = None, note: str = "") -> None:
    text = (note + "\n\n" if note else "") + result_card(test)
    chat_id = test.chat_id or (message.chat.id if message else None)
    if not chat_id:
        return
    if test.message_id:
        try:
            await bot.edit_message_text(text, chat_id=chat_id, message_id=test.message_id, reply_markup=result_keyboard(test))
        except TelegramBadRequest:
            await bot.send_message(chat_id, text, reply_markup=result_keyboard(test), protect_content=True)
    else:
        await bot.send_message(chat_id, text, reply_markup=result_keyboard(test), protect_content=True)
    user = await session.get(User, test.user_id)
    await bot.send_message(chat_id, "Main menu restored.", reply_markup=main_keyboard(bool(user and user.is_admin)))


async def begin_test_ui(bot: Bot, session: AsyncSession, message: Message, test: AiTest) -> None:
    """Remove the persistent keyboard, then post the single test message."""
    intro = await message.answer("🎯 Test mode — the menu is hidden until you finish. Use /stop to leave the test.",
                                 reply_markup=ReplyKeyboardRemove())
    test.chat_id = message.chat.id
    await show_test_question(bot, session, test, test.current_index, message=message)


async def resume_prompt(message: Message, session: AsyncSession, active: AiTest) -> None:
    answered = int((await session.execute(select(func.count()).select_from(AiTestQuestion).where(
        AiTestQuestion.test_id == active.id, AiTestQuestion.selected_index.is_not(None)))).scalar_one())
    await message.answer(f"You have an unfinished test: <b>{esc(active.topic)}</b> ({answered}/{active.question_count} answered).",
                         reply_markup=inline([[("▶️ Resume", f"tn:{active.id}:{active.current_index}")],
                                              [("🏁 Submit as is", f"tf:{active.id}")],
                                              [("🗑 Abandon", f"gt:discard:{active.id}")]]))


async def owned_active_test(cb: CallbackQuery, session: AsyncSession, db_user: User, test_id: int) -> AiTest | None:
    test = await load_owned_test(session, test_id, db_user)
    if not test:
        await cb.answer("This test is not yours or no longer exists.", show_alert=True); return None
    if test.status != "in_progress":
        await cb.answer("This test is already finished.", show_alert=True); return None
    return test


@router.callback_query(F.data.startswith("ta:"))
async def test_answer(cb: CallbackQuery, session: AsyncSession, db_user: User, bot: Bot):
    try:
        test_id, idx, opt = map(int, cb.data.split(":")[1:])
    except ValueError:
        await cb.answer("Invalid button.", show_alert=True); return
    test = await owned_active_test(cb, session, db_user, test_id)
    if not test: return
    questions = await load_test_questions(session, test)
    if test_expired(test):
        await finalize_test(session, test, questions, status="expired"); await cb.answer("Time is up.", show_alert=True)
        await show_result(bot, session, test, message=cb.message, note="⏰ Time is over — submitted automatically."); return
    if not (0 <= idx < len(questions)):
        await cb.answer("Invalid question.", show_alert=True); return
    q = questions[idx]
    if not (0 <= opt < len(q.options())):
        await cb.answer("Invalid option.", show_alert=True); return
    if q.selected_index == opt:
        await cb.answer("Already recorded."); return          # repeated press → no change, no double scoring
    q.selected_index, q.answered_at = opt, now_utc()
    await session.flush()
    await cb.answer(f"Recorded: {LETTERS[opt]}")
    if cb.message and not test.message_id:
        test.chat_id, test.message_id = cb.message.chat.id, cb.message.message_id
    await show_test_question(bot, session, test, idx, message=cb.message)


@router.callback_query(F.data.startswith("tn:"))
async def test_navigate(cb: CallbackQuery, session: AsyncSession, db_user: User, bot: Bot):
    try:
        test_id, idx = map(int, cb.data.split(":")[1:])
    except ValueError:
        await cb.answer("Invalid button.", show_alert=True); return
    test = await owned_active_test(cb, session, db_user, test_id)
    if not test: return
    await cb.answer()
    if not test.message_id and cb.message:
        # Resuming from a prompt message: hide menu and open a fresh test message.
        await cb.message.answer("▶️ Resuming your test…", reply_markup=ReplyKeyboardRemove())
        test.chat_id = cb.message.chat.id
        db_user.active_test_id = test.id
    await show_test_question(bot, session, test, idx, message=cb.message)


@router.callback_query(F.data.startswith("tx:"))
async def test_toggle_full(cb: CallbackQuery, session: AsyncSession, db_user: User, bot: Bot):
    try:
        test_id, idx = map(int, cb.data.split(":")[1:])
    except ValueError:
        await cb.answer("Invalid button.", show_alert=True); return
    test = await owned_active_test(cb, session, db_user, test_id)
    if not test: return
    test.show_full = not test.show_full
    await cb.answer()
    await show_test_question(bot, session, test, idx, message=cb.message)


@router.callback_query(F.data.startswith("tf:"))
async def test_finish(cb: CallbackQuery, session: AsyncSession, db_user: User, bot: Bot):
    test_id = parse_int(cb.data.split(":")[1], 0) or 0
    test = await load_owned_test(session, test_id, db_user)
    if not test:
        await cb.answer("This test is not yours or no longer exists.", show_alert=True); return
    questions = await load_test_questions(session, test)
    if not await finalize_test(session, test, questions):
        await cb.answer("Already submitted."); return
    await audit(session, db_user.telegram_id, "test.finish", str(test.id), f"{test.correct}/{test.question_count}")
    await cb.answer("Submitted ✅")
    if cb.message and not test.message_id:
        test.chat_id, test.message_id = cb.message.chat.id, cb.message.message_id
    await show_result(bot, session, test, message=cb.message)


@router.callback_query(F.data.startswith("tv:"))
async def test_view_result(cb: CallbackQuery, session: AsyncSession, db_user: User):
    test = await load_owned_test(session, parse_int(cb.data.split(":")[1], 0) or 0, db_user)
    if not test or test.status == "in_progress":
        await cb.answer("Result not available.", show_alert=True); return
    await cb.answer()
    await safe_edit(cb.message, result_card(test), result_keyboard(test), protect=True)


def render_review_page(test: AiTest, questions: list[AiTestQuestion], page: int, explain: bool) -> tuple[str, InlineKeyboardMarkup]:
    pages = max(1, (len(questions) + REVIEW_PAGE - 1) // REVIEW_PAGE)
    page = max(0, min(page, pages - 1))
    chunk = questions[page * REVIEW_PAGE:(page + 1) * REVIEW_PAGE]
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
        block = f"<b>Q{q.position + 1}.</b> {esc(q.text)}\nYour answer: {yours}\nCorrect: <b>{esc(correct_txt)}</b>"
        if explain and q.explanation:
            block += f"\n💡 {esc(q.explanation)}"
        blocks.append(block)
    sfx = ":x" if explain else ""
    nav: list[tuple[str, str]] = []
    if page > 0: nav.append(("⬅️ Previous", f"tr:{test.id}:{page - 1}{sfx}"))
    if page < pages - 1: nav.append(("Next ➡️", f"tr:{test.id}:{page + 1}{sfx}"))
    rows = ([nav] if nav else []) + [[("💡 Hide explanations" if explain else "💡 Explanations", f"tr:{test.id}:{page}{'' if explain else ':x'}"),
                                       ("📊 Result", f"tv:{test.id}")], [("📜 Test History", "th:0"), ("🏠 Home", "menu:home")]]
    return "\n\n".join(blocks), inline(rows)


@router.callback_query(F.data.startswith("tr:"))
async def test_review(cb: CallbackQuery, session: AsyncSession, db_user: User):
    parts = cb.data.split(":")
    test = await load_owned_test(session, parse_int(parts[1], 0) or 0, db_user)
    if not test or test.status == "in_progress":
        await cb.answer("Review is available after the test is finished.", show_alert=True); return
    page = parse_int(parts[2], 0) if len(parts) > 2 else 0
    explain = len(parts) > 3 and parts[3] == "x"
    await cb.answer()
    text, kb = render_review_page(test, await load_test_questions(session, test), page or 0, explain)
    await safe_edit(cb.message, text, kb, protect=True)


async def show_test_history(message: Message, session: AsyncSession, user: User, page: int = 0, *, edit: bool = False) -> None:
    total = int((await session.execute(select(func.count()).select_from(AiTest).where(AiTest.user_id == user.id, AiTest.status != "in_progress"))).scalar_one())
    pages = max(1, (total + HISTORY_PAGE - 1) // HISTORY_PAGE)
    page = max(0, min(page, pages - 1))
    tests = list((await session.execute(select(AiTest).where(AiTest.user_id == user.id, AiTest.status != "in_progress")
                                        .order_by(AiTest.id.desc()).offset(page * HISTORY_PAGE).limit(HISTORY_PAGE))).scalars())
    if not tests:
        text, kb = "📜 <b>Test History</b>\n\nNo tests yet. Generate an AI test or take a mock test to see results here.", inline([[("🧪 Generate AI Test", "gt:new")], [("🏠 Home", "menu:home")]])
    else:
        lines = [f"📜 <b>Test History</b> (page {page + 1}/{pages}, {total} tests)", ""]
        rows: list[list[tuple[str, str]]] = []
        for t in tests:
            icon = "📝" if t.kind == "mock" else "🧪"
            lines.append(f"{icon} <b>{esc(t.topic)}</b> — {t.correct}/{t.question_count} ({t.accuracy:.0f}%) · {fmt_date(t.completed_at or t.created_at)}")
            rows.append([(f"{icon} {t.topic[:28]} · {t.correct}/{t.question_count}", f"tv:{t.id}")])
        nav: list[tuple[str, str]] = []
        if page > 0: nav.append(("⬅️", f"th:{page - 1}"))
        if page < pages - 1: nav.append(("➡️", f"th:{page + 1}"))
        if nav: rows.append(nav)
        rows.append([("🏠 Home", "menu:home")])
        text, kb = "\n".join(lines), inline(rows)
    if edit:
        await safe_edit(message, text, kb)
    else:
        await message.answer(text, reply_markup=kb)


@router.callback_query(F.data.startswith("th:"))
async def test_history_callback(cb: CallbackQuery, session: AsyncSession, db_user: User):
    await cb.answer()
    await show_test_history(cb.message, session, db_user, parse_int(cb.data.split(":")[1], 0) or 0, edit=True)


async def stop_active_test(bot: Bot, session: AsyncSession, user: User, chat_id: int, *, abandon: bool) -> bool:
    """/stop: submit (score saved answers) or abandon the active test. Never touches history or the account."""
    test = await active_test_for(session, user)
    if not test:
        user.active_test_id = None
        return False
    questions = await load_test_questions(session, test)
    await finalize_test(session, test, questions, status="abandoned" if abandon else "completed")
    test.chat_id = test.chat_id or chat_id
    if abandon:
        if test.message_id:
            try: await bot.edit_message_text(f"🛑 Test <b>{esc(test.topic)}</b> was abandoned.", chat_id=test.chat_id, message_id=test.message_id)
            except TelegramBadRequest: pass
    else:
        await show_result(bot, session, test, note="🛑 Test stopped — scored from the answers you saved.")
    return True



# ============================ AI Test Generator — setup flow ============================
def topic_keyboard(exams: list[Exam]) -> InlineKeyboardMarkup:
    names_lower = {t.lower() for t in COMMON_TEST_TOPICS}
    buttons: list[tuple[str, str]] = [(t, f"gt:t:{i}") for i, t in enumerate(COMMON_TEST_TOPICS)]
    buttons += [(e.name, f"gt:e:{e.id}") for e in exams if e.name.lower() not in names_lower][:10]
    rows = [buttons[i:i + 2] for i in range(0, len(buttons), 2)]
    rows.append([("✍️ Custom Topic", "gt:c")]); rows.append([("❌ Cancel", "gt:x")])
    return inline(rows)


def count_keyboard(max_q: int) -> InlineKeyboardMarkup:
    presets = [n for n in (5, 10, 20, 30, 50) if n <= max_q]
    rows = [[(f"{n} Questions", f"gt:n:{n}") for n in presets[i:i + 2]] for i in range(0, len(presets), 2)]
    rows.append([("🔢 Custom Number", "gt:nc")]); rows.append([("⬅️ Back", "gt:bt"), ("❌ Cancel", "gt:x")])
    return inline(rows)


def difficulty_keyboard(lang: str) -> InlineKeyboardMarkup:
    def mark(v: str) -> str: return " ✅" if lang == v else ""
    return inline([
        [("🟢 Easy", "gt:d:easy"), ("🟡 Medium", "gt:d:medium")],
        [("🔴 Hard", "gt:d:hard"), ("🎲 Mixed", "gt:d:mixed")],
        [("🇬🇧 English" + mark("en"), "gt:l:en"), ("🇮🇳 हिन्दी" + mark("hi"), "gt:l:hi")],
        [("⬅️ Back", "gt:bn"), ("❌ Cancel", "gt:x")],
    ])


async def aitest_max_questions(session: AsyncSession, user: User) -> int:
    return max(AI_TEST_MIN, min(AI_TEST_MAX_HARD, (await effective_limits(session, user)).get("aitest_max_q", 10)))


async def aitest_available(message: Message, session: AsyncSession, user: User) -> bool:
    if not await feature_enabled(session, "aitest"):
        await message.answer("🧪 AI Test generation is temporarily disabled by the administrator."); return False
    if not await current_api_key(session):
        await message.answer(AI_ERROR_TEXT["no_key"]); return False
    ok, why = await check_quota(session, user, "aitest_daily", "aitest")
    if not ok:
        await send_html(message, why, url_button_rows([[("💳 Subscription", "sub:open", False)]])); return False
    return True


async def start_test_setup(message: Message, session: AsyncSession, user: User, state: FSMContext) -> None:
    active = await active_test_for(session, user)
    if active:
        await resume_prompt(message, session, active); return
    if not await aitest_available(message, session, user):
        return
    await state.clear()
    await show_topic_step(message, session, state, edit=False)


async def show_topic_step(message: Message, session: AsyncSession, state: FSMContext, *, edit: bool) -> None:
    exams = list((await session.execute(select(Exam).where(Exam.active.is_(True)).order_by(Exam.name))).scalars())
    await state.set_state(TestFlow.topic)
    text = ("🧪 <b>Generate AI Test</b>\n\nStep 1/3 — Choose an exam or topic, or tap ✍️ Custom Topic to type your own "
            "(e.g. <i>BPSC — Bihar History</i>, <i>Photosynthesis</i>).\n\n<i>AI practice questions are generated on the fly and are "
            "not admin-verified exam questions.</i>")
    await (safe_edit(message, text, topic_keyboard(exams)) if edit else message.answer(text, reply_markup=topic_keyboard(exams)))


async def show_count_step(message: Message, session: AsyncSession, user: User, state: FSMContext, *, edit: bool) -> None:
    data = await state.get_data(); await state.set_state(TestFlow.count)
    max_q = await aitest_max_questions(session, user)
    text = f"🧪 <b>Generate AI Test</b>\n\nTopic: <b>{esc(data.get('topic'))}</b>\n\nStep 2/3 — How many questions? (1–{max_q} on your plan)"
    await (safe_edit(message, text, count_keyboard(max_q)) if edit else message.answer(text, reply_markup=count_keyboard(max_q)))


async def show_difficulty_step(message: Message, state: FSMContext, *, edit: bool) -> None:
    data = await state.get_data(); await state.set_state(TestFlow.difficulty)
    lang = data.get("lang", "en")
    text = (f"🧪 <b>Generate AI Test</b>\n\nTopic: <b>{esc(data.get('topic'))}</b>\nQuestions: <b>{data.get('count')}</b>\n"
            f"Language: <b>{'हिन्दी' if lang == 'hi' else 'English'}</b>\n\nStep 3/3 — Pick a difficulty to start generating.")
    await (safe_edit(message, text, difficulty_keyboard(lang)) if edit else message.answer(text, reply_markup=difficulty_keyboard(lang)))


GENERATING_USERS: set[int] = set()


@router.callback_query(F.data.startswith("gt:"))
async def test_setup_callback(cb: CallbackQuery, session: AsyncSession, db_user: User, state: FSMContext, bot: Bot):
    parts = cb.data.split(":")
    action, arg = (parts[1] if len(parts) > 1 else ""), (parts[2] if len(parts) > 2 else "")
    if not await gate(cb, db_user, session, bot): return
    if action == "x":
        await state.clear(); await cb.answer("Cancelled"); await safe_edit(cb.message, "❌ Test setup cancelled."); return
    if action == "new":
        await cb.answer(); await start_test_setup(cb.message, session, db_user, state); return
    if action == "discard":
        test = await load_owned_test(session, parse_int(arg, 0) or 0, db_user)
        if test and test.status == "in_progress":
            await finalize_test(session, test, await load_test_questions(session, test), status="abandoned")
        await cb.answer("Abandoned"); await safe_edit(cb.message, "🗑 Unfinished test abandoned.")
        await show_home(cb.message, db_user); return
    current = await state.get_state()
    if current not in (TestFlow.topic.state, TestFlow.count.state, TestFlow.difficulty.state, TestFlow.custom_topic.state, TestFlow.custom_count.state):
        await cb.answer("This setup screen has expired. Start again from 🧪 Generate AI Test.", show_alert=True); return
    if action == "t" and arg.isdigit() and int(arg) < len(COMMON_TEST_TOPICS):
        await state.update_data(topic=COMMON_TEST_TOPICS[int(arg)]); await cb.answer()
        await show_count_step(cb.message, session, db_user, state, edit=True); return
    if action == "e":
        exam = await session.get(Exam, parse_int(arg, 0) or 0)
        if not exam: await cb.answer("Exam not found.", show_alert=True); return
        await state.update_data(topic=exam.name); await cb.answer()
        await show_count_step(cb.message, session, db_user, state, edit=True); return
    if action == "c":
        await state.set_state(TestFlow.custom_topic); await cb.answer()
        await safe_edit(cb.message, "✍️ Type your topic (3–120 characters). Send /cancel to stop.", inline([[("❌ Cancel", "gt:x")]])); return
    if action == "bt":
        await cb.answer(); await show_topic_step(cb.message, session, state, edit=True); return
    if action == "n" and arg.isdigit():
        n = int(arg); max_q = await aitest_max_questions(session, db_user)
        if not (AI_TEST_MIN <= n <= max_q):
            await cb.answer(f"Choose between {AI_TEST_MIN} and {max_q}.", show_alert=True); return
        await state.update_data(count=n); await cb.answer(); await show_difficulty_step(cb.message, state, edit=True); return
    if action == "nc":
        await state.set_state(TestFlow.custom_count); await cb.answer()
        await safe_edit(cb.message, f"🔢 Send a number between {AI_TEST_MIN} and {await aitest_max_questions(session, db_user)}.", inline([[("⬅️ Back", "gt:bn"), ("❌ Cancel", "gt:x")]])); return
    if action == "bn":
        await cb.answer(); await show_count_step(cb.message, session, db_user, state, edit=True); return
    if action == "l" and arg in ("en", "hi"):
        await state.update_data(lang=arg); await cb.answer(); await show_difficulty_step(cb.message, state, edit=True); return
    if action == "d" and arg in AI_TEST_DIFFICULTIES:
        await cb.answer(); await run_generation(cb.message, session, db_user, state, arg, bot); return
    await cb.answer("Unknown action.", show_alert=True)


@router.message(TestFlow.custom_topic, F.text)
async def custom_topic_input(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    topic = re.sub(r"\s+", " ", message.text or "").strip()
    if _is_cmd(message): raise SkipHandler
    if not (3 <= len(topic) <= 120):
        await message.answer("Please send a topic between 3 and 120 characters."); return
    await state.update_data(topic=topic)
    await show_count_step(message, session, db_user, state, edit=False)


@router.message(TestFlow.custom_count, F.text)
async def custom_count_input(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    if _is_cmd(message): raise SkipHandler
    n = parse_int(message.text or "", None); max_q = await aitest_max_questions(session, db_user)
    if n is None or not (AI_TEST_MIN <= n <= max_q):
        await message.answer(f"Send a whole number between {AI_TEST_MIN} and {max_q}."); return
    await state.update_data(count=n)
    await show_difficulty_step(message, state, edit=False)


async def run_generation(message: Message, session: AsyncSession, user: User, state: FSMContext, difficulty: str, bot: Bot) -> None:
    data = await state.get_data()
    topic, count, lang = str(data.get("topic") or ""), int(data.get("count") or 0), str(data.get("lang") or "en")
    if not topic or not count:
        await state.clear(); await message.answer("Setup data was lost. Please start again from 🧪 Generate AI Test."); return
    if user.id in GENERATING_USERS:
        await message.answer("⏳ Your previous test is still being generated. Please wait."); return
    ok, why = await check_quota(session, user, "aitest_daily", "aitest")
    if not ok:
        await state.clear(); await send_html(message, why); return
    api_key = await current_api_key(session)
    await state.set_state(TestFlow.generating)
    GENERATING_USERS.add(user.id)
    progress_msg = await safe_edit(message, f"⚙️ Generating <b>{count}</b> {difficulty} questions on <b>{esc(topic)}</b>…\n\n0/{count} ready")
    await session.commit()
    last = [0.0]
    async def progress(done: int, total: int) -> None:
        if time.monotonic() - last[0] > 2.5:
            last[0] = time.monotonic()
            await safe_edit(progress_msg, f"⚙️ Generating <b>{total}</b> {difficulty} questions on <b>{esc(topic)}</b>…\n\n{done}/{total} ready")
    try:
        questions, err = await generate_test_questions(topic, count, difficulty, lang, api_key, progress)
    finally:
        GENERATING_USERS.discard(user.id)
        await state.clear()
    await session.refresh(user)
    if user.status == "banned" or (not user.access_granted and not user.is_admin):
        return
    if err:
        txt = GENERATION_ERROR_TEXT.get(err) or AI_ERROR_TEXT.get(err) or AI_ERROR_TEXT["http"]
        if questions and err == "incomplete" and len(questions) >= max(AI_TEST_MIN, count // 2):
            await safe_edit(progress_msg, f"⚠️ Only {len(questions)} of {count} questions passed validation.",
                            inline([[("▶️ Start with these", f"gs:{len(questions)}")], [("🔄 Try again", "gt:new")], [("🏠 Home", "menu:home")]]))
            await state.update_data(partial={"topic": topic, "difficulty": difficulty, "lang": lang, "questions": questions, "requested": count})
            return
        await safe_edit(progress_msg, txt, inline([[("🔄 Try again", "gt:new")], [("🏠 Home", "menu:home")]])); return
    await record_usage(session, user, "aitest")
    test = await create_test_session(session, user, kind="ai", topic=topic, questions=questions, mode="practice",
                                     difficulty=difficulty, lang=lang, requested=count)
    await audit(session, user.telegram_id, "aitest.create", str(test.id), f"{topic} x{count}")
    await try_delete(progress_msg)
    await begin_test_ui(bot, session, message, test)


@router.callback_query(F.data.startswith("gs:"))
async def start_partial_test(cb: CallbackQuery, session: AsyncSession, db_user: User, state: FSMContext, bot: Bot):
    data = (await state.get_data()).get("partial")
    if not data:
        await cb.answer("These questions have expired. Generate again.", show_alert=True); return
    await state.clear(); await cb.answer()
    await record_usage(session, db_user, "aitest")
    test = await create_test_session(session, db_user, kind="ai", topic=data["topic"], questions=data["questions"], mode="practice",
                                     difficulty=data["difficulty"], lang=data["lang"], requested=data["requested"])
    await try_delete(cb.message)
    await begin_test_ui(bot, session, cb.message, test)


# ============================ Mock tests (admin bank, approved questions only) ============================
async def list_mock_tests(message: Message, session: AsyncSession, user: User, *, edit: bool = False) -> None:
    if not await feature_enabled(session, "mock"):
        await message.answer("📝 Mock tests are temporarily disabled by the administrator."); return
    if not user.selected_exam_id:
        await message.answer("Select your exam first."); await show_exams(message, session); return
    tests = list((await session.execute(select(MockTest).where(MockTest.exam_id == user.selected_exam_id, MockTest.published.is_(True)).order_by(MockTest.id.desc()))).scalars())
    if not tests:
        await message.answer("No mock tests have been published for your exam yet."); return
    rows = [[(f"{t.title} · {t.duration} min", f"mockinfo:{t.id}")] for t in tests] + [[("🏠 Home", "menu:home")]]
    text = "📝 <b>Mock Tests</b> — admin-verified question sets. Choose one:"
    await (safe_edit(message, text, inline(rows)) if edit else message.answer(text, reply_markup=inline(rows)))


@router.callback_query(F.data == "mock:list")
async def mock_list_cb(cb: CallbackQuery, session: AsyncSession, db_user: User, bot: Bot):
    if not await gate(cb, db_user, session, bot): return
    await cb.answer(); await list_mock_tests(cb.message, session, db_user)


async def mock_servable_questions(session: AsyncSession, test_id: int) -> list[Question]:
    qids = list((await session.execute(select(MockQuestion.question_id).where(MockQuestion.test_id == test_id).order_by(MockQuestion.position))).scalars())
    out: list[Question] = []
    for qid in qids:
        q = await session.get(Question, qid)
        if q and is_servable(q):
            out.append(q)
    return out


@router.callback_query(F.data.startswith("mockinfo:"))
async def mock_info(cb: CallbackQuery, session: AsyncSession, db_user: User):
    test = await session.get(MockTest, parse_int(cb.data.split(":")[1], 0) or 0)
    if not test or not test.published:
        await cb.answer("Test unavailable.", show_alert=True); return
    count = len(await mock_servable_questions(session, test.id))
    await cb.answer()
    await safe_edit(cb.message, f"📝 <b>{esc(test.title)}</b>\nQuestions: {count} (admin-verified)\nTime limit: {test.duration} minutes\n"
                    "Exam mode: answers are revealed only after you submit. The timer starts when you press Start.",
                    inline([[("▶️ Start test", f"mockstart:{test.id}")], [("⬅️ Back", "mock:list")]]))


@router.callback_query(F.data.startswith("mockstart:"))
async def mock_start(cb: CallbackQuery, session: AsyncSession, db_user: User, bot: Bot):
    if not await gate(cb, db_user, session, bot): return
    test = await session.get(MockTest, parse_int(cb.data.split(":")[1], 0) or 0)
    if not test or not test.published:
        await cb.answer("Test unavailable.", show_alert=True); return
    if await active_test_for(session, db_user):
        await cb.answer("Finish or stop your current test first (/stop).", show_alert=True); return
    ok, why = await check_quota(session, db_user, "mock_daily", "mock")
    if not ok:
        await cb.answer(); await send_html(cb.message, why, url_button_rows([[("💳 Subscription", "sub:open", False)]])); return
    bank = await mock_servable_questions(session, test.id)
    if not bank:
        await cb.answer("This test has no approved questions yet.", show_alert=True); return
    snaps = [shuffled_snapshot(q) for q in bank]
    session_test = await create_test_session(session, db_user, kind="mock", topic=test.title, questions=snaps, mode="exam",
                                             mock_test_id=test.id, duration_min=test.duration, lang=db_user.language)
    await record_usage(session, db_user, "mock")
    await audit(session, db_user.telegram_id, "mock.start", str(session_test.id), test.title)
    await cb.answer("Test started")
    await try_delete(cb.message)
    await begin_test_ui(bot, session, cb.message, session_test)



# ============================ Trial & subscription screens ============================
async def plan_config(session: AsyncSession) -> dict[str, Any]:
    return {
        "name": await get_setting(session, "plan_name", "Exam Yatra Premium"),
        "price": await setting_float(session, "plan_price", 99.0),
        "validity_days": await setting_int(session, "plan_validity_days", -1),      # -1 = not configured, 0 = lifetime
        "upi_id": (await get_setting(session, "upi_id", "")).strip(),
        "payee": (await get_setting(session, "upi_payee", "")).strip(),
        "purchases_enabled": await setting_bool(session, "purchases_enabled", True),
    }


def validity_label(days: int) -> str:
    return "not configured" if days < 0 else ("Lifetime" if days == 0 else f"{days} days")


def upi_id_valid(upi: str) -> bool:
    return bool(re.fullmatch(r"[A-Za-z0-9.\-_]{2,256}@[A-Za-z]{2,64}", upi or ""))


def build_upi_uri(upi_id: str, payee: str, amount: float, note: str) -> str:
    from urllib.parse import quote
    params = [f"pa={quote(upi_id)}"]
    if payee: params.append(f"pn={quote(payee[:50])}")
    params += [f"am={amount:.2f}", "cu=INR", f"tn={quote(note[:50])}"]
    return "upi://pay?" + "&".join(params)


def make_qr_png(data: str) -> bytes:
    import qrcode
    img = qrcode.make(data, box_size=8, border=2)
    buf = io.BytesIO(); img.save(buf, format="PNG")
    return buf.getvalue()


def subscription_status_text(user: User) -> str:
    refresh_entitlements(user)
    tier = user_tier(user)
    lines = [f"Current plan: <b>{TIER_LABEL[tier]}</b>"]
    if user.subscription_status == "active":
        lines.append("Premium valid until: <b>" + (fmt_dt(user.subscription_expiry) if user.subscription_expiry else "Lifetime") + "</b>")
    elif user.subscription_status == "expired":
        lines.append(f"Premium expired on {fmt_dt(user.subscription_expiry)}")
    if user.trial_status == "active":
        lines.append(f"Free trial: {trial_days_left(user)} day(s) left (ends {fmt_dt(user.trial_ends_at)})")
    elif user.trial_status == "expired":
        lines.append(f"Free trial ended on {fmt_dt(user.trial_ends_at)}")
    return "\n".join(lines)


async def show_subscription(message: Message, session: AsyncSession, user: User, *, edit: bool = False) -> None:
    plan = await plan_config(session)
    contact = await support_contact(session)
    text = ("💳 <b>Subscription</b>\n\n" + subscription_status_text(user) + "\n\n━━━━━━━━━━━━━━━━━━━━\n"
            f"⭐ <b>{esc(plan['name'])}</b>\nPrice: <b>₹{plan['price']:.0f}</b>\nValidity: <b>{validity_label(plan['validity_days'])}</b>\n"
            "Usage: Unlimited AI Tutor, image solving, AI tests, mock tests and study materials within the validity period.")
    rows: list[list[tuple[str, str, bool]]] = []
    pending = (await session.execute(select(PaymentRequest).where(PaymentRequest.user_id == user.id, PaymentRequest.status.in_(
        [PAY_AWAITING_UTR, PAY_AWAITING_SHOT, PAY_PENDING])).order_by(PaymentRequest.id.desc()).limit(1))).scalars().first()
    if pending:
        text += f"\n\n🕒 You have a payment request <b>#{pending.id}</b> in state <i>{pending.status.replace('_', ' ')}</i>."
        if pending.status in (PAY_AWAITING_UTR, PAY_AWAITING_SHOT):
            rows.append([("▶️ Continue payment", f"pay:resume:{pending.id}", False), ("❌ Cancel request", f"pay:cancel:{pending.id}", False)])
    elif plan["validity_days"] < 0 or not upi_id_valid(plan["upi_id"]):
        text += "\n\n⚠️ Purchases are not available yet: the administrator has not finished configuring the plan (validity / UPI ID)."
    elif not plan["purchases_enabled"]:
        text += "\n\n⚠️ Purchases are temporarily disabled."
    elif not await feature_enabled(session, "payments"):
        text += "\n\n⚠️ Payments are temporarily disabled."
    else:
        rows.append([("🛒 Buy Subscription", "pay:buy", False)])
    rows += support_rows(contact)
    rows.append([("🏠 Home", "menu:home", False)])
    kb = url_button_rows(rows)
    await (safe_edit(message, text, kb) if edit else message.answer(text, reply_markup=kb))


@router.callback_query(F.data == "sub:open")
async def sub_open(cb: CallbackQuery, session: AsyncSession, db_user: User):
    await cb.answer(); await show_subscription(cb.message, session, db_user)


# ============================ Manual UPI payment flow ============================
@router.callback_query(F.data.startswith("pay:"))
async def payment_callbacks(cb: CallbackQuery, session: AsyncSession, db_user: User, state: FSMContext, bot: Bot):
    parts = cb.data.split(":")
    action = parts[1] if len(parts) > 1 else ""
    if not await gate(cb, db_user, session, bot): return
    if action == "buy":
        await cb.answer(); await start_purchase(cb.message, session, db_user, state); return
    if action in ("resume", "cancel"):
        req = await session.get(PaymentRequest, parse_int(parts[2], 0) or 0) if len(parts) > 2 else None
        if not req or req.user_id != db_user.id:
            await cb.answer("Payment request not found.", show_alert=True); return
        if action == "cancel":
            if req.status not in (PAY_AWAITING_UTR, PAY_AWAITING_SHOT):
                await cb.answer("This request can no longer be cancelled.", show_alert=True); return
            req.status = PAY_CANCELLED; await session.flush()
            if (await state.get_state() or "").startswith("PaymentFlow"): await state.clear()
            await cb.answer("Cancelled"); await show_subscription(cb.message, session, db_user, edit=True); return
        await cb.answer()
        if req.status == PAY_AWAITING_UTR:
            await state.set_state(PaymentFlow.utr); await state.update_data(payment_id=req.id); await ask_utr(cb.message)
        elif req.status == PAY_AWAITING_SHOT:
            await state.set_state(PaymentFlow.screenshot); await state.update_data(payment_id=req.id); await ask_screenshot(cb.message)
        else:
            await show_subscription(cb.message, session, db_user, edit=True)
        return
    await cb.answer("Unknown action.", show_alert=True)


async def start_purchase(message: Message, session: AsyncSession, user: User, state: FSMContext) -> None:
    plan = await plan_config(session)
    contact = await support_contact(session)
    if not await feature_enabled(session, "payments") or not plan["purchases_enabled"]:
        await message.answer("Purchases are temporarily disabled."); return
    if plan["validity_days"] < 0:
        await message.answer("⚠️ The subscription validity has not been configured by the administrator yet, so payments cannot be accepted.",
                             reply_markup=url_button_rows(support_rows(contact)) if contact else None); return
    if not upi_id_valid(plan["upi_id"]):
        await message.answer("⚠️ The payment UPI ID is missing or invalid. Please contact the admin.",
                             reply_markup=url_button_rows(support_rows(contact)) if contact else None); return
    refresh_entitlements(user)
    if user.subscription_status == "active":
        await message.answer("✅ Your Premium subscription is already active" + (f" until {fmt_dt(user.subscription_expiry)}." if user.subscription_expiry else " (lifetime).")); return
    if await active_test_for(session, user):
        await message.answer("Please finish or /stop your active test before starting a payment."); return
    existing = (await session.execute(select(PaymentRequest).where(PaymentRequest.user_id == user.id, PaymentRequest.status.in_(
        [PAY_AWAITING_UTR, PAY_AWAITING_SHOT, PAY_PENDING])))).scalars().first()
    if existing:
        if existing.status == PAY_PENDING:
            await message.answer(f"🕒 Payment request #{existing.id} is already awaiting admin approval."); return
        req = existing
    else:
        req = PaymentRequest(user_id=user.id, plan_name=plan["name"][:64], amount=float(plan["price"]), validity_days=int(plan["validity_days"]))
        session.add(req); await session.flush()
        await audit(session, user.telegram_id, "payment.create", str(req.id), f"₹{req.amount:.2f}")
    note = f"ExamYatra #{req.id}"
    uri = build_upi_uri(plan["upi_id"], plan["payee"], req.amount, note)
    caption = (f"🛒 <b>{esc(req.plan_name)}</b>\n\n💰 Amount: <b>₹{req.amount:.2f}</b>\n📆 Validity: <b>{validity_label(req.validity_days)}</b>\n"
               f"🏦 UPI ID: <code>{esc(plan['upi_id'])}</code>" + (f"\n👤 Payee: {esc(plan['payee'])}" if plan["payee"] else "") +
               f"\n📝 Note: <code>{esc(note)}</code>\n\nScan the QR with any UPI app or pay to the UPI ID above with the exact amount.\n\n"
               "<i>Verification is manual: an administrator checks your reference number and screenshot before activating Premium.</i>")
    try:
        png = make_qr_png(uri)
        await message.answer_photo(BufferedInputFile(png, filename=f"examyatra-{req.id}.png"), caption=caption)
    except Exception as e:                                   # QR library failure must not block paying by UPI ID
        log.warning("QR generation failed: %r", e)
        await message.answer(caption + "\n\n(QR image unavailable — please pay to the UPI ID.)")
    await state.set_state(PaymentFlow.utr); await state.update_data(payment_id=req.id)
    await ask_utr(message)


async def ask_utr(message: Message) -> None:
    await message.answer("1️⃣ After completing your payment, enter your <b>UPI transaction reference number / UTR</b> "
                         f"({UTR_MIN}–{UTR_MAX} letters/digits).\n\nSend /cancel_payment to abort.")


async def ask_screenshot(message: Message) -> None:
    await message.answer("2️⃣ Now send a <b>clear screenshot</b> of your payment confirmation (as a photo or image file).\n\nSend /cancel_payment to abort.")


async def current_payment(session: AsyncSession, user: User, state: FSMContext) -> PaymentRequest | None:
    pid = (await state.get_data()).get("payment_id")
    req = await session.get(PaymentRequest, pid) if pid else None
    if req and req.user_id == user.id:
        return req
    return (await session.execute(select(PaymentRequest).where(PaymentRequest.user_id == user.id, PaymentRequest.status.in_(
        [PAY_AWAITING_UTR, PAY_AWAITING_SHOT])).order_by(PaymentRequest.id.desc()))).scalars().first()


@router.message(Command("cancel_payment"))
async def cancel_payment_cmd(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    req = await current_payment(session, db_user, state)
    if (await state.get_state() or "").startswith("PaymentFlow"): await state.clear()
    if req and req.status in (PAY_AWAITING_UTR, PAY_AWAITING_SHOT):
        req.status = PAY_CANCELLED; await session.flush()
        await message.answer("❌ Payment request cancelled.", reply_markup=main_keyboard(db_user.is_admin))
    else:
        await message.answer("There is no payment in progress.", reply_markup=main_keyboard(db_user.is_admin))


@router.message(PaymentFlow.utr, F.text)
async def payment_utr_input(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    text = (message.text or "").strip()
    if _is_cmd(message): raise SkipHandler
    req = await current_payment(session, db_user, state)
    if not req or req.status != PAY_AWAITING_UTR:
        await state.clear(); await message.answer("This payment request is no longer open. Open 💳 Subscription to start again."); return
    utr = re.sub(r"\s+", "", text).upper()
    if not re.fullmatch(r"[A-Z0-9\-]+", utr) or not (UTR_MIN <= len(utr) <= UTR_MAX):
        await message.answer(f"❌ That doesn't look like a valid reference. Send only the {UTR_MIN}–{UTR_MAX} character UTR / transaction ID (letters and digits)."); return
    dup = (await session.execute(select(PaymentRequest).where(PaymentRequest.utr == utr, PaymentRequest.id != req.id))).scalars().first()
    if dup:
        await message.answer("❌ This reference number has already been submitted. Check it and send the correct one, or contact the admin."); return
    req.utr = utr; req.status = PAY_AWAITING_SHOT
    try:
        await session.flush()
    except IntegrityError:
        await session.rollback(); await message.answer("❌ This reference number has already been submitted."); return
    await state.set_state(PaymentFlow.screenshot)
    await message.answer(f"✅ Reference <code>{esc(utr)}</code> saved.")
    await ask_screenshot(message)


@router.message(PaymentFlow.screenshot, F.photo | F.document)
async def payment_screenshot_input(message: Message, session: AsyncSession, db_user: User, state: FSMContext, bot: Bot):
    req = await current_payment(session, db_user, state)
    if not req or req.status != PAY_AWAITING_SHOT:
        await state.clear(); await message.answer("This payment request is no longer open. Open 💳 Subscription to start again."); return
    if message.photo:
        file_id, meta = message.photo[-1].file_id, {"type": "photo", "size": message.photo[-1].file_size}
    else:
        doc = message.document
        if not (doc.mime_type or "").startswith("image/"):
            await message.answer("❌ Please send the screenshot as a photo or an image file (JPG/PNG), not another document type."); return
        if (doc.file_size or 0) > MAX_IMAGE_BYTES:
            await message.answer("❌ Image too large (max 8 MB)."); return
        file_id, meta = doc.file_id, {"type": "document", "mime": doc.mime_type, "size": doc.file_size, "name": doc.file_name}
    req.screenshot_file_id = file_id; req.screenshot_meta = json.dumps(meta)
    req.status = PAY_PENDING; req.submitted_at = now_utc()
    await session.flush()
    await audit(session, db_user.telegram_id, "payment.submit", str(req.id), req.utr)
    await state.clear()
    await try_delete(message)        # best effort; Telegram may not permit deleting the user's message
    await message.answer("✅ <b>Payment details submitted successfully.</b>\n\nYour payment is awaiting administrator approval. "
                         "Please wait for confirmation — you will be notified here.", reply_markup=main_keyboard(db_user.is_admin))
    await notify_admins_payment(bot, session, req, db_user)


def admin_payment_text(req: PaymentRequest, user: User) -> str:
    uname = f"@{user.username}" if user.username else "—"
    return (f"💰 <b>PAYMENT REVIEW #{req.id}</b>\n\nUser: {esc(user.full_name)} ({uname})\nTelegram ID: <code>{user.telegram_id}</code>\n"
            f"Plan: {esc(req.plan_name)} · ₹{req.amount:.2f} · {validity_label(req.validity_days)}\nUTR: <code>{esc(req.utr)}</code>\n"
            f"Submitted: {fmt_dt(req.submitted_at)}\nStatus: <b>{esc(req.status.replace('_', ' '))}</b>" +
            (f"\nDecided by {req.decided_by} at {fmt_dt(req.decided_at)}" if req.decided_at else "") +
            (f"\nReason: {esc(req.reject_reason)}" if req.reject_reason else "") +
            "\n\n<i>A screenshot is not proof of payment — please confirm the credit in your UPI app before approving.</i>")


def admin_payment_keyboard(req: PaymentRequest) -> InlineKeyboardMarkup | None:
    if req.status != PAY_PENDING:
        return None
    return inline([[("✅ Approve", f"padm:approve:{req.id}"), ("❌ Reject", f"padm:reject:{req.id}")]])


async def notify_admins_payment(bot: Bot, session: AsyncSession, req: PaymentRequest, user: User) -> None:
    ids: list[list[int]] = []
    for admin_id in ADMIN_IDS:
        try:
            try:
                sent = await bot.send_photo(admin_id, req.screenshot_file_id, caption=admin_payment_text(req, user), reply_markup=admin_payment_keyboard(req))
            except TelegramBadRequest:
                sent = await bot.send_document(admin_id, req.screenshot_file_id, caption=admin_payment_text(req, user), reply_markup=admin_payment_keyboard(req))
            ids.append([admin_id, sent.message_id])
        except TelegramAPIError as e:
            log.warning("Could not notify admin %s about payment %s: %r", admin_id, req.id, e)
    req.admin_message_ids = json.dumps(ids)
    await session.flush()


async def activate_subscription(session: AsyncSession, user: User, plan_name: str, validity_days: int, actor: int, source: str) -> None:
    """Extends an active subscription, otherwise starts from now. validity_days=0 → lifetime."""
    refresh_entitlements(user)
    if validity_days == 0:
        user.subscription_expiry = None
    else:
        base = user.subscription_expiry if (user.subscription_status == "active" and user.subscription_expiry and user.subscription_expiry > now_utc()) else now_utc()
        user.subscription_expiry = base + timedelta(days=validity_days)
    user.subscription_status = "active"; user.current_plan = plan_name[:64]
    await session.flush()
    await audit(session, actor, "subscription.activate", str(user.telegram_id), f"{source}: {plan_name} / {validity_label(validity_days)}")


async def refresh_admin_payment_cards(bot: Bot, req: PaymentRequest, user: User) -> None:
    try:
        for admin_id, mid in json.loads(req.admin_message_ids or "[]"):
            try:
                await bot.edit_message_caption(chat_id=admin_id, message_id=mid, caption=admin_payment_text(req, user), reply_markup=admin_payment_keyboard(req))
            except TelegramAPIError:
                pass
    except ValueError:
        pass


@router.callback_query(F.data.startswith("padm:"))
async def admin_payment_decision(cb: CallbackQuery, session: AsyncSession, db_user: User, state: FSMContext, bot: Bot):
    if not db_user.is_admin or not is_admin_id(cb.from_user.id):
        await cb.answer("Admin only.", show_alert=True); return
    parts = cb.data.split(":")
    action, pid = parts[1], parse_int(parts[2], 0) or 0
    # Row lock on PostgreSQL; on SQLite the single writer serialises us anyway.
    stmt = select(PaymentRequest).where(PaymentRequest.id == pid)
    if not IS_SQLITE:
        stmt = stmt.with_for_update()
    req = (await session.execute(stmt)).scalar_one_or_none()
    if not req:
        await cb.answer("Payment request not found.", show_alert=True); return
    user = await session.get(User, req.user_id)
    if req.status != PAY_PENDING:
        await cb.answer(f"Already {req.status.replace('_', ' ')}.", show_alert=True)
        await refresh_admin_payment_cards(bot, req, user); return
    if user.telegram_id == cb.from_user.id:
        await cb.answer("You cannot approve your own payment.", show_alert=True); return
    if action == "approve":
        if req.validity_days < 0:
            await cb.answer("Plan validity is not configured — fix Payment Settings first.", show_alert=True); return
        req.status = PAY_APPROVED; req.decided_at = now_utc(); req.decided_by = cb.from_user.id
        await activate_subscription(session, user, req.plan_name, req.validity_days, cb.from_user.id, f"payment #{req.id}")
        await audit(session, cb.from_user.id, "payment.approve", str(req.id), f"user {user.telegram_id}")
        await session.commit()        # entitlement + payment status land together or not at all
        await cb.answer("Approved ✅")
        await refresh_admin_payment_cards(bot, req, user)
        until = fmt_dt(user.subscription_expiry) if user.subscription_expiry else "Lifetime access"
        try:
            await bot.send_message(user.telegram_id, "🎉 <b>SUBSCRIPTION ACTIVATED!</b>\n\nYour Exam Yatra Premium access is now active.\n\n"
                                   f"Plan: {esc(req.plan_name)}\nPrice: ₹{req.amount:.0f}\nValid until: <b>{until}</b>\n"
                                   "Usage: Unlimited within your plan's validity.", reply_markup=main_keyboard(user.is_admin))
        except TelegramAPIError:
            pass
        return
    if action == "reject":
        await state.set_state(AdminFlow.reject_reason); await state.update_data(reject_pid=req.id)
        await cb.answer()
        await cb.message.answer(f"✍️ Send a short rejection reason for payment #{req.id} (or send <code>-</code> for none). /cancel to abort.")
        return
    await cb.answer("Unknown action.", show_alert=True)


@router.message(AdminFlow.reject_reason, F.text)
async def admin_reject_reason(message: Message, session: AsyncSession, db_user: User, state: FSMContext, bot: Bot):
    if not db_user.is_admin: await state.clear(); return
    if _is_cmd(message): raise SkipHandler
    pid = (await state.get_data()).get("reject_pid"); await state.clear()
    req = await session.get(PaymentRequest, pid) if pid else None
    if not req or req.status != PAY_PENDING:
        await message.answer("This payment is no longer pending."); return
    reason = (message.text or "").strip()
    req.status = PAY_REJECTED; req.decided_at = now_utc(); req.decided_by = message.from_user.id
    req.reject_reason = None if reason == "-" else reason[:300]
    user = await session.get(User, req.user_id)
    await audit(session, message.from_user.id, "payment.reject", str(req.id), req.reject_reason)
    await session.flush()
    await message.answer(f"❌ Payment #{req.id} rejected. The user keeps their previous access state.")
    await refresh_admin_payment_cards(bot, req, user)
    try:
        await bot.send_message(user.telegram_id, f"❌ <b>Payment #{req.id} was not approved.</b>" + (f"\nReason: {esc(req.reject_reason)}" if req.reject_reason else "") +
                               "\n\nIf you believe this is a mistake, contact the admin. You may submit a new payment request from 💳 Subscription.",
                               reply_markup=url_button_rows(support_rows(await support_contact(session))) or None)
    except TelegramAPIError:
        pass



# ============================ Study materials ============================
async def material_exams(session: AsyncSession) -> list[Exam]:
    return list((await session.execute(select(Exam).where(Exam.active.is_(True)).order_by(Exam.name))).scalars())


async def materials_root(message: Message, session: AsyncSession, user: User, *, edit: bool = False) -> None:
    if not await feature_enabled(session, "materials"):
        await message.answer("📚 Study Materials are temporarily disabled by the administrator."); return
    ok, why = await check_quota(session, user, "materials", "materials")
    if not ok:
        await send_html(message, why, url_button_rows([[("💳 Subscription", "sub:open", False)]])); return
    exams = await material_exams(session)
    rows = [[(e.name, f"mat:e:{e.id}")] for e in exams] + [[("🔎 Search", "mat:search")], [("🏠 Home", "menu:home")]]
    text = "📚 <b>Study Materials</b>\n\nChoose an examination:"
    await (safe_edit(message, text, inline(rows)) if edit else message.answer(text, reply_markup=inline(rows)))


async def material_subjects_for(session: AsyncSession, exam_id: int) -> list[str]:
    rows = list((await session.execute(select(Material.subject).where(Material.exam_id == exam_id, Material.published.is_(True),
                                                                      Material.subject.is_not(None)).distinct())).scalars())
    configured = [s.strip() for s in (await get_setting(session, "material_subjects", "")).split("|") if s.strip()] or DEFAULT_MATERIAL_SUBJECTS
    ordered = [s for s in configured if s in rows] + sorted(s for s in rows if s not in configured)
    return ordered


class MaterialSearch(StatesGroup):
    query = State()


@router.callback_query(F.data.startswith("mat:"))
async def material_callbacks(cb: CallbackQuery, session: AsyncSession, db_user: User, state: FSMContext, bot: Bot):
    if not await gate(cb, db_user, session, bot): return
    parts = cb.data.split(":")
    action = parts[1] if len(parts) > 1 else ""
    if action == "root":
        await cb.answer(); await materials_root(cb.message, session, db_user, edit=True); return
    if action == "search":
        await state.set_state(MaterialSearch.query); await cb.answer()
        await safe_edit(cb.message, "🔎 Type a word from the material title (e.g. <i>polity</i>). /cancel to stop.", inline([[("⬅️ Back", "mat:root")]])); return
    if action == "e":
        exam = await session.get(Exam, parse_int(parts[2], 0) or 0)
        if not exam: await cb.answer("Exam not found.", show_alert=True); return
        subjects = await material_subjects_for(session, exam.id)
        await cb.answer()
        if not subjects:
            await safe_edit(cb.message, f"📚 <b>{esc(exam.name)}</b>\n\nNo study materials have been published for this exam yet.", inline([[("⬅️ Back", "mat:root")]])); return
        rows = [[(s, f"mat:s:{exam.id}:{i}")] for i, s in enumerate(subjects)] + [[("⬅️ Back", "mat:root")]]
        await safe_edit(cb.message, f"📚 <b>{esc(exam.name)}</b>\n\nChoose a subject:", inline(rows)); return
    if action == "s":
        exam = await session.get(Exam, parse_int(parts[2], 0) or 0)
        subjects = await material_subjects_for(session, exam.id) if exam else []
        si = parse_int(parts[3], -1)
        if not exam or not (0 <= si < len(subjects)):
            await cb.answer("This list has changed — open Study Materials again.", show_alert=True); return
        subject = subjects[si]
        fmts = list((await session.execute(select(Material.fmt).where(Material.exam_id == exam.id, Material.subject == subject, Material.published.is_(True)).distinct())).scalars())
        rows = [[(MATERIAL_FORMATS.get(f, f), f"mat:l:{exam.id}:{si}:{f}:0")] for f in fmts] + [[("📂 All formats", f"mat:l:{exam.id}:{si}:all:0")], [("⬅️ Back", f"mat:e:{exam.id}")]]
        await cb.answer()
        await safe_edit(cb.message, f"📚 <b>{esc(exam.name)} › {esc(subject)}</b>\n\nChoose a format:", inline(rows)); return
    if action == "l":
        exam = await session.get(Exam, parse_int(parts[2], 0) or 0)
        subjects = await material_subjects_for(session, exam.id) if exam else []
        si, fmt, page = parse_int(parts[3], -1), parts[4], parse_int(parts[5], 0) or 0
        if not exam or not (0 <= si < len(subjects)):
            await cb.answer("This list has changed — open Study Materials again.", show_alert=True); return
        subject = subjects[si]
        stmt = select(Material).where(Material.exam_id == exam.id, Material.subject == subject, Material.published.is_(True))
        if fmt != "all": stmt = stmt.where(Material.fmt == fmt)
        items = list((await session.execute(stmt.order_by(Material.id.desc()))).scalars())
        await cb.answer()
        await render_material_list(cb.message, items, page, f"{exam.name} › {subject}", back=f"mat:s:{exam.id}:{si}", prefix=f"mat:l:{exam.id}:{si}:{fmt}"); return
    if action == "o":
        m = await session.get(Material, parse_int(parts[2], 0) or 0)
        if not m or not m.published:
            await cb.answer("This material is no longer available.", show_alert=True); return
        await cb.answer(); await deliver_material(cb.message, m); return
    await cb.answer("Unknown action.", show_alert=True)


async def render_material_list(message: Message, items: list[Material], page: int, title: str, *, back: str, prefix: str) -> None:
    per = 8
    pages = max(1, (len(items) + per - 1) // per); page = max(0, min(page, pages - 1))
    chunk = items[page * per:(page + 1) * per]
    if not items:
        await safe_edit(message, f"📚 <b>{esc(title)}</b>\n\nNo resources exist in this category yet.", inline([[("⬅️ Back", back)]])); return
    rows = [[(f"{MATERIAL_FORMATS.get(m.fmt, '📄').split(' ')[0]} {m.title[:50]}", f"mat:o:{m.id}")] for m in chunk]
    nav: list[tuple[str, str]] = []
    if page > 0: nav.append(("⬅️", f"{prefix}:{page - 1}"))
    if page < pages - 1: nav.append(("➡️", f"{prefix}:{page + 1}"))
    if nav: rows.append(nav)
    rows.append([("⬅️ Back", back), ("🏠 Home", "menu:home")])
    await safe_edit(message, f"📚 <b>{esc(title)}</b> (page {page + 1}/{pages})\nTap a resource to open it:", inline(rows))


async def deliver_material(message: Message, m: Material) -> None:
    origin = "🤖 AI-generated notes (not an official document)" if m.origin == "ai" else "✅ Added by administrator"
    caption = (f"📚 <b>{esc(m.title)}</b>\n{MATERIAL_FORMATS.get(m.fmt, m.fmt)} · {'हिन्दी' if m.language == 'hi' else 'English'}\n" +
               (f"\n{esc(m.description)}\n" if m.description else "") + (f"\n📎 Source: {esc(m.source)}" if m.source else "") + f"\n<i>{origin}</i>")
    try:
        if m.file_id and m.fmt == "image":
            await message.answer_photo(m.file_id, caption=caption[:1000], protect_content=True)
        elif m.file_id:
            await message.answer_document(m.file_id, caption=caption[:1000], protect_content=True)
        elif m.url:
            await message.answer(caption, reply_markup=url_button_rows([[("🔗 Open resource", m.url, True)]]))
        else:
            await message.answer(caption, protect_content=True)
    except TelegramBadRequest as e:
        log.warning("Material %s delivery failed: %s", m.id, e)
        await message.answer("⚠️ This file could not be delivered (it may have been removed). Please inform the admin.")


@router.message(MaterialSearch.query, F.text)
async def material_search_input(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    q = (message.text or "").strip()
    if _is_cmd(message): raise SkipHandler
    await state.clear()
    if len(q) < 2:
        await message.answer("Please type at least 2 characters."); return
    stmt = select(Material).where(Material.published.is_(True), func.lower(Material.title).like(f"%{q.lower()}%"))
    if db_user.selected_exam_id:
        stmt = stmt.where(or_(Material.exam_id == db_user.selected_exam_id, Material.exam_id.is_(None)))
    items = list((await session.execute(stmt.order_by(Material.id.desc()).limit(40))).scalars())
    if not items:
        await message.answer(f"No materials match “{esc(q)}”.", reply_markup=inline([[("⬅️ Study Materials", "mat:root")]])); return
    rows = [[(f"{MATERIAL_FORMATS.get(m.fmt, '📄').split(' ')[0]} {m.title[:50]}", f"mat:o:{m.id}")] for m in items[:20]] + [[("⬅️ Study Materials", "mat:root")]]
    await message.answer(f"🔎 Results for “{esc(q)}”:", reply_markup=inline(rows))


# ============================ Performance, leaderboard, profile, help ============================
async def performance(message: Message, session: AsyncSession, user: User):
    total = int((await session.execute(select(func.count()).select_from(Practice).where(Practice.user_id == user.id, Practice.answered_at.is_not(None)))).scalar_one())
    correct = int((await session.execute(select(func.count()).select_from(Practice).where(Practice.user_id == user.id, Practice.answered_at.is_not(None), Practice.is_correct.is_(True)))).scalar_one())
    accuracy = f"{correct / total * 100:.1f}%" if total else "—"
    legacy_mocks = int((await session.execute(select(func.count()).select_from(MockAttempt).where(MockAttempt.user_id == user.id, MockAttempt.status == "completed"))).scalar_one())
    mocks = int((await session.execute(select(func.count()).select_from(AiTest).where(AiTest.user_id == user.id, AiTest.kind == "mock", AiTest.status != "in_progress"))).scalar_one())
    ai_tests = int((await session.execute(select(func.count()).select_from(AiTest).where(AiTest.user_id == user.id, AiTest.kind == "ai", AiTest.status == "completed"))).scalar_one())
    ai_avg = (await session.execute(select(func.avg(AiTest.accuracy)).where(AiTest.user_id == user.id, AiTest.kind == "ai", AiTest.status == "completed"))).scalar_one()
    mock_avg = (await session.execute(select(func.avg(AiTest.accuracy)).where(AiTest.user_id == user.id, AiTest.kind == "mock", AiTest.status != "in_progress"))).scalar_one()
    if not total and not mocks and not ai_tests and not legacy_mocks:
        await message.answer("📊 <b>My Performance</b>\n\nNo activity yet. Try ❓ Daily Quiz or 🧪 Generate AI Test to get started."); return
    await message.answer("📊 <b>My Performance</b>\n\n"
                         f"❓ Quiz questions answered: {total}\n✅ Correct: {correct} · Accuracy: {accuracy}\n\n"
                         f"📝 Mock tests: {mocks + legacy_mocks}" + (f" (avg {float(mock_avg):.0f}%)" if mocks and mock_avg is not None else "") +
                         f"\n🧪 AI tests: {ai_tests}" + (f" (avg {float(ai_avg):.0f}%)" if ai_tests and ai_avg is not None else ""),
                         reply_markup=inline([[("📜 Test History", "th:0")]]))


async def leaderboard(message: Message, session: AsyncSession):
    if not await feature_enabled(session, "leaderboard"):
        await message.answer("🏆 Leaderboard is temporarily disabled."); return
    rows = (await session.execute(
        select(User.full_name, func.count(Practice.id).label("c")).join(Practice, Practice.user_id == User.id)
        .where(Practice.answered_at.is_not(None), Practice.is_correct.is_(True), User.status == "active")
        .group_by(User.id).order_by(func.count(Practice.id).desc()).limit(10))).all()
    if not rows:
        await message.answer("🏆 The leaderboard is empty. Answer quiz questions to appear here."); return
    medals = ["🥇", "🥈", "🥉"]
    await message.answer("🏆 <b>Leaderboard — correct quiz answers</b>\n\n" +
                         "\n".join(f"{medals[i] if i < 3 else str(i + 1) + '.'} {esc(name)} — {score}" for i, (name, score) in enumerate(rows)))


async def profile(message: Message, session: AsyncSession, user: User):
    exam = await session.get(Exam, user.selected_exam_id) if user.selected_exam_id else None
    limits = await effective_limits(session, user)
    used_ai = await usage_today(session, user, "ai"); used_img = await usage_today(session, user, "image"); used_t = await usage_today(session, user, "aitest")
    await message.answer(
        f"👤 <b>My Profile</b>\nName: {esc(user.full_name)}\nTelegram ID: <code>{user.telegram_id}</code>\n"
        f"Exam: {esc(exam.name if exam else 'Not selected')}\nJoined: {fmt_date(user.joined_at)}\n"
        f"Answer style: {'Short' if user.answer_style == STYLE_SHORT else 'Detailed'} · Language: {'हिन्दी' if user.language == 'hi' else 'English'}\n\n"
        + subscription_status_text(user) +
        f"\n\n<b>Today's usage</b>\n🧠 AI Tutor: {used_ai}/{limit_text(limits['ai_daily'])}\n📷 Image solves: {used_img}/{limit_text(limits['image_daily'])}\n"
        f"🧪 AI tests: {used_t}/{limit_text(limits['aitest_daily'])}\n<i>Counters reset at midnight IST.</i>",
        reply_markup=inline([[("💳 Subscription", "sub:open"), ("⚙️ Settings", "set:open")]]))


async def help_text(session: AsyncSession) -> tuple[str, InlineKeyboardMarkup | None]:
    contact = await support_contact(session)
    text = ("❔ <b>Help</b>\n\n"
            "🎯 Select Exam — choose your target exam.\n❓ Daily Quiz — admin-verified MCQs with instant feedback.\n"
            "🧪 Generate AI Test — AI practice tests (clearly labelled as AI-generated).\n📝 Mock Tests — timed tests from verified questions.\n"
            "🧠 Ask AI Tutor — type any doubt (Hindi/English).\n📷 Solve Image — send a photo of a question.\n"
            "📚 Study Materials — PDFs, notes and links by exam and subject.\n💳 Subscription — Premium with unlimited usage.\n\n"
            "Commands: /home · /help · /stop (leave a test) · /cancel (abort an input)\n\n"
            "🔒 Test content is sent with Telegram's forward/save protection. Note: Telegram does not offer screenshot blocking for bot chats, "
            "so please respect the content rules.")
    if contact:
        text += f"\n\n📨 Support: {esc(contact)}"
    rows = support_rows(contact)
    return text, (url_button_rows(rows) if rows else None)


# ============================ Commands & menu buttons ============================
@router.message(CommandStart())
async def start(message: Message, session: AsyncSession, db_user: User, state: FSMContext, bot: Bot):
    if not await gate(message, db_user, session, bot): return
    cur = await state.get_state()
    if cur and not cur.startswith("PaymentFlow"): await state.clear()
    trial = ""
    if db_user.trial_status == "active":
        trial = f"\n\n🎁 Your free trial is active — {trial_days_left(db_user)} day(s) left."
    elif db_user.trial_status == "expired" and db_user.subscription_status != "active":
        trial = "\n\n⌛ Your free trial has ended. Open 💳 Subscription to continue with Premium."
    await message.answer(f"👋 Welcome to <b>Exam Yatra</b>, {esc(db_user.full_name)}!\nPrepare • Practice • Progress{trial}\n\n"
                         "Choose a tool below, or type a doubt / send a question photo.", reply_markup=main_keyboard(db_user.is_admin))
    if await active_test_for(session, db_user):
        await resume_prompt(message, session, await active_test_for(session, db_user))
    elif not db_user.selected_exam_id:
        await show_exams(message, session)


@router.message(Command("home", "menu"))
@router.message(F.text == "🏠 Home")
async def home_cmd(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    cur = await state.get_state()
    if cur and not cur.startswith("PaymentFlow"): await state.clear()
    active = await active_test_for(session, db_user)
    if active:
        await message.answer("You have a test in progress. Resume it, or use /stop to submit it.",
                             reply_markup=inline([[("▶️ Resume", f"tn:{active.id}:{active.current_index}")], [("🏁 Submit", f"tf:{active.id}")]]))
        return
    await show_home(message, db_user)


@router.message(F.text == "📂 More Features")
async def more_features(message: Message, db_user: User):
    await message.answer("📂 <b>More Features</b>", reply_markup=more_keyboard(db_user.is_admin))


@router.message(Command("stop"))
async def stop_cmd(message: Message, session: AsyncSession, db_user: User, state: FSMContext, bot: Bot):
    cur = await state.get_state()
    if cur and not cur.startswith("PaymentFlow"): await state.clear()
    GENERATING_USERS.discard(db_user.id)
    if await stop_active_test(bot, session, db_user, message.chat.id, abandon=False):
        return
    await show_home(message, db_user, "🛑 Nothing was running. Main menu:")


@router.message(Command("cancel"))
async def cancel_cmd(message: Message, db_user: User, state: FSMContext):
    cur = await state.get_state()
    if cur and cur.startswith("PaymentFlow"):
        await message.answer("A payment is in progress. Use /cancel_payment to abort it, or continue sending the requested details."); return
    data = await state.get_data()
    restore_path = data.get("db_restore_path")
    if restore_path:
        try: os.remove(restore_path)
        except OSError: pass
    await state.clear()
    await show_home(message, db_user, "✅ Cancelled.")


@router.message(Command("help"))
@router.message(F.text == "❔ Help")
async def help_cmd(message: Message, session: AsyncSession):
    text, kb = await help_text(session)
    await message.answer(text, reply_markup=kb)


@router.message(Command("myid"))
async def myid(message: Message):
    await message.answer(f"Your Telegram ID: <code>{message.from_user.id}</code>")


@router.message(F.text == "🎯 Select Exam")
async def select_exam_btn(message: Message, session: AsyncSession, db_user: User, bot: Bot):
    if not await gate(message, db_user, session, bot): return
    await show_exams(message, session)


@router.message(F.text == "❓ Daily Quiz")
async def quiz_btn(message: Message, session: AsyncSession, db_user: User, bot: Bot):
    if not await gate(message, db_user, session, bot): return
    await send_quiz(message, session, db_user)


@router.message(F.text == "🧪 Generate AI Test")
async def generate_test_button(message: Message, session: AsyncSession, db_user: User, state: FSMContext, bot: Bot):
    if not await gate(message, db_user, session, bot): return
    await start_test_setup(message, session, db_user, state)


@router.message(F.text == "📝 Mock Tests")
async def mock_btn(message: Message, session: AsyncSession, db_user: User, bot: Bot):
    if not await gate(message, db_user, session, bot): return
    active = await active_test_for(session, db_user)
    if active: await resume_prompt(message, session, active); return
    await list_mock_tests(message, session, db_user)


@router.message(F.text == "🧠 Ask AI Tutor")
async def ai_tutor_btn(message: Message, session: AsyncSession, db_user: User, bot: Bot):
    if not await gate(message, db_user, session, bot): return
    await message.answer("🧠 Type your question (Hindi or English). I answer in your chosen style — change it in ⚙️ Settings.")


@router.message(F.text == "📷 Solve Image")
async def solve_image_btn(message: Message, session: AsyncSession, db_user: User, bot: Bot):
    if not await gate(message, db_user, session, bot): return
    await message.answer("📷 Send a clear photo of the question (max 8 MB). Add a caption if you want a specific part solved.")


@router.message(F.text == "📜 Test History")
async def test_history_button(message: Message, session: AsyncSession, db_user: User, bot: Bot):
    if not await gate(message, db_user, session, bot): return
    await show_test_history(message, session, db_user)


@router.message(F.text == "📚 Study Materials")
async def materials_btn(message: Message, session: AsyncSession, db_user: User, bot: Bot):
    if not await gate(message, db_user, session, bot): return
    await materials_root(message, session, db_user)


@router.message(F.text == "📊 My Performance")
async def perf_btn(message: Message, session: AsyncSession, db_user: User, bot: Bot):
    if not await gate(message, db_user, session, bot): return
    await performance(message, session, db_user)


@router.message(F.text == "🏆 Leaderboard")
async def lb_btn(message: Message, session: AsyncSession, db_user: User, bot: Bot):
    if not await gate(message, db_user, session, bot): return
    await leaderboard(message, session)


@router.message(F.text == "👤 My Profile")
@router.message(Command("profile"))
async def profile_btn(message: Message, session: AsyncSession, db_user: User, bot: Bot):
    if not await gate(message, db_user, session, bot, require_channel=False): return
    await profile(message, session, db_user)


@router.message(F.text == "⚙️ Settings")
@router.message(Command("settings"))
async def settings_btn(message: Message, db_user: User):
    await message.answer(settings_text(db_user), reply_markup=settings_keyboard(db_user))


@router.message(F.text == "💳 Subscription")
@router.message(Command("subscribe"))
async def subscription_btn(message: Message, session: AsyncSession, db_user: User, bot: Bot):
    if not await gate(message, db_user, session, bot, require_channel=False): return
    await show_subscription(message, session, db_user)


@router.message(Command("language"))
async def language_command(message: Message, db_user: User):
    parts = (message.text or "").split(maxsplit=1)
    if len(parts) != 2 or parts[1].lower() not in ("en", "hi"):
        await message.answer("Usage: /language en or /language hi"); return
    db_user.language = parts[1].lower()
    await message.answer(f"Language preference saved: {db_user.language}")


# ---- Photo / document / free text (lowest priority; registered after all FSM handlers) ----
async def download_image(bot: Bot, file_id: str, size: int | None) -> bytes | None:
    if size and size > MAX_IMAGE_BYTES:
        return None
    f = await bot.get_file(file_id)
    buf = io.BytesIO()
    await bot.download_file(f.file_path, buf)
    data = buf.getvalue()
    return data if len(data) <= MAX_IMAGE_BYTES else None


@router.message(AdminFlow.db_restore_upload, F.document)
@admin_only
async def admin_db_restore_upload(message: Message, state: FSMContext, bot: Bot, db_user: User, **_):
    doc = message.document
    if not doc or not doc.file_name:
        await message.answer("Please upload the backup as a named document file."); return
    expected_ext = ".sql" if IS_SQLITE else ".json"
    if not doc.file_name.lower().endswith(expected_ext):
        await message.answer(f"This database expects a {expected_ext} backup. No data was changed."); return
    if doc.file_size is None or doc.file_size <= 0 or doc.file_size > MAX_DB_BACKUP_BYTES:
        await message.answer(f"Backup file must be between 1 byte and {MAX_DB_BACKUP_BYTES // (1024*1024)} MB."); return
    try:
        tg_file = await bot.get_file(doc.file_id)
        buf = io.BytesIO()
        await bot.download_file(tg_file.file_path, buf)
        raw = buf.getvalue()
        if not raw or len(raw) > MAX_DB_BACKUP_BYTES:
            await message.answer("Backup size is invalid. No data was changed."); return
        # Quick format-only validation before asking for confirmation; actual restore validates again.
        if IS_SQLITE:
            _sqlite_validate_dump(raw.decode("utf-8-sig"))
        else:
            payload = json.loads(raw.decode("utf-8"))
            if not isinstance(payload, dict) or payload.get("format") != "examyatra-db-backup" or payload.get("version") != 1 or payload.get("dialect") != "postgresql":
                raise ValueError("Unsupported backup format.")
        suffix = ".sql" if IS_SQLITE else ".json"
        fd, path = tempfile.mkstemp(prefix="examyatra_upload_", suffix=suffix)
        with os.fdopen(fd, "wb") as f: f.write(raw)
        await state.update_data(db_restore_path=path, db_restore_name=doc.file_name)
        await state.set_state(AdminFlow.db_restore_upload)
        await message.answer("⚠️ <b>Backup file validated for format.</b>\n\nRestoring will replace database records with the uploaded backup. Current records, subscriptions, question history, and usage records may be replaced by the backup contents. A safety backup will be sent to you first.\n\nConfirm only if you are sure.", reply_markup=inline([[ ("⚠️ Confirm Restore", "adm:dbconfirm") ], [ ("❌ Cancel", "adm:dbcancel") ]]))
    except Exception as e:
        log.warning("Rejected database backup upload from admin %s: %s", message.from_user.id, type(e).__name__)
        await message.answer(f"❌ Backup rejected: {esc(str(e)[:220])}. No database records were changed.")


@router.message(AdminFlow.db_restore_upload)
@admin_only
async def admin_db_restore_wrong_upload(message: Message, state: FSMContext, db_user: User, **_):
    if _is_cmd(message): raise SkipHandler
    await message.answer("Please upload the backup file as a document, or use /cancel to abort.")


@router.message(StateFilter(None), F.photo)
async def photo_question(message: Message, session: AsyncSession, db_user: User, bot: Bot):
    if not await gate(message, db_user, session, bot): return
    if await active_test_for(session, db_user):
        await message.answer("You're in a test — finish or /stop it before sending photos."); return
    data = await download_image(bot, message.photo[-1].file_id, message.photo[-1].file_size)
    if not data:
        await message.answer("❌ Image too large (max 8 MB)."); return
    await answer_student_question(message, session, db_user, image_bytes=data, mime_type="image/jpeg", caption=message.caption or "")


@router.message(StateFilter(None), F.document)
async def document_question(message: Message, session: AsyncSession, db_user: User, bot: Bot):
    if not await gate(message, db_user, session, bot): return
    doc = message.document
    if not (doc.mime_type or "").startswith("image/") or doc.mime_type not in ("image/jpeg", "image/png", "image/webp"):
        await message.answer("I can read question images (JPG/PNG/WEBP). For PDFs, please send a screenshot of the question."); return
    data = await download_image(bot, doc.file_id, doc.file_size)
    if not data:
        await message.answer("❌ Image too large (max 8 MB)."); return
    await answer_student_question(message, session, db_user, image_bytes=data, mime_type=doc.mime_type, caption=message.caption or "")


@router.message(StateFilter(None), F.text & ~F.text.startswith("/"))
async def free_text(message: Message, session: AsyncSession, db_user: User, bot: Bot):
    text = (message.text or "").strip()
    if text in MENU_BUTTONS:
        return
    if not await gate(message, db_user, session, bot): return
    if await active_test_for(session, db_user):
        active = await active_test_for(session, db_user)
        await message.answer("You're in a test. Use the buttons on the question, or /stop to submit.",
                             reply_markup=inline([[("▶️ Back to test", f"tn:{active.id}:{active.current_index}")]])); return
    if len(text) < 3:
        await message.answer("Please type a complete question."); return
    await answer_student_question(message, session, db_user, question_text=text)



# ============================ Admin panel ============================
def admin_only(fn):
    async def wrapper(event, *args, **kwargs):
        db_user: User = kwargs.get("db_user")
        if not db_user or not db_user.is_admin or not is_admin_id(event.from_user.id):
            if isinstance(event, CallbackQuery):
                await event.answer("Admin only.", show_alert=True)
            else:
                await event.answer("Unknown command. Send /help.")
            return
        return await fn(event, *args, **kwargs)
    wrapper.__name__ = fn.__name__
    return wrapper


# ============================ Manual database backup / restore ============================
def _sqlite_db_path() -> str:
    url = make_url(DATABASE_URL)
    if url.database in (None, "", ":memory:"):
        raise RuntimeError("SQLite in-memory databases cannot be safely restored on this deployment.")
    path = Path(url.database)
    if not path.is_absolute():
        path = Path.cwd() / path
    return str(path.resolve())


def _encode_db_value(value: Any) -> Any:
    if isinstance(value, datetime):
        return {"__ey_type__": "datetime", "value": value.isoformat()}
    if isinstance(value, date):
        return {"__ey_type__": "date", "value": value.isoformat()}
    if isinstance(value, Decimal):
        return {"__ey_type__": "decimal", "value": str(value)}
    if isinstance(value, (bytes, bytearray, memoryview)):
        return {"__ey_type__": "bytes", "value": base64.b64encode(bytes(value)).decode("ascii")}
    return value


def _decode_db_value(value: Any) -> Any:
    if not isinstance(value, dict) or "__ey_type__" not in value:
        return value
    typ, raw = value.get("__ey_type__"), value.get("value")
    if typ == "datetime": return datetime.fromisoformat(raw)
    if typ == "date": return date.fromisoformat(raw)
    if typ == "decimal": return Decimal(raw)
    if typ == "bytes": return base64.b64decode(raw, validate=True)
    raise ValueError("Unsupported typed value in backup.")


async def create_database_backup() -> tuple[bytes, str, str]:
    """Create a manual, point-in-time backup. SQLite uses native SQL dump; PostgreSQL uses a typed logical JSON snapshot."""
    stamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S_UTC")
    if IS_SQLITE:
        db_path = _sqlite_db_path()
        if not os.path.isfile(db_path):
            raise RuntimeError("SQLite database file was not found. The database may not have been initialized yet.")
        # SQLite's iterdump runs against one read transaction, giving a consistent SQL dump.
        with sqlite3.connect(f"file:{db_path}?mode=ro", uri=True, timeout=15) as con:
            con.execute("BEGIN")
            sql_text = "\n".join(con.iterdump()) + "\n"
        return sql_text.encode("utf-8"), f"examyatra_backup_{stamp}.sql", "sqlite"

    def dump_sync(sync_conn):
        metadata = sa_inspect(sync_conn).get_table_names()
        md = __import__("sqlalchemy").MetaData()
        md.reflect(bind=sync_conn, only=metadata)
        tables = {}
        for table in md.sorted_tables:
            rows = sync_conn.execute(table.select()).mappings().all()
            tables[table.name] = [{k: _encode_db_value(v) for k, v in row.items()} for row in rows]
        return {"format": "examyatra-db-backup", "version": 1, "created_at": datetime.now(timezone.utc).isoformat(), "dialect": "postgresql", "tables": tables}
    async with engine.connect() as conn:
        payload = await conn.run_sync(dump_sync)
    return json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode("utf-8"), f"examyatra_backup_{stamp}.eydb.json", "postgresql"


def _sqlite_validate_dump(sql_text: str) -> None:
    if not sql_text.strip() or len(sql_text) > MAX_DB_BACKUP_BYTES:
        raise ValueError("Backup is empty or exceeds the configured size limit.")
    statements, pending = [], ""
    for line in sql_text.splitlines():
        pending += line + "\n"
        if sqlite3.complete_statement(pending):
            statement = pending.strip(); pending = ""
            if statement: statements.append(statement)
    if pending.strip():
        raise ValueError("SQL backup appears truncated or has an incomplete statement.")
    if not statements:
        raise ValueError("No SQL statements found.")
    allowed_prefixes = ("CREATE TABLE ", "CREATE INDEX ", "CREATE UNIQUE INDEX ", "INSERT INTO ", "BEGIN TRANSACTION", "COMMIT", "PRAGMA FOREIGN_KEYS=OFF", "PRAGMA FOREIGN_KEYS=ON", 'DELETE FROM "SQLITE_SEQUENCE"')
    for statement in statements:
        upper = statement.upper().lstrip()
        if not upper.startswith(allowed_prefixes):
            raise ValueError("Backup contains an unsupported SQL statement; restore was blocked for safety.")


def _validate_sqlite_db(path: str) -> None:
    with sqlite3.connect(path) as con:
        integrity = con.execute("PRAGMA integrity_check").fetchone()
        if not integrity or integrity[0] != "ok":
            raise ValueError("The uploaded backup failed SQLite integrity validation.")
        names = {r[0] for r in con.execute("SELECT name FROM sqlite_master WHERE type='table'")}
        required = {"users", "questions", "exams", "settings"}
        if not required.issubset(names):
            raise ValueError("Backup is missing required Exam Yatra tables; restore was blocked.")


async def restore_sqlite_backup(sql_bytes: bytes) -> None:
    sql_text = sql_bytes.decode("utf-8-sig")
    _sqlite_validate_dump(sql_text)
    current_path = _sqlite_db_path()
    parent = os.path.dirname(current_path) or "."
    os.makedirs(parent, exist_ok=True)
    fd, temp_path = tempfile.mkstemp(prefix="examyatra_restore_", suffix=".db", dir=parent)
    os.close(fd)
    try:
        with sqlite3.connect(temp_path) as temp_db:
            temp_db.execute("PRAGMA foreign_keys=OFF")
            temp_db.executescript(sql_text)
            temp_db.commit()
        _validate_sqlite_db(temp_path)
        # Safety backup is already delivered to the admin before this function is called.
        await engine.dispose()
        os.replace(temp_path, current_path)
        await engine.dispose()  # fresh connections will open the restored file
        async with engine.begin() as conn:
            await conn.run_sync(Base.metadata.create_all)
    finally:
        if os.path.exists(temp_path):
            os.remove(temp_path)


async def restore_postgres_backup(raw: bytes) -> None:
    payload = json.loads(raw.decode("utf-8"))
    if not isinstance(payload, dict) or payload.get("format") != "examyatra-db-backup" or payload.get("version") != 1 or payload.get("dialect") != "postgresql" or not isinstance(payload.get("tables"), dict):
        raise ValueError("This is not a supported Exam Yatra PostgreSQL backup.")
    tables_data = payload["tables"]
    if not tables_data or len(tables_data) > 100:
        raise ValueError("Backup table list is invalid.")
    def restore_sync(sync_conn):
        md = __import__("sqlalchemy").MetaData()
        md.reflect(bind=sync_conn)
        expected = {t.name for t in md.sorted_tables}
        if set(tables_data) != expected:
            raise ValueError("Backup schema does not match the current database. No records were changed.")
        required = {"users", "questions", "exams", "settings"}
        if not required.issubset(expected):
            raise ValueError("Current database schema is missing required Exam Yatra tables.")
        # Transaction is managed by engine.begin(); any insert/delete failure rolls the full restore back.
        for table in reversed(md.sorted_tables):
            sync_conn.execute(table.delete())
        for table in md.sorted_tables:
            rows = tables_data.get(table.name)
            if not isinstance(rows, list):
                raise ValueError(f"Invalid rows for table {table.name}.")
            allowed_cols = {c.name for c in table.columns}
            prepared = []
            for row in rows:
                if not isinstance(row, dict) or not set(row).issubset(allowed_cols):
                    raise ValueError(f"Invalid columns in table {table.name}.")
                prepared.append({k: _decode_db_value(v) for k, v in row.items()})
            if prepared:
                sync_conn.execute(table.insert(), prepared)
        # Reset PostgreSQL identity/serial sequences so new records do not collide with restored IDs.
        for table in md.sorted_tables:
            for col in table.columns:
                if col.primary_key and getattr(col.type, "python_type", None) is int:
                    sync_conn.execute(sa_text("SELECT setval(pg_get_serial_sequence(:tbl, :col), COALESCE((SELECT MAX(" + '"' + col.name + '"' + ") FROM \"" + table.name + "\"), 1), (SELECT COUNT(*) > 0 FROM \"" + table.name + "\"))"), {"tbl": table.name, "col": col.name})
    async with engine.begin() as conn:
        await conn.run_sync(restore_sync)


def admin_keyboard() -> InlineKeyboardMarkup:
    return inline([
        [("📊 Dashboard", "adm:dash"), ("👥 Users", "adm:users")],
        [("📢 Channels", "adm:ch"), ("🎁 Trials", "adm:trial")],
        [("💳 Payments", "adm:pay"), ("⭐ Plan & UPI", "adm:plan")],
        [("📚 Question Bank", "adm:qb"), ("📂 Materials", "adm:mat")],
        [("📏 Usage Limits", "adm:lim"), ("🔑 API Key", "adm:api")],
        [("⚙️ Features", "adm:feat"), ("📣 Broadcast", "adm:bc")],
        [("🛠 Maintenance", "adm:maint"), ("📨 Support contact", "adm:support")],
        [("➕ Exam", "adm:addexam"), ("📝 Mock tests", "adm:mock")],
        [("🗄️ Database Backup / Restore", "adm:db")],
        [("📜 Audit log", "adm:audit:0")],
    ])


BACK_ADMIN = [("↩️ Admin menu", "adm:back")]


@router.message(F.text == "🛠 Admin Panel")
@router.message(Command("admin"))
@admin_only
async def admin_panel(message: Message, db_user: User, **_):
    await message.answer("🛠 <b>Exam Yatra Admin Panel</b>", reply_markup=admin_keyboard())


async def admin_count(session: AsyncSession, stmt) -> int:
    return int((await session.execute(select(func.count()).select_from(stmt.subquery()))).scalar_one())


async def dashboard_text(session: AsyncSession) -> str:
    now = now_utc(); day = today_ist()
    c = lambda stmt: admin_count(session, stmt)   # noqa: E731
    users = await c(select(User.id)); active = await c(select(User.id).where(User.status == "active"))
    banned = await c(select(User.id).where(User.status == "banned"))
    trial_active = await c(select(User.id).where(User.trial_status == "active", User.trial_ends_at > now))
    trial_expired = await c(select(User.id).where(or_(User.trial_status == "expired", and_(User.trial_status == "active", User.trial_ends_at <= now))))
    prem = await c(select(User.id).where(User.subscription_status == "active", or_(User.subscription_expiry.is_(None), User.subscription_expiry > now)))
    prem_exp = await c(select(User.id).where(or_(User.subscription_status == "expired", and_(User.subscription_status == "active", User.subscription_expiry <= now))))
    pay_p = await c(select(PaymentRequest.id).where(PaymentRequest.status == PAY_PENDING))
    pay_a = await c(select(PaymentRequest.id).where(PaymentRequest.status == PAY_APPROVED))
    pay_r = await c(select(PaymentRequest.id).where(PaymentRequest.status == PAY_REJECTED))
    q_all = await c(select(Question.id)); q_ok = await c(select(Question.id).where(Question.status == Q_APPROVED))
    q_pend = await c(select(Question.id).where(Question.status == Q_PENDING))
    exams = await c(select(Exam.id).where(Exam.active.is_(True)))
    ai_tests = await c(select(AiTest.id).where(AiTest.kind == "ai"))
    usage = (await session.execute(select(UsageCounter.feature, func.sum(UsageCounter.count)).where(UsageCounter.day == day).group_by(UsageCounter.feature))).all()
    usage_txt = ", ".join(f"{f}: {int(n)}" for f, n in usage) or "none yet"
    return ("📊 <b>Dashboard</b>\n\n"
            f"👥 Users: {users} (active {active}, banned {banned})\n🎁 Trials: {trial_active} active · {trial_expired} expired\n"
            f"⭐ Premium: {prem} active · {prem_exp} expired\n💳 Payments: {pay_p} pending · {pay_a} approved · {pay_r} rejected\n"
            f"📚 Questions: {q_all} total · ✅ {q_ok} approved · 🕒 {q_pend} pending review\n🎯 Exams: {exams} · 🧪 AI tests generated: {ai_tests}\n"
            f"📈 Usage today (IST): {esc(usage_txt)}\n🛠 Maintenance: {'ON' if await maintenance_on(session) else 'off'} · "
            f"📢 Channel check: {'ON' if await setting_bool(session, 'channel_verification', False) else 'off'}")


def features_keyboard(status: dict[str, bool]) -> InlineKeyboardMarkup:
    return inline([[(f"{'🟢' if status[k] else '🔴'} {k}", f"adm:feat:{k}")] for k in FEATURE_KEYS] + [BACK_ADMIN])


async def user_card(session: AsyncSession, u: User) -> str:
    refresh_entitlements(u)
    limits = await effective_limits(session, u)
    ov = u.overrides()
    last_tests = list((await session.execute(select(AiTest).where(AiTest.user_id == u.id).order_by(AiTest.id.desc()).limit(3))).scalars())
    tests_txt = "\n".join(f"  • {t.topic[:30]} — {t.correct}/{t.question_count} ({t.status})" for t in last_tests) or "  —"
    return (f"👤 <b>{esc(u.full_name)}</b> (@{esc(u.username) or '—'})\nID: <code>{u.telegram_id}</code> · joined {fmt_date(u.joined_at)} · last active {fmt_dt(u.last_active_at)}\n"
            f"Status: <b>{u.status}</b> · access: {'granted' if u.access_granted else 'REVOKED'} · admin: {'yes' if u.is_admin else 'no'}\n"
            f"Tier: <b>{TIER_LABEL[user_tier(u)]}</b>\n"
            f"Trial: {u.trial_status} ({fmt_date(u.trial_started_at)} → {fmt_date(u.trial_ends_at)}, +{u.trial_extended_by_admin}d by admin)\n"
            f"Subscription: {u.subscription_status} · plan {esc(u.current_plan) or '—'} · until {fmt_dt(u.subscription_expiry) if u.subscription_expiry else ('lifetime' if u.subscription_status == 'active' else '—')}\n"
            f"Limits: " + ", ".join(f"{k}={limit_text(v)}" for k, v in limits.items()) + (f"\nOverrides: {esc(json.dumps(ov))}" if ov else "") +
            f"\nUsage today: ai {await usage_today(session, u, 'ai')} · image {await usage_today(session, u, 'image')} · aitest {await usage_today(session, u, 'aitest')}\n"
            f"Recent tests:\n{tests_txt}" + (f"\nNotes: {esc(u.notes)}" if u.notes else ""))


def user_actions_keyboard(u: User) -> InlineKeyboardMarkup:
    uid = u.telegram_id
    return inline([
        [("🚫 Ban" if u.status != "banned" else "✅ Unban", f"adm:u:{uid}:{'ban' if u.status != 'banned' else 'unban'}"),
         ("🔒 Revoke access" if u.access_granted else "🔓 Restore access", f"adm:u:{uid}:{'revoke' if u.access_granted else 'restore'}")],
        [("⭐ Grant/extend Premium", f"adm:u:{uid}:grant"), ("♾ Lifetime", f"adm:u:{uid}:lifetime:confirm")],
        [("⛔ Revoke Premium", f"adm:u:{uid}:unsub:confirm"), ("🎁 Extend trial", f"adm:u:{uid}:trialext")],
        [("🔁 Reset trial (explicit)", f"adm:u:{uid}:trialreset:confirm"), ("🗑 Revoke trial", f"adm:u:{uid}:trialrevoke:confirm")],
        [("📏 Set limit override", f"adm:u:{uid}:limit"), ("🧹 Clear overrides", f"adm:u:{uid}:limitclear")],
        [("🔄 Reset today's counters", f"adm:u:{uid}:usagereset"), ("🔄 Refresh", f"adm:u:{uid}:view")],
        BACK_ADMIN,
    ])


async def show_user_admin(message: Message, session: AsyncSession, u: User, *, edit: bool = True) -> None:
    text, kb = await user_card(session, u), user_actions_keyboard(u)
    await (safe_edit(message, text, kb) if edit else message.answer(text, reply_markup=kb))


async def paged_users(session: AsyncSession, where, page: int, title: str, prefix: str) -> tuple[str, InlineKeyboardMarkup]:
    total = await admin_count(session, select(User.id).where(where))
    pages = max(1, (total + ADMIN_PAGE - 1) // ADMIN_PAGE); page = max(0, min(page, pages - 1))
    users = list((await session.execute(select(User).where(where).order_by(User.id.desc()).offset(page * ADMIN_PAGE).limit(ADMIN_PAGE))).scalars())
    lines = [f"<b>{title}</b> — {total} users (page {page + 1}/{pages})", ""]
    rows: list[list[tuple[str, str]]] = []
    for u in users:
        refresh_entitlements(u)
        extra = ""
        if u.trial_status == "active": extra = f"trial ends {fmt_date(u.trial_ends_at)} ({trial_days_left(u)}d left)"
        elif u.subscription_status == "active": extra = "premium until " + (fmt_date(u.subscription_expiry) if u.subscription_expiry else "lifetime")
        elif u.trial_status == "expired": extra = f"trial ended {fmt_date(u.trial_ends_at)}"
        lines.append(f"• {esc(u.full_name)} <code>{u.telegram_id}</code> — {extra}")
        rows.append([(f"{u.full_name[:24]} · {u.telegram_id}", f"adm:u:{u.telegram_id}:view")])
    nav: list[tuple[str, str]] = []
    if page > 0: nav.append(("⬅️", f"{prefix}:{page - 1}"))
    if page < pages - 1: nav.append(("➡️", f"{prefix}:{page + 1}"))
    if nav: rows.append(nav)
    rows.append(BACK_ADMIN)
    return "\n".join(lines), inline(rows)


async def channels_screen(session: AsyncSession) -> tuple[str, InlineKeyboardMarkup]:
    on = await setting_bool(session, "channel_verification", False)
    chans = list((await session.execute(select(RequiredChannel).order_by(RequiredChannel.id))).scalars())
    lines = [f"📢 <b>Required Channels</b> — verification is <b>{'ON' if on else 'OFF'}</b>", "",
             "The bot must be an <b>administrator</b> in each channel to check membership.", ""]
    rows: list[list[tuple[str, str]]] = [[("🔴 Disable verification" if on else "🟢 Enable verification", "adm:ch:toggle"), ("➕ Add channel", "adm:ch:add")]]
    for ch in chans:
        lines.append(f"{'🟢' if ch.enabled else '⚪️'} #{ch.id} {esc(ch.chat_ref)} — {esc(ch.title) or '—'}" + (f"\n   🔗 {esc(ch.invite_url)}" if ch.invite_url else ""))
        rows.append([(f"{'Disable' if ch.enabled else 'Enable'} #{ch.id}", f"adm:ch:en:{ch.id}"), (f"🔗 Invite URL #{ch.id}", f"adm:ch:url:{ch.id}"),
                     (f"🗑 Remove #{ch.id}", f"adm:ch:del:{ch.id}:confirm")])
    rows.append([("🔎 Check bot rights", "adm:ch:check")]); rows.append(BACK_ADMIN)
    if not chans: lines.append("No channels configured.")
    return "\n".join(lines), inline(rows)


async def plan_screen(session: AsyncSession) -> tuple[str, InlineKeyboardMarkup]:
    p = await plan_config(session)
    warn = []
    if p["validity_days"] < 0: warn.append("⚠️ Validity not configured — purchases are blocked until you set it.")
    if not upi_id_valid(p["upi_id"]): warn.append("⚠️ UPI ID missing/invalid — purchases are blocked.")
    text = ("⭐ <b>Plan & Payment Settings</b>\n\n"
            f"Plan name: <b>{esc(p['name'])}</b>\nPrice: <b>₹{p['price']:.2f}</b>\nValidity: <b>{validity_label(p['validity_days'])}</b>\n"
            f"UPI ID: <code>{esc(p['upi_id']) or '—'}</code>\nPayee name: {esc(p['payee']) or '—'}\nPurchases: {'enabled' if p['purchases_enabled'] else 'DISABLED'}\n"
            f"Trial: {'enabled' if await setting_bool(session, 'trial_enabled', True) else 'disabled'} · {await setting_int(session, 'trial_days', 7)} days\n\n" + "\n".join(warn))
    kb = inline([
        [("✏️ Plan name", "adm:set:plan_name"), ("💰 Price", "adm:set:plan_price")],
        [("📆 Validity (days, 0=lifetime)", "adm:set:plan_validity_days")],
        [("🏦 UPI ID", "adm:set:upi_id"), ("👤 Payee name", "adm:set:upi_payee")],
        [("🛒 Toggle purchases", "adm:toggle:purchases_enabled"), ("🎁 Toggle trial", "adm:toggle:trial_enabled")],
        [("🎁 Trial days", "adm:set:trial_days"), ("👁 Preview payment screen", "adm:plan:preview")],
        BACK_ADMIN])
    return text, kb


async def payments_list(session: AsyncSession, status: str, page: int) -> tuple[str, InlineKeyboardMarkup]:
    total = await admin_count(session, select(PaymentRequest.id).where(PaymentRequest.status == status))
    pages = max(1, (total + ADMIN_PAGE - 1) // ADMIN_PAGE); page = max(0, min(page, pages - 1))
    reqs = list((await session.execute(select(PaymentRequest).where(PaymentRequest.status == status).order_by(PaymentRequest.id.desc()).offset(page * ADMIN_PAGE).limit(ADMIN_PAGE))).scalars())
    lines = [f"💳 <b>Payments — {status.replace('_', ' ')}</b> ({total})", ""]
    rows: list[list[tuple[str, str]]] = [[("🕒 Pending", "adm:pay:pending_review:0"), ("✅ Approved", "adm:pay:approved:0"), ("❌ Rejected", "adm:pay:rejected:0")]]
    for r in reqs:
        u = await session.get(User, r.user_id)
        lines.append(f"#{r.id} · {esc(u.full_name if u else '?')} <code>{u.telegram_id if u else '?'}</code> · ₹{r.amount:.0f} · UTR {esc(r.utr) or '—'} · {fmt_dt(r.submitted_at or r.created_at)}")
        rows.append([(f"#{r.id} · {u.full_name[:20] if u else '?'} · ₹{r.amount:.0f}", f"adm:payv:{r.id}")])
    nav: list[tuple[str, str]] = []
    if page > 0: nav.append(("⬅️", f"adm:pay:{status}:{page - 1}"))
    if page < pages - 1: nav.append(("➡️", f"adm:pay:{status}:{page + 1}"))
    if nav: rows.append(nav)
    rows.append(BACK_ADMIN)
    return "\n".join(lines), inline(rows)


async def limits_screen(session: AsyncSession) -> tuple[str, InlineKeyboardMarkup]:
    pol = await load_policies(session)
    lines = ["📏 <b>Usage Limits</b> (-1 = unlimited, 0 = not included; daily counters reset at midnight IST)", ""]
    for tier in TIERS:
        lines.append(f"<b>{TIER_LABEL[tier]}</b>: " + ", ".join(f"{k}={pol[tier][k]}" for k in LIMIT_KEYS))
    rows = [[(f"✏️ {tier}", f"adm:limset:{tier}")] for tier in TIERS]
    rows.append([("📈 Users at limit today", "adm:limhit"), ("📊 Usage (7 days)", "adm:limhist")])
    rows.append(BACK_ADMIN)
    return "\n".join(lines), inline(rows)


async def qb_screen(session: AsyncSession) -> tuple[str, InlineKeyboardMarkup]:
    counts = {s: await admin_count(session, select(Question.id).where(Question.status == s)) for s in Q_STATUSES}
    exams = list((await session.execute(select(Exam).order_by(Exam.name))).scalars())
    text = ("📚 <b>Question Bank</b>\n\n" + " · ".join(f"{s}: {n}" for s, n in counts.items()) +
            "\n\nOnly <b>approved</b> questions are served in Daily Quiz and Mock Tests. Legacy questions were imported as <i>pending</i> and need review.")
    rows = [[("🕒 Review pending", "adm:qr:pending:0"), ("✅ Approved", "adm:qr:approved:0"), ("❌ Rejected", "adm:qr:rejected:0")],
            [("➕ Add question", "adm:addq"), ("🔎 Search / open by ID", "adm:qsearch")],
            [("👯 Find duplicates", "adm:qdups")]]
    rows += [[(f"📂 {e.name}", f"adm:qexam:{e.id}:0")] for e in exams[:12]]
    rows.append(BACK_ADMIN)
    return text, inline(rows)


def question_admin_keyboard(q: Question, back: str = "adm:qb") -> InlineKeyboardMarkup:
    rows = []
    if q.status != Q_APPROVED: rows.append([("✅ Approve", f"adm:q:{q.id}:approve")])
    if q.status != Q_REJECTED: rows.append([("❌ Reject", f"adm:q:{q.id}:reject")])
    rows.append([("✏️ Edit (resend block)", f"adm:q:{q.id}:edit"), ("👁 Preview as student", f"adm:q:{q.id}:preview")])
    rows.append([("📴 Unpublish" if q.published else "📶 Publish", f"adm:q:{q.id}:pub"), ("🗑 Delete", f"adm:q:{q.id}:del:confirm")])
    rows.append([("⬅️ Back", back)] + BACK_ADMIN)
    return inline(rows)


async def question_list(session: AsyncSession, where, page: int, title: str, prefix: str) -> tuple[str, InlineKeyboardMarkup]:
    total = await admin_count(session, select(Question.id).where(where))
    pages = max(1, (total + ADMIN_PAGE - 1) // ADMIN_PAGE); page = max(0, min(page, pages - 1))
    qs = list((await session.execute(select(Question).where(where).order_by(Question.id.desc()).offset(page * ADMIN_PAGE).limit(ADMIN_PAGE))).scalars())
    lines = [f"<b>{title}</b> — {total} (page {page + 1}/{pages})", ""]
    rows: list[list[tuple[str, str]]] = []
    for q in qs:
        icon = {Q_APPROVED: "✅", Q_PENDING: "🕒", Q_REJECTED: "❌"}.get(q.status, "📝")
        lines.append(f"{icon} #{q.id} {esc(q.text[:70])}")
        rows.append([(f"{icon} #{q.id} {q.text[:40]}", f"adm:q:{q.id}:view")])
    nav: list[tuple[str, str]] = []
    if page > 0: nav.append(("⬅️", f"{prefix}:{page - 1}"))
    if page < pages - 1: nav.append(("➡️", f"{prefix}:{page + 1}"))
    if nav: rows.append(nav)
    rows.append([("⬅️ Question Bank", "adm:qb")])
    return "\n".join(lines), inline(rows)


async def materials_admin_screen(session: AsyncSession, page: int = 0) -> tuple[str, InlineKeyboardMarkup]:
    total = await admin_count(session, select(Material.id))
    pages = max(1, (total + ADMIN_PAGE - 1) // ADMIN_PAGE); page = max(0, min(page, pages - 1))
    items = list((await session.execute(select(Material).order_by(Material.id.desc()).offset(page * ADMIN_PAGE).limit(ADMIN_PAGE))).scalars())
    lines = [f"📂 <b>Study Materials</b> — {total} items (page {page + 1}/{pages})", ""]
    rows: list[list[tuple[str, str]]] = [[("➕ Add material", "adm:mat:add"), ("🗂 Subject list", "adm:set:material_subjects")]]
    for m in items:
        ex = await session.get(Exam, m.exam_id) if m.exam_id else None
        lines.append(f"{'🟢' if m.published else '⚪️'} #{m.id} [{m.fmt}] {esc(m.title[:40])} — {esc(ex.name if ex else 'all')} / {esc(m.subject) or '—'}")
        rows.append([(f"{'🟢' if m.published else '⚪️'} #{m.id} {m.title[:30]}", f"adm:matv:{m.id}")])
    nav: list[tuple[str, str]] = []
    if page > 0: nav.append(("⬅️", f"adm:mat:p:{page - 1}"))
    if page < pages - 1: nav.append(("➡️", f"adm:mat:p:{page + 1}"))
    if nav: rows.append(nav)
    rows.append(BACK_ADMIN)
    return "\n".join(lines), inline(rows)


MATERIAL_FORMAT_HELP = ("Send material details, one per line:\n<code>TITLE: Indian Polity Notes\nEXAM: Bihar Police\nSUB: Indian Constitution\n"
                        "TOPIC: Fundamental Rights (optional)\nLANG: hi|en (optional)\nFMT: pdf|doc|image|link|notes\nURL: https://... (only for link)\n"
                        "DESC: short description (optional)\nSRC: source/credit (optional)</code>\n\nFor pdf/doc/image you will be asked to upload the file next.")


SETTING_PROMPTS = {
    "plan_name": "Send the plan name (max 64 chars).", "plan_price": "Send the price in rupees, e.g. 99.",
    "plan_validity_days": "Send validity in days (e.g. 30). Send 0 for lifetime access.", "upi_id": "Send the UPI ID, e.g. name@bank.",
    "upi_payee": "Send the payee name shown in UPI apps.", "trial_days": "Send trial length in days (0 disables trials for new users).",
    "material_subjects": "Send the subject list separated by | (used as the preferred order), e.g. General Knowledge|Indian History|Science.",
    "maintenance_message": "Send the maintenance message users will see.", "support_contact": "Send the support contact: @username or https://t.me/... link.",
}


async def apply_setting(session: AsyncSession, key: str, raw: str) -> str | None:
    raw = raw.strip()
    if key == "plan_price":
        try: v = float(raw)
        except ValueError: return "Price must be a number."
        if v <= 0 or v > 100000: return "Price out of range."
        await set_setting(session, key, f"{v:.2f}"); return None
    if key in ("plan_validity_days", "trial_days"):
        v = parse_int(raw, None)
        if v is None or v < 0 or v > 3650: return "Send a whole number of days (0–3650)."
        await set_setting(session, key, str(v)); return None
    if key == "upi_id":
        if not upi_id_valid(raw): return "That is not a valid UPI ID (expected name@bank)."
        await set_setting(session, key, raw); return None
    if key == "support_contact":
        if not (re.fullmatch(r"@[A-Za-z0-9_]{5,32}", raw) or raw.startswith("https://t.me/")): return "Send @username or a https://t.me/ link."
        await set_setting(session, key, raw); return None
    if not raw: return "Value cannot be empty."
    await set_setting(session, key, raw[:500]); return None



@router.callback_query(F.data.startswith("adm:"))
@admin_only
async def admin_callbacks(cb: CallbackQuery, session: AsyncSession, db_user: User, state: FSMContext, bot: Bot, **_):
    parts = cb.data.split(":")
    action = parts[1] if len(parts) > 1 else ""
    a2 = parts[2] if len(parts) > 2 else ""
    a3 = parts[3] if len(parts) > 3 else ""
    a4 = parts[4] if len(parts) > 4 else ""
    actor = cb.from_user.id
    msg = cb.message

    async def edit(text: str, kb: InlineKeyboardMarkup | None = None) -> None:
        await safe_edit(msg, text, kb)

    # ----- navigation -----
    if action == "back":
        await cb.answer(); await state.clear(); await edit("🛠 <b>Exam Yatra Admin Panel</b>", admin_keyboard()); return
    if action == "dash":
        await cb.answer(); await edit(await dashboard_text(session), inline([[("🔄 Refresh", "adm:dash")], BACK_ADMIN])); return
    if action == "db":
        await cb.answer()
        await edit("🗄️ <b>Database Backup / Restore</b>\n\n• No scheduled or background backups are created.\n• Manual backup sends a file to this admin chat.\n• Restore requires a compatible backup upload and confirmation.\n• A one-time safety backup is sent to you immediately before a confirmed restore.", inline([
            [("🗄️ Backup Database", "adm:dbbackup")],
            [("♻️ Restore Database", "adm:dbrestore")], BACK_ADMIN]))
        return
    if action == "dbbackup":
        await cb.answer("Creating backup…")
        if DB_BACKUP_LOCK.locked():
            await msg.answer("⏳ A database backup/restore operation is already running. Try again shortly."); return
        async with DB_BACKUP_LOCK:
            try:
                content, filename, dialect = await create_database_backup()
                if len(content) > MAX_DB_BACKUP_BYTES:
                    raise ValueError(f"Backup exceeds the configured {MAX_DB_BACKUP_BYTES // (1024*1024)} MB limit.")
                await bot.send_document(actor, BufferedInputFile(content, filename=filename), caption=f"🗄️ Manual database backup\nDatabase: {dialect}\nCreated: {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S UTC')}\nNo scheduled backups are enabled.")
                await audit(session, actor, "db.backup.success", filename, f"dialect={dialect}; bytes={len(content)}")
                await session.commit()
                await msg.answer(f"✅ Backup created and sent to your private admin chat.\nFile: <code>{esc(filename)}</code>")
            except Exception as e:
                log.exception("Manual database backup failed")
                await audit(session, actor, "db.backup.failed", details=type(e).__name__)
                await session.commit()
                await msg.answer(f"❌ Backup failed: {esc(type(e).__name__)}. Check server logs; database credentials are not shown.")
        return
    if action == "dbrestore":
        await state.set_state(AdminFlow.db_restore_upload)
        await cb.answer()
        ext = ".sql" if IS_SQLITE else ".eydb.json"
        await msg.answer(f"♻️ <b>Restore database</b>\nUpload a compatible Exam Yatra backup file ({ext}).\n\nThe current database will not be changed yet. After validation, you must confirm. A safety backup will be sent to you immediately before restore.\n\n/cancel to abort.")
        return
    if action == "dbconfirm":
        data = await state.get_data()
        path = data.get("db_restore_path")
        if not path or not os.path.isfile(path):
            await state.clear(); await cb.answer("Backup upload expired. Upload it again.", show_alert=True); return
        if DB_BACKUP_LOCK.locked():
            await cb.answer("Another database operation is running.", show_alert=True); return
        await cb.answer("Validating and restoring…")
        async with DB_BACKUP_LOCK:
            safety_path = None
            try:
                raw = Path(path).read_bytes()
                if not raw or len(raw) > MAX_DB_BACKUP_BYTES:
                    raise ValueError("Backup is empty or exceeds the configured size limit.")
                # Create and deliver a recovery copy before touching the current database.
                safety_bytes, safety_name, dialect = await create_database_backup()
                await bot.send_document(actor, BufferedInputFile(safety_bytes, filename=safety_name), caption="🛟 Automatic one-time safety backup made immediately before your manually confirmed restore. This is NOT a scheduled backup.")
                if IS_SQLITE:
                    if not path.lower().endswith(".sql"):
                        raise ValueError("SQLite restore requires an .sql backup file.")
                    await restore_sqlite_backup(raw)
                else:
                    if not path.lower().endswith((".json", ".eydb.json")):
                        raise ValueError("PostgreSQL restore requires an Exam Yatra .json backup file.")
                    await restore_postgres_backup(raw)
                # Verify that the restored database is reachable and core tables exist.
                async with engine.connect() as conn:
                    tables = await conn.run_sync(lambda c: set(sa_inspect(c).get_table_names()))
                if not {"users", "questions", "exams", "settings"}.issubset(tables):
                    raise RuntimeError("Post-restore verification failed; required tables are missing.")
                await audit(session, actor, "db.restore.success", os.path.basename(path), f"dialect={dialect}")
                await session.commit()
                await state.clear()
                await msg.answer("✅ Database restore completed and core-table verification passed. The safety backup was sent to your private admin chat.", reply_markup=admin_keyboard())
            except Exception as e:
                log.exception("Database restore failed")
                await audit(session, actor, "db.restore.failed", os.path.basename(path), type(e).__name__)
                await session.commit()
                await state.clear()
                await msg.answer(f"❌ Restore failed: {esc(type(e).__name__)}. Check server logs. Do not delete the safety backup; use it for recovery if needed.", reply_markup=admin_keyboard())
            finally:
                try: os.remove(path)
                except OSError: pass
        return
    if action == "dbcancel":
        data = await state.get_data(); path = data.get("db_restore_path")
        if path:
            try: os.remove(path)
            except OSError: pass
        await state.clear(); await cb.answer("Restore cancelled."); await edit("🛠 <b>Exam Yatra Admin Panel</b>", admin_keyboard()); return

    # ----- users -----
    if action == "users":
        await cb.answer()
        await edit("👥 <b>User Management</b>", inline([
            [("🔎 Find by Telegram ID", "adm:ufind")],
            [("🆕 Recent users", "adm:ul:recent:0"), ("🚫 Banned", "adm:ul:banned:0")],
            [("🎁 On trial", "adm:ul:trial:0"), ("⌛ Trial expired", "adm:ul:trialexp:0")],
            [("⭐ Premium active", "adm:ul:prem:0"), ("⌛ Premium expired", "adm:ul:premexp:0")],
            [("💳 Awaiting approval", "adm:ul:paypend:0"), ("💰 Converted to paid", "adm:ul:conv:0")],
            BACK_ADMIN])); return
    if action == "ufind":
        await state.set_state(AdminFlow.user_lookup); await cb.answer()
        await msg.answer("🔎 Send the user's numeric Telegram ID or @username. /cancel to abort."); return
    if action == "ul":
        now = now_utc(); page = parse_int(a3, 0) or 0
        filters = {
            "recent": (User.id > 0, "🆕 Recent users"), "banned": (User.status == "banned", "🚫 Banned users"),
            "trial": (and_(User.trial_status == "active", User.trial_ends_at > now), "🎁 Users on trial"),
            "trialexp": (or_(User.trial_status == "expired", and_(User.trial_status == "active", User.trial_ends_at <= now)), "⌛ Trial expired"),
            "trialsoon": (and_(User.trial_status == "active", User.trial_ends_at > now, User.trial_ends_at <= now + timedelta(days=2)), "⏳ Trial ending within 48h"),
            "prem": (and_(User.subscription_status == "active", or_(User.subscription_expiry.is_(None), User.subscription_expiry > now)), "⭐ Premium active"),
            "premexp": (or_(User.subscription_status == "expired", and_(User.subscription_status == "active", User.subscription_expiry <= now)), "⌛ Premium expired"),
            "paypend": (User.id.in_(select(PaymentRequest.user_id).where(PaymentRequest.status == PAY_PENDING)), "💳 Awaiting payment approval"),
            "conv": (User.id.in_(select(PaymentRequest.user_id).where(PaymentRequest.status == PAY_APPROVED)), "💰 Converted to paid"),
        }
        if a2 not in filters: await cb.answer("Unknown list.", show_alert=True); return
        where, title = filters[a2]
        await cb.answer(); text, kb = await paged_users(session, where, page, title, f"adm:ul:{a2}"); await edit(text, kb); return
    if action == "u":
        target = (await session.execute(select(User).where(User.telegram_id == (parse_int(a2, 0) or 0)))).scalar_one_or_none()
        if not target: await cb.answer("User not found.", show_alert=True); return
        op = a3
        if a4 == "confirm":
            await cb.answer()
            await edit(f"⚠️ Confirm <b>{esc(op)}</b> for {esc(target.full_name)} (<code>{target.telegram_id}</code>)?",
                       inline([[("✅ Yes, do it", f"adm:u:{target.telegram_id}:{op}:go"), ("❌ No", f"adm:u:{target.telegram_id}:view")]])); return
        if op == "view":
            await cb.answer(); await show_user_admin(msg, session, target); return
        if op in ("ban", "unban"):
            target.status = "banned" if op == "ban" else "active"
            await audit(session, actor, f"user.{op}", str(target.telegram_id))
            if op == "ban":
                t = await active_test_for(session, target)
                if t: await finalize_test(session, t, await load_test_questions(session, t), status="abandoned")
            await cb.answer("Done"); await show_user_admin(msg, session, target); return
        if op in ("revoke", "restore"):
            target.access_granted = (op == "restore")
            await audit(session, actor, f"user.access.{op}", str(target.telegram_id))
            await cb.answer("Done"); await show_user_admin(msg, session, target); return
        if op == "grant":
            await state.set_state(AdminFlow.user_action_value); await state.update_data(uid=target.telegram_id, op="grant"); await cb.answer()
            await msg.answer(f"⭐ Send the number of days of Premium to grant/extend for {esc(target.full_name)} (e.g. 30). /cancel to abort."); return
        if op == "lifetime" and a4 == "go":
            await activate_subscription(session, target, await get_setting(session, "plan_name", "Exam Yatra Premium"), 0, actor, "admin lifetime grant")
            await cb.answer("Lifetime access granted"); await show_user_admin(msg, session, target); return
        if op == "unsub" and a4 == "go":
            target.subscription_status = "revoked"; target.subscription_expiry = now_utc()
            await audit(session, actor, "subscription.revoke", str(target.telegram_id))
            await cb.answer("Premium revoked"); await show_user_admin(msg, session, target); return
        if op == "trialext":
            await state.set_state(AdminFlow.user_action_value); await state.update_data(uid=target.telegram_id, op="trialext"); await cb.answer()
            await msg.answer("🎁 Send the number of extra trial days (e.g. 3). /cancel to abort."); return
        if op == "trialreset" and a4 == "go":
            days = await setting_int(session, "trial_days", 7)
            target.trial_started_at = now_utc(); target.trial_ends_at = now_utc() + timedelta(days=days); target.trial_status = "active"
            await audit(session, actor, "trial.reset", str(target.telegram_id), f"{days} days")
            await cb.answer("Trial reset"); await show_user_admin(msg, session, target); return
        if op == "trialrevoke" and a4 == "go":
            target.trial_status = "revoked"; target.trial_ends_at = now_utc()
            await audit(session, actor, "trial.revoke", str(target.telegram_id))
            await cb.answer("Trial revoked"); await show_user_admin(msg, session, target); return
        if op == "limit":
            await state.set_state(AdminFlow.user_action_value); await state.update_data(uid=target.telegram_id, op="limit"); await cb.answer()
            await msg.answer("📏 Send <code>key value</code>, e.g. <code>ai_daily 50</code> (-1 = unlimited).\nKeys: " + ", ".join(LIMIT_KEYS)); return
        if op == "limitclear":
            target.limit_overrides = "{}"; await audit(session, actor, "limits.clear", str(target.telegram_id))
            await cb.answer("Overrides cleared"); await show_user_admin(msg, session, target); return
        if op == "usagereset":
            await session.execute(update(UsageCounter).where(UsageCounter.user_id == target.id, UsageCounter.day == today_ist()).values(count=0))
            await audit(session, actor, "usage.reset", str(target.telegram_id))
            await cb.answer("Today's counters reset"); await show_user_admin(msg, session, target); return
        await cb.answer("Unknown user action.", show_alert=True); return

    # ----- channels -----
    if action == "ch":
        if a2 == "toggle":
            cur = await setting_bool(session, "channel_verification", False)
            await set_setting(session, "channel_verification", "false" if cur else "true")
            await audit(session, actor, "channel.verification", "on" if not cur else "off")
        elif a2 == "add":
            await state.set_state(AdminFlow.channel_add); await cb.answer()
            await msg.answer("➕ Send the channel as <code>@username</code> or its numeric chat id (e.g. -1001234567890). "
                             "Make the bot an administrator of the channel first. /cancel to abort."); return
        elif a2 == "en":
            ch = await session.get(RequiredChannel, parse_int(a3, 0) or 0)
            if ch: ch.enabled = not ch.enabled; await audit(session, actor, "channel.toggle", ch.chat_ref, str(ch.enabled))
        elif a2 == "url":
            await state.set_state(AdminFlow.channel_invite); await state.update_data(ch_id=parse_int(a3, 0)); await cb.answer()
            await msg.answer("🔗 Send the invite URL (https://t.me/...). Send <code>-</code> to clear. /cancel to abort."); return
        elif a2 == "del":
            ch = await session.get(RequiredChannel, parse_int(a3, 0) or 0)
            if a4 == "confirm":
                await cb.answer(); await edit(f"⚠️ Remove channel {esc(ch.chat_ref) if ch else '?'}?", inline([[("✅ Remove", f"adm:ch:del:{a3}:go"), ("❌ Keep", "adm:ch")]])); return
            if ch and a4 == "go":
                await session.delete(ch); await audit(session, actor, "channel.remove", ch.chat_ref)
        elif a2 == "check":
            report = []
            for ch in list((await session.execute(select(RequiredChannel))).scalars()):
                try:
                    me = await bot.get_chat_member(channel_chat_id(ch), (await bot.me()).id)
                    chat = await bot.get_chat(channel_chat_id(ch))
                    ch.title = (chat.title or ch.title or "")[:160]
                    report.append(f"{'✅' if me.status in (ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.CREATOR) else '⚠️ not admin'} {esc(ch.chat_ref)} — {esc(chat.title)}")
                except TelegramAPIError as e:
                    report.append(f"❌ {esc(ch.chat_ref)} — {esc(str(e)[:80])}")
            await cb.answer(); await msg.answer("🔎 <b>Bot rights check</b>\n\n" + ("\n".join(report) or "No channels."))
        await cb.answer()
        text, kb = await channels_screen(session); await edit(text, kb); return

    # ----- trials -----
    if action == "trial":
        await cb.answer()
        await edit(f"🎁 <b>Trial Management</b>\n\nTrial: {'enabled' if await setting_bool(session, 'trial_enabled', True) else 'disabled'} · "
                   f"{await setting_int(session, 'trial_days', 7)} days for new users.\nUse a user's card to extend, reset or revoke an individual trial.",
                   inline([[("🎁 Toggle trial", "adm:toggle:trial_enabled"), ("📆 Trial days", "adm:set:trial_days")],
                           [("🎁 On trial", "adm:ul:trial:0"), ("⏳ Ending in 48h", "adm:ul:trialsoon:0")],
                           [("⌛ Expired", "adm:ul:trialexp:0"), ("💰 Converted", "adm:ul:conv:0")], BACK_ADMIN])); return

    # ----- plan / payments -----
    if action == "plan":
        if a2 == "preview":
            await cb.answer(); p = await plan_config(session)
            if not upi_id_valid(p["upi_id"]) or p["validity_days"] < 0:
                await msg.answer("Configure a valid UPI ID and validity first."); return
            uri = build_upi_uri(p["upi_id"], p["payee"], p["price"], "ExamYatra preview")
            try: await msg.answer_photo(BufferedInputFile(make_qr_png(uri), filename="preview.png"), caption=f"Preview — ₹{p['price']:.2f} to <code>{esc(p['upi_id'])}</code>\n<code>{esc(uri)}</code>")
            except Exception as e: await msg.answer(f"QR generation failed: {esc(type(e).__name__)}")
            return
        await cb.answer(); text, kb = await plan_screen(session); await edit(text, kb); return
    if action == "set" and a2 in SETTING_PROMPTS:
        await state.set_state(AdminFlow.setting_value); await state.update_data(key=a2); await cb.answer()
        await msg.answer("✏️ " + SETTING_PROMPTS[a2] + f"\nCurrent: <code>{esc(await get_setting(session, a2, '')) or '—'}</code>\n/cancel to abort."); return
    if action == "toggle" and a2 in ("purchases_enabled", "trial_enabled"):
        cur = await setting_bool(session, a2, True); await set_setting(session, a2, "false" if cur else "true")
        await audit(session, actor, f"setting.{a2}", str(not cur)); await cb.answer("Toggled")
        text, kb = await plan_screen(session); await edit(text, kb); return
    if action == "pay":
        status = a2 or PAY_PENDING; await cb.answer()
        text, kb = await payments_list(session, status, parse_int(a3, 0) or 0); await edit(text, kb); return
    if action == "payv":
        req = await session.get(PaymentRequest, parse_int(a2, 0) or 0)
        if not req: await cb.answer("Not found.", show_alert=True); return
        u = await session.get(User, req.user_id); await cb.answer()
        try:
            if req.screenshot_file_id:
                await msg.answer_photo(req.screenshot_file_id, caption=admin_payment_text(req, u), reply_markup=admin_payment_keyboard(req))
            else:
                await msg.answer(admin_payment_text(req, u), reply_markup=admin_payment_keyboard(req))
        except TelegramBadRequest:
            await msg.answer(admin_payment_text(req, u), reply_markup=admin_payment_keyboard(req))
        return

    # ----- question bank -----
    if action == "qb":
        await cb.answer(); await state.clear(); text, kb = await qb_screen(session); await edit(text, kb); return
    if action == "qr" and a2 in Q_STATUSES:
        await cb.answer(); text, kb = await question_list(session, Question.status == a2, parse_int(a3, 0) or 0, f"Questions — {a2}", f"adm:qr:{a2}"); await edit(text, kb); return
    if action == "qexam":
        ex = await session.get(Exam, parse_int(a2, 0) or 0); await cb.answer()
        text, kb = await question_list(session, Question.exam_id == (ex.id if ex else -1), parse_int(a3, 0) or 0, f"Questions — {ex.name if ex else '?'}", f"adm:qexam:{a2}"); await edit(text, kb); return
    if action == "qsearch":
        await state.set_state(AdminFlow.search_question); await cb.answer()
        await msg.answer("🔎 Send a question ID (e.g. <code>42</code>) or a search phrase. /cancel to abort."); return
    if action == "qdups":
        await cb.answer()
        dup_hashes = list((await session.execute(select(Question.text_hash).group_by(Question.text_hash).having(func.count(Question.id) > 1).limit(20))).scalars())
        if not dup_hashes: await msg.answer("👯 No exact duplicates found."); return
        lines = ["👯 <b>Duplicate groups</b>", ""]
        for h in dup_hashes:
            group = list((await session.execute(select(Question).where(Question.text_hash == h).order_by(Question.id))).scalars())
            lines.append("• " + ", ".join(f"#{q.id}({q.status})" for q in group) + f" — {esc(group[0].text[:60])}")
        await msg.answer("\n".join(lines)); return
    if action == "addq":
        exams = list((await session.execute(select(Exam).where(Exam.active.is_(True)).order_by(Exam.name))).scalars())
        await cb.answer()
        await edit("➕ <b>Add question</b> — choose the exam:", inline([[(e.name, f"adm:addqe:{e.id}")] for e in exams] + [[("⬅️ Question Bank", "adm:qb")]])); return
    if action == "addqe":
        ex = await session.get(Exam, parse_int(a2, 0) or 0)
        if not ex: await cb.answer("Exam not found.", show_alert=True); return
        await state.set_state(AdminFlow.add_question); await state.update_data(exam_id=ex.id); await cb.answer()
        await msg.answer(f"➕ Adding to <b>{esc(ex.name)}</b>. You can send several questions one after another; /cancel when done.\n\n" + QUESTION_FORMAT_HELP); return
    if action == "q":
        q = await session.get(Question, parse_int(a2, 0) or 0)
        if not q: await cb.answer("Question not found.", show_alert=True); return
        op = a3
        ex = await session.get(Exam, q.exam_id); sub = await session.get(Subject, q.subject_id) if q.subject_id else None
        if op == "view":
            await cb.answer(); await edit(render_question_admin(q, ex.name if ex else "", sub.name if sub else ""), question_admin_keyboard(q)); return
        if op == "approve":
            probs = question_problems(q)
            if probs: await cb.answer("Cannot approve: " + "; ".join(probs)[:150], show_alert=True); return
            q.status = Q_APPROVED; q.verified_at = now_utc(); q.verified_by = actor; q.published = True
            await audit(session, actor, "question.approve", str(q.id)); await cb.answer("Approved ✅")
        elif op == "reject":
            q.status = Q_REJECTED; q.verified_at = now_utc(); q.verified_by = actor
            await audit(session, actor, "question.reject", str(q.id)); await cb.answer("Rejected")
        elif op == "pub":
            q.published = not q.published; await audit(session, actor, "question.publish", str(q.id), str(q.published)); await cb.answer("Updated")
        elif op == "edit":
            await state.set_state(AdminFlow.edit_question); await state.update_data(qid=q.id); await cb.answer()
            await msg.answer(f"✏️ Editing #{q.id}. Send the full block again (it replaces text, options, answer and metadata; the question returns to <i>pending</i>).\n\n" + QUESTION_FORMAT_HELP); return
        elif op == "preview":
            await cb.answer()
            await msg.answer(f"❓ <b>PREVIEW</b>\n\n━━━━━━━━━━━━━━━━━━━━\n\n<b>{esc(q.text)}</b>",
                             reply_markup=inline([[(button_label(LETTERS[i], o.text), "noop")] for i, o in enumerate(q.options)])); return
        elif op == "del":
            if a4 == "confirm":
                await cb.answer(); await edit(f"⚠️ Permanently delete question #{q.id}? Attempt history that references it is kept.", inline([[("🗑 Delete", f"adm:q:{q.id}:del:go"), ("❌ Keep", f"adm:q:{q.id}:view")]])); return
            if a4 == "go":
                await session.execute(update(MockQuestion).where(MockQuestion.question_id == q.id).values(position=0))
                await session.execute(sa_text("DELETE FROM mock_questions WHERE question_id = :q"), {"q": q.id})
                await session.delete(q); await audit(session, actor, "question.delete", str(q.id)); await cb.answer("Deleted")
                text, kb = await qb_screen(session); await edit(text, kb); return
        await session.flush()
        await edit(render_question_admin(q, ex.name if ex else "", sub.name if sub else ""), question_admin_keyboard(q)); return

    # ----- materials -----
    if action == "mat":
        if a2 == "add":
            await state.set_state(AdminFlow.material_meta); await cb.answer(); await msg.answer("📂 " + MATERIAL_FORMAT_HELP + "\n/cancel to abort."); return
        await cb.answer(); text, kb = await materials_admin_screen(session, parse_int(a3, 0) or 0 if a2 == "p" else 0); await edit(text, kb); return
    if action == "matv":
        m = await session.get(Material, parse_int(a2, 0) or 0)
        if not m: await cb.answer("Not found.", show_alert=True); return
        op = a3
        if op == "pub":
            m.published = not m.published; await audit(session, actor, "material.publish", str(m.id), str(m.published))
        elif op == "del":
            if a4 == "confirm":
                await cb.answer(); await edit(f"⚠️ Delete material #{m.id} “{esc(m.title)}”?", inline([[("🗑 Delete", f"adm:matv:{m.id}:del:go"), ("❌ Keep", f"adm:matv:{m.id}")]])); return
            if a4 == "go":
                await session.delete(m); await audit(session, actor, "material.delete", str(m.id)); await cb.answer("Deleted")
                text, kb = await materials_admin_screen(session); await edit(text, kb); return
        elif op == "preview":
            await cb.answer(); await deliver_material(msg, m); return
        await cb.answer()
        ex = await session.get(Exam, m.exam_id) if m.exam_id else None
        await edit(f"📂 <b>#{m.id} {esc(m.title)}</b>\nExam: {esc(ex.name if ex else 'all')} · Subject: {esc(m.subject) or '—'} · Topic: {esc(m.topic) or '—'}\n"
                   f"Format: {m.fmt} · Lang: {m.language} · {'published' if m.published else 'unpublished'}\nFile: {esc(m.file_name) or '—'} · URL: {esc(m.url) or '—'}\n"
                   f"{esc(m.description) or ''}",
                   inline([[("👁 Preview", f"adm:matv:{m.id}:preview"), ("📴 Unpublish" if m.published else "📶 Publish", f"adm:matv:{m.id}:pub")],
                           [("🗑 Delete", f"adm:matv:{m.id}:del:confirm")], [("⬅️ Materials", "adm:mat")]])); return

    # ----- limits -----
    if action == "lim":
        await cb.answer(); text, kb = await limits_screen(session); await edit(text, kb); return
    if action == "limset" and a2 in TIERS:
        await state.set_state(AdminFlow.setting_value); await state.update_data(key=f"policy:{a2}"); await cb.answer()
        await msg.answer(f"✏️ Send <code>key value</code> for tier <b>{a2}</b>, e.g. <code>ai_daily 20</code>. Keys: {', '.join(LIMIT_KEYS)}. /cancel to abort."); return
    if action == "limhit":
        await cb.answer(); day = today_ist(); pol = await load_policies(session)
        rows = (await session.execute(select(UsageCounter, User).join(User, User.id == UsageCounter.user_id).where(UsageCounter.day == day))).all()
        hits = []
        for uc, u in rows:
            lk = {"ai": "ai_daily", "image": "image_daily", "aitest": "aitest_daily", "quiz": "quiz_daily", "mock": "mock_daily"}.get(uc.feature)
            if not lk: continue
            cap = {**pol[user_tier(u)], **u.overrides()}.get(lk, 0)
            if cap >= 0 and uc.count >= cap: hits.append(f"• {esc(u.full_name)} <code>{u.telegram_id}</code> — {uc.feature} {uc.count}/{cap}")
        await msg.answer("📈 <b>Users at a limit today</b>\n\n" + ("\n".join(hits[:50]) or "None.")); return
    if action == "limhist":
        await cb.answer()
        since = (datetime.now(IST) - timedelta(days=6)).strftime("%Y-%m-%d")
        rows = (await session.execute(select(UsageCounter.day, UsageCounter.feature, func.sum(UsageCounter.count)).where(UsageCounter.day >= since)
                                      .group_by(UsageCounter.day, UsageCounter.feature).order_by(UsageCounter.day.desc()))).all()
        by_day: dict[str, list[str]] = {}
        for d, f, n in rows: by_day.setdefault(d, []).append(f"{f} {int(n)}")
        await msg.answer("📊 <b>Usage — last 7 days</b>\n\n" + ("\n".join(f"{d}: {', '.join(v)}" for d, v in by_day.items()) or "No data.")); return

    # ----- API key -----
    if action == "api":
        key = await current_api_key(session); src = "database" if await get_setting(session, "gemini_api_key", "") else ("environment" if ENV_GEMINI_API_KEY else "none")
        if a2 == "test":
            await cb.answer("Testing…")
            ok, info = await test_api_key(key) if key else (False, "No key configured.")
            await msg.answer(("✅ " if ok else "❌ ") + info); return
        if a2 == "add":
            await state.set_state(AdminFlow.api_key); await cb.answer()
            await msg.answer("🔑 Send the Gemini API key. It is validated with a real request before saving, and your message is deleted afterwards. /cancel to abort."); return
        if a2 == "del":
            if a4 == "confirm" or a3 == "confirm":
                await cb.answer(); await edit("⚠️ Remove the saved API key? The environment variable (if any) will be used instead.", inline([[("🗑 Remove", "adm:api:del:go"), ("❌ Keep", "adm:api")]])); return
            await set_setting(session, "gemini_api_key", ""); await audit(session, actor, "apikey.remove"); await cb.answer("Removed")
        else:
            await cb.answer()
        key = await current_api_key(session)
        await edit(f"🔑 <b>API Management</b>\n\nModel: <code>{esc(GEMINI_MODEL)}</code>\nKey: <code>{esc(mask_key(key))}</code> (source: {src})",
                   inline([[("🧪 Test current key", "adm:api:test")], [("➕ Add / replace key", "adm:api:add"), ("🗑 Remove saved key", "adm:api:del:confirm")], BACK_ADMIN])); return

    # ----- features / broadcast / maintenance / support / exams / mocks / audit -----
    if action == "feat":
        if a2 in FEATURE_KEYS:
            cur = await feature_enabled(session, a2); await set_setting(session, f"feature:{a2}", "false" if cur else "true")
            await audit(session, actor, "feature.toggle", a2, str(not cur))
        await cb.answer()
        status = {k: await feature_enabled(session, k) for k in FEATURE_KEYS}
        await edit("⚙️ <b>Features</b> — disabled features are blocked in their handlers, not just hidden.", features_keyboard(status)); return
    if action == "bc":
        await state.set_state(AdminFlow.broadcast); await cb.answer()
        await msg.answer("📣 Send the broadcast text (HTML allowed). It goes to all active, non-banned users. /cancel to abort."); return
    if action == "maint":
        if a2 == "toggle":
            cur = await maintenance_on(session); await set_setting(session, "maintenance", "false" if cur else "true")
            await audit(session, actor, "maintenance", str(not cur))
        await cb.answer()
        await edit(f"🛠 <b>Maintenance</b>: {'ON' if await maintenance_on(session) else 'off'}\nMessage: {esc(await get_setting(session, 'maintenance_message', ENV_MAINTENANCE_MESSAGE))}",
                   inline([[("🔁 Toggle", "adm:maint:toggle"), ("✏️ Message", "adm:set:maintenance_message")], BACK_ADMIN])); return
    if action == "support":
        await cb.answer()
        await edit(f"📨 <b>Support contact</b>: {esc(await support_contact(session)) or '— (not set)'}\nShown in Help, Subscription, payment and access screens.",
                   inline([[("✏️ Change", "adm:set:support_contact")], BACK_ADMIN])); return
    if action == "addexam":
        await state.set_state(AdminFlow.add_exam); await cb.answer(); await msg.answer("➕ Send the new exam name (e.g. <code>SSC CGL</code>). /cancel to abort."); return
    if action == "mock":
        tests = list((await session.execute(select(MockTest).order_by(MockTest.id.desc()).limit(15))).scalars())
        lines = ["📝 <b>Mock tests</b>", ""]
        rows: list[list[tuple[str, str]]] = [[("➕ Create mock test", "adm:mockadd")]]
        for t in tests:
            n = len(await mock_servable_questions(session, t.id)); total = await admin_count(session, select(MockQuestion.id).where(MockQuestion.test_id == t.id))
            lines.append(f"{'🟢' if t.published else '⚪️'} #{t.id} {esc(t.title)} — {n}/{total} approved · {t.duration} min")
            rows.append([(f"{'📴' if t.published else '📶'} #{t.id} {t.title[:20]}", f"adm:mockpub:{t.id}"), (f"➕ add Qs #{t.id}", f"adm:mockq:{t.id}")])
        rows.append(BACK_ADMIN); await cb.answer(); await edit("\n".join(lines), inline(rows)); return
    if action == "mockadd":
        await state.set_state(AdminFlow.mock_test); await state.update_data(step="create"); await cb.answer()
        await msg.answer("📝 Send: <code>Exam name | Test title | duration minutes</code>\nExample: <code>Bihar Police | Constable Set 1 | 30</code>. /cancel to abort."); return
    if action == "mockpub":
        t = await session.get(MockTest, parse_int(a2, 0) or 0)
        if t: t.published = not t.published; await audit(session, actor, "mock.publish", str(t.id), str(t.published))
        await cb.answer("Updated"); await admin_callbacks(cb.model_copy(update={"data": "adm:mock"}), session=session, db_user=db_user, state=state, bot=bot); return
    if action == "mockq":
        t = await session.get(MockTest, parse_int(a2, 0) or 0)
        if not t: await cb.answer("Not found.", show_alert=True); return
        await state.set_state(AdminFlow.mock_test); await state.update_data(step="attach", test_id=t.id); await cb.answer()
        await msg.answer(f"➕ Send approved question IDs to attach to <b>{esc(t.title)}</b>, separated by spaces or commas (e.g. <code>12 15 19</code>), "
                         "or <code>auto 20</code> to attach 20 random approved questions of this exam. /cancel when done."); return
    if action == "audit":
        page = parse_int(a2, 0) or 0; await cb.answer()
        rows = list((await session.execute(select(AuditLog).order_by(AuditLog.id.desc()).offset(page * 15).limit(15))).scalars())
        text = "📜 <b>Audit log</b>\n\n" + ("\n".join(f"{fmt_dt(r.at)} · {r.actor_tg_id} · <b>{esc(r.action)}</b> {esc(r.target) or ''} {esc((r.details or '')[:60])}" for r in rows) or "Empty.")
        await edit(text, inline([[("⬅️", f"adm:audit:{max(0, page - 1)}"), ("➡️", f"adm:audit:{page + 1}")], BACK_ADMIN])); return
    await cb.answer("Unknown admin action.", show_alert=True)


@router.callback_query(F.data == "noop")
async def noop(cb: CallbackQuery):
    await cb.answer()



# ============================ Admin text inputs (FSM) ============================
@router.message(AdminFlow.add_exam, F.text)
@admin_only
async def admin_add_exam(message: Message, session: AsyncSession, db_user: User, state: FSMContext, **_):
    if _is_cmd(message): raise SkipHandler
    name = (message.text or "").strip()[:100]
    if len(name) < 2: await message.answer("Name too short."); return
    if (await session.execute(select(Exam).where(func.lower(Exam.name) == name.lower()))).scalar_one_or_none():
        await message.answer("Exam already exists."); return
    session.add(Exam(name=name)); await audit(session, message.from_user.id, "exam.add", name); await state.clear()
    await message.answer(f"✅ Added exam: <b>{esc(name)}</b>", reply_markup=admin_keyboard())


@router.message(AdminFlow.add_question, F.text)
@admin_only
async def admin_add_question(message: Message, session: AsyncSession, db_user: User, state: FSMContext, **_):
    if _is_cmd(message): raise SkipHandler
    exam_id = (await state.get_data()).get("exam_id")
    if not exam_id: await state.clear(); await message.answer("Exam selection lost — open Question Bank → Add question again."); return
    data, err = parse_question_block(message.text or "")
    if err: await message.answer(err); return
    q, err = await create_bank_question(session, exam_id, data, message.from_user.id)
    if err: await message.answer(err); return
    await message.answer(f"🕒 Saved as <b>pending</b> question #{q.id}. Send another, or /cancel.", reply_markup=inline([[("✅ Approve now", f"adm:q:{q.id}:approve"), ("👁 View", f"adm:q:{q.id}:view")]]))


@router.message(AdminFlow.edit_question, F.text)
@admin_only
async def admin_edit_question(message: Message, session: AsyncSession, db_user: User, state: FSMContext, **_):
    if _is_cmd(message): raise SkipHandler
    qid = (await state.get_data()).get("qid"); q = await session.get(Question, qid) if qid else None
    if not q: await state.clear(); await message.answer("Question no longer exists."); return
    data, err = parse_question_block(message.text or "")
    if err: await message.answer(err); return
    dup = await find_duplicate(session, data["text"], exclude_id=q.id)
    if dup: await message.answer(f"Rejected: duplicate of question #{dup.id}."); return
    q.text = data["text"]; q.explanation = data.get("explanation"); q.topic = data.get("topic"); q.source = data.get("source"); q.reference_url = data.get("url")
    q.subject_id = await get_or_create_subject(session, q.exam_id, data.get("subject")) or q.subject_id
    q.text_hash = question_hash(q.text); q.status = Q_PENDING; q.verified_at = None; q.verified_by = None
    for o in list(q.options): await session.delete(o)
    await session.flush()
    for i, o in enumerate(data["options"]): session.add(Option(question_id=q.id, position=i, text=o, correct=(i == data["correct_index"])))
    await session.flush(); await session.refresh(q, attribute_names=["options"])
    await audit(session, message.from_user.id, "question.edit", str(q.id)); await state.clear()
    ex = await session.get(Exam, q.exam_id)
    await message.answer(render_question_admin(q, ex.name if ex else ""), reply_markup=question_admin_keyboard(q))


@router.message(AdminFlow.search_question, F.text)
@admin_only
async def admin_search_question(message: Message, session: AsyncSession, db_user: User, state: FSMContext, **_):
    if _is_cmd(message): raise SkipHandler
    term = (message.text or "").strip(); await state.clear()
    if term.isdigit():
        q = await session.get(Question, int(term))
        if not q: await message.answer("No question with that ID."); return
        ex = await session.get(Exam, q.exam_id); sub = await session.get(Subject, q.subject_id) if q.subject_id else None
        await message.answer(render_question_admin(q, ex.name if ex else "", sub.name if sub else ""), reply_markup=question_admin_keyboard(q)); return
    qs = list((await session.execute(select(Question).where(func.lower(Question.text).like(f"%{term.lower()}%")).order_by(Question.id.desc()).limit(15))).scalars())
    if not qs: await message.answer("No matches."); return
    await message.answer(f"🔎 Matches for “{esc(term)}”:", reply_markup=inline([[(f"#{q.id} [{q.status}] {q.text[:35]}", f"adm:q:{q.id}:view")] for q in qs] + [[("⬅️ Question Bank", "adm:qb")]]))


@router.message(AdminFlow.material_meta, F.text)
@admin_only
async def admin_material_meta(message: Message, session: AsyncSession, db_user: User, state: FSMContext, **_):
    if _is_cmd(message): raise SkipHandler
    fields: dict[str, str] = {}
    for line in (message.text or "").splitlines():
        m = re.match(r"^\s*(TITLE|EXAM|SUB|TOPIC|LANG|FMT|URL|DESC|SRC)\s*[:：]\s*(.*)$", line, re.I)
        if m: fields[m.group(1).upper()] = m.group(2).strip()
    title, fmt = fields.get("TITLE", ""), fields.get("FMT", "").lower()
    if len(title) < 3: await message.answer("TITLE is required (3+ chars)."); return
    if fmt not in MATERIAL_FORMATS: await message.answer("FMT must be one of: " + ", ".join(MATERIAL_FORMATS)); return
    exam = None
    if fields.get("EXAM"):
        exam = (await session.execute(select(Exam).where(func.lower(Exam.name) == fields["EXAM"].lower()))).scalar_one_or_none()
        if not exam: await message.answer(f"Exam “{esc(fields['EXAM'])}” not found. Add it first or fix the name."); return
    if not fields.get("SUB"): await message.answer("SUB (subject) is required so students can find the material."); return
    url = fields.get("URL", "")
    if fmt == "link" and not re.match(r"^https?://", url): await message.answer("A link material needs a valid URL."); return
    lang = fields.get("LANG", "en").lower(); lang = lang if lang in ("en", "hi") else "en"
    meta = {"title": title[:200], "exam_id": exam.id if exam else None, "subject": fields["SUB"][:100], "topic": fields.get("TOPIC") or None,
            "language": lang, "fmt": fmt, "url": url or None, "description": fields.get("DESC") or None, "source": fields.get("SRC") or None}
    if fmt in ("link", "notes"):
        m = Material(**meta, published=True, created_at=now_utc()); session.add(m); await session.flush()
        await audit(session, message.from_user.id, "material.add", str(m.id), title); await state.clear()
        await message.answer(f"✅ Material #{m.id} published.", reply_markup=admin_keyboard()); return
    await state.set_state(AdminFlow.material_file); await state.update_data(meta=meta)
    await message.answer("📎 Now upload the file (as a document; images may be sent as photo). /cancel to abort.")


@router.message(AdminFlow.material_file, F.document | F.photo)
@admin_only
async def admin_material_file(message: Message, session: AsyncSession, db_user: User, state: FSMContext, **_):
    meta = (await state.get_data()).get("meta")
    if not meta: await state.clear(); await message.answer("Metadata lost — start again."); return
    if message.document:
        file_id, fname = message.document.file_id, message.document.file_name
        if meta["fmt"] == "pdf" and (message.document.mime_type or "") not in ("application/pdf",) and not (fname or "").lower().endswith(".pdf"):
            await message.answer("Expected a PDF file."); return
    else:
        file_id, fname = message.photo[-1].file_id, "photo.jpg"
        if meta["fmt"] != "image": await message.answer("Send this as a document (file), not as a photo."); return
    m = Material(**meta, file_id=file_id, file_name=(fname or "")[:200], published=True, created_at=now_utc())
    session.add(m); await session.flush(); await audit(session, message.from_user.id, "material.add", str(m.id), meta["title"]); await state.clear()
    await message.answer(f"✅ Material #{m.id} published (delivered via Telegram file_id).", reply_markup=admin_keyboard())


@router.message(AdminFlow.mock_test, F.text)
@admin_only
async def admin_mock_input(message: Message, session: AsyncSession, db_user: User, state: FSMContext, **_):
    if _is_cmd(message): raise SkipHandler
    data = await state.get_data()
    if data.get("step") == "create":
        p = [x.strip() for x in (message.text or "").split("|")]
        if len(p) != 3: await message.answer("Format: Exam name | Title | minutes"); return
        exam = (await session.execute(select(Exam).where(func.lower(Exam.name) == p[0].lower()))).scalar_one_or_none()
        mins = parse_int(p[2], None)
        if not exam: await message.answer("Exam not found."); return
        if not mins or not (1 <= mins <= 300): await message.answer("Duration must be 1–300 minutes."); return
        t = MockTest(exam_id=exam.id, title=p[1][:160], duration=mins, published=False); session.add(t); await session.flush()
        await audit(session, message.from_user.id, "mock.create", str(t.id), t.title)
        await state.update_data(step="attach", test_id=t.id)
        await message.answer(f"✅ Created mock test #{t.id} (unpublished). Now send approved question IDs (e.g. <code>12 15 19</code>) or <code>auto 20</code>. /cancel when done."); return
    t = await session.get(MockTest, data.get("test_id") or 0)
    if not t: await state.clear(); await message.answer("Mock test not found."); return
    txt = (message.text or "").strip().lower()
    existing = set((await session.execute(select(MockQuestion.question_id).where(MockQuestion.test_id == t.id))).scalars())
    pos = len(existing)
    if txt.startswith("auto"):
        n = parse_int(txt.split()[-1], 10) or 10
        pool = [q for q in (await session.execute(select(Question).where(Question.exam_id == t.exam_id, Question.status == Q_APPROVED, Question.published.is_(True)))).scalars() if is_servable(q) and q.id not in existing]
        random.shuffle(pool); ids = [q.id for q in pool[:n]]
    else:
        ids = [int(x) for x in re.findall(r"\d+", txt)]
    added, skipped = 0, []
    for qid in ids:
        q = await session.get(Question, qid)
        if not q or q.exam_id != t.exam_id or not is_servable(q) or qid in existing:
            skipped.append(qid); continue
        session.add(MockQuestion(test_id=t.id, question_id=qid, position=pos)); pos += 1; existing.add(qid); added += 1
    await session.flush()
    await message.answer(f"➕ Attached {added} question(s) to #{t.id} (total {pos})." + (f"\nSkipped (not approved / wrong exam / duplicate): {skipped[:20]}" if skipped else "") +
                         "\nSend more IDs, or /cancel. Publish it from Admin → Mock tests.")


@router.message(AdminFlow.api_key, F.text)
@admin_only
async def admin_api_key(message: Message, session: AsyncSession, db_user: User, state: FSMContext, **_):
    if _is_cmd(message): raise SkipHandler
    key = (message.text or "").strip()
    await try_delete(message)
    if len(key) < 20 or " " in key: await message.answer("That does not look like an API key."); return
    note = await message.answer("🧪 Validating key…")
    ok, info = await test_api_key(key)
    if not ok:
        await safe_edit(note, "❌ Key not saved. " + info); return
    await set_setting(session, "gemini_api_key", key); await audit(session, message.from_user.id, "apikey.set", mask_key(key)); await state.clear()
    await safe_edit(note, "✅ Key saved. " + info)


@router.message(AdminFlow.channel_add, F.text)
@admin_only
async def admin_channel_add(message: Message, session: AsyncSession, db_user: User, state: FSMContext, bot: Bot, **_):
    if _is_cmd(message): raise SkipHandler
    ref = (message.text or "").strip()
    if not (re.fullmatch(r"@[A-Za-z0-9_]{5,32}", ref) or re.fullmatch(r"-?\d{6,20}", ref)):
        await message.answer("Send @username or a numeric chat id."); return
    ch = RequiredChannel(chat_ref=ref, enabled=True)
    try:
        chat = await bot.get_chat(int(ref) if ref.lstrip("-").isdigit() else ref)
        ch.title = (chat.title or "")[:160]
        if getattr(chat, "username", None): ch.invite_url = f"https://t.me/{chat.username}"
        elif getattr(chat, "invite_link", None): ch.invite_url = chat.invite_link
        me = await bot.get_chat_member(chat.id, (await bot.me()).id)
        warn = "" if me.status in (ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.CREATOR) else "\n⚠️ The bot is NOT an admin there yet — membership checks will fail until it is."
    except TelegramAPIError as e:
        warn = f"\n⚠️ Could not read the chat ({esc(str(e)[:80])}). Add the bot as admin, then use 🔎 Check bot rights."
    session.add(ch); await session.flush(); await audit(session, message.from_user.id, "channel.add", ref); await state.clear()
    text, kb = await channels_screen(session)
    await message.answer(f"✅ Channel {esc(ref)} added.{warn}"); await message.answer(text, reply_markup=kb)


@router.message(AdminFlow.channel_invite, F.text)
@admin_only
async def admin_channel_invite(message: Message, session: AsyncSession, db_user: User, state: FSMContext, **_):
    if _is_cmd(message): raise SkipHandler
    ch = await session.get(RequiredChannel, (await state.get_data()).get("ch_id") or 0)
    if not ch: await state.clear(); await message.answer("Channel not found."); return
    val = (message.text or "").strip()
    if val != "-" and not val.startswith("https://t.me/"): await message.answer("Send a https://t.me/ link or - to clear."); return
    ch.invite_url = None if val == "-" else val[:500]; await state.clear()
    text, kb = await channels_screen(session); await message.answer(text, reply_markup=kb)


@router.message(AdminFlow.user_lookup, F.text)
@admin_only
async def admin_user_lookup(message: Message, session: AsyncSession, db_user: User, state: FSMContext, **_):
    if _is_cmd(message): raise SkipHandler
    term = (message.text or "").strip(); await state.clear()
    if term.lstrip("-").isdigit():
        u = (await session.execute(select(User).where(User.telegram_id == int(term)))).scalar_one_or_none()
    else:
        u = (await session.execute(select(User).where(func.lower(User.username) == term.lstrip("@").lower()))).scalar_one_or_none()
    if not u: await message.answer("User not found (they must have started the bot at least once)."); return
    await show_user_admin(message, session, u, edit=False)


@router.message(AdminFlow.user_action_value, F.text)
@admin_only
async def admin_user_action_value(message: Message, session: AsyncSession, db_user: User, state: FSMContext, bot: Bot, **_):
    if _is_cmd(message): raise SkipHandler
    data = await state.get_data(); op = data.get("op")
    u = (await session.execute(select(User).where(User.telegram_id == data.get("uid")))).scalar_one_or_none()
    if not u: await state.clear(); await message.answer("User not found."); return
    txt = (message.text or "").strip()
    if op == "grant":
        days = parse_int(txt, None)
        if not days or days <= 0 or days > 3650: await message.answer("Send a positive number of days."); return
        await activate_subscription(session, u, await get_setting(session, "plan_name", "Exam Yatra Premium"), days, message.from_user.id, "admin grant")
        try: await bot.send_message(u.telegram_id, f"🎉 Premium access granted until <b>{fmt_dt(u.subscription_expiry)}</b>.")
        except TelegramAPIError: pass
    elif op == "trialext":
        days = parse_int(txt, None)
        if not days or days <= 0 or days > 365: await message.answer("Send a positive number of days."); return
        refresh_entitlements(u)
        base = u.trial_ends_at if (u.trial_status == "active" and u.trial_ends_at and u.trial_ends_at > now_utc()) else now_utc()
        if not u.trial_started_at: u.trial_started_at = now_utc()
        u.trial_ends_at = base + timedelta(days=days); u.trial_status = "active"; u.trial_extended_by_admin += days
        await audit(session, message.from_user.id, "trial.extend", str(u.telegram_id), f"+{days}d")
    elif op == "limit":
        p = txt.split()
        if len(p) != 2 or p[0] not in LIMIT_KEYS or parse_int(p[1], None) is None: await message.answer("Format: <code>key value</code>."); return
        ov = u.overrides(); ov[p[0]] = int(p[1]); u.limit_overrides = json.dumps(ov)
        await audit(session, message.from_user.id, "limits.override", str(u.telegram_id), f"{p[0]}={p[1]}")
    await state.clear(); await session.flush()
    await show_user_admin(message, session, u, edit=False)


@router.message(AdminFlow.setting_value, F.text)
@admin_only
async def admin_setting_value(message: Message, session: AsyncSession, db_user: User, state: FSMContext, **_):
    if _is_cmd(message): raise SkipHandler
    key = (await state.get_data()).get("key") or ""
    txt = (message.text or "").strip()
    if key.startswith("policy:"):
        tier = key.split(":")[1]; p = txt.split()
        if len(p) != 2 or p[0] not in LIMIT_KEYS or parse_int(p[1], None) is None: await message.answer("Format: <code>key value</code>."); return
        await save_policy(session, tier, p[0], int(p[1])); await audit(session, message.from_user.id, "policy.set", tier, f"{p[0]}={p[1]}")
        await state.clear(); text, kb = await limits_screen(session); await message.answer(text, reply_markup=kb); return
    err = await apply_setting(session, key, txt)
    if err: await message.answer("❌ " + err); return
    await audit(session, message.from_user.id, "setting.set", key, txt if key not in ("upi_id",) else "***")
    await state.clear()
    await message.answer(f"✅ Saved <b>{esc(key)}</b>.", reply_markup=admin_keyboard())


@router.message(AdminFlow.broadcast, F.text)
@admin_only
async def admin_broadcast(message: Message, session: AsyncSession, db_user: User, state: FSMContext, bot: Bot, **_):
    if _is_cmd(message): raise SkipHandler
    text = message.html_text or message.text or ""
    await state.clear()
    ids = list((await session.execute(select(User.telegram_id).where(User.status == "active", User.access_granted.is_(True)))).scalars())
    await audit(session, message.from_user.id, "broadcast", details=f"{len(ids)} recipients")
    await session.commit()
    sent = failed = 0
    status = await message.answer(f"📣 Sending to {len(ids)} users…")
    for i, tg_id in enumerate(ids, 1):
        try:
            await bot.send_message(tg_id, text); sent += 1
        except TelegramForbiddenError:
            failed += 1
        except TelegramAPIError:
            failed += 1
        await asyncio.sleep(0.05)          # ~20 msg/s keeps us under Telegram's broadcast limits
        if i % 100 == 0:
            await safe_edit(status, f"📣 {i}/{len(ids)} processed…")
    await safe_edit(status, f"📣 Broadcast done. Sent: {sent}, failed/blocked: {failed}.")


# Admin-only commands kept for convenience (hidden from the public command list; always permission-checked).
@router.message(Command("ban", "unban", "grant", "revoke"))
@admin_only
async def admin_quick_commands(message: Message, session: AsyncSession, db_user: User, **_):
    parts = (message.text or "").split()
    cmd = parts[0].lstrip("/").split("@")[0]
    if len(parts) < 2 or not parts[1].lstrip("-").isdigit():
        await message.answer(f"Usage: /{cmd} &lt;telegram_id&gt;" + (" &lt;days&gt;" if cmd == "grant" else "")); return
    u = (await session.execute(select(User).where(User.telegram_id == int(parts[1])))).scalar_one_or_none()
    if not u: await message.answer("User not found."); return
    if cmd == "ban": u.status = "banned"
    elif cmd == "unban": u.status = "active"
    elif cmd == "revoke": u.access_granted = False
    elif cmd == "grant":
        days = parse_int(parts[2], None) if len(parts) > 2 else None
        if days is None:
            u.access_granted = True
        else:
            await activate_subscription(session, u, await get_setting(session, "plan_name", "Exam Yatra Premium"), days, message.from_user.id, "admin command")
    await audit(session, message.from_user.id, f"cmd.{cmd}", str(u.telegram_id))
    await show_user_admin(message, session, u, edit=False)


# ============================ Infrastructure ============================
class DBMiddleware:
    """One session per update, committed after the handler, rolled back on error. Injects db_user."""
    async def __call__(self, handler, event, data):
        tg_user = getattr(event, "from_user", None)
        if not tg_user or tg_user.is_bot:
            return await handler(event, data)
        async with Session() as session:
            user = await get_user(session, tg_user)
            await session.commit()
            data["session"] = session
            data["db_user"] = user
            try:
                result = await handler(event, data)
                await session.commit()
                return result
            except Exception:
                await session.rollback()
                raise


async def on_error(event, bot: Bot):
    exc = event.exception
    log.error("Unhandled update error: %r", exc, exc_info=(type(exc), exc, exc.__traceback__))
    try:
        if event.update.callback_query:
            await event.update.callback_query.answer("Something went wrong. Please try again.", show_alert=True)
        elif event.update.message:
            await event.update.message.answer("⚠️ Something went wrong. Please try again or send /home.")
    except Exception:
        pass
    return True


async def seed_default_exams():
    async with Session() as session:
        for name in ["SSC", "Railway", "Banking", "Bihar Police", "BPSC", "UPSC", "Teaching Exams"]:
            if not (await session.execute(select(Exam).where(func.lower(Exam.name) == name.lower()))).scalar_one_or_none():
                session.add(Exam(name=name))
        await session.commit()


async def expiry_loop(bot: Bot, stop: asyncio.Event):
    """Every 30 s: auto-submit timed tests past their deadline and notify the student."""
    while not stop.is_set():
        try:
            async with Session() as session:
                tests = list((await session.execute(select(AiTest).where(AiTest.status == "in_progress", AiTest.deadline_at.is_not(None), AiTest.deadline_at <= now_utc()))).scalars())
                for t in tests:
                    await finalize_test(session, t, await load_test_questions(session, t), status="expired")
                    await session.commit()
                    try:
                        await show_result(bot, session, t, note="⏰ Time is over — the test was submitted automatically.")
                    except TelegramAPIError as e:
                        log.warning("Could not deliver expiry result for test %s: %r", t.id, e)
        except Exception:
            log.exception("Expiry task failed")
        try:
            await asyncio.wait_for(stop.wait(), timeout=30)
        except asyncio.TimeoutError:
            pass


PUBLIC_COMMANDS = [
    BotCommand(command="start", description="Start Exam Yatra"), BotCommand(command="home", description="Main menu"),
    BotCommand(command="help", description="Help and support"), BotCommand(command="stop", description="Leave the current test"),
    BotCommand(command="cancel", description="Cancel the current input"),
]
ADMIN_COMMANDS = PUBLIC_COMMANDS + [BotCommand(command="admin", description="Admin panel"), BotCommand(command="myid", description="Show my Telegram ID")]


async def register_commands(bot: Bot) -> None:
    await bot.set_my_commands(PUBLIC_COMMANDS, scope=BotCommandScopeDefault())
    for admin_id in ADMIN_IDS:
        try:
            await bot.set_my_commands(ADMIN_COMMANDS, scope=BotCommandScopeChat(chat_id=admin_id))
        except TelegramAPIError as e:      # admin has not started the bot yet — harmless
            log.info("Admin command scope for %s skipped: %s", admin_id, e)


def validate_startup_config() -> None:
    problems = []
    if not BOT_TOKEN or ":" not in BOT_TOKEN:
        problems.append("BOT_TOKEN is missing or malformed (get it from @BotFather).")
    if not ADMIN_IDS:
        problems.append("ADMIN_IDS is empty — the admin panel and payment approvals will be unavailable.")
    if DATABASE_URL.startswith("sqlite") and os.getenv("RENDER"):
        log.warning("SQLite on Render: the disk is ephemeral unless a persistent disk is attached. Use PostgreSQL for production data.")
    if not ENV_GEMINI_API_KEY:
        log.warning("GEMINI_API_KEY not set — AI features stay disabled until a key is added from Admin Panel → API Key.")
    if problems:
        for p in problems: log.error("CONFIG: %s", p)
        if any("BOT_TOKEN" in p for p in problems):
            raise SystemExit("Fatal configuration error — see log above.")


async def main():
    validate_startup_config()
    log.info("Database: %s", re.sub(r"://[^@/]+@", "://***@", DATABASE_URL))
    try:
        await ensure_schema()
    except Exception as e:
        raise SystemExit(f"Database initialisation failed: {type(e).__name__}: {e}")
    await seed_default_exams()
    dp.message.middleware(DBMiddleware())
    dp.callback_query.middleware(DBMiddleware())
    dp.errors.register(on_error)
    bot = Bot(BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    stop = asyncio.Event()
    expiry_task = asyncio.create_task(expiry_loop(bot, stop))

    async def health(_request):
        return web.json_response({"status": "ok", "service": "ExamYatra", "time": now_utc().isoformat()})
    app = web.Application(); app.router.add_get("/", health); app.router.add_get("/health", health)
    runner = web.AppRunner(app); await runner.setup()
    port = int(os.getenv("PORT", "10000"))
    await web.TCPSite(runner, host="0.0.0.0", port=port).start()
    log.info("Health server listening on 0.0.0.0:%s", port)
    try:
        me = await bot.get_me()
        await register_commands(bot)
        log.info("Exam Yatra started as @%s (model %s, admins %s)", me.username, GEMINI_MODEL, sorted(ADMIN_IDS))
        # drop_pending_updates avoids replaying a backlog after a redeploy; a second instance with the same token
        # would raise TelegramConflictError — run exactly one instance.
        await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types(), close_bot_session=True, drop_pending_updates=False)
    except TelegramUnauthorizedError:
        log.error("Telegram rejected BOT_TOKEN. Check the token from @BotFather."); raise
    finally:
        stop.set(); expiry_task.cancel()
        try: await expiry_task
        except (asyncio.CancelledError, Exception): pass
        await runner.cleanup()
        await engine.dispose()


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        log.info("Bot stopped.")
