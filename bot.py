"""
ExamYatra — single-file Telegram study bot.
Run: python bot.py

Environment:
  BOT_TOKEN (required)
  ADMIN_IDS=123456,789012
  DATABASE_URL=sqlite+aiosqlite:///./examyatra.db
  GEMINI_API_KEY=... (optional; enables AI tutor and image-question solving)
  GEMINI_MODEL=gemini-2.5-flash
  MAINTENANCE_MODE=false
  MAINTENANCE_MESSAGE=ExamYatra is being updated. Please try again soon.
  SUPPORT_CONTACT=@your_support
  FREE_AI_DAILY_LIMIT=10
"""
from __future__ import annotations

import asyncio
import html
import json
import logging
import os
import random
import re
import time
from datetime import datetime, timedelta, timezone
from typing import Any

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
    UniqueConstraint, select, func, delete, update
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

def esc(value: Any) -> str:
    return html.escape(str(value or ""))

def is_admin_id(tg_id: int) -> bool:
    return tg_id in ADMIN_IDS

def main_keyboard(is_admin: bool = False) -> ReplyKeyboardMarkup:
    rows = [
        [KeyboardButton(text="🎯 Select Exam"), KeyboardButton(text="❓ Daily Quiz")],
        [KeyboardButton(text="🧠 Ask AI Tutor"), KeyboardButton(text="📷 Solve Image")],
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


async def ai_generate(prompt: str, image_bytes: bytes | None = None, mime_type: str = "image/jpeg",
                      api_key: str | None = None) -> str:
    api_key = (api_key or GEMINI_API_KEY).strip()
    if not api_key:
        return ("AI features are not configured yet. Ask the admin to open Admin Panel → Gemini API key "
                "and add a valid key. The other bot features can still work.")
    parts: list[dict[str, Any]] = [{"text": prompt}]
    if image_bytes:
        import base64
        parts.append({"inline_data": {"mime_type": mime_type, "data": base64.b64encode(image_bytes).decode("ascii")}})
    url = f"https://generativelanguage.googleapis.com/v1beta/models/{GEMINI_MODEL}:generateContent"
    payload = {
        "contents": [{"role": "user", "parts": parts}],
        "generationConfig": {"temperature": 0.25, "maxOutputTokens": 1800},
        "systemInstruction": {"parts": [{"text":
            "You are ExamYatra, a careful and encouraging tutor for competitive-exam students in India. "
            "Read the question carefully, explain step by step in simple language, state assumptions, "
            "show formulas/calculations when useful, and finish with the final answer. If an image is unclear, "
            "say what cannot be read rather than guessing. Reply in the language used by the student when possible."
        }]}
    }
    async with httpx.AsyncClient(timeout=httpx.Timeout(55.0)) as client:
        response = await client.post(url, params={"key": api_key}, json=payload)
        if response.status_code >= 400:
            log.warning("Gemini API returned %s: %s", response.status_code, response.text[:500])
            if response.status_code in (401, 403):
                return "AI service authentication failed. Please ask the admin to check GEMINI_API_KEY."
            if response.status_code == 429:
                return "The AI service is busy or its quota is exhausted. Please try again later."
            return "AI service error. Please try again later."
        data = response.json()
    try:
        return "\n".join(p.get("text", "") for p in data["candidates"][0]["content"]["parts"] if p.get("text")).strip() or "I couldn't generate an answer. Please try again."
    except (KeyError, IndexError, TypeError):
        return "I couldn't read the AI response. Please try again."

async def check_ai_limit(message: Message, user: User) -> bool:
    if user.is_admin:
        return True
    if user.ai_count >= FREE_AI_DAILY_LIMIT:
        await message.answer(f"Daily AI limit reached ({FREE_AI_DAILY_LIMIT} requests). Try again tomorrow.")
        return False
    user.ai_count += 1
    return True

async def answer_long(message: Message, text: str) -> None:
    text = text or "No response."
    # Telegram message limit is 4096 characters. Keep a safety margin.
    for i in range(0, len(text), 3900):
        await message.answer(text[i:i+3900], parse_mode=None)

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
async def start(message: Message, session: AsyncSession, db_user: User):
    if not await gate(message, db_user, session): return
    await message.answer(
        f"👋 Welcome to <b>ExamYatra</b>, {esc(db_user.full_name)}!\n"
        "Prepare • Practice • Progress\n\n"
        "Choose a tool below. You can also send a question photo or type a doubt directly.",
        reply_markup=main_keyboard(db_user.is_admin),
    )
    if not db_user.selected_exam_id:
        await show_exams(message, session)

@router.message(Command("menu"))
async def menu(message: Message, db_user: User):
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
        "• Mock Tests: take timed tests created by the admin.\n"
        "• Study Materials: open shared notes and resources.\n"
        "• Performance: view your practice accuracy.\n"
        "Commands: /start, /menu, /help, /profile" + support
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
    await cb.message.edit_text(f"✅ Your selected exam is <b>{esc(exam.name)}</b>.\nNow try Daily Quiz or Mock Tests.")

@router.message(F.text == "❓ Daily Quiz")
async def quiz_menu(message: Message, session: AsyncSession, db_user: User):
    if (await get_setting(session, "feature_quiz", "true")).lower() != "true":
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
    try: await cb.message.edit_text(text, reply_markup=inline([[("➡️ Next question", "quiz:next")]]))
    except TelegramBadRequest: await cb.message.answer(text, reply_markup=inline([[("➡️ Next question", "quiz:next")]]))

@router.callback_query(F.data == "quiz:next")
async def quiz_next(cb: CallbackQuery, session: AsyncSession, db_user: User):
    await cb.answer()
    await send_quiz(cb.message, session, db_user)

@router.message(F.text == "🧠 Ask AI Tutor")
async def ai_tutor_start(message: Message, state: FSMContext, session: AsyncSession):
    if (await get_setting(session, "feature_ai", "true")).lower() != "true":
        await message.answer("AI tools are temporarily disabled by the administrator."); return
    await state.set_state("ai_tutor")
    await message.answer("🧠 Send your question as text. I'll explain it step by step. Send /cancel to stop.")

@router.message(F.text == "📷 Solve Image")
async def image_help(message: Message, session: AsyncSession):
    if (await get_setting(session, "feature_ai", "true")).lower() != "true":
        await message.answer("AI tools are temporarily disabled by the administrator."); return
    await message.answer("📷 Send a clear photo/screenshot of the question here. I'll read it and explain the solution step by step. You can also add a caption such as 'solve in Hindi'.")

@router.message(F.photo)
async def photo_question(message: Message, bot: Bot, session: AsyncSession, db_user: User):
    if not await gate(message, db_user, session): return
    if (await get_setting(session, "feature_ai", "true")).lower() != "true":
        await message.answer("AI tools are temporarily disabled by the administrator."); return
    if not await check_ai_limit(message, db_user): return
    photo = message.photo[-1]
    file = await bot.get_file(photo.file_id)
    if file.file_size and file.file_size > MAX_IMAGE_BYTES:
        await message.answer("This image is too large. Please send a compressed image under 8 MB.")
        return
    stream = await bot.download_file(file.file_path)
    image_bytes = stream.read()
    mime = "image/jpeg"
    caption = message.caption or ""
    prompt = (
        "Analyze the attached student question image. First transcribe the visible question and choices (if any), "
        "then solve it carefully step by step, explain the concept in beginner-friendly language, and state the final answer. "
        "For MCQs, identify the correct option and explain why the others are not correct if possible. "
        f"Student instructions: {caption or 'No extra instructions; answer in the language most suitable for the student.'}"
    )
    await message.answer("🔎 Reading the image and solving the question…")
    result = await ai_generate(prompt, image_bytes, mime, api_key=await current_api_key(session))
    await answer_long(message, result)

@router.message(F.document)
async def document_question(message: Message, bot: Bot, session: AsyncSession, db_user: User):
    if (await get_setting(session, "feature_ai", "true")).lower() != "true":
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
    result = await ai_generate("Read and solve this exam question image step by step. Transcribe it first, explain simply, and clearly state the final answer.", stream.read(), doc.mime_type or "image/jpeg", api_key=await current_api_key(session))
    await answer_long(message, result)

@router.message(F.text == "/cancel")
@router.message(Command("cancel"))
async def cancel(message: Message, state: FSMContext):
    await state.clear()
    await message.answer("Cancelled.", reply_markup=main_keyboard(is_admin_id(message.from_user.id)))

@router.message(F.text, StateFilter(None), ~F.text.startswith("/"))
async def text_router(message: Message, session: AsyncSession, db_user: User, state: FSMContext):
    text = (message.text or "").strip()
    if not text or text.startswith("/"): return
    if not await gate(message, db_user, session): return
    current = await state.get_state()
    if current == "ai_tutor" or current is not None:
        if (await get_setting(session, "feature_ai", "true")).lower() != "true":
            await state.clear()
            await message.answer("AI tools are temporarily disabled by the administrator."); return
        if not await check_ai_limit(message, db_user): return
        await state.clear()
        await message.answer("🧠 Thinking…")
        result = await ai_generate(
            "Answer this student's study question. Explain the reasoning step by step, use simple language, "
            "show formulas/examples when useful, and give a concise final answer.\n\nQuestion:\n" + text,
            api_key=await current_api_key(session)
        )
        await answer_long(message, result)
        return
    if text == "📝 Mock Tests":
        if (await get_setting(session, "feature_mock", "true")).lower() != "true":
            await message.answer("Mock Tests are temporarily disabled by the administrator."); return
        await list_mock_tests(message, session, db_user); return
    if text == "📚 Study Materials":
        if (await get_setting(session, "feature_materials", "true")).lower() != "true":
            await message.answer("Study Materials are temporarily disabled by the administrator."); return
        await list_materials(message, session, db_user); return
    if text == "📊 My Performance":
        await performance(message, session, db_user); return
    if text == "🏆 Leaderboard":
        await leaderboard(message, session); return
    if text in ("👤 My Profile", "/profile"):
        await profile(message, session, db_user); return
    if text == "⚙️ Settings":
        await message.answer("⚙️ Settings\nUse /language en or /language hi to set your preferred language.\nUse /delete_me to delete your account data.")
        return
    # Any normal text is treated as a study doubt, so a student can simply type a question.
    if (await get_setting(session, "feature_ai", "true")).lower() != "true":
        await message.answer("AI tools are temporarily disabled by the administrator."); return
    if not await check_ai_limit(message, db_user): return
    await message.answer("🧠 I'll treat that as a study question…")
    result = await ai_generate("Answer this student's question clearly and step by step:\n\n" + text,
                                api_key=await current_api_key(session))
    await answer_long(message, result)

async def list_mock_tests(message: Message, session: AsyncSession, user: User):
    if not user.selected_exam_id:
        await message.answer("Select your exam first."); await show_exams(message, session); return
    tests = list((await session.execute(select(MockTest).where(
        MockTest.exam_id == user.selected_exam_id, MockTest.published.is_(True)
    ).order_by(MockTest.id.desc()))).scalars())
    if not tests:
        await message.answer("No mock tests have been published for your exam yet."); return
    await message.answer("📝 Choose a mock test:", reply_markup=inline([
        [(f"{t.title} · {t.duration} min", f"mockinfo:{t.id}") for t in tests[i:i+1]]
        for i in range(len(tests))
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
    await cb.message.edit_text(
        f"📝 <b>{esc(test.title)}</b>\nQuestions: {count}\nTime limit: {test.duration} minutes\n"
        "The timer starts when you press Start.",
        reply_markup=inline([[("▶️ Start test", f"mockstart:{tid}")]])
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
    await message.answer(
        f"📝 <b>{esc((await session.get(MockTest, attempt.test_id)).title)}</b>\n"
        f"Question {index+1}/{len(qids)} · {max(0,int((attempt.deadline_at-now_utc()).total_seconds()//60))} min left\n\n"
        f"{esc(q.text)}\n\n" + "\n".join(lines) +
        (f"\n\nSelected: {esc(answers.get(str(q.id), 'Not answered'))}" if str(q.id) in answers else ""),
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
    await message.answer(
        f"🏁 <b>Mock test result: {esc(test.title)}</b>\n\n"
        f"Score: <b>{correct}/{len(qids)}</b>\n✅ Correct: {correct}\n❌ Incorrect: {incorrect}\n"
        f"⏭ Unanswered: {a.unanswered}\nAccuracy: {correct/(correct+incorrect)*100:.1f}%" if correct+incorrect else
        f"🏁 <b>Mock test result: {esc(test.title)}</b>\n\nScore: {correct}/{len(qids)}\nNo answers attempted."
    )

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
    await message.answer(f"📊 <b>Your Performance</b>\nQuestions answered: {total}\nCorrect: {correct}\nAccuracy: {accuracy}\nMock tests completed: {mocks}")

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
    await message.answer(
        f"👤 <b>My Profile</b>\nName: {esc(user.full_name)}\nTelegram ID: <code>{user.telegram_id}</code>\n"
        f"Exam: {esc(exam.name if exam else 'Not selected')}\nJoined: {user.joined_at:%d %b %Y}\n"
        f"Account: {esc(user.status)}\nAI requests today: {user.ai_count}/{FREE_AI_DAILY_LIMIT if not user.is_admin else 'unlimited'}"
    )

@router.message(Command("profile"))
async def profile_command(message: Message, session: AsyncSession, db_user: User):
    await profile(message, session, db_user)

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
async def delete_callback(cb: CallbackQuery, session: AsyncSession, db_user: User):
    if cb.data == "delete:cancel":
        await cb.answer("Cancelled"); await cb.message.edit_text("Data deletion cancelled."); return
    await session.execute(delete(User).where(User.id == db_user.id))
    await session.flush()
    await cb.answer("Deleted")
    await cb.message.edit_text("Your profile and activity have been deleted. Send /start to register again.")

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
        await cb.message.answer(f"📊 Stats\nUsers: {users}\nActive: {active}\nQuestions: {qs}\nActive exams: {exams}")
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
            "/feature materials on|off\n/maintenance on|off\n"
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
        keys = ["ai", "quiz", "mock", "materials"]
        status = "\n".join(f"{k}: {await get_setting(session, 'feature_'+k, 'true')}" for k in keys)
        await cb.message.answer("⚙️ Feature switches:\n" + status + "\nUse /feature NAME on|off.")
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
    await message.answer("✅ Gemini API key validated and saved. AI tutor and image-question solving are ready.")

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
        try: await bot.send_message(u.telegram_id, text); sent += 1
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
    if len(parts)!=3 or parts[1].lower() not in ("ai","quiz","mock","materials") or parts[2].lower() not in ("on","off"):
        await message.answer("Usage: /feature ai|quiz|mock|materials on|off"); return
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
    async with engine.begin() as conn:
        await conn.run_sync(Base.metadata.create_all)
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
