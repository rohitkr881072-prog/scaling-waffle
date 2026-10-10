"""Unit tests for the pure logic in bot.py: MCQ validation, shuffled-option scoring, duplicate detection,
UPI URI, URL normalisation, entitlement derivation. Run: pytest -q
No Telegram or network access is needed; BOT_TOKEN is faked so the module imports."""
import os
import sys
from datetime import timedelta

os.environ.setdefault("BOT_TOKEN", "123:TEST")
os.environ.setdefault("DATABASE_URL", "sqlite+aiosqlite:///./test_examyatra.db")
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import bot  # noqa: E402


class FakeTQ:
    def __init__(self, options, correct_index, selected_index=None, position=0):
        self.options_json = bot.json.dumps(options)
        self.correct_index = correct_index
        self.selected_index = selected_index
        self.position = position
        self.explanation = None
        self.text = "q"

    def options(self):
        return bot.json.loads(self.options_json)


class FakeOpt:
    def __init__(self, text, correct):
        self.text, self.correct = text, correct


class FakeQ:
    def __init__(self, text, options):
        self.text = text
        self.options = options
        self.explanation = None
        self.difficulty = "medium"
        self.id = 1
        self.status = bot.Q_APPROVED
        self.published = True


# ---- TEST 4/5/6: malformed questions are rejected ----
def test_three_options_rejected():
    assert bot.validate_mcq("What is the capital of Bihar?", ["Patna", "Gaya", "Ranchi"], 0)


def test_two_correct_rejected():
    q = FakeQ("Which article provides for the Election Commission?",
              [FakeOpt("324", True), FakeOpt("326", True), FakeOpt("280", False), FakeOpt("148", False)])
    assert any("more than one" in p for p in bot.question_problems(q))
    assert not bot.is_servable(q)


def test_no_correct_rejected():
    q = FakeQ("Which article provides for the Election Commission?",
              [FakeOpt("324", False), FakeOpt("326", False), FakeOpt("280", False), FakeOpt("148", False)])
    assert bot.question_problems(q)


def test_duplicate_options_rejected():
    assert bot.validate_mcq("Some valid question text here?", ["A", "A", "B", "C"], 0)


def test_valid_question_passes():
    assert bot.validate_mcq("Which article provides for the Election Commission?", ["324", "326", "280", "148"], 0) == []


# ---- TEST 2/3: shuffled options keep the answer mapping; score derives from saved answers ----
def test_shuffled_snapshot_keeps_correct_mapping():
    q = FakeQ("Which article provides for the Election Commission?",
              [FakeOpt("Article 324", True), FakeOpt("Article 326", False), FakeOpt("Article 280", False), FakeOpt("Article 148", False)])
    for _ in range(50):
        snap = bot.shuffled_snapshot(q)
        assert snap["options"][snap["correct_index"]] == "Article 324"
        assert sorted(snap["options"]) == sorted(o.text for o in q.options)


def test_score_from_saved_answers():
    qs = [FakeTQ(["a", "b", "c", "d"], 1, selected_index=1),   # correct
          FakeTQ(["a", "b", "c", "d"], 2, selected_index=0),   # wrong
          FakeTQ(["a", "b", "c", "d"], 3, selected_index=None)]  # unanswered
    assert bot.score_from_questions(qs) == (1, 1, 1)


def test_repeated_press_does_not_double_count():
    q = FakeTQ(["a", "b", "c", "d"], 1, selected_index=1)
    before = bot.score_from_questions([q])
    q.selected_index = 1          # same selection again
    assert bot.score_from_questions([q]) == before == (1, 0, 0)


# ---- generated-question validation ----
def test_generated_question_rejected_without_explanation():
    assert bot.validate_generated_question({"question": "What is 2+2 in decimal?", "options": ["1", "2", "3", "4"], "correct_index": 3}, set()) is None


def test_generated_question_rejects_duplicate():
    seen = {bot.normalize_question_text("What is the capital of India?")}
    item = {"question": "What is the capital of India?", "options": ["Delhi", "Mumbai", "Kolkata", "Chennai"], "correct_index": 0, "explanation": "Delhi."}
    assert bot.validate_generated_question(item, seen) is None
    assert bot.validate_generated_question(item, set()) is not None


# ---- button labels never collide ----
def test_long_option_labels_flagged():
    long_a = "The Constitution of India came into force on 26 January 1950 after adoption"
    long_b = "The Constitution of India came into force on 26 January 1950 after ratification"
    assert bot.labels_ambiguous([long_a, long_b, "x", "y"])
    assert not bot.labels_ambiguous(["324", "326", "280", "148"])


# ---- payments / config helpers ----
def test_upi_uri_uses_configured_amount():
    uri = bot.build_upi_uri("examyatra@upi", "Exam Yatra", 99.0, "ExamYatra #7")
    assert uri.startswith("upi://pay?pa=examyatra%40upi") and "am=99.00" in uri and "cu=INR" in uri


def test_upi_id_validation():
    assert bot.upi_id_valid("name@okaxis") and not bot.upi_id_valid("not-a-upi") and not bot.upi_id_valid("")


def test_database_url_normalisation():
    assert bot.normalize_database_url("postgres://u:p@h/db").startswith("postgresql+asyncpg://")
    assert bot.normalize_database_url("postgresql://u:p@h/db?sslmode=require").endswith("ssl=require")
    assert bot.normalize_database_url("").startswith("sqlite+aiosqlite")


def test_question_parser_and_answer_index():
    block = "Q: Which article provides for the Election Commission?\nA: 324\nB: 326\nC: 280\nD: 148\nANS: A\nEXP: Article 324."
    data, err = bot.parse_question_block(block)
    assert err == "" and data["correct_index"] == 0 and data["options"] == ["324", "326", "280", "148"]
    bad, err = bot.parse_question_block(block.replace("ANS: A", "ANS: E"))
    assert bad is None and "correct answer" in err


# ---- entitlements: expiry derived from timestamps, nothing deleted ----
def test_trial_expiry_and_tier():
    u = bot.User(telegram_id=1, trial_status="active", trial_started_at=bot.now_utc() - timedelta(days=8),
                 trial_ends_at=bot.now_utc() - timedelta(days=1), subscription_status="none", limit_overrides="{}", is_admin=False)
    assert bot.user_tier(u) == "free" and u.trial_status == "expired" and u.trial_started_at is not None


def test_premium_tier_and_lifetime():
    u = bot.User(telegram_id=2, trial_status="expired", subscription_status="active", subscription_expiry=None, limit_overrides="{}", is_admin=False)
    assert bot.user_tier(u) == "premium"
    u.subscription_expiry = bot.now_utc() - timedelta(seconds=1)
    assert bot.user_tier(u) == "free" and u.subscription_status == "expired"


def test_overrides_take_precedence():
    u = bot.User(telegram_id=3, trial_status="none", subscription_status="none", limit_overrides='{"ai_daily": 77}', is_admin=False)
    assert u.overrides() == {"ai_daily": 77}


def test_md_to_html_escapes_and_formats():
    out = bot.md_to_html("**Bold** <script> `x`")
    assert "<b>Bold</b>" in out and "&lt;script&gt;" in out and "<code>x</code>" in out
