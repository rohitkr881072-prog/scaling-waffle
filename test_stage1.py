"""Stage 1 tests: pure functions are extracted from bot.py with ast (aiogram/SQLAlchemy are not importable offline)."""
import ast, html, re, os, unittest
from typing import Any
SRC = open(os.path.join(os.path.dirname(__file__), "..", "bot.py"), encoding="utf-8").read()
WANT = {"_norm_math", "_clean_items", "render_structured_answer", "clean_plain", "esc", "_pdf_safe", "_pdf_latin", "_pdf_wrap_long"}
ns = {"re": re, "html": html, "Any": Any, "STYLE_SHORT": "short", "STYLE_DETAILED": "detailed"}
tree = ast.parse(SRC)
for node in tree.body:
    if isinstance(node, ast.FunctionDef) and node.name in WANT:
        exec(compile(ast.Module([node], []), "bot.py", "exec"), ns)
    if isinstance(node, ast.Assign) and any(getattr(t, "id", "") == "_LATIN_MAP" for t in node.targets):
        exec(compile(ast.Module([node], []), "bot.py", "exec"), ns)
R = ns["render_structured_answer"]; plain = lambda t: html.unescape(re.sub(r"<[^>]+>", "", t))


class T(unittest.TestCase):
    def test_geometry_en_hi(self):
        for lang in ("en", "hi"):
            d = {"kind": "math", "steps": ["(x−1)² + (y−2)² = (x−7)² + y²", "12x − 4y − 44 = 0", "3x − y − 11 = 0"], "answer": "3x − y − 11 = 0"}
            out = plain(R(d, "detailed", lang))
            self.assertIn("3x − y − 11 = 0", out); self.assertNotIn("3x + y", out); self.assertNotIn("⚠️", out)

    def test_mismatch_flagged(self):          # the screenshot bug: derivation says minus, final says plus
        d = {"kind": "math", "steps": ["12x − 4y − 44 = 0", "3x − y − 11 = 0"], "answer": "3x + y − 11 = 0"}
        self.assertIn("please verify", plain(R(d, "detailed", "en")))

    def test_integral(self):
        a = "I = π²/16 + G/2 − (π ln 2)/8"
        d = {"kind": "math", "steps": ["I = ∫₀^{π/2} x sin x/(sin x + cos x) dx", a], "answer": a}
        out = plain(R(d, "detailed", "en")); self.assertIn("ln 2", out); self.assertNotIn("⚠️", out)

    def test_capacitor(self):
        d = {"kind": "math", "steps": ["C' = K·C = 3 × 4 μF = 12 μF", "Q' = C'V = 12 μF × 12 V = 144 μC"], "answer": "C' = 12 μF, Q' = 144 μC"}
        out = plain(R(d, "detailed", "en")); self.assertIn("12 μF", out); self.assertIn("144 μC", out)

    def test_math_is_clean(self):
        d = {"kind": "math", "steps": ["a = 1", "b = 2", "c = 3"], "answer": "c = 3"}
        out = R(d, "detailed", "en"); self.assertNotIn("Step-by-step", out); self.assertNotIn("Concept", out)
        self.assertTrue(out.rstrip().endswith("c = 3"))

    def test_short_concise(self):
        out = plain(R({"answer": "B) 144 μC", "steps": ["x"] * 9}, "short", "en")); self.assertEqual(out.strip(), "✅ B) 144 μC")

    def test_theory_no_template(self):
        out = plain(R({"kind": "theory", "answer": "Photosynthesis makes glucose.", "explanation": "Plants use light, CO2 and water."}, "detailed", "en"))
        self.assertNotIn("Step", out); self.assertNotIn("Concept", out)

    def test_vocab_20(self):
        words = [("Apple", "सेब"), ("Ball", "गेंद"), ("Cat", "बिल्ली"), ("Dog", "कुत्ता")] + [(f"W{i}", f"श{i}") for i in range(16)]
        items = [f"{i+1}. {e} : {h}" for i, (e, h) in enumerate(words)] + ["apple : सेब"]      # numbering + duplicate must be cleaned
        out = plain(R({"kind": "list", "answer": "", "items": items}, "detailed", "hi")).strip().split("\n")
        self.assertEqual(len(out), 20); self.assertEqual(out[0], "1. Apple : सेब"); self.assertEqual(out[3], "4. Dog : कुत्ता")
        self.assertNotIn("Step", "\n".join(out))

    def test_unicode_and_markup(self):
        out = R({"kind": "math", "steps": ["x₁² + y₂³ = 5 × 3 − 2 <b>"], "answer": "5 × 3 − 2"}, "detailed", "en")
        self.assertIn("x₁² + y₂³", out); self.assertIn("&lt;b&gt;", out)       # tags escaped, symbols intact

    def test_pdf_helpers(self):
        t = ns["_pdf_latin"]("Report — ✔ ✘ हिन्दी ₹5")
        t.encode("latin-1")                                                     # must never raise
        self.assertNotIn("—", t)
        self.assertLessEqual(max(len(w) for w in ns["_pdf_wrap_long"]("x" * 300).split()), 60)

if __name__ == "__main__":
    unittest.main(verbosity=2)
