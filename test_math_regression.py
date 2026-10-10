"""
Regression tests for the two reference problems in the Exam Yatra master prompt.
Pure standard library — run with:  python -m pytest tests/  or  python tests/test_math_regression.py

These tests verify the *reference values* deterministically. They do NOT call Gemini. Wire them
into the answer-validation path by comparing the numeric value the model returns (parsed from the
'answer' field) against `integral_reference()` with a 1e-3 tolerance.
"""
import math
import unittest


def catalan(terms: int = 2_000_000) -> float:
    return sum((-1) ** k / (2 * k + 1) ** 2 for k in range(terms))


def integral_reference() -> float:
    """I = pi^2/16 + G/2 - pi*ln(2)/8"""
    return math.pi ** 2 / 16 + catalan() / 2 - math.pi * math.log(2) / 8


def integral_numeric(n: int = 200_000) -> float:
    """Composite Simpson's rule for ∫_0^{π/2} x sin x / (sin x + cos x) dx."""
    a, b = 0.0, math.pi / 2
    h = (b - a) / n
    f = lambda x: x * math.sin(x) / (math.sin(x) + math.cos(x))
    s = f(a) + f(b)
    for i in range(1, n):
        s += f(a + i * h) * (4 if i % 2 else 2)
    return s * h / 3


class MathRegression(unittest.TestCase):
    def test_definite_integral_closed_form_matches_numeric(self):
        ref, num = integral_reference(), integral_numeric()
        self.assertAlmostEqual(ref, 0.8026348, places=6)
        self.assertAlmostEqual(ref, num, places=6)

    def test_capacitor_with_battery_connected(self):
        C, V, K = 4e-6, 12.0, 3
        C2 = K * C                     # battery stays connected → V fixed, C scales by K
        Q2 = C2 * V
        self.assertAlmostEqual(C2 * 1e6, 12.0, places=9)   # 12 μF
        self.assertAlmostEqual(Q2 * 1e6, 144.0, places=9)  # 144 μC


if __name__ == "__main__":
    unittest.main()
