import PillowProblems.Basic

/-!
# Problem 44 (Algebra: Properties of Numbers)

**Question.** *(dated 18/3/81)*

> If \(a\), \(b\) be two numbers prime to each other, a value may be found for \(n\) which will make \((a^{n} - 1)\) a multiple of \(b\).

*(Carroll's solution: Chapter III, problem 44; text in `data/problems.json`.)*

**Lean reading.** `a, b` are integers (this includes Carroll's whole numbers) with
`IsCoprime a b`, and the claim is that some *positive* exponent `n` makes `b ∣ aⁿ - 1`
(`n = 0` would make the statement trivial, so positivity is required). Carroll's proof via
circulating decimals in radix `a` is replaced by Euler's theorem in `ZMod |b|`, with
`n = φ(|b|)`; the case `b = 0` (where `a = ±1`) is handled with `n = 2`.
`problem44_examples` checks Carroll's three examples, together with the fact that each of his
values of `n` (the period of `1/b` in radix `a`) is the least one.

**Status.** proved
-/

namespace PillowProblems.P44

/-- If `a, b` are coprime, some positive power of `a` is `≡ 1 (mod b)`. -/
theorem problem44 (a b : ℤ) (h : IsCoprime a b) : ∃ n : ℕ, 0 < n ∧ b ∣ a ^ n - 1 := by
  sorry

/-- Carroll's examples: `10⁶ - 1` is a multiple of 7, `8² - 1` of 9, `7¹² - 1` of 13, and in each
case no smaller positive exponent works. -/
theorem problem44_examples :
    (7 ∣ 10 ^ 6 - 1 ∧ ∀ n < 6, 0 < n → ¬ 7 ∣ 10 ^ n - 1) ∧
      (9 ∣ 8 ^ 2 - 1 ∧ ∀ n < 2, 0 < n → ¬ 9 ∣ 8 ^ n - 1) ∧
      (13 ∣ 7 ^ 12 - 1 ∧ ∀ n < 12, 0 < n → ¬ 13 ∣ 7 ^ n - 1) := by
  sorry

end PillowProblems.P44
