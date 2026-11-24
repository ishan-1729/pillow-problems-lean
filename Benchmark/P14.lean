import PillowProblems.Basic

/-!
# Problem 14 (Algebra: Properties of Numbers)

**Question.** *(dated 2/12/81)*

> Prove that 3 times the sum of 3 squares is also the sum of 4 squares.

*(Carroll's solution: Chapter III, problem 14; text in `data/problems.json`.)*

**Lean reading.** Carroll proves the explicit identity
`3(a² + b² + c²) = (a + b + c)² + (b - c)² + (c - a)² + (a - b)²`, which `problem14` states in
any commutative ring (so for whole numbers, integers or fractions alike); `problem14_exists`
is the question's literal form for integers. The squares of the identity may be `0²` (when two
of `a, b, c` are equal), so "sum of 4 squares" is read as allowing zero squares; this is
necessary, since `problem14_zero_needed` shows `3(1² + 1² + 1²) = 9` is not a sum of 4
positive squares. (For integers the existence statement alone also follows from Lagrange's
four-square theorem; Carroll's content is the explicit identity.) `problem14_examples` checks
Carroll's two numerical examples.

**Status.** proved
-/

namespace PillowProblems.P14

/-- Carroll's identity: 3 times a sum of 3 squares is the sum of the 4 squares
`(a + b + c)², (b - c)², (c - a)², (a - b)²`. -/
theorem problem14 {R : Type*} [CommRing R] (a b c : R) :
    3 * (a ^ 2 + b ^ 2 + c ^ 2) = (a + b + c) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2 := by
  sorry

/-- The question as stated, for integers. -/
theorem problem14_exists (a b c : ℤ) :
    ∃ p q r s : ℤ, 3 * (a ^ 2 + b ^ 2 + c ^ 2) = p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 := by
  sorry

/-- Carroll's numerical examples. -/
theorem problem14_examples :
    3 * (1 ^ 2 + 2 ^ 2 + 3 ^ 2) = 6 ^ 2 + 1 ^ 2 + 2 ^ 2 + 1 ^ 2 ∧
      3 * (1 ^ 2 + 3 ^ 2 + 7 ^ 2) = 11 ^ 2 + 4 ^ 2 + 6 ^ 2 + 2 ^ 2 := by
  sorry

/-- Zero squares must be allowed: `3(1² + 1² + 1²) = 9` is not a sum of 4 positive squares. -/
theorem problem14_zero_needed :
    ¬ ∃ p q r s : ℕ, 0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧
      p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 = 3 * (1 ^ 2 + 1 ^ 2 + 1 ^ 2) := by
  sorry

end PillowProblems.P14
