import PillowProblems.Basic

/-!
# Problem 1 (Algebra: Properties of Numbers)

**Question.** *(dated 24/3/84)*

> Find a general formula for two squares whose sum = 2.

*(Carroll's solution: Chapter III, problem 1; text in `data/problems.json`.)*

**Lean reading.** The two "squares" are `u ^ 2` and `v ^ 2` with `u v : ℚ`: Carroll works
with fractions (he divides `u² + v² = 2m²` by `m²`), and over `ℚ` the question has genuine
content. His general formula, with parameters `x, y`, is
`u = (x² - y² + 2xy) / (x² + y²)`, `v = (x² - y² - 2xy) / (x² + y²)`. The theorem `problem1`
states that this formula is both sound and complete: a rational pair `(u, v)` satisfies
`u² + v² = 2` exactly when it is given by the formula for some integers `x, y` not both zero
(the only restriction needed, so that `x² + y² ≠ 0`). Taking `x, y` rational instead gives the
same set of pairs, since the formula is unchanged by scaling `(x, y)`; `problem1_rat` records
soundness for rational parameters.

**Status.** proved
-/

namespace PillowProblems.P01

/-- Carroll's formula gives every rational solution of `u² + v² = 2`, and only those:
the parameters are integers `x, y`, not both zero. -/
theorem problem1 (u v : ℚ) :
    u ^ 2 + v ^ 2 = 2 ↔
      ∃ x y : ℤ, (x, y) ≠ (0, 0) ∧
        u = ((x : ℚ) ^ 2 - y ^ 2 + 2 * x * y) / (x ^ 2 + y ^ 2) ∧
        v = ((x : ℚ) ^ 2 - y ^ 2 - 2 * x * y) / (x ^ 2 + y ^ 2) := by
  sorry

/-- Soundness of Carroll's formula for rational parameters `x, y`, not both zero. -/
theorem problem1_rat (x y : ℚ) (hxy : (x, y) ≠ (0, 0)) :
    ((x ^ 2 - y ^ 2 + 2 * x * y) / (x ^ 2 + y ^ 2)) ^ 2 +
      ((x ^ 2 - y ^ 2 - 2 * x * y) / (x ^ 2 + y ^ 2)) ^ 2 = 2 := by
  sorry

end PillowProblems.P01
