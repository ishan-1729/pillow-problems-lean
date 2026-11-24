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
  constructor
  · intro h
    by_cases ha : u + v = -2
    · -- the point `(-1, -1)`, reached by `x = 0, y = 1`
      have hu : u = -1 := by nlinarith [sq_nonneg (u - v)]
      have hv : v = -1 := by linarith
      refine ⟨0, 1, by simp, ?_, ?_⟩ <;> simp [hu, hv]
    · set p : ℚ := 1 + (u + v) / 2 with hp
      set q : ℚ := (u - v) / 2 with hq
      have hp0 : p ≠ 0 := by
        intro h0; apply ha; linarith
      set D : ℚ := (p.den : ℚ) * q.den with hD
      have hD0 : D ≠ 0 := by positivity
      refine ⟨p.num * q.den, q.num * p.den, ?_, ?_, ?_⟩
      · intro h0
        simp only [Prod.mk.injEq, mul_eq_zero, Rat.num_eq_zero, Nat.cast_eq_zero,
          Rat.den_ne_zero, or_false] at h0
        exact hp0 h0.1
      all_goals
        have hx : ((p.num * q.den : ℤ) : ℚ) = p * D := by
          push_cast; rw [← Rat.mul_den_eq_num]; ring
        have hy : ((q.num * p.den : ℤ) : ℚ) = q * D := by
          push_cast; rw [← Rat.mul_den_eq_num]; ring
        have hpq : (p * D) ^ 2 + (q * D) ^ 2 ≠ 0 := by
          have : 0 < (p * D) ^ 2 := by positivity
          positivity
        rw [hx, hy, eq_div_iff hpq, hp, hq]
      · linear_combination (D ^ 2 * (u + 1) / 2) * h
      · linear_combination (D ^ 2 * (v + 1) / 2) * h
  · rintro ⟨x, y, hxy, rfl, rfl⟩
    have hne : (x : ℚ) ^ 2 + (y : ℚ) ^ 2 ≠ 0 := by
      intro h0
      have hx : (x : ℚ) = 0 := by nlinarith [sq_nonneg (x : ℚ), sq_nonneg (y : ℚ)]
      have hy : (y : ℚ) = 0 := by nlinarith [sq_nonneg (x : ℚ), sq_nonneg (y : ℚ)]
      exact hxy (by simp_all)
    field_simp
    ring

/-- Soundness of Carroll's formula for rational parameters `x, y`, not both zero. -/
theorem problem1_rat (x y : ℚ) (hxy : (x, y) ≠ (0, 0)) :
    ((x ^ 2 - y ^ 2 + 2 * x * y) / (x ^ 2 + y ^ 2)) ^ 2 +
      ((x ^ 2 - y ^ 2 - 2 * x * y) / (x ^ 2 + y ^ 2)) ^ 2 = 2 := by
  have hne : x ^ 2 + y ^ 2 ≠ 0 := by
    intro h0
    have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    exact hxy (by simp [hx, hy])
  field_simp
  ring

end PillowProblems.P01
