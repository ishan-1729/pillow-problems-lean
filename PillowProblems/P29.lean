import PillowProblems.Basic

/-!
# Problem 29 (Algebra: Properties of Numbers)

**Question.** *(dated 3/12/81)*

> Prove that the sum of 2 different squares, multiplied by the sum of 2 different squares, gives the sum of 2 squares in 2 different ways.

*(Carroll's solution: Chapter III, problem 29; text in `data/problems.json`.)*

**Lean reading.** The numbers are integers `a, b, c, d`; "2 different squares" means
`a² ≠ b²` and `c² ≠ d²`. The two ways are Carroll's `(ac + bd)² + (ad - bc)²` and
`(ac - bd)² + (ad + bc)²`, and "different" means different as unordered pairs of squares
(`Sym2`). The question is ill-posed as to whether `0²` counts as a square, and under either
uniform answer the claim is false: if `0²` is allowed throughout, `1² + 0²` is a sum of 2
different squares and `(1² + 0²)(1² + 2²) = 5` is a sum of 2 squares in only one way
(`problem29_zero_input`); if `0²` is excluded throughout, `(1² + 2²)(1² + 2²) = 25 = 3² + 4²`
in only one way (`problem29_zero_output`), the other way being `5² + 0²`. We therefore
formalize the reading Carroll's solution uses: the given squares are nonzero
(`a, b, c, d ≠ 0`; his step "it cannot = (ac - bd)" needs `bd ≠ 0`), while a square `0²` may
occur in a resulting way (he never excludes `ad = bc`). `problem29_iff` gives the exact
condition (Carroll's argument run both ways): the two ways coincide iff `abcd = 0` or
`(a² - b²)(c² - d²) = 0`.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P29

/-- The product of two sums of two different (nonzero) squares is a sum of two squares in
two different ways: Carroll's two representations are not the same pair of squares. -/
theorem problem29 (a b c d : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hab : a ^ 2 ≠ b ^ 2) (hcd : c ^ 2 ≠ d ^ 2) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 ∧
      (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 ∧
      s((a * c + b * d) ^ 2, (a * d - b * c) ^ 2) ≠ s((a * c - b * d) ^ 2, (a * d + b * c) ^ 2) := by
  refine ⟨by ring, by ring, ?_⟩
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
  · have : 4 * a * b * c * d = 0 := by linear_combination h1
    simp_all
  · have : (a ^ 2 - b ^ 2) * (c ^ 2 - d ^ 2) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 this with h | h
    · exact hab (sub_eq_zero.1 h)
    · exact hcd (sub_eq_zero.1 h)

/-- Exactly when Carroll's two ways coincide. -/
theorem problem29_iff (a b c d : ℤ) :
    s((a * c + b * d) ^ 2, (a * d - b * c) ^ 2) = s((a * c - b * d) ^ 2, (a * d + b * c) ^ 2) ↔
      a * b * c * d = 0 ∨ (a ^ 2 - b ^ 2) * (c ^ 2 - d ^ 2) = 0 := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · left
      have h4 : 4 * (a * b * c * d) = 0 := by linear_combination h1
      exact (mul_eq_zero.1 h4).resolve_left (by norm_num)
    · right; linear_combination h1
  · rintro (h | h)
    · left; constructor
      · linear_combination 4 * h
      · linear_combination -4 * h
    · right; constructor
      · linear_combination h
      · linear_combination -h

theorem problem29_nonvacuous :
    ∃ a b c d : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧ a ^ 2 ≠ b ^ 2 ∧ c ^ 2 ≠ d ^ 2 :=
  ⟨1, 2, 1, 3, by norm_num⟩

/-- If `0²` counted as one of the given squares, the claim would fail: `1² + 0²` is a sum of
2 different squares, and `(1² + 0²)(1² + 2²) = 5` is a sum of 2 squares in only one way. -/
theorem problem29_zero_input :
    ∀ p q r s : ℕ, p ^ 2 + q ^ 2 = (1 ^ 2 + 0 ^ 2) * (1 ^ 2 + 2 ^ 2) →
      r ^ 2 + s ^ 2 = (1 ^ 2 + 0 ^ 2) * (1 ^ 2 + 2 ^ 2) → s(p ^ 2, q ^ 2) = s(r ^ 2, s ^ 2) := by
  intro p q r s h1 h2
  norm_num at h1 h2
  have hp : p < 3 := by nlinarith
  have hq : q < 3 := by nlinarith
  have hr : r < 3 := by nlinarith
  have hs : s < 3 := by nlinarith
  interval_cases p <;> interval_cases q <;> interval_cases r <;> interval_cases s <;>
    simp_all [Sym2.eq_swap]

/-- If `0²` were excluded from the resulting ways too, the claim would fail:
`(1² + 2²)(1² + 2²) = 25` is a sum of 2 positive squares in only one way (`3² + 4²`). -/
theorem problem29_zero_output :
    ∀ p q r s : ℕ, 0 < p → 0 < q → 0 < r → 0 < s →
      p ^ 2 + q ^ 2 = (1 ^ 2 + 2 ^ 2) * (1 ^ 2 + 2 ^ 2) →
      r ^ 2 + s ^ 2 = (1 ^ 2 + 2 ^ 2) * (1 ^ 2 + 2 ^ 2) → s(p ^ 2, q ^ 2) = s(r ^ 2, s ^ 2) := by
  intro p q r s _ _ _ _ h1 h2
  norm_num at h1 h2
  have hp : p < 5 := by nlinarith
  have hq : q < 5 := by nlinarith
  have hr : r < 5 := by nlinarith
  have hs : s < 5 := by nlinarith
  interval_cases p <;> interval_cases q <;> interval_cases r <;> interval_cases s <;>
    simp_all [Sym2.eq_swap]

end PillowProblems.P29
