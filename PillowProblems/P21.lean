import PillowProblems.Basic

/-!
# Problem 21 (Algebra: Series)

**Question.** *(dated 7/4/89)*

> Sum, (1) to \(n\) terms, (2) to 100 terms, the series \[ 1\,.\,3\,.\,5 + 2\,.\,4\,.\,6 + \&c. \]

**Answer.**

> (1) \(\dfrac{n . \overline{n + 1} . \overline{n + 4} . \overline{n + 5}}{4}\); \(\quad\text{(2)}\quad 27,573,000\).

*(Carroll's solution: Chapter III, problem 21; text in `data/problems.json`.)*

**Lean reading.** The "&c." is read, as in Carroll's solution, as the series whose
`k`-th term is `k.(k+2).(k+4)` (`term`; `term_one_two` checks the two terms he writes), and
`S n` is the sum of the terms `k = 1, …, n` in `ℕ`. Part (1) is stated for every `n` as an
identity in `ℚ`, so that Carroll's division by 4 is exact division; part (2) is the natural-number
value of `S 100`. No hypotheses are needed.

**Status.** proved
-/

namespace PillowProblems.P21

/-- The `k`-th term of the series `1.3.5 + 2.4.6 + &c.`, namely `k.(k+2).(k+4)`. -/
def term (k : ℕ) : ℕ := k * (k + 2) * (k + 4)

/-- The sum of the first `n` terms of the series. -/
def S (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, term k

/-- The first two terms are the ones Carroll writes, `1.3.5` and `2.4.6`. -/
theorem term_one_two : term 1 = 1 * 3 * 5 ∧ term 2 = 2 * 4 * 6 := by
  decide

/-- Part (1): the sum to `n` terms is `n(n+1)(n+4)(n+5)/4`. -/
theorem problem21_a (n : ℕ) :
    (S n : ℚ) = n * (n + 1) * (n + 4) * (n + 5) / 4 := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    rw [S, Finset.sum_Icc_succ_top (by omega), Nat.cast_add, ← S, ih]
    simp only [term]
    push_cast
    ring

/-- Part (2): the sum to 100 terms is `27,573,000`. -/
theorem problem21_b : S 100 = 27573000 := by
  have h := problem21_a 100
  norm_num at h
  exact_mod_cast h

end PillowProblems.P21
