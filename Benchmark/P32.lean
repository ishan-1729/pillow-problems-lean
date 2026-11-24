import PillowProblems.Basic

/-!
# Problem 32 (Algebra: Series)

**Question.** *(dated 7/4/89)*

> Sum the Series \(1\,.\,5 + 2\,.\,6 +\&c.\) (1) to \(n\) terms; (2) to 100 terms.

**Answer.**

> \[ \begin{align} (1)\quad &\dfrac{n.(n+1).(2n+13)}{6};\\ (2)\quad &358550.\\ \end{align} \]

*(Carroll's solution: Chapter III, problem 32; text in `data/problems.json`.)*

**Lean reading.** The "&c." is read, as in Carroll's solution, as the series whose
`k`-th term is `k.(k+4)` (`term`; `term_one_two` checks the two terms he writes), and `S n` is
the sum of the terms `k = 1, …, n` in `ℕ`. Part (1) is stated for every `n` as an identity in
`ℚ`, so that Carroll's division by 6 is exact division; part (2) is the natural-number value of
`S 100`. No hypotheses are needed.

**Status.** proved
-/

namespace PillowProblems.P32

/-- The `k`-th term of the series `1.5 + 2.6 + &c.`, namely `k.(k+4)`. -/
def term (k : ℕ) : ℕ := k * (k + 4)

/-- The sum of the first `n` terms of the series. -/
def S (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, term k

/-- The first two terms are the ones Carroll writes, `1.5` and `2.6`. -/
theorem term_one_two : term 1 = 1 * 5 ∧ term 2 = 2 * 6 := by
  sorry

/-- Part (1): the sum to `n` terms is `n(n+1)(2n+13)/6`. -/
theorem problem32_a (n : ℕ) :
    (S n : ℚ) = n * (n + 1) * (2 * n + 13) / 6 := by
  sorry

/-- Part (2): the sum to 100 terms is `358550`. -/
theorem problem32_b : S 100 = 358550 := by
  sorry

end PillowProblems.P32
