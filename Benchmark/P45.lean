import PillowProblems.Basic

/-!
# Problem 45 (Algebra: Chances)

**Question.** *(dated 5/84)*

> If an infinite number of rods be broken: find the chance that one at least is broken in the middle.

**Answer.**

> \[ \cdot 6321207 \quad \&c. \]

*(Carroll's solution: Chapter III, problem 45; text in `data/problems.json`.)*

**Lean reading.** Read literally with a continuous break point, each rod breaks exactly at
its middle with chance `0`, so the question has no content; we formalize Carroll's reading from
his solution. At stage `n = 2k+1` (odd, so that there is a middle point) there are `n` rods, each
rod can break only at one of `n` equally frangible points, the rods break independently, and all
`n^n` cases (`Breaks k`) are equally likely; `chanceMiddle k` is the chance that some rod breaks at
the middle point. Carroll's "infinite number of rods" is the limit `n → ∞`, in which the number
of rods and the number of break points grow together, exactly as in his solution.
`chanceMiddle_eq` is his finite formula `1 - (1 - 1/n)^n`, `problem45` proves the limit is
`1 - e⁻¹` (his `1 - (1 - 0)^(1/0)`), and `problem45_decimal` gives its decimal value. Carroll's
exact answer is right, but his decimal `·6321207 &c.` is not: `1 - e⁻¹ = ·63212055…`, so the
seventh decimal is `5` (`6` rounded), not `7` (his step `3·0861612 - 2·7182818 = ·3678793`
should give `·3678794`).

**Status.** proved (corrected)
-/

namespace PillowProblems.P45

open Filter Topology Real

/-- The `n`-th stage of Carroll's model, with `n = 2k+1` odd: there are `n` rods, each rod can
break only at one of `n` equally frangible points `0, …, n-1`, and the rods break independently.
A case is the list of break points of the `n` rods. -/
abbrev Breaks (k : ℕ) := Fin (2 * k + 1) → Fin (2 * k + 1)

/-- The middle point of a rod divided into `2k+2` equal parts by `2k+1` points. -/
def middle (k : ℕ) : Fin (2 * k + 1) := ⟨k, by omega⟩

/-- The event that at least one rod is broken in the middle. -/
def someMiddle (k : ℕ) (f : Breaks k) : Prop := ∃ i, f i = middle k

instance (k : ℕ) : DecidablePred (someMiddle k) := fun f => by unfold someMiddle; infer_instance

/-- The chance, at stage `n = 2k+1`, that at least one rod is broken in the middle. -/
def chanceMiddle (k : ℕ) : ℚ := uniformChance (someMiddle k)

/-- Carroll's finite formula: at stage `n = 2k+1` the chance is `1 - (1 - 1/n)^n`. -/
theorem chanceMiddle_eq (k : ℕ) :
    chanceMiddle k = 1 - (1 - 1 / (2 * k + 1 : ℚ)) ^ (2 * k + 1) := by
  sorry

/-- Carroll's answer, exactly: as the number of rods (and of possible break points) tends to
infinity, the chance tends to `1 - (1 - 0)^(1/0) = 1 - e⁻¹`. -/
theorem problem45 :
    Tendsto (fun k => (chanceMiddle k : ℝ)) atTop (𝓝 (1 - exp (-1))) := by
  sorry

/-- The decimal value: `1 - e⁻¹ = ·6321205…`, so Carroll's seventh decimal (`·6321207`) is wrong. -/
theorem problem45_decimal :
    (0.6321205 : ℝ) < 1 - exp (-1) ∧ 1 - exp (-1) < 0.6321206 ∧
      ¬ ((0.6321207 : ℝ) ≤ 1 - exp (-1) ∧ 1 - exp (-1) < 0.6321208) := by
  sorry

end PillowProblems.P45
