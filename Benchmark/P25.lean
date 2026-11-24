import PillowProblems.Basic

/-!
# Problem 25 (Algebra: Equational Problems)

**Question.** *(dated 7/2/76)*

> If '\(\epsilon\)', '\(\alpha\)', '\(\lambda\)' represent proper fractions; and if, in a certain hospital, '\(\epsilon\)' of the patients have lost an eye, '\(\alpha\)' an arm, and '\(\lambda\)' a leg: what is the least possible number who have lost all three?

**Answer.**

> \[\epsilon + \alpha + \lambda - 2.\]

*(Carroll's solution: Chapter III, problem 25; text in `data/problems.json`.)*

**Lean reading.** The patients are `Fin N` (`0 < N`) and `E, A, L` are the sets who have lost an eye, an
arm, a leg, with `|E| = ε N`, `|A| = α N`, `|L| = ℓ N` (`ℓ` stands for Carroll's λ, a reserved
word in Lean). Like Carroll's answer, the "number" is measured as a fraction of all patients. The
hypotheses `ε, α, ℓ ≤ 1` and "`ε N`, `α N`, `ℓ N` are whole numbers" are needed for such a
hospital to exist; "proper" (`0 < ε < 1` etc.) is not needed. Carroll's answer `ε + α + λ - 2`
is right only when `ε + α + λ ≥ 2`; otherwise it is negative and the least possible fraction is
`0` (e.g. `ε = α = λ = 1/2`, `problem25_formula_fails`). So the theorem proves the least possible
fraction is `max (ε + α + ℓ - 2) 0` (`problem25`), which is Carroll's value when
`ε + α + ℓ ≥ 2` (`problem25_carroll`). The minimising arrangement is Carroll's row: the
`EA`-class is made as small as possible and the `L`-class starts from the other end.

**Status.** proved (corrected)
-/

namespace PillowProblems.P25

/-- The possible fractions of the `N` patients who have lost all three, when the fractions `ε`,
`α`, `ℓ` of them have lost an eye, an arm, a leg. -/
def allThreeFractions (N : ℕ) (ε α ℓ : ℚ) : Set ℚ :=
  {q | ∃ E A L : Finset (Fin N), (E.card : ℚ) = ε * N ∧ (A.card : ℚ) = α * N ∧
    (L.card : ℚ) = ℓ * N ∧ q = ((E ∩ A ∩ L).card : ℚ) / N}

/-- The least possible fraction who have lost all three is `max (ε + α + ℓ - 2) 0`. -/
theorem problem25 (N : ℕ) (hN : 0 < N) (ε α ℓ : ℚ) (hε : ε ≤ 1) (hα : α ≤ 1) (hℓ : ℓ ≤ 1)
    (hεN : ∃ e : ℕ, (e : ℚ) = ε * N) (hαN : ∃ a : ℕ, (a : ℚ) = α * N)
    (hℓN : ∃ l : ℕ, (l : ℚ) = ℓ * N) :
    IsLeast (allThreeFractions N ε α ℓ) (max (ε + α + ℓ - 2) 0) := by
  sorry

/-- Carroll's answer: when `ε + α + ℓ ≥ 2` the least possible fraction is `ε + α + ℓ - 2`. -/
theorem problem25_carroll (N : ℕ) (hN : 0 < N) (ε α ℓ : ℚ) (hε : ε ≤ 1) (hα : α ≤ 1) (hℓ : ℓ ≤ 1)
    (hεN : ∃ e : ℕ, (e : ℚ) = ε * N) (hαN : ∃ a : ℕ, (a : ℚ) = α * N)
    (hℓN : ∃ l : ℕ, (l : ℚ) = ℓ * N) (h2 : 2 ≤ ε + α + ℓ) :
    IsLeast (allThreeFractions N ε α ℓ) (ε + α + ℓ - 2) := by
  sorry

/-- Without `ε + α + ℓ ≥ 2` Carroll's formula fails: with `ε = α = ℓ = 1/2` the least fraction
is `0`, not `-1/2`. -/
theorem problem25_formula_fails :
    IsLeast (allThreeFractions 2 (1/2) (1/2) (1/2)) 0 ∧
      ¬ IsLeast (allThreeFractions 2 (1/2) (1/2) (1/2)) (1/2 + 1/2 + 1/2 - 2) := by
  sorry

end PillowProblems.P25
