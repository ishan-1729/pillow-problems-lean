import PillowProblems.Basic

/-!
# Problem 5 (Algebra: Chances)

**Question.** *(dated 8/9/87)*

> A bag contains one counter, known to be either white or black. A white counter is put in, the bag shaken, and a counter drawn out, which proves to be white. What is now the chance of drawing a white counter?

**Answer.**

> Two-thirds.

*(Carroll's solution: Chapter III, problem 5; text in `data/problems.json`.)*

**Lean reading.** The experiment is modelled by the equally likely cases `Outcome = Colour × Fin 2`:
the first component is the colour of the counter originally in the bag, and the second says which
of the two counters then in the bag (`0` the original one, `1` the white one put in) is drawn.
Carroll tacitly takes the two possible original colours to be equally likely ("known to be either
white or black"), and "the bag shaken" means each of the two counters is equally likely to be
drawn; both are encoded by the uniform weight. The question asks for the chance that the counter
left in the bag (the one not drawn) is white, conditional on the observed event that the drawn
counter was white; conditional chance is `condChance` (chance of event and observation divided by
chance of observation). The value `2/3` is computed, not assumed.

**Status.** proved
-/

namespace PillowProblems.P05

/-- The colour of a counter. -/
inductive Colour
  | white
  | black
  deriving DecidableEq, Repr

open Colour

instance : Fintype Colour := ⟨{white, black}, by intro x; cases x <;> simp⟩

/-- The chance of `E` given the observation `O`, with the cases weighted by `w`:
the chance of `E ∧ O` divided by the chance of `O`. -/
def condChance {Ω : Type*} [Fintype Ω] (w : Ω → ℚ) (E O : Ω → Prop) [DecidablePred E]
    [DecidablePred O] : ℚ :=
  chance w (fun ω => E ω ∧ O ω) / chance w O

/-- The bag after the white counter is put in, when it originally held a counter of colour `c`:
counter `0` is the original one, counter `1` the white one added. -/
def bag (c : Colour) : Fin 2 → Colour := ![c, white]

/-- An elementary case: the original colour, and which of the two counters is drawn. -/
abbrev Outcome := Colour × Fin 2

/-- The observed event: the counter drawn proves to be white. -/
def drawnWhite (ω : Outcome) : Prop := bag ω.1 ω.2 = white

instance : DecidablePred drawnWhite := fun ω => by unfold drawnWhite; infer_instance

/-- The event asked about: the counter now left in the bag (the one not drawn) is white,
so that the next draw gives a white counter. -/
def nextWhite (ω : Outcome) : Prop := bag ω.1 ω.2.rev = white

instance : DecidablePred nextWhite := fun ω => by unfold nextWhite; infer_instance

/-- **Problem 5.** After a white counter has been drawn, the chance of drawing a white counter
is two-thirds. -/
theorem problem5 : condChance (fun _ : Outcome => (1 : ℚ)) nextWhite drawnWhite = 2 / 3 := by
  sorry

end PillowProblems.P05
