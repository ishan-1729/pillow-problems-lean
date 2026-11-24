import PillowProblems.Basic

/-!
# Problem 27 (Algebra: Chances)

**Question.** *(dated 4/3/80)*

> There are 3 bags, each containing 6 counters; one contains 5 white and one black; another, 4 white and 2 black; the third, 3 white and 3 black. From two of the bags (it is not known which) 2 counters are drawn, and prove to be black and white. What is the chance of drawing a white counter from the remaining bag?

**Answer.**

> Seventeen-twentyfifths.

*(Carroll's solution: Chapter III, problem 27; text in `data/problems.json`.)*

**Lean reading.** The bags are `0 = A` (5 white, 1 black), `1 = B` (4 white, 2 black), `2 = C` (3
white, 3 black), each counter labelled. An outcome records which bag is the remaining one and which
counter is drawn from each bag (for the remaining bag, the counter that will be drawn from it); all
outcomes are equally likely. Tacit assumptions made explicit: "it is not known which" is read as
each bag being equally likely to be the remaining one, and "2 counters are drawn" as one counter
drawn at random from each of the other two bags (Carroll's reading in his solution). We condition on
the observation that of these two counters one is white and one black, and ask for the chance that
the counter drawn from the remaining bag is white.

**Status.** proved
-/

namespace PillowProblems.P27

/-- The colour of a counter. -/
inductive Colour
  | white
  | black
  deriving DecidableEq

open Colour

/-- The contents of the bags `0 = A`, `1 = B`, `2 = C`, counter by counter. -/
def contents : Fin 3 → Fin 6 → Colour :=
  ![![white, white, white, white, white, black],
    ![white, white, white, white, black, black],
    ![white, white, white, black, black, black]]

/-- An outcome: the remaining bag, and the counter drawn from each of `A`, `B`, `C`. -/
abbrev Outcome := Fin 3 × (Fin 6 × Fin 6 × Fin 6)

/-- The remaining bag (the one not drawn from at first). -/
def remaining (ω : Outcome) : Fin 3 := ω.1

/-- The counter drawn from bag `b`. -/
def drawn (ω : Outcome) : Fin 3 → Fin 6 := ![ω.2.1, ω.2.2.1, ω.2.2.2]

/-- The colour of the counter drawn from bag `b`. -/
def colourFrom (ω : Outcome) (b : Fin 3) : Colour := contents b (drawn ω b)

/-- What was observed: the counters drawn from the two bags other than the remaining one are
one white and one black. -/
def observed (ω : Outcome) : Prop :=
  ∃ b₁ b₂, b₁ ≠ remaining ω ∧ b₂ ≠ remaining ω ∧
    colourFrom ω b₁ = white ∧ colourFrom ω b₂ = black

instance : DecidablePred observed := fun ω => by unfold observed; infer_instance

/-- The chance of `E` given that `O` was observed: the cases are the outcomes consistent with `O`,
all equally likely. -/
def condChance {Ω : Type*} [Fintype Ω] (O E : Ω → Prop) [DecidablePred O] [DecidablePred E] : ℚ :=
  uniformChance (Ω := {ω // O ω}) (fun ω => E ω.1)

set_option maxRecDepth 100000 in
/-- **Problem 27.** Given the observation, the chance of drawing a white counter from the remaining
bag is `17/25`. -/
theorem problem27 :
    condChance observed (fun ω => colourFrom ω (remaining ω) = white) = 17 / 25 := by
  sorry

end PillowProblems.P27
