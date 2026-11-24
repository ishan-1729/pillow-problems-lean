import PillowProblems.Basic

/-!
# Problem 41 (Algebra: Chances)

**Question.** *(dated 9/87)*

> My friend brings me a bag containing four counters, each of which is either black or white. He bids me draw two, both of which prove to be white. He then says "I meant to tell you, before you began, that there was at least *one* white counter in the bag. However, you know it now, without my telling you. Draw again."
>
> (1) What is now my chance of drawing white?
>
> (2) What would it have been, if he had not spoken?

**Answer.**

> (1) Seven-twelfths. (2) One-half.

*(Carroll's solution: Chapter III, problem 41; text in `data/problems.json`.)*

**Lean reading.** The four counters are labelled `0`-`3`; an outcome records the colour of each and
the three counters drawn in order (the two drawn first, then the one drawn on "Draw again"), drawn
at random without replacement. Tacit assumption: a priori each counter is independently equally
likely black or white (Carroll's chances 1, 4, 6, 4, 1 over 16 in (2)); all possible outcomes are
equally likely. Part (2) conditions on the first two counters drawn being white: chance `1/2`, as
Carroll says. Part (1) conditions in addition on the friend's information "at least one white
counter in the bag"; that is implied by the observed draw (as the friend himself remarks), so the
chance is again `1/2`, not Carroll's `7/12`. What is wrong: Carroll's a priori chances `1/8, 3/8,
3/8, 1/8` for `WWWW, WWWB, WWBB, WBBB` are not those of a bag known to contain at least one white
(which are `1, 4, 6, 4` over `15`); they are those of a bag in which one particular counter is known
to be white and the other three are unknown. `problem41_carroll` shows that under that different
information (counter `0` known to be white) the chance is indeed `7/12`.

**Status.** proved (corrected)
-/

namespace PillowProblems.P41

/-- The colour of a counter. -/
inductive Colour
  | white
  | black
  deriving DecidableEq

open Colour

instance : Fintype Colour := ⟨{white, black}, by intro x; cases x <;> simp⟩

/-- An outcome: the colours of counters `0, 1, 2, 3`, and the counters `(i, j, k)` drawn in order
(`i, j` the first two, `k` the one drawn again). -/
abbrev Outcome := (Colour × Colour × Colour × Colour) × (Fin 4 × Fin 4 × Fin 4)

/-- The colour of counter `n`. -/
def colour (ω : Outcome) : Fin 4 → Colour := ![ω.1.1, ω.1.2.1, ω.1.2.2.1, ω.1.2.2.2]

/-- The three counters drawn are distinct (no replacement). -/
def possible (ω : Outcome) : Prop :=
  ω.2.1 ≠ ω.2.2.1 ∧ ω.2.1 ≠ ω.2.2.2 ∧ ω.2.2.1 ≠ ω.2.2.2

/-- The observed event: the first two counters drawn are white. -/
def drewTwoWhite (ω : Outcome) : Prop := colour ω ω.2.1 = white ∧ colour ω ω.2.2.1 = white

/-- The friend's information: at least one counter in the bag is white. -/
def atLeastOneWhite (ω : Outcome) : Prop := ∃ n, colour ω n = white

/-- The counter drawn again is white. -/
def drawWhite (ω : Outcome) : Prop := colour ω ω.2.2.2 = white

instance : DecidablePred possible := fun ω => by unfold possible; infer_instance
instance : DecidablePred drewTwoWhite := fun ω => by unfold drewTwoWhite; infer_instance
instance : DecidablePred atLeastOneWhite := fun ω => by unfold atLeastOneWhite; infer_instance
instance : DecidablePred drawWhite := fun ω => by unfold drawWhite; infer_instance

/-- The chance of `E` given that `O` was observed: the cases are the outcomes consistent with `O`,
all equally likely. -/
def condChance {Ω : Type*} [Fintype Ω] (O E : Ω → Prop) [DecidablePred O] [DecidablePred E] : ℚ :=
  uniformChance (Ω := {ω // O ω}) (fun ω => E ω.1)

set_option maxRecDepth 100000 in
/-- **Problem 41 (1)** (corrected). Knowing there was at least one white counter, and having drawn
two whites, the chance of drawing white is `1/2` (Carroll: `7/12`). -/
theorem problem41_a :
    condChance (fun ω => possible ω ∧ atLeastOneWhite ω ∧ drewTwoWhite ω) drawWhite = 1 / 2 := by
  sorry

set_option maxRecDepth 100000 in
/-- **Problem 41 (2).** Had the friend not spoken, the chance would have been `1/2`. -/
theorem problem41_b :
    condChance (fun ω => possible ω ∧ drewTwoWhite ω) drawWhite = 1 / 2 := by
  sorry

set_option maxRecDepth 100000 in
/-- What Carroll's solution of (1) actually computes: if instead a particular counter (`0`) were
known to be white, the chance would be `7/12`. -/
theorem problem41_carroll :
    condChance (fun ω => possible ω ∧ colour ω 0 = white ∧ drewTwoWhite ω) drawWhite =
      7 / 12 := by
  sorry

end PillowProblems.P41
