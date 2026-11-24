import PillowProblems.Basic

/-!
# Problem 38 (Algebra: Chances)

**Question.** *(dated 3/76)*

> There are 3 bags, '\(A\)', '\(B\)', and '\(C\)'. '\(A\)' contains 3 red counters, '\(B\)' 2 red and one white, '\(C\)' one red and 2 white. Two bags are taken at random, and a counter drawn from each: both prove to be red. The counters are replaced, and the experiment is repeated with the same two bags: one proves to be red. What is the chance of the other being red?

**Answer.**

> Fortynine-seventytwoths.

*(Carroll's solution: Chapter III, problem 38; text in `data/problems.json`.)*

**Lean reading.** The bags are `0 = A` (3 red), `1 = B` (2 red, 1 white), `2 = C` (1 red, 2 white),
counters labelled. The final sentence is ambiguous: "one proves to be red" may mean that a
particular one of the two counters is seen to be red (the other not yet seen), or only that at least
one of them is red. Carroll's solution takes the first reading: his six equally likely arrangements
are (bag of the unseen counter, bag of the counter seen red, bag left out). So an outcome records an
ordered pair `(u, o)` of distinct bags (`u`: the bag whose second counter is unknown, `o`: the bag
whose second counter is seen), the counters drawn from `u` and `o` in the first experiment, and
those drawn in the second; all possible outcomes are equally likely (bags and counters taken at
random, counters replaced, and which of the two second counters is looked at first chosen at random,
independently of the colours, as Carroll's equal a priori weight on his six arrangements assumes). We condition on: both first counters red and the second counter from `o`
red, and ask for the chance the second counter from `u` is red: `49/72`. For comparison,
`problem38_atLeastOne` shows that under the other reading (at least one of the second pair red,
chance that both are) the answer would be `49/95`.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P38

/-- The colour of a counter. -/
inductive Colour
  | red
  | white
  deriving DecidableEq

open Colour

/-- The contents of the bags `0 = A`, `1 = B`, `2 = C`, counter by counter. -/
def contents : Fin 3 → Fin 3 → Colour :=
  ![![red, red, red], ![red, red, white], ![red, white, white]]

/-- An outcome `((u, o), (a₁, a₂), (b₁, b₂))`: `u, o` are the two bags taken (`u` the one whose
counter in the second experiment is unknown, `o` the one whose counter is seen), `a₁, a₂` the
counters drawn from `u, o` in the first experiment and `b₁, b₂` in the second. -/
abbrev Outcome := (Fin 3 × Fin 3) × (Fin 3 × Fin 3) × (Fin 3 × Fin 3)

/-- The two bags taken are different. -/
def possible (ω : Outcome) : Prop := ω.1.1 ≠ ω.1.2

/-- The colour of the counter drawn from bag `u` in the first experiment. -/
def firstU (ω : Outcome) : Colour := contents ω.1.1 ω.2.1.1
/-- The colour of the counter drawn from bag `o` in the first experiment. -/
def firstO (ω : Outcome) : Colour := contents ω.1.2 ω.2.1.2
/-- The colour of the counter drawn from bag `u` in the second experiment (the unknown one). -/
def secondU (ω : Outcome) : Colour := contents ω.1.1 ω.2.2.1
/-- The colour of the counter drawn from bag `o` in the second experiment (the one seen). -/
def secondO (ω : Outcome) : Colour := contents ω.1.2 ω.2.2.2

instance : DecidablePred possible := fun ω => by unfold possible; infer_instance

/-- The chance of `E` given that `O` was observed: the cases are the outcomes consistent with `O`,
all equally likely. -/
def condChance {Ω : Type*} [Fintype Ω] (O E : Ω → Prop) [DecidablePred O] [DecidablePred E] : ℚ :=
  uniformChance (Ω := {ω // O ω}) (fun ω => E ω.1)

set_option maxRecDepth 100000 in
/-- **Problem 38** (Carroll's reading). Both counters of the first experiment are red, and in the
second experiment the counter from bag `o` is seen to be red; the chance that the other counter
(from bag `u`) is red is `49/72`. -/
theorem problem38 :
    condChance (fun ω => possible ω ∧ firstU ω = red ∧ firstO ω = red ∧ secondO ω = red)
      (fun ω => secondU ω = red) = 49 / 72 := by
  sorry

set_option maxRecDepth 100000 in
/-- The other reading: told only that at least one counter of the second experiment is red, the
chance that both are red would be `49/95` (not Carroll's answer). -/
theorem problem38_atLeastOne :
    condChance (fun ω => possible ω ∧ firstU ω = red ∧ firstO ω = red ∧
        (secondU ω = red ∨ secondO ω = red))
      (fun ω => secondU ω = red ∧ secondO ω = red) = 49 / 95 := by
  sorry

end PillowProblems.P38
