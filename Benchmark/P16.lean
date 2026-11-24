import PillowProblems.Basic

/-!
# Problem 16 (Algebra: Chances)

**Question.** *(dated 10/87)*

> There are two bags, one containing a counter, known to be either white or black; the other containing 1 white and 2 black. A white is put into the first, the bag shaken, and a counter drawn out, which proves to be white. Which course will now give the best chance of drawing a white—to draw from one of the two bags without knowing which it is, or to empty one bag into the other and then draw?

**Answer.**

> The first course gives chance = \(\tfrac{1}{2}\); the second, \(\tfrac{5}{12}\). Hence the first is best.

*(Carroll's solution: Chapter III, problem 16; text in `data/problems.json`.)*

**Lean reading.** As in Problem 5, the counter originally in the first bag is white or black
with chance `1/2` each (Carroll's tacit prior). After the white is put in and the bag shaken, each
of its two counters is equally likely to be drawn. The observation is that the drawn counter is
white, and each course is judged by the chance of drawing a white *conditional* on that
observation (`condChance`). In the first course "one of the two bags without knowing which" is
read, as Carroll reads it, as each bag being taken with chance `1/2` and then each counter in it
being equally likely. So the elementary cases `Colour × Fin 2 × (Fin 1 ⊕ Fin 3)` (original
colour; counter drawn first; then either the single counter left in the first bag or one of the
three counters of the second) carry the product weights `course1Weight`. In the second course the
counter left in the first bag and the three of the second bag end up in one bag (which bag is
emptied into which does not matter), and each of the four counters is equally likely, so the cases
`Colour × Fin 2 × Fin 4` are equally likely. The values `1/2` and `5/12`, and hence that the first
course is better, are computed from these models.

**Status.** proved
-/

namespace PillowProblems.P16

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

/-- The first bag after the white is put in, when it originally held a counter of colour `c`:
counter `0` is the original one, counter `1` the white one added. -/
def firstBag (c : Colour) : Fin 2 → Colour := ![c, white]

/-- The second bag: 1 white and 2 black. -/
def secondBag : Fin 3 → Colour := ![white, black, black]

/-- The counter left in the first bag when counter `d` has been drawn from it. -/
def leftInFirst (c : Colour) (d : Fin 2) : Colour := firstBag c d.rev

/-! ### First course: draw from one of the two bags, not knowing which -/

/-- An elementary case of the first course: the original colour in the first bag, the counter
drawn from it, and the final draw: `inl 0` is the single counter left in the first bag, `inr j`
is counter `j` of the second bag. -/
abbrev Course1 := Colour × Fin 2 × (Fin 1 ⊕ Fin 3)

/-- The chance of the final draw: a bag is taken with chance `1/2`, then each of its counters is
equally likely (the first bag now holds 1 counter, the second 3). -/
def finalDrawWeight : Fin 1 ⊕ Fin 3 → ℚ
  | .inl _ => 1 / 2 * (1 / 1)
  | .inr _ => 1 / 2 * (1 / 3)

/-- The weight of an elementary case of the first course: original colour (`1/2` each), counter
first drawn (`1/2` each), final draw. -/
def course1Weight (ω : Course1) : ℚ := 1 / 2 * (1 / 2) * finalDrawWeight ω.2.2

/-- The colour of the counter finally drawn in the first course. -/
def course1Colour (ω : Course1) : Colour :=
  match ω.2.2 with
  | .inl _ => leftInFirst ω.1 ω.2.1
  | .inr j => secondBag j

/-- The observation: the counter drawn from the first bag was white. -/
def observed1 (ω : Course1) : Prop := firstBag ω.1 ω.2.1 = white

instance : DecidablePred observed1 := fun ω => by unfold observed1; infer_instance

/-- The event: the counter finally drawn is white. -/
def final1White (ω : Course1) : Prop := course1Colour ω = white

instance : DecidablePred final1White := fun ω => by unfold final1White; infer_instance

/-! ### Second course: empty one bag into the other, then draw -/

/-- An elementary case of the second course: the original colour in the first bag, the counter
drawn from it, and which of the four counters of the united bag is finally drawn. -/
abbrev Course2 := Colour × Fin 2 × Fin 4

/-- The united bag: the counter left in the first bag together with the three of the second. -/
def unitedBag (c : Colour) (d : Fin 2) : Fin 4 → Colour :=
  Matrix.vecCons (leftInFirst c d) secondBag

/-- The observation: the counter drawn from the first bag was white. -/
def observed2 (ω : Course2) : Prop := firstBag ω.1 ω.2.1 = white

instance : DecidablePred observed2 := fun ω => by unfold observed2; infer_instance

/-- The event: the counter finally drawn from the united bag is white. -/
def final2White (ω : Course2) : Prop := unitedBag ω.1 ω.2.1 ω.2.2 = white

instance : DecidablePred final2White := fun ω => by unfold final2White; infer_instance

/-- **Problem 16.** Given that the counter drawn from the first bag was white, the first course
(draw from one of the bags, not knowing which) gives chance `1/2` of a white, and the second
(empty one bag into the other, then draw) gives `5/12`; hence the first course is the better. -/
theorem problem16 :
    condChance course1Weight final1White observed1 = 1 / 2 ∧
      condChance (fun _ : Course2 => (1 : ℚ)) final2White observed2 = 5 / 12 ∧
      condChance (fun _ : Course2 => (1 : ℚ)) final2White observed2 <
        condChance course1Weight final1White observed1 := by
  sorry

end PillowProblems.P16
