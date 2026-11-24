import PillowProblems.Basic

/-!
# Problem 19 (Algebra: Chances)

**Question.**

> There are 3 bags; one containing a white counter and a black one, another two white and a black, and the third 3 white and a black. It is not known in what order the bags are placed. A white counter is drawn from one of them, and a black from another. What is the chance of drawing a white counter from the remaining bag?

**Answer.**

> Eleven-seventeenths.

*(Carroll's solution: Chapter III, problem 19; text in `data/problems.json`.)*

**Lean reading.** Call the bags `A` (1 white, 1 black), `B` (2 white, 1 black) and `C` (3 white,
1 black), numbered `0, 1, 2`. "Not known in what order the bags are placed" is read, as Carroll
reads it, as every order (a permutation `σ`, with bag `σ p` in place `p`) being equally likely.
The white is drawn from the bag in place `0` and the black from the bag in place `1`, and the
question asks for the chance of a white from the bag in place `2`, conditional on that observation
(`condChance`). Draws are modelled by choosing, independently and uniformly, one counter of each
bag (`Fin 2 × Fin 3 × Fin 4`; only the counters of the bags actually drawn from matter). So the
`6 · 24` elementary cases `Equiv.Perm (Fin 3) × Fin 2 × Fin 3 × Fin 4` are equally likely, and the
model gives Carroll's case weights `1/2 · 1/3`, `1/2 · 1/4`, and so on. The value `11/17` is
computed by counting cases.

**Status.** proved
-/

namespace PillowProblems.P19

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

/-- Bag `A`: a white counter and a black one. -/
def bagA : Fin 2 → Colour := ![white, black]

/-- Bag `B`: two white and a black. -/
def bagB : Fin 3 → Colour := ![white, white, black]

/-- Bag `C`: three white and a black. -/
def bagC : Fin 4 → Colour := ![white, white, white, black]

/-- An elementary case: the order of the bags (bag `σ p` stands in place `p`), and the counter
that a draw from bag `A`, `B`, `C` respectively gives. -/
abbrev Outcome := Equiv.Perm (Fin 3) × Fin 2 × Fin 3 × Fin 4

/-- The colour drawn from bag `k` (`0 = A`, `1 = B`, `2 = C`) in the case `ω`. -/
def drawn (ω : Outcome) (k : Fin 3) : Colour :=
  match k with
  | 0 => bagA ω.2.1
  | 1 => bagB ω.2.2.1
  | 2 => bagC ω.2.2.2

/-- The observation: a white is drawn from the bag in place `0` and a black from the bag in
place `1`. -/
def observed (ω : Outcome) : Prop := drawn ω (ω.1 0) = white ∧ drawn ω (ω.1 1) = black

instance : DecidablePred observed := fun ω => by unfold observed; infer_instance

/-- The event: a white is drawn from the remaining bag, in place `2`. -/
def remainingWhite (ω : Outcome) : Prop := drawn ω (ω.1 2) = white

instance : DecidablePred remainingWhite := fun ω => by unfold remainingWhite; infer_instance

private lemma card_observed : (Finset.univ.filter observed).card = 34 := by decide

private lemma card_both :
    (Finset.univ.filter (fun ω => remainingWhite ω ∧ observed ω)).card = 22 := by decide

/-- **Problem 19.** After a white has been drawn from one bag and a black from another, the
chance of drawing a white from the remaining bag is eleven-seventeenths. -/
theorem problem19 :
    condChance (fun _ : Outcome => (1 : ℚ)) remainingWhite observed = 11 / 17 := by
  change uniformChance (fun ω => remainingWhite ω ∧ observed ω) / uniformChance observed = 11 / 17
  rw [uniformChance_eq, uniformChance_eq, card_observed, card_both]
  have h : (Fintype.card Outcome : ℚ) ≠ 0 := by positivity
  field_simp
  norm_num

end PillowProblems.P19
