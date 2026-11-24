import PillowProblems.Basic

/-!
# Problem 23 (Algebra: Chances)

**Question.** *(dated 25/9/87)*

> A bag contains 2 counters, each of which is known to be black or white. 2 white and a black are put in, and 2 white and a black drawn out. Then a white is put in, and a white drawn out. What is the chance that it now contains 2 white?

**Answer.**

> Two-fifths.

*(Carroll's solution: Chapter III, problem 23; text in `data/problems.json`.)*

**Lean reading.** The bag's history is modelled by six labelled counters: `0`, `1` are the two
original counters, whose colours are unknown, `2`, `3` the two whites and `4` the black put in, and
`5` the white put in later. An outcome records the colours of counters `0`, `1`, the three counters
drawn the first time (in the order drawn, without replacement, from the five then in the bag), and
the counter drawn the second time (one of the three then in the bag); all possible outcomes are
equally likely. Tacit assumptions made explicit: each original counter is independently equally
likely black or white (giving Carroll's a priori chances 1/4, 1/2, 1/4 for 2 W, 1 W 1 B, 2 B), and
both draws are at random; since each stage always offers the same number of choices (5·4·3, then 3),
uniformity over whole outcomes is the same as drawing at random at each stage. We condition on what
was observed (the first draw 2 white and 1 black, the second draw white) and ask for the chance that
the two counters left in the bag are both white.

**Status.** proved
-/

namespace PillowProblems.P23

/-- The colour of a counter. -/
inductive Colour
  | white
  | black
  deriving DecidableEq

open Colour

instance : Fintype Colour := ⟨{white, black}, by intro x; cases x <;> simp⟩

/-- The six counters that are ever in the bag: `0`, `1` the original two (colours `orig`), `2`, `3`
the two whites and `4` the black put in first, `5` the white put in afterwards. -/
def colour (orig : Colour × Colour) : Fin 6 → Colour :=
  ![orig.1, orig.2, white, white, black, white]

/-- An outcome: the colours of the two original counters, the three counters drawn the first
time (in the order drawn, from the counters `0`-`4` then in the bag), and the counter drawn the
second time. -/
abbrev Outcome := (Colour × Colour) × (Fin 5 × Fin 5 × Fin 5) × Fin 6

/-- The counters drawn the first time. -/
def firstDraw (ω : Outcome) : List (Fin 6) :=
  [ω.2.1.1.castSucc, ω.2.1.2.1.castSucc, ω.2.1.2.2.castSucc]

/-- The counter drawn the second time. -/
def secondDraw (ω : Outcome) : Fin 6 := ω.2.2

/-- The outcome can occur: three different counters drawn the first time; then one of the counters
then in the bag (the two left and the white counter `5`) drawn. -/
def possible (ω : Outcome) : Prop :=
  (firstDraw ω).Nodup ∧ secondDraw ω ∉ firstDraw ω

/-- What was observed: the first draw was 2 white and a black; the second draw was white. -/
def observed (ω : Outcome) : Prop :=
  ((firstDraw ω).filter (fun i => colour ω.1 i = white)).length = 2 ∧
    ((firstDraw ω).filter (fun i => colour ω.1 i = black)).length = 1 ∧
    colour ω.1 (secondDraw ω) = white

/-- The counters left in the bag at the end. -/
def finalBag (ω : Outcome) : List (Fin 6) :=
  (List.finRange 6).filter (fun i => i ∉ firstDraw ω ∧ i ≠ secondDraw ω)

instance : DecidablePred possible := fun ω => by unfold possible; infer_instance
instance : DecidablePred observed := fun ω => by unfold observed; infer_instance

/-- The chance of `E` given that `O` was observed: the cases are the outcomes consistent with `O`,
all equally likely. -/
def condChance {Ω : Type*} [Fintype Ω] (O E : Ω → Prop) [DecidablePred O] [DecidablePred E] : ℚ :=
  uniformChance (Ω := {ω // O ω}) (fun ω => E ω.1)

private lemma condChance_eq {Ω : Type*} [Fintype Ω] (O E : Ω → Prop) [DecidablePred O]
    [DecidablePred E] :
    condChance O E = (Finset.univ.filter (fun ω => O ω ∧ E ω)).card /
      (Finset.univ.filter O).card := by
  rw [condChance, uniformChance_eq, Fintype.card_subtype]
  congr 2
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter O E)

set_option maxRecDepth 100000 in
/-- **Problem 23.** Given what was observed, the chance that the bag now contains 2 white is `2/5`. -/
theorem problem23 :
    condChance (fun ω => possible ω ∧ observed ω)
      (fun ω => ((finalBag ω).filter (fun i => colour ω.1 i = white)).length = 2) = 2 / 5 := by
  rw [condChance_eq]
  have h1 : (Finset.univ.filter (fun ω => (possible ω ∧ observed ω) ∧
      ((finalBag ω).filter (fun i => colour ω.1 i = white)).length = 2)).card = 108 := by
    decide
  have h2 : (Finset.univ.filter (fun ω => possible ω ∧ observed ω)).card = 270 := by decide
  rw [h1, h2]; norm_num

set_option maxRecDepth 100000 in
/-- Sanity check on the model: the final bag always holds exactly 2 counters. -/
theorem problem23_finalBag_card : ∀ ω : Outcome, possible ω → (finalBag ω).length = 2 := by
  decide

end PillowProblems.P23
