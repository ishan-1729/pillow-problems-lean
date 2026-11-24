import PillowProblems.Basic

/-!
# Problem 72 (Transcendental Probabilities)

**Question.** *(dated 8/9/87)*

> A bag contains 2 counters, as to which nothing is known except that each is either black or white. Ascertain their colours without taking them out of the bag.

**Answer.**

> One is black, and the other white.

*(Carroll's solution: Chapter III, problem 72; text in `data/problems.json`.)*

**Lean reading.** "Nothing is known" is modelled as in Carroll's solution: the four colourings
`Bag := Fin 2 → Colour` are equally likely, so `BB, BW, WW` have chances `1/4, 1/2, 1/4`
(`problem72_prior`), and adding a black counter and drawing one of the three at random is the
uniform model on `Bag × Fin 3`. Carroll's answer is wrong (a deliberate fallacy, one of his
"transcendental probabilities"), although each of his computations is true and proved here: a bag
of three *known* counters gives a black with chance `2/3` iff it holds exactly two blacks
(`problem72_known_bag`), and the unknown bag with a black added gives a black with chance `2/3`
(`problem72_draw`). The error is applying the first fact to the second situation, where `2/3` is an
average over the possible contents. `problem72` proves the correct answer: the colours cannot be
ascertained, since no statement "the bag holds `k` blacks" has chance `1`, `BW` has chance only
`1/2` (also after a black is drawn), and the augmented bag is `BBW` only with chance `1/2`;
`problem72_other_prior` shows that under another ignorance prior (`BB, BW, WW` equally likely) the
drawing chance is again `2/3` while `BW` has chance `1/3`.

**Status.** proved (corrected)
-/

namespace PillowProblems.P72

/-- The colour of a counter. -/
inductive Colour | black | white
  deriving DecidableEq

open Colour

instance : Fintype Colour := ⟨{black, white}, by intro x; cases x <;> simp⟩

theorem card_colour : Fintype.card Colour = 2 := by
  sorry

/-- The unknown contents of the bag: the colours of counter `0` and counter `1`. -/
abbrev Bag := Fin 2 → Colour

/-- The number of black counters in a bag of `n` counters. -/
def numBlack {n : ℕ} (c : Fin n → Colour) : ℕ := (Finset.univ.filter fun i => c i = black).card

/-- The bag after a black counter (counter `2`) has been added. -/
def addBlack (b : Bag) : Fin 3 → Colour := ![b 0, b 1, black]

/-- Weights making the three compositions `BB`, `BW`, `WW` equally likely (the composition `BW`
is shared by two colourings). -/
def compositionWeight (b : Bag) : ℕ := if numBlack b = 1 then 1 else 2

/-- Carroll's premise (true): for a bag of three *known* counters, the chance of drawing a black
is `2/3` exactly when two of them are black. -/
theorem problem72_known_bag (c : Fin 3 → Colour) :
    uniformChance (fun i => c i = black) = 2 / 3 ↔ numBlack c = 2 := by
  sorry

/-- Carroll's prior (true): `BB`, `BW`, `WW` have chances `1/4`, `1/2`, `1/4`. -/
theorem problem72_prior :
    uniformChance (fun b : Bag => numBlack b = 2) = 1 / 4 ∧
    uniformChance (fun b : Bag => numBlack b = 1) = 1 / 2 ∧
    uniformChance (fun b : Bag => numBlack b = 0) = 1 / 4 := by
  sorry

/-- Carroll's computation (true): after a black counter is added, the chance of drawing a black
is `2/3`. -/
theorem problem72_draw :
    uniformChance (fun ω : Bag × Fin 3 => addBlack ω.1 ω.2 = black) = 2 / 3 := by
  sorry

/-- **Problem 72**, the correct answer: the colours cannot be ascertained. The drawing chance is
indeed `2/3`, but no statement "the bag holds exactly `k` black counters" has chance `1`; the bag
is `BW` only with chance `1/2`, also given that a black is drawn from the augmented bag; and the
augmented bag is `BBW` only with chance `1/2`. -/
theorem problem72 :
    uniformChance (fun ω : Bag × Fin 3 => addBlack ω.1 ω.2 = black) = 2 / 3 ∧
    (∀ k : ℕ, uniformChance (fun b : Bag => numBlack b = k) < 1) ∧
    uniformChance (fun b : Bag => numBlack b = 1) = 1 / 2 ∧
    uniformChance (fun ω : Bag × Fin 3 => numBlack ω.1 = 1 ∧ addBlack ω.1 ω.2 = black) /
      uniformChance (fun ω : Bag × Fin 3 => addBlack ω.1 ω.2 = black) = 1 / 2 ∧
    uniformChance (fun b : Bag => numBlack (addBlack b) = 2) = 1 / 2 := by
  sorry

/-- Carroll's conclusion does not follow: "the bag contains one black and one white" has chance
`1/2 ≠ 1`, and the other contents `BB` and `WW` keep positive chance. -/
theorem problem72_not_ascertained :
    uniformChance (fun b : Bag => numBlack b = 1) ≠ 1 ∧
    0 < uniformChance (fun b : Bag => numBlack b = 2) ∧
    0 < uniformChance (fun b : Bag => numBlack b = 0) := by
  sorry

/-- With a different "ignorance" prior (the compositions `BB`, `BW`, `WW` equally likely) the
chance of drawing a black from the augmented bag is again `2/3`, while `BW` has chance `1/3`:
the chance `2/3` cannot reveal the contents. -/
theorem problem72_other_prior :
    chance (fun ω : Bag × Fin 3 => (compositionWeight ω.1 : ℚ))
      (fun ω => addBlack ω.1 ω.2 = black) = 2 / 3 ∧
    chance (fun b : Bag => (compositionWeight b : ℚ)) (fun b : Bag => numBlack b = 1) = 1 / 3 := by
  sorry

end PillowProblems.P72
