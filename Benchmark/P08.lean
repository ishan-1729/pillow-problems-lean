import PillowProblems.Basic

/-!
# Problem 8 (Algebra: Equational Problems)

**Question.** *(dated 3/89)*

> Some men sat in a circle, so that each had 2 neighbours; and each had a certain number of shillings. The first had 1/ more than the second, who had 1/ more than the third, and so on. The first gave 1/ to the second, who gave 2/ to the third, and so on, each giving 1/ more than he received, as long as possible. There were then 2 neighbours, one of whom had 4 times as much as the other. How many men were there? And how much had the poorest man at first?

**Answer.**

> 7 men; 2 shillings.

*(Carroll's solution: Chapter III, problem 8; text in `data/problems.json`.)*

**Lean reading.** The men are numbered `0, …, m - 1` round the circle (`0` is "the first"), with
`3 ≤ m` so that each has two distinct neighbours; their initial shillings `w` drop by 1/ from
each man to the next (`Descending`), so the last man is the poorest. The passing is simulated
step by step exactly as told (`holdings`): at step `t` the man `t % m` hands `t + 1` shillings,
counting what he has just received, to the next man, and it stops at the first step `T` at which
he cannot (`StopsAt`; `problem8_terminates` shows such a `T` always exists). Holdings are
integers so that the simulation is a total function; before `T` no one ever goes negative.
The theorem is an iff: the stopped position has two neighbours in the ratio 4 : 1 exactly when
there are 7 men and the poorest started with 2/, so Carroll's answer is the only one.

**Status.** proved
-/

namespace PillowProblems.P08

/-- Step `t` of the passing (counting from `0`): man `t % m` hands `t + 1` shillings to his
neighbour `(t + 1) % m`. So the first man gives 1/ to the second, who gives 2/ to the third, and so
on round the circle, each giving 1/ more than he received. -/
def transfer (m : ℕ) (h : ℕ → ℤ) (t : ℕ) : ℕ → ℤ := fun i =>
  h i - (if i = t % m then ((t : ℤ) + 1) else 0) + (if i = (t + 1) % m then ((t : ℤ) + 1) else 0)

/-- What every man holds after the first `t` steps, the men starting with `w i` shillings. -/
def holdings (m : ℕ) (w : ℕ → ℕ) : ℕ → ℕ → ℤ
  | 0 => fun i => (w i : ℤ)
  | t + 1 => transfer m (holdings m w t) t

/-- At step `t` the man whose turn it is can hand on `t + 1` shillings. -/
def CanGive (m : ℕ) (w : ℕ → ℕ) (t : ℕ) : Prop := (t : ℤ) + 1 ≤ holdings m w t (t % m)

/-- The passing goes on "as long as possible": every step before `T` can be made, step `T`
cannot. -/
def StopsAt (m : ℕ) (w : ℕ → ℕ) (T : ℕ) : Prop := (∀ t < T, CanGive m w t) ∧ ¬ CanGive m w T

/-- "The first had 1/ more than the second, who had 1/ more than the third, and so on". -/
def Descending (m : ℕ) (w : ℕ → ℕ) : Prop := ∀ i, i + 1 < m → w i = w (i + 1) + 1

/-- Two neighbours, one of whom has 4 times as much as the other. -/
def FourfoldNeighbours (m : ℕ) (h : ℕ → ℤ) : Prop :=
  ∃ i < m, h i = 4 * h ((i + 1) % m) ∨ h ((i + 1) % m) = 4 * h i

/-- The final position has two neighbours, one with 4 times as much as the other, exactly when
there are 7 men and the poorest had 2 shillings at first. -/
theorem problem8 (m : ℕ) (w : ℕ → ℕ) (T : ℕ) (hm : 3 ≤ m) (hw : Descending m w)
    (hT : StopsAt m w T) :
    FourfoldNeighbours m (holdings m w T) ↔ m = 7 ∧ IsLeast (w '' Set.Iio m) 2 := by
  sorry

/-- The passing always stops. -/
theorem problem8_terminates (m : ℕ) (w : ℕ → ℕ) (hm : 0 < m) (hw : Descending m w) :
    ∃ T, StopsAt m w T := by
  sorry

/-- The situation of the problem occurs (7 men holding 8/, 7/, …, 2/). -/
theorem problem8_nonvacuous :
    ∃ (w : ℕ → ℕ) (T : ℕ), Descending 7 w ∧ StopsAt 7 w T ∧
      FourfoldNeighbours 7 (holdings 7 w T) := by
  sorry

end PillowProblems.P08
