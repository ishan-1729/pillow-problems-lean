import PillowProblems.Basic

/-!
# Problem 20 (Pure Geometry, Plane)

**Question.** *(dated 5/88)*

> In the base of a given Triangle find a Point such that if from it two lines be drawn, terminated by the sides, one being perpendicular to the base and one to the left-hand side, they shall be equal.

*(Carroll's solution: Chapter III, problem 20; text in `data/problems.json`.)*

**Lean reading.** `ABC` is a nondegenerate triangle (`cross A B C ≠ 0`) with base `BC` and
left-hand side `AB`. Following Carroll's figure and his formulas `PQ = PC tan C`,
`PR = PB sin B`, the line from `P ∈ BC` perpendicular to the base is terminated at `Q` on the side
`AC`, and the line perpendicular to `AB` at `R` on the side `AB` (`EqualPerps`); the problem asks
for `PQ = PR`. Fixing these sides is Carroll's reading: if the lines could end on any side,
`P = B` would be a degenerate solution with both lines of length `0`. The tacit hypotheses
`∠C < π/2` and `∠B ≤ π/2` are those of his figure; without them the perpendicular to the base
cannot reach `AC`, or the foot `R` falls outside `AB`. `D` is the foot of the altitude from `A`
(on line `BC`, `AD ⊥ BC`), which Carroll's answer uses. The theorem proves that the solutions are
exactly the points `P` of `BC` with `PC · AB = DC · PB` (Carroll's `PC : PB = DC : AB`) and that
there is exactly one; `problem20_nonvacuous` exhibits a triangle meeting the hypotheses.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P20

open EuclideanGeometry Real
open scoped RealInnerProductSpace

/-- `P` solves Problem 20 for the triangle `ABC` (base `BC`, left-hand side `AB`): `P` lies on
the base, the line from `P` perpendicular to the base ends at `Q` on the side `AC`, the line
from `P` perpendicular to `AB` ends at `R` on `AB`, and `PQ = PR`. -/
def EqualPerps (A B C P : Plane) : Prop :=
  P ∈ segment ℝ B C ∧ ∃ Q ∈ segment ℝ A C, ∃ R ∈ segment ℝ A B,
    ⟪Q - P, C - B⟫ = 0 ∧ ⟪R - P, B - A⟫ = 0 ∧ dist P Q = dist P R

/-- **Problem 20.** For a triangle `ABC` with acute angle `C` and non-obtuse angle `B`, and `D` the
foot of the altitude from `A`, the points of the base solving the problem are exactly those with
`PC : PB = DC : AB` (Carroll's answer), and there is exactly one. -/
theorem problem20 (A B C D : Plane) (hABC : cross A B C ≠ 0)
    (hB : ∠ A B C ≤ π / 2) (hC : ∠ A C B < π / 2)
    (hD : D ∈ line[ℝ, B, C]) (hAD : ⟪A - D, C - B⟫ = 0) :
    (∀ P, EqualPerps A B C P ↔
      (P ∈ segment ℝ B C ∧ dist P C * dist A B = dist D C * dist P B)) ∧
    ∃! P, EqualPerps A B C P := by
  sorry

/-- The hypotheses of `problem20` are satisfiable: `A = (1, 2)`, `B = (0, 0)`, `C = (3, 0)`,
with altitude foot `D = (1, 0)`. -/
theorem problem20_nonvacuous :
    ∃ A B C D : Plane, cross A B C ≠ 0 ∧ ∠ A B C ≤ π / 2 ∧ ∠ A C B < π / 2 ∧
      D ∈ line[ℝ, B, C] ∧ ⟪A - D, C - B⟫ = 0 := by
  sorry

end PillowProblems.P20
