import PillowProblems.Basic

/-!
# Problem 36 (Pure Geometry, Plane)

**Question.** *(dated 3/89)*

> In a given Triangle, to draw a line, from a Point on one side of it, to a Point on the other side, perpendicular to one of these sides, and equal to the sum of the portions, of these sides, intercepted between it and the base.

*(Carroll's solution: Chapter III, problem 36; text in `data/problems.json`.)*

**Lean reading.** `A B C` is a non-collinear triangle with base `BC`. The required line runs from `C'` on the
side `AB` to `B'` on the side `AC` (closed segments). As in Carroll's analysis it is perpendicular
to `AB` (right angle at `C'`); a line perpendicular to `AC` is the same statement with `B` and `C`
exchanged. The portions of the sides intercepted between it and the base are `BC'` and `CB'`.
`problem36` shows that such a line has the property iff `AB' = (AB + AC)/(1 + sin A + cos A)` and
`AC' = (AB + AC) cos A/(1 + sin A + cos A)`, so the line is unique. This is the position of
the line through Carroll's point `D`; his construction by the bisector of `∠ACE` and the `45°` line
at `B` is not itself formalized. `problem36_limits` proves Carroll's limits of possibility exactly:
the line exists iff `A ≤ 90°`, `B ≥ 45°` and `C ≥ 45° - A/2`. When `A = 90°` the line degenerates
into a piece of `AC`, with `C' = A`.

**Status.** proved
-/

namespace PillowProblems.P36

open scoped EuclideanGeometry RealInnerProductSpace
open Real

/-- **Problem 36.** In a triangle `ABC` (base `BC`), let `C'` be a point of the side `AB` and `B'`
a point of the side `AC` with `B'C'` perpendicular to `AB`. Then `B'C'` equals the sum `BC' + CB'`
of the portions of the sides intercepted between it and the base if and only if
`AB' = (AB + AC) / (1 + sin A + cos A)` and `AC' = (AB + AC) cos A / (1 + sin A + cos A)`; so
there is at most one such line. -/
theorem problem36 (A B C : Plane) (hABC : ¬ Collinear ℝ {A, B, C}) (C' B' : Plane)
    (hC' : C' ∈ segment ℝ A B) (hB' : B' ∈ segment ℝ A C) (hperp : ⟪B' - C', B - A⟫ = 0) :
    dist B' C' = dist B C' + dist C B' ↔
      dist A B' = (dist A B + dist A C) / (1 + sin (∠ B A C) + cos (∠ B A C)) ∧
      dist A C' =
        (dist A B + dist A C) * cos (∠ B A C) / (1 + sin (∠ B A C) + cos (∠ B A C)) := by
  sorry

/-- **Problem 36, limits of possibility.** Such a line exists if and only if `A ≤ 90°`,
`B ≥ 45°` and `C ≥ 45° - A/2`, as Carroll states. -/
theorem problem36_limits (A B C : Plane) (hABC : ¬ Collinear ℝ {A, B, C}) :
    (∃ C' B' : Plane, C' ∈ segment ℝ A B ∧ B' ∈ segment ℝ A C ∧ ⟪B' - C', B - A⟫ = 0 ∧
        dist B' C' = dist B C' + dist C B') ↔
      ∠ B A C ≤ π / 2 ∧ π / 4 ≤ ∠ A B C ∧ π / 4 - ∠ B A C / 2 ≤ ∠ A C B := by
  sorry

end PillowProblems.P36
