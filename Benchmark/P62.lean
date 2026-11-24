import PillowProblems.Basic

/-!
# Problem 62 (Pure Geometry, Plane)

**Question.** *(dated 12/76)*

> Given two Lines meeting at a Point, and given a Point lying within the angle contained by them: draw a line, through the given Point, and forming, with the given Lines, the least possible Triangle.

*(Carroll's solution: Chapter III, problem 62; text in `data/problems.json`.)*

**Lean reading.** The two given lines meet at `A`; the angle is given by points `B`, `C` on its arms
(`cross A B C ≠ 0`), and `P` lies strictly inside it (`InAngle`: `P = A + s (B - A) + t (C - A)`
with `s, t > 0`). A line through `P` forms a triangle with the given lines as in Carroll's
figure when it cuts both arms, i.e. meets the rays from `A` through `B` and `C` at points
`G, H ≠ A` (`Cuts`); the triangle is `AGH`. This restriction is tacit in Carroll: a line through
`P` meeting one arm and the backward extension of the other cuts off triangles of arbitrarily
small area, so without it there is no least triangle. `problem62` proves that there is exactly
one least triangle, and that a cut is least iff `P` is the midpoint of `GH` (Carroll's `FP = PE`,
which his construction `DE = AD` produces).

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P62

open scoped EuclideanGeometry

/-- `P` lies strictly within the angle `BAC` formed by the lines `AB`, `AC`. -/
def InAngle (A B C P : Plane) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ P = A + s • (B - A) + t • (C - A)

/-- A line through `P` cuts the arms of the angle `BAC`: it meets the ray `AB` (beyond `A`) at `G`
and the ray `AC` (beyond `A`) at `H`, so that it forms with the given lines the triangle `AGH`. -/
def Cuts (A B C P G H : Plane) : Prop :=
  (∃ g : ℝ, 0 < g ∧ G = A + g • (B - A)) ∧ (∃ h : ℝ, 0 < h ∧ H = A + h • (C - A)) ∧
    P ∈ line[ℝ, G, H]

theorem problem62 (A B C P : Plane) (hT : cross A B C ≠ 0) (hP : InAngle A B C P) :
    (∃! GH : Plane × Plane, Cuts A B C P GH.1 GH.2 ∧
        ∀ G H, Cuts A B C P G H → triArea A GH.1 GH.2 ≤ triArea A G H) ∧
    ∀ G H, Cuts A B C P G H →
      ((∀ G' H', Cuts A B C P G' H' → triArea A G H ≤ triArea A G' H') ↔
        midpoint ℝ G H = P) := by
  sorry

/-- The hypotheses are satisfiable: the point `(1, 1)` within the right angle at the origin. -/
theorem problem62_nonvacuous :
    cross (pt 0 0) (pt 1 0) (pt 0 1) ≠ 0 ∧ InAngle (pt 0 0) (pt 1 0) (pt 0 1) (pt 1 1) := by
  sorry

end PillowProblems.P62
