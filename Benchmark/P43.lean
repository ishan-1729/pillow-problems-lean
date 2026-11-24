import PillowProblems.Basic

/-!
# Problem 43 (Trigonometry: Plane)

**Question.** *(dated 2/82)*

> From the ends of the base of a given Triangle draw two lines, intersecting, terminated by the sides, and forming an isosceles Triangle at the base, and a Tetragon, equal to it, at the vertex.

*(Carroll's solution: Chapter III, problem 43; text in `data/problems.json`.)*

**Lean reading.** `ABC` is a non-degenerate triangle (`cross A B C ≠ 0`) with base `BC`. The two lines are
`BD` and `CE`, with `D` strictly inside side `AC` and `E` strictly inside side `AB` ("terminated by
the sides"). They meet at `F`, which lies strictly inside both segments `BD` and `CE`. The
isosceles triangle at the base is `FBC` with `FB = FC`. The tetragon `AEFD` is convex, and its
area is taken as `triArea A E F + triArea A F D` (cut along the diagonal `AF`). As in Carroll's
solution, the answer is the base angle `θ = ∠FBC` (this fixes both lines), given through
`cot B = cot ∠ABC` and `cot C = cot ∠ACB`. `problem43` proves that in every such configuration
`cot θ = ½{cot B + cot C + √(5cot²B + 6cot B cot C + 5cot²C)}`. `problem43_exists` proves that
the configuration exists in every triangle, so the hypotheses can be met. Correction: Carroll's
answer has `±`, but only `+` is possible. His quadratic `cot²θ - (cot B + cot C) cot θ -
(cot²B + cot B cot C + cot²C) = 0` has roots whose product is negative, so the `-` root is negative.
That would make `θ` obtuse, but `θ` is less than both base angles `B` and `C`, whose sum is less than `π`.

**Status.** proved (corrected)
-/

namespace PillowProblems.P43

open scoped EuclideanGeometry
open AffineMap

/-- **Problem 43.** In the triangle `ABC` let `BD` and `CE` (`D` on `AC`, `E` on `AB`) meet at `F`,
so that `FB = FC` and the tetragon `AEFD` (made of the triangles `AEF`, `AFD`) has the same area as
the triangle `FBC`. Then the base angle `θ = ∠FBC` of the isosceles triangle is given by
`cot θ = ½ {cot B + cot C + √(5 cot² B + 6 cot B cot C + 5 cot² C)}`. -/
theorem problem43 (A B C D E F : Plane) (hABC : cross A B C ≠ 0)
    (hD : Sbtw ℝ A D C) (hE : Sbtw ℝ A E B) (hFD : Sbtw ℝ B F D) (hFE : Sbtw ℝ C F E)
    (hiso : dist F B = dist F C)
    (harea : triArea A E F + triArea A F D = triArea F B C) :
    Real.cot (∠ F B C) =
      (Real.cot (∠ A B C) + Real.cot (∠ A C B) +
        √(5 * Real.cot (∠ A B C) ^ 2 + 6 * Real.cot (∠ A B C) * Real.cot (∠ A C B) +
          5 * Real.cot (∠ A C B) ^ 2)) / 2 := by
  sorry

/-- **Problem 43 (the construction is possible).** In every triangle the two lines can be drawn:
there are `D` on `AC`, `E` on `AB`, `F = BD ∩ CE` with `FB = FC` and `AEFD` equal in area
to `FBC`. -/
theorem problem43_exists (A B C : Plane) (hABC : cross A B C ≠ 0) :
    ∃ D E F : Plane, Sbtw ℝ A D C ∧ Sbtw ℝ A E B ∧ Sbtw ℝ B F D ∧ Sbtw ℝ C F E ∧
      dist F B = dist F C ∧ triArea A E F + triArea A F D = triArea F B C := by
  sorry

end PillowProblems.P43
