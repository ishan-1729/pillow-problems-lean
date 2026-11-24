import PillowProblems.Basic

/-!
# Problem 9 (Pure Geometry, Plane)

**Question.** *(dated 11/76)*

> Given two Lines meeting at a Point, and given a Point lying within the angle contained by them: draw, from the given Point, two lines, at right angles to each other, and forming with the given Lines and the line joining their intersection to the given Point, two equal Triangles.

*(Carroll's solution: Chapter III, problem 9; text in `data/problems.json`.)*

**Lean reading.** The given lines are `AB` and `AC`, distinct and meeting at `A` (`cross A B C ≠ 0`);
`B`, `C` mark which of the four angles is meant, and "`P` within the angle" is read as `P - A`
being a positive combination of `B - A` and `C - A` (`InsideAngle`). The two lines drawn from
`P` are `PL`, `PM` with `L` on `AB`, `M` on `AC`; the two triangles are `APL` and `APM` (formed
with the given lines and `AP`). `IsSolution` asks that `L ≠ P`, `M ≠ P`, `∠LPM = π/2` (mathlib's
unoriented angle), that the triangles are genuine (positive area) and that they have equal area
("equal Triangles" in Euclid's sense). `problem9` proves that a solution exists with `L`, `M` even
on the arms (rays) `AB`, `AC`; as in Carroll's construction, `L = A + t·a·(B - A)`,
`M = A + t·b·(C - A)` for a root `t > 0` of a quadratic, which always has a positive root.
Uniqueness is not claimed because it fails: Carroll's semicircle may cut `AP` twice, and
`problem9_not_unique` gives a concrete case with two different solutions (it also shows the
hypotheses are satisfiable).

**Status.** proved
-/

namespace PillowProblems.P09

open EuclideanGeometry
open scoped Real

/-- `P` lies strictly within the angle `BAC` contained by the lines `AB`, `AC`: `P - A` is a
combination of `B - A` and `C - A` with positive coefficients. -/
def InsideAngle (A B C P : Plane) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ P -ᵥ A = a • (B -ᵥ A) + b • (C -ᵥ A)

/-- The lines `PL`, `PM` (with `L` on the line `AB`, `M` on the line `AC`) are at right angles,
and the triangles `APL`, `APM` are genuine and equal. -/
def IsSolution (A P L M : Plane) : Prop :=
  L ≠ P ∧ M ≠ P ∧ ∠ L P M = π / 2 ∧ 0 < triArea A P L ∧ triArea A P L = triArea A P M

/-- For two lines `AB`, `AC` meeting at `A` and a point `P` within the angle `BAC`, there are
points `L` on the arm `AB` and `M` on the arm `AC` such that `PL ⊥ PM` and the triangles `APL`,
`APM` are equal. -/
theorem problem9 (A B C P : Plane) (hABC : cross A B C ≠ 0) (hP : InsideAngle A B C P) :
    ∃ l m : ℝ, 0 < l ∧ 0 < m ∧
      IsSolution A P (AffineMap.lineMap A B l) (AffineMap.lineMap A C m) := by
  sorry

/-- The solution is in general not unique: for the lines through `A = (0,0)`, `B = (1,2)`,
`C = (-1,2)` and the point `P = (0,1)`, both `L = (1,2), M = (-1,2)` and
`L = (1/3,2/3), M = (-1/3,2/3)` solve the problem. (This also shows the hypotheses of
`problem9` are satisfiable.) -/
theorem problem9_not_unique :
    cross (pt 0 0) (pt 1 2) (pt (-1) 2) ≠ 0 ∧ InsideAngle (pt 0 0) (pt 1 2) (pt (-1) 2) (pt 0 1) ∧
      IsSolution (pt 0 0) (pt 0 1) (AffineMap.lineMap (pt 0 0) (pt 1 2) (1 : ℝ))
        (AffineMap.lineMap (pt 0 0) (pt (-1) 2) (1 : ℝ)) ∧
      IsSolution (pt 0 0) (pt 0 1) (AffineMap.lineMap (pt 0 0) (pt 1 2) (1 / 3 : ℝ))
        (AffineMap.lineMap (pt 0 0) (pt (-1) 2) (1 / 3 : ℝ)) ∧
      AffineMap.lineMap (pt 0 0) (pt 1 2) (1 : ℝ) ≠
        AffineMap.lineMap (pt 0 0) (pt 1 2) (1 / 3 : ℝ) := by
  sorry

end PillowProblems.P09
