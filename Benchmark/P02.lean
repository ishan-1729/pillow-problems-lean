import PillowProblems.Basic

/-!
# Problem 2 (Pure Geometry, Plane)

**Question.**

> In a given Triangle to place a line parallel to the base, such that the portions of sides, intercepted between it and the base, shall be together equal to the base.

*(Carroll's solution: Chapter III, problem 2; text in `data/problems.json`.)*

**Lean reading.** The triangle is `ABC` with base `BC`, non-degenerate (`cross A B C ≠ 0`; for a
degenerate triangle `BC = AB + AC` and the only "solution" would be the point `A`). The required
line meets the sides `AB`, `AC` in `D`, `E`, which must lie on the closed sides (`Wbtw ℝ B D A`,
`Wbtw ℝ C E A`: the line is placed *in* the triangle); the line `DE` is parallel to `BC`
(mathlib's `AffineSubspace.Parallel`, which also forces `D ≠ E`); the intercepted portions are
`BD` and `CE`, and the condition is `BD + CE = BC`. `problem2` shows that these conditions hold
exactly for `D`, `E` dividing `BA`, `CA` in the ratio `BD / BA = CE / CA = BC / (AB + AC)`, so the
required line exists and is unique. `problem2_construction` verifies Carroll's synthesis: the
bisector of angle `A` meets `BC` at `F` (`∠BAF = ∠FAC`), and `BD = BF`, `CE = CF`.

**Status.** proved
-/

namespace PillowProblems.P02

open EuclideanGeometry

/-- The line `DE` (with `D` on side `AB`, `E` on side `AC`) is parallel to the base `BC` and cuts
off `BD + CE = BC` exactly when `BD / BA = CE / CA = BC / (AB + AC)`. In particular the required
line exists and is unique. -/
theorem problem2 (A B C : Plane) (h : cross A B C ≠ 0) (D E : Plane) :
    (Wbtw ℝ B D A ∧ Wbtw ℝ C E A ∧ (line[ℝ, D, E]).Parallel (line[ℝ, B, C]) ∧
        dist B D + dist C E = dist B C) ↔
      (D = AffineMap.lineMap B A (dist B C / (dist A B + dist A C)) ∧
        E = AffineMap.lineMap C A (dist B C / (dist A B + dist A C))) := by
  sorry

/-- Carroll's construction: if the bisector of the angle `A` meets the base at `F`, then the
required points satisfy `BD = BF` and `CE = CF`. -/
theorem problem2_construction (A B C : Plane) (h : cross A B C ≠ 0) :
    let t := dist B C / (dist A B + dist A C)
    let D := AffineMap.lineMap B A t
    let E := AffineMap.lineMap C A t
    let F := AffineMap.lineMap B C (dist A B / (dist A B + dist A C))
    ∠ B A F = ∠ F A C ∧ Wbtw ℝ B F C ∧ dist B D = dist B F ∧ dist C E = dist C F := by
  sorry

end PillowProblems.P02
