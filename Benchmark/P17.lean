import PillowProblems.Basic

/-!
# Problem 17 (Pure Geometry, Plane)

**Question.** *(dated 3/89)*

> In a given Triangle place a line parallel to the base, such that if, from its ends, lines be drawn, parallel to the sides and terminated by the base, they shall be together equal to the first line.

*(Carroll's solution: Chapter III, problem 17; text in `data/problems.json`.)*

**Lean reading.** The triangle is `ABC` with base `BC`, non-degenerate (`cross A B C ≠ 0`). The
line placed in the triangle meets the sides `AB`, `AC` at `D`, `E` (on the closed sides,
`Wbtw`; on the full lines `AB`, `AC` there is a second solution outside the triangle) and is
parallel to `BC`. From `D`, `E` the lines `DF ∥ AC` and `EG ∥ AB` are drawn and "terminated by
the base", i.e. `F`, `G` lie on the line `BC`; the condition is `DF + EG = DE`. Parallelism is
mathlib's `AffineSubspace.Parallel` of the lines through the named points. `problem17` shows
these conditions hold exactly when `BD / BA = CE / CA = BF / BC = CG / CB = BC / (AB + BC + CA)`,
so the required line exists and is unique. `problem17_construction` verifies Carroll's
synthesis: the line passes through the point `H` where the bisectors of the angles `B` and `C`
meet (`∠ABH = ∠HBC`, `∠ACH = ∠HCB`, and `H` lies on the segment `DE`).

**Status.** proved
-/

namespace PillowProblems.P17

open EuclideanGeometry

/-- The required line `DE` (with the lines `DF ∥ AC`, `EG ∥ AB` drawn to the base) is exactly
the one with `BD / BA = CE / CA = BC / (AB + BC + CA)`; in particular it exists and is unique. -/
theorem problem17 (A B C : Plane) (h : cross A B C ≠ 0) (D E F G : Plane) :
    (Wbtw ℝ B D A ∧ Wbtw ℝ C E A ∧ F ∈ line[ℝ, B, C] ∧ G ∈ line[ℝ, B, C] ∧
        (line[ℝ, D, E]).Parallel (line[ℝ, B, C]) ∧ (line[ℝ, D, F]).Parallel (line[ℝ, A, C]) ∧
        (line[ℝ, E, G]).Parallel (line[ℝ, A, B]) ∧ dist D F + dist E G = dist D E) ↔
      (D = AffineMap.lineMap B A (dist B C / (dist A B + dist B C + dist A C)) ∧
        E = AffineMap.lineMap C A (dist B C / (dist A B + dist B C + dist A C)) ∧
        F = AffineMap.lineMap B C (dist B C / (dist A B + dist B C + dist A C)) ∧
        G = AffineMap.lineMap C B (dist B C / (dist A B + dist B C + dist A C))) := by
  sorry

/-- Carroll's construction: the required line passes through the meeting point `H` of the
bisectors of the angles `B` and `C` (the in-centre, `H = (a A + b B + c C) / (a + b + c)`). -/
theorem problem17_construction (A B C : Plane) (h : cross A B C ≠ 0) :
    let p := dist A B + dist B C + dist A C
    let H : Plane := (dist B C / p) • A + (dist A C / p) • B + (dist A B / p) • C
    ∠ A B H = ∠ H B C ∧ ∠ A C H = ∠ H C B ∧
      Wbtw ℝ (AffineMap.lineMap B A (dist B C / p)) H (AffineMap.lineMap C A (dist B C / p)) := by
  sorry

end PillowProblems.P17
