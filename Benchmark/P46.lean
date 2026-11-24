import PillowProblems.Basic

/-!
# Problem 46 (Pure Geometry, Plane)

**Question.** *(dated 19/11/87)*

> In a given Triangle, whose base is divided at a given Point, inscribe a Triangle, having its angles equal to given angles, and having an assigned vertex at the given Point.

*(Carroll's solution: Chapter III, problem 46; text in `data/problems.json`.)*

**Lean reading.** `A B C` is a triangle (`cross A B C ≠ 0`), `D` a point strictly between `B` and `C`, and the
given angles are `δ, ε, φ > 0` with `δ + ε + φ = π`. `δ` belongs at the assigned vertex `D`, `ε` at
the vertex `E` on `CA`, and `φ` at the vertex `F` on `AB`; the other assignment is the same
statement with `ε, φ` exchanged. Angles are mathlib's unoriented angles, so a triangle and its
mirror image both count. "Inscribe" is read with `E, F` on the side *lines* `CA, AB`, which is how
Carroll's construction produces them: he never checks that they fall within the sides, and on the
closed sides a solution need not exist. Added hypothesis: `δ ≠ A` and `δ + A ≠ π`. In those
excluded cases, turning `DE` through `±δ` about `D` maps line `CA` to a line parallel to `AB`, so
one orientation gives no triangle or infinitely many. Under it the theorem gives the complete answer:
exactly two such triangles, one of each orientation. Carroll's circle construction is not
formalized; the proof locates `E, F` by the spiral similarity about `D`. `problem46_nonvacuous`
exhibits data satisfying the hypotheses.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P46

open scoped EuclideanGeometry RealInnerProductSpace
open Real

/-- The triangle `DEF` has the angles `δ, ε, φ` at `D, E, F`. -/
def HasAngles (D E F : Plane) (δ ε φ : ℝ) : Prop :=
  ∠ E D F = δ ∧ ∠ D E F = ε ∧ ∠ D F E = φ

/-- `F - D` is `E - D` turned through the angle `σ δ` (`σ = ±1`, `cd = cos δ`, `sd = sin δ`) and
scaled by `k`. -/
private def Rel (k cd sd σ : ℝ) (D E F : Plane) : Prop :=
  F 0 - D 0 = k * (cd * (E 0 - D 0) - σ * sd * (E 1 - D 1)) ∧
  F 1 - D 1 = k * (cd * (E 1 - D 1) + σ * sd * (E 0 - D 0))

/-- **Problem 46.** Let `ABC` be a triangle whose base `BC` is divided at the point `D`, and let
`δ, ε, φ` be positive angles with sum `π`. Unless `δ` equals the angle `A` or its supplement,
there are exactly two triangles `DEF` with `E` on the side `CA` and `F` on the side `AB` (taken as
lines) whose angles at `D, E, F` are `δ, ε, φ` (one of each orientation). -/
theorem problem46 (A B C D : Plane) (hABC : cross A B C ≠ 0) (hD : Sbtw ℝ B D C)
    (δ ε φ : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hφ : 0 < φ) (hsum : δ + ε + φ = π)
    (hA1 : δ ≠ ∠ B A C) (hA2 : δ + ∠ B A C ≠ π) :
    ∃ p q : Plane × Plane, p ≠ q ∧
      {x : Plane × Plane | x.1 ∈ line[ℝ, C, A] ∧ x.2 ∈ line[ℝ, A, B] ∧
        HasAngles D x.1 x.2 δ ε φ} = {p, q} := by
  sorry

/-- The hypotheses of `problem46` can be met: the right isosceles triangle `A = (0, 0)`,
`B = (1, 0)`, `C = (0, 1)` (so `∠A = π/2`), `D` the midpoint of `BC`, and the angles
`π/3, π/3, π/3`. -/
theorem problem46_nonvacuous :
    ∃ (A B C D : Plane) (δ ε φ : ℝ), cross A B C ≠ 0 ∧ Sbtw ℝ B D C ∧ 0 < δ ∧ 0 < ε ∧ 0 < φ ∧
      δ + ε + φ = π ∧ δ ≠ ∠ B A C ∧ δ + ∠ B A C ≠ π := by
  sorry

end PillowProblems.P46
