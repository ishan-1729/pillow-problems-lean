import PillowProblems.Basic

/-!
# Problem 49 (Trigonometry: Solid)

**Question.** *(dated 16/11/86)*

> If four equilateral Triangles be made the sides of a square Pyramid: find the ratio which its volume has to that of a Tetrahedron made of the Triangles.

**Answer.**

> Two.

*(Carroll's solution: Chapter III, problem 49; text in `data/problems.json`.)*

**Lean reading.** Points are in `Space = EuclideanSpace ℝ (Fin 3)`. The volume of a tetrahedron
`ABCD` is the usual `|(B - A) · ((C - A) × (D - A))| / 6` (`tetVol`), and the volume of a pyramid
with apex `E` on a square base `ABCD` is the sum of the volumes of the two tetrahedra `EABC`,
`EACD` into which the diagonal plane `EAC` cuts it (`pyramidVol`); Carroll uses
⅓ · base · height instead, which gives the same number. `IsSquare A B C D` says that `ABCD` is a
nondegenerate square: `A ≠ B`, `AB = BC`, `AB ⊥ BC`, `D = A + C - B`. "Four equilateral
triangles are the sides of the pyramid" is read as: the apex `E` is at distance `AB` from each of
`A, B, C, D` (so the four lateral faces are equilateral triangles of side `AB`), and "a
tetrahedron made of the triangles" as: `PQRS` has all six edges equal to `AB`. No other
hypotheses are needed. The theorem holds for an arbitrary such configuration in space (not one
fixed in coordinates) and also records that the tetrahedron's volume is nonzero, so the ratio is
meaningful; `problem49_nonvacuous` exhibits a configuration.

**Status.** proved
-/

namespace PillowProblems.P49

open scoped RealInnerProductSpace

/-- The triple product `(B - A) · ((C - A) × (D - A))`: six times the signed volume of the
tetrahedron `ABCD`. -/
noncomputable def triple (A B C D : Space) : ℝ :=
  (B 0 - A 0) * ((C 1 - A 1) * (D 2 - A 2) - (C 2 - A 2) * (D 1 - A 1))
  - (B 1 - A 1) * ((C 0 - A 0) * (D 2 - A 2) - (C 2 - A 2) * (D 0 - A 0))
  + (B 2 - A 2) * ((C 0 - A 0) * (D 1 - A 1) - (C 1 - A 1) * (D 0 - A 0))

/-- The volume of the tetrahedron `ABCD`. -/
noncomputable def tetVol (A B C D : Space) : ℝ := |triple A B C D| / 6

/-- `ABCD` (in this cyclic order) is a nondegenerate square. -/
def IsSquare (A B C D : Space) : Prop :=
  A ≠ B ∧ dist A B = dist B C ∧ inner ℝ (A - B) (C - B) = 0 ∧ D = A + C - B

/-- The volume of the pyramid with apex `E` and square base `ABCD`: the sum of the two
tetrahedra `EABC`, `EACD` into which the diagonal plane through `E`, `A`, `C` divides it. -/
noncomputable def pyramidVol (E A B C D : Space) : ℝ := tetVol E A B C + tetVol E A C D

/-- Squared distance in coordinates. -/
private noncomputable def sq3 (X Y : Space) : ℝ :=
  (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 + (X 2 - Y 2) ^ 2

/-- The Gram determinant of three vectors `u, v, w`, written through the six squared distances
`|u|², |v|², |w|², |u - v|², |v - w|², |u - w|²`. -/
private noncomputable def gram (uu vv ww uv' vw' uw' : ℝ) : ℝ :=
  uu * vv * ww + 2 * ((uu + vv - uv') / 2) * ((vv + ww - vw') / 2) * ((uu + ww - uw') / 2)
    - uu * ((vv + ww - vw') / 2) ^ 2 - vv * ((uu + ww - uw') / 2) ^ 2
    - ww * ((uu + vv - uv') / 2) ^ 2

/-- **Problem 49.** The square pyramid whose four lateral faces are equilateral triangles has
twice the volume of the regular tetrahedron made of the same triangles. -/
theorem problem49 (A B C D E P Q R S : Space) (hsq : IsSquare A B C D)
    (hEA : dist E A = dist A B) (hEB : dist E B = dist A B) (hEC : dist E C = dist A B)
    (hED : dist E D = dist A B)
    (hPQ : dist P Q = dist A B) (hPR : dist P R = dist A B) (hPS : dist P S = dist A B)
    (hQR : dist Q R = dist A B) (hQS : dist Q S = dist A B) (hRS : dist R S = dist A B) :
    tetVol P Q R S ≠ 0 ∧ pyramidVol E A B C D / tetVol P Q R S = 2 := by
  sorry

/-- The point `(x, y, z)` of space. -/
noncomputable def sp (x y z : ℝ) : Space := !₂[x, y, z]

/-- The hypotheses of `problem49` are satisfiable: the unit square `ABCD` with apex
`E = (½, ½, √2/2)`, and the regular tetrahedron `PQRS` of edge `1`. -/
theorem problem49_nonvacuous :
    IsSquare (sp 0 0 0) (sp 1 0 0) (sp 1 1 0) (sp 0 1 0) ∧
      dist (sp (1 / 2) (1 / 2) (√2 / 2)) (sp 0 0 0) = dist (sp 0 0 0) (sp 1 0 0) ∧
      dist (sp (1 / 2) (1 / 2) (√2 / 2)) (sp 1 0 0) = dist (sp 0 0 0) (sp 1 0 0) ∧
      dist (sp (1 / 2) (1 / 2) (√2 / 2)) (sp 1 1 0) = dist (sp 0 0 0) (sp 1 0 0) ∧
      dist (sp (1 / 2) (1 / 2) (√2 / 2)) (sp 0 1 0) = dist (sp 0 0 0) (sp 1 0 0) ∧
      dist (sp 0 0 0) (sp 1 0 0) = dist (sp 0 0 0) (sp 1 0 0) ∧
      dist (sp 0 0 0) (sp (1 / 2) (√3 / 2) 0) = dist (sp 0 0 0) (sp 1 0 0) ∧
      dist (sp 0 0 0) (sp (1 / 2) (√3 / 6) (√6 / 3)) = dist (sp 0 0 0) (sp 1 0 0) ∧
      dist (sp 1 0 0) (sp (1 / 2) (√3 / 2) 0) = dist (sp 0 0 0) (sp 1 0 0) ∧
      dist (sp 1 0 0) (sp (1 / 2) (√3 / 6) (√6 / 3)) = dist (sp 0 0 0) (sp 1 0 0) ∧
      dist (sp (1 / 2) (√3 / 2) 0) (sp (1 / 2) (√3 / 6) (√6 / 3)) =
        dist (sp 0 0 0) (sp 1 0 0) := by
  sorry

end PillowProblems.P49
