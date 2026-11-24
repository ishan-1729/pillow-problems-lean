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

private lemma dist_sq_eq (X Y : Space) : dist X Y ^ 2 = sq3 X Y := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [sq3, Real.dist_eq, sq_abs]

/-- The Gram determinant of three vectors `u, v, w`, written through the six squared distances
`|u|², |v|², |w|², |u - v|², |v - w|², |u - w|²`. -/
private noncomputable def gram (uu vv ww uv' vw' uw' : ℝ) : ℝ :=
  uu * vv * ww + 2 * ((uu + vv - uv') / 2) * ((vv + ww - vw') / 2) * ((uu + ww - uw') / 2)
    - uu * ((vv + ww - vw') / 2) ^ 2 - vv * ((uu + ww - uw') / 2) ^ 2
    - ww * ((uu + vv - uv') / 2) ^ 2

private lemma triple_sq (X Y Z W : Space) :
    triple X Y Z W ^ 2 =
      gram (sq3 X Y) (sq3 X Z) (sq3 X W) (sq3 Y Z) (sq3 Z W) (sq3 Y W) := by
  simp only [triple, gram, sq3]
  ring

private lemma abs_triple {X Y Z W : Space} {s : ℝ} (h : triple X Y Z W ^ 2 = s ^ 6 / 2) :
    |triple X Y Z W| = √(s ^ 6 / 2) := by
  rw [← h, Real.sqrt_sq_eq_abs]

/-- **Problem 49.** The square pyramid whose four lateral faces are equilateral triangles has
twice the volume of the regular tetrahedron made of the same triangles. -/
theorem problem49 (A B C D E P Q R S : Space) (hsq : IsSquare A B C D)
    (hEA : dist E A = dist A B) (hEB : dist E B = dist A B) (hEC : dist E C = dist A B)
    (hED : dist E D = dist A B)
    (hPQ : dist P Q = dist A B) (hPR : dist P R = dist A B) (hPS : dist P S = dist A B)
    (hQR : dist Q R = dist A B) (hQS : dist Q S = dist A B) (hRS : dist R S = dist A B) :
    tetVol P Q R S ≠ 0 ∧ pyramidVol E A B C D / tetVol P Q R S = 2 := by
  obtain ⟨hAB, hABC, hinn, hD⟩ := hsq
  set s := dist A B with hs
  have spos : 0 < s := dist_pos.mpr hAB
  have e : ∀ {X Y : Space}, dist X Y = s → sq3 X Y = s ^ 2 := by
    intro X Y h; rw [← dist_sq_eq, h]
  have hDi : ∀ i, D i = A i + C i - B i := fun i => by rw [hD]; simp
  have hin : (A 0 - B 0) * (C 0 - B 0) + (A 1 - B 1) * (C 1 - B 1)
      + (A 2 - B 2) * (C 2 - B 2) = 0 := by
    rw [← hinn]; simp [PiLp.inner_apply, Fin.sum_univ_three]; ring
  have sAB : sq3 A B = s ^ 2 := e rfl
  have sBC : sq3 B C = s ^ 2 := e hABC.symm
  have sAC : sq3 A C = 2 * s ^ 2 := by
    have : sq3 A C = sq3 A B + sq3 B C - 2 * ((A 0 - B 0) * (C 0 - B 0)
        + (A 1 - B 1) * (C 1 - B 1) + (A 2 - B 2) * (C 2 - B 2)) := by
      simp only [sq3]; ring
    rw [this, sAB, sBC, hin]; ring
  have sCD : sq3 C D = s ^ 2 := by
    rw [← sAB]; simp only [sq3, hDi]; ring
  have sAD : sq3 A D = s ^ 2 := by
    rw [← sBC]; simp only [sq3, hDi]; ring
  have t1 : triple E A B C ^ 2 = s ^ 6 / 2 := by
    rw [triple_sq, e hEA, e hEB, e hEC, sAB, sBC, sAC]; simp only [gram]; ring
  have t2 : triple E A C D ^ 2 = s ^ 6 / 2 := by
    rw [triple_sq, e hEA, e hEC, e hED, sAC, sCD, sAD]; simp only [gram]; ring
  have t3 : triple P Q R S ^ 2 = s ^ 6 / 2 := by
    rw [triple_sq, e hPQ, e hPR, e hPS, e hQR, e hRS, e hQS]; simp only [gram]; ring
  have kpos : 0 < √(s ^ 6 / 2) := Real.sqrt_pos.mpr (by positivity)
  have hT : tetVol P Q R S = √(s ^ 6 / 2) / 6 := by rw [tetVol, abs_triple t3]
  have hP : pyramidVol E A B C D = 2 * (√(s ^ 6 / 2) / 6) := by
    rw [pyramidVol, tetVol, tetVol, abs_triple t1, abs_triple t2]; ring
  refine ⟨by rw [hT]; positivity, ?_⟩
  rw [hP, hT]
  field_simp

/-- The point `(x, y, z)` of space. -/
noncomputable def sp (x y z : ℝ) : Space := !₂[x, y, z]

private lemma dist_sp {x y z x' y' z' : ℝ}
    (h : (x - x') ^ 2 + (y - y') ^ 2 + (z - z') ^ 2 = 1) :
    dist (sp x y z) (sp x' y' z') = 1 := by
  rw [← Real.sqrt_sq (dist_nonneg), dist_sq_eq, ← Real.sqrt_one, ← h]
  rfl

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
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hAB : dist (sp 0 0 0) (sp 1 0 0) = 1 := dist_sp (by norm_num)
  rw [hAB]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, dist_sp (by linear_combination h2 / 4),
    dist_sp (by linear_combination h2 / 4), dist_sp (by linear_combination h2 / 4),
    dist_sp (by linear_combination h2 / 4), rfl, dist_sp (by linear_combination h3 / 4),
    dist_sp (by linear_combination h3 / 36 + h6 / 9), dist_sp (by linear_combination h3 / 4),
    dist_sp (by linear_combination h3 / 36 + h6 / 9),
    dist_sp (by linear_combination h3 / 9 + h6 / 9)⟩
  · intro h; rw [h, dist_self] at hAB; exact zero_ne_one hAB
  · rw [hAB]; exact (dist_sp (by norm_num)).symm
  · simp [sp, PiLp.inner_apply, Fin.sum_univ_three]
  · ext i; fin_cases i <;> simp [sp]

end PillowProblems.P49
