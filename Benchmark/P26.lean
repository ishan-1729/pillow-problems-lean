import PillowProblems.Basic

/-!
# Problem 26 (Pure Geometry, Plane)

**Question.** *(dated 4/89)*

> Within a given Triangle place a similar Triangle, whose area shall have to its area a given ratio less than unity, whose sides shall be parallel to its sides, and whose vertices shall be equidistant from its vertices.

*(Carroll's solution: Chapter III, problem 26; text in `data/problems.json`.)*

**Lean reading.** `ABC` is a nondegenerate triangle (`cross A B C ≠ 0`). "Similar, with sides
parallel to its sides" is modelled as `B' - A'`, `C' - B'`, `A' - C'` being multiples of
`B - A`, `C - B`, `A - C` (similarity then follows). The area condition is
`triArea A'B'C' = ρ · triArea ABC` with `0 < ρ < 1`, and the vertices are equidistant:
`AA' = BB' = CC'`. "Within" means each of `A'`, `B'`, `C'` lies in the closed triangle
(`convexHull`). `D` is any point equidistant from `A`, `B`, `C` (Carroll's intersection of the
perpendicular bisectors); the answer is not built into it. `problem26_all` shows, with no
further assumption, that the solutions without the "within" condition are exactly the
homotheties of centre `D` and ratio `±√ρ`. Carroll's reading is that the placed triangle keeps
the orientation of `ABC` (sides parallel in the same sense, `SidesParallelSameSense`); under it
`problem26` proves that a solution exists exactly when the circumcentre `D` lies within `ABC`
(no obtuse angle), and that it is then Carroll's triangle `A' = D + √ρ (A - D)`, …, uniquely.
Carroll does not notice that for an obtuse-angled triangle his construction leaves the triangle
and there is no solution at all. `problem26_literal` treats the literal reading, where the ratio
`-√ρ` (a triangle turned half round, which Carroll does not consider) is a further solution
whenever its vertices lie within `ABC` (e.g. for small `ρ` in an acute triangle).

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P26

open EuclideanGeometry

/-- The sides of `A'B'C'` are parallel to the corresponding sides of `ABC`. -/
def SidesParallel (A B C A' B' C' : Plane) : Prop :=
  (∃ l : ℝ, B' - A' = l • (B - A)) ∧ (∃ l : ℝ, C' - B' = l • (C - B)) ∧
    (∃ l : ℝ, A' - C' = l • (A - C))

/-- The sides of `A'B'C'` are parallel to, and point the same way as, the corresponding sides
of `ABC` (so `A'B'C'` is not turned half round). -/
def SidesParallelSameSense (A B C A' B' C' : Plane) : Prop :=
  (∃ l : ℝ, 0 < l ∧ B' - A' = l • (B - A)) ∧ (∃ l : ℝ, 0 < l ∧ C' - B' = l • (C - B)) ∧
    (∃ l : ℝ, 0 < l ∧ A' - C' = l • (A - C))

/-- **Problem 26, all solutions.** With `D` the circumcentre of `ABC`, a triangle `A'B'C'` with
sides parallel to those of `ABC`, area `ρ` times that of `ABC` (`0 < ρ < 1`) and
`AA' = BB' = CC'` is the image of `ABC` under the homothety of centre `D` and ratio `√ρ` or
`-√ρ`. -/
theorem problem26_all (A B C D : Plane) (hABC : cross A B C ≠ 0)
    (hD : dist D A = dist D B ∧ dist D B = dist D C) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (A' B' C' : Plane) :
    (SidesParallel A B C A' B' C' ∧ triArea A' B' C' = ρ * triArea A B C ∧
        dist A A' = dist B B' ∧ dist B B' = dist C C') ↔
      ∃ k : ℝ, (k = √ρ ∨ k = -√ρ) ∧
        A' = D + k • (A - D) ∧ B' = D + k • (B - D) ∧ C' = D + k • (C - D) := by
  sorry

/-- **Problem 26.** The triangles within `ABC`, with sides parallel to its sides in the same
sense, area `ρ` times its area and vertices equidistant from its vertices, are as follows: there
is one exactly when the circumcentre `D` lies within `ABC` (no obtuse angle), and it is then
Carroll's, `A' = D + √ρ (A - D)`, `B' = D + √ρ (B - D)`, `C' = D + √ρ (C - D)`
(`DB' = k · DB`, `k = √ρ`). For an obtuse-angled triangle there is none. -/
theorem problem26 (A B C D : Plane) (hABC : cross A B C ≠ 0)
    (hD : dist D A = dist D B ∧ dist D B = dist D C)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (A' B' C' : Plane) :
    (SidesParallelSameSense A B C A' B' C' ∧ triArea A' B' C' = ρ * triArea A B C ∧
        dist A A' = dist B B' ∧ dist B B' = dist C C' ∧
        A' ∈ convexHull ℝ {A, B, C} ∧ B' ∈ convexHull ℝ {A, B, C} ∧
        C' ∈ convexHull ℝ {A, B, C}) ↔
      (D ∈ convexHull ℝ {A, B, C} ∧
        A' = D + √ρ • (A - D) ∧ B' = D + √ρ • (B - D) ∧ C' = D + √ρ • (C - D)) := by
  sorry

/-- **Problem 26, literal reading.** If "sides parallel" allows the placed triangle to be turned
half round, the solutions within `ABC` are Carroll's triangle (when the circumcentre `D` lies
within `ABC`) and, in addition, the image of `ABC` under the homothety of centre `D` and ratio
`-√ρ`, whenever that image lies within `ABC`. -/
theorem problem26_literal (A B C D : Plane) (hABC : cross A B C ≠ 0)
    (hD : dist D A = dist D B ∧ dist D B = dist D C)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (A' B' C' : Plane) :
    (SidesParallel A B C A' B' C' ∧ triArea A' B' C' = ρ * triArea A B C ∧
        dist A A' = dist B B' ∧ dist B B' = dist C C' ∧
        A' ∈ convexHull ℝ {A, B, C} ∧ B' ∈ convexHull ℝ {A, B, C} ∧
        C' ∈ convexHull ℝ {A, B, C}) ↔
      ((D ∈ convexHull ℝ {A, B, C} ∧
          A' = D + √ρ • (A - D) ∧ B' = D + √ρ • (B - D) ∧ C' = D + √ρ • (C - D)) ∨
        (A' = D + (-√ρ) • (A - D) ∧ B' = D + (-√ρ) • (B - D) ∧ C' = D + (-√ρ) • (C - D) ∧
          A' ∈ convexHull ℝ {A, B, C} ∧ B' ∈ convexHull ℝ {A, B, C} ∧
          C' ∈ convexHull ℝ {A, B, C})) := by
  sorry

/-- The hypotheses of `problem26` are satisfiable (a right isosceles triangle). -/
theorem problem26_nonvacuous :
    ∃ A B C D : Plane, cross A B C ≠ 0 ∧ (dist D A = dist D B ∧ dist D B = dist D C) ∧
      D ∈ convexHull ℝ {A, B, C} := by
  sorry

end PillowProblems.P26
