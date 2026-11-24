import PillowProblems.Basic

/-!
# Problem 58 (Algebra: Chances)

**Question.** *(dated 20/1/84)*

> Three Points are taken at random on an infinite Plane. Find the chance of their being the vertices of an obtuse-angled Triangle.

**Answer.**

> \[ \frac{3}{8 - \dfrac{6\sqrt{3}}{\pi}}. \]

*(Carroll's solution: Chapter III, problem 58; text in `data/problems.json`.)*

**Lean reading.** As stated the problem is ill-posed (there is no uniform distribution on an
infinite plane, and other ways of making "at random" precise give other values, e.g.
`9/8 − 4/π² ≈ 0.72` for three points uniform in a disc, against Carroll's `≈ 0.64`), so we
formalize exactly the reading of Carroll's solution: the longest side `AB` (any `A ≠ B`) is fixed
and the third vertex `C` is uniform (normalised Lebesgue measure, `ProbabilityTheory.cond volume`)
over his figure `ABDCE`, i.e. `carrollRegion A B`, the points left of `AB` with `CA < AB` and
`CB < AB`; the other side of `AB` is `carrollRegion B A` (`carrollRegion_swap`), so it is covered
too. Ties between sides, collinear `C` and boundary points are null sets (Carroll's "practically
*nil*"), so strict inequalities are used. "Obtuse-angled" is the literal condition that some
unoriented angle `∠` of `ABC` exceeds `π/2`, not Carroll's semicircle criterion, which is proved
(`problem58_obtuse_iff`). With `AB = 2a` the areas `πa²/2` and `a²(4π/3 − √3)` are derived by a
change of variables and integration, giving the chance `3/(8 − 6√3/π)`. That `C` is uniform over
the figure once the longest side is fixed is Carroll's own assumption, not derived from any limit
of uniform distributions on bounded regions.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P58

open Real MeasureTheory Set EuclideanGeometry

/-- Carroll's figure `ABDCE`: the points `C` on the left of the directed line `AB`
(`0 < cross A B C`) for which `AB` is strictly the longest side of `ABC`. Where the third vertex
may lie once `AB` is named as the longest side. -/
def carrollRegion (A B : Plane) : Set Plane :=
  {C | dist C A < dist A B ∧ dist C B < dist A B ∧ 0 < cross A B C}

/-- The triangle `ABC` is obtuse-angled: one of its three angles exceeds a right angle. -/
def IsObtuse (A B C : Plane) : Prop :=
  π / 2 < ∠ B A C ∨ π / 2 < ∠ A B C ∨ π / 2 < ∠ A C B

/-- Carroll's chance: the probability that `ABC` is obtuse-angled when `C` is uniformly
distributed (normalised Lebesgue measure) over `carrollRegion A B`. -/
noncomputable def obtuseChance (A B : Plane) : ℝ :=
  (ProbabilityTheory.cond volume (carrollRegion A B) {C | IsObtuse A B C}).toReal

/-- The figure on the other side of `AB` is `carrollRegion B A`, so every statement below for all
`A ≠ B` covers both sides. -/
theorem carrollRegion_swap (A B : Plane) :
    carrollRegion B A = {C | dist C A < dist A B ∧ dist C B < dist A B ∧ cross A B C < 0} := by
  sorry

private noncomputable def eqv : Plane ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

/-- Carroll's key step: inside the figure, the triangle is obtuse-angled exactly when `C` lies
inside the semicircle on `AB`. -/
theorem problem58_obtuse_iff (A B C : Plane) (hC : C ∈ carrollRegion A B) :
    IsObtuse A B C ↔ dist C (midpoint ℝ A B) < dist A B / 2 := by
  sorry

/-! Integrals. -/

/-! Standard regions in `ℝ × ℝ`. -/

private def TO : Set (ℝ × ℝ) := {q | q.1 ^ 2 + q.2 ^ 2 < 1 ∧ 0 < q.1}

private def TR : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 + (q.2 - 1) ^ 2 < 4 ∧ q.1 ^ 2 + (q.2 + 1) ^ 2 < 4 ∧ 0 < q.1}

/-! The similarity taking the standard configuration to `A, B`. -/

private noncomputable def simL (u0 u1 : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun p := pt (p 0 * u1 + p 1 * u0) (-(p 0 * u0) + p 1 * u1)
  map_add' x y := by
    refine PiLp.ext fun i => ?_
    fin_cases i <;> simp [pt] <;> ring
  map_smul' c x := by
    refine PiLp.ext fun i => ?_
    fin_cases i <;> simp [pt] <;> ring

private noncomputable def Lof (A B : Plane) : Plane →ₗ[ℝ] Plane :=
  simL ((A 0 - B 0) / 2) ((A 1 - B 1) / 2)

private noncomputable def mid (A B : Plane) : Plane := pt ((A 0 + B 0) / 2) ((A 1 + B 1) / 2)

private noncomputable def sc (A B : Plane) : ℝ := ((A 0 - B 0) / 2) ^ 2 + ((A 1 - B 1) / 2) ^ 2

/-- With `AB = 2a`: the area of the figure `ABDCE` is `a² (4π/3 − √3)`. -/
theorem problem58_area_figure (A B : Plane) (hAB : A ≠ B) :
    volume (carrollRegion A B) = ENNReal.ofReal ((dist A B / 2) ^ 2 * (4 * π / 3 - √3)) := by
  sorry

/-- With `AB = 2a`: the part of the figure where the triangle is obtuse (the semicircle) has
area `π a² / 2`. -/
theorem problem58_area_semicircle (A B : Plane) (hAB : A ≠ B) :
    volume (carrollRegion A B ∩ {C | IsObtuse A B C}) =
      ENNReal.ofReal (π * (dist A B / 2) ^ 2 / 2) := by
  sorry

/-- **Problem 58** (Carroll's reading): the chance of an obtuse-angled triangle is
`3 / (8 − 6√3/π)`. -/
theorem problem58 (A B : Plane) (hAB : A ≠ B) :
    obtuseChance A B = 3 / (8 - 6 * √3 / π) := by
  sorry

/-- A concrete instance of `problem58`. -/
theorem problem58_nonvacuous : obtuseChance (pt 0 0) (pt 2 0) = 3 / (8 - 6 * √3 / π) := by
  sorry

end PillowProblems.P58
