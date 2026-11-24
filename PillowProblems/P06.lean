import PillowProblems.Basic

/-!
# Problem 6 (Trigonometry: Plane)

**Question.**

> Given lengths of lines drawn, from vertices of Triangle, to middle points of opposite sides, to find its sides and angles.

**Answer.**

> Calling the sides '\(2a\)', '\(2b\)', '\(2c\)' and the lines '\(\alpha\)', '\(\beta\)', '\(\gamma\)', we have
>
> \(\quad\quad a^{2}=\dfrac{-\alpha^{2}+2\beta^{2}+2\gamma^{2}}{9},\)
>
> \(\quad \cos A= \dfrac{5\alpha^{2}-\beta^{2}-\gamma^{2}}{2\sqrt{2\alpha^{2}-\beta^{2}+2\gamma^{2}}.{\sqrt{2\alpha^{2}+2\beta^{2}-\gamma^{2}}}}\).

*(Carroll's solution: Chapter III, problem 6; text in `data/problems.json`.)*

**Lean reading.** The Triangle is three points `A B C` of the `Plane`; Carroll's sides are
`2a = BC`, `2b = CA`, `2c = AB`, and his lines are the medians `α = A M_A`, `β = B M_B`,
`γ = C M_C`, where `M_A = midpoint ℝ B C` etc. "Find its sides and angles" is read as: the sides
and the cosines of the angles are given by Carroll's formulas in `α, β, γ`. `problem6_sides`
gives `a² = (-α² + 2β² + 2γ²)/9` and its two cyclic companions, and the side lengths
`BC = ⅔ √(-α² + 2β² + 2γ²)` etc. (so the sides, hence the triangle up to congruence, are
determined by the medians). `problem6` gives Carroll's formula for `cos A` and, as he says
("and so for other angles"), the cyclic formulas for `cos B` and `cos C`. The cosine formulas
need the vertices pairwise distinct (otherwise the angle is the junk value `π/2` and the
denominators vanish); no other hypothesis is needed, and the formulas hold even for collinear
triangles.

**Status.** proved
-/

namespace PillowProblems.P06

open EuclideanGeometry

private lemma dist_sq' (P Q : Plane) : dist P Q ^ 2 = (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
    Real.dist_eq, sq_abs, sq_abs]

private lemma midpoint_apply' (B C : Plane) (i : Fin 2) :
    (midpoint ℝ B C) i = (B i + C i) / 2 := by
  rw [midpoint_eq_smul_add]
  simp
  ring

private lemma dist_mid_sq (A B C : Plane) :
    dist A (midpoint ℝ B C) ^ 2 = (A 0 - (B 0 + C 0) / 2) ^ 2 + (A 1 - (B 1 + C 1) / 2) ^ 2 := by
  rw [dist_sq', midpoint_apply', midpoint_apply']

private lemma inner_eq' (x y : Plane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

private lemma sqrt_eq_of_sq {X d : ℝ} (hd : 0 ≤ d) (h : X = d ^ 2) : Real.sqrt X = d := by
  rw [h, Real.sqrt_sq hd]

/-- The sides from the medians: with sides `2a = BC, 2b = CA, 2c = AB` and medians
`α, β, γ` from `A, B, C`, `a² = (-α² + 2β² + 2γ²)/9` (and cyclically), so
`BC = ⅔ √(-α² + 2β² + 2γ²)` (and cyclically). -/
theorem problem6_sides (A B C : Plane) :
    (dist B C / 2) ^ 2 = (-dist A (midpoint ℝ B C) ^ 2 + 2 * dist B (midpoint ℝ C A) ^ 2
        + 2 * dist C (midpoint ℝ A B) ^ 2) / 9 ∧
    (dist C A / 2) ^ 2 = (2 * dist A (midpoint ℝ B C) ^ 2 - dist B (midpoint ℝ C A) ^ 2
        + 2 * dist C (midpoint ℝ A B) ^ 2) / 9 ∧
    (dist A B / 2) ^ 2 = (2 * dist A (midpoint ℝ B C) ^ 2 + 2 * dist B (midpoint ℝ C A) ^ 2
        - dist C (midpoint ℝ A B) ^ 2) / 9 ∧
    dist B C = 2 / 3 * Real.sqrt (-dist A (midpoint ℝ B C) ^ 2 + 2 * dist B (midpoint ℝ C A) ^ 2
        + 2 * dist C (midpoint ℝ A B) ^ 2) ∧
    dist C A = 2 / 3 * Real.sqrt (2 * dist A (midpoint ℝ B C) ^ 2 - dist B (midpoint ℝ C A) ^ 2
        + 2 * dist C (midpoint ℝ A B) ^ 2) ∧
    dist A B = 2 / 3 * Real.sqrt (2 * dist A (midpoint ℝ B C) ^ 2 + 2 * dist B (midpoint ℝ C A) ^ 2
        - dist C (midpoint ℝ A B) ^ 2) := by
  have e1 : -dist A (midpoint ℝ B C) ^ 2 + 2 * dist B (midpoint ℝ C A) ^ 2
      + 2 * dist C (midpoint ℝ A B) ^ 2 = (3 / 2 * dist B C) ^ 2 := by
    rw [dist_mid_sq, dist_mid_sq, dist_mid_sq, mul_pow, dist_sq']; ring
  have e2 : 2 * dist A (midpoint ℝ B C) ^ 2 - dist B (midpoint ℝ C A) ^ 2
      + 2 * dist C (midpoint ℝ A B) ^ 2 = (3 / 2 * dist C A) ^ 2 := by
    rw [dist_mid_sq, dist_mid_sq, dist_mid_sq, mul_pow, dist_sq']; ring
  have e3 : 2 * dist A (midpoint ℝ B C) ^ 2 + 2 * dist B (midpoint ℝ C A) ^ 2
      - dist C (midpoint ℝ A B) ^ 2 = (3 / 2 * dist A B) ^ 2 := by
    rw [dist_mid_sq, dist_mid_sq, dist_mid_sq, mul_pow, dist_sq']; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; ring
  · rw [e2]; ring
  · rw [e3]; ring
  · rw [sqrt_eq_of_sq (by positivity) e1]; ring
  · rw [sqrt_eq_of_sq (by positivity) e2]; ring
  · rw [sqrt_eq_of_sq (by positivity) e3]; ring

private lemma cos_formula (A B C : Plane) (hAB : A ≠ B) (hCA : C ≠ A) :
    Real.cos (∠ B A C) = (5 * dist A (midpoint ℝ B C) ^ 2 - dist B (midpoint ℝ C A) ^ 2
        - dist C (midpoint ℝ A B) ^ 2) /
      (2 * Real.sqrt (2 * dist A (midpoint ℝ B C) ^ 2 - dist B (midpoint ℝ C A) ^ 2
        + 2 * dist C (midpoint ℝ A B) ^ 2) *
        Real.sqrt (2 * dist A (midpoint ℝ B C) ^ 2 + 2 * dist B (midpoint ℝ C A) ^ 2
        - dist C (midpoint ℝ A B) ^ 2)) := by
  obtain ⟨-, -, -, -, h2, h3⟩ := problem6_sides A B C
  have s2 : Real.sqrt (2 * dist A (midpoint ℝ B C) ^ 2 - dist B (midpoint ℝ C A) ^ 2
      + 2 * dist C (midpoint ℝ A B) ^ 2) = 3 / 2 * dist C A := by linarith
  have s3 : Real.sqrt (2 * dist A (midpoint ℝ B C) ^ 2 + 2 * dist B (midpoint ℝ C A) ^ 2
      - dist C (midpoint ℝ A B) ^ 2) = 3 / 2 * dist A B := by linarith
  rw [s2, s3]
  have hc : 0 < dist A B := dist_pos.mpr hAB
  have hb : 0 < dist C A := dist_pos.mpr hCA
  have hnum : 5 * dist A (midpoint ℝ B C) ^ 2 - dist B (midpoint ℝ C A) ^ 2
      - dist C (midpoint ℝ A B) ^ 2 = 9 / 2 * inner ℝ (B -ᵥ A) (C -ᵥ A) := by
    rw [dist_mid_sq, dist_mid_sq, dist_mid_sq, inner_eq']
    simp only [vsub_eq_sub, PiLp.sub_apply]
    ring
  rw [hnum, EuclideanGeometry.angle, InnerProductGeometry.cos_angle, ← dist_eq_norm_vsub,
    ← dist_eq_norm_vsub, dist_comm B A]
  field_simp
  ring

/-- The angles from the medians: Carroll's formula for `cos A`, and the cyclic formulas for
`cos B` and `cos C`. -/
theorem problem6 (A B C : Plane) (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) :
    Real.cos (∠ B A C) = (5 * dist A (midpoint ℝ B C) ^ 2 - dist B (midpoint ℝ C A) ^ 2
        - dist C (midpoint ℝ A B) ^ 2) /
      (2 * Real.sqrt (2 * dist A (midpoint ℝ B C) ^ 2 - dist B (midpoint ℝ C A) ^ 2
        + 2 * dist C (midpoint ℝ A B) ^ 2) *
        Real.sqrt (2 * dist A (midpoint ℝ B C) ^ 2 + 2 * dist B (midpoint ℝ C A) ^ 2
        - dist C (midpoint ℝ A B) ^ 2)) ∧
    Real.cos (∠ C B A) = (5 * dist B (midpoint ℝ C A) ^ 2 - dist C (midpoint ℝ A B) ^ 2
        - dist A (midpoint ℝ B C) ^ 2) /
      (2 * Real.sqrt (2 * dist B (midpoint ℝ C A) ^ 2 - dist C (midpoint ℝ A B) ^ 2
        + 2 * dist A (midpoint ℝ B C) ^ 2) *
        Real.sqrt (2 * dist B (midpoint ℝ C A) ^ 2 + 2 * dist C (midpoint ℝ A B) ^ 2
        - dist A (midpoint ℝ B C) ^ 2)) ∧
    Real.cos (∠ A C B) = (5 * dist C (midpoint ℝ A B) ^ 2 - dist A (midpoint ℝ B C) ^ 2
        - dist B (midpoint ℝ C A) ^ 2) /
      (2 * Real.sqrt (2 * dist C (midpoint ℝ A B) ^ 2 - dist A (midpoint ℝ B C) ^ 2
        + 2 * dist B (midpoint ℝ C A) ^ 2) *
        Real.sqrt (2 * dist C (midpoint ℝ A B) ^ 2 + 2 * dist A (midpoint ℝ B C) ^ 2
        - dist B (midpoint ℝ C A) ^ 2)) := by
  exact ⟨cos_formula A B C hAB hCA, cos_formula B C A hBC hAB, cos_formula C A B hCA hBC⟩

end PillowProblems.P06
