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

private lemma vec_ext {u v : Plane} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext i; fin_cases i <;> simp [h0, h1]

private lemma inner_coord (u v : Plane) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]; ring

/-- For two lines `AB`, `AC` meeting at `A` and a point `P` within the angle `BAC`, there are
points `L` on the arm `AB` and `M` on the arm `AC` such that `PL ⊥ PM` and the triangles `APL`,
`APM` are equal. -/
theorem problem9 (A B C P : Plane) (hABC : cross A B C ≠ 0) (hP : InsideAngle A B C P) :
    ∃ l m : ℝ, 0 < l ∧ 0 < m ∧
      IsSolution A P (AffineMap.lineMap A B l) (AffineMap.lineMap A C m) := by
  obtain ⟨a, b, ha, hb, hw⟩ := hP
  have hw0 : P 0 = A 0 + a * (B 0 - A 0) + b * (C 0 - A 0) := by
    have := congrArg (fun v : Plane => v 0) hw; simp at this; linarith
  have hw1 : P 1 = A 1 + a * (B 1 - A 1) + b * (C 1 - A 1) := by
    have := congrArg (fun v : Plane => v 1) hw; simp at this; linarith
  have hcr : cross A B C = (B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1) := rfl
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (a * (B 0 - A 0) + b * (C 0 - A 0)) ^ 2 +
      (a * (B 1 - A 1) + b * (C 1 - A 1)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = a * b * ((B 0 - A 0) * (C 0 - A 0) +
      (B 1 - A 1) * (C 1 - A 1)) := ⟨_, rfl⟩
  have hWpos : 0 < W := by
    rcases (show 0 ≤ W by rw [hW]; positivity).lt_or_eq with h | h
    · exact h
    exfalso
    have e0 : a * (B 0 - A 0) + b * (C 0 - A 0) = 0 := by nlinarith
    have e1 : a * (B 1 - A 1) + b * (C 1 - A 1) = 0 := by nlinarith
    have : a * cross A B C = 0 := by
      rw [hcr]; linear_combination (C 1 - A 1) * e0 - (C 0 - A 0) * e1
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact hABC h'
  have hDisc : W ^ 2 - 4 * c * W = W * ((a * (B 0 - A 0) - b * (C 0 - A 0)) ^ 2 +
      (a * (B 1 - A 1) - b * (C 1 - A 1)) ^ 2) := by rw [hW, hc]; ring
  have hD : 0 ≤ W ^ 2 - 4 * c * W := by rw [hDisc]; positivity
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (W ^ 2 - 4 * c * W) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = W ^ 2 - 4 * c * W := by rw [hs]; exact Real.sq_sqrt hD
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 2 * W / (W + s) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  have htW : t * (W + s) = 2 * W := by rw [ht]; field_simp
  have key : c * t ^ 2 - W * t + W = 0 := by
    have h' : (W + s) ^ 2 * (c * t ^ 2 - W * t + W) = 0 := by
      linear_combination (c * (t * (W + s) + 2 * W) - W * (W + s)) * htW + W * hs2
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' (by positivity)
    · exact h''
  have hL0 : (AffineMap.lineMap A B (t * a) : Plane) 0 = A 0 + t * a * (B 0 - A 0) := by
    simp [AffineMap.lineMap_apply_module]; ring
  have hL1 : (AffineMap.lineMap A B (t * a) : Plane) 1 = A 1 + t * a * (B 1 - A 1) := by
    simp [AffineMap.lineMap_apply_module]; ring
  have hM0 : (AffineMap.lineMap A C (t * b) : Plane) 0 = A 0 + t * b * (C 0 - A 0) := by
    simp [AffineMap.lineMap_apply_module]; ring
  have hM1 : (AffineMap.lineMap A C (t * b) : Plane) 1 = A 1 + t * b * (C 1 - A 1) := by
    simp [AffineMap.lineMap_apply_module]; ring
  have hL : cross A P (AffineMap.lineMap A B (t * a)) =
      -(t * a * b * cross A B C) := by
    rw [hcr]; simp only [cross, hL0, hL1, hw0, hw1]; ring
  have hM : cross A P (AffineMap.lineMap A C (t * b)) = t * a * b * cross A B C := by
    rw [hcr]; simp only [cross, hM0, hM1, hw0, hw1]; ring
  have hne : t * a * b * cross A B C ≠ 0 := by
    have : 0 < t * a * b := by positivity
    exact mul_ne_zero this.ne' hABC
  have hAPP : cross A P P = 0 := by simp only [cross]; ring
  refine ⟨t * a, t * b, by positivity, by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; rw [h, hAPP] at hL; exact hne (by linarith)
  · intro h; rw [h, hAPP] at hM; exact hne (by linarith)
  · rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two,
      inner_coord, vsub_eq_sub, vsub_eq_sub, PiLp.sub_apply, PiLp.sub_apply, PiLp.sub_apply,
      PiLp.sub_apply, hL0, hL1, hM0, hM1, hw0, hw1]
    subst hW hc
    linear_combination key
  · rw [triArea, hL, abs_neg]
    have := abs_pos.mpr hne
    linarith
  · rw [triArea, triArea, hL, hM, abs_neg]

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
  have hne : ∀ u v : Plane, u 0 ≠ v 0 → u ≠ v := fun u v h e => h (by rw [e])
  refine ⟨by simp [cross], ⟨1 / 4, 1 / 4, by norm_num, by norm_num, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · apply vec_ext <;> simp; norm_num
  · apply hne; simp
  · apply hne; simp
  · rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two,
      inner_coord]
    simp [AffineMap.lineMap_apply_module]; norm_num
  · simp [triArea, cross, AffineMap.lineMap_apply_module]
  · simp [triArea, cross, AffineMap.lineMap_apply_module]
  · apply hne; simp [AffineMap.lineMap_apply_module]
  · apply hne; simp [AffineMap.lineMap_apply_module]
  · rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two,
      inner_coord]
    simp [AffineMap.lineMap_apply_module]; norm_num
  · simp [triArea, cross, AffineMap.lineMap_apply_module]
  · simp [triArea, cross, AffineMap.lineMap_apply_module]
  · apply hne; simp [AffineMap.lineMap_apply_module]

end PillowProblems.P09
