import PillowProblems.Basic

/-!
# Problem 60 (Trigonometry: Plane)

**Question.** *(dated 21/3/90)*

> Given a Triangle \(ABC\), and that its base \(BC\) is divided at \(D\) in the ratio \(m\) to \(n\): find the angles \(BAD\), \(CAD\).

**Answer.**

> \(\cot{BAD} = \dfrac{(m+n)\cot{A} + n\cot{B}}{m}\);
>
> similarly, \(\quad\cot{CAD} = \dfrac{(m+n)\cot{A} + m\cot{C}}{n}\).

*(Carroll's solution: Chapter III, problem 60; text in `data/problems.json`.)*

**Lean reading.** `A B C` are points of the plane forming a genuine triangle
(`cross A B C ≠ 0`); Carroll's `A`, `B`, `C` in the answer are the angles `∠BAC`, `∠ABC`, `∠ACB`.
"`BC` divided at `D` in the ratio `m` to `n`" is read as internal division, as in Carroll's figure:
`m, n > 0`, `D` lies on the segment `BC` (`Wbtw ℝ B D C`) and `BD / DC = m / n`. As in Carroll's
answer, the angles `BAD`, `CAD` are found by giving their cotangents (`Real.cot`); the theorem also
proves both angles lie in `(0, π)`, where `cot` is strictly decreasing, so the cotangent
determines each angle uniquely.

**Status.** proved
-/

namespace PillowProblems.P60

open EuclideanGeometry Real

private lemma inner_plane (x y : Plane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- `cot ∠PQR = ⟪P - Q, R - Q⟫ / |cross Q P R|`, and the angle is strictly between `0` and `π`. -/
private lemma cot_angle (P Q R : Plane) (h : cross Q P R ≠ 0) :
    Real.cot (∠ P Q R) = inner ℝ (P - Q) (R - Q) / |cross Q P R| ∧ 0 < Real.sin (∠ P Q R) := by
  have hx : P - Q ≠ 0 := by
    intro hx; apply h
    have h0 : P 0 = Q 0 := by have := congrFun (congrArg (⇑) hx) 0; simpa [sub_eq_zero] using this
    have h1 : P 1 = Q 1 := by have := congrFun (congrArg (⇑) hx) 1; simpa [sub_eq_zero] using this
    simp [cross, h0, h1]
  have hy : R - Q ≠ 0 := by
    intro hy; apply h
    have h0 : R 0 = Q 0 := by have := congrFun (congrArg (⇑) hy) 0; simpa [sub_eq_zero] using this
    have h1 : R 1 = Q 1 := by have := congrFun (congrArg (⇑) hy) 1; simpa [sub_eq_zero] using this
    simp [cross, h0, h1]
  have hN : 0 < ‖P - Q‖ * ‖R - Q‖ := mul_pos (norm_pos_iff.2 hx) (norm_pos_iff.2 hy)
  have hc := InnerProductGeometry.cos_angle_mul_norm_mul_norm (P - Q) (R - Q)
  have hs := InnerProductGeometry.sin_angle_mul_norm_mul_norm (P - Q) (R - Q)
  have hsq : inner ℝ (P - Q) (P - Q) * inner ℝ (R - Q) (R - Q) -
      inner ℝ (P - Q) (R - Q) * inner ℝ (P - Q) (R - Q) = (cross Q P R) ^ 2 := by
    simp only [inner_plane, cross, PiLp.sub_apply]; ring
  rw [hsq, Real.sqrt_sq_eq_abs] at hs
  have hang : ∠ P Q R = InnerProductGeometry.angle (P - Q) (R - Q) := rfl
  have habs : 0 < |cross Q P R| := abs_pos.2 h
  have hsin : 0 < Real.sin (∠ P Q R) := by
    rw [hang]; by_contra hle; push Not at hle
    nlinarith
  refine ⟨?_, hsin⟩
  rw [Real.cot_eq_cos_div_sin, hang, ← hc, ← hs]
  field_simp

private lemma angle_pos_lt_pi {P Q R : Plane} (h : 0 < Real.sin (∠ P Q R)) :
    0 < ∠ P Q R ∧ ∠ P Q R < π := by
  have h0 := EuclideanGeometry.angle_nonneg P Q R
  have h1 := EuclideanGeometry.angle_le_pi P Q R
  refine ⟨lt_of_le_of_ne h0 ?_, lt_of_le_of_ne h1 ?_⟩
  · intro he; rw [← he, Real.sin_zero] at h; exact lt_irrefl _ h
  · intro he; rw [he, Real.sin_pi] at h; exact lt_irrefl _ h

/-- Carroll's answer: with `D` dividing `BC` internally as `m : n`,
`cot BAD = ((m + n) cot A + n cot B) / m` and `cot CAD = ((m + n) cot A + m cot C) / n`;
both angles lie strictly between `0` and `π`, where `cot` is injective, so this finds them. -/
theorem problem60 (A B C D : Plane) (m n : ℝ) (hABC : cross A B C ≠ 0) (hm : 0 < m) (hn : 0 < n)
    (hD : Wbtw ℝ B D C) (hratio : dist B D / dist D C = m / n) :
    Real.cot (∠ B A D) = ((m + n) * Real.cot (∠ B A C) + n * Real.cot (∠ A B C)) / m ∧
    Real.cot (∠ C A D) = ((m + n) * Real.cot (∠ B A C) + m * Real.cot (∠ A C B)) / n ∧
    (0 < ∠ B A D ∧ ∠ B A D < π) ∧ (0 < ∠ C A D ∧ ∠ C A D < π) := by
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hD
  have hBC : B ≠ C := by
    rintro rfl; apply hABC; simp only [cross]; ring
  have hdBC : 0 < dist B C := dist_pos.2 hBC
  rw [dist_left_lineMap, dist_lineMap_right, Real.norm_eq_abs, Real.norm_eq_abs] at hratio
  have ht1' : t ≠ 1 := by
    rintro rfl
    simp only [sub_self, abs_zero, zero_mul, div_zero] at hratio
    exact absurd hratio.symm (div_ne_zero hm.ne' hn.ne')
  have hlt : t < 1 := lt_of_le_of_ne ht1 ht1'
  rw [abs_of_nonneg ht0, abs_of_pos (by linarith : (0:ℝ) < 1 - t)] at hratio
  have ht : t = m / (m + n) := by
    rw [div_eq_div_iff (by positivity) hn.ne'] at hratio
    have h2 : (t * n - m * (1 - t)) * dist B C = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · field_simp; linarith
    · exact absurd h3 hdBC.ne'
  have htpos : 0 < t := by rw [ht]; positivity
  set D := AffineMap.lineMap B C t with hDdef
  have hD0 : D 0 = B 0 + t * (C 0 - B 0) := by
    simp [hDdef, AffineMap.lineMap_apply]; ring
  have hD1 : D 1 = B 1 + t * (C 1 - B 1) := by
    simp [hDdef, AffineMap.lineMap_apply]; ring
  set K := cross A B C with hK
  have c1 : cross A B D = t * K := by simp only [hK, cross, hD0, hD1]; ring
  have c2 : cross B A C = -K := by simp only [hK, cross]; ring
  have c3 : cross A C D = -((1 - t) * K) := by simp only [hK, cross, hD0, hD1]; ring
  have c4 : cross C A B = K := by simp only [hK, cross]; ring
  have hKpos : 0 < |K| := abs_pos.2 hABC
  have h1t : 0 < 1 - t := by linarith
  obtain ⟨eBAD, sBAD⟩ := cot_angle B A D (by rw [c1]; exact mul_ne_zero htpos.ne' hABC)
  obtain ⟨eBAC, -⟩ := cot_angle B A C hABC
  obtain ⟨eABC, -⟩ := cot_angle A B C (by rw [c2]; exact neg_ne_zero.2 hABC)
  obtain ⟨eCAD, sCAD⟩ := cot_angle C A D (by rw [c3]; exact neg_ne_zero.2 (mul_ne_zero h1t.ne' hABC))
  obtain ⟨eACB, -⟩ := cot_angle A C B (by rw [c4]; exact hABC)
  rw [c1, abs_mul, abs_of_pos htpos] at eBAD
  rw [c2, abs_neg] at eABC
  rw [c3, abs_neg, abs_mul, abs_of_pos h1t] at eCAD
  rw [c4] at eACB
  rw [← hK] at eBAC
  refine ⟨?_, ?_, angle_pos_lt_pi sBAD, angle_pos_lt_pi sCAD⟩
  · rw [eBAD, eBAC, eABC]
    simp only [inner_plane, PiLp.sub_apply, hD0, hD1]
    rw [ht]
    field_simp
    ring
  · have h1t' : 1 - t = n / (m + n) := by rw [ht]; field_simp; ring
    rw [eCAD, eBAC, eACB, h1t']
    simp only [inner_plane, PiLp.sub_apply, hD0, hD1]
    rw [ht]
    field_simp
    ring

end PillowProblems.P60
