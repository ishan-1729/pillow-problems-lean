import PillowProblems.Basic

/-!
# Problem 4 (Trigonometry: Plane)

**Question.** *(dated 19/4/76)*

> In a given acute-angled Triangle inscribe a Triangle, whose sides make, at each of the vertices, equal angles with the sides of the given Triangle.

*(Carroll's solution: Chapter III, problem 4; text in `data/problems.json`.)*

**Lean reading.** The given Triangle `ABC` is non-degenerate (`¬ Collinear`) and acute-angled
(all three angles `< π/2`). An inscribed Triangle has `A'` strictly inside side `BC`, `B'`
inside `CA`, `C'` inside `AB`; "its sides make, at each of the vertices, equal angles with
the sides of the given Triangle" is read, as in Carroll's solution, as
`∠ B A' C' = ∠ C A' B'`, `∠ C B' A' = ∠ A B' C'`, `∠ A C' B' = ∠ B C' A'`. Carroll's
construction is that `A'B'C'` is the triangle of the feet of the altitudes. `problem4` proves
that an inscribed triangle has the property exactly when `A', B', C'` are the feet of the
perpendiculars from `A, B, C` on the opposite sides (stated as: on the side line, and
`AA' ⊥ BC`, etc.), so the answer is unique; `problem4_exists` proves that the required triangle
exists. The uniqueness proof follows Carroll (the angles at `A', B', C'` are `A, B, C`, and the
sine rule in the corner triangles gives `BA' = c cos B`); the existence proof uses the
similarity of `BA'C'` and `BAC` (SAS). Acuteness is needed for existence (the feet lie inside
the sides); the uniqueness direction does not use it. `problem4_nonvacuous` exhibits an acute
triangle, so the hypotheses are consistent.

**Status.** proved
-/

namespace PillowProblems.P04

open EuclideanGeometry
open scoped Real

private lemma inner_eq' (x y : Plane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

private lemma dist_sq' (P Q : Plane) : dist P Q ^ 2 = (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
    Real.dist_eq, sq_abs, sq_abs]

private lemma lineMap_apply' (B C : Plane) (t : ℝ) (i : Fin 2) :
    (AffineMap.lineMap B C t : Plane) i = B i + t * (C i - B i) := by
  rw [AffineMap.lineMap_apply]
  simp
  ring

private lemma inner_pos_of_acute {X Y Z : Plane} (h : ∠ X Y Z < π / 2) :
    0 < inner ℝ (X -ᵥ Y) (Z -ᵥ Y) := by
  by_contra hle
  push Not at hle
  exact absurd h (not_lt.mpr (InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mp hle))

private lemma pos_of_mul_sq {t d : ℝ} (h : 0 < t * d ^ 2) : 0 < t := by
  by_contra h'
  push Not at h'
  nlinarith [sq_nonneg d]

private lemma not_col_perm {A B C : Plane} (h : ¬ Collinear ℝ {A, B, C}) :
    ¬ Collinear ℝ {B, C, A} ∧ ¬ Collinear ℝ {C, A, B} ∧ ¬ Collinear ℝ {A, C, B} ∧
      ¬ Collinear ℝ {B, A, C} ∧ ¬ Collinear ℝ {C, B, A} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · convert h using 2
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

/-- A point `F` of the line `XY` with `PF ⊥ XY`: its parameter on the line. -/
private lemma param_of {P X Y F : Plane} (hF : F ∈ line[ℝ, X, Y])
    (hp : inner ℝ (P -ᵥ F) (Y -ᵥ X) = 0) :
    ∃ t, F = AffineMap.lineMap X Y t ∧ t * dist X Y ^ 2 = inner ℝ (P -ᵥ X) (Y -ᵥ X) ∧
      (1 - t) * dist X Y ^ 2 = inner ℝ (P -ᵥ Y) (X -ᵥ Y) := by
  obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hF
  refine ⟨t, rfl, ?_, ?_⟩ <;>
  · rw [inner_eq'] at hp ⊢
    rw [dist_sq']
    simp only [vsub_eq_sub, PiLp.sub_apply, lineMap_apply'] at hp ⊢
    first
    | linear_combination -hp
    | linear_combination hp

/-- If `F` is on the segment `XY` and `2·XF·XY = XY² + PX² - PY²`, then `PF ⊥ XY`. -/
private lemma foot_of {P X Y F : Plane} (h : Wbtw ℝ X F Y)
    (hrel : 2 * (dist X F * dist X Y) = dist X Y ^ 2 + dist P X ^ 2 - dist P Y ^ 2) :
    inner ℝ (P -ᵥ F) (Y -ᵥ X) = 0 := by
  obtain ⟨t, ⟨ht0, -⟩, rfl⟩ := h
  rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg ht0] at hrel
  have h2 : 2 * (t * dist X Y * dist X Y) = 2 * t * dist X Y ^ 2 := by ring
  rw [h2, dist_sq' X Y, dist_sq' P X, dist_sq' P Y] at hrel
  rw [inner_eq']
  simp only [vsub_eq_sub, PiLp.sub_apply, lineMap_apply']
  linear_combination (-1 / 2 : ℝ) * hrel

/-- The corner triangle `X'YZ'` (with `X'` on ray `YZ`, `Z'` on ray `YX` and
`YX'·YZ = YZ'·YX`) is similar to `XYZ`, so `∠ Y X' Z' = ∠ Y X Z`. -/
private lemma key {X Y Z X' Z' : Plane} (hT : ¬ Collinear ℝ {X, Y, Z}) {t s : ℝ} (ht : 0 < t)
    (hs : 0 < s) (hX' : X' = AffineMap.lineMap Y Z t) (hZ' : Z' = AffineMap.lineMap Y X s)
    (hrel : t * dist Y Z ^ 2 = s * dist Y X ^ 2) : ∠ Y X' Z' = ∠ Y X Z := by
  have hXY : X ≠ Y := ne₁₂_of_not_collinear hT
  have hYZ : Y ≠ Z := ne₂₃_of_not_collinear hT
  have hd1 : dist X' Y = t * dist Y Z := by
    rw [hX', dist_lineMap_left, Real.norm_eq_abs, abs_of_pos ht]
  have hd2 : dist Y Z' = s * dist Y X := by
    rw [hZ', dist_left_lineMap, Real.norm_eq_abs, abs_of_pos hs]
  have hang : ∠ X' Y Z' = ∠ X Y Z := by
    rw [hX', hZ']
    unfold EuclideanGeometry.angle
    rw [AffineMap.lineMap_vsub_left, AffineMap.lineMap_vsub_left,
      InnerProductGeometry.angle_smul_left_of_pos _ _ ht,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hs, InnerProductGeometry.angle_comm]
  have hX'Y : X' ≠ Y := by
    intro h
    rw [h, dist_self] at hd1
    have := dist_pos.mpr hYZ
    nlinarith
  have hZ'Y : Z' ≠ Y := by
    intro h
    rw [h, dist_self] at hd2
    have := dist_pos.mpr hXY.symm
    nlinarith
  have hT' : ¬ Collinear ℝ {X', Y, Z'} := by
    rw [collinear_iff_eq_or_eq_or_sin_eq_zero, hang]
    push Not
    exact ⟨hX'Y, hZ'Y, sin_ne_zero_of_not_collinear hT⟩
  have hsim := similar_of_side_angle_side hT' hT hang
    (by rw [hd1, hd2, dist_comm X Y]; linear_combination hrel)
  have := hsim.angle_eq_all.2.2
  rw [angle_comm Y X' Z', this, angle_comm Z X Y]

/-- The inscribed triangles whose sides make equal angles with the sides of the acute-angled
triangle `ABC` at each vertex are exactly given by the feet of the altitudes: `A'` on `BC`
with `AA' ⊥ BC`, and so on. -/
theorem problem4 (A B C : Plane) (hT : ¬ Collinear ℝ {A, B, C})
    (hA : ∠ B A C < π / 2) (hB : ∠ A B C < π / 2) (hC : ∠ A C B < π / 2) (A' B' C' : Plane) :
    (Sbtw ℝ B A' C ∧ Sbtw ℝ C B' A ∧ Sbtw ℝ A C' B ∧
      ∠ B A' C' = ∠ C A' B' ∧ ∠ C B' A' = ∠ A B' C' ∧ ∠ A C' B' = ∠ B C' A') ↔
    ((A' ∈ line[ℝ, B, C] ∧ inner ℝ (A -ᵥ A') (C -ᵥ B) = 0) ∧
      (B' ∈ line[ℝ, C, A] ∧ inner ℝ (B -ᵥ B') (A -ᵥ C) = 0) ∧
      (C' ∈ line[ℝ, A, B] ∧ inner ℝ (C -ᵥ C') (B -ᵥ A) = 0)) := by
  obtain ⟨hT1, hT2, hT3, hT4, hT5⟩ := not_col_perm hT
  constructor
  · rintro ⟨hA', hB', hC', e1, e2, e3⟩
    -- Carroll's angle chase: the angles at `A', B', C'` are `A, B, C`
    have sB1 := angle_add_angle_add_angle_eq_pi C' hA'.ne_left
    have rB : ∠ C' B A' = ∠ A B C := by
      rw [hA'.angle_eq_right C', hC'.symm.angle_eq_left C]
    have sC1 := angle_add_angle_add_angle_eq_pi A' hB'.ne_left
    have rC : ∠ A' C B' = ∠ B C A := by
      rw [hB'.angle_eq_right A', hA'.symm.angle_eq_left A]
    have sA1 := angle_add_angle_add_angle_eq_pi B' hC'.ne_left
    have rA : ∠ B' A C' = ∠ C A B := by
      rw [hC'.angle_eq_right B', hB'.symm.angle_eq_left B]
    have hsum := angle_add_angle_add_angle_eq_pi C (ne₁₂_of_not_collinear hT).symm
    rw [angle_comm A' C' B, ← e3] at sB1
    rw [angle_comm B' A' C, ← e1] at sC1
    rw [angle_comm C' B' A, ← e2] at sA1
    have hx : ∠ B A' C' = ∠ C A B := by linarith
    have hy : ∠ C B' A' = ∠ A B C := by linarith
    have hz : ∠ A C' B' = ∠ B C A := by linarith
    -- the sine rule in the corner triangles and in `ABC`
    have T1 := law_sin A' C' B
    have T2 := law_sin B' A' C
    have T3 := law_sin C' B' A
    rw [angle_comm A' C' B, ← e3, hz, hx] at T1
    rw [angle_comm B' A' C, ← e1, hx, hy] at T2
    rw [angle_comm C' B' A, ← e2, hy, hz] at T3
    have LS1 := law_sin A B C
    have LS2 := law_sin B C A
    have LS3 := law_sin C A B
    have sA : 0 < Real.sin (∠ C A B) := sin_pos_of_not_collinear hT2
    have sB : 0 < Real.sin (∠ A B C) := sin_pos_of_not_collinear hT
    have sC : 0 < Real.sin (∠ B C A) := sin_pos_of_not_collinear hT1
    have sumA := hA'.wbtw.dist_add_dist
    have sumB := hB'.wbtw.dist_add_dist
    have sumC := hC'.wbtw.dist_add_dist
    have rels : 2 * (dist B A' * dist B C) = dist B C ^ 2 + dist A B ^ 2 - dist C A ^ 2 ∧
        2 * (dist C B' * dist C A) = dist C A ^ 2 + dist B C ^ 2 - dist A B ^ 2 ∧
        2 * (dist A C' * dist A B) = dist A B ^ 2 + dist C A ^ 2 - dist B C ^ 2 := by
      generalize Real.sin (∠ C A B) = SA at *
      generalize Real.sin (∠ A B C) = SB at *
      generalize Real.sin (∠ B C A) = SC at *
      generalize dist B C = a at *
      generalize dist C A = b at *
      generalize dist A B = c at *
      generalize dist B A' = p at *
      generalize dist A' C = p' at *
      generalize dist C B' = q at *
      generalize dist B' A = q' at *
      generalize dist A C' = r at *
      generalize dist C' B = r' at *
      have f1 : p * a = r' * c := by
        apply mul_left_cancel₀ sA.ne'
        linear_combination -a * T1 - r' * LS3
      have f2 : p' * a = q * b := by
        apply mul_left_cancel₀ sA.ne'
        linear_combination a * T2 + q * LS1
      have f3 : q' * b = r * c := by
        apply mul_left_cancel₀ sB.ne'
        linear_combination b * T3 + r * LS2
      have G1 : 2 * (p * a) = a ^ 2 + c ^ 2 - b ^ 2 := by
        linear_combination f1 + c * sumC + f3 - b * sumB - f2 + a * sumA
      have G2 : 2 * (q * b) = b ^ 2 + a ^ 2 - c ^ 2 := by
        linear_combination -2 * f2 + 2 * a * sumA - G1
      have G3 : 2 * (r * c) = c ^ 2 + b ^ 2 - a ^ 2 := by
        linear_combination -2 * f3 + 2 * b * sumB - G2
      exact ⟨G1, G2, G3⟩
    obtain ⟨G1, G2, G3⟩ := rels
    refine ⟨⟨hA'.wbtw.mem_affineSpan, foot_of hA'.wbtw ?_⟩,
      ⟨hB'.wbtw.mem_affineSpan, foot_of hB'.wbtw ?_⟩,
      ⟨hC'.wbtw.mem_affineSpan, foot_of hC'.wbtw ?_⟩⟩
    · rw [dist_comm A C]; exact G1
    · rw [dist_comm B A]; exact G2
    · rw [dist_comm C B]; exact G3
  · rintro ⟨⟨hA'm, hA'p⟩, ⟨hB'm, hB'p⟩, ⟨hC'm, hC'p⟩⟩
    obtain ⟨tA, rfl, hA1, hA2⟩ := param_of hA'm hA'p
    obtain ⟨tB, rfl, hB1, hB2⟩ := param_of hB'm hB'p
    obtain ⟨tC, rfl, hC1, hC2⟩ := param_of hC'm hC'p
    have RA := inner_pos_of_acute hA
    have RB := inner_pos_of_acute hB
    have RC := inner_pos_of_acute hC
    rw [real_inner_comm] at hB1 hC1 hC2
    have tA0 : 0 < tA := pos_of_mul_sq (d := dist B C) (by rw [hA1]; exact RB)
    have tA1 : 0 < 1 - tA := pos_of_mul_sq (d := dist B C) (by rw [hA2]; exact RC)
    have tB0 : 0 < tB := pos_of_mul_sq (d := dist C A) (by rw [hB1]; exact RC)
    have tB1 : 0 < 1 - tB := pos_of_mul_sq (d := dist C A) (by rw [hB2]; exact RA)
    have tC0 : 0 < tC := pos_of_mul_sq (d := dist A B) (by rw [hC1]; exact RA)
    have tC1 : 0 < 1 - tC := pos_of_mul_sq (d := dist A B) (by rw [hC2]; exact RB)
    have hAB : A ≠ B := ne₁₂_of_not_collinear hT
    have hBC : B ≠ C := ne₂₃_of_not_collinear hT
    have hAC : A ≠ C := ne₁₃_of_not_collinear hT
    have eA := (AffineMap.lineMap_apply_one_sub C B tA).symm
    have eB := (AffineMap.lineMap_apply_one_sub A C tB).symm
    have eC := (AffineMap.lineMap_apply_one_sub B A tC).symm
    have k1 := key hT tA0 tC1 rfl eC (by rw [hA1, dist_comm B A, hC2])
    have k2 := key hT3 tA1 tB0 eA rfl (by rw [dist_comm C B, hA2, hB1])
    have k3 := key hT1 tB0 tA1 rfl eA (by rw [hB1, dist_comm C B, hA2])
    have k4 := key hT4 tB1 tC0 eB rfl (by rw [dist_comm A C, hB2, hC1])
    have k5 := key hT2 tC0 tB1 rfl eB (by rw [hC1, dist_comm A C, hB2])
    have k6 := key hT5 tC1 tA0 eC rfl (by rw [dist_comm B A, hC2, hA1])
    refine ⟨sbtw_lineMap_iff.mpr ⟨hBC, tA0, by linarith⟩,
      sbtw_lineMap_iff.mpr ⟨hAC.symm, tB0, by linarith⟩,
      sbtw_lineMap_iff.mpr ⟨hAB, tC0, by linarith⟩, ?_, ?_, ?_⟩
    · rw [k1, k2, angle_comm]
    · rw [k3, k4, angle_comm]
    · rw [k5, k6, angle_comm]

/-- Carroll's construction succeeds: the triangle of the feet of the altitudes is inscribed
in the acute-angled triangle `ABC` and has the required property. -/
theorem problem4_exists (A B C : Plane) (hT : ¬ Collinear ℝ {A, B, C})
    (hA : ∠ B A C < π / 2) (hB : ∠ A B C < π / 2) (hC : ∠ A C B < π / 2) :
    ∃ A' B' C' : Plane, Sbtw ℝ B A' C ∧ Sbtw ℝ C B' A ∧ Sbtw ℝ A C' B ∧
      ∠ B A' C' = ∠ C A' B' ∧ ∠ C B' A' = ∠ A B' C' ∧ ∠ A C' B' = ∠ B C' A' := by
  have foot : ∀ P X Y : Plane, X ≠ Y →
      ∃ F, F ∈ line[ℝ, X, Y] ∧ inner ℝ (P -ᵥ F) (Y -ᵥ X) = 0 := by
    intro P X Y hXY
    have hd : dist X Y ^ 2 ≠ 0 := pow_ne_zero 2 (dist_ne_zero.mpr hXY)
    refine ⟨AffineMap.lineMap X Y (inner ℝ (P -ᵥ X) (Y -ᵥ X) / dist X Y ^ 2),
      AffineMap.lineMap_mem_affineSpan_pair _ _ _, ?_⟩
    have h : ∀ t : ℝ, inner ℝ (P -ᵥ AffineMap.lineMap X Y t) (Y -ᵥ X) =
        inner ℝ (P -ᵥ X) (Y -ᵥ X) - t * dist X Y ^ 2 := by
      intro t
      rw [inner_eq', inner_eq', dist_sq']
      simp only [vsub_eq_sub, PiLp.sub_apply, lineMap_apply']
      ring
    rw [h, div_mul_cancel₀ _ hd, sub_self]
  obtain ⟨A', hA'⟩ := foot A B C (ne₂₃_of_not_collinear hT)
  obtain ⟨B', hB'⟩ := foot B C A (ne₁₃_of_not_collinear hT).symm
  obtain ⟨C', hC'⟩ := foot C A B (ne₁₂_of_not_collinear hT)
  exact ⟨A', B', C', (problem4 A B C hT hA hB hC A' B' C').mpr ⟨hA', hB', hC'⟩⟩

/-- The hypotheses of `problem4` can be met: the triangle `(0,2), (-1,0), (1,0)` is acute. -/
theorem problem4_nonvacuous : ∃ A B C : Plane, ¬ Collinear ℝ {A, B, C} ∧
    ∠ B A C < π / 2 ∧ ∠ A B C < π / 2 ∧ ∠ A C B < π / 2 := by
  have acute : ∀ X Y Z : Plane, 0 < inner ℝ (X -ᵥ Y) (Z -ᵥ Y) → ∠ X Y Z < π / 2 :=
    fun X Y Z h => lt_of_not_ge fun h' =>
      absurd (InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mpr h') (not_le.mpr h)
  refine ⟨pt 0 2, pt (-1) 0, pt 1 0, ?_, acute _ _ _ (by rw [inner_eq']; norm_num),
    acute _ _ _ (by rw [inner_eq']; norm_num), acute _ _ _ (by rw [inner_eq']; norm_num)⟩
  rw [collinear_iff_of_mem (p₀ := pt (-1) 0) (by simp)]
  rintro ⟨v, hv⟩
  obtain ⟨r1, hr1⟩ := hv (pt 0 2) (by simp)
  obtain ⟨r2, hr2⟩ := hv (pt 1 0) (by simp)
  have a1 := congrArg (fun P : Plane => P 1) hr1
  have c0 := congrArg (fun P : Plane => P 0) hr2
  have c1 := congrArg (fun P : Plane => P 1) hr2
  simp at a1 c0 c1
  rcases c1 with h | h
  · rw [h] at c0; linarith
  · rw [h, mul_zero] at a1; linarith

end PillowProblems.P04
