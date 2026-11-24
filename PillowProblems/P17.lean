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

private lemma vec_ext {u v : Plane} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext i; fin_cases i <;> simp [h0, h1]

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
  have hAB : A ≠ B := by rintro rfl; apply h; simp [cross]
  have hBC : B ≠ C := by rintro rfl; apply h; simp [cross]
  have hAC : A ≠ C := by rintro rfl; apply h; simp [cross]
  have ha : 0 < dist B C := dist_pos.mpr hBC
  have hb : 0 < dist A C := dist_pos.mpr hAC
  have hc : 0 < dist A B := dist_pos.mpr hAB
  have hp : 0 < dist A B + dist B C + dist A C := by linarith
  unfold cross at h
  constructor
  · rintro ⟨⟨s, ⟨hs0, hs1⟩, rfl⟩, ⟨u, ⟨hu0, hu1⟩, rfl⟩, hF, hG, hDE, hDF, hEG, hsum⟩
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hF hG
    obtain ⟨f, rfl⟩ := hF
    obtain ⟨g, rfl⟩ := hG
    rw [AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul] at hDE hDF hEG
    obtain ⟨k1, hk1⟩ := hDE
    obtain ⟨k2, hk2⟩ := hDF
    obtain ⟨k3, hk3⟩ := hEG
    have e10 := congrArg (fun v : Plane => v 0) hk1
    have e11 := congrArg (fun v : Plane => v 1) hk1
    have e20 := congrArg (fun v : Plane => v 0) hk2
    have e21 := congrArg (fun v : Plane => v 1) hk2
    have e30 := congrArg (fun v : Plane => v 0) hk3
    have e31 := congrArg (fun v : Plane => v 1) hk3
    simp [AffineMap.lineMap_apply_module, Units.smul_def] at e10 e11 e20 e21 e30 e31
    have hus : u = s := by
      have : (u - s) * ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) = 0 := by
        linear_combination (C 1 - B 1) * e10 - (C 0 - B 0) * e11
      have := (mul_eq_zero.mp this).resolve_right h; linarith
    subst hus
    have hk2s : (k2 : ℝ) = u := by
      have : ((k2 : ℝ) - u) * ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) = 0 := by
        linear_combination (C 1 - B 1) * e20 - (C 0 - B 0) * e21
      have := (mul_eq_zero.mp this).resolve_right h; linarith
    have hfs : f = u := by
      have : (f - u) * ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) = 0 := by
        linear_combination (-(A 1 - B 1)) * e20 + (A 0 - B 0) * e21 +
          ((A 1 - B 1) * (C 0 - A 0) - (A 0 - B 0) * (C 1 - A 1)) * hk2s
      have := (mul_eq_zero.mp this).resolve_right h; linarith
    have hgs : g = 1 - u := by
      have : (g - 1 + u) * ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) = 0 := by
        linear_combination (-(A 1 - B 1)) * e30 + (A 0 - B 0) * e31
      have := (mul_eq_zero.mp this).resolve_right h; linarith
    subst hfs hgs
    have hDF' : dist (AffineMap.lineMap B A f) (AffineMap.lineMap B C f) = f * dist A C := by
      have : AffineMap.lineMap B A f -ᵥ AffineMap.lineMap B C f = f • (A -ᵥ C) := by
        apply vec_ext <;> simp [AffineMap.lineMap_apply_module] <;> ring
      rw [dist_eq_norm_vsub, this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0,
        ← dist_eq_norm_vsub]
    have hEG' : dist (AffineMap.lineMap C A f) (AffineMap.lineMap B C (1 - f)) =
        f * dist A B := by
      have : AffineMap.lineMap C A f -ᵥ AffineMap.lineMap B C (1 - f) = f • (A -ᵥ B) := by
        apply vec_ext <;> simp [AffineMap.lineMap_apply_module] <;> ring
      rw [dist_eq_norm_vsub, this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0,
        ← dist_eq_norm_vsub]
    have hDE' : dist (AffineMap.lineMap B A f) (AffineMap.lineMap C A f) =
        (1 - f) * dist B C := by
      have : AffineMap.lineMap B A f -ᵥ AffineMap.lineMap C A f = (1 - f) • (B -ᵥ C) := by
        apply vec_ext <;> simp [AffineMap.lineMap_apply_module] <;> ring
      rw [dist_eq_norm_vsub, this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith),
        ← dist_eq_norm_vsub]
    rw [hDF', hEG', hDE'] at hsum
    have hf : f = dist B C / (dist A B + dist B C + dist A C) := by
      rw [eq_div_iff hp.ne']; linarith
    subst hf
    refine ⟨rfl, rfl, rfl, ?_⟩
    apply vec_ext <;> simp [AffineMap.lineMap_apply_module] <;> ring
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    set t := dist B C / (dist A B + dist B C + dist A C) with ht
    have ht0 : 0 < t := div_pos ha hp
    have ht1 : t < 1 := (div_lt_one hp).mpr (by linarith)
    refine ⟨⟨t, ⟨ht0.le, ht1.le⟩, rfl⟩, ⟨t, ⟨ht0.le, ht1.le⟩, rfl⟩,
      mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨t, rfl⟩,
      mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨1 - t, ?_⟩, ?_, ?_, ?_, ?_⟩
    · apply vec_ext <;> simp [AffineMap.lineMap_apply_module] <;> ring
    · rw [AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul]
      refine ⟨Units.mk0 (1 - t) (by linarith), ?_⟩
      apply vec_ext <;> simp [AffineMap.lineMap_apply_module] <;> ring
    · rw [AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul]
      refine ⟨Units.mk0 t ht0.ne', ?_⟩
      apply vec_ext <;> simp [AffineMap.lineMap_apply_module] <;> ring
    · rw [AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul]
      refine ⟨Units.mk0 t ht0.ne', ?_⟩
      apply vec_ext <;> simp [AffineMap.lineMap_apply_module] <;> ring
    · have e1 : AffineMap.lineMap B A t -ᵥ AffineMap.lineMap B C t = t • (A -ᵥ C) := by
        apply vec_ext <;> simp [AffineMap.lineMap_apply_module] <;> ring
      have e2 : AffineMap.lineMap C A t -ᵥ AffineMap.lineMap C B t = t • (A -ᵥ B) := by
        apply vec_ext <;> simp [AffineMap.lineMap_apply_module] <;> ring
      have e3 : AffineMap.lineMap B A t -ᵥ AffineMap.lineMap C A t = (1 - t) • (B -ᵥ C) := by
        apply vec_ext <;> simp [AffineMap.lineMap_apply_module] <;> ring
      rw [dist_eq_norm_vsub, dist_eq_norm_vsub, dist_eq_norm_vsub, e1, e2, e3, norm_smul,
        norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht0,
        abs_of_pos (by linarith), ← dist_eq_norm_vsub, ← dist_eq_norm_vsub,
        ← dist_eq_norm_vsub, ht]
      field_simp
      ring

private lemma angle_bisect (u w : Plane) :
    InnerProductGeometry.angle u (‖w‖ • u + ‖u‖ • w) =
      InnerProductGeometry.angle (‖w‖ • u + ‖u‖ • w) w := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  unfold InnerProductGeometry.angle
  congr 1
  have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [inner_add_right, inner_add_left, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  have e1 : ‖w‖ * ‖u‖ ^ 2 + ‖u‖ * inner ℝ u w = ‖u‖ * (‖u‖ * ‖w‖ + inner ℝ u w) := by ring
  have e2 : ‖w‖ * inner ℝ u w + ‖u‖ * ‖w‖ ^ 2 = ‖w‖ * (‖u‖ * ‖w‖ + inner ℝ u w) := by ring
  rw [e1, e2, mul_div_mul_left _ _ hu', mul_comm ‖‖w‖ • u + ‖u‖ • w‖ ‖w‖,
    mul_div_mul_left _ _ hw']

/-- Carroll's construction: the required line passes through the meeting point `H` of the
bisectors of the angles `B` and `C` (the in-centre, `H = (a A + b B + c C) / (a + b + c)`). -/
theorem problem17_construction (A B C : Plane) (h : cross A B C ≠ 0) :
    let p := dist A B + dist B C + dist A C
    let H : Plane := (dist B C / p) • A + (dist A C / p) • B + (dist A B / p) • C
    ∠ A B H = ∠ H B C ∧ ∠ A C H = ∠ H C B ∧
      Wbtw ℝ (AffineMap.lineMap B A (dist B C / p)) H (AffineMap.lineMap C A (dist B C / p)) := by
  intro p H
  have hAB : A ≠ B := by rintro rfl; apply h; simp [cross]
  have hBC : B ≠ C := by rintro rfl; apply h; simp [cross]
  have hAC : A ≠ C := by rintro rfl; apply h; simp [cross]
  have ha : 0 < dist B C := dist_pos.mpr hBC
  have hb : 0 < dist A C := dist_pos.mpr hAC
  have hc : 0 < dist A B := dist_pos.mpr hAB
  have hp : 0 < p := by simp only [p]; linarith
  have hp' : 0 < 1 / p := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have hH : H -ᵥ B = (1 / p) • (‖C -ᵥ B‖ • (A -ᵥ B) + ‖A -ᵥ B‖ • (C -ᵥ B)) := by
      rw [← dist_eq_norm_vsub, ← dist_eq_norm_vsub, dist_comm C B]
      apply vec_ext <;> simp [H, p] <;> field_simp <;> ring
    simp only [EuclideanGeometry.angle]
    rw [hH, InnerProductGeometry.angle_smul_right_of_pos _ _ hp',
      InnerProductGeometry.angle_smul_left_of_pos _ _ hp', angle_bisect]
  · have hH : H -ᵥ C = (1 / p) • (‖B -ᵥ C‖ • (A -ᵥ C) + ‖A -ᵥ C‖ • (B -ᵥ C)) := by
      rw [← dist_eq_norm_vsub, ← dist_eq_norm_vsub]
      apply vec_ext <;> simp [H, p] <;> field_simp <;> ring
    simp only [EuclideanGeometry.angle]
    rw [hH, InnerProductGeometry.angle_smul_right_of_pos _ _ hp',
      InnerProductGeometry.angle_smul_left_of_pos _ _ hp', angle_bisect]
  · refine ⟨dist A B / (dist A B + dist A C), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_le_one (by linarith)]; linarith
    · apply vec_ext <;> simp [H, p, AffineMap.lineMap_apply_module] <;> field_simp <;> ring

end PillowProblems.P17
