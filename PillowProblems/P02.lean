import PillowProblems.Basic

/-!
# Problem 2 (Pure Geometry, Plane)

**Question.**

> In a given Triangle to place a line parallel to the base, such that the portions of sides, intercepted between it and the base, shall be together equal to the base.

*(Carroll's solution: Chapter III, problem 2; text in `data/problems.json`.)*

**Lean reading.** The triangle is `ABC` with base `BC`, non-degenerate (`cross A B C ≠ 0`; for a
degenerate triangle `BC = AB + AC` and the only "solution" would be the point `A`). The required
line meets the sides `AB`, `AC` in `D`, `E`, which must lie on the closed sides (`Wbtw ℝ B D A`,
`Wbtw ℝ C E A`: the line is placed *in* the triangle); the line `DE` is parallel to `BC`
(mathlib's `AffineSubspace.Parallel`, which also forces `D ≠ E`); the intercepted portions are
`BD` and `CE`, and the condition is `BD + CE = BC`. `problem2` shows that these conditions hold
exactly for `D`, `E` dividing `BA`, `CA` in the ratio `BD / BA = CE / CA = BC / (AB + AC)`, so the
required line exists and is unique. `problem2_construction` verifies Carroll's synthesis: the
bisector of angle `A` meets `BC` at `F` (`∠BAF = ∠FAC`), and `BD = BF`, `CE = CF`.

**Status.** proved
-/

namespace PillowProblems.P02

open EuclideanGeometry

private lemma cross_eq_zero_of_wbtw {B A C : Plane} (h : Wbtw ℝ B A C) : cross A B C = 0 := by
  obtain ⟨r, -, rfl⟩ := h
  simp [cross, AffineMap.lineMap_apply_module]; ring

private lemma dist_lt (A B C : Plane) (h : cross A B C ≠ 0) :
    dist B C < dist A B + dist A C := by
  have h1 : dist B C ≤ dist B A + dist A C := dist_triangle B A C
  rcases h1.lt_or_eq with h1 | h1
  · rwa [dist_comm B A] at h1
  · exact absurd (cross_eq_zero_of_wbtw (dist_add_dist_eq_iff.mp h1.symm)) h

/-- The line `DE` (with `D` on side `AB`, `E` on side `AC`) is parallel to the base `BC` and cuts
off `BD + CE = BC` exactly when `BD / BA = CE / CA = BC / (AB + AC)`. In particular the required
line exists and is unique. -/
theorem problem2 (A B C : Plane) (h : cross A B C ≠ 0) (D E : Plane) :
    (Wbtw ℝ B D A ∧ Wbtw ℝ C E A ∧ (line[ℝ, D, E]).Parallel (line[ℝ, B, C]) ∧
        dist B D + dist C E = dist B C) ↔
      (D = AffineMap.lineMap B A (dist B C / (dist A B + dist A C)) ∧
        E = AffineMap.lineMap C A (dist B C / (dist A B + dist A C))) := by
  have hlt := dist_lt A B C h
  have hpos : 0 < dist A B + dist A C := lt_of_le_of_lt dist_nonneg hlt
  constructor
  · rintro ⟨⟨s, ⟨hs0, hs1⟩, rfl⟩, ⟨u, ⟨hu0, hu1⟩, rfl⟩, hpar, hsum⟩
    rw [AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul] at hpar
    obtain ⟨k, hk⟩ := hpar
    have h0 := congrArg (fun v : Plane => v 0) hk
    have h1 := congrArg (fun v : Plane => v 1) hk
    simp [AffineMap.lineMap_apply_module, Units.smul_def] at h0 h1
    have hus : u = s := by
      have : (u - s) * cross A B C = 0 := by
        unfold cross; linear_combination (C 1 - B 1) * h0 - (C 0 - B 0) * h1
      have := (mul_eq_zero.mp this).resolve_right h; linarith
    subst hus
    rw [dist_left_lineMap, dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg hu0,
      dist_comm B A, dist_comm C A] at hsum
    have : u = dist B C / (dist A B + dist A C) := by
      rw [eq_div_iff hpos.ne']; linarith
    subst this; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    set t := dist B C / (dist A B + dist A C) with ht
    have ht0 : 0 ≤ t := div_nonneg dist_nonneg hpos.le
    have ht1 : t < 1 := (div_lt_one hpos).mpr hlt
    refine ⟨⟨t, ⟨ht0, ht1.le⟩, rfl⟩, ⟨t, ⟨ht0, ht1.le⟩, rfl⟩, ?_, ?_⟩
    · rw [AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul]
      refine ⟨Units.mk0 (1 - t) (by linarith), ?_⟩
      ext i; fin_cases i <;> simp [AffineMap.lineMap_apply_module] <;> ring
    · rw [dist_left_lineMap, dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg ht0,
        dist_comm B A, dist_comm C A, ht]
      field_simp

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

/-- Carroll's construction: if the bisector of the angle `A` meets the base at `F`, then the
required points satisfy `BD = BF` and `CE = CF`. -/
theorem problem2_construction (A B C : Plane) (h : cross A B C ≠ 0) :
    let t := dist B C / (dist A B + dist A C)
    let D := AffineMap.lineMap B A t
    let E := AffineMap.lineMap C A t
    let F := AffineMap.lineMap B C (dist A B / (dist A B + dist A C))
    ∠ B A F = ∠ F A C ∧ Wbtw ℝ B F C ∧ dist B D = dist B F ∧ dist C E = dist C F := by
  intro t D E F
  have hlt := dist_lt A B C h
  have hpos : 0 < dist A B + dist A C := lt_of_le_of_lt dist_nonneg hlt
  have hs0 : 0 ≤ dist A B / (dist A B + dist A C) := div_nonneg dist_nonneg hpos.le
  have hs1 : dist A B / (dist A B + dist A C) ≤ 1 :=
    (div_le_one hpos).mpr (le_add_of_nonneg_right dist_nonneg)
  have ht0 : 0 ≤ t := div_nonneg dist_nonneg hpos.le
  refine ⟨?_, ⟨_, ⟨hs0, hs1⟩, rfl⟩, ?_, ?_⟩
  · have hF : F -ᵥ A = (1 / (dist A B + dist A C)) •
        (‖C -ᵥ A‖ • (B -ᵥ A) + ‖B -ᵥ A‖ • (C -ᵥ A)) := by
      rw [← dist_eq_norm_vsub, ← dist_eq_norm_vsub, dist_comm C A, dist_comm B A]
      ext i; fin_cases i <;> simp [F, AffineMap.lineMap_apply_module] <;> field_simp <;> ring
    have hpos' : 0 < 1 / (dist A B + dist A C) := by positivity
    simp only [EuclideanGeometry.angle]
    rw [hF, InnerProductGeometry.angle_smul_right_of_pos _ _ hpos',
      InnerProductGeometry.angle_smul_left_of_pos _ _ hpos', angle_bisect]
  · simp only [D, F]
    rw [dist_left_lineMap, dist_left_lineMap, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ht0, abs_of_nonneg hs0, dist_comm B A]
    simp only [t]; field_simp
  · simp only [E, F]
    rw [dist_left_lineMap, dist_comm C (AffineMap.lineMap B C _), dist_lineMap_right,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht0, abs_of_nonneg (by linarith),
      dist_comm C A]
    simp only [t]; field_simp; ring

end PillowProblems.P02
