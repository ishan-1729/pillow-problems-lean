import PillowProblems.Basic

/-!
# Problem 36 (Pure Geometry, Plane)

**Question.** *(dated 3/89)*

> In a given Triangle, to draw a line, from a Point on one side of it, to a Point on the other side, perpendicular to one of these sides, and equal to the sum of the portions, of these sides, intercepted between it and the base.

*(Carroll's solution: Chapter III, problem 36; text in `data/problems.json`.)*

**Lean reading.** `A B C` is a non-collinear triangle with base `BC`. The required line runs from `C'` on the
side `AB` to `B'` on the side `AC` (closed segments). As in Carroll's analysis it is perpendicular
to `AB` (right angle at `C'`); a line perpendicular to `AC` is the same statement with `B` and `C`
exchanged. The portions of the sides intercepted between it and the base are `BC'` and `CB'`.
`problem36` shows that such a line has the property iff `AB' = (AB + AC)/(1 + sin A + cos A)` and
`AC' = (AB + AC) cos A/(1 + sin A + cos A)`, so the line is unique. This is the position of
the line through Carroll's point `D`; his construction by the bisector of `∠ACE` and the `45°` line
at `B` is not itself formalized. `problem36_limits` proves Carroll's limits of possibility exactly:
the line exists iff `A ≤ 90°`, `B ≥ 45°` and `C ≥ 45° - A/2`. When `A = 90°` the line degenerates
into a piece of `AC`, with `C' = A`.

**Status.** proved
-/

namespace PillowProblems.P36

open scoped EuclideanGeometry RealInnerProductSpace
open Real

private lemma seg_param {X Y P : Plane} (h : P ∈ segment ℝ X Y) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ P = X + s • (Y - X) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h
  refine ⟨b, hb, by linarith, ?_⟩
  obtain rfl : a = 1 - b := by linarith
  module

private lemma seg_mem {X Y : Plane} {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    X + s • (Y - X) ∈ segment ℝ X Y :=
  ⟨1 - s, s, by linarith, h0, by ring, by module⟩

/-- `π/4 - α/2 ≤ γ` in trigonometric form (for `γ + α ≤ π`). With `α = 0` it says that
`π/4 ≤ γ` exactly when `cos γ ≤ sin γ`. -/
private lemma trig_cond {α γ : ℝ} (hα0 : 0 ≤ α) (hγ0 : 0 ≤ γ) (hαγ : γ + α ≤ π) :
    π / 4 - α / 2 ≤ γ ↔ cos γ * cos α ≤ sin γ * (1 + sin α) := by
  set φ := π / 4 - α / 2 with hφ
  have hcos : 0 < cos φ := by
    apply cos_pos_of_mem_Ioo; constructor <;> linarith [pi_pos]
  have h2φ : 2 * φ = π / 2 - α := by rw [hφ]; ring
  have h2 : 2 * cos φ ^ 2 = 1 + sin α := by
    rw [cos_sq φ, h2φ, cos_pi_div_two_sub]; ring
  have h3 : 2 * sin φ * cos φ = cos α := by
    rw [← sin_two_mul, h2φ, sin_pi_div_two_sub]
  have key : 2 * cos φ * sin (γ - φ) = sin γ * (1 + sin α) - cos γ * cos α := by
    rw [sin_sub]; linear_combination sin γ * h2 - cos γ * h3
  constructor
  · intro h
    have : 0 ≤ sin (γ - φ) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
    linarith [mul_nonneg (mul_nonneg zero_le_two hcos.le) this]
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have : sin (γ - φ) < 0 := sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith [pi_pos])
    linarith [mul_neg_of_pos_of_neg (mul_pos zero_lt_two hcos) this]

/-- `B'C' · AB` in terms of the parameters of `C' = A + s·AB` and `B' = A + r·AC`. -/
private lemma inner_eq (A B C : Plane) (r s : ℝ) :
    ⟪(A + r • (C - A)) - (A + s • (B - A)), B - A⟫ =
      dist A B * (r * dist A C * cos (∠ B A C) - s * dist A B) := by
  have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (B - A) (C - A)
  have hin : ⟪C - A, B - A⟫ = cos (∠ B A C) * (dist A B * dist A C) := by
    rw [real_inner_comm, ← h, EuclideanGeometry.angle]
    simp only [vsub_eq_sub]
    rw [dist_comm A B, dist_eq_norm, dist_comm A C, dist_eq_norm]
  have e1 : (A + r • (C - A)) - (A + s • (B - A)) = r • (C - A) - s • (B - A) := by abel
  rw [e1, inner_sub_left, inner_smul_left, inner_smul_left, hin, real_inner_self_eq_norm_sq,
    ← dist_eq_norm, dist_comm B A]
  simp only [RCLike.conj_to_real]
  ring

private lemma not_col {A B C : Plane} (hABC : ¬ Collinear ℝ {A, B, C}) :
    0 < dist A B ∧ 0 < dist A C ∧ 0 < sin (∠ B A C) := by
  refine ⟨dist_pos.mpr (ne₁₂_of_not_collinear hABC), dist_pos.mpr (ne₁₃_of_not_collinear hABC),
    ?_⟩
  apply EuclideanGeometry.sin_pos_of_not_collinear
  have : ({B, A, C} : Set Plane) = {A, B, C} := Set.insert_comm _ _ _
  rwa [this]

/-- The common computation: for `C' = A + s·AB` and `B' = A + r·AC` with `B'C' ⊥ AB`,
`AC' = AB' · cos A`, and `B'C' = BC' + CB'` exactly when `AB' · (1 + sin A + cos A) = AB + AC`. -/
private lemma core {A B C : Plane} (hABC : ¬ Collinear ℝ {A, B, C}) {r s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hperp : ⟪(A + r • (C - A)) - (A + s • (B - A)), B - A⟫ = 0) :
    s * dist A B = r * dist A C * cos (∠ B A C) ∧
    (dist (A + r • (C - A)) (A + s • (B - A)) =
        dist B (A + s • (B - A)) + dist C (A + r • (C - A)) ↔
      r * dist A C * (1 + sin (∠ B A C) + cos (∠ B A C)) = dist A B + dist A C) := by
  obtain ⟨hc0, hb0, hsin⟩ := not_col hABC
  rw [inner_eq] at hperp
  set c := dist A B with hc
  set b := dist A C with hb
  set co := cos (∠ B A C) with hco
  set si := sin (∠ B A C) with hsi
  have hnu : ‖B - A‖ = c := by rw [hc, dist_comm, dist_eq_norm]
  have hnv : ‖C - A‖ = b := by rw [hb, dist_comm, dist_eq_norm]
  have hpy : si ^ 2 + co ^ 2 = 1 := sin_sq_add_cos_sq _
  have hsc : s * c = r * b * co := by
    rcases mul_eq_zero.mp hperp with h | h
    · linarith
    · linarith
  refine ⟨hsc, ?_⟩
  have hin' : ⟪C - A, B - A⟫ = co * (c * b) := by
    have := inner_eq A B C 1 0
    simp only [one_smul, zero_smul, add_zero, add_sub_cancel_left, zero_mul, sub_zero,
      one_mul] at this
    rw [this]; ring
  have e1 : (A + r • (C - A)) - (A + s • (B - A)) = r • (C - A) - s • (B - A) := by abel
  have hq : ‖r • (C - A) - s • (B - A)‖ ^ 2 = r ^ 2 * b ^ 2 - 2 * (r * (s * (co * (c * b)))) +
      s ^ 2 * c ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, hin', hnu, hnv,
      Real.norm_of_nonneg hr0, Real.norm_of_nonneg hs0]
    simp only [RCLike.conj_to_real]
    ring
  have hd1 : dist (A + r • (C - A)) (A + s • (B - A)) = r * b * si := by
    rw [dist_eq_norm, e1, ← pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero, hq]
    linear_combination (-(r * b) ^ 2) * hpy + (s * c - r * b * co) * hsc
  have hd2 : dist B (A + s • (B - A)) = (1 - s) * c := by
    rw [dist_eq_norm, show B - (A + s • (B - A)) = (1 - s) • (B - A) by module, norm_smul, hnu,
      Real.norm_of_nonneg (by linarith)]
  have hd3 : dist C (A + r • (C - A)) = (1 - r) * b := by
    rw [dist_eq_norm, show C - (A + r • (C - A)) = (1 - r) • (C - A) by module, norm_smul, hnv,
      Real.norm_of_nonneg (by linarith)]
  rw [hd1, hd2, hd3]
  constructor
  · intro h; linear_combination h - hsc
  · intro h; linear_combination h + hsc

private lemma dist_from (X Y : Plane) {r : ℝ} (hr : 0 ≤ r) :
    dist X (X + r • (Y - X)) = r * dist X Y := by
  rw [dist_eq_norm', add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr, ← dist_eq_norm']

private lemma den_pos {A B C : Plane} (hABC : ¬ Collinear ℝ {A, B, C}) :
    0 < 1 + sin (∠ B A C) + cos (∠ B A C) := by
  have := (not_col hABC).2.2
  have := neg_one_le_cos (∠ B A C)
  linarith

/-- **Problem 36.** In a triangle `ABC` (base `BC`), let `C'` be a point of the side `AB` and `B'`
a point of the side `AC` with `B'C'` perpendicular to `AB`. Then `B'C'` equals the sum `BC' + CB'`
of the portions of the sides intercepted between it and the base if and only if
`AB' = (AB + AC) / (1 + sin A + cos A)` and `AC' = (AB + AC) cos A / (1 + sin A + cos A)`; so
there is at most one such line. -/
theorem problem36 (A B C : Plane) (hABC : ¬ Collinear ℝ {A, B, C}) (C' B' : Plane)
    (hC' : C' ∈ segment ℝ A B) (hB' : B' ∈ segment ℝ A C) (hperp : ⟪B' - C', B - A⟫ = 0) :
    dist B' C' = dist B C' + dist C B' ↔
      dist A B' = (dist A B + dist A C) / (1 + sin (∠ B A C) + cos (∠ B A C)) ∧
      dist A C' =
        (dist A B + dist A C) * cos (∠ B A C) / (1 + sin (∠ B A C) + cos (∠ B A C)) := by
  obtain ⟨s, hs0, hs1, rfl⟩ := seg_param hC'
  obtain ⟨r, hr0, hr1, rfl⟩ := seg_param hB'
  obtain ⟨hsc, hiff⟩ := core hABC hs0 hs1 hr0 hr1 hperp
  have hden := den_pos hABC
  rw [hiff, dist_from A C hr0, dist_from A B hs0]
  constructor
  · intro h
    refine ⟨by rw [eq_div_iff hden.ne']; exact h, ?_⟩
    rw [eq_div_iff hden.ne', hsc]
    linear_combination cos (∠ B A C) * h
  · rintro ⟨h, -⟩
    rw [h]
    field_simp

/-- **Problem 36, limits of possibility.** Such a line exists if and only if `A ≤ 90°`,
`B ≥ 45°` and `C ≥ 45° - A/2`, as Carroll states. -/
theorem problem36_limits (A B C : Plane) (hABC : ¬ Collinear ℝ {A, B, C}) :
    (∃ C' B' : Plane, C' ∈ segment ℝ A B ∧ B' ∈ segment ℝ A C ∧ ⟪B' - C', B - A⟫ = 0 ∧
        dist B' C' = dist B C' + dist C B') ↔
      ∠ B A C ≤ π / 2 ∧ π / 4 ≤ ∠ A B C ∧ π / 4 - ∠ B A C / 2 ≤ ∠ A C B := by
  obtain ⟨hc0, hb0, hsin⟩ := not_col hABC
  have hden := den_pos hABC
  have hBC : 0 < dist B C := dist_pos.mpr (ne₂₃_of_not_collinear hABC)
  -- the angles and the laws of cosines and sines
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi C
    (ne₁₂_of_not_collinear hABC).symm
  rw [EuclideanGeometry.angle_comm B C A, EuclideanGeometry.angle_comm C A B] at hsum
  have lA := EuclideanGeometry.law_cos B A C
  have lB := EuclideanGeometry.law_cos A B C
  have lC := EuclideanGeometry.law_cos A C B
  have sB := EuclideanGeometry.law_sin A B C
  have sC := EuclideanGeometry.law_sin A C B
  rw [EuclideanGeometry.angle_comm C A B] at sB
  rw [dist_comm B A, dist_comm C A] at lA
  rw [dist_comm C B] at lB sC
  rw [dist_comm B A] at sC
  rw [dist_comm C A] at sB
  set a := dist B C
  set b := dist A C
  set c := dist A B
  set co := cos (∠ B A C)
  set si := sin (∠ B A C)
  have hpy : si ^ 2 + co ^ 2 = 1 := sin_sq_add_cos_sq _
  have hcB : a * cos (∠ A B C) = c - b * co := by
    have : c * (a * cos (∠ A B C) - (c - b * co)) = 0 := by linear_combination (1 / 2) * lB + (1 / 2) * lA
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have hcC : a * cos (∠ A C B) = b - c * co := by
    have : b * (a * cos (∠ A C B) - (b - c * co)) = 0 := by linear_combination (1 / 2) * lC + (1 / 2) * lA
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  -- the existence of the line, in algebraic form
  have key : (∃ C' B' : Plane, C' ∈ segment ℝ A B ∧ B' ∈ segment ℝ A C ∧ ⟪B' - C', B - A⟫ = 0 ∧
        dist B' C' = dist B C' + dist C B') ↔
      0 ≤ co ∧ c ≤ b * (si + co) ∧ b * co ≤ c * (1 + si) := by
    constructor
    · rintro ⟨C', B', hC', hB', hperp, hd⟩
      obtain ⟨s, hs0, hs1, rfl⟩ := seg_param hC'
      obtain ⟨r, hr0, hr1, rfl⟩ := seg_param hB'
      obtain ⟨hsc, hiff⟩ := core hABC hs0 hs1 hr0 hr1 hperp
      have h := hiff.mp hd
      have hrb : 0 < r * b := by
        by_contra hn
        rw [not_lt] at hn
        linarith [mul_le_mul_of_nonneg_right hn hden.le]
      have hco : 0 ≤ co := by
        by_contra hn
        rw [not_le] at hn
        linarith [mul_nonneg hs0 hc0.le, mul_neg_of_pos_of_neg hrb hn]
      refine ⟨hco, ?_, ?_⟩
      · have e : b * (si + co) - c = (1 - r) * b * (1 + si + co) := by linear_combination h
        linarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hr1) hb0.le) hden.le]
      · have e : c * (1 + si) - b * co = (1 - s) * c * (1 + si + co) := by
          linear_combination (1 + si + co) * hsc + co * h
        linarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hs1) hc0.le) hden.le]
    · rintro ⟨h1, h2, h3⟩
      set y := (c + b) / (1 + si + co) with hy
      have hy0 : 0 < y := div_pos (by linarith) hden
      have hyd : y * (1 + si + co) = c + b := by rw [hy]; field_simp
      have hr0 : 0 ≤ y / b := div_nonneg hy0.le hb0.le
      have hr1 : y / b ≤ 1 := by
        rw [div_le_one hb0, hy, div_le_iff₀ hden]
        linarith [show b * (1 + si + co) = b + b * (si + co) by ring]
      have hs0 : 0 ≤ y * co / c := div_nonneg (mul_nonneg hy0.le h1) hc0.le
      have hs1 : y * co / c ≤ 1 := by
        rw [div_le_one hc0, hy, div_mul_eq_mul_div, div_le_iff₀ hden]
        linarith [show (c + b) * co = c * co + b * co by ring,
          show c * (1 + si + co) = c * (1 + si) + c * co by ring]
      have hperp : ⟪(A + (y / b) • (C - A)) - (A + (y * co / c) • (B - A)), B - A⟫ = 0 := by
        rw [inner_eq, div_mul_cancel₀ y hb0.ne', div_mul_cancel₀ (y * co) hc0.ne', sub_self,
          mul_zero]
      refine ⟨_, _, seg_mem hs0 hs1, seg_mem hr0 hr1, hperp, ?_⟩
      rw [(core hABC hs0 hs1 hr0 hr1 hperp).2, div_mul_cancel₀ y hb0.ne']
      linarith
  rw [key]
  -- the three conditions as angle conditions
  have hα0 := EuclideanGeometry.angle_nonneg B A C
  have hαπ := EuclideanGeometry.angle_le_pi B A C
  have hβ0 := EuclideanGeometry.angle_nonneg A B C
  have hγ0 := EuclideanGeometry.angle_nonneg A C B
  have c1 : 0 ≤ co ↔ ∠ B A C ≤ π / 2 := by
    constructor
    · intro h
      by_contra hn
      rw [not_le] at hn
      have := cos_neg_of_pi_div_two_lt_of_lt hn (by linarith [pi_pos])
      linarith
    · intro h
      exact cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], h⟩
  have c2 : c ≤ b * (si + co) ↔ π / 4 ≤ ∠ A B C := by
    have := trig_cond (α := 0) (γ := ∠ A B C) le_rfl hβ0 (by linarith)
    rw [cos_zero, sin_zero] at this
    simp only [zero_div, sub_zero, mul_one, add_zero] at this
    rw [this]
    have e : a * (sin (∠ A B C) - cos (∠ A B C)) = b * (si + co) - c := by
      linear_combination sB - hcB
    constructor
    · intro h
      have : 0 ≤ a * (sin (∠ A B C) - cos (∠ A B C)) := by rw [e]; linarith
      have := (mul_nonneg_iff_of_pos_left hBC).mp this
      linarith
    · intro h
      have : 0 ≤ a * (sin (∠ A B C) - cos (∠ A B C)) := mul_nonneg hBC.le (by linarith)
      linarith
  have c3 : b * co ≤ c * (1 + si) ↔ π / 4 - ∠ B A C / 2 ≤ ∠ A C B := by
    rw [trig_cond hα0 hγ0 (by linarith)]
    have e : a * (sin (∠ A C B) * (1 + si) - cos (∠ A C B) * co) = c * (1 + si) - b * co := by
      linear_combination (1 + si) * sC - co * hcC + c * hpy
    constructor
    · intro h
      have : 0 ≤ a * (sin (∠ A C B) * (1 + si) - cos (∠ A C B) * co) := by rw [e]; linarith
      have := (mul_nonneg_iff_of_pos_left hBC).mp this
      linarith
    · intro h
      have : 0 ≤ a * (sin (∠ A C B) * (1 + si) - cos (∠ A C B) * co) :=
        mul_nonneg hBC.le (by linarith)
      linarith
  rw [c1, c2, c3]

end PillowProblems.P36
