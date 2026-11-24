import PillowProblems.Basic

/-!
# Problem 18 (Pure Geometry, Plane, Trigonometry: Plane)

**Question.** *(dated 11/89)*

> Find a Point, in the base of a given Triangle, such that, if from it perpendiculars be dropped upon the sides, the line joining their extremities shall be parallel to the base. (1) Trigonometrically. (2) Geometrically.

**Answer.**

> (1) Divide base \(BC\), at \(E\), so that \(\dfrac{BE}{EC} = \dfrac{\sin 2C}{\sin 2B}\).
>
> (2) At \(B\), \(C\), make right angles \(ABD\), \(ACD\); and join \(AD\) cutting \(BC\) at \(E\), which is the required Point.

*(Carroll's solution: Chapter III, problem 18; text in `data/problems.json`.)*

**Lean reading.** The triangle is nondegenerate; `F`, `G` are the feet of the perpendiculars from `E` on
the lines `AB`, `AC` (`IsFoot`; they fall on the extensions of the sides when an angle is
obtuse), and "`FG` parallel to the base" is `G - F = k (C - B)` for some `k`. Carroll's
`BE / EC = sin 2C / sin 2B` is stated cross-multiplied, `BE · sin 2B = EC · sin 2C`, which also
covers a right angle at `B` (`sin 2B = 0`, the point is then `C`). `problem18_a` is the
statement for `E` in the base `BC` (lengths `BE`, `EC`); `problem18_line` is the same on the
whole line `BC` with signed lengths `BE = τ·BC`, `EC = (1 - τ)·BC`. Since the condition is
linear in `τ`, it determines the point uniquely when `sin 2B + sin 2C ≠ 0` (inside the base
when the triangle is acute); when `|B - C| = 90°` there is no such point. `problem18_b` is
part (2): the point `D` with right angles `ABD`, `ACD` exists, and if `AD` meets the line `BC`
at `E` then `FG ∥ BC` and `E` satisfies part (1). Carroll takes for granted that `AD` cuts the
base; `problem18_b_cuts` proves that it does, at exactly one point of the base, whenever the
base angles `B`, `C` are acute (for a right or obtuse base angle the point falls at or beyond an
end of the base, or does not exist).

**Status.** proved
-/

namespace PillowProblems.P18

open scoped EuclideanGeometry RealInnerProductSpace

/-- `F` is the foot of the perpendicular dropped from `E` upon the line `XY`. -/
def IsFoot (E X Y F : Plane) : Prop :=
  F ∈ line[ℝ, X, Y] ∧ ⟪E - F, Y - X⟫ = 0

private lemma inner2 (P Q : Plane) : ⟪P, Q⟫ = P 0 * Q 0 + P 1 * Q 1 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]; ring

private lemma normsq2 (P : Plane) : ‖P‖ ^ 2 = P 0 ^ 2 + P 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]; simp [Fin.sum_univ_two]

private lemma ext2 {P Q : Plane} (h0 : P 0 = Q 0) (h1 : P 1 = Q 1) : P = Q := by
  ext i; fin_cases i <;> simp [h0, h1]

private lemma mem_line {B C X : Plane} : X ∈ line[ℝ, B, C] ↔ ∃ t : ℝ, X = B + t • (C - B) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  constructor
  · rintro ⟨t, ht⟩; exact ⟨t, by rw [← ht]; abel⟩
  · rintro ⟨t, ht⟩; exact ⟨t, by rw [ht]; abel⟩

/-- The foot of the perpendicular from `E` on `AX` is `A + φ (X - A)` with
`φ |AX|² = ⟪E - A, X - A⟫`. -/
private lemma foot_param {E A X F : Plane} (hF : IsFoot E A X F) :
    ∃ φ : ℝ, F = A + φ • (X - A) ∧ φ * ‖X - A‖ ^ 2 = ⟪E - A, X - A⟫ := by
  obtain ⟨hl, hp⟩ := hF
  obtain ⟨φ, rfl⟩ := mem_line.1 hl
  refine ⟨φ, rfl, ?_⟩
  rw [inner2] at hp ⊢; rw [normsq2]
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hp ⊢
  linear_combination -hp

/-- `FG ∥ BC` iff the feet divide `AB`, `AC` in the same ratio (`AF : FB = AG : GC`). -/
private lemma par_iff {A B C : Plane} (hT : cross A B C ≠ 0) (φ ψ : ℝ) :
    (∃ k : ℝ, (A + ψ • (C - A)) - (A + φ • (B - A)) = k • (C - B)) ↔ ψ = φ := by
  constructor
  · rintro ⟨k, hk⟩
    have h0 := congrArg (· 0) hk
    have h1 := congrArg (· 1) hk
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at h0 h1
    have : (ψ - φ) * cross A B C = 0 := by
      unfold cross
      linear_combination (C 1 - B 1) * h0 - (C 0 - B 0) * h1
    linarith [(mul_eq_zero.1 this).resolve_right hT]
  · rintro rfl
    exact ⟨ψ, by module⟩

/-- Trigonometric form of the angle data: `sin 2B · |BA|² |BC|² = 2 |T| ⟪BA, BC⟫`. -/
private lemma sin_two_angle (A B C : Plane) :
    Real.sin (2 * ∠ A B C) * (‖A - B‖ ^ 2 * ‖C - B‖ ^ 2) =
      2 * |cross A B C| * ⟪A - B, C - B⟫ := by
  have hs := InnerProductGeometry.sin_angle_mul_norm_mul_norm (A - B) (C - B)
  have hc := InnerProductGeometry.cos_angle_mul_norm_mul_norm (A - B) (C - B)
  have hS : ⟪A - B, A - B⟫ * ⟪C - B, C - B⟫ - ⟪A - B, C - B⟫ * ⟪A - B, C - B⟫ =
      cross A B C ^ 2 := by
    simp only [inner2, cross, PiLp.sub_apply]; ring
  rw [hS, Real.sqrt_sq_eq_abs] at hs
  rw [EuclideanGeometry.angle, Real.sin_two_mul]
  simp only [vsub_eq_sub] at hs hc ⊢
  rw [← hc, ← hs]; ring

private lemma sin_two_angle' (A B C : Plane) :
    Real.sin (2 * ∠ A C B) * (‖A - C‖ ^ 2 * ‖B - C‖ ^ 2) =
      2 * |cross A B C| * ⟪A - C, B - C⟫ := by
  rw [sin_two_angle A C B]
  congr 2
  rw [← abs_neg]; congr 1; simp only [cross]; ring

private lemma ne_of_cross {A B C : Plane} (hT : cross A B C ≠ 0) : A ≠ B ∧ B ≠ C ∧ C ≠ A := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> apply hT <;> simp only [cross] <;> ring

private lemma cramer (u0 u1 v0 v1 p q : ℝ) (h : u0 * v1 - u1 * v0 ≠ 0) :
    ∃ x y : ℝ, u0 * x + u1 * y = p ∧ v0 * x + v1 * y = q :=
  ⟨(p * v1 - u1 * q) / (u0 * v1 - u1 * v0), (u0 * q - v0 * p) / (u0 * v1 - u1 * v0),
    by field_simp; ring,
    by rw [mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff h]; ring⟩

/-- **Problem 18 (1)**, on the whole line `BC`, with signed lengths `BE = τ·BC`, `EC = (1-τ)·BC`:
the perpendiculars from `E` have feet `F`, `G` with `FG ∥ BC` iff `BE · sin 2B = EC · sin 2C`. -/
theorem problem18_line (A B C E F G : Plane) (hT : cross A B C ≠ 0) (τ : ℝ)
    (hE : E = B + τ • (C - B)) (hF : IsFoot E A B F) (hG : IsFoot E A C G) :
    (∃ k : ℝ, G - F = k • (C - B)) ↔
      τ * Real.sin (2 * ∠ A B C) = (1 - τ) * Real.sin (2 * ∠ A C B) := by
  subst hE
  obtain ⟨hAB, hBC, hCA⟩ := ne_of_cross hT
  obtain ⟨φ, rfl, hφ⟩ := foot_param hF
  obtain ⟨ψ, rfl, hψ⟩ := foot_param hG
  rw [par_iff hT]
  have hu : 0 < ‖A - B‖ ^ 2 := by have := norm_pos_iff.2 (sub_ne_zero.2 hAB); positivity
  have hv : 0 < ‖A - C‖ ^ 2 := by have := norm_pos_iff.2 (sub_ne_zero.2 hCA.symm); positivity
  have hw : 0 < ‖C - B‖ ^ 2 := by have := norm_pos_iff.2 (sub_ne_zero.2 hBC.symm); positivity
  have hS : 0 < |cross A B C| := abs_pos.2 hT
  have sB := sin_two_angle A B C
  have sC := sin_two_angle' A B C
  have nBC : ‖B - C‖ ^ 2 = ‖C - B‖ ^ 2 := by rw [norm_sub_rev]
  rw [nBC] at sC
  set X := Real.sin (2 * ∠ A B C)
  set Y := Real.sin (2 * ∠ A C B)
  -- the condition `ψ = φ` is a polynomial condition on `τ`
  have key : ψ = φ ↔ τ * ⟪A - B, C - B⟫ * ‖A - C‖ ^ 2 - (1 - τ) * ⟪A - C, B - C⟫ * ‖A - B‖ ^ 2
      = 0 := by
    have nAB : ‖B - A‖ ^ 2 = ‖A - B‖ ^ 2 := by rw [norm_sub_rev]
    have nAC : ‖C - A‖ ^ 2 = ‖A - C‖ ^ 2 := by rw [norm_sub_rev]
    rw [nAB] at hφ; rw [nAC] at hψ
    have e : ψ * (‖A - B‖ ^ 2 * ‖A - C‖ ^ 2) - φ * (‖A - B‖ ^ 2 * ‖A - C‖ ^ 2) =
        τ * ⟪A - B, C - B⟫ * ‖A - C‖ ^ 2 - (1 - τ) * ⟪A - C, B - C⟫ * ‖A - B‖ ^ 2 := by
      have i1 : ⟪B + τ • (C - B) - A, B - A⟫ = (1 - τ) * ‖A - B‖ ^ 2 + τ * ⟪A - B, A - C⟫ := by
        rw [normsq2]; simp only [inner2, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
          smul_eq_mul]; ring
      have i2 : ⟪B + τ • (C - B) - A, C - A⟫ = (1 - τ) * ⟪A - B, A - C⟫ + τ * ‖A - C‖ ^ 2 := by
        rw [normsq2]; simp only [inner2, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
          smul_eq_mul]; ring
      have i3 : ⟪A - B, C - B⟫ = ‖A - B‖ ^ 2 - ⟪A - B, A - C⟫ := by
        rw [normsq2]; simp only [inner2, PiLp.sub_apply]; ring
      have i4 : ⟪A - C, B - C⟫ = ‖A - C‖ ^ 2 - ⟪A - B, A - C⟫ := by
        rw [normsq2]; simp only [inner2, PiLp.sub_apply]; ring
      rw [i1] at hφ; rw [i2] at hψ; rw [i3, i4]
      linear_combination ‖A - B‖ ^ 2 * hψ - ‖A - C‖ ^ 2 * hφ
    constructor
    · intro h; rw [h] at e; linarith
    · intro h; rw [h] at e
      have : (ψ - φ) * (‖A - B‖ ^ 2 * ‖A - C‖ ^ 2) = 0 := by linarith
      linarith [(mul_eq_zero.1 this).resolve_right (by positivity)]
  rw [key]
  -- translate into the sines of the doubled angles
  constructor
  · intro h
    have : (τ * X - (1 - τ) * Y) * (‖A - B‖ ^ 2 * ‖C - B‖ ^ 2 * ‖A - C‖ ^ 2) = 0 := by
      linear_combination (τ * ‖A - C‖ ^ 2) * sB - ((1 - τ) * ‖A - B‖ ^ 2) * sC +
        (2 * |cross A B C|) * h
    have := (mul_eq_zero.1 this).resolve_right (by positivity)
    linarith
  · intro h
    have : 2 * |cross A B C| * (τ * ⟪A - B, C - B⟫ * ‖A - C‖ ^ 2 -
        (1 - τ) * ⟪A - C, B - C⟫ * ‖A - B‖ ^ 2) = 0 := by
      linear_combination (-(τ * ‖A - C‖ ^ 2)) * sB + ((1 - τ) * ‖A - B‖ ^ 2) * sC +
        (‖A - B‖ ^ 2 * ‖C - B‖ ^ 2 * ‖A - C‖ ^ 2) * h
    exact (mul_eq_zero.1 this).resolve_left (by positivity)

/-- **Problem 18 (1)**, as Carroll states it, for `E` in the base `BC`:
`FG ∥ BC` iff `BE · sin 2B = EC · sin 2C`, i.e. `BE / EC = sin 2C / sin 2B`. -/
theorem problem18_a (A B C E F G : Plane) (hT : cross A B C ≠ 0) (hE : E ∈ segment ℝ B C)
    (hF : IsFoot E A B F) (hG : IsFoot E A C G) :
    (∃ k : ℝ, G - F = k • (C - B)) ↔
      dist B E * Real.sin (2 * ∠ A B C) = dist E C * Real.sin (2 * ∠ A C B) := by
  obtain ⟨-, hBC, -⟩ := ne_of_cross hT
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hE
  have hE' : a • B + b • C = B + b • (C - B) := by
    rw [show a = 1 - b by linarith]; module
  rw [problem18_line A B C _ F G hT b hE' hF hG, hE']
  have d1 : dist B (B + b • (C - B)) = b * dist B C := by
    rw [dist_eq_norm, show B - (B + b • (C - B)) = -(b • (C - B)) by abel, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hb, ← dist_eq_norm, dist_comm]
  have d2 : dist (B + b • (C - B)) C = (1 - b) * dist B C := by
    rw [dist_eq_norm, show B + b • (C - B) - C = (1 - b) • (B - C) by module, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by linarith), ← dist_eq_norm]
  rw [d1, d2]
  have hd : 0 < dist B C := dist_pos.2 hBC
  constructor
  · intro h; linear_combination dist B C * h
  · intro h
    have : (b * Real.sin (2 * ∠ A B C) - (1 - b) * Real.sin (2 * ∠ A C B)) * dist B C = 0 := by
      linear_combination h
    linarith [(mul_eq_zero.1 this).resolve_right hd.ne']

/-- **Problem 18 (2)**: the geometric construction. The point `D` with right angles `ABD`, `ACD`
exists; and if `AD` cuts the base at `E` (`E = B + τ (C - B)`), then the perpendiculars from `E`
have feet `F`, `G` with `FG ∥ BC` (so `E` is the point of part (1)). -/
theorem problem18_b (A B C : Plane) (hT : cross A B C ≠ 0) :
    (∃ D : Plane, ⟪A - B, D - B⟫ = 0 ∧ ⟪A - C, D - C⟫ = 0) ∧
    ∀ D E F G : Plane, ∀ τ : ℝ, ⟪A - B, D - B⟫ = 0 → ⟪A - C, D - C⟫ = 0 →
      E ∈ line[ℝ, A, D] → E = B + τ • (C - B) → IsFoot E A B F → IsFoot E A C G →
      (∃ k : ℝ, G - F = k • (C - B)) ∧
        τ * Real.sin (2 * ∠ A B C) = (1 - τ) * Real.sin (2 * ∠ A C B) := by
  refine ⟨?_, ?_⟩
  · -- solve the two linear equations for `D` by Cramer's rule
    have hdet : (A 0 - B 0) * (A 1 - C 1) - (A 1 - B 1) * (A 0 - C 0) ≠ 0 := by
      intro h; apply hT; simp only [cross]; linear_combination h
    obtain ⟨x, y, h1, h2⟩ := cramer (A 0 - B 0) (A 1 - B 1) (A 0 - C 0) (A 1 - C 1)
      ((A 0 - B 0) * B 0 + (A 1 - B 1) * B 1) ((A 0 - C 0) * C 0 + (A 1 - C 1) * C 1) hdet
    refine ⟨pt x y, ?_, ?_⟩ <;> rw [inner2] <;> simp only [PiLp.sub_apply, pt_zero, pt_one]
    · linear_combination h1
    · linear_combination h2
  · intro D E F G τ hD1 hD2 hE1 hE2 hF hG
    obtain ⟨σ, hσ⟩ := mem_line.1 hE1
    obtain ⟨φ, rfl, hφ⟩ := foot_param hF
    obtain ⟨ψ, rfl, hψ⟩ := foot_param hG
    obtain ⟨hAB, -, hCA⟩ := ne_of_cross hT
    have hu : 0 < ‖B - A‖ ^ 2 := by have := norm_pos_iff.2 (sub_ne_zero.2 hAB.symm); positivity
    have hv : 0 < ‖C - A‖ ^ 2 := by have := norm_pos_iff.2 (sub_ne_zero.2 hCA); positivity
    -- `AF : AB = AE : AD = AG : AC`
    have e1 : φ = σ := by
      have : (φ - σ) * ‖B - A‖ ^ 2 = 0 := by
        rw [hσ, normsq2] at hφ; rw [normsq2]
        rw [inner2] at hD1 hφ
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hD1 hφ ⊢
        linear_combination hφ - σ * hD1
      linarith [(mul_eq_zero.1 this).resolve_right hu.ne']
    have e2 : ψ = σ := by
      have : (ψ - σ) * ‖C - A‖ ^ 2 = 0 := by
        rw [hσ, normsq2] at hψ; rw [normsq2]
        rw [inner2] at hD2 hψ
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hD2 hψ ⊢
        linear_combination hψ - σ * hD2
      linarith [(mul_eq_zero.1 this).resolve_right hv.ne']
    have hpar : ∃ k : ℝ, (A + ψ • (C - A)) - (A + φ • (B - A)) = k • (C - B) :=
      (par_iff hT φ ψ).2 (by rw [e1, e2])
    exact ⟨hpar, (problem18_line A B C E _ _ hT τ hE2 ⟨(mem_line.2 ⟨φ, rfl⟩), hF.2⟩
      ⟨(mem_line.2 ⟨ψ, rfl⟩), hG.2⟩).1 hpar⟩

/-- Feet of perpendiculars exist. -/
private lemma foot_exists (E X Y : Plane) (hXY : X ≠ Y) : ∃ F, IsFoot E X Y F := by
  have hn : 0 < (Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2 := by
    have h := pow_pos (norm_pos_iff.2 (sub_ne_zero.2 hXY.symm)) 2
    rw [normsq2] at h; simpa using h
  refine ⟨X + (((E 0 - X 0) * (Y 0 - X 0) + (E 1 - X 1) * (Y 1 - X 1)) /
    ((Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2)) • (Y - X), mem_line.2 ⟨_, rfl⟩, ?_⟩
  rw [inner2]
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- An acute angle has a positive inner product. -/
private lemma inner_pos_of_acute {A B C : Plane} (h : ∠ A B C < Real.pi / 2) :
    0 < ⟪A - B, C - B⟫ := by
  rcases lt_or_ge 0 ⟪A - B, C - B⟫ with h' | h'
  · exact h'
  · have := InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.1 h'
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub] at h
    linarith

/-- **Problem 18 (2)**, completed: when the base angles `B`, `C` are acute, the line `AD` does cut
the base `BC`, at exactly one point `E` (which by `problem18_b` is the required point). -/
theorem problem18_b_cuts (A B C D : Plane) (hT : cross A B C ≠ 0)
    (hB : ∠ A B C < Real.pi / 2) (hC : ∠ A C B < Real.pi / 2)
    (hD1 : ⟪A - B, D - B⟫ = 0) (hD2 : ⟪A - C, D - C⟫ = 0) :
    ∃! E : Plane, E ∈ segment ℝ B C ∧ E ∈ line[ℝ, A, D] := by
  obtain ⟨hAB, hBC, hCA⟩ := ne_of_cross hT
  have hS : 0 < |cross A B C| := abs_pos.2 hT
  have ib := inner_pos_of_acute hB
  have ic := inner_pos_of_acute hC
  have hu : 0 < ‖A - B‖ ^ 2 := by have := norm_pos_iff.2 (sub_ne_zero.2 hAB); positivity
  have hv : 0 < ‖A - C‖ ^ 2 := by have := norm_pos_iff.2 (sub_ne_zero.2 hCA.symm); positivity
  have hw : 0 < ‖C - B‖ ^ 2 := by have := norm_pos_iff.2 (sub_ne_zero.2 hBC.symm); positivity
  have nBC : ‖B - C‖ ^ 2 = ‖C - B‖ ^ 2 := by rw [norm_sub_rev]
  have sB := sin_two_angle A B C
  have sC := sin_two_angle' A B C
  rw [nBC] at sC
  set X := Real.sin (2 * ∠ A B C)
  set Y := Real.sin (2 * ∠ A C B)
  have hX : 0 < X := by
    have h1 : 0 < X * (‖A - B‖ ^ 2 * ‖C - B‖ ^ 2) := by
      rw [sB]; exact mul_pos (mul_pos two_pos hS) ib
    exact (pos_iff_pos_of_mul_pos h1).2 (by positivity)
  have hY : 0 < Y := by
    have h1 : 0 < Y * (‖A - C‖ ^ 2 * ‖C - B‖ ^ 2) := by
      rw [sC]; exact mul_pos (mul_pos two_pos hS) ic
    exact (pos_iff_pos_of_mul_pos h1).2 (by positivity)
  have hXY : X + Y ≠ 0 := by positivity
  -- the point `E` of part (1)
  set τ := Y / (X + Y) with hτ
  have hτX : τ * X = (1 - τ) * Y := by rw [hτ]; field_simp; ring
  refine ⟨B + τ • (C - B), ⟨⟨1 - τ, τ, ?_, ?_, by ring, by module⟩, ?_⟩, ?_⟩
  · rw [hτ, sub_nonneg, div_le_one (by positivity)]; linarith
  · positivity
  · -- `E` lies on `AD`: `E - A = φ (D - A)`, where `AF = φ AB`, `AG = φ AC`
    obtain ⟨F, hF⟩ := foot_exists (B + τ • (C - B)) A B hAB
    obtain ⟨G, hG⟩ := foot_exists (B + τ • (C - B)) A C hCA.symm
    have hpar := (problem18_line A B C _ F G hT τ rfl hF hG).2 hτX
    obtain ⟨φ, rfl, hφ⟩ := foot_param hF
    obtain ⟨ψ, rfl, hψ⟩ := foot_param hG
    have e := (par_iff hT φ ψ).1 hpar
    rw [e] at hψ
    rw [normsq2, inner2] at hφ hψ
    rw [inner2] at hD1 hD2
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hφ hψ hD1 hD2
    unfold cross at hT
    rw [mem_line]
    refine ⟨φ, ext2 ?_ ?_⟩ <;>
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] <;>
      apply mul_right_cancel₀ hT
    · linear_combination (C 1 - A 1) * (-hφ + φ * hD1) - (B 1 - A 1) * (-hψ + φ * hD2)
    · linear_combination (B 0 - A 0) * (-hψ + φ * hD2) - (C 0 - A 0) * (-hφ + φ * hD1)
  · rintro E' ⟨⟨a, b, ha, hb, hab, rfl⟩, hl⟩
    have hE' : a • B + b • C = B + b • (C - B) := by
      rw [show a = 1 - b by linarith]; module
    obtain ⟨F, hF⟩ := foot_exists (a • B + b • C) A B hAB
    obtain ⟨G, hG⟩ := foot_exists (a • B + b • C) A C hCA.symm
    have := ((problem18_b A B C hT).2 D _ F G b hD1 hD2 hl hE' hF hG).2
    have hb' : b = τ := by
      rw [hτ, eq_div_iff hXY]; linarith
    rw [hE', hb']

end PillowProblems.P18
