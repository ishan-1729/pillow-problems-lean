import PillowProblems.Basic

/-!
# Problem 46 (Pure Geometry, Plane)

**Question.** *(dated 19/11/87)*

> In a given Triangle, whose base is divided at a given Point, inscribe a Triangle, having its angles equal to given angles, and having an assigned vertex at the given Point.

*(Carroll's solution: Chapter III, problem 46; text in `data/problems.json`.)*

**Lean reading.** `A B C` is a triangle (`cross A B C ≠ 0`), `D` a point strictly between `B` and `C`, and the
given angles are `δ, ε, φ > 0` with `δ + ε + φ = π`. `δ` belongs at the assigned vertex `D`, `ε` at
the vertex `E` on `CA`, and `φ` at the vertex `F` on `AB`; the other assignment is the same
statement with `ε, φ` exchanged. Angles are mathlib's unoriented angles, so a triangle and its
mirror image both count. "Inscribe" is read with `E, F` on the side *lines* `CA, AB`, which is how
Carroll's construction produces them: he never checks that they fall within the sides, and on the
closed sides a solution need not exist. Added hypothesis: `δ ≠ A` and `δ + A ≠ π`. In those
excluded cases, turning `DE` through `±δ` about `D` maps line `CA` to a line parallel to `AB`, so
one orientation gives no triangle or infinitely many. Under it the theorem gives the complete answer:
exactly two such triangles, one of each orientation. Carroll's circle construction is not
formalized; the proof locates `E, F` by the spiral similarity about `D`. `problem46_nonvacuous`
exhibits data satisfying the hypotheses.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P46

open scoped EuclideanGeometry RealInnerProductSpace
open Real

/-- The triangle `DEF` has the angles `δ, ε, φ` at `D, E, F`. -/
def HasAngles (D E F : Plane) (δ ε φ : ℝ) : Prop :=
  ∠ E D F = δ ∧ ∠ D E F = ε ∧ ∠ D F E = φ

private lemma inner_coord (P Q : Plane) : ⟪P, Q⟫ = P 0 * Q 0 + P 1 * Q 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

private lemma norm_sq_coord (P : Plane) : ‖P‖ ^ 2 = P 0 ^ 2 + P 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]

private lemma plane_ext {P Q : Plane} (h0 : P 0 = Q 0) (h1 : P 1 = Q 1) : P = Q := by
  ext i; fin_cases i <;> simp [h0, h1]

private lemma line_param {X Y P : Plane} (h : P ∈ line[ℝ, X, Y]) :
    ∃ s : ℝ, P 0 = X 0 + s * (Y 0 - X 0) ∧ P 1 = X 1 + s * (Y 1 - X 1) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at h
  obtain ⟨s, rfl⟩ := h
  refine ⟨s, ?_, ?_⟩ <;> simp [AffineMap.lineMap_apply_module'] <;> ring

private lemma line_mem (X Y : Plane) (s : ℝ) : X + s • (Y - X) ∈ line[ℝ, X, Y] := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  exact ⟨s, by rw [AffineMap.lineMap_apply_module']; abel⟩

/-- An angle is determined by its cosine. -/
private lemma angle_of_cos {x y : Plane} {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π)
    (hx : x ≠ 0) (hy : y ≠ 0) (h : ⟪x, y⟫ = cos θ * (‖x‖ * ‖y‖)) :
    InnerProductGeometry.angle x y = θ := by
  apply injOn_cos ⟨InnerProductGeometry.angle_nonneg x y, InnerProductGeometry.angle_le_pi x y⟩
    ⟨h0, hπ⟩
  rw [InnerProductGeometry.cos_angle, h]
  have : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  field_simp

/-- `F - D` is `E - D` turned through the angle `σ δ` (`σ = ±1`, `cd = cos δ`, `sd = sin δ`) and
scaled by `k`. -/
private def Rel (k cd sd σ : ℝ) (D E F : Plane) : Prop :=
  F 0 - D 0 = k * (cd * (E 0 - D 0) - σ * sd * (E 1 - D 1)) ∧
  F 1 - D 1 = k * (cd * (E 1 - D 1) + σ * sd * (E 0 - D 0))

/-- A triangle `DEF` has the angles `δ, ε, φ` exactly when `DF` is `DE` turned through `± δ` and
scaled by `sin ε / sin φ`. -/
private lemma char {D E F : Plane} {δ ε φ : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hφ : 0 < φ)
    (hsum : δ + ε + φ = π) :
    HasAngles D E F δ ε φ ↔
      E ≠ D ∧ ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ Rel (sin ε / sin φ) (cos δ) (sin δ) σ D E F := by
  have hδπ : δ < π := by linarith
  have hεπ : ε < π := by linarith
  have hφπ : φ < π := by linarith
  have sδ := sin_pos_of_pos_of_lt_pi hδ hδπ
  have sε := sin_pos_of_pos_of_lt_pi hε hεπ
  have sφ := sin_pos_of_pos_of_lt_pi hφ hφπ
  have hφsum : sin φ = sin δ * cos ε + cos δ * sin ε := by
    rw [show φ = π - (δ + ε) by linarith, sin_pi_sub, sin_add]
  have pyδ := sin_sq_add_cos_sq δ
  have pyε := sin_sq_add_cos_sq ε
  set k := sin ε / sin φ with hk
  have hk0 : 0 < k := div_pos sε sφ
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hED : E ≠ D := by
      rintro rfl
      rw [EuclideanGeometry.angle_self_left] at h1 h2
      linarith
    have hFD : F ≠ D := by
      rintro rfl
      rw [EuclideanGeometry.angle_self_right] at h1
      rw [EuclideanGeometry.angle_self_left] at h3
      linarith
    refine ⟨hED, ?_⟩
    have hx : E - D ≠ 0 := sub_ne_zero.mpr hED
    have hy : F - D ≠ 0 := sub_ne_zero.mpr hFD
    have hlaw := EuclideanGeometry.law_sin F E D
    rw [EuclideanGeometry.angle_comm F E D, h2, h3, dist_eq_norm, dist_comm, dist_eq_norm] at hlaw
    have hcos : ⟪E - D, F - D⟫ = cos δ * (‖E - D‖ * ‖F - D‖) := by
      rw [← h1, EuclideanGeometry.angle, InnerProductGeometry.cos_angle]
      simp only [vsub_eq_sub]
      have : ‖E - D‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have : ‖F - D‖ ≠ 0 := norm_ne_zero_iff.mpr hy
      field_simp
    set n := ‖E - D‖ with hn
    set m := ‖F - D‖ with hm
    have hn0 : 0 < n := norm_pos_iff.mpr hx
    have hmk : m = k * n := by
      rw [hk]; field_simp; linarith
    have hn2 : n ^ 2 = (E 0 - D 0) ^ 2 + (E 1 - D 1) ^ 2 := by
      rw [hn, norm_sq_coord]; simp
    have hm2 : m ^ 2 = (F 0 - D 0) ^ 2 + (F 1 - D 1) ^ 2 := by
      rw [hm, norm_sq_coord]; simp
    rw [inner_coord] at hcos
    simp only [PiLp.sub_apply] at hcos
    set x0 := E 0 - D 0
    set x1 := E 1 - D 1
    set y0 := F 0 - D 0
    set y1 := F 1 - D 1
    have hcr : (x0 * y1 - x1 * y0) ^ 2 = (n * m * sin δ) ^ 2 := by
      linear_combination (-n ^ 2) * hm2 - (y0 ^ 2 + y1 ^ 2) * hn2 -
        (x0 * y0 + x1 * y1 + cos δ * (n * m)) * hcos - (n * m) ^ 2 * pyδ
    have hn2' : n ^ 2 ≠ 0 := pow_ne_zero 2 hn0.ne'
    have fin : ∀ σ : ℝ, x0 * y1 - x1 * y0 = σ * (n * m * sin δ) →
        Rel k (cos δ) (sin δ) σ D E F := by
      intro σ hσ'
      constructor
      · apply mul_right_cancel₀ hn2'
        linear_combination y0 * hn2 + x0 * hcos - x1 * hσ' +
          n * (cos δ * x0 - σ * sin δ * x1) * hmk
      · apply mul_right_cancel₀ hn2'
        linear_combination y1 * hn2 + x1 * hcos + x0 * hσ' +
          n * (cos δ * x1 + σ * sin δ * x0) * hmk
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hcr with h | h
    · exact ⟨1, Or.inl rfl, fin 1 (by rw [h]; ring)⟩
    · exact ⟨-1, Or.inr rfl, fin (-1) (by rw [h]; ring)⟩
  · rintro ⟨hED, σ, hσ, h0, h1⟩
    have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hx : E - D ≠ 0 := sub_ne_zero.mpr hED
    set n := ‖E - D‖ with hn
    have hn0 : 0 < n := norm_pos_iff.mpr hx
    have hn2 : n ^ 2 = (E 0 - D 0) ^ 2 + (E 1 - D 1) ^ 2 := by
      rw [hn, norm_sq_coord]; simp
    set x0 := E 0 - D 0
    set x1 := E 1 - D 1
    have hFD : ‖F - D‖ = k * n := by
      rw [← pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero, norm_sq_coord]
      simp only [PiLp.sub_apply]
      rw [h0, h1]
      linear_combination (k ^ 2 * (x0 ^ 2 + x1 ^ 2)) * pyδ +
        (k ^ 2 * (x0 ^ 2 + x1 ^ 2) * sin δ ^ 2) * hσ2 - k ^ 2 * hn2
    have hy : F - D ≠ 0 := by
      rw [← norm_pos_iff, hFD]; positivity
    -- the angle at `D`
    have hD : ∠ E D F = δ := by
      rw [EuclideanGeometry.angle]
      simp only [vsub_eq_sub]
      apply angle_of_cos hδ.le hδπ.le hx hy
      rw [hFD, inner_coord]
      simp only [PiLp.sub_apply]
      rw [h0, h1]
      linear_combination (-(k * cos δ)) * hn2
    -- the angle at `E`
    set g := sin δ / sin φ with hg
    have hg2 : sin δ ^ 2 = sin ε ^ 2 - 2 * sin ε * cos δ * sin φ + sin φ ^ 2 := by
      rw [hφsum]; linear_combination (sin ε) ^ 2 * pyδ - (sin δ) ^ 2 * pyε
    have hgk : g ^ 2 = k ^ 2 - 2 * k * cos δ + 1 := by
      rw [hg, hk, div_pow, hg2]; field_simp
    have hgc : 1 - k * cos δ = cos ε * g := by
      rw [hg, hk]; field_simp; rw [hφsum]; ring
    have e0 : F 0 - E 0 = k * (cos δ * x0 - σ * sin δ * x1) - x0 := by rw [← h0]; ring
    have e1 : F 1 - E 1 = k * (cos δ * x1 + σ * sin δ * x0) - x1 := by rw [← h1]; ring
    have hDE : ‖D - E‖ = n := by rw [← neg_sub, norm_neg]
    have hg0 : 0 < g := div_pos sδ sφ
    have hFE : ‖F - E‖ = g * n := by
      rw [← pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero, norm_sq_coord]
      simp only [PiLp.sub_apply]
      rw [e0, e1]
      linear_combination (k ^ 2 * (x0 ^ 2 + x1 ^ 2)) * pyδ +
        (k ^ 2 * (x0 ^ 2 + x1 ^ 2) * sin δ ^ 2) * hσ2 - (k ^ 2 - 2 * k * cos δ + 1) * hn2 -
        n ^ 2 * hgk
    have hE : ∠ D E F = ε := by
      rw [EuclideanGeometry.angle]
      simp only [vsub_eq_sub]
      apply angle_of_cos hε.le hεπ.le (by rw [← neg_sub]; exact neg_ne_zero.mpr hx)
        (by rw [← norm_pos_iff, hFE]; exact mul_pos hg0 hn0)
      rw [hDE, hFE, inner_coord]
      simp only [PiLp.sub_apply]
      rw [e0, e1, show D 0 - E 0 = -x0 by ring, show D 1 - E 1 = -x1 by ring]
      linear_combination (-(1 - k * cos δ)) * hn2 + n ^ 2 * hgc
    refine ⟨hD, hE, ?_⟩
    have hsum' := EuclideanGeometry.angle_add_angle_add_angle_eq_pi F hED
    rw [EuclideanGeometry.angle_comm E F D, EuclideanGeometry.angle_comm F D E, hD, hE] at hsum'
    linarith

/-- Two linear equations in `s, t` with nonzero determinant have exactly the Cramer solution. -/
private lemma cramer {w0 w1 m0 m1 g0 g1 s t : ℝ} (hΔ : m0 * w1 - m1 * w0 ≠ 0) :
    (t * w0 - s * m0 = g0 ∧ t * w1 - s * m1 = g1) ↔
      (s = (w0 * g1 - w1 * g0) / (m0 * w1 - m1 * w0) ∧
        t = (m0 * g1 - m1 * g0) / (m0 * w1 - m1 * w0)) := by
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · rw [eq_div_iff hΔ]; linear_combination w0 * h1 - w1 * h0
    · rw [eq_div_iff hΔ]; linear_combination m0 * h1 - m1 * h0
  · rintro ⟨rfl, rfl⟩
    constructor <;> field_simp <;> ring

/-- For one orientation `σ`, there is exactly one pair `E ∈ CA`, `F ∈ AB` (as lines) with `DF`
the image of `DE` under the turn-and-scale, provided the determinant does not vanish. -/
private lemma solve (A B C D : Plane) (k cd sd σ : ℝ)
    (hΔ : (k * (cd * (A 0 - C 0) - σ * sd * (A 1 - C 1))) * (B 1 - A 1) -
      (k * (cd * (A 1 - C 1) + σ * sd * (A 0 - C 0))) * (B 0 - A 0) ≠ 0) :
    ∃ p : Plane × Plane, p.1 ∈ line[ℝ, C, A] ∧ p.2 ∈ line[ℝ, A, B] ∧ Rel k cd sd σ D p.1 p.2 ∧
      ∀ q : Plane × Plane, q.1 ∈ line[ℝ, C, A] → q.2 ∈ line[ℝ, A, B] →
        Rel k cd sd σ D q.1 q.2 → q = p := by
  set w0 := B 0 - A 0
  set w1 := B 1 - A 1
  set m0 := k * (cd * (A 0 - C 0) - σ * sd * (A 1 - C 1))
  set m1 := k * (cd * (A 1 - C 1) + σ * sd * (A 0 - C 0))
  set g0 := k * (cd * (C 0 - D 0) - σ * sd * (C 1 - D 1)) - (A 0 - D 0)
  set g1 := k * (cd * (C 1 - D 1) + σ * sd * (C 0 - D 0)) - (A 1 - D 1)
  -- `Rel` for points `C + s·CA`, `A + t·AB` is a linear system in `s, t`
  have hsys : ∀ (E F : Plane) (s t : ℝ), E 0 = C 0 + s * (A 0 - C 0) →
      E 1 = C 1 + s * (A 1 - C 1) → F 0 = A 0 + t * (B 0 - A 0) → F 1 = A 1 + t * (B 1 - A 1) →
      (Rel k cd sd σ D E F ↔ (t * w0 - s * m0 = g0 ∧ t * w1 - s * m1 = g1)) := by
    intro E F s t e0 e1 f0 f1
    unfold Rel
    rw [e0, e1, f0, f1]
    constructor
    · rintro ⟨h0, h1⟩
      constructor
      · linear_combination h0
      · linear_combination h1
    · rintro ⟨h0, h1⟩
      constructor
      · linear_combination h0
      · linear_combination h1
  set s := (w0 * g1 - w1 * g0) / (m0 * w1 - m1 * w0) with hsdef
  set t := (m0 * g1 - m1 * g0) / (m0 * w1 - m1 * w0) with htdef
  refine ⟨(C + s • (A - C), A + t • (B - A)), line_mem _ _ _, line_mem _ _ _, ?_, ?_⟩
  · rw [hsys _ _ s t (by simp) (by simp) (by simp) (by simp)]
    exact (cramer hΔ).mpr ⟨rfl, rfl⟩
  · rintro ⟨E, F⟩ hE hF hR
    obtain ⟨s', e0, e1⟩ := line_param hE
    obtain ⟨t', f0, f1⟩ := line_param hF
    rw [hsys E F s' t' e0 e1 f0 f1, cramer hΔ] at hR
    obtain ⟨rfl, rfl⟩ := hR
    simp only at e0 e1 f0 f1
    refine Prod.ext (plane_ext ?_ ?_) (plane_ext ?_ ?_) <;>
      (simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, e0, e1, f0, f1,
        hsdef, htdef])

/-- **Problem 46.** Let `ABC` be a triangle whose base `BC` is divided at the point `D`, and let
`δ, ε, φ` be positive angles with sum `π`. Unless `δ` equals the angle `A` or its supplement,
there are exactly two triangles `DEF` with `E` on the side `CA` and `F` on the side `AB` (taken as
lines) whose angles at `D, E, F` are `δ, ε, φ` (one of each orientation). -/
theorem problem46 (A B C D : Plane) (hABC : cross A B C ≠ 0) (hD : Sbtw ℝ B D C)
    (δ ε φ : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hφ : 0 < φ) (hsum : δ + ε + φ = π)
    (hA1 : δ ≠ ∠ B A C) (hA2 : δ + ∠ B A C ≠ π) :
    ∃ p q : Plane × Plane, p ≠ q ∧
      {x : Plane × Plane | x.1 ∈ line[ℝ, C, A] ∧ x.2 ∈ line[ℝ, A, B] ∧
        HasAngles D x.1 x.2 δ ε φ} = {p, q} := by
  have hδπ : δ < π := by linarith
  have sδ := sin_pos_of_pos_of_lt_pi hδ hδπ
  have sε := sin_pos_of_pos_of_lt_pi hε (by linarith)
  have sφ := sin_pos_of_pos_of_lt_pi hφ (by linarith)
  set k := sin ε / sin φ with hk
  have hk0 : 0 < k := div_pos sε sφ
  set α := ∠ B A C with hα
  have hα0 : 0 ≤ α := EuclideanGeometry.angle_nonneg _ _ _
  have hαπ : α ≤ π := EuclideanGeometry.angle_le_pi _ _ _
  have hAB : B - A ≠ 0 := by
    intro h; apply hABC; rw [sub_eq_zero] at h; rw [h]; simp [cross]
  have hAC : C - A ≠ 0 := by
    intro h; apply hABC; rw [sub_eq_zero] at h; rw [h]; simp [cross]
  set b := ‖C - A‖ with hb
  set c := ‖B - A‖ with hc
  have hb0 : 0 < b := norm_pos_iff.mpr hAC
  have hc0 : 0 < c := norm_pos_iff.mpr hAB
  have hb2 : b ^ 2 = (C 0 - A 0) ^ 2 + (C 1 - A 1) ^ 2 := by rw [hb, norm_sq_coord]; simp
  have hc2 : c ^ 2 = (B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2 := by rw [hc, norm_sq_coord]; simp
  have hcosα : (B 0 - A 0) * (C 0 - A 0) + (B 1 - A 1) * (C 1 - A 1) = cos α * (c * b) := by
    have h := InnerProductGeometry.cos_angle (B - A) (C - A)
    rw [inner_coord] at h
    simp only [PiLp.sub_apply] at h
    rw [hα, EuclideanGeometry.angle]
    simp only [vsub_eq_sub]
    rw [h, ← hb, ← hc]
    field_simp
  have pyδ := sin_sq_add_cos_sq δ
  have hprod : ((k * (cos δ * (A 0 - C 0) - 1 * sin δ * (A 1 - C 1))) * (B 1 - A 1) -
      (k * (cos δ * (A 1 - C 1) + 1 * sin δ * (A 0 - C 0))) * (B 0 - A 0)) *
      ((k * (cos δ * (A 0 - C 0) - (-1) * sin δ * (A 1 - C 1))) * (B 1 - A 1) -
      (k * (cos δ * (A 1 - C 1) + (-1) * sin δ * (A 0 - C 0))) * (B 0 - A 0)) =
      k ^ 2 * (b ^ 2 * c ^ 2) * ((cos δ - cos α) * (cos δ + cos α)) := by
    linear_combination (k ^ 2 * cos δ ^ 2) *
        (-((B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2) * hb2 - b ^ 2 * hc2) -
      (k ^ 2 * ((A 0 - C 0) * (B 0 - A 0) + (A 1 - C 1) * (B 1 - A 1)) ^ 2) * pyδ -
      (k ^ 2 * ((B 0 - A 0) * (C 0 - A 0) + (B 1 - A 1) * (C 1 - A 1) + cos α * (c * b))) *
        hcosα
  have hcd1 : cos δ - cos α ≠ 0 := by
    intro h; apply hA1
    exact injOn_cos ⟨hδ.le, hδπ.le⟩ ⟨hα0, hαπ⟩ (by linarith)
  have hcd2 : cos δ + cos α ≠ 0 := by
    intro h; apply hA2
    have := injOn_cos ⟨hδ.le, hδπ.le⟩ ⟨by linarith, by linarith⟩
      (show cos δ = cos (π - α) by rw [cos_pi_sub]; linarith)
    linarith
  have hne : _ := hprod ▸ mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hk0.ne')
    (mul_ne_zero (pow_ne_zero 2 hb0.ne') (pow_ne_zero 2 hc0.ne')))
    (mul_ne_zero hcd1 hcd2)
  obtain ⟨p, hp1, hp2, hpR, hpU⟩ :=
    solve A B C D k (cos δ) (sin δ) 1 (left_ne_zero_of_mul hne)
  obtain ⟨q, hq1, hq2, hqR, hqU⟩ :=
    solve A B C D k (cos δ) (sin δ) (-1) (right_ne_zero_of_mul hne)
  -- `D` is not on the line `CA`
  have hDCA : ∀ E ∈ line[ℝ, C, A], E ≠ D := by
    intro E hE hED
    obtain ⟨s, e0, e1⟩ := line_param hE
    rw [hED] at e0 e1
    obtain ⟨⟨μ, -, hμ⟩, -, hDC⟩ := hD
    have d0 : D 0 = B 0 + μ * (C 0 - B 0) := by
      rw [← hμ, AffineMap.lineMap_apply_module']; simp; ring
    have d1 : D 1 = B 1 + μ * (C 1 - B 1) := by
      rw [← hμ, AffineMap.lineMap_apply_module']; simp; ring
    have hμ1 : μ ≠ 1 := by
      rintro rfl; apply hDC; rw [← hμ]; simp
    have h0 : (1 - μ) * cross A B C = 0 := by
      simp only [cross]
      linear_combination (-(A 1 - C 1)) * e0 + (A 1 - C 1) * d0 + (A 0 - C 0) * e1 -
        (A 0 - C 0) * d1
    rcases mul_eq_zero.mp h0 with h | h
    · exact hμ1 (by linarith)
    · exact hABC h
  refine ⟨p, q, ?_, ?_⟩
  · intro hpq
    rw [← hpq] at hqR
    obtain ⟨a0, a1⟩ := hpR
    obtain ⟨b0, b1⟩ := hqR
    have hks : 2 * k * sin δ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hk0.ne') sδ.ne'
    apply hDCA p.1 hp1
    apply plane_ext
    · have : 2 * k * sin δ * (p.1 0 - D 0) = 0 := by linear_combination b1 - a1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hks
      · linarith
    · have : 2 * k * sin δ * (p.1 1 - D 1) = 0 := by linear_combination a0 - b0
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hks
      · linarith
  · ext ⟨E, F⟩
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hE, hF, hA⟩
      obtain ⟨-, σ, hσ, hR⟩ := (char hδ hε hφ hsum).mp hA
      rcases hσ with rfl | rfl
      · left; exact hpU (E, F) hE hF hR
      · right; exact hqU (E, F) hE hF hR
    · rintro (rfl | rfl)
      · exact ⟨hp1, hp2, (char hδ hε hφ hsum).mpr ⟨hDCA _ hp1, 1, Or.inl rfl, hpR⟩⟩
      · exact ⟨hq1, hq2, (char hδ hε hφ hsum).mpr ⟨hDCA _ hq1, -1, Or.inr rfl, hqR⟩⟩

/-- The hypotheses of `problem46` can be met: the right isosceles triangle `A = (0, 0)`,
`B = (1, 0)`, `C = (0, 1)` (so `∠A = π/2`), `D` the midpoint of `BC`, and the angles
`π/3, π/3, π/3`. -/
theorem problem46_nonvacuous :
    ∃ (A B C D : Plane) (δ ε φ : ℝ), cross A B C ≠ 0 ∧ Sbtw ℝ B D C ∧ 0 < δ ∧ 0 < ε ∧ 0 < φ ∧
      δ + ε + φ = π ∧ δ ≠ ∠ B A C ∧ δ + ∠ B A C ≠ π := by
  have hA : ∠ (pt 1 0) (pt 0 0) (pt 0 1) = π / 2 := by
    rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    simp [inner_coord]
  have hBC : pt 1 0 ≠ pt 0 1 := by
    intro h
    have := congrArg (fun P : Plane => P 0) h
    simp at this
  refine ⟨pt 0 0, pt 1 0, pt 0 1, midpoint ℝ (pt 1 0) (pt 0 1), π / 3, π / 3, π / 3,
    by simp [cross], sbtw_midpoint_of_ne ℝ hBC, by positivity, by positivity, by positivity,
    by ring, ?_, ?_⟩
  · rw [hA]; intro h; linarith [pi_pos]
  · rw [hA]; intro h; linarith [pi_pos]

end PillowProblems.P46
