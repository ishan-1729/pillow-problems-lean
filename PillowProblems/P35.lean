import PillowProblems.Basic

/-!
# Problem 35 (Pure Geometry, Plane)

**Question.** *(dated 11/76)*

> With a given Triangle, to describe a Circle, cutting each side in two points, such that, if radii be drawn perpendicular to the sides, they are divided by the sides in given ratios.

*(Carroll's solution: Chapter III, problem 35; text in `data/problems.json`.)*

**Lean reading.** The triangle is `A B C` with `cross A B C ≠ 0`; the given ratios `k, l, m` belong to the
sides `BC, CA, AB` and are proper fractions (`0 < k, l, m < 1`, Carroll's N.B.). As in Carroll's
solution, the ratio of a side is (part of the perpendicular radius outside the triangle) : (radius):
the radius `OK ⊥ XY` meets the side line at `M`, `M` lies between `O` and `K`, and `MK = k·r`
(`RadiusDivided`). The centre is required to lie strictly inside the triangle (positive barycentric
coordinates, `Inside`), which is what puts the parts `MK` outside the triangle. "Cutting each side in
two points" is read for the side lines (`CutsTwice`): for the closed sides the problem can be
impossible (for `k` small and `l, m` near `1` the centre is near `A` and the circle meets line `AB`
beyond `A`), and Carroll's construction never checks it. The theorem gives all solutions: the circle
works iff its centre is the point whose distances from the sides are as `1-k : 1-l : 1-m` (written
with barycentric weights `a(1-k), b(1-l), c(1-m)`, `a, b, c` the sides) and
`r = 2·area / (a(1-k) + b(1-l) + c(1-m))`. So the circle exists and is unique.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P35

open scoped EuclideanGeometry RealInnerProductSpace

/-- `O` lies strictly inside the triangle `ABC` (all three barycentric coordinates positive). -/
def Inside (O A B C : Plane) : Prop :=
  ∃ u v w : ℝ, 0 < u ∧ 0 < v ∧ 0 < w ∧ u + v + w = 1 ∧ O = u • A + v • B + w • C

/-- The circle with centre `O` and radius `r` cuts the side `XY` (as a line) in two points. -/
def CutsTwice (O : Plane) (r : ℝ) (X Y : Plane) : Prop :=
  ∃ P Q : Plane, P ≠ Q ∧ P ∈ line[ℝ, X, Y] ∧ Q ∈ line[ℝ, X, Y] ∧ dist O P = r ∧ dist O Q = r

/-- The radius `OK` of the circle (centre `O`, radius `r`) drawn at right angles to the side `XY`
is divided by that side, at `M`, so that the part `MK` beyond the side is to the radius as
`k : 1`. -/
def RadiusDivided (O : Plane) (r : ℝ) (X Y : Plane) (k : ℝ) : Prop :=
  ∃ K M : Plane, dist O K = r ∧ ⟪K - O, Y - X⟫ = 0 ∧ M ∈ line[ℝ, X, Y] ∧ Wbtw ℝ O M K ∧
    dist M K = k * r

/-- The circle (centre `O`, radius `r`) solves the problem for the triangle `ABC` and the ratios
`k, l, m` belonging to the sides `BC, CA, AB`. -/
def Solves (A B C : Plane) (k l m : ℝ) (O : Plane) (r : ℝ) : Prop :=
  Inside O A B C ∧ 0 < r ∧
  CutsTwice O r B C ∧ CutsTwice O r C A ∧ CutsTwice O r A B ∧
  RadiusDivided O r B C k ∧ RadiusDivided O r C A l ∧ RadiusDivided O r A B m

private lemma inner_coord (P Q : Plane) : ⟪P, Q⟫ = P 0 * Q 0 + P 1 * Q 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

private lemma dist_sq_coord (P Q : Plane) : dist P Q ^ 2 = (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma mem_line (X Y : Plane) (t : ℝ) : X + t • (Y - X) ∈ line[ℝ, X, Y] := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  exact ⟨t, by rw [AffineMap.lineMap_apply_module']; abel⟩

/-- For `M` the foot of the perpendicular from `O` to the line `XY`, `|cross X Y O| = XY · OM`. -/
private lemma abs_cross_eq {X Y O M : Plane} (hM : M ∈ line[ℝ, X, Y]) (hperp : ⟪O - M, Y - X⟫ = 0) :
    |cross X Y O| = dist X Y * dist O M := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hM
  obtain ⟨τ, rfl⟩ := hM
  rw [AffineMap.lineMap_apply_module'] at hperp ⊢
  rw [inner_coord] at hperp
  simp at hperp
  have hsq : cross X Y O ^ 2 = (dist X Y * dist O (τ • (Y - X) + X)) ^ 2 := by
    rw [mul_pow, dist_sq_coord, dist_sq_coord]
    simp only [cross, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    linear_combination (-(O 0 - (τ * (Y 0 - X 0) + X 0)) * (Y 0 - X 0) -
      (O 1 - (τ * (Y 1 - X 1) + X 1)) * (Y 1 - X 1)) * hperp
  rw [← Real.sqrt_sq_eq_abs, hsq, Real.sqrt_sq (by positivity)]

private lemma cross_inside {O A B C : Plane} {u v w : ℝ} (h : u + v + w = 1)
    (hO : O = u • A + v • B + w • C) :
    cross B C O = u * cross A B C ∧ cross C A O = v * cross A B C ∧
      cross A B O = w * cross A B C := by
  obtain rfl : w = 1 - u - v := by linarith
  subst hO
  refine ⟨?_, ?_, ?_⟩ <;> simp only [cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> ring


/-- One side: what a divided perpendicular radius says about the distance of the centre from it. -/
private lemma side_dist {O X Y : Plane} {r k : ℝ} (h : RadiusDivided O r X Y k) :
    |cross X Y O| = dist X Y * ((1 - k) * r) := by
  obtain ⟨K, M, hOK, hperp, hM, hbtw, hMK⟩ := h
  have hsum := hbtw.dist_add_dist
  obtain ⟨t, -, hMt⟩ := hbtw
  have hOM : ⟪O - M, Y - X⟫ = 0 := by
    rw [← hMt, AffineMap.lineMap_apply_module']
    have : O - (t • (K - O) + O) = (-t) • (K - O) := by module
    rw [this, inner_smul_left, hperp, mul_zero]
  rw [abs_cross_eq hM hOM]
  congr 1
  linarith

/-- One side: a centre at the right distance from the side gives a divided radius, and the
circle cuts the side twice. -/
private lemma side_ok {O X Y : Plane} {r k : ℝ} (hr : 0 < r) (hk0 : 0 < k) (hk1 : k < 1)
    (hXY : 0 < dist X Y) (hd : |cross X Y O| = dist X Y * ((1 - k) * r)) :
    RadiusDivided O r X Y k ∧ CutsTwice O r X Y := by
  have hw : Y - X ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h, dist_self] at hXY; exact lt_irrefl _ hXY
  have hnw : ‖Y - X‖ = dist X Y := by rw [dist_comm, dist_eq_norm]
  have h1k : (1 - k) ≠ 0 := by linarith
  set a := dist X Y with ha
  set τ := ⟪O - X, Y - X⟫ / a ^ 2 with hτ
  set M := X + τ • (Y - X) with hM
  have hMl : M ∈ line[ℝ, X, Y] := mem_line X Y τ
  have hperp : ⟪O - M, Y - X⟫ = 0 := by
    have : O - M = (O - X) - τ • (Y - X) := by rw [hM]; abel
    rw [this, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hnw, hτ]
    simp only [RCLike.conj_to_real]
    field_simp
    ring
  have hOM : dist O M = (1 - k) * r := by
    have := abs_cross_eq hMl hperp
    rw [hd] at this
    exact (mul_left_cancel₀ hXY.ne' this).symm
  have hnMO : ‖M - O‖ = (1 - k) * r := by rw [← dist_eq_norm, dist_comm, hOM]
  set K := O + (1 - k)⁻¹ • (M - O) with hK
  have hKO : K - O = (1 - k)⁻¹ • (M - O) := by rw [hK]; abel
  have hperp' : ⟪M - O, Y - X⟫ = 0 := by rw [← neg_sub, inner_neg_left, hperp, neg_zero]
  refine ⟨⟨K, M, ?_, ?_, hMl, ?_, ?_⟩, ?_⟩
  · rw [dist_comm, dist_eq_norm, hKO, norm_smul, hnMO, Real.norm_eq_abs, abs_inv,
      abs_of_pos (by linarith : 0 < 1 - k)]
    field_simp
  · rw [hKO, inner_smul_left, hperp', mul_zero]
  · refine ⟨1 - k, ⟨by linarith, by linarith⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module', hKO, smul_smul, mul_inv_cancel₀ h1k, one_smul,
      sub_add_cancel]
  · have e : K - M = (k / (1 - k)) • (M - O) := by
      have e' : (1 - k)⁻¹ - 1 = k / (1 - k) := by field_simp; ring
      rw [← e', hK]; module
    rw [dist_comm, dist_eq_norm, e, norm_smul, hnMO, Real.norm_eq_abs,
      abs_of_pos (div_pos hk0 (by linarith))]
    field_simp
  · have hpos : 0 < r ^ 2 - ((1 - k) * r) ^ 2 := by
      have e : r ^ 2 - ((1 - k) * r) ^ 2 = r * r * (k * (2 - k)) := by ring
      rw [e]; have : 0 < 2 - k := by linarith
      positivity
    set δ := Real.sqrt (r ^ 2 - ((1 - k) * r) ^ 2) / a with hδ
    have hδpos : 0 < δ := div_pos (Real.sqrt_pos.mpr hpos) hXY
    have hne : ‖δ • (Y - X)‖ ^ 2 = r ^ 2 - ((1 - k) * r) ^ 2 := by
      rw [norm_smul, hnw, Real.norm_of_nonneg hδpos.le, hδ, mul_pow, div_pow,
        Real.sq_sqrt hpos.le]
      field_simp
    have hin : ⟪M - O, δ • (Y - X)⟫ = 0 := by
      rw [inner_smul_right, hperp', mul_zero]
    refine ⟨M + δ • (Y - X), M - δ • (Y - X), ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      have h2 : (2 * δ) • (Y - X) = 0 := by
        have : (2 * δ) • (Y - X) = (M + δ • (Y - X)) - (M - δ • (Y - X)) := by module
        rw [this, h, sub_self]
      rcases smul_eq_zero.mp h2 with h3 | h3
      · linarith
      · exact hw h3
    · rw [show M + δ • (Y - X) = X + (τ + δ) • (Y - X) by rw [hM]; module]
      exact mem_line X Y _
    · rw [show M - δ • (Y - X) = X + (τ - δ) • (Y - X) by rw [hM]; module]
      exact mem_line X Y _
    · rw [← pow_left_inj₀ dist_nonneg hr.le two_ne_zero, dist_comm, dist_eq_norm,
        show M + δ • (Y - X) - O = (M - O) + δ • (Y - X) by abel, norm_add_sq_real, hin, hne,
        hnMO]
      ring
    · rw [← pow_left_inj₀ dist_nonneg hr.le two_ne_zero, dist_comm, dist_eq_norm,
        show M - δ • (Y - X) - O = (M - O) - δ • (Y - X) by abel, norm_sub_sq_real, hin, hne,
        hnMO]
      ring

private lemma dist_pos_of_cross {A B C : Plane} (h : cross A B C ≠ 0) :
    0 < dist B C ∧ 0 < dist C A ∧ 0 < dist A B := by
  refine ⟨dist_pos.mpr ?_, dist_pos.mpr ?_, dist_pos.mpr ?_⟩ <;> rintro rfl <;> apply h <;>
    simp [cross]

/-- **Problem 35.** For a triangle `ABC` and proper fractions `k, l, m` belonging to the sides
`BC, CA, AB`: a circle with centre `O` inside the triangle and radius `r` cuts each side in two
points and has its radii perpendicular to the sides divided by the sides so that the parts outside
the triangle are `k, l, m` times the radius, if and only if `O` is the point whose distances from
the sides are as `1 - k : 1 - l : 1 - m` (explicitly, the weighted centre below, `a, b, c` being
the sides) and `r = 2·area / (a(1-k) + b(1-l) + c(1-m))`. So there is exactly one such circle. -/
theorem problem35 (A B C : Plane) (hABC : cross A B C ≠ 0) (k l m : ℝ)
    (hk : 0 < k ∧ k < 1) (hl : 0 < l ∧ l < 1) (hm : 0 < m ∧ m < 1) (O : Plane) (r : ℝ) :
    Solves A B C k l m O r ↔
      O = (dist B C * (1 - k) + dist C A * (1 - l) + dist A B * (1 - m))⁻¹ •
          ((dist B C * (1 - k)) • A + (dist C A * (1 - l)) • B + (dist A B * (1 - m)) • C) ∧
      r = 2 * triArea A B C / (dist B C * (1 - k) + dist C A * (1 - l) + dist A B * (1 - m)) := by
  obtain ⟨ha, hb, hc⟩ := dist_pos_of_cross hABC
  obtain ⟨hk0, hk1⟩ := hk
  obtain ⟨hl0, hl1⟩ := hl
  obtain ⟨hm0, hm1⟩ := hm
  have hS : 0 < |cross A B C| := abs_pos.mpr hABC
  have hT : 2 * triArea A B C = |cross A B C| := by simp only [triArea]; ring
  have ha' := mul_pos ha (by linarith : 0 < 1 - k)
  have hb' := mul_pos hb (by linarith : 0 < 1 - l)
  have hc' := mul_pos hc (by linarith : 0 < 1 - m)
  set a := dist B C
  set b := dist C A
  set c := dist A B
  set S := cross A B C
  set T := a * (1 - k) + b * (1 - l) + c * (1 - m) with hTdef
  have hTpos : 0 < T := by linarith
  have hT0 : T ≠ 0 := hTpos.ne'
  rw [hT]
  constructor
  · rintro ⟨⟨u, v, w, hu, hv, hw, huvw, hO⟩, hr, -, -, -, hBC, hCA, hAB⟩
    obtain ⟨e1, e2, e3⟩ := cross_inside huvw hO
    have d1 := side_dist hBC
    have d2 := side_dist hCA
    have d3 := side_dist hAB
    rw [e1, abs_mul, abs_of_pos hu] at d1
    rw [e2, abs_mul, abs_of_pos hv] at d2
    rw [e3, abs_mul, abs_of_pos hw] at d3
    change u * |S| = a * ((1 - k) * r) at d1
    change v * |S| = b * ((1 - l) * r) at d2
    change w * |S| = c * ((1 - m) * r) at d3
    have hrS : r * T = |S| := by
      have : (u + v + w) * |S| = |S| := by rw [huvw, one_mul]
      rw [hTdef]; linear_combination this - d1 - d2 - d3
    have hr' : r = |S| / T := by
      field_simp; linarith
    refine ⟨?_, hr'⟩
    have hu' : u = T⁻¹ * (a * (1 - k)) := by
      field_simp
      have : u * (r * T) = r * (a * (1 - k)) := by rw [hrS]; linarith
      exact mul_left_cancel₀ hr.ne' (by linarith)
    have hv' : v = T⁻¹ * (b * (1 - l)) := by
      field_simp
      have : v * (r * T) = r * (b * (1 - l)) := by rw [hrS]; linarith
      exact mul_left_cancel₀ hr.ne' (by linarith)
    have hw' : w = T⁻¹ * (c * (1 - m)) := by
      field_simp
      have : w * (r * T) = r * (c * (1 - m)) := by rw [hrS]; linarith
      exact mul_left_cancel₀ hr.ne' (by linarith)
    rw [hO, hu', hv', hw']
    module
  · rintro ⟨hO, hr⟩
    have hrpos : 0 < r := by rw [hr]; exact div_pos hS hTpos
    have hu : 0 < T⁻¹ * (a * (1 - k)) := mul_pos (inv_pos.mpr hTpos) ha'
    have hv : 0 < T⁻¹ * (b * (1 - l)) := mul_pos (inv_pos.mpr hTpos) hb'
    have hw : 0 < T⁻¹ * (c * (1 - m)) := mul_pos (inv_pos.mpr hTpos) hc'
    have hsum : T⁻¹ * (a * (1 - k)) + T⁻¹ * (b * (1 - l)) + T⁻¹ * (c * (1 - m)) = 1 := by
      rw [← mul_add, ← mul_add, inv_mul_cancel₀ hTpos.ne']
    have hO' : O = (T⁻¹ * (a * (1 - k))) • A + (T⁻¹ * (b * (1 - l))) • B +
        (T⁻¹ * (c * (1 - m))) • C := by rw [hO]; module
    obtain ⟨e1, e2, e3⟩ := cross_inside hsum hO'
    have d1 : |cross B C O| = a * ((1 - k) * r) := by
      rw [e1, abs_mul, abs_of_pos hu, hr]; ring
    have d2 : |cross C A O| = b * ((1 - l) * r) := by
      rw [e2, abs_mul, abs_of_pos hv, hr]; ring
    have d3 : |cross A B O| = c * ((1 - m) * r) := by
      rw [e3, abs_mul, abs_of_pos hw, hr]; ring
    obtain ⟨r1, c1⟩ := side_ok hrpos hk0 hk1 ha d1
    obtain ⟨r2, c2⟩ := side_ok hrpos hl0 hl1 hb d2
    obtain ⟨r3, c3⟩ := side_ok hrpos hm0 hm1 hc d3
    exact ⟨⟨_, _, _, hu, hv, hw, hsum, hO'⟩, hrpos, c1, c2, c3, r1, r2, r3⟩

end PillowProblems.P35
