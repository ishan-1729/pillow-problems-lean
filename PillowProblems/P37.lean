import PillowProblems.Basic

/-!
# Problem 37 (Trigonometry: Plane)

**Question.** *(dated 12/91)*

> Two given Circles intersect, so that their common chord subtends angles of 30° and 60° at their centres. What fraction of the smaller Circle is within the larger?

**Answer.**

> \[\dfrac{4 + \sqrt{3}}{12} - \dfrac{1 + \sqrt{3}}{2\pi};\quad \text{i.e.}\,\, \text{about}\,\, \cdot 044\].

*(Carroll's solution: Chapter III, problem 37; text in `data/problems.json`.)*

**Lean reading.** Areas are Lebesgue measure (`volume`) on the plane, and a circle's area is that
of its open disc `Metric.ball` (the boundary has measure zero). The circles have centres `A` and
`D` and meet at `B` and `C`, so their radii are `AB = AC` and `DB = DC` and `BC` is the common
chord; the hypotheses are `∠BAC = 30°` and `∠BDC = 60°`, with no fixed position or size. The
question is ambiguous: the centres may lie on opposite sides of the common chord (Carroll's figure
and solution) or on the same side, and both figures exist. "Opposite sides" is `cross B C A *
cross B C D < 0` (the triangles `BCA` and `BCD` have opposite orientations). For this reading,
`problem37` proves that the circle about `D` is the smaller one and that the fraction of its area
lying inside the other circle is Carroll's `(4 + √3)/12 - (1 + √3)/(2π)`. For the other figure
(`cross B C A * cross B C D > 0`), `problem37_sameSide` proves that the fraction is `1 + √3/12 -
1/(2π)`; `problem37_nonvacuous` shows that both figures exist. The proofs move the figure by a
rigid motion (`frame`, shown to preserve distances, angles and area) so that the chord lies on the
`y`-axis and the centres on the `x`-axis. Each circular segment is then the region between two
graphs, whose area is the integral of `2√(R² - u²)`. Carroll's decimal "about ·044" is slightly
off: he rounded the two terms to `·478` and `·434` (with `π ≈ 22/7`), whose difference is `·044`,
although even with `π = 22/7` the difference is `·0430…`. The true value is `0·0429…`;
`problem37_approx` proves that it lies between `·042` and `·043`.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P37

open scoped EuclideanGeometry
open MeasureTheory Real

/-- Antiderivative of `2 √(R² - u²)`; `segF R u₂ - segF R u₁` is the area of the part of a disc
of radius `R` between two chords at (signed) distances `u₁ ≤ u₂` from the centre. -/
private noncomputable def segF (R u : ℝ) : ℝ :=
  R ^ 2 * arcsin (R⁻¹ * u) + u * √(R ^ 2 - u ^ 2)

private lemma hasDerivAt_segF {R x : ℝ} (hR : 0 < R) (hx1 : -R < x) (hx2 : x < R) :
    HasDerivAt (segF R) (2 * √(R ^ 2 - x ^ 2)) x := by
  have h₁ : 0 < R ^ 2 - x ^ 2 := sub_pos_of_lt (sq_lt_sq' hx1 hx2)
  have hR1 : -1 < R⁻¹ * x := by
    rw [← div_eq_inv_mul, lt_div_iff₀ hR]; linarith
  have hR2 : R⁻¹ * x < 1 := by
    rw [← div_eq_inv_mul, div_lt_iff₀ hR]; linarith
  have d1 : HasDerivAt (fun u => R⁻¹ * u) R⁻¹ x := by
    simpa using (hasDerivAt_id x).const_mul R⁻¹
  have d2 : HasDerivAt (fun u => arcsin (R⁻¹ * u)) (1 / √(1 - (R⁻¹ * x) ^ 2) * R⁻¹) x :=
    (hasDerivAt_arcsin hR1.ne' hR2.ne).comp x d1
  have d3 : HasDerivAt (fun u => R ^ 2 - u ^ 2) (-(2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub (R ^ 2)
  have d4 : HasDerivAt (fun u => √(R ^ 2 - u ^ 2)) (-(2 * x) / (2 * √(R ^ 2 - x ^ 2))) x :=
    d3.sqrt h₁.ne'
  have d5 := (d2.const_mul (R ^ 2)).add ((hasDerivAt_id' x).mul d4)
  refine d5.congr_deriv ?_
  have hs0 : 0 < √(R ^ 2 - x ^ 2) := Real.sqrt_pos.2 h₁
  have hsq : √(R ^ 2 - x ^ 2) ^ 2 = R ^ 2 - x ^ 2 := Real.sq_sqrt h₁.le
  have hs : √(1 - (R⁻¹ * x) ^ 2) = √(R ^ 2 - x ^ 2) / R := by
    rw [show 1 - (R⁻¹ * x) ^ 2 = (R ^ 2 - x ^ 2) / R ^ 2 by field_simp,
      Real.sqrt_div' _ (sq_nonneg R), Real.sqrt_sq hR.le]
  rw [hs]
  set s := √(R ^ 2 - x ^ 2)
  have e1 : R ^ 2 * (1 / (s / R) * R⁻¹) = R ^ 2 / s := by field_simp
  have e2 : x * (-(2 * x) / (2 * s)) = -(x ^ 2 / s) := by field_simp
  rw [e1, e2, show R ^ 2 / s + (1 * s + -(x ^ 2 / s)) = (R ^ 2 - x ^ 2) / s + s by ring, ← hsq,
    pow_two, mul_div_assoc, div_self hs0.ne', mul_one]
  ring

/-- The area of the part of the disc with centre `(c, 0)` and radius `R` lying over `a < x ≤ b`
(with `c - R ≤ a ≤ b ≤ c + R`). -/
private lemma vol_seg {a b c R : ℝ} (hR : 0 < R) (ha : c - R ≤ a) (hab : a ≤ b)
    (hb : b ≤ c + R) :
    volume {z : ℝ × ℝ | z.1 ∈ Set.Ioc a b ∧ (z.1 - c) ^ 2 + z.2 ^ 2 < R ^ 2} =
      ENNReal.ofReal (segF R (b - c) - segF R (a - c)) := by
  set g : ℝ → ℝ := fun x => √(R ^ 2 - (x - c) ^ 2) with hg_def
  have hg : Continuous g := by fun_prop
  have hset : {z : ℝ × ℝ | z.1 ∈ Set.Ioc a b ∧ (z.1 - c) ^ 2 + z.2 ^ 2 < R ^ 2} =
      regionBetween (-g) g (Set.Ioc a b) := by
    ext z
    simp only [regionBetween, Set.mem_ofPred_eq, Set.mem_Ioo, hg_def, Pi.neg_apply]
    constructor
    · rintro ⟨hz, h⟩
      refine ⟨hz, ?_⟩
      have : |z.2| < √(R ^ 2 - (z.1 - c) ^ 2) := by
        apply Real.lt_sqrt_of_sq_lt; rw [sq_abs]; linarith
      exact abs_lt.1 this
    · rintro ⟨hz, h1, h2⟩
      refine ⟨hz, ?_⟩
      have : |z.2| < √(R ^ 2 - (z.1 - c) ^ 2) := abs_lt.2 ⟨h1, h2⟩
      have := (Real.lt_sqrt (abs_nonneg _)).1 this
      rw [sq_abs] at this
      linarith
  have hint : IntegrableOn g (Set.Ioc a b) :=
    hg.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  rw [hset, Measure.volume_eq_prod, volume_regionBetween_eq_integral hint.neg hint
    measurableSet_Ioc (fun x _ => neg_le_self (Real.sqrt_nonneg _))]
  congr 1
  rw [← intervalIntegral.integral_of_le hab]
  have hcongr : g - -g = fun x => 2 * g x := by
    ext x; simp only [Pi.sub_apply, Pi.neg_apply]; ring
  rw [hcongr]
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt (fun x => segF R (x - c)) (2 * g x) x := by
    rintro x ⟨hx1, hx2⟩
    exact HasDerivAt.comp_sub_const x c (hasDerivAt_segF hR (by linarith) (by linarith))
  have hcont : ContinuousOn (fun x => segF R (x - c)) (Set.Icc a b) := by
    unfold segF; fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv
    ((continuous_const.mul hg).intervalIntegrable _ _)

private lemma dist_sq' (X Y : Plane) : dist X Y ^ 2 = (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- The coordinate map of the plane onto `ℝ × ℝ`; it preserves area. -/
private noncomputable def toProd (z : Plane) : ℝ × ℝ := (z 0, z 1)

private lemma toProd_mp : MeasurePreserving toProd volume volume := by
  have := (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  convert this using 1
  funext z
  rfl

private lemma ball_eq (x0 R : ℝ) (hR : 0 < R) :
    Metric.ball (pt x0 0) R = toProd ⁻¹' {z : ℝ × ℝ | (z.1 - x0) ^ 2 + z.2 ^ 2 < R ^ 2} := by
  ext z
  simp only [Metric.mem_ball, Set.mem_preimage, Set.mem_ofPred_eq, toProd]
  rw [EuclideanSpace.dist_eq, Real.sqrt_lt' hR]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma cos_angle_chord (ℓ x : ℝ) :
    Real.cos (∠ (pt 0 ℓ) (pt x 0) (pt 0 (-ℓ))) = (x ^ 2 - ℓ ^ 2) / (x ^ 2 + ℓ ^ 2) := by
  unfold EuclideanGeometry.angle
  rw [InnerProductGeometry.cos_angle]
  simp only [vsub_eq_sub]
  have hn : ∀ v : Plane, ‖v‖ = √(v 0 ^ 2 + v 1 ^ 2) := by
    intro v; rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two]
  rw [hn, hn]
  simp only [PiLp.sub_apply, pt_zero, pt_one, PiLp.inner_apply, Fin.sum_univ_two,
    RCLike.inner_apply, conj_trivial]
  rw [← Real.sqrt_mul (by positivity), show ((0 - x) ^ 2 + (ℓ - 0) ^ 2) * ((0 - x) ^ 2 + (-ℓ - 0) ^ 2)
    = (x ^ 2 + ℓ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  ring

/-- The area computation, once the shape of the figure is known. -/
private lemma lens_fraction (ℓ p q R r : ℝ) (hℓ : 0 < ℓ) (hp' : p = (2 + √3) * ℓ)
    (hq' : q = √3 * ℓ) (hR : 0 < R) (hr : 0 < r) (hR2 : R ^ 2 = p ^ 2 + ℓ ^ 2)
    (hr2 : r ^ 2 = q ^ 2 + ℓ ^ 2) :
    (volume (Metric.ball (pt (-p) 0) R ∩ Metric.ball (pt q 0) r)).toReal /
      (volume (Metric.ball (pt q 0) r)).toReal = (4 + √3) / 12 - (1 + √3) / (2 * π) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < √3 := by positivity
  have hp : 0 < p := by rw [hp']; positivity
  have hq : 0 < q := by rw [hq']; positivity
  have hr' : r = 2 * ℓ := by
    rw [← Real.sqrt_sq hr.le, hr2, hq', show (√3 * ℓ) ^ 2 + ℓ ^ 2 = (2 * ℓ) ^ 2 by
      linear_combination ℓ ^ 2 * h3, Real.sqrt_sq (by positivity)]
  have hpR : p < R := by
    have := abs_lt_of_sq_lt_sq (show p ^ 2 < R ^ 2 by rw [hR2]; linarith [sq_pos_of_pos hℓ])
      hR.le
    linarith [le_abs_self p]
  have hqr : q < r := by
    have := abs_lt_of_sq_lt_sq (show q ^ 2 < r ^ 2 by rw [hr2]; linarith [sq_pos_of_pos hℓ])
      hr.le
    linarith [le_abs_self q]
  -- values of the antiderivative
  have hRp : R⁻¹ * p = cos (π / 12) := by
    have hc : cos (π / 12) ^ 2 = (2 + √3) / 4 := by
      rw [Real.cos_sq, show 2 * (π / 12) = π / 6 by ring, Real.cos_pi_div_six]; ring
    have hcpos : 0 < cos (π / 12) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
    have hl : (R⁻¹ * p) ^ 2 = (2 + √3) / 4 := by
      rw [mul_pow, inv_pow, hR2, hp', ← div_eq_inv_mul, div_eq_iff (by positivity)]
      linear_combination (-(2 + √3) * ℓ ^ 2 / 4) * h3
    rw [← Real.sqrt_sq (by positivity : 0 ≤ R⁻¹ * p), hl, ← hc, Real.sqrt_sq hcpos.le]
  have hrq : r⁻¹ * q = cos (π / 6) := by
    rw [hr', hq', Real.cos_pi_div_six]; field_simp
  have hV1 : segF R (R - p - -p) - segF R (0 - -p) = R ^ 2 * (π / 12) - p * ℓ := by
    rw [show R - p - -p = R by ring, show (0 : ℝ) - -p = p by ring]
    unfold segF
    rw [inv_mul_cancel₀ hR.ne', Real.arcsin_one, sub_self, Real.sqrt_zero, hRp,
      Real.arcsin_eq_pi_div_two_sub_arccos, Real.arccos_cos (by positivity) (by linarith [pi_pos]),
      hR2, show p ^ 2 + ℓ ^ 2 - p ^ 2 = ℓ ^ 2 by ring, Real.sqrt_sq hℓ.le]
    ring
  have hV2 : segF r (0 - q) - segF r (q - r - q) = r ^ 2 * (π / 6) - q * ℓ := by
    rw [show (0 : ℝ) - q = -q by ring, show q - r - q = -r by ring]
    unfold segF
    rw [mul_neg, mul_neg, neg_sq, neg_sq, sub_self, Real.sqrt_zero, inv_mul_cancel₀ hr.ne',
      Real.arcsin_neg, Real.arcsin_neg, Real.arcsin_one, hrq,
      Real.arcsin_eq_pi_div_two_sub_arccos, Real.arccos_cos (by positivity) (by linarith [pi_pos]),
      hr2, show q ^ 2 + ℓ ^ 2 - q ^ 2 = ℓ ^ 2 by ring, Real.sqrt_sq hℓ.le]
    ring
  have hVd : segF r (q + r - q) - segF r (q - r - q) = π * r ^ 2 := by
    rw [show q + r - q = r by ring, show q - r - q = -r by ring]
    unfold segF
    rw [mul_neg, inv_mul_cancel₀ hr.ne', Real.arcsin_neg, Real.arcsin_one, neg_sq, sub_self,
      Real.sqrt_zero]
    ring
  have hV1' : R ^ 2 * (π / 12) - p * ℓ = ℓ ^ 2 * (2 + √3) * (π / 3 - 1) := by
    rw [hR2, hp']; linear_combination (ℓ ^ 2 * π / 12) * h3
  have hV2' : r ^ 2 * (π / 6) - q * ℓ = ℓ ^ 2 * (2 * π / 3 - √3) := by
    rw [hr', hq']; ring
  have hpi := pi_gt_three
  have hs2 : √3 < 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hV1n : 0 ≤ R ^ 2 * (π / 12) - p * ℓ := by
    rw [hV1']; apply mul_nonneg (by positivity); linarith
  have hV2n : 0 ≤ r ^ 2 * (π / 6) - q * ℓ := by
    rw [hV2']; apply mul_nonneg (by positivity); linarith
  -- the regions, in coordinates
  have hmeas : ∀ c ρ : ℝ, MeasurableSet {z : ℝ × ℝ | (z.1 - c) ^ 2 + z.2 ^ 2 < ρ ^ 2} := by
    intro c ρ; exact measurableSet_lt (by fun_prop) measurable_const
  have hS1 : ({z : ℝ × ℝ | (z.1 - -p) ^ 2 + z.2 ^ 2 < R ^ 2} ∩
      {z : ℝ × ℝ | (z.1 - q) ^ 2 + z.2 ^ 2 < r ^ 2}) ∩ {z : ℝ × ℝ | 0 < z.1} =
      {z : ℝ × ℝ | z.1 ∈ Set.Ioc 0 (R - p) ∧ (z.1 - -p) ^ 2 + z.2 ^ 2 < R ^ 2} := by
    ext ⟨x, y⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, _⟩, hx⟩
      refine ⟨⟨hx, ?_⟩, h1⟩
      have := abs_lt_of_sq_lt_sq (by linarith [sq_nonneg y] : (x - -p) ^ 2 < R ^ 2) hR.le
      linarith [(abs_lt.1 this).2]
    · rintro ⟨⟨hx, _⟩, h1⟩
      refine ⟨⟨h1, ?_⟩, hx⟩
      have e : (x - q) ^ 2 + y ^ 2 =
          (x - -p) ^ 2 + y ^ 2 - 2 * (p * x) - 2 * (q * x) + q ^ 2 - p ^ 2 := by ring
      rw [e, hr2]
      linarith [mul_pos hp hx, mul_pos hq hx]
  have hS2 : ({z : ℝ × ℝ | (z.1 - -p) ^ 2 + z.2 ^ 2 < R ^ 2} ∩
      {z : ℝ × ℝ | (z.1 - q) ^ 2 + z.2 ^ 2 < r ^ 2}) \ {z : ℝ × ℝ | 0 < z.1} =
      {z : ℝ × ℝ | z.1 ∈ Set.Ioc (q - r) 0 ∧ (z.1 - q) ^ 2 + z.2 ^ 2 < r ^ 2} := by
    ext ⟨x, y⟩
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc, not_lt]
    constructor
    · rintro ⟨⟨_, h2⟩, hx⟩
      refine ⟨⟨?_, hx⟩, h2⟩
      have := abs_lt_of_sq_lt_sq (by linarith [sq_nonneg y] : (x - q) ^ 2 < r ^ 2) hr.le
      linarith [(abs_lt.1 this).1]
    · rintro ⟨⟨_, hx⟩, h2⟩
      refine ⟨⟨?_, h2⟩, hx⟩
      have e : (x - -p) ^ 2 + y ^ 2 =
          (x - q) ^ 2 + y ^ 2 + 2 * (p * x) + 2 * (q * x) + p ^ 2 - q ^ 2 := by ring
      rw [e, hR2]
      linarith [mul_nonpos_of_nonneg_of_nonpos hp.le hx, mul_nonpos_of_nonneg_of_nonpos hq.le hx]
  have hdisc : {z : ℝ × ℝ | (z.1 - q) ^ 2 + z.2 ^ 2 < r ^ 2} =
      {z : ℝ × ℝ | z.1 ∈ Set.Ioc (q - r) (q + r) ∧ (z.1 - q) ^ 2 + z.2 ^ 2 < r ^ 2} := by
    ext ⟨x, y⟩
    simp only [Set.mem_ofPred_eq, Set.mem_Ioc]
    constructor
    · intro h
      have := abs_lt_of_sq_lt_sq (by linarith [sq_nonneg y] : (x - q) ^ 2 < r ^ 2) hr.le
      exact ⟨⟨by linarith [(abs_lt.1 this).1], by linarith [(abs_lt.1 this).2]⟩, h⟩
    · exact fun h => h.2
  rw [ball_eq (-p) R hR, ball_eq q r hr, ← Set.preimage_inter,
    toProd_mp.measure_preimage ((hmeas _ _).inter (hmeas _ _)).nullMeasurableSet,
    toProd_mp.measure_preimage (hmeas _ _).nullMeasurableSet,
    ← measure_inter_add_sdiff _ (measurableSet_lt measurable_const measurable_fst), hS1, hS2, hdisc,
    vol_seg hR (by linarith) (by linarith) (by linarith),
    vol_seg hr (by linarith) (by linarith) (by linarith),
    vol_seg hr (by linarith) (by linarith) (by linarith), hV1, hV2, hVd,
    ← ENNReal.ofReal_add hV1n hV2n, ENNReal.toReal_ofReal (add_nonneg hV1n hV2n),
    ENNReal.toReal_ofReal (by positivity)]
  have hN : R ^ 2 * (π / 12) - p * ℓ + (r ^ 2 * (π / 6) - q * ℓ) =
      ℓ ^ 2 * (π * (4 + √3) / 3 - 2 * (1 + √3)) := by
    rw [hV1', hV2']; ring
  rw [hN, hr']
  field_simp
  ring

/-- The problem in the standard position: chord `B = (0, ℓ)`, `C = (0, -ℓ)` on the `y`-axis,
centres `A = (-p, 0)`, `D = (q, 0)` on the `x`-axis, on opposite sides of the chord. -/
private theorem std (ℓ p q : ℝ) (hℓ : 0 < ℓ) (hp : 0 < p) (hq : 0 < q)
    (hA : ∠ (pt 0 ℓ) (pt (-p) 0) (pt 0 (-ℓ)) = π / 6)
    (hD : ∠ (pt 0 ℓ) (pt q 0) (pt 0 (-ℓ)) = π / 3) :
    dist (pt q 0) (pt 0 ℓ) < dist (pt (-p) 0) (pt 0 ℓ) ∧
    (volume (Metric.ball (pt (-p) 0) (dist (pt (-p) 0) (pt 0 ℓ)) ∩
        Metric.ball (pt q 0) (dist (pt q 0) (pt 0 ℓ)))).toReal /
      (volume (Metric.ball (pt q 0) (dist (pt q 0) (pt 0 ℓ)))).toReal =
      (4 + √3) / 12 - (1 + √3) / (2 * π) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < √3 := by positivity
  -- the angle conditions fix the shape
  have hcA := cos_angle_chord ℓ (-p)
  rw [hA, Real.cos_pi_div_six, neg_sq, eq_div_iff (by positivity)] at hcA
  have hcD := cos_angle_chord ℓ q
  rw [hD, Real.cos_pi_div_three, eq_div_iff (by positivity)] at hcD
  have hp2 : p ^ 2 = ((2 + √3) * ℓ) ^ 2 := by
    linear_combination (-2) * (2 + √3) * hcA + p ^ 2 * h3
  have hq2 : q ^ 2 = (√3 * ℓ) ^ 2 := by
    linear_combination (-2) * hcD - ℓ ^ 2 * h3
  have hp' : p = (2 + √3) * ℓ := by
    rw [← Real.sqrt_sq hp.le, hp2, Real.sqrt_sq (by positivity)]
  have hq' : q = √3 * ℓ := by
    rw [← Real.sqrt_sq hq.le, hq2, Real.sqrt_sq (by positivity)]
  -- the radii
  have hR2 : dist (pt (-p) 0) (pt 0 ℓ) ^ 2 = p ^ 2 + ℓ ^ 2 := by
    rw [dist_sq']; simp only [pt_zero, pt_one]; ring
  have hr2 : dist (pt q 0) (pt 0 ℓ) ^ 2 = q ^ 2 + ℓ ^ 2 := by
    rw [dist_sq']; simp only [pt_zero, pt_one]; ring
  have hR : 0 < dist (pt (-p) 0) (pt 0 ℓ) := by
    have h := abs_lt_of_sq_lt_sq (show (0 : ℝ) ^ 2 < dist (pt (-p) 0) (pt 0 ℓ) ^ 2 by
      rw [hR2, zero_pow two_ne_zero]; positivity) dist_nonneg
    simpa using h
  have hr : 0 < dist (pt q 0) (pt 0 ℓ) := by
    have h := abs_lt_of_sq_lt_sq (show (0 : ℝ) ^ 2 < dist (pt q 0) (pt 0 ℓ) ^ 2 by
      rw [hr2, zero_pow two_ne_zero]; positivity) dist_nonneg
    simpa using h
  refine ⟨?_, lens_fraction ℓ p q _ _ hℓ hp' hq' hR hr hR2 hr2⟩
  have hqp : q < p := by rw [hp', hq']; linarith
  have := abs_lt_of_sq_lt_sq (show dist (pt q 0) (pt 0 ℓ) ^ 2 < dist (pt (-p) 0) (pt 0 ℓ) ^ 2 by
    rw [hR2, hr2]; linarith [sq_lt_sq' (by linarith) hqp]) hR.le
  linarith [le_abs_self (dist (pt q 0) (pt 0 ℓ))]

/-- The area computation for the other figure, both centres on the same side of the chord. -/
private lemma lens_fraction_same (ℓ p q R r : ℝ) (hℓ : 0 < ℓ) (hp' : p = (2 + √3) * ℓ)
    (hq' : q = √3 * ℓ) (hR : 0 < R) (hr : 0 < r) (hR2 : R ^ 2 = p ^ 2 + ℓ ^ 2)
    (hr2 : r ^ 2 = q ^ 2 + ℓ ^ 2) :
    (volume (Metric.ball (pt (-p) 0) R ∩ Metric.ball (pt (-q) 0) r)).toReal /
      (volume (Metric.ball (pt (-q) 0) r)).toReal = 1 + √3 / 12 - 1 / (2 * π) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < √3 := by positivity
  have hp : 0 < p := by rw [hp']; positivity
  have hq : 0 < q := by rw [hq']; positivity
  have hpq : q < p := by rw [hp', hq']; linarith
  have hr' : r = 2 * ℓ := by
    rw [← Real.sqrt_sq hr.le, hr2, hq', show (√3 * ℓ) ^ 2 + ℓ ^ 2 = (2 * ℓ) ^ 2 by
      linear_combination ℓ ^ 2 * h3, Real.sqrt_sq (by positivity)]
  have hpR : p < R := by
    have := abs_lt_of_sq_lt_sq (show p ^ 2 < R ^ 2 by rw [hR2]; linarith [sq_pos_of_pos hℓ])
      hR.le
    linarith [le_abs_self p]
  have hqr : q < r := by
    have := abs_lt_of_sq_lt_sq (show q ^ 2 < r ^ 2 by rw [hr2]; linarith [sq_pos_of_pos hℓ])
      hr.le
    linarith [le_abs_self q]
  -- values of the antiderivative
  have hRp : R⁻¹ * p = cos (π / 12) := by
    have hc : cos (π / 12) ^ 2 = (2 + √3) / 4 := by
      rw [Real.cos_sq, show 2 * (π / 12) = π / 6 by ring, Real.cos_pi_div_six]; ring
    have hcpos : 0 < cos (π / 12) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
    have hl : (R⁻¹ * p) ^ 2 = (2 + √3) / 4 := by
      rw [mul_pow, inv_pow, hR2, hp', ← div_eq_inv_mul, div_eq_iff (by positivity)]
      linear_combination (-(2 + √3) * ℓ ^ 2 / 4) * h3
    rw [← Real.sqrt_sq (by positivity : 0 ≤ R⁻¹ * p), hl, ← hc, Real.sqrt_sq hcpos.le]
  have hrq : r⁻¹ * q = cos (π / 6) := by
    rw [hr', hq', Real.cos_pi_div_six]; field_simp
  have hV1 : segF R (R - p - -p) - segF R (0 - -p) = R ^ 2 * (π / 12) - p * ℓ := by
    rw [show R - p - -p = R by ring, show (0 : ℝ) - -p = p by ring]
    unfold segF
    rw [inv_mul_cancel₀ hR.ne', Real.arcsin_one, sub_self, Real.sqrt_zero, hRp,
      Real.arcsin_eq_pi_div_two_sub_arccos, Real.arccos_cos (by positivity) (by linarith [pi_pos]),
      hR2, show p ^ 2 + ℓ ^ 2 - p ^ 2 = ℓ ^ 2 by ring, Real.sqrt_sq hℓ.le]
    ring
  have hV2 : segF r (0 - -q) - segF r (-q - r - -q) =
      r ^ 2 * (π / 3) + q * ℓ + r ^ 2 * (π / 2) := by
    rw [show (0 : ℝ) - -q = q by ring, show -q - r - -q = -r by ring]
    unfold segF
    rw [mul_neg, inv_mul_cancel₀ hr.ne', Real.arcsin_neg, Real.arcsin_one, neg_sq, sub_self,
      Real.sqrt_zero, hrq, Real.arcsin_eq_pi_div_two_sub_arccos,
      Real.arccos_cos (by positivity) (by linarith [pi_pos]),
      hr2, show q ^ 2 + ℓ ^ 2 - q ^ 2 = ℓ ^ 2 by ring, Real.sqrt_sq hℓ.le]
    ring
  have hVd : segF r (-q + r - -q) - segF r (-q - r - -q) = π * r ^ 2 := by
    rw [show -q + r - -q = r by ring, show -q - r - -q = -r by ring]
    unfold segF
    rw [mul_neg, inv_mul_cancel₀ hr.ne', Real.arcsin_neg, Real.arcsin_one, neg_sq, sub_self,
      Real.sqrt_zero]
    ring
  have hV1' : R ^ 2 * (π / 12) - p * ℓ = ℓ ^ 2 * (2 + √3) * (π / 3 - 1) := by
    rw [hR2, hp']; linear_combination (ℓ ^ 2 * π / 12) * h3
  have hpi := pi_gt_three
  have hs2 : √3 < 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hV1n : 0 ≤ R ^ 2 * (π / 12) - p * ℓ := by
    rw [hV1']; apply mul_nonneg (by positivity); linarith
  have hV2n : 0 ≤ r ^ 2 * (π / 3) + q * ℓ + r ^ 2 * (π / 2) := by positivity
  -- the regions, in coordinates
  have hmeas : ∀ c ρ : ℝ, MeasurableSet {z : ℝ × ℝ | (z.1 - c) ^ 2 + z.2 ^ 2 < ρ ^ 2} := by
    intro c ρ; exact measurableSet_lt (by fun_prop) measurable_const
  have hS1 : ({z : ℝ × ℝ | (z.1 - -p) ^ 2 + z.2 ^ 2 < R ^ 2} ∩
      {z : ℝ × ℝ | (z.1 - -q) ^ 2 + z.2 ^ 2 < r ^ 2}) ∩ {z : ℝ × ℝ | 0 < z.1} =
      {z : ℝ × ℝ | z.1 ∈ Set.Ioc 0 (R - p) ∧ (z.1 - -p) ^ 2 + z.2 ^ 2 < R ^ 2} := by
    ext ⟨x, y⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, _⟩, hx⟩
      refine ⟨⟨hx, ?_⟩, h1⟩
      have := abs_lt_of_sq_lt_sq (by linarith [sq_nonneg y] : (x - -p) ^ 2 < R ^ 2) hR.le
      linarith [(abs_lt.1 this).2]
    · rintro ⟨⟨hx, _⟩, h1⟩
      refine ⟨⟨h1, ?_⟩, hx⟩
      have e : (x - -q) ^ 2 + y ^ 2 =
          (x - -p) ^ 2 + y ^ 2 - 2 * (p * x) + 2 * (q * x) + q ^ 2 - p ^ 2 := by ring
      have hpx : q * x < p * x := mul_lt_mul_of_pos_right hpq hx
      rw [e, hr2]
      linarith
  have hS2 : ({z : ℝ × ℝ | (z.1 - -p) ^ 2 + z.2 ^ 2 < R ^ 2} ∩
      {z : ℝ × ℝ | (z.1 - -q) ^ 2 + z.2 ^ 2 < r ^ 2}) \ {z : ℝ × ℝ | 0 < z.1} =
      {z : ℝ × ℝ | z.1 ∈ Set.Ioc (-q - r) 0 ∧ (z.1 - -q) ^ 2 + z.2 ^ 2 < r ^ 2} := by
    ext ⟨x, y⟩
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc, not_lt]
    constructor
    · rintro ⟨⟨_, h2⟩, hx⟩
      refine ⟨⟨?_, hx⟩, h2⟩
      have := abs_lt_of_sq_lt_sq (by linarith [sq_nonneg y] : (x - -q) ^ 2 < r ^ 2) hr.le
      linarith [(abs_lt.1 this).1]
    · rintro ⟨⟨_, hx⟩, h2⟩
      refine ⟨⟨?_, h2⟩, hx⟩
      have e : (x - -p) ^ 2 + y ^ 2 =
          (x - -q) ^ 2 + y ^ 2 + 2 * (p * x) - 2 * (q * x) + p ^ 2 - q ^ 2 := by ring
      have hpx : p * x ≤ q * x := mul_le_mul_of_nonpos_right hpq.le hx
      rw [e, hR2]
      linarith
  have hdisc : {z : ℝ × ℝ | (z.1 - -q) ^ 2 + z.2 ^ 2 < r ^ 2} =
      {z : ℝ × ℝ | z.1 ∈ Set.Ioc (-q - r) (-q + r) ∧ (z.1 - -q) ^ 2 + z.2 ^ 2 < r ^ 2} := by
    ext ⟨x, y⟩
    simp only [Set.mem_ofPred_eq, Set.mem_Ioc]
    constructor
    · intro h
      have := abs_lt_of_sq_lt_sq (by linarith [sq_nonneg y] : (x - -q) ^ 2 < r ^ 2) hr.le
      exact ⟨⟨by linarith [(abs_lt.1 this).1], by linarith [(abs_lt.1 this).2]⟩, h⟩
    · exact fun h => h.2
  rw [ball_eq (-p) R hR, ball_eq (-q) r hr, ← Set.preimage_inter,
    toProd_mp.measure_preimage ((hmeas _ _).inter (hmeas _ _)).nullMeasurableSet,
    toProd_mp.measure_preimage (hmeas _ _).nullMeasurableSet,
    ← measure_inter_add_sdiff _ (measurableSet_lt measurable_const measurable_fst), hS1, hS2, hdisc,
    vol_seg hR (by linarith) (by linarith) (by linarith),
    vol_seg hr (by linarith) (by linarith) (by linarith),
    vol_seg hr (by linarith) (by linarith) (by linarith), hV1, hV2, hVd,
    ← ENNReal.ofReal_add hV1n hV2n, ENNReal.toReal_ofReal (add_nonneg hV1n hV2n),
    ENNReal.toReal_ofReal (by positivity)]
  have hN : R ^ 2 * (π / 12) - p * ℓ + (r ^ 2 * (π / 3) + q * ℓ + r ^ 2 * (π / 2)) =
      ℓ ^ 2 * (π * (12 + √3) / 3 - 2) := by
    rw [hV1', hr', hq']; ring
  rw [hN, hr']
  field_simp
  ring

/-- The other figure in the standard position: chord `B = (0, ℓ)`, `C = (0, -ℓ)`, centres
`A = (-p, 0)`, `D = (-q, 0)` on the same side of the chord. -/
private theorem std_same (ℓ p q : ℝ) (hℓ : 0 < ℓ) (hp : 0 < p) (hq : 0 < q)
    (hA : ∠ (pt 0 ℓ) (pt (-p) 0) (pt 0 (-ℓ)) = π / 6)
    (hD : ∠ (pt 0 ℓ) (pt (-q) 0) (pt 0 (-ℓ)) = π / 3) :
    dist (pt (-q) 0) (pt 0 ℓ) < dist (pt (-p) 0) (pt 0 ℓ) ∧
    (volume (Metric.ball (pt (-p) 0) (dist (pt (-p) 0) (pt 0 ℓ)) ∩
        Metric.ball (pt (-q) 0) (dist (pt (-q) 0) (pt 0 ℓ)))).toReal /
      (volume (Metric.ball (pt (-q) 0) (dist (pt (-q) 0) (pt 0 ℓ)))).toReal =
      1 + √3 / 12 - 1 / (2 * π) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < √3 := by positivity
  have hcA := cos_angle_chord ℓ (-p)
  rw [hA, Real.cos_pi_div_six, neg_sq, eq_div_iff (by positivity)] at hcA
  have hcD := cos_angle_chord ℓ (-q)
  rw [hD, Real.cos_pi_div_three, neg_sq, eq_div_iff (by positivity)] at hcD
  have hp2 : p ^ 2 = ((2 + √3) * ℓ) ^ 2 := by
    linear_combination (-2) * (2 + √3) * hcA + p ^ 2 * h3
  have hq2 : q ^ 2 = (√3 * ℓ) ^ 2 := by
    linear_combination (-2) * hcD - ℓ ^ 2 * h3
  have hp' : p = (2 + √3) * ℓ := by
    rw [← Real.sqrt_sq hp.le, hp2, Real.sqrt_sq (by positivity)]
  have hq' : q = √3 * ℓ := by
    rw [← Real.sqrt_sq hq.le, hq2, Real.sqrt_sq (by positivity)]
  have hR2 : dist (pt (-p) 0) (pt 0 ℓ) ^ 2 = p ^ 2 + ℓ ^ 2 := by
    rw [dist_sq']; simp only [pt_zero, pt_one]; ring
  have hr2 : dist (pt (-q) 0) (pt 0 ℓ) ^ 2 = q ^ 2 + ℓ ^ 2 := by
    rw [dist_sq']; simp only [pt_zero, pt_one]; ring
  have hR : 0 < dist (pt (-p) 0) (pt 0 ℓ) := by
    have h := abs_lt_of_sq_lt_sq (show (0 : ℝ) ^ 2 < dist (pt (-p) 0) (pt 0 ℓ) ^ 2 by
      rw [hR2, zero_pow two_ne_zero]; positivity) dist_nonneg
    simpa using h
  have hr : 0 < dist (pt (-q) 0) (pt 0 ℓ) := by
    have h := abs_lt_of_sq_lt_sq (show (0 : ℝ) ^ 2 < dist (pt (-q) 0) (pt 0 ℓ) ^ 2 by
      rw [hr2, zero_pow two_ne_zero]; positivity) dist_nonneg
    simpa using h
  refine ⟨?_, lens_fraction_same ℓ p q _ _ hℓ hp' hq' hR hr hR2 hr2⟩
  have hqp : q < p := by rw [hp', hq']; linarith
  have := abs_lt_of_sq_lt_sq (show dist (pt (-q) 0) (pt 0 ℓ) ^ 2 < dist (pt (-p) 0) (pt 0 ℓ) ^ 2 by
    rw [hR2, hr2]; linarith [sq_lt_sq' (by linarith) hqp]) hR.le
  linarith [le_abs_self (dist (pt (-q) 0) (pt 0 ℓ))]

/-- In a plane, an angle is determined by the three distances. -/
private lemma angle_eq_of_dist {A B C A' B' C' : Plane} (hAB : A ≠ B) (hAC : A ≠ C)
    (h1 : dist A' B' = dist A B) (h2 : dist A' C' = dist A C) (h3 : dist B' C' = dist B C) :
    ∠ B' A' C' = ∠ B A C := by
  have l1 := EuclideanGeometry.law_cos B A C
  have l2 := EuclideanGeometry.law_cos B' A' C'
  rw [dist_comm B' A', dist_comm C' A', h1, h2, h3] at l2
  rw [dist_comm B A, dist_comm C A] at l1
  have hpos : 0 < dist A B * dist A C := mul_pos (dist_pos.2 hAB) (dist_pos.2 hAC)
  have hcos : Real.cos (∠ B' A' C') = Real.cos (∠ B A C) := by
    have : (2 * (dist A B * dist A C)) * (Real.cos (∠ B' A' C') - Real.cos (∠ B A C)) = 0 := by
      linear_combination l2 - l1
    have := (mul_eq_zero.1 this).resolve_left (by positivity)
    linarith
  exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩ hcos

/-- A rigid motion taking the midpoint of `BC` to the origin and `BC` to the `y`-axis (with `B`
above), followed by the reflection `x ↦ -x` when `s = -1`. -/
private noncomputable def frame (B C : Plane) (s : ℝ) (X : Plane) : Plane :=
  pt (s * ((B 1 - C 1) / dist B C * (X 0 - (B 0 + C 0) / 2) -
      (B 0 - C 0) / dist B C * (X 1 - (B 1 + C 1) / 2)))
    ((B 0 - C 0) / dist B C * (X 0 - (B 0 + C 0) / 2) +
      (B 1 - C 1) / dist B C * (X 1 - (B 1 + C 1) / 2))

private lemma unit_dir {B C : Plane} (hBC : B ≠ C) :
    ((B 0 - C 0) / dist B C) ^ 2 + ((B 1 - C 1) / dist B C) ^ 2 = 1 ∧
    B 0 - C 0 = dist B C * ((B 0 - C 0) / dist B C) ∧
    B 1 - C 1 = dist B C * ((B 1 - C 1) / dist B C) := by
  have hn : 0 < dist B C := dist_pos.2 hBC
  have hn2 := dist_sq' B C
  refine ⟨?_, by field_simp, by field_simp⟩
  rw [div_pow, div_pow, ← add_div, ← hn2]
  exact div_self (by positivity)

private lemma frame_dist {B C : Plane} (hBC : B ≠ C) {s : ℝ} (hs : s ^ 2 = 1) (X Y : Plane) :
    dist (frame B C s X) (frame B C s Y) = dist X Y := by
  obtain ⟨he, -, -⟩ := unit_dir hBC
  rw [← pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero, dist_sq', dist_sq']
  unfold frame
  simp only [pt_zero, pt_one]
  set e0 := (B 0 - C 0) / dist B C
  set e1 := (B 1 - C 1) / dist B C
  linear_combination (e1 * (X 0 - Y 0) - e0 * (X 1 - Y 1)) ^ 2 * hs +
    ((X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2) * he

private lemma frame_surj {B C : Plane} (hBC : B ≠ C) {s : ℝ} (hs : s ^ 2 = 1) :
    Function.Surjective (frame B C s) := by
  obtain ⟨he, -, -⟩ := unit_dir hBC
  set e0 := (B 0 - C 0) / dist B C
  set e1 := (B 1 - C 1) / dist B C
  intro Y
  refine ⟨pt ((B 0 + C 0) / 2 + (s * Y 0 * e1 + Y 1 * e0))
    ((B 1 + C 1) / 2 + (-(s * Y 0 * e0) + Y 1 * e1)), ?_⟩
  ext i
  fin_cases i
  · simp only [frame, Fin.zero_eta, Fin.isValue, pt_zero, pt_one]
    linear_combination (Y 0 * (e0 ^ 2 + e1 ^ 2)) * hs + Y 0 * he
  · simp only [frame, Fin.mk_one, Fin.isValue, pt_zero, pt_one]
    linear_combination Y 1 * he

/-- Rigid motions preserve area. -/
private lemma frame_volume {B C : Plane} (hBC : B ≠ C) {s : ℝ} (hs : s ^ 2 = 1) (S : Set Plane) :
    volume (frame B C s ⁻¹' S) = volume S := by
  have hiso : Isometry (frame B C s) := Isometry.of_dist_eq (frame_dist hBC hs)
  have hv : (volume : Measure Plane) = μHE[2] :=
    (EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2).symm
  rw [hv, hiso.euclideanHausdorffMeasure_preimage, (frame_surj hBC hs).range_eq, Set.inter_univ]

/-- **Problem 37.** Two circles, with centres `A` and `D`, meet at `B` and `C` (the circle about
`A` has radius `AB = AC`, that about `D` radius `DB = DC`), and the centres lie on opposite sides
of the common chord `BC` (Carroll's figure). If the chord subtends `30°` at `A` and `60°` at
`D`, then the circle about `D` is the smaller one, and the fraction of its area lying within the
circle about `A` is `(4 + √3)/12 - (1 + √3)/(2π)`. -/
theorem problem37 (A D B C : Plane) (hAC : dist A C = dist A B) (hDC : dist D C = dist D B)
    (hside : cross B C A * cross B C D < 0)
    (hA : ∠ B A C = π / 6) (hD : ∠ B D C = π / 3) :
    dist D B < dist A B ∧
    (volume (Metric.ball A (dist A B) ∩ Metric.ball D (dist D B))).toReal /
      (volume (Metric.ball D (dist D B))).toReal =
      (4 + √3) / 12 - (1 + √3) / (2 * π) := by
  have hKA0 : cross B C A ≠ 0 := by
    rintro h; rw [h, zero_mul] at hside; exact lt_irrefl _ hside
  have hKD0 : cross B C D ≠ 0 := by
    rintro h; rw [h, mul_zero] at hside; exact lt_irrefl _ hside
  have hBC : B ≠ C := by rintro rfl; apply hKA0; unfold cross; ring
  have hAB : A ≠ B := by rintro rfl; apply hKA0; unfold cross; ring
  have hAC' : A ≠ C := by rintro rfl; apply hKA0; unfold cross; ring
  have hDB : D ≠ B := by rintro rfl; apply hKD0; unfold cross; ring
  have hDC' : D ≠ C := by rintro rfl; apply hKD0; unfold cross; ring
  obtain ⟨s, hs, hsA, hsD⟩ : ∃ s : ℝ, s ^ 2 = 1 ∧ s * cross B C A < 0 ∧
      0 < s * cross B C D := by
    rcases lt_or_gt_of_ne hKA0 with h | h
    · exact ⟨1, by norm_num, by linarith, by nlinarith⟩
    · exact ⟨-1, by norm_num, by linarith, by nlinarith⟩
  have hn : 0 < dist B C := dist_pos.2 hBC
  have hfd := frame_dist hBC hs
  obtain ⟨he, he0, he1⟩ := unit_dir hBC
  have hAeq := dist_sq' A C
  have hAeq' := dist_sq' A B
  have hDeq := dist_sq' D C
  have hDeq' := dist_sq' D B
  rw [hAC] at hAeq
  rw [hDC] at hDeq
  set n := dist B C with hn_def
  set e0 := (B 0 - C 0) / n
  set e1 := (B 1 - C 1) / n
  set m0 := (B 0 + C 0) / 2
  set m1 := (B 1 + C 1) / 2
  -- the centres, in the new frame
  have hKA : cross B C A = n * (e1 * (A 0 - m0) - e0 * (A 1 - m1)) := by
    unfold cross; linear_combination (A 0 - m0) * he1 - (A 1 - m1) * he0
  have hKD : cross B C D = n * (e1 * (D 0 - m0) - e0 * (D 1 - m1)) := by
    unfold cross; linear_combination (D 0 - m0) * he1 - (D 1 - m1) * he0
  have hA1 : e0 * (A 0 - m0) + e1 * (A 1 - m1) = 0 := by
    have : n * (e0 * (A 0 - m0) + e1 * (A 1 - m1)) = 0 := by
      linear_combination hAeq' / 2 - hAeq / 2 - (A 0 - m0) * he0 - (A 1 - m1) * he1
    exact (mul_eq_zero.1 this).resolve_left hn.ne'
  have hD1 : e0 * (D 0 - m0) + e1 * (D 1 - m1) = 0 := by
    have : n * (e0 * (D 0 - m0) + e1 * (D 1 - m1)) = 0 := by
      linear_combination hDeq' / 2 - hDeq / 2 - (D 0 - m0) * he0 - (D 1 - m1) * he1
    exact (mul_eq_zero.1 this).resolve_left hn.ne'
  set p := -(s * (e1 * (A 0 - m0) - e0 * (A 1 - m1))) with hp_def
  set q := s * (e1 * (D 0 - m0) - e0 * (D 1 - m1)) with hq_def
  have hp : 0 < p := by
    have h' : n * p = -(s * cross B C A) := by rw [hKA, hp_def]; ring
    by_contra h
    have := mul_le_mul_of_nonneg_left (not_lt.1 h) hn.le
    linarith
  have hq : 0 < q := by
    have h' : n * q = s * cross B C D := by rw [hKD, hq_def]; ring
    by_contra h
    have := mul_le_mul_of_nonneg_left (not_lt.1 h) hn.le
    linarith
  have hfB : frame B C s B = pt 0 (n / 2) := by
    ext i; fin_cases i
    · simp only [frame, Fin.zero_eta, Fin.isValue, pt_zero]
      linear_combination (s * e1 / 2) * he0 - (s * e0 / 2) * he1
    · simp only [frame, Fin.mk_one, Fin.isValue, pt_one]
      linear_combination (e0 / 2) * he0 + (e1 / 2) * he1 + (n / 2) * he
  have hfC : frame B C s C = pt 0 (-(n / 2)) := by
    ext i; fin_cases i
    · simp only [frame, Fin.zero_eta, Fin.isValue, pt_zero]
      linear_combination (-(s * e1 / 2)) * he0 + (s * e0 / 2) * he1
    · simp only [frame, Fin.mk_one, Fin.isValue, pt_one]
      linear_combination (-(e0 / 2)) * he0 - (e1 / 2) * he1 - (n / 2) * he
  have hfA : frame B C s A = pt (-p) 0 := by
    ext i; fin_cases i
    · simp only [frame, Fin.zero_eta, Fin.isValue, pt_zero, hp_def]; ring
    · simp only [frame, Fin.mk_one, Fin.isValue, pt_one]; exact hA1
  have hfD : frame B C s D = pt q 0 := by
    ext i; fin_cases i
    · simp only [frame, Fin.zero_eta, Fin.isValue, pt_zero, hq_def]; rfl
    · simp only [frame, Fin.mk_one, Fin.isValue, pt_one]; exact hD1
  have hA' := angle_eq_of_dist hAB hAC' (hfd A B) (hfd A C) (hfd B C)
  have hD' := angle_eq_of_dist hDB hDC' (hfd D B) (hfd D C) (hfd B C)
  rw [hfA, hfB, hfC, hA] at hA'
  rw [hfD, hfB, hfC, hD] at hD'
  obtain ⟨k1, k2⟩ := std (n / 2) p q (by positivity) hp hq hA' hD'
  rw [← hfA, ← hfB, ← hfD, hfd, hfd] at k1 k2
  have hpre : ∀ (X : Plane) (r : ℝ),
      frame B C s ⁻¹' Metric.ball (frame B C s X) r = Metric.ball X r := by
    intro X r; ext Y; simp only [Set.mem_preimage, Metric.mem_ball, hfd]
  refine ⟨k1, ?_⟩
  rw [← hpre A, ← hpre D, ← Set.preimage_inter, frame_volume hBC hs, frame_volume hBC hs]
  exact k2

/-- The other reading of problem 37: the same circles, but with both centres on the same side of
the common chord `BC`. Then the circle about `D` is again the smaller one, and the fraction of
its area lying within the circle about `A` is `1 + √3/12 - 1/(2π)` (about `·985`). -/
theorem problem37_sameSide (A D B C : Plane) (hAC : dist A C = dist A B)
    (hDC : dist D C = dist D B)
    (hside : 0 < cross B C A * cross B C D)
    (hA : ∠ B A C = π / 6) (hD : ∠ B D C = π / 3) :
    dist D B < dist A B ∧
    (volume (Metric.ball A (dist A B) ∩ Metric.ball D (dist D B))).toReal /
      (volume (Metric.ball D (dist D B))).toReal =
      1 + √3 / 12 - 1 / (2 * π) := by
  have hKA0 : cross B C A ≠ 0 := by
    rintro h; rw [h, zero_mul] at hside; exact lt_irrefl _ hside
  have hKD0 : cross B C D ≠ 0 := by
    rintro h; rw [h, mul_zero] at hside; exact lt_irrefl _ hside
  have hBC : B ≠ C := by rintro rfl; apply hKA0; unfold cross; ring
  have hAB : A ≠ B := by rintro rfl; apply hKA0; unfold cross; ring
  have hAC' : A ≠ C := by rintro rfl; apply hKA0; unfold cross; ring
  have hDB : D ≠ B := by rintro rfl; apply hKD0; unfold cross; ring
  have hDC' : D ≠ C := by rintro rfl; apply hKD0; unfold cross; ring
  obtain ⟨s, hs, hsA, hsD⟩ : ∃ s : ℝ, s ^ 2 = 1 ∧ s * cross B C A < 0 ∧
      s * cross B C D < 0 := by
    rcases lt_or_gt_of_ne hKA0 with h | h
    · exact ⟨1, by norm_num, by linarith, by nlinarith⟩
    · exact ⟨-1, by norm_num, by linarith, by nlinarith⟩
  have hn : 0 < dist B C := dist_pos.2 hBC
  have hfd := frame_dist hBC hs
  obtain ⟨he, he0, he1⟩ := unit_dir hBC
  have hAeq := dist_sq' A C
  have hAeq' := dist_sq' A B
  have hDeq := dist_sq' D C
  have hDeq' := dist_sq' D B
  rw [hAC] at hAeq
  rw [hDC] at hDeq
  set n := dist B C with hn_def
  set e0 := (B 0 - C 0) / n
  set e1 := (B 1 - C 1) / n
  set m0 := (B 0 + C 0) / 2
  set m1 := (B 1 + C 1) / 2
  -- the centres, in the new frame
  have hKA : cross B C A = n * (e1 * (A 0 - m0) - e0 * (A 1 - m1)) := by
    unfold cross; linear_combination (A 0 - m0) * he1 - (A 1 - m1) * he0
  have hKD : cross B C D = n * (e1 * (D 0 - m0) - e0 * (D 1 - m1)) := by
    unfold cross; linear_combination (D 0 - m0) * he1 - (D 1 - m1) * he0
  have hA1 : e0 * (A 0 - m0) + e1 * (A 1 - m1) = 0 := by
    have : n * (e0 * (A 0 - m0) + e1 * (A 1 - m1)) = 0 := by
      linear_combination hAeq' / 2 - hAeq / 2 - (A 0 - m0) * he0 - (A 1 - m1) * he1
    exact (mul_eq_zero.1 this).resolve_left hn.ne'
  have hD1 : e0 * (D 0 - m0) + e1 * (D 1 - m1) = 0 := by
    have : n * (e0 * (D 0 - m0) + e1 * (D 1 - m1)) = 0 := by
      linear_combination hDeq' / 2 - hDeq / 2 - (D 0 - m0) * he0 - (D 1 - m1) * he1
    exact (mul_eq_zero.1 this).resolve_left hn.ne'
  set p := -(s * (e1 * (A 0 - m0) - e0 * (A 1 - m1))) with hp_def
  set q := -(s * (e1 * (D 0 - m0) - e0 * (D 1 - m1))) with hq_def
  have hp : 0 < p := by
    have h' : n * p = -(s * cross B C A) := by rw [hKA, hp_def]; ring
    by_contra h
    have := mul_le_mul_of_nonneg_left (not_lt.1 h) hn.le
    linarith
  have hq : 0 < q := by
    have h' : n * q = -(s * cross B C D) := by rw [hKD, hq_def]; ring
    by_contra h
    have := mul_le_mul_of_nonneg_left (not_lt.1 h) hn.le
    linarith
  have hfB : frame B C s B = pt 0 (n / 2) := by
    ext i; fin_cases i
    · simp only [frame, Fin.zero_eta, Fin.isValue, pt_zero]
      linear_combination (s * e1 / 2) * he0 - (s * e0 / 2) * he1
    · simp only [frame, Fin.mk_one, Fin.isValue, pt_one]
      linear_combination (e0 / 2) * he0 + (e1 / 2) * he1 + (n / 2) * he
  have hfC : frame B C s C = pt 0 (-(n / 2)) := by
    ext i; fin_cases i
    · simp only [frame, Fin.zero_eta, Fin.isValue, pt_zero]
      linear_combination (-(s * e1 / 2)) * he0 + (s * e0 / 2) * he1
    · simp only [frame, Fin.mk_one, Fin.isValue, pt_one]
      linear_combination (-(e0 / 2)) * he0 - (e1 / 2) * he1 - (n / 2) * he
  have hfA : frame B C s A = pt (-p) 0 := by
    ext i; fin_cases i
    · simp only [frame, Fin.zero_eta, Fin.isValue, pt_zero, hp_def]; ring
    · simp only [frame, Fin.mk_one, Fin.isValue, pt_one]; exact hA1
  have hfD : frame B C s D = pt (-q) 0 := by
    ext i; fin_cases i
    · simp only [frame, Fin.zero_eta, Fin.isValue, pt_zero, hq_def]; ring
    · simp only [frame, Fin.mk_one, Fin.isValue, pt_one]; exact hD1
  have hA' := angle_eq_of_dist hAB hAC' (hfd A B) (hfd A C) (hfd B C)
  have hD' := angle_eq_of_dist hDB hDC' (hfd D B) (hfd D C) (hfd B C)
  rw [hfA, hfB, hfC, hA] at hA'
  rw [hfD, hfB, hfC, hD] at hD'
  obtain ⟨k1, k2⟩ := std_same (n / 2) p q (by positivity) hp hq hA' hD'
  rw [← hfA, ← hfB, ← hfD, hfd, hfd] at k1 k2
  have hpre : ∀ (X : Plane) (r : ℝ),
      frame B C s ⁻¹' Metric.ball (frame B C s X) r = Metric.ball X r := by
    intro X r; ext Y; simp only [Set.mem_preimage, Metric.mem_ball, hfd]
  refine ⟨k1, ?_⟩
  rw [← hpre A, ← hpre D, ← Set.preimage_inter, frame_volume hBC hs, frame_volume hBC hs]
  exact k2

/-- Both figures exist: chord `B = (0, 1)`, `C = (0, -1)`, centre `A = (-(2 + √3), 0)`, and
centre `D = (√3, 0)` (opposite sides) or `D = (-√3, 0)` (same side). So the hypotheses of
`problem37` and of `problem37_sameSide` are satisfiable. -/
theorem problem37_nonvacuous :
    (∃ A D B C : Plane, dist A C = dist A B ∧ dist D C = dist D B ∧
      cross B C A * cross B C D < 0 ∧ ∠ B A C = π / 6 ∧ ∠ B D C = π / 3) ∧
    (∃ A D B C : Plane, dist A C = dist A B ∧ dist D C = dist D B ∧
      0 < cross B C A * cross B C D ∧ ∠ B A C = π / 6 ∧ ∠ B D C = π / 3) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < √3 := by positivity
  have hang : ∀ x : ℝ, ∠ (pt 0 1) (pt x 0) (pt 0 (-1)) =
      Real.arccos ((x ^ 2 - 1 ^ 2) / (x ^ 2 + 1 ^ 2)) := by
    intro x
    rw [← cos_angle_chord, Real.arccos_cos (EuclideanGeometry.angle_nonneg _ _ _)
      (EuclideanGeometry.angle_le_pi _ _ _)]
  have hdist : ∀ x : ℝ, dist (pt x 0) (pt 0 (-1)) = dist (pt x 0) (pt 0 1) := by
    intro x
    rw [← pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero, dist_sq', dist_sq']
    simp only [pt_zero, pt_one]; ring
  have hcross : ∀ x : ℝ, cross (pt 0 1) (pt 0 (-1)) (pt x 0) = 2 * x := by
    intro x; unfold cross; simp only [pt_zero, pt_one]; ring
  have hA : ∠ (pt 0 1) (pt (-(2 + √3)) 0) (pt 0 (-1)) = π / 6 := by
    rw [hang, show ((-(2 + √3)) ^ 2 - 1 ^ 2) / ((-(2 + √3)) ^ 2 + 1 ^ 2) = Real.cos (π / 6) by
      rw [Real.cos_pi_div_six, div_eq_iff (by positivity)]
      linear_combination (-(1 + √3 / 2)) * h3,
      Real.arccos_cos (by positivity) (by linarith [pi_pos])]
  have hD : ∀ x : ℝ, x ^ 2 = 3 → ∠ (pt 0 1) (pt x 0) (pt 0 (-1)) = π / 3 := by
    intro x hx
    rw [hang, hx, show ((3 : ℝ) - 1 ^ 2) / (3 + 1 ^ 2) = Real.cos (π / 3) by
      rw [Real.cos_pi_div_three]; norm_num,
      Real.arccos_cos (by positivity) (by linarith [pi_pos])]
  refine ⟨⟨_, pt √3 0, _, _, hdist _, hdist _, ?_, hA, hD _ h3⟩,
    ⟨_, pt (-√3) 0, _, _, hdist _, hdist _, ?_, hA, hD _ (by rw [neg_sq, h3])⟩⟩
  · rw [hcross, hcross]
    have := mul_pos (by positivity : (0 : ℝ) < 4 * (2 + √3)) h3p
    linarith [show 2 * -(2 + √3) * (2 * √3) = -(4 * (2 + √3) * √3) by ring]
  · rw [hcross, hcross]
    have := mul_pos (by positivity : (0 : ℝ) < 4 * (2 + √3)) h3p
    linarith [show 2 * -(2 + √3) * (2 * -√3) = 4 * (2 + √3) * √3 by ring]

/-- Carroll's decimal "about ·044" is slightly off: the fraction lies between `·042` and `·043`
(it is `·0429…`; Carroll's `·044` comes from rounding the two terms to `·478` and `·434`). -/
theorem problem37_approx :
    0.042 < (4 + √3) / 12 - (1 + √3) / (2 * π) ∧ (4 + √3) / 12 - (1 + √3) / (2 * π) < 0.043 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 ≤ √3 := Real.sqrt_nonneg 3
  have hs1 : 1.732 < √3 := by nlinarith
  have hs2 : √3 < 1.7321 := by nlinarith
  have hp1 := pi_gt_d4
  have hp2 := pi_lt_d4
  have hpi : 0 < 2 * π := by positivity
  have hu : (1 + √3) / (2 * π) < 0.4349 := by
    rw [div_lt_iff₀ hpi]; nlinarith
  have hl : 0.4348 < (1 + √3) / (2 * π) := by
    rw [lt_div_iff₀ hpi]; nlinarith
  constructor <;> linarith

end PillowProblems.P37
