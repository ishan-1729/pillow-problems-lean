import PillowProblems.Basic

/-!
# Problem 58 (Algebra: Chances)

**Question.** *(dated 20/1/84)*

> Three Points are taken at random on an infinite Plane. Find the chance of their being the vertices of an obtuse-angled Triangle.

**Answer.**

> \[ \frac{3}{8 - \dfrac{6\sqrt{3}}{\pi}}. \]

*(Carroll's solution: Chapter III, problem 58; text in `data/problems.json`.)*

**Lean reading.** As stated the problem is ill-posed (there is no uniform distribution on an
infinite plane, and other ways of making "at random" precise give other values, e.g.
`9/8 − 4/π² ≈ 0.72` for three points uniform in a disc, against Carroll's `≈ 0.64`), so we
formalize exactly the reading of Carroll's solution: the longest side `AB` (any `A ≠ B`) is fixed
and the third vertex `C` is uniform (normalised Lebesgue measure, `ProbabilityTheory.cond volume`)
over his figure `ABDCE`, i.e. `carrollRegion A B`, the points left of `AB` with `CA < AB` and
`CB < AB`; the other side of `AB` is `carrollRegion B A` (`carrollRegion_swap`), so it is covered
too. Ties between sides, collinear `C` and boundary points are null sets (Carroll's "practically
*nil*"), so strict inequalities are used. "Obtuse-angled" is the literal condition that some
unoriented angle `∠` of `ABC` exceeds `π/2`, not Carroll's semicircle criterion, which is proved
(`problem58_obtuse_iff`). With `AB = 2a` the areas `πa²/2` and `a²(4π/3 − √3)` are derived by a
change of variables and integration, giving the chance `3/(8 − 6√3/π)`. That `C` is uniform over
the figure once the longest side is fixed is Carroll's own assumption, not derived from any limit
of uniform distributions on bounded regions.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P58

open Real MeasureTheory Set EuclideanGeometry

/-- Carroll's figure `ABDCE`: the points `C` on the left of the directed line `AB`
(`0 < cross A B C`) for which `AB` is strictly the longest side of `ABC`. Where the third vertex
may lie once `AB` is named as the longest side. -/
def carrollRegion (A B : Plane) : Set Plane :=
  {C | dist C A < dist A B ∧ dist C B < dist A B ∧ 0 < cross A B C}

/-- The triangle `ABC` is obtuse-angled: one of its three angles exceeds a right angle. -/
def IsObtuse (A B C : Plane) : Prop :=
  π / 2 < ∠ B A C ∨ π / 2 < ∠ A B C ∨ π / 2 < ∠ A C B

/-- Carroll's chance: the probability that `ABC` is obtuse-angled when `C` is uniformly
distributed (normalised Lebesgue measure) over `carrollRegion A B`. -/
noncomputable def obtuseChance (A B : Plane) : ℝ :=
  (ProbabilityTheory.cond volume (carrollRegion A B) {C | IsObtuse A B C}).toReal

/-- The figure on the other side of `AB` is `carrollRegion B A`, so every statement below for all
`A ≠ B` covers both sides. -/
theorem carrollRegion_swap (A B : Plane) :
    carrollRegion B A = {C | dist C A < dist A B ∧ dist C B < dist A B ∧ cross A B C < 0} := by
  ext C
  have h : cross B A C = -cross A B C := by unfold cross; ring
  simp only [carrollRegion, mem_ofPred_eq, h, dist_comm B A, neg_pos]
  tauto

private noncomputable def eqv : Plane ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

private lemma eqv_apply (p : Plane) : eqv p = (p 0, p 1) := rfl

private lemma eqv_pres : MeasurePreserving eqv volume volume :=
  (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

private lemma dist_sq' (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
    Real.dist_eq, sq_abs, sq_abs]

private lemma inner' (x y : Plane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

private lemma isObtuse_iff (A B C : Plane) : IsObtuse A B C ↔
    inner ℝ (B - A) (C - A) < 0 ∨ inner ℝ (A - B) (C - B) < 0 ∨ inner ℝ (A - C) (B - C) < 0 := by
  simp only [IsObtuse, EuclideanGeometry.angle,
    ← InnerProductGeometry.inner_neg_iff_pi_div_two_lt_angle, vsub_eq_sub]

private lemma isOpen_region (A B : Plane) : IsOpen (carrollRegion A B) := by
  have hc : Continuous fun C : Plane => cross A B C := by unfold cross; fun_prop
  have h1 : IsOpen {C : Plane | dist C A < dist A B} :=
    isOpen_lt (by fun_prop) continuous_const
  have h2 : IsOpen {C : Plane | dist C B < dist A B} :=
    isOpen_lt (by fun_prop) continuous_const
  have h3 : IsOpen {C : Plane | 0 < cross A B C} := isOpen_lt continuous_const hc
  exact h1.inter (h2.inter h3)

/-- Carroll's key step: inside the figure, the triangle is obtuse-angled exactly when `C` lies
inside the semicircle on `AB`. -/
theorem problem58_obtuse_iff (A B C : Plane) (hC : C ∈ carrollRegion A B) :
    IsObtuse A B C ↔ dist C (midpoint ℝ A B) < dist A B / 2 := by
  obtain ⟨h1, h2, -⟩ := hC
  have h1' := (sq_lt_sq₀ dist_nonneg dist_nonneg).2 h1
  have h2' := (sq_lt_sq₀ dist_nonneg dist_nonneg).2 h2
  have hm : ∀ i, (midpoint ℝ A B) i = (A i + B i) / 2 := by
    intro i; rw [midpoint_eq_smul_add]; simp; ring
  rw [dist_sq', dist_sq'] at h1' h2'
  rw [isObtuse_iff, inner', inner', inner', ← sq_lt_sq₀ dist_nonneg (by positivity), div_pow,
    dist_sq', dist_sq', hm, hm]
  simp only [PiLp.sub_apply]
  constructor
  · rintro (h | h | h) <;> nlinarith
  · intro h; right; right; nlinarith

/-! Integrals. -/

private lemma hasDerivAt_F (r x : ℝ) (hr : 0 < r) (hx : |x| < r) :
    HasDerivAt (fun x => (x * √(r ^ 2 - x ^ 2) + r ^ 2 * arcsin (x / r)) / 2)
      (√(r ^ 2 - x ^ 2)) x := by
  have hpos : 0 < r ^ 2 - x ^ 2 := by
    have := sq_lt_sq' (abs_lt.1 hx).1 (abs_lt.1 hx).2
    linarith
  have hxr : |x / r| < 1 := by rw [abs_div, abs_of_pos hr, div_lt_one hr]; exact hx
  have h1 := (hasDerivAt_id' x).mul (((hasDerivAt_pow 2 x).const_sub (r ^ 2)).sqrt hpos.ne')
  have h2 := (Real.hasDerivAt_arcsin (x := x / r) (by intro h; rw [h] at hxr; norm_num at hxr)
      (by intro h; rw [h] at hxr; norm_num at hxr)).comp x ((hasDerivAt_id' x).div_const r)
  convert (h1.add (h2.const_mul (r ^ 2))).div_const 2 using 1
  · funext y; simp [Function.comp_apply]
  have hs : √(1 - (x / r) ^ 2) = √(r ^ 2 - x ^ 2) / r := by
    rw [show 1 - (x / r) ^ 2 = (r ^ 2 - x ^ 2) / r ^ 2 by field_simp, sqrt_div' _ (sq_nonneg r),
      sqrt_sq hr.le]
  rw [hs]
  have hS : 0 < √(r ^ 2 - x ^ 2) := sqrt_pos.2 hpos
  have hS2 : √(r ^ 2 - x ^ 2) ^ 2 = r ^ 2 - x ^ 2 := sq_sqrt hpos.le
  norm_num
  field_simp
  linear_combination hS2

private lemma integral_sqrt_sub_sq (r b : ℝ) (hr : 0 < r) (hb : 0 ≤ b) (hbr : b ≤ r) :
    ∫ x in (0 : ℝ)..b, √(r ^ 2 - x ^ 2) = (b * √(r ^ 2 - b ^ 2) + r ^ 2 * arcsin (b / r)) / 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb
    (f := fun x => (x * √(r ^ 2 - x ^ 2) + r ^ 2 * arcsin (x / r)) / 2)]
  · simp
  · exact (by fun_prop : Continuous fun x : ℝ =>
      (x * √(r ^ 2 - x ^ 2) + r ^ 2 * arcsin (x / r)) / 2).continuousOn
  · intro x hx
    apply hasDerivAt_F r x hr
    rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
  · exact (by fun_prop : Continuous fun x : ℝ => √(r ^ 2 - x ^ 2)).intervalIntegrable _ _

private lemma integral_one : ∫ x in (0 : ℝ)..1, √(1 - x ^ 2) = π / 4 := by
  have := integral_sqrt_sub_sq 1 1 one_pos zero_le_one le_rfl
  norm_num at this
  rw [this]; ring

private lemma sqrt3_le_two : √3 ≤ 2 := by
  rw [sqrt_le_left (by norm_num)]; norm_num

private lemma integral_two : ∫ x in (0 : ℝ)..√3, √(4 - x ^ 2) = √3 / 2 + 2 * π / 3 := by
  have := integral_sqrt_sub_sq 2 (√3) two_pos (sqrt_nonneg _) sqrt3_le_two
  have e1 : (2:ℝ) ^ 2 - √3 ^ 2 = 1 := by rw [sq_sqrt (by norm_num)]; norm_num
  have e2 : arcsin (√3 / 2) = π / 3 := by
    rw [← sin_pi_div_three, arcsin_sin] <;> linarith [pi_pos]
  rw [e1, e2] at this
  norm_num at this ⊢
  rw [this]; ring

/-! Standard regions in `ℝ × ℝ`. -/

private def TO : Set (ℝ × ℝ) := {q | q.1 ^ 2 + q.2 ^ 2 < 1 ∧ 0 < q.1}

private def TR : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 + (q.2 - 1) ^ 2 < 4 ∧ q.1 ^ 2 + (q.2 + 1) ^ 2 < 4 ∧ 0 < q.1}

private lemma vol_TO : volume TO = ENNReal.ofReal (π / 2) := by
  have hset : TO = regionBetween (fun x => -√(1 - x ^ 2)) (fun x => √(1 - x ^ 2)) (Ioo 0 1) := by
    ext ⟨x, y⟩
    simp only [TO, mem_ofPred_eq, regionBetween, mem_Ioo]
    have ht := sqrt_nonneg (1 - x ^ 2)
    constructor
    · rintro ⟨h1, h2⟩
      have hx : 0 ≤ 1 - x ^ 2 := by nlinarith
      have ht2 := sq_sqrt hx
      refine ⟨⟨h2, by nlinarith⟩, ?_, ?_⟩ <;> nlinarith
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      have hx : 0 ≤ 1 - x ^ 2 := by nlinarith
      have ht2 := sq_sqrt hx
      exact ⟨by nlinarith, h1⟩
  have hc : Continuous fun x : ℝ => √(1 - x ^ 2) := by fun_prop
  rw [hset, Measure.volume_eq_prod, volume_regionBetween_eq_integral]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    simp only [Pi.sub_apply, sub_neg_eq_add]
    rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
      integral_one]
    ring
  · exact hc.neg.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  · exact hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  · exact measurableSet_Ioo
  · intro x _; linarith [sqrt_nonneg (1 - x ^ 2)]

private lemma vol_TR : volume TR = ENNReal.ofReal (4 * π / 3 - √3) := by
  have hset : TR = regionBetween (fun x => 1 - √(4 - x ^ 2)) (fun x => √(4 - x ^ 2) - 1)
      (Ioo 0 √3) := by
    ext ⟨x, y⟩
    simp only [TR, mem_ofPred_eq, regionBetween, mem_Ioo]
    have ht := sqrt_nonneg (4 - x ^ 2)
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hx : 0 ≤ 4 - x ^ 2 := by nlinarith
      have ht2 := sq_sqrt hx
      have hx3 : x < √3 := (lt_sqrt h3.le).2 (by nlinarith)
      refine ⟨⟨h3, hx3⟩, ?_, ?_⟩
      · by_contra hc; push Not at hc; nlinarith
      · by_contra hc; push Not at hc; nlinarith
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      have hx2 : x ^ 2 < 3 := by
        have := (lt_sqrt h1.le).1 h2; linarith
      have hx : 0 ≤ 4 - x ^ 2 := by nlinarith
      have ht2 := sq_sqrt hx
      refine ⟨by nlinarith, by nlinarith, h1⟩
  have hc : Continuous fun x : ℝ => √(4 - x ^ 2) := by fun_prop
  rw [hset, Measure.volume_eq_prod, volume_regionBetween_eq_integral]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (sqrt_nonneg 3)]
    have hfun : ((fun x : ℝ => √(4 - x ^ 2) - 1) - fun x => 1 - √(4 - x ^ 2)) =
        fun x => 2 * √(4 - x ^ 2) - 2 := by
      funext x; simp only [Pi.sub_apply]; ring
    rw [hfun, intervalIntegral.integral_sub ((hc.intervalIntegrable _ _).const_mul 2)
      intervalIntegrable_const, intervalIntegral.integral_const_mul, integral_two,
      intervalIntegral.integral_const]
    simp
    ring
  · exact (continuous_const.sub hc).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  · exact (hc.sub continuous_const).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  · exact measurableSet_Ioo
  · intro x hx
    have : 1 ≤ √(4 - x ^ 2) := by
      have := (lt_sqrt hx.1.le).1 hx.2
      rw [← sqrt_one]; exact sqrt_le_sqrt (by linarith)
    linarith

/-! The similarity taking the standard configuration to `A, B`. -/

private noncomputable def simL (u0 u1 : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun p := pt (p 0 * u1 + p 1 * u0) (-(p 0 * u0) + p 1 * u1)
  map_add' x y := by
    refine PiLp.ext fun i => ?_
    fin_cases i <;> simp [pt] <;> ring
  map_smul' c x := by
    refine PiLp.ext fun i => ?_
    fin_cases i <;> simp [pt] <;> ring

private lemma simL_det (u0 u1 : ℝ) : LinearMap.det (simL u0 u1) = u0 ^ 2 + u1 ^ 2 := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, simL, pt]
  ring

private noncomputable def Lof (A B : Plane) : Plane →ₗ[ℝ] Plane :=
  simL ((A 0 - B 0) / 2) ((A 1 - B 1) / 2)

private noncomputable def mid (A B : Plane) : Plane := pt ((A 0 + B 0) / 2) ((A 1 + B 1) / 2)

private noncomputable def sc (A B : Plane) : ℝ := ((A 0 - B 0) / 2) ^ 2 + ((A 1 - B 1) / 2) ^ 2

private lemma g0 (A B p : Plane) : (Lof A B p + mid A B) 0 =
    p 0 * ((A 1 - B 1) / 2) + p 1 * ((A 0 - B 0) / 2) + (A 0 + B 0) / 2 := by
  simp [Lof, simL, mid]

private lemma g1 (A B p : Plane) : (Lof A B p + mid A B) 1 =
    -(p 0 * ((A 0 - B 0) / 2)) + p 1 * ((A 1 - B 1) / 2) + (A 1 + B 1) / 2 := by
  simp [Lof, simL, mid]

private lemma sc_pos (A B : Plane) (hAB : A ≠ B) : 0 < sc A B := by
  unfold sc
  by_contra h
  apply hAB
  have h0 : A 0 = B 0 := by nlinarith [sq_nonneg ((A 0 - B 0) / 2), sq_nonneg ((A 1 - B 1) / 2)]
  have h1 : A 1 = B 1 := by nlinarith [sq_nonneg ((A 0 - B 0) / 2), sq_nonneg ((A 1 - B 1) / 2)]
  refine PiLp.ext fun i => ?_
  fin_cases i
  · exact h0
  · exact h1

private lemma dist_half_sq (A B : Plane) : (dist A B / 2) ^ 2 = sc A B := by
  rw [div_pow, dist_sq', sc]; ring

private lemma vol_transfer (A B : Plane) (hAB : A ≠ B) (S : Set Plane) (T : Set (ℝ × ℝ))
    (h : Lof A B ⁻¹' ((· + mid A B) ⁻¹' S) = eqv ⁻¹' T) :
    volume S = ENNReal.ofReal ((dist A B / 2) ^ 2) * volume T := by
  have hs := sc_pos A B hAB
  have hdet : LinearMap.det (Lof A B) = sc A B := simL_det _ _
  rw [dist_half_sq, ← eqv_pres.measure_preimage_equiv T, ← h,
    Measure.addHaar_preimage_linearMap volume (by rw [hdet]; exact hs.ne'),
    measure_preimage_add_right, hdet, abs_of_pos (inv_pos.2 hs), ← mul_assoc,
    ← ENNReal.ofReal_mul hs.le, mul_inv_cancel₀ hs.ne', ENNReal.ofReal_one, one_mul]

private lemma lt_cancel {s a b : ℝ} (hs : 0 < s) : s * a < s * b ↔ a < b := by
  constructor <;> intro h <;> nlinarith

private lemma neg_cancel {s a : ℝ} (hs : 0 < s) : s * a < 0 ↔ a < 0 := by
  constructor <;> intro h <;> nlinarith

private lemma pos_cancel {s a : ℝ} (hs : 0 < s) : 0 < s * a ↔ 0 < a := by
  constructor <;> intro h <;> nlinarith

private lemma atoms (A B p : Plane) :
    dist (Lof A B p + mid A B) A ^ 2 = sc A B * (p 0 ^ 2 + (p 1 - 1) ^ 2) ∧
    dist (Lof A B p + mid A B) B ^ 2 = sc A B * (p 0 ^ 2 + (p 1 + 1) ^ 2) ∧
    dist A B ^ 2 = sc A B * 4 ∧
    cross A B (Lof A B p + mid A B) = sc A B * (2 * p 0) ∧
    inner ℝ (B - A) (Lof A B p + mid A B - A) = sc A B * (2 - 2 * p 1) ∧
    inner ℝ (A - B) (Lof A B p + mid A B - B) = sc A B * (2 * p 1 + 2) ∧
    inner ℝ (A - (Lof A B p + mid A B)) (B - (Lof A B p + mid A B)) =
      sc A B * (p 0 ^ 2 + p 1 ^ 2 - 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dist_sq', g0, g1, sc]; ring
  · rw [dist_sq', g0, g1, sc]; ring
  · rw [dist_sq', sc]; ring
  · rw [cross, g0, g1, sc]; ring
  · rw [inner']; simp only [PiLp.sub_apply]; rw [g0, g1, sc]; ring
  · rw [inner']; simp only [PiLp.sub_apply]; rw [g0, g1, sc]; ring
  · rw [inner']; simp only [PiLp.sub_apply]; rw [g0, g1, sc]; ring

private lemma preimage_region (A B : Plane) (hAB : A ≠ B) :
    Lof A B ⁻¹' ((· + mid A B) ⁻¹' carrollRegion A B) = eqv ⁻¹' TR := by
  have hs := sc_pos A B hAB
  ext p
  obtain ⟨e1, e2, e3, e4, -, -, -⟩ := atoms A B p
  simp only [mem_preimage, carrollRegion, TR, mem_ofPred_eq, eqv_apply]
  rw [← sq_lt_sq₀ dist_nonneg dist_nonneg, ← sq_lt_sq₀ dist_nonneg dist_nonneg, e1, e2, e3, e4,
    lt_cancel hs, lt_cancel hs, pos_cancel hs]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by linarith⟩

private lemma preimage_obtuse (A B : Plane) (hAB : A ≠ B) :
    Lof A B ⁻¹' ((· + mid A B) ⁻¹' (carrollRegion A B ∩ {C | IsObtuse A B C})) =
      eqv ⁻¹' TO := by
  have hs := sc_pos A B hAB
  ext p
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := atoms A B p
  simp only [mem_preimage, carrollRegion, TO, mem_inter_iff, mem_ofPred_eq, eqv_apply,
    isObtuse_iff]
  rw [← sq_lt_sq₀ dist_nonneg dist_nonneg, ← sq_lt_sq₀ dist_nonneg dist_nonneg, e1, e2, e3, e4,
    e5, e6, e7, lt_cancel hs, lt_cancel hs, pos_cancel hs, neg_cancel hs, neg_cancel hs,
    neg_cancel hs]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h | h | h⟩
    · nlinarith
    · nlinarith
    · exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by nlinarith, by nlinarith, by linarith⟩, Or.inr (Or.inr (by linarith))⟩

/-- With `AB = 2a`: the area of the figure `ABDCE` is `a² (4π/3 − √3)`. -/
theorem problem58_area_figure (A B : Plane) (hAB : A ≠ B) :
    volume (carrollRegion A B) = ENNReal.ofReal ((dist A B / 2) ^ 2 * (4 * π / 3 - √3)) := by
  rw [vol_transfer A B hAB _ TR (preimage_region A B hAB), vol_TR,
    ← ENNReal.ofReal_mul (sq_nonneg _)]

/-- With `AB = 2a`: the part of the figure where the triangle is obtuse (the semicircle) has
area `π a² / 2`. -/
theorem problem58_area_semicircle (A B : Plane) (hAB : A ≠ B) :
    volume (carrollRegion A B ∩ {C | IsObtuse A B C}) =
      ENNReal.ofReal (π * (dist A B / 2) ^ 2 / 2) := by
  rw [vol_transfer A B hAB _ TO (preimage_obtuse A B hAB), vol_TO,
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  ring_nf

/-- **Problem 58** (Carroll's reading): the chance of an obtuse-angled triangle is
`3 / (8 − 6√3/π)`. -/
theorem problem58 (A B : Plane) (hAB : A ≠ B) :
    obtuseChance A B = 3 / (8 - 6 * √3 / π) := by
  have hs : 0 < (dist A B / 2) ^ 2 := by
    have := dist_pos.2 hAB; positivity
  have hk : 0 < 4 * π / 3 - √3 := by linarith [pi_gt_three, sqrt3_le_two]
  have hk' : 0 < 8 - 6 * √3 / π := by
    rw [sub_pos, div_lt_iff₀ pi_pos]; nlinarith [pi_gt_three, sqrt3_le_two]
  rw [obtuseChance, ProbabilityTheory.cond_apply (isOpen_region A B).measurableSet,
    problem58_area_figure A B hAB, problem58_area_semicircle A B hAB, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (mul_pos hs hk).le,
    ENNReal.toReal_ofReal (by positivity)]
  have h8 : 8 - 6 * √3 / π = 6 * (4 * π / 3 - √3) / π := by field_simp; ring
  rw [h8]
  generalize (dist A B / 2) ^ 2 = a at hs ⊢
  generalize 4 * π / 3 - √3 = k at hk ⊢
  field_simp
  ring

/-- A concrete instance of `problem58`. -/
theorem problem58_nonvacuous : obtuseChance (pt 0 0) (pt 2 0) = 3 / (8 - 6 * √3 / π) := by
  apply problem58
  intro h
  have := congrArg (fun P : Plane => P 0) h
  norm_num at this

end PillowProblems.P58
