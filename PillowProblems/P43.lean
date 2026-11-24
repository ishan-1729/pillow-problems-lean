import PillowProblems.Basic

/-!
# Problem 43 (Trigonometry: Plane)

**Question.** *(dated 2/82)*

> From the ends of the base of a given Triangle draw two lines, intersecting, terminated by the sides, and forming an isosceles Triangle at the base, and a Tetragon, equal to it, at the vertex.

*(Carroll's solution: Chapter III, problem 43; text in `data/problems.json`.)*

**Lean reading.** `ABC` is a non-degenerate triangle (`cross A B C ≠ 0`) with base `BC`. The two lines are
`BD` and `CE`, with `D` strictly inside side `AC` and `E` strictly inside side `AB` ("terminated by
the sides"). They meet at `F`, which lies strictly inside both segments `BD` and `CE`. The
isosceles triangle at the base is `FBC` with `FB = FC`. The tetragon `AEFD` is convex, and its
area is taken as `triArea A E F + triArea A F D` (cut along the diagonal `AF`). As in Carroll's
solution, the answer is the base angle `θ = ∠FBC` (this fixes both lines), given through
`cot B = cot ∠ABC` and `cot C = cot ∠ACB`. `problem43` proves that in every such configuration
`cot θ = ½{cot B + cot C + √(5cot²B + 6cot B cot C + 5cot²C)}`. `problem43_exists` proves that
the configuration exists in every triangle, so the hypotheses can be met. Correction: Carroll's
answer has `±`, but only `+` is possible. His quadratic `cot²θ - (cot B + cot C) cot θ -
(cot²B + cot B cot C + cot²C) = 0` has roots whose product is negative, so the `-` root is negative.
That would make `θ` obtuse, but `θ` is less than both base angles `B` and `C`, whose sum is less than `π`.

**Status.** proved (corrected)
-/

namespace PillowProblems.P43

open scoped EuclideanGeometry
open AffineMap

private lemma inner_eq (x y : Plane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

private lemma dist_sq (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma norm_sq' (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, sq_abs]

private lemma lineMap_apply' (A B : Plane) (t : ℝ) (i : Fin 2) :
    (lineMap A B t : Plane) i = A i + t * (B i - A i) := by
  simp [AffineMap.lineMap_apply]; ring

/-- The cotangent of an angle of a triangle: `cot ∠PQR = (QP · QR) / |2·area(PQR)|`. -/
private lemma cot_angle (P Q R : Plane) (h : cross P Q R ≠ 0) :
    Real.cot (∠ P Q R) = inner ℝ (P - Q) (R - Q) / |cross P Q R| := by
  have hPQ : P - Q ≠ 0 := by
    intro h'; apply h
    have e0 : P 0 = Q 0 := by have := congrArg (· 0) h'; simp at this; linarith
    have e1 : P 1 = Q 1 := by have := congrArg (· 1) h'; simp at this; linarith
    unfold cross; rw [e0, e1]; ring
  have hRQ : R - Q ≠ 0 := by
    intro h'; apply h
    have e0 : R 0 = Q 0 := by have := congrArg (· 0) h'; simp at this; linarith
    have e1 : R 1 = Q 1 := by have := congrArg (· 1) h'; simp at this; linarith
    unfold cross; rw [e0, e1]; ring
  have hn : ‖P - Q‖ * ‖R - Q‖ ≠ 0 := mul_ne_zero (norm_ne_zero_iff.2 hPQ) (norm_ne_zero_iff.2 hRQ)
  have hs := InnerProductGeometry.sin_angle_mul_norm_mul_norm (P - Q) (R - Q)
  have e : inner ℝ (P - Q) (P - Q) * inner ℝ (R - Q) (R - Q) -
      inner ℝ (P - Q) (R - Q) * inner ℝ (P - Q) (R - Q) = cross P Q R ^ 2 := by
    simp only [inner_eq, PiLp.sub_apply]; unfold cross; ring
  rw [e, Real.sqrt_sq_eq_abs] at hs
  have hsin : Real.sin (InnerProductGeometry.angle (P - Q) (R - Q)) =
      |cross P Q R| / (‖P - Q‖ * ‖R - Q‖) := eq_div_of_mul_eq hn hs
  show Real.cot (InnerProductGeometry.angle (P -ᵥ Q) (R -ᵥ Q)) = _
  rw [vsub_eq_sub, vsub_eq_sub, Real.cot_eq_cos_div_sin, InnerProductGeometry.cos_angle, hsin]
  have : |cross P Q R| ≠ 0 := abs_ne_zero.2 h
  field_simp

/-- `B - A` and `C - A` are linearly independent when `ABC` is a triangle. -/
private lemma indep (A B C : Plane) (h : cross A B C ≠ 0) (α β : ℝ)
    (h0 : α * (B 0 - A 0) + β * (C 0 - A 0) = 0) (h1 : α * (B 1 - A 1) + β * (C 1 - A 1) = 0) :
    α = 0 ∧ β = 0 := by
  unfold cross at h
  constructor
  · have : α * ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) = 0 := by
      linear_combination (C 1 - A 1) * h0 - (C 0 - A 0) * h1
    exact (mul_eq_zero.1 this).resolve_right h
  · have : β * ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) = 0 := by
      linear_combination (B 0 - A 0) * h1 - (B 1 - A 1) * h0
    exact (mul_eq_zero.1 this).resolve_right h

/-- The algebraic heart of Carroll's solution. With `F = f₁A + f₂B + f₃C` (barycentric),
`I = BA·BC`, `J = CA·CB`, `k = 2·area`, the isosceles condition and `f₁² = f₂ f₃` (the area
condition) give `cot θ = (I + J) / (2 f₁ k)` as the positive root of
`X² - (x + y) X - (x² + xy + y²) = 0`, where `x = cot B = I/k`, `y = cot C = J/k`. -/
private lemma key_alg (f1 f3 I J k : ℝ) (hk : 0 < k) (h1 : 0 < f1) (h1' : f1 < 1)
    (hS : 0 < I + J) (iso : 2 * (f1 * I + f3 * (I + J)) = I + J)
    (quad : f1 ^ 2 = (1 - f1 - f3) * f3) :
    (I + J) / (2 * f1 * k) =
      (I / k + J / k + √(5 * (I / k) ^ 2 + 6 * (I / k) * (J / k) + 5 * (J / k) ^ 2)) / 2 := by
  have T : (I + J) ^ 2 - 2 * f1 * (I + J) ^ 2 - 4 * f1 ^ 2 * (I ^ 2 + I * J + J ^ 2) = 0 := by
    linear_combination (-4 * (I + J) ^ 2) * quad - (2 * f1 * (I - J)) * iso +
      (2 * (f1 * I + f3 * (I + J)) - (I + J)) * iso
  have hpos : 0 < 2 * ((I + J) / (2 * f1 * k)) - I / k - J / k := by
    have : 2 * ((I + J) / (2 * f1 * k)) - I / k - J / k = (I + J) * (1 - f1) / (f1 * k) := by
      field_simp; ring
    rw [this]
    have : 0 < 1 - f1 := by linarith
    positivity
  have hsq : (2 * ((I + J) / (2 * f1 * k)) - I / k - J / k) ^ 2 =
      5 * (I / k) ^ 2 + 6 * (I / k) * (J / k) + 5 * (J / k) ^ 2 := by
    rw [← sub_eq_zero]
    have : (2 * ((I + J) / (2 * f1 * k)) - I / k - J / k) ^ 2 -
        (5 * (I / k) ^ 2 + 6 * (I / k) * (J / k) + 5 * (J / k) ^ 2) =
        ((I + J) ^ 2 - 2 * f1 * (I + J) ^ 2 - 4 * f1 ^ 2 * (I ^ 2 + I * J + J ^ 2)) /
          (f1 ^ 2 * k ^ 2) := by
      field_simp; ring
    rw [this, T, zero_div]
  rw [← hsq, Real.sqrt_sq hpos.le]
  ring

/-- **Problem 43.** In the triangle `ABC` let `BD` and `CE` (`D` on `AC`, `E` on `AB`) meet at `F`,
so that `FB = FC` and the tetragon `AEFD` (made of the triangles `AEF`, `AFD`) has the same area as
the triangle `FBC`. Then the base angle `θ = ∠FBC` of the isosceles triangle is given by
`cot θ = ½ {cot B + cot C + √(5 cot² B + 6 cot B cot C + 5 cot² C)}`. -/
theorem problem43 (A B C D E F : Plane) (hABC : cross A B C ≠ 0)
    (hD : Sbtw ℝ A D C) (hE : Sbtw ℝ A E B) (hFD : Sbtw ℝ B F D) (hFE : Sbtw ℝ C F E)
    (hiso : dist F B = dist F C)
    (harea : triArea A E F + triArea A F D = triArea F B C) :
    Real.cot (∠ F B C) =
      (Real.cot (∠ A B C) + Real.cot (∠ A C B) +
        √(5 * Real.cot (∠ A B C) ^ 2 + 6 * Real.cot (∠ A B C) * Real.cot (∠ A C B) +
          5 * Real.cot (∠ A C B) ^ 2)) / 2 := by
  obtain ⟨⟨s, ⟨s0, s1⟩, rfl⟩, -⟩ := sbtw_iff_mem_image_Ioo_and_ne.1 hD
  obtain ⟨⟨t, ⟨t0, t1⟩, rfl⟩, -⟩ := sbtw_iff_mem_image_Ioo_and_ne.1 hE
  obtain ⟨⟨μ, ⟨μ0, μ1⟩, rfl⟩, -⟩ := sbtw_iff_mem_image_Ioo_and_ne.1 hFD
  obtain ⟨⟨ν, ⟨ν0, ν1⟩, hν⟩, -⟩ := sbtw_iff_mem_image_Ioo_and_ne.1 hFE
  -- `F = f₁ A + f₂ B + f₃ C` with `f₁ = μ(1-s)`, `f₂ = 1-μ`, `f₃ = μ s`; and `F` is on `CE`
  have p0 := congrArg (· 0) hν
  have p1 := congrArg (· 1) hν
  simp only [lineMap_apply'] at p0 p1
  obtain ⟨R1, R2⟩ := indep A B C hABC (ν * t - (1 - μ)) (1 - ν - μ * s)
    (by linear_combination p0) (by linear_combination p1)
  clear p0 p1 hν
  have f1pos : 0 < μ * (1 - s) := mul_pos μ0 (by linarith)
  have f2pos : 0 < s * (1 - μ) := mul_pos s0 (by linarith)
  have f1lt : μ * (1 - s) < 1 := by
    have : μ * (1 - s) < 1 * 1 := mul_lt_mul'' μ1 (by linarith) μ0.le (by linarith)
    linarith
  -- the signed areas
  have cAEF : cross A (lineMap A B t) (lineMap B (lineMap A C s) μ) = t * (μ * s) * cross A B C := by
    unfold cross; simp only [lineMap_apply']; ring
  have cAFD : cross A (lineMap B (lineMap A C s) μ) (lineMap A C s) = s * (1 - μ) * cross A B C := by
    unfold cross; simp only [lineMap_apply']; ring
  have cFBC : cross (lineMap B (lineMap A C s) μ) B C = μ * (1 - s) * cross A B C := by
    unfold cross; simp only [lineMap_apply']; ring
  have cACB : cross A C B = -cross A B C := by unfold cross; ring
  have hk : 0 < |cross A B C| := abs_pos.2 hABC
  -- the area condition: `t f₃ + s f₂ = f₁`, hence `f₁² = f₂ f₃`
  unfold triArea at harea
  rw [cAEF, cAFD, cFBC, abs_mul (t * (μ * s)), abs_mul (s * (1 - μ)), abs_mul (μ * (1 - s)), abs_of_pos (by positivity : 0 < t * (μ * s)),
    abs_of_pos f2pos, abs_of_pos f1pos]
    at harea
  have Ar : μ * (1 - s) = t * (μ * s) + s * (1 - μ) := by
    have := harea
    field_simp at this
    exact mul_right_cancel₀ hk.ne' (by linarith)
  have R1' : ν * t = 1 - μ := by linarith
  have R2' : ν = 1 - μ * s := by linarith
  have quad : (μ * (1 - s)) ^ 2 = (1 - μ * (1 - s) - μ * s) * (μ * s) := by
    linear_combination μ * ν * Ar - μ * (μ * (1 - s) - s * (1 - μ)) * R2' + μ * μ * s * R1'
  -- the isosceles condition
  have hiso2 : dist (lineMap B (lineMap A C s) μ : Plane) B ^ 2 =
      dist (lineMap B (lineMap A C s) μ : Plane) C ^ 2 := by rw [hiso]
  rw [dist_sq, dist_sq] at hiso2
  simp only [lineMap_apply'] at hiso2
  have eF2 : 2 * inner ℝ (lineMap B (lineMap A C s) μ - B) (C - B) =
      inner ℝ (A - B) (C - B) + inner ℝ (A - C) (B - C) := by
    simp only [inner_eq, PiLp.sub_apply, lineMap_apply']
    linear_combination hiso2
  clear hiso2 hiso
  have eF3 : inner ℝ (lineMap B (lineMap A C s) μ - B) (C - B) =
      μ * (1 - s) * inner ℝ (A - B) (C - B) +
        μ * s * (inner ℝ (A - B) (C - B) + inner ℝ (A - C) (B - C)) := by
    simp only [inner_eq, PiLp.sub_apply, lineMap_apply']
    ring
  have iso : 2 * (μ * (1 - s) * inner ℝ (A - B) (C - B) +
      μ * s * (inner ℝ (A - B) (C - B) + inner ℝ (A - C) (B - C))) =
      inner ℝ (A - B) (C - B) + inner ℝ (A - C) (B - C) := by
    rw [← eF3, eF2]
  have hS : 0 < inner ℝ (A - B) (C - B) + inner ℝ (A - C) (B - C) := by
    have hBC : B ≠ C := by rintro rfl; apply hABC; unfold cross; ring
    have := dist_pos.2 hBC
    have e : inner ℝ (A - B) (C - B) + inner ℝ (A - C) (B - C) = dist B C ^ 2 := by
      rw [dist_sq]; simp only [inner_eq, PiLp.sub_apply]; ring
    rw [e]; positivity
  -- the three cotangents
  have hFBC : cross (lineMap B (lineMap A C s) μ) B C ≠ 0 := by
    rw [cFBC]; exact mul_ne_zero f1pos.ne' hABC
  have eF : inner ℝ (lineMap B (lineMap A C s) μ - B) (C - B) =
      (inner ℝ (A - B) (C - B) + inner ℝ (A - C) (B - C)) / 2 := by
    linarith
  rw [cot_angle _ _ _ hFBC, cot_angle _ _ _ hABC, cot_angle _ _ _ (by rw [cACB]; exact neg_ne_zero.2 hABC),
    cFBC, cACB, abs_neg, eF, abs_mul, abs_of_pos f1pos]
  rw [div_div, show 2 * (μ * (1 - s) * |cross A B C|) = 2 * (μ * (1 - s)) * |cross A B C| by ring]
  exact key_alg (μ * (1 - s)) (μ * s) (inner ℝ (A - B) (C - B)) (inner ℝ (A - C) (B - C))
    |cross A B C| hk f1pos f1lt hS iso quad

/-- **Problem 43 (the construction is possible).** In every triangle the two lines can be drawn:
there are `D` on `AC`, `E` on `AB`, `F = BD ∩ CE` with `FB = FC` and `AEFD` equal in area
to `FBC`. -/
theorem problem43_exists (A B C : Plane) (hABC : cross A B C ≠ 0) :
    ∃ D E F : Plane, Sbtw ℝ A D C ∧ Sbtw ℝ A E B ∧ Sbtw ℝ B F D ∧ Sbtw ℝ C F E ∧
      dist F B = dist F C ∧ triArea A E F + triArea A F D = triArea F B C := by
  -- `F(r) = N(r) / w(r)` with `N(r) = r(1-r) A + (1-r)² B + r² C`, `w(r) = 1 - r + r²`;
  -- `φ(r) = w² (FB² - FC²)` changes sign on `[0, 1]`
  let φ : ℝ → ℝ := fun r =>
    (r * (1 - r) * A 0 + (1 - r) ^ 2 * B 0 + r ^ 2 * C 0 - (1 - r + r ^ 2) * B 0) ^ 2 +
    (r * (1 - r) * A 1 + (1 - r) ^ 2 * B 1 + r ^ 2 * C 1 - (1 - r + r ^ 2) * B 1) ^ 2 -
    (r * (1 - r) * A 0 + (1 - r) ^ 2 * B 0 + r ^ 2 * C 0 - (1 - r + r ^ 2) * C 0) ^ 2 -
    (r * (1 - r) * A 1 + (1 - r) ^ 2 * B 1 + r ^ 2 * C 1 - (1 - r + r ^ 2) * C 1) ^ 2
  have hc : Continuous φ := by fun_prop
  have hBC : B ≠ C := by rintro rfl; apply hABC; unfold cross; ring
  have hd : 0 < (B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2 := by rw [← dist_sq]; exact pow_pos (dist_pos.2 hBC) 2
  have h0 : φ 0 < 0 := by
    have : φ 0 = -((B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2) := by simp only [φ]; ring
    linarith
  have h1 : 0 < φ 1 := by
    have : φ 1 = (B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2 := by simp only [φ]; ring
    linarith
  obtain ⟨s, ⟨s0, s1⟩, hs⟩ := intermediate_value_Ioo zero_le_one hc.continuousOn ⟨h0, h1⟩
  have hw : 0 < 1 - s + s ^ 2 := by nlinarith [sq_nonneg s]
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = s / (1 - s + s ^ 2) := ⟨_, rfl⟩
  have hμs : μ * (1 - s + s ^ 2) = s := by rw [hμ]; field_simp
  have μ0 : 0 < μ := by rw [hμ]; positivity
  have μ1 : μ < 1 := by
    rw [hμ, div_lt_one hw]; nlinarith [sq_pos_of_pos (by linarith : (0 : ℝ) < 1 - s)]
  have hF : (lineMap B (lineMap A C s) μ : Plane) =
      lineMap C (lineMap A B (1 - s)) ((1 - s) / (1 - s + s ^ 2)) := by
    ext i; fin_cases i <;> simp only [lineMap_apply'] <;> rw [hμ] <;> field_simp <;> ring
  refine ⟨lineMap A C s, lineMap A B (1 - s), lineMap B (lineMap A C s) μ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine sbtw_lineMap_iff.2 ⟨?_, s0, s1⟩
    rintro rfl; apply hABC; unfold cross; ring
  · refine sbtw_lineMap_iff.2 ⟨?_, by linarith, by linarith⟩
    rintro rfl; apply hABC; unfold cross; ring
  · refine sbtw_lineMap_iff.2 ⟨?_, μ0, μ1⟩
    intro h; apply hABC; rw [h]; unfold cross; simp only [lineMap_apply']; ring
  · rw [hF]
    refine sbtw_lineMap_iff.2 ⟨?_, by positivity, ?_⟩
    · intro h; apply hABC; rw [h]; unfold cross; simp only [lineMap_apply']; ring
    · rw [div_lt_one hw]; nlinarith [sq_pos_of_pos s0]
  · rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, dist_sq, dist_sq, ← sub_eq_zero]
    simp only [lineMap_apply']
    have e : ∀ i : Fin 2, B i + μ * (A i + s * (C i - A i) - B i) =
        (s * (1 - s) * A i + (1 - s) ^ 2 * B i + s ^ 2 * C i) / (1 - s + s ^ 2) := by
      intro i; rw [hμ]; field_simp; ring
    rw [e 0, e 1]
    have : φ s / (1 - s + s ^ 2) ^ 2 = 0 := by rw [hs, zero_div]
    rw [← this]; simp only [φ]; field_simp; ring
  · have cAEF : cross A (lineMap A B (1 - s)) (lineMap B (lineMap A C s) μ) =
        (1 - s) * (μ * s) * cross A B C := by
      unfold cross; simp only [lineMap_apply']; ring
    have cAFD : cross A (lineMap B (lineMap A C s) μ) (lineMap A C s) =
        s * (1 - μ) * cross A B C := by
      unfold cross; simp only [lineMap_apply']; ring
    have cFBC : cross (lineMap B (lineMap A C s) μ) B C = μ * (1 - s) * cross A B C := by
      unfold cross; simp only [lineMap_apply']; ring
    unfold triArea
    rw [cAEF, cAFD, cFBC, abs_mul ((1 - s) * (μ * s)), abs_mul (s * (1 - μ)), abs_mul (μ * (1 - s)),
      abs_of_pos (by have : 0 < 1 - s := by linarith
                     positivity : 0 < (1 - s) * (μ * s)),
      abs_of_pos (mul_pos s0 (by linarith) : 0 < s * (1 - μ)),
      abs_of_pos (mul_pos μ0 (by linarith) : 0 < μ * (1 - s))]
    linear_combination (-|cross A B C| / 2) * hμs

end PillowProblems.P43
