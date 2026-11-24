import PillowProblems.Basic

/-!
# Problem 7 (Trigonometry: Plane)

**Question.** *(dated 4 or 5/89)*

> Given 2 adjacent sides, and the included angle, of a Tetragon; and that the angles, at the other ends of these 2 sides, are right: find (1) remaining sides, (2) area.

**Answer.**

> [Figure: A geometric diagram of triangle ABD with extended points C and E, connected by dashed lines.]
>
> Let \(AB\), \(AD\) be given sides, and \(B\), \(D\) the right \(\angle\)s; and let \(AB = b\), \(AD = d\).
>
> (1) \(\quad BC = \dfrac{d-b\cos A}{\sin A};\quad CD = \dfrac{b-d\cos A}{\sin A};\)
>
> (2) \(\quad\text{area} = \dfrac{2bd-(b^{2}+d^{2})\cos A}{2\sin A}\).

*(Carroll's solution: Chapter III, problem 7; text in `data/problems.json`.)*

**Lean reading.** The Tetragon is four points `A B C D` of the `Plane`, taken in order;
the given sides are `b = AB`, `d = AD` with included angle `α = ∠ B A D`, and the angles at `B`
and `D` are right: `∠ A B C = π/2`, `∠ A D C = π/2`. Carroll tacitly takes the Tetragon to be
convex (as in his figure); this is the hypothesis that its diagonals `AC`, `BD` meet, and it is
needed. The right angles fix `C` (the meet of the perpendiculars to `AB` at `B` and to `AD`
at `D`), and when `d < b cos α` or `b < d cos α` the side `CD` (resp. `BC`) crosses `AB`
(resp. `AD`), so `ABCD` is a crossed, not a simple, quadrilateral and the remaining sides are
`|d - b cos α| / sin α`, `|b - d cos α| / sin α`; for a simple Tetragon with these angles the
convexity hypothesis is automatic. We also assume `A ≠ B`, `A ≠ D` and `sin α ≠ 0` (the given sides are
genuine and not collinear), which his formulas need. The area of the Tetragon is the shoelace
area `quadArea`, which is the usual area for a convex (indeed any simple) quadrilateral; under
the hypotheses it equals Carroll's `½ (AB·BC + AD·DC)`. The theorem proves Carroll's formulas
for `BC`, `CD` and the area, which determine them from the data; `problem7_nonvacuous` (the
unit square) shows that the hypotheses are consistent.

**Status.** proved
-/

namespace PillowProblems.P07

open EuclideanGeometry
open scoped Real

/-- The area of the quadrilateral `ABCD` with vertices in this order (shoelace formula; it is
the usual area when `ABCD` is simple, e.g. convex). -/
noncomputable def quadArea (A B C D : Plane) : ℝ := |cross A B C + cross A C D| / 2

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

/-- The algebraic core, with `A` at the origin: `u = B - A`, `w = D - A`, `x = C - A`. -/
private lemma core (u0 u1 w0 w1 x0 x1 t r : ℝ) (hcr : u0 * w1 - u1 * w0 ≠ 0)
    (h1 : u0 * x0 + u1 * x1 = u0 ^ 2 + u1 ^ 2) (h2 : w0 * x0 + w1 * x1 = w0 ^ 2 + w1 ^ 2)
    (ht : 0 ≤ t) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hP0 : t * x0 = (1 - r) * u0 + r * w0) (hP1 : t * x1 = (1 - r) * u1 + r * w1) :
    0 ≤ (u0 ^ 2 + u1 ^ 2) - (u0 * w0 + u1 * w1) ∧ 0 ≤ (w0 ^ 2 + w1 ^ 2) - (u0 * w0 + u1 * w1) ∧
    ((x0 - u0) ^ 2 + (x1 - u1) ^ 2) * (u0 * w1 - u1 * w0) ^ 2 =
      (u0 ^ 2 + u1 ^ 2) * ((w0 ^ 2 + w1 ^ 2) - (u0 * w0 + u1 * w1)) ^ 2 ∧
    ((x0 - w0) ^ 2 + (x1 - w1) ^ 2) * (u0 * w1 - u1 * w0) ^ 2 =
      (w0 ^ 2 + w1 ^ 2) * ((u0 ^ 2 + u1 ^ 2) - (u0 * w0 + u1 * w1)) ^ 2 ∧
    ((u0 * x1 - x0 * u1) + (x0 * w1 - w0 * x1)) * (u0 * w1 - u1 * w0) =
      2 * (u0 ^ 2 + u1 ^ 2) * (w0 ^ 2 + w1 ^ 2) -
        ((u0 ^ 2 + u1 ^ 2) + (w0 ^ 2 + w1 ^ 2)) * (u0 * w0 + u1 * w1) := by
  set cr := u0 * w1 - u1 * w0 with hcr_def
  set U := u0 ^ 2 + u1 ^ 2 with hU
  set W := w0 ^ 2 + w1 ^ 2 with hW
  set R := u0 * w0 + u1 * w1 with hR
  have hU0 : 0 < U := by
    rcases (eq_or_ne u0 0) with h | h
    · have : u1 ≠ 0 := by rintro rfl; apply hcr; simp [hcr_def, h]
      positivity
    · positivity
  have hW0 : 0 < W := by
    rcases (eq_or_ne w0 0) with h | h
    · have : w1 ≠ 0 := by rintro rfl; apply hcr; simp [hcr_def, h]
      positivity
    · positivity
  -- the two "cross" coordinates of `x` in the basis `u, w`
  have ea : t * (x0 * w1 - w0 * x1) = (1 - r) * cr := by
    rw [hcr_def]; linear_combination w1 * hP0 - w0 * hP1
  have eb : t * (u0 * x1 - x0 * u1) = r * cr := by
    rw [hcr_def]; linear_combination u0 * hP1 - u1 * hP0
  have fa : (x0 * w1 - w0 * x1) * cr = W * (U - R) := by
    rw [hcr_def, hW, hU, hR]; linear_combination (w0 ^ 2 + w1 ^ 2) * h1 - (u0 * w0 + u1 * w1) * h2
  have fb : (u0 * x1 - x0 * u1) * cr = U * (W - R) := by
    rw [hcr_def, hW, hU, hR]; linear_combination (u0 ^ 2 + u1 ^ 2) * h2 - (u0 * w0 + u1 * w1) * h1
  have htpos : 0 < t := by
    rcases ht.lt_or_eq with h | h
    · exact h
    · exfalso
      subst h
      have h1r : (1 - r) * cr = 0 := by linarith
      have hr : r * cr = 0 := by linarith
      rcases mul_eq_zero.mp h1r with h' | h'
      · rcases mul_eq_zero.mp hr with h'' | h''
        · linarith
        · exact hcr h''
      · exact hcr h'
  have hUR : 0 ≤ U - R := by
    have h3 : t * (W * (U - R)) = (1 - r) * cr ^ 2 := by rw [← fa, ← mul_assoc, ea]; ring
    have h4 : 0 ≤ (1 - r) * cr ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    by_contra hneg
    push Not at hneg
    have : t * (W * (U - R)) < 0 := mul_neg_of_pos_of_neg htpos (mul_neg_of_pos_of_neg hW0 hneg)
    linarith
  have hWR : 0 ≤ W - R := by
    have h3 : t * (U * (W - R)) = r * cr ^ 2 := by rw [← fb, ← mul_assoc, eb]; ring
    have h4 : 0 ≤ r * cr ^ 2 := mul_nonneg hr0 (sq_nonneg _)
    by_contra hneg
    push Not at hneg
    have : t * (U * (W - R)) < 0 := mul_neg_of_pos_of_neg htpos (mul_neg_of_pos_of_neg hU0 hneg)
    linarith
  have e1 : ((x0 - u0) ^ 2 + (x1 - u1) ^ 2) * U = (u0 * x1 - x0 * u1) ^ 2 := by
    rw [hU]; linear_combination (u0 * x0 + u1 * x1 - (u0 ^ 2 + u1 ^ 2)) * h1
  have e2 : ((x0 - w0) ^ 2 + (x1 - w1) ^ 2) * W = (x0 * w1 - w0 * x1) ^ 2 := by
    rw [hW]; linear_combination (w0 * x0 + w1 * x1 - (w0 ^ 2 + w1 ^ 2)) * h2
  refine ⟨hUR, hWR, ?_, ?_, ?_⟩
  · apply mul_right_cancel₀ hU0.ne'
    linear_combination cr ^ 2 * e1 + ((u0 * x1 - x0 * u1) * cr + U * (W - R)) * fb
  · apply mul_right_cancel₀ hW0.ne'
    linear_combination cr ^ 2 * e2 + ((x0 * w1 - w0 * x1) * cr + W * (U - R)) * fa
  · linear_combination fa + fb

/-- Carroll's answer: with `AB = b`, `AD = d`, included angle `α = ∠BAD`, and right angles at
`B` and `D` in the convex Tetragon `ABCD`,
`BC = (d - b cos α)/sin α`, `CD = (b - d cos α)/sin α`, and
area `= (2bd - (b² + d²) cos α)/(2 sin α)`. -/
theorem problem7 (A B C D : Plane) (hAB : A ≠ B) (hAD : A ≠ D) (hsin : Real.sin (∠ B A D) ≠ 0)
    (hB : ∠ A B C = π / 2) (hD : ∠ A D C = π / 2)
    (hconvex : ∃ P, Wbtw ℝ A P C ∧ Wbtw ℝ B P D) :
    dist B C = (dist A D - dist A B * Real.cos (∠ B A D)) / Real.sin (∠ B A D) ∧
    dist C D = (dist A B - dist A D * Real.cos (∠ B A D)) / Real.sin (∠ B A D) ∧
    quadArea A B C D = (2 * dist A B * dist A D - (dist A B ^ 2 + dist A D ^ 2) *
      Real.cos (∠ B A D)) / (2 * Real.sin (∠ B A D)) := by
  obtain ⟨P, ⟨t, ⟨ht0, -⟩, hPt⟩, ⟨r, ⟨hr0, hr1⟩, hPr⟩⟩ := hconvex
  have hP0 := congrArg (fun Q : Plane => Q 0) (hPt.trans hPr.symm)
  have hP1 := congrArg (fun Q : Plane => Q 1) (hPt.trans hPr.symm)
  simp only [lineMap_apply'] at hP0 hP1
  have hBi := (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mpr hB
  have hDi := (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mpr hD
  rw [inner_eq'] at hBi hDi
  simp only [vsub_eq_sub, PiLp.sub_apply] at hBi hDi
  have hb : 0 < dist A B := dist_pos.mpr hAB
  have hd : 0 < dist A D := dist_pos.mpr hAD
  have hb2 : dist A B ^ 2 = (B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2 := by rw [dist_sq']; ring
  have hd2 : dist A D ^ 2 = (D 0 - A 0) ^ 2 + (D 1 - A 1) ^ 2 := by rw [dist_sq']; ring
  have hnB : ‖B -ᵥ A‖ = dist A B := by rw [dist_comm, dist_eq_norm_vsub]
  have hnD : ‖D -ᵥ A‖ = dist A D := by rw [dist_comm, dist_eq_norm_vsub]
  have hK : Real.cos (∠ B A D) * (dist A B * dist A D) =
      (B 0 - A 0) * (D 0 - A 0) + (B 1 - A 1) * (D 1 - A 1) := by
    have := InnerProductGeometry.cos_angle_mul_norm_mul_norm (B -ᵥ A) (D -ᵥ A)
    rw [hnB, hnD] at this
    rw [EuclideanGeometry.angle, this, inner_eq']
    simp only [vsub_eq_sub, PiLp.sub_apply]
  have hS : Real.sin (∠ B A D) * (dist A B * dist A D) =
      |(B 0 - A 0) * (D 1 - A 1) - (B 1 - A 1) * (D 0 - A 0)| := by
    have := InnerProductGeometry.sin_angle_mul_norm_mul_norm (B -ᵥ A) (D -ᵥ A)
    rw [hnB, hnD] at this
    rw [EuclideanGeometry.angle, this, ← Real.sqrt_sq_eq_abs]
    congr 1
    rw [inner_eq', inner_eq', inner_eq']
    simp only [vsub_eq_sub, PiLp.sub_apply]
    ring
  have hcr : (B 0 - A 0) * (D 1 - A 1) - (B 1 - A 1) * (D 0 - A 0) ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hS
    exact hsin ((mul_eq_zero.mp hS).resolve_right (mul_pos hb hd).ne')
  obtain ⟨hUR, hWR, hBC, hCD, hArea⟩ := core (B 0 - A 0) (B 1 - A 1) (D 0 - A 0) (D 1 - A 1)
    (C 0 - A 0) (C 1 - A 1) t r hcr (by linear_combination -hBi) (by linear_combination -hDi)
    ht0 hr0 hr1 (by linear_combination hP0) (by linear_combination hP1)
  simp only [← hb2, ← hd2] at hUR hWR hBC hCD hArea
  have hbd : dist A B * dist A D ≠ 0 := (mul_pos hb hd).ne'
  refine ⟨?_, ?_, ?_⟩
  · have key : dist B C * |(B 0 - A 0) * (D 1 - A 1) - (B 1 - A 1) * (D 0 - A 0)| =
        dist A B * (dist A D ^ 2 - ((B 0 - A 0) * (D 0 - A 0) + (B 1 - A 1) * (D 1 - A 1))) := by
      refine (pow_left_inj₀ (by positivity) (mul_nonneg hb.le hWR) two_ne_zero).mp ?_
      rw [mul_pow, mul_pow, sq_abs, hb2, dist_sq' B C]
      rw [hb2] at hBC
      linear_combination hBC
    rw [eq_div_iff hsin]
    apply mul_right_cancel₀ hbd
    linear_combination dist B C * hS + key + dist A B * hK
  · have key : dist C D * |(B 0 - A 0) * (D 1 - A 1) - (B 1 - A 1) * (D 0 - A 0)| =
        dist A D * (dist A B ^ 2 - ((B 0 - A 0) * (D 0 - A 0) + (B 1 - A 1) * (D 1 - A 1))) := by
      refine (pow_left_inj₀ (by positivity) (mul_nonneg hd.le hUR) two_ne_zero).mp ?_
      rw [mul_pow, mul_pow, sq_abs, hd2, dist_sq' C D]
      rw [hd2] at hCD
      linear_combination hCD
    rw [eq_div_iff hsin]
    apply mul_right_cancel₀ hbd
    linear_combination dist C D * hS + key + dist A D * hK
  · have hX : 0 ≤ 2 * dist A B ^ 2 * dist A D ^ 2 - (dist A B ^ 2 + dist A D ^ 2) *
        ((B 0 - A 0) * (D 0 - A 0) + (B 1 - A 1) * (D 1 - A 1)) := by
      have e : 2 * dist A B ^ 2 * dist A D ^ 2 - (dist A B ^ 2 + dist A D ^ 2) *
          ((B 0 - A 0) * (D 0 - A 0) + (B 1 - A 1) * (D 1 - A 1)) =
          dist A B ^ 2 * (dist A D ^ 2 - ((B 0 - A 0) * (D 0 - A 0) + (B 1 - A 1) * (D 1 - A 1))) +
          dist A D ^ 2 * (dist A B ^ 2 - ((B 0 - A 0) * (D 0 - A 0) + (B 1 - A 1) * (D 1 - A 1))) := by
        ring
      rw [e]
      exact add_nonneg (mul_nonneg (sq_nonneg _) hWR) (mul_nonneg (sq_nonneg _) hUR)
    have key : |cross A B C + cross A C D| *
        |(B 0 - A 0) * (D 1 - A 1) - (B 1 - A 1) * (D 0 - A 0)| =
        2 * dist A B ^ 2 * dist A D ^ 2 - (dist A B ^ 2 + dist A D ^ 2) *
        ((B 0 - A 0) * (D 0 - A 0) + (B 1 - A 1) * (D 1 - A 1)) := by
      have e : (cross A B C + cross A C D) *
          ((B 0 - A 0) * (D 1 - A 1) - (B 1 - A 1) * (D 0 - A 0)) =
          2 * dist A B ^ 2 * dist A D ^ 2 - (dist A B ^ 2 + dist A D ^ 2) *
          ((B 0 - A 0) * (D 0 - A 0) + (B 1 - A 1) * (D 1 - A 1)) := by
        unfold cross
        linear_combination hArea
      rw [← abs_mul, e, abs_of_nonneg hX]
    unfold quadArea
    rw [eq_div_iff (mul_ne_zero two_ne_zero hsin)]
    apply mul_right_cancel₀ hbd
    linear_combination |cross A B C + cross A C D| * hS + key +
      (dist A B ^ 2 + dist A D ^ 2) * hK

private lemma pt_eq_lineMap (P Q : Plane) (t x y : ℝ) (h0 : P 0 + t * (Q 0 - P 0) = x)
    (h1 : P 1 + t * (Q 1 - P 1) = y) : AffineMap.lineMap P Q t = pt x y := by
  ext i
  fin_cases i
  · rw [AffineMap.lineMap_apply]; simp; linarith
  · rw [AffineMap.lineMap_apply]; simp; linarith

/-- The hypotheses of `problem7` can be met (the unit square). -/
theorem problem7_nonvacuous : ∃ A B C D : Plane, A ≠ B ∧ A ≠ D ∧ Real.sin (∠ B A D) ≠ 0 ∧
    ∠ A B C = π / 2 ∧ ∠ A D C = π / 2 ∧ ∃ P, Wbtw ℝ A P C ∧ Wbtw ℝ B P D := by
  have rt : ∀ X Y Z : Plane, inner ℝ (X -ᵥ Y) (Z -ᵥ Y) = 0 → ∠ X Y Z = π / 2 :=
    fun X Y Z h => (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp h
  have n1 : pt 0 0 ≠ pt 1 0 := by
    intro h; have := congrArg (fun P : Plane => P 0) h; norm_num at this
  have n2 : pt 0 0 ≠ pt 0 1 := by
    intro h; have := congrArg (fun P : Plane => P 1) h; norm_num at this
  refine ⟨pt 0 0, pt 1 0, pt 1 1, pt 0 1, n1, n2, ?_, rt _ _ _ (by rw [inner_eq']; norm_num),
    rt _ _ _ (by rw [inner_eq']; norm_num), pt (1 / 2) (1 / 2),
    ⟨1 / 2, ⟨by norm_num, by norm_num⟩, pt_eq_lineMap _ _ _ _ _ (by norm_num) (by norm_num)⟩,
    ⟨1 / 2, ⟨by norm_num, by norm_num⟩, pt_eq_lineMap _ _ _ _ _ (by norm_num) (by norm_num)⟩⟩
  rw [rt _ _ _ (by rw [inner_eq']; norm_num), Real.sin_pi_div_two]
  norm_num

end PillowProblems.P07
