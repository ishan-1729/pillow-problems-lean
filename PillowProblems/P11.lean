import PillowProblems.Basic

/-!
# Problem 11 (Trigonometry: Plane)

**Question.** *(dated 31/3/82)*

> A Triangle \(ABC\) has another \(A'B'C'\) inscribed in it, so that \(\angle BA′C′ = \angle CB′A′ = \angle AC′B′ = \theta\); thus making it similar to the first Triangle. Find ratio between homologous sides. And solve for "\(\theta = 90°\)".
>
> [Figure: A geometric diagram of triangle ABC with interior points and a smaller inscribed triangle A'B'C' formed by connecting midpoints or cevians, with labeled intersection point O.]
>
> The Triangles can be proved similar thus:— \[ \begin{array}{c} \angle C′A′B′ + \angle B′A′C = \text{supp. of}~ \theta,\\ \angle B′A′C + \angle A′CB′ = \text{supp. of}~ \theta;\\ \therefore \text{these pairs are equal};~ \therefore \angle C′A′B′ = C. \end{array} \]
>
> Hence \(\angle A′B′C′ = A,~ \text{and}~ \angle B′C′A′ = B.\)
>
> Let \(C′A′ = ka;~\therefore A′B′ = kb,~ \text{and}~ B′C′ = kc\). We have to find \(k\).

**Answer.**

> The required ratio is equal to \[ \frac{\sin A \sin B \sin C}{\sin \theta (1 + \cos A \cos B \cos C) + \cos \theta \sin A \sin B \sin C}. \]
>
> If \(\theta = 90°\), this = \(\dfrac{\sin A \sin B \sin C}{1 + \cos A \cos B \cos C}.\)

*(Carroll's solution: Chapter III, problem 11; text in `data/problems.json`.)*

**Lean reading.** `A B C` is a genuine triangle (`¬ Collinear`), and the inscribed triangle
has `A'` strictly inside side `BC`, `B'` inside `CA`, `C'` inside `AB`, with
`∠ B A' C' = ∠ C B' A' = ∠ A C' B' = θ`. Writing `A, B, C` for the angles `∠ B A C`, `∠ A B C`,
`∠ A C B`, the theorem `problem11` proves `C'A' = k·a`, `A'B' = k·b`, `B'C' = k·c` with
`a = BC, b = CA, c = AB` and `k` Carroll's ratio; in particular the triangles are similar
(SSS), so the similarity asserted in the question is proved, not assumed. Carroll obtains
`A'B' = kb` from the similarity; here instead all three sides are found at once from the
six sine-rule relations in the corner triangles (a linear system in `C'A', A'B', B'C'` whose
determinant is positive), which avoids adding unoriented angles at `A'`. `problem11_right` is the
case `θ = 90°`. No hypothesis on `θ` is needed: it is a geometric angle, and the configuration
forces `0 < θ < π`; `problem11_nonvacuous` exhibits the configuration (equilateral triangle,
medial triangle, `θ = π/3`), and `problem11_right_nonvacuous` exhibits the case `θ = 90°`
(equilateral triangle, `BA' = CB' = AC' = BC/3`).

**Status.** proved
-/

namespace PillowProblems.P11

open EuclideanGeometry
open scoped Real

private lemma sin_angle_nonneg' (P Q R : Plane) : 0 ≤ Real.sin (∠ P Q R) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (angle_nonneg _ _ _) (angle_le_pi _ _ _)

private lemma pos_of_mul_eq {u v w t : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 ≤ w)
    (h : u * v = t * w) : 0 < w := by
  rcases hw.lt_or_eq with hw | hw
  · exact hw
  · rw [← hw, mul_zero] at h; nlinarith [mul_pos hu hv]

/-- Sine rule in the corner triangle `V P Q` (`P` on side `VW`, `Q` on side `UV`, angle `θ` at
`P`): `VP · sin V = PQ · sin (V + θ)`, and `sin (V + θ) ≥ 0`. -/
private lemma corner1 {V P Q W U : Plane} {θ : ℝ} (hP : Sbtw ℝ V P W) (hQ : Sbtw ℝ U Q V)
    (hθ : ∠ V P Q = θ) :
    dist V P * Real.sin (∠ U V W) = dist P Q * Real.sin (∠ U V W + θ) ∧
      0 ≤ Real.sin (∠ U V W + θ) := by
  have hl := law_sin Q V P
  have hray : ∠ Q V P = ∠ U V W := by
    rw [hP.angle_eq_right Q]
    exact hQ.symm.angle_eq_left W
  have hsum := angle_add_angle_add_angle_eq_pi Q hP.ne_left
  have h' : ∠ P Q V = π - (∠ U V W + θ) := by rw [← hθ, ← hray]; linarith
  have hs : Real.sin (∠ U V W + θ) = Real.sin (∠ P Q V) := by rw [h', Real.sin_pi_sub]
  refine ⟨?_, by rw [hs]; exact sin_angle_nonneg' _ _ _⟩
  rw [hray, ← hs] at hl
  linarith [hl]

/-- Sine rule in the corner triangle `V P Q` (`P` on side `UV`, `Q` on side `VW`, angle `θ` at
`Q`): `VP · sin V = PQ · sin θ`. -/
private lemma corner2 {U V W P Q : Plane} {θ : ℝ} (hP : Sbtw ℝ U P V) (hQ : Sbtw ℝ V Q W)
    (hθ : ∠ V Q P = θ) :
    dist V P * Real.sin (∠ U V W) = dist P Q * Real.sin θ := by
  have hl := law_sin Q V P
  have hray : ∠ Q V P = ∠ U V W := by
    rw [hQ.angle_eq_left P, hP.symm.angle_eq_right W, angle_comm]
  rw [hray, angle_comm P Q V, hθ] at hl
  linarith [hl]

/-- Carroll's answer: the ratio of homologous sides of the inscribed triangle `A'B'C'` to the
triangle `ABC` is `sin A sin B sin C / (sin θ (1 + cos A cos B cos C) + cos θ sin A sin B sin C)`. -/
theorem problem11 (A B C A' B' C' : Plane) (θ : ℝ) (hABC : ¬ Collinear ℝ {A, B, C})
    (hA' : Sbtw ℝ B A' C) (hB' : Sbtw ℝ C B' A) (hC' : Sbtw ℝ A C' B)
    (h1 : ∠ B A' C' = θ) (h2 : ∠ C B' A' = θ) (h3 : ∠ A C' B' = θ) :
    let k := Real.sin (∠ B A C) * Real.sin (∠ A B C) * Real.sin (∠ A C B) /
      (Real.sin θ * (1 + Real.cos (∠ B A C) * Real.cos (∠ A B C) * Real.cos (∠ A C B)) +
        Real.cos θ * (Real.sin (∠ B A C) * Real.sin (∠ A B C) * Real.sin (∠ A C B)))
    dist C' A' = k * dist B C ∧ dist A' B' = k * dist C A ∧ dist B' C' = k * dist A B := by
  intro k
  simp only [k]
  -- the corner triangles
  obtain ⟨g1, n1⟩ := corner1 hA' hC' h1
  obtain ⟨g1c, n1c⟩ := corner1 hB' hA' h2
  obtain ⟨g1a, n1a⟩ := corner1 hC' hB' h3
  have g2c := corner2 hA' hB' h2
  have g2a := corner2 hB' hC' h3
  have g2b := corner2 hC' hA' h1
  have sa := hA'.wbtw.dist_add_dist
  have sb := hB'.wbtw.dist_add_dist
  have sc := hC'.wbtw.dist_add_dist
  rw [angle_comm B C A] at g1c n1c g2c
  rw [angle_comm C A B] at g1a n1a g2a
  rw [dist_comm A' C'] at g1
  rw [dist_comm B' A'] at g1c
  rw [dist_comm C' B'] at g1a
  rw [dist_comm A' C] at sa
  rw [dist_comm B' A] at sb
  rw [dist_comm C' B] at sc
  -- the main triangle
  have hBA : B ≠ A := (ne₁₂_of_not_collinear hABC).symm
  have LS := law_sin A B C
  have LS2 := law_sin B C A
  have LS3 := law_sin C A B
  rw [angle_comm C A B] at LS LS3
  rw [angle_comm B C A] at LS2 LS3
  have hsum := angle_add_angle_add_angle_eq_pi C hBA
  rw [angle_comm B C A, angle_comm C A B] at hsum
  have sA : 0 < Real.sin (∠ B A C) := sin_pos_of_not_collinear (by
    rwa [Set.insert_comm])
  have sB : 0 < Real.sin (∠ A B C) := sin_pos_of_not_collinear hABC
  have sC : 0 < Real.sin (∠ A C B) := sin_pos_of_not_collinear (by
    rwa [Set.pair_comm])
  have hcB : Real.cos (∠ A B C) = Real.sin (∠ B A C) * Real.sin (∠ A C B) -
      Real.cos (∠ B A C) * Real.cos (∠ A C B) := by
    rw [show ∠ A B C = π - (∠ B A C + ∠ A C B) by linarith, Real.cos_pi_sub, Real.cos_add]; ring
  have hcC : Real.cos (∠ A C B) = Real.sin (∠ B A C) * Real.sin (∠ A B C) -
      Real.cos (∠ B A C) * Real.cos (∠ A B C) := by
    rw [show ∠ A C B = π - (∠ B A C + ∠ A B C) by linarith, Real.cos_pi_sub, Real.cos_add]; ring
  have hcA : Real.cos (∠ B A C) = Real.sin (∠ A B C) * Real.sin (∠ A C B) -
      Real.cos (∠ A B C) * Real.cos (∠ A C B) := by
    rw [show ∠ B A C = π - (∠ A B C + ∠ A C B) by linarith, Real.cos_pi_sub, Real.cos_add]; ring
  have pA := Real.sin_sq_add_cos_sq (∠ B A C)
  have pB := Real.sin_sq_add_cos_sq (∠ A B C)
  have pC := Real.sin_sq_add_cos_sq (∠ A C B)
  have hTA := Real.sin_add (∠ B A C) θ
  have hTB := Real.sin_add (∠ A B C) θ
  have hTC := Real.sin_add (∠ A C B) θ
  have hθ0 : 0 ≤ Real.sin θ := by rw [← h1]; exact sin_angle_nonneg' _ _ _
  have hp1 : 0 < dist B A' := dist_pos.mpr hA'.left_ne
  have hp2 : 0 < dist C B' := dist_pos.mpr hB'.left_ne
  have hp3 : 0 < dist A C' := dist_pos.mpr hC'.left_ne
  have hq3 : 0 < dist B C' := dist_pos.mpr hC'.right_ne
  have ha : 0 < dist B C := dist_pos.mpr hA'.left_ne_right
  have hx0 : 0 ≤ dist C' A' := dist_nonneg
  have hy0 : 0 ≤ dist A' B' := dist_nonneg
  have hz0 : 0 ≤ dist B' C' := dist_nonneg
  -- abbreviations
  generalize Real.sin (∠ B A C + θ) = TA at *
  generalize Real.sin (∠ A B C + θ) = TB at *
  generalize Real.sin (∠ A C B + θ) = TC at *
  generalize Real.sin (∠ B A C) = SA at *
  generalize Real.sin (∠ A B C) = SB at *
  generalize Real.sin (∠ A C B) = SC at *
  generalize Real.cos (∠ B A C) = CA at *
  generalize Real.cos (∠ A B C) = CB at *
  generalize Real.cos (∠ A C B) = CC at *
  generalize Real.sin θ = sθ at *
  generalize Real.cos θ = cθ at *
  generalize dist B C = a at *
  generalize dist C A = b at *
  generalize dist A B = c at *
  generalize dist C' A' = x at *
  generalize dist A' B' = y at *
  generalize dist B' C' = z at *
  -- positivity of the sines in the corner triangles
  have tB : 0 < TB := pos_of_mul_eq hp1 sB n1 g1
  have tC : 0 < TC := pos_of_mul_eq hp2 sC n1c g1c
  have tA : 0 < TA := pos_of_mul_eq hp3 sA n1a g1a
  have tθ : 0 < sθ := pos_of_mul_eq hq3 sB hθ0 g2b
  -- the linear system for `x = C'A'`, `y = A'B'`, `z = B'C'`
  have E1 : x * TB * SC + y * sθ * SB = a * SB * SC := by
    linear_combination -SC * g1 - SB * g2c + SB * SC * sa
  have E2 : y * TC * SA + z * sθ * SC = b * SC * SA := by
    linear_combination -SA * g1c - SC * g2a + SC * SA * sb
  have E3 : z * TA * SB + x * sθ * SA = c * SA * SB := by
    linear_combination -SB * g1a - SA * g2b + SA * SB * sc
  obtain ⟨D, hD⟩ : ∃ D, D = sθ * (1 + CA * CB * CC) + cθ * (SA * SB * SC) := ⟨_, rfl⟩
  have hD1 : D = SA * SC * TB + sθ * SB ^ 2 := by
    linear_combination hD + sθ * CB * hcB - sθ * pB - SA * SC * hTB
  have hD2 : D = SB * SA * TC + sθ * SC ^ 2 := by
    linear_combination hD + sθ * CC * hcC - sθ * pC - SB * SA * hTC
  have hD3 : D = SC * SB * TA + sθ * SA ^ 2 := by
    linear_combination hD + sθ * CA * hcA - sθ * pA - SC * SB * hTA
  have R1 : (TB * SC) * (x * D - SA * SB * SC * a) + (sθ * SB) * (y * D - SA * SB * SC * b) = 0 := by
    linear_combination D * E1 + a * SB * SC * hD1 + SB ^ 2 * SC * sθ * LS
  have R2 : (TC * SA) * (y * D - SA * SB * SC * b) + (sθ * SC) * (z * D - SA * SB * SC * c) = 0 := by
    linear_combination D * E2 + b * SC * SA * hD2 + SC ^ 2 * SA * sθ * LS2
  have R3 : (TA * SB) * (z * D - SA * SB * SC * c) + (sθ * SA) * (x * D - SA * SB * SC * a) = 0 := by
    linear_combination D * E3 + c * SA * SB * hD3 + SA ^ 2 * SB * sθ * LS3
  have hΔ : 0 < (TB * SC) * (TC * SA) * (TA * SB) + (sθ * SB) * (sθ * SC) * (sθ * SA) := by
    positivity
  have dx : x * D - SA * SB * SC * a = 0 := by
    have : ((TB * SC) * (TC * SA) * (TA * SB) + (sθ * SB) * (sθ * SC) * (sθ * SA)) *
        (x * D - SA * SB * SC * a) = 0 := by
      linear_combination (TC * SA) * (TA * SB) * R1 - (sθ * SB) * (TA * SB) * R2 +
        (sθ * SB) * (sθ * SC) * R3
    exact (mul_eq_zero.mp this).resolve_left hΔ.ne'
  have dy : y * D - SA * SB * SC * b = 0 := by
    have : ((TB * SC) * (TC * SA) * (TA * SB) + (sθ * SB) * (sθ * SC) * (sθ * SA)) *
        (y * D - SA * SB * SC * b) = 0 := by
      linear_combination (TA * SB) * (TB * SC) * R2 - (sθ * SC) * (TB * SC) * R3 +
        (sθ * SC) * (sθ * SA) * R1
    exact (mul_eq_zero.mp this).resolve_left hΔ.ne'
  have dz : z * D - SA * SB * SC * c = 0 := by
    have : ((TB * SC) * (TC * SA) * (TA * SB) + (sθ * SB) * (sθ * SC) * (sθ * SA)) *
        (z * D - SA * SB * SC * c) = 0 := by
      linear_combination (TB * SC) * (TC * SA) * R3 - (sθ * SA) * (TC * SA) * R1 +
        (sθ * SA) * (sθ * SB) * R2
    exact (mul_eq_zero.mp this).resolve_left hΔ.ne'
  have hD0 : D ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at dx
    have : 0 < SA * SB * SC * a := by positivity
    linarith
  rw [← hD]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> linarith

/-- Corollary (`θ = 90°`): the ratio is `sin A sin B sin C / (1 + cos A cos B cos C)`. -/
theorem problem11_right (A B C A' B' C' : Plane) (hABC : ¬ Collinear ℝ {A, B, C})
    (hA' : Sbtw ℝ B A' C) (hB' : Sbtw ℝ C B' A) (hC' : Sbtw ℝ A C' B)
    (h1 : ∠ B A' C' = π / 2) (h2 : ∠ C B' A' = π / 2) (h3 : ∠ A C' B' = π / 2) :
    let k := Real.sin (∠ B A C) * Real.sin (∠ A B C) * Real.sin (∠ A C B) /
      (1 + Real.cos (∠ B A C) * Real.cos (∠ A B C) * Real.cos (∠ A C B))
    dist C' A' = k * dist B C ∧ dist A' B' = k * dist C A ∧ dist B' C' = k * dist A B := by
  have h := problem11 A B C A' B' C' (π / 2) hABC hA' hB' hC' h1 h2 h3
  simp only [Real.sin_pi_div_two, Real.cos_pi_div_two, one_mul, zero_mul, add_zero] at h
  exact h

private lemma norm_eq' (v : Plane) : ‖v‖ = Real.sqrt (v 0 ^ 2 + v 1 ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

private lemma inner_eq' (x y : Plane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

private lemma angle_eq_of (P Q R : Plane) (h1 : (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 = 1)
    (h2 : (R 0 - Q 0) ^ 2 + (R 1 - Q 1) ^ 2 = 1)
    (h3 : (P 0 - Q 0) * (R 0 - Q 0) + (P 1 - Q 1) * (R 1 - Q 1) = 1 / 2) :
    ∠ P Q R = Real.arccos (1 / 2) := by
  unfold EuclideanGeometry.angle InnerProductGeometry.angle
  rw [inner_eq', norm_eq', norm_eq']
  simp only [vsub_eq_sub, PiLp.sub_apply]
  rw [h1, h2, h3, Real.sqrt_one]
  norm_num

private lemma pt_eq_lineMap (P Q : Plane) (t x y : ℝ) (h0 : P 0 + t * (Q 0 - P 0) = x)
    (h1 : P 1 + t * (Q 1 - P 1) = y) : pt x y = AffineMap.lineMap P Q t := by
  ext i
  fin_cases i
  · rw [AffineMap.lineMap_apply]; simp; linarith
  · rw [AffineMap.lineMap_apply]; simp; linarith

/-- The hypotheses of `problem11` can be met: the medial triangle of an equilateral triangle,
with `θ = π/3`. -/
theorem problem11_nonvacuous : ∃ A B C A' B' C' : Plane, ∃ θ : ℝ, ¬ Collinear ℝ {A, B, C} ∧
    Sbtw ℝ B A' C ∧ Sbtw ℝ C B' A ∧ Sbtw ℝ A C' B ∧
    ∠ B A' C' = θ ∧ ∠ C B' A' = θ ∧ ∠ A C' B' = θ := by
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 = 3 :=
    ⟨Real.sqrt 3, by positivity, Real.sq_sqrt (by norm_num)⟩
  refine ⟨pt 0 s, pt (-1) 0, pt 1 0, pt 0 0, pt (1 / 2) (s / 2), pt (-1 / 2) (s / 2),
    Real.arccos (1 / 2), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [collinear_iff_of_mem (p₀ := pt (-1) 0) (by simp)]
    rintro ⟨v, hv⟩
    obtain ⟨r1, hr1⟩ := hv (pt 0 s) (by simp)
    obtain ⟨r2, hr2⟩ := hv (pt 1 0) (by simp)
    have a0 := congrArg (fun P : Plane => P 0) hr1
    have a1 := congrArg (fun P : Plane => P 1) hr1
    have c0 := congrArg (fun P : Plane => P 0) hr2
    have c1 := congrArg (fun P : Plane => P 1) hr2
    simp at a0 a1 c0 c1
    rcases c1 with h | h
    · rw [h] at c0; linarith
    · rw [h, mul_zero] at a1; linarith
  · rw [pt_eq_lineMap (pt (-1) 0) (pt 1 0) (1 / 2) 0 0 (by simp; norm_num) (by simp)]
    refine sbtw_lineMap_iff.mpr ⟨?_, by norm_num, by norm_num⟩
    intro h
    have := congrArg (fun P : Plane => P 0) h
    simp at this
    norm_num at this
  · rw [pt_eq_lineMap (pt 1 0) (pt 0 s) (1 / 2) (1 / 2) (s / 2) (by simp; norm_num)
      (by simp; ring)]
    refine sbtw_lineMap_iff.mpr ⟨?_, by norm_num, by norm_num⟩
    intro h
    have := congrArg (fun P : Plane => P 0) h
    simp at this
  · rw [pt_eq_lineMap (pt 0 s) (pt (-1) 0) (1 / 2) (-1 / 2) (s / 2) (by simp; norm_num)
      (by simp; ring)]
    refine sbtw_lineMap_iff.mpr ⟨?_, by norm_num, by norm_num⟩
    intro h
    have := congrArg (fun P : Plane => P 0) h
    simp at this
  · exact angle_eq_of _ _ _ (by norm_num) (by simp; nlinarith [hs]) (by norm_num)
  · exact angle_eq_of _ _ _ (by simp; nlinarith [hs]) (by simp; nlinarith [hs])
      (by simp; nlinarith [hs])
  · exact angle_eq_of _ _ _ (by simp; nlinarith [hs]) (by norm_num) (by norm_num)

private lemma right_of (P Q R : Plane)
    (h : (P 0 - Q 0) * (R 0 - Q 0) + (P 1 - Q 1) * (R 1 - Q 1) = 0) : ∠ P Q R = π / 2 := by
  apply (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp
  rw [inner_eq']
  simpa only [vsub_eq_sub, PiLp.sub_apply] using h

/-- The hypotheses of `problem11_right` can be met: in the equilateral triangle
`B = (0,0)`, `C = (1,0)`, `A = (1/2, √3/2)`, take `BA' = CB' = AC' = 1/3`. -/
theorem problem11_right_nonvacuous : ∃ A B C A' B' C' : Plane, ¬ Collinear ℝ {A, B, C} ∧
    Sbtw ℝ B A' C ∧ Sbtw ℝ C B' A ∧ Sbtw ℝ A C' B ∧
    ∠ B A' C' = π / 2 ∧ ∠ C B' A' = π / 2 ∧ ∠ A C' B' = π / 2 := by
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 = 3 :=
    ⟨Real.sqrt 3, by positivity, Real.sq_sqrt (by norm_num)⟩
  refine ⟨pt (1 / 2) (s / 2), pt 0 0, pt 1 0, pt (1 / 3) 0, pt (5 / 6) (s / 6),
    pt (1 / 3) (s / 3), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [collinear_iff_of_mem (p₀ := pt 0 0) (by simp)]
    rintro ⟨v, hv⟩
    obtain ⟨r1, hr1⟩ := hv (pt (1 / 2) (s / 2)) (by simp)
    obtain ⟨r2, hr2⟩ := hv (pt 1 0) (by simp)
    have a0 := congrArg (fun P : Plane => P 0) hr1
    have a1 := congrArg (fun P : Plane => P 1) hr1
    have c0 := congrArg (fun P : Plane => P 0) hr2
    have c1 := congrArg (fun P : Plane => P 1) hr2
    simp at a0 a1 c0 c1
    rcases c1 with h | h
    · rw [h] at c0; linarith
    · rw [h, mul_zero] at a1; linarith
  · rw [pt_eq_lineMap (pt 0 0) (pt 1 0) (1 / 3) (1 / 3) 0
      (by simp only [pt_zero]; ring) (by simp only [pt_one]; ring)]
    refine sbtw_lineMap_iff.mpr ⟨?_, by norm_num, by norm_num⟩
    intro h
    have := congrArg (fun P : Plane => P 0) h
    simp at this
  · rw [pt_eq_lineMap (pt 1 0) (pt (1 / 2) (s / 2)) (1 / 3) (5 / 6) (s / 6)
      (by simp only [pt_zero]; ring) (by simp only [pt_one]; ring)]
    refine sbtw_lineMap_iff.mpr ⟨?_, by norm_num, by norm_num⟩
    intro h
    have := congrArg (fun P : Plane => P 0) h
    simp at this
  · rw [pt_eq_lineMap (pt (1 / 2) (s / 2)) (pt 0 0) (1 / 3) (1 / 3) (s / 3)
      (by simp only [pt_zero]; ring) (by simp only [pt_one]; ring)]
    refine sbtw_lineMap_iff.mpr ⟨?_, by norm_num, by norm_num⟩
    intro h
    have := congrArg (fun P : Plane => P 0) h
    simp at this
  · exact right_of _ _ _ (by simp only [pt_zero, pt_one]; ring)
  · exact right_of _ _ _ (by simp only [pt_zero, pt_one]; nlinarith [hs])
  · exact right_of _ _ _ (by simp only [pt_zero, pt_one]; nlinarith [hs])

end PillowProblems.P11
