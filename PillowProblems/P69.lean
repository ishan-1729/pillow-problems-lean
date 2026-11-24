import PillowProblems.Basic

/-!
# Problem 69 (Trigonometry: Plane)

**Question.** *(dated 8/89)*

> If, from each of the angles of a given Triangle \(ABC\), taken cyclically, a certain proper fraction of it be cut off, the arithmetical values of the 3 fractions being represented by '\(k\), \(l\), \(m\)'; and if it be given that the Triangle, formed by the lines so drawn, is similar to the given one, the angle, formed by the lines drawn from \(B\) and \(C\), being equal to \(A\), and so on: find \(k\), \(l\), \(m\), as similar functions of a single variable. Also find the ratio which each side of the second Triangle bears to the corresponding side of the first.

**Answer.**

> (1) \(k = \dfrac{\theta-B}{A}\); \(l = \dfrac{\theta-C}{B}\); \(m = \dfrac{\theta-A}{C}\).
>
> (2) Calling new Triangle '\(A'B'C'\)', \[ \frac{a'}{a} = \frac{b'}{b} = \frac{c'}{c} = 2\cos{\theta}. \]

*(Carroll's solution: Chapter III, problem 69; text in `data/problems.json`.)*

**Lean reading.** `ABC` is a genuine triangle in the plane (`cross A B C ≠ 0`); Carroll's `A`,
`B`, `C` are the angles `∠BAC`, `∠ABC`, `∠ACB`. "Taken cyclically" is read as in Carroll's
solution: the line `AD` cuts off `∠BAD = k·A` next to `AB`, `BE` cuts off `∠CBE = l·B` next to
`BC`, `CF` cuts off `∠ACF = m·C` next to `CA`, with `D, E, F` strictly inside the opposite sides
(a line from a vertex cutting off a proper part of the angle meets the opposite side internally)
and `0 < k, l, m < 1` ("proper fraction"). The inner triangle has `A' = BE ∩ CF`, `B' = CF ∩ AD`,
`C' = AD ∩ BE` (stated as membership in the lines), and similarity with the stated correspondence
is `∠B'A'C' = A`, `∠A'B'C' = B`, `∠A'C'B' = C`; no nondegeneracy of `A'B'C'` is assumed (the proof
shows the three lines cannot be concurrent). The single variable is `θ`, proved to be `∠ADC`
(Carroll's § 2). Carroll's ratio `2 cos θ` is wrong in sign when `θ > 90°`, which the hypotheses
allow (e.g. an equilateral triangle with `θ = 100°`, `k = l = m = 2/3`): then `B'` lies beyond `C'`
from `A` (Carroll's `B'C' = AC' - AB'` is negative), since a length cannot be
negative. The true ratio of corresponding sides is `|2 cos θ|`, which agrees with
Carroll's for `θ < 90°`; this is what `problem69` proves. `problem69_converse` proves Carroll's
§ 2–3 converse: every `θ` with `max(A,B,C) < θ < π - max(A,B,C)` and `θ ≠ 90°` does give proper
fractions `k, l, m` and a configuration with all the hypotheses of `problem69`. `θ = 90°`, which
Carroll's limits allow, must be excluded: the three lines are then the altitudes, which are
concurrent, so no triangle is formed (Carroll's ratio `2 cos 90° = 0` reflects this).
`problem69_nonvacuous` exhibits an explicit configuration with rational coordinates.

**Status.** proved (corrected)
-/

namespace PillowProblems.P69

open EuclideanGeometry Real

private lemma inner_plane (x y : Plane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

private lemma ext_plane {P Q : Plane} (h0 : P 0 = Q 0) (h1 : P 1 = Q 1) : P = Q := by
  ext i; fin_cases i <;> simp [h0, h1]

private lemma lm_apply (P Q : Plane) (r : ℝ) (i : Fin 2) :
    AffineMap.lineMap P Q r i = P i + r * (Q i - P i) := by
  simp [AffineMap.lineMap_apply]; ring

/-- `sin ∠PQR > 0` for a nondegenerate triangle. -/
private lemma sin_angle_pos (P Q R : Plane) (h : cross Q P R ≠ 0) : 0 < Real.sin (∠ P Q R) := by
  have hx : P - Q ≠ 0 := by
    intro hx; apply h
    have h0 : P 0 = Q 0 := by have := congrFun (congrArg (⇑) hx) 0; simpa [sub_eq_zero] using this
    have h1 : P 1 = Q 1 := by have := congrFun (congrArg (⇑) hx) 1; simpa [sub_eq_zero] using this
    simp [cross, h0, h1]
  have hy : R - Q ≠ 0 := by
    intro hy; apply h
    have h0 : R 0 = Q 0 := by have := congrFun (congrArg (⇑) hy) 0; simpa [sub_eq_zero] using this
    have h1 : R 1 = Q 1 := by have := congrFun (congrArg (⇑) hy) 1; simpa [sub_eq_zero] using this
    simp [cross, h0, h1]
  have hN : 0 < ‖P - Q‖ * ‖R - Q‖ := mul_pos (norm_pos_iff.2 hx) (norm_pos_iff.2 hy)
  have hs := InnerProductGeometry.sin_angle_mul_norm_mul_norm (P - Q) (R - Q)
  have hsq : inner ℝ (P - Q) (P - Q) * inner ℝ (R - Q) (R - Q) -
      inner ℝ (P - Q) (R - Q) * inner ℝ (P - Q) (R - Q) = (cross Q P R) ^ 2 := by
    simp only [inner_plane, cross, PiLp.sub_apply]; ring
  rw [hsq, Real.sqrt_sq_eq_abs] at hs
  have hang : ∠ P Q R = InnerProductGeometry.angle (P - Q) (R - Q) := rfl
  have habs : 0 < |cross Q P R| := abs_pos.2 h
  rw [hang]; by_contra hle; push Not at hle
  nlinarith

private lemma lineMap_eq_iff (A D B E : Plane) (lam mu : ℝ) :
    AffineMap.lineMap A D lam = AffineMap.lineMap B E mu ↔
      (A 0 + lam * (D 0 - A 0) = B 0 + mu * (E 0 - B 0) ∧
        A 1 + lam * (D 1 - A 1) = B 1 + mu * (E 1 - B 1)) := by
  constructor
  · intro h
    exact ⟨by rw [← lm_apply, h, lm_apply], by rw [← lm_apply, h, lm_apply]⟩
  · rintro ⟨h0, h1⟩
    exact ext_plane (by rw [lm_apply, lm_apply, h0]) (by rw [lm_apply, lm_apply, h1])

/-- Two cevians `AD`, `BE` of a triangle meet at a point strictly inside both, and only there. -/
private lemma cevian (A B C D E P : Plane) (h : cross A B C ≠ 0) (hD : Sbtw ℝ B D C)
    (hE : Sbtw ℝ C E A) (hP1 : P ∈ line[ℝ, A, D]) (hP2 : P ∈ line[ℝ, B, E]) :
    Sbtw ℝ A P D ∧ Sbtw ℝ B P E ∧
      ∀ Q, Q ∈ line[ℝ, A, D] → Q ∈ line[ℝ, B, E] → Q = P := by
  obtain ⟨s, ⟨hs0, hs1⟩, hDs⟩ := hD.wbtw
  obtain ⟨u, ⟨hu0, hu1⟩, hEu⟩ := hE.wbtw
  have hs0' : s ≠ 0 := by rintro rfl; exact hD.ne_left (by rw [← hDs]; simp)
  have hs1' : s ≠ 1 := by rintro rfl; exact hD.ne_right (by rw [← hDs]; simp)
  have hu0' : u ≠ 0 := by rintro rfl; exact hE.ne_left (by rw [← hEu]; simp)
  have hu1' : u ≠ 1 := by rintro rfl; exact hE.ne_right (by rw [← hEu]; simp)
  have hs0 : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs0')
  have hs1 : s < 1 := lt_of_le_of_ne hs1 hs1'
  have hu0 : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu0')
  have hu1 : u < 1 := lt_of_le_of_ne hu1 hu1'
  have hD0 : D 0 = B 0 + s * (C 0 - B 0) := by rw [← hDs, lm_apply]
  have hD1 : D 1 = B 1 + s * (C 1 - B 1) := by rw [← hDs, lm_apply]
  have hE0 : E 0 = C 0 + u * (A 0 - C 0) := by rw [← hEu, lm_apply]
  have hE1 : E 1 = C 1 + u * (A 1 - C 1) := by rw [← hEu, lm_apply]
  have hden : 0 < 1 - u + u * s := by nlinarith
  -- any common point has the parameters below
  have key : ∀ lam mu : ℝ, AffineMap.lineMap A D lam = AffineMap.lineMap B E mu →
      mu = s / (1 - u + u * s) ∧ lam = 1 - mu * u := by
    intro lam mu hlm
    obtain ⟨e0, e1⟩ := (lineMap_eq_iff A D B E lam mu).1 hlm
    rw [hD0, hE0] at e0
    rw [hD1, hE1] at e1
    have k1 : (lam * (1 - s) - (1 - mu)) * cross A B C = 0 := by
      simp only [cross]
      linear_combination (C 1 - A 1) * e0 - (C 0 - A 0) * e1
    have k2 : (lam * s - mu * (1 - u)) * cross A B C = 0 := by
      simp only [cross]
      linear_combination -(B 1 - A 1) * e0 + (B 0 - A 0) * e1
    have k1' := (mul_eq_zero.1 k1).resolve_right h
    have k2' := (mul_eq_zero.1 k2).resolve_right h
    have hlam : lam = 1 - mu * u := by linarith
    refine ⟨?_, hlam⟩
    rw [eq_div_iff hden.ne']
    rw [hlam] at k2'
    linarith
  obtain ⟨lam, hlam⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hP1
  obtain ⟨mu, hmu⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hP2
  obtain ⟨hmu', hlam'⟩ := key lam mu (hlam.trans hmu.symm)
  have hmu0 : 0 < mu := by rw [hmu']; positivity
  have hmu1 : mu < 1 := by rw [hmu', div_lt_one hden]; nlinarith
  have hAD : A ≠ D := by
    intro hAD; apply h
    have h0 : A 0 = B 0 + s * (C 0 - B 0) := by rw [hAD, hD0]
    have h1 : A 1 = B 1 + s * (C 1 - B 1) := by rw [hAD, hD1]
    simp only [cross, h0, h1]; ring
  have hBE : B ≠ E := by
    intro hBE; apply h
    have h0 : B 0 = C 0 + u * (A 0 - C 0) := by rw [hBE, hE0]
    have h1 : B 1 = C 1 + u * (A 1 - C 1) := by rw [hBE, hE1]
    simp only [cross, h0, h1]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [← hlam, sbtw_lineMap_iff]
    refine ⟨hAD, ?_, ?_⟩ <;> rw [hlam'] <;> nlinarith
  · rw [← hmu, sbtw_lineMap_iff]
    exact ⟨hBE, hmu0, hmu1⟩
  · intro Q hQ1 hQ2
    obtain ⟨lam2, hlam2⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hQ1
    obtain ⟨mu2, hmu2⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hQ2
    obtain ⟨hmu2', -⟩ := key lam2 mu2 (hlam2.trans hmu2.symm)
    rw [← hmu2, ← hmu, hmu2', hmu']

/-- A point `Y` on a line through `O` and `U` (with `O ≠ U`) satisfies `Y - O = a • (U - O)`. -/
private lemma sub_eq_smul_of_mem {U V O Y : Plane} (hY : Y ∈ line[ℝ, U, V])
    (hO : O ∈ line[ℝ, U, V]) (hOV : O ≠ V) : ∃ a : ℝ, Y - O = a • (V - O) := by
  obtain ⟨r, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hY
  obtain ⟨q, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hO
  have hq : q ≠ 1 := by rintro rfl; exact hOV (by simp)
  have hq' : 1 - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq)
  refine ⟨(r - q) / (1 - q), ext_plane ?_ ?_⟩ <;>
  · simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, lm_apply]
    field_simp
    ring

private lemma angle_smul_smul_cases (x y : Plane) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    InnerProductGeometry.angle (a • x) (b • y) = InnerProductGeometry.angle x y ∨
      InnerProductGeometry.angle (a • x) (b • y) = π - InnerProductGeometry.angle x y := by
  rcases ha.lt_or_gt with ha | ha <;> rcases hb.lt_or_gt with hb | hb
  · left
    rw [InnerProductGeometry.angle_smul_left_of_neg _ _ ha,
      InnerProductGeometry.angle_smul_right_of_neg _ _ hb, InnerProductGeometry.angle_neg_neg]
  · right
    rw [InnerProductGeometry.angle_smul_left_of_neg _ _ ha,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hb, InnerProductGeometry.angle_neg_left]
  · right
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ ha,
      InnerProductGeometry.angle_smul_right_of_neg _ _ hb, InnerProductGeometry.angle_neg_right]
  · left
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ ha,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hb]

private lemma cross_cyc (A B C : Plane) : cross B C A = cross A B C := by
  simp only [cross]; ring

private lemma ne_of_cross {A B C : Plane} (h : cross A B C ≠ 0) : A ≠ B ∧ B ≠ C ∧ C ≠ A := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> apply h <;> simp only [cross] <;> ring

private lemma triangle_sum {A B C : Plane} (h : cross A B C ≠ 0) :
    ∠ B A C + ∠ C B A + ∠ A C B = π := by
  have := angle_add_angle_add_angle_eq_pi C (ne_of_cross h).1.symm
  rw [angle_comm A B C, angle_comm B C A, angle_comm C A B] at this
  linarith

/-- The angle relation at the vertex `C'` of the inner triangle (Carroll's equation (1)). -/
private lemma eqn_at (A B C D E A' B' C' : Plane) (k l : ℝ) (h : cross A B C ≠ 0)
    (hk1 : k < 1) (hl0 : 0 < l) (hD : Sbtw ℝ B D C) (hE : Sbtw ℝ C E A)
    (hkD : ∠ B A D = k * ∠ B A C) (hlE : ∠ C B E = l * ∠ C B A)
    (hA' : A' ∈ line[ℝ, B, E]) (hB' : B' ∈ line[ℝ, A, D])
    (hC'AD : Sbtw ℝ A C' D) (hC'BE : Sbtw ℝ B C' E)
    (hC'1 : C' ∈ line[ℝ, A, D]) (hC'2 : C' ∈ line[ℝ, B, E])
    (hAC : A' ≠ C') (hBC : B' ≠ C') (hang : ∠ A' C' B' = ∠ A C B) :
    k * ∠ B A C + (1 - l) * ∠ C B A = ∠ A C B := by
  obtain ⟨hAB0, hBC0, hCA0⟩ := ne_of_cross h
  have hsum := triangle_sum h
  have hα : 0 < ∠ B A C := by
    have := sin_angle_pos B A C h
    rcases (EuclideanGeometry.angle_nonneg B A C).lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, Real.sin_zero] at this; exact absurd this (lt_irrefl 0)
  have hβ : 0 ≤ ∠ C B A := EuclideanGeometry.angle_nonneg _ _ _
  have hsplitA : ∠ B A D + ∠ D A C = ∠ B A C := angle_add_of_ne_of_ne hAB0 hCA0.symm hD.wbtw
  have hsplitB : ∠ C B E + ∠ E B A = ∠ C B A := angle_add_of_ne_of_ne hBC0 hAB0.symm hE.wbtw
  have e1 : ∠ C' A B = ∠ D A B := hC'AD.angle_eq_left B
  have e2 : ∠ C' B A = ∠ E B A := hC'BE.angle_eq_left A
  have htri := angle_add_angle_add_angle_eq_pi C' hAB0.symm
  have hpi := hC'BE.angle₁₂₃_eq_pi
  have hsupp := angle_add_angle_eq_pi_of_angle_eq_pi A hpi
  obtain ⟨a, ha⟩ := sub_eq_smul_of_mem hA' hC'2 hC'BE.ne_right
  have hB'' : B' ∈ line[ℝ, D, A] := by rw [Set.pair_comm]; exact hB'
  have hC'' : C' ∈ line[ℝ, D, A] := by rw [Set.pair_comm]; exact hC'1
  obtain ⟨b, hb⟩ := sub_eq_smul_of_mem hB'' hC'' hC'AD.ne_left
  have ha0 : a ≠ 0 := by
    rintro rfl; apply hAC; rw [zero_smul, sub_eq_zero] at ha; exact ha
  have hb0 : b ≠ 0 := by
    rintro rfl; apply hBC; rw [zero_smul, sub_eq_zero] at hb; exact hb
  have hang' : ∠ A' C' B' = InnerProductGeometry.angle (a • (E - C')) (b • (A - C')) := by
    rw [← ha, ← hb]; rfl
  have hEC'A : ∠ E C' A = InnerProductGeometry.angle (E - C') (A - C') := rfl
  have c1 := angle_comm A B C'
  have c2 := angle_comm B C' A
  have c3 := angle_comm D A B
  have c4 := angle_comm E C' A
  have hkα : 0 < (1 - k) * ∠ B A C := mul_pos (by linarith) hα
  have hlβ : 0 ≤ l * ∠ C B A := mul_nonneg hl0.le hβ
  rcases angle_smul_smul_cases (E - C') (A - C') ha0 hb0 with hc | hc
  · rw [hang', hc, ← hEC'A] at hang
    linarith
  · rw [hang', hc, ← hEC'A] at hang
    nlinarith

private lemma dist_on_segment {A D X Y : Plane} (hX : Wbtw ℝ A X D) (hY : Wbtw ℝ A Y D) :
    dist Y X = |dist A X - dist A Y| := by
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hX
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hY
  rw [dist_lineMap_lineMap, dist_left_lineMap, dist_left_lineMap, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hs0, abs_of_nonneg ht0, ← sub_mul, abs_mul,
    abs_of_nonneg dist_nonneg, Real.dist_eq, abs_sub_comm]

/-- The side `B'C'` of the inner triangle (Carroll's § 4), given equations (1) and (3). -/
private lemma side_len (A B C D E F B' C' : Plane) (k l m : ℝ) (h : cross A B C ≠ 0)
    (hD : Sbtw ℝ B D C) (hE : Sbtw ℝ C E A)
    (hkD : ∠ B A D = k * ∠ B A C) (hlE : ∠ C B E = l * ∠ C B A) (hmF : ∠ A C F = m * ∠ A C B)
    (hC'AD : Sbtw ℝ A C' D) (hC'BE : Sbtw ℝ B C' E) (hB'AD : Sbtw ℝ A B' D)
    (hB'CF : Sbtw ℝ C B' F)
    (e1 : k * ∠ B A C + (1 - l) * ∠ C B A = ∠ A C B)
    (e3 : m * ∠ A C B + (1 - k) * ∠ B A C = ∠ C B A) :
    dist B' C' = |2 * Real.cos (k * ∠ B A C + ∠ C B A)| * dist B C := by
  obtain ⟨hAB0, hBC0, hCA0⟩ := ne_of_cross h
  have hsum := triangle_sum h
  have sα := sin_angle_pos B A C h
  have sβ := sin_angle_pos C B A (by rw [cross_cyc]; exact h)
  have sγ := sin_angle_pos A C B (by rw [cross_cyc, cross_cyc]; exact h)
  have hsplitA : ∠ B A D + ∠ D A C = ∠ B A C := angle_add_of_ne_of_ne hAB0 hCA0.symm hD.wbtw
  have hsplitB : ∠ C B E + ∠ E B A = ∠ C B A := angle_add_of_ne_of_ne hBC0 hAB0.symm hE.wbtw
  have a1 : ∠ C' A B = ∠ D A B := hC'AD.angle_eq_left B
  have a2 : ∠ C' B A = ∠ E B A := hC'BE.angle_eq_left A
  have a3 : ∠ B' A C = ∠ D A C := hB'AD.angle_eq_left C
  have a4 : ∠ B' C A = ∠ F C A := hB'CF.angle_eq_left A
  have t1 := angle_add_angle_add_angle_eq_pi C' hAB0.symm
  have t2 := angle_add_angle_add_angle_eq_pi B' hCA0
  set θ := k * ∠ B A C + ∠ C B A with hθ
  -- the angles of the triangles `ABC'` and `AB'C`
  have g1 : ∠ A C' B = π - ∠ A C B := by
    have := angle_comm A B C'; have := angle_comm B C' A; have := angle_comm D A B; linarith
  have g2 : ∠ C' B A = π - (∠ B A C + θ) := by linarith
  have g3 : ∠ A B' C = π - ∠ C B A := by
    have := angle_comm A C B'; have := angle_comm C B' A; have := angle_comm F C A
    nlinarith
  have g4 : ∠ B' C A = θ - ∠ B A C := by
    have := angle_comm F C A; linarith
  have l1 := law_sin C' B A
  have l2 := law_sin B' C A
  have l3 := law_sin B A C
  have l4 := law_sin C A B
  rw [g1, Real.sin_pi_sub, g2, Real.sin_pi_sub] at l1
  rw [g3, Real.sin_pi_sub, g4] at l2
  rw [angle_comm C A B, angle_comm B C A] at l4
  rw [dist_comm B A] at l1
  rw [dist_comm C B] at l3
  rw [dist_comm C A] at l2
  have hX : Real.sin (∠ B A C) * dist A C' = Real.sin (∠ B A C + θ) * dist B C := by
    apply mul_left_cancel₀ sγ.ne'
    linear_combination (-Real.sin (∠ B A C)) * l1 + Real.sin (∠ B A C + θ) * l4
  have hY : Real.sin (∠ B A C) * dist A B' = Real.sin (θ - ∠ B A C) * dist B C := by
    apply mul_left_cancel₀ sβ.ne'
    linear_combination (-Real.sin (∠ B A C)) * l2 + Real.sin (θ - ∠ B A C) * l3
  have hd := dist_on_segment hC'AD.wbtw hB'AD.wbtw
  apply mul_left_cancel₀ sα.ne'
  calc Real.sin (∠ B A C) * dist B' C'
      = |Real.sin (∠ B A C) * dist A C' - Real.sin (∠ B A C) * dist A B'| := by
        rw [hd, ← mul_sub, abs_mul, abs_of_pos sα]
    _ = |(Real.sin (∠ B A C + θ) - Real.sin (θ - ∠ B A C)) * dist B C| := by
        rw [hX, hY, sub_mul]
    _ = |2 * Real.cos θ * Real.sin (∠ B A C)| * dist B C := by
        rw [abs_mul _ (dist B C), abs_of_nonneg dist_nonneg, Real.sin_add, Real.sin_sub]
        congr 2; ring
    _ = Real.sin (∠ B A C) * (|2 * Real.cos θ| * dist B C) := by
        rw [abs_mul _ (Real.sin _), abs_of_pos sα]; ring

private lemma angle_pos_of_cross (P Q R : Plane) (h : cross Q P R ≠ 0) : 0 < ∠ P Q R := by
  have hs := sin_angle_pos P Q R h
  rcases (EuclideanGeometry.angle_nonneg P Q R).lt_or_eq with h0 | h0
  · exact h0
  · rw [← h0, Real.sin_zero] at hs; exact absurd hs (lt_irrefl 0)

private lemma angle_eq_of_inner {x y x' y' : Plane} {c : ℝ} (hc : 0 < c)
    (hxy : inner ℝ x' y' = c * inner ℝ x y) (hxx : inner ℝ x' x' = c * inner ℝ x x)
    (hyy : inner ℝ y' y' = c * inner ℝ y y) :
    InnerProductGeometry.angle x' y' = InnerProductGeometry.angle x y := by
  have nx : ‖x'‖ = √c * ‖x‖ := by
    rw [← Real.sqrt_sq (norm_nonneg x'), ← real_inner_self_eq_norm_sq, hxx,
      real_inner_self_eq_norm_sq, Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg x)]
  have ny : ‖y'‖ = √c * ‖y‖ := by
    rw [← Real.sqrt_sq (norm_nonneg y'), ← real_inner_self_eq_norm_sq, hyy,
      real_inner_self_eq_norm_sq, Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg y)]
  unfold InnerProductGeometry.angle
  rw [nx, ny, hxy]
  congr 1
  have hsc : √c * √c = c := Real.mul_self_sqrt hc.le
  rw [show √c * ‖x‖ * (√c * ‖y‖) = (√c * √c) * (‖x‖ * ‖y‖) by ring, hsc]
  exact mul_div_mul_left _ _ hc.ne'

private lemma mem_line_of {P Q X : Plane} (r : ℝ) (h0 : X 0 = P 0 + r * (Q 0 - P 0))
    (h1 : X 1 = P 1 + r * (Q 1 - P 1)) : X ∈ line[ℝ, P, Q] :=
  (mem_affineSpan_pair_iff_exists_lineMap_eq).2
    ⟨r, ext_plane (by rw [lm_apply, h0]) (by rw [lm_apply, h1])⟩

private lemma sbtw_of {P Q X : Plane} (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hPQ : P ≠ Q)
    (h0 : X 0 = P 0 + r * (Q 0 - P 0)) (h1 : X 1 = P 1 + r * (Q 1 - P 1)) :
    Sbtw ℝ P X Q := by
  have : X = AffineMap.lineMap P Q r := ext_plane (by rw [lm_apply, h0]) (by rw [lm_apply, h1])
  rw [this, sbtw_lineMap_iff]
  exact ⟨hPQ, hr0, hr1⟩

/-- Carroll's answer, with the corrected side ratio: writing `θ = ∠ADC` (the angle each of the
three lines makes with the opposite side), `k = (θ - B)/A`, `l = (θ - C)/B`, `m = (θ - A)/C`, and
each side of the inner triangle is `|2 cos θ|` times the corresponding side of `ABC`. -/
theorem problem69 (A B C D E F A' B' C' : Plane) (k l m : ℝ) (hABC : cross A B C ≠ 0)
    (hk : 0 < k ∧ k < 1) (hl : 0 < l ∧ l < 1) (hm : 0 < m ∧ m < 1)
    (hD : Sbtw ℝ B D C) (hE : Sbtw ℝ C E A) (hF : Sbtw ℝ A F B)
    (hkD : ∠ B A D = k * ∠ B A C) (hlE : ∠ C B E = l * ∠ A B C) (hmF : ∠ A C F = m * ∠ A C B)
    (hA'1 : A' ∈ line[ℝ, B, E]) (hA'2 : A' ∈ line[ℝ, C, F])
    (hB'1 : B' ∈ line[ℝ, C, F]) (hB'2 : B' ∈ line[ℝ, A, D])
    (hC'1 : C' ∈ line[ℝ, A, D]) (hC'2 : C' ∈ line[ℝ, B, E])
    (hsimA : ∠ B' A' C' = ∠ B A C) (hsimB : ∠ A' B' C' = ∠ A B C)
    (hsimC : ∠ A' C' B' = ∠ A C B) :
    ∃ θ : ℝ, θ = ∠ A D C ∧
      k = (θ - ∠ A B C) / ∠ B A C ∧ l = (θ - ∠ A C B) / ∠ A B C ∧
      m = (θ - ∠ B A C) / ∠ A C B ∧
      dist B' C' = |2 * Real.cos θ| * dist B C ∧ dist C' A' = |2 * Real.cos θ| * dist C A ∧
      dist A' B' = |2 * Real.cos θ| * dist A B := by
  rw [angle_comm A B C] at hlE hsimB ⊢
  rw [angle_comm A' B' C'] at hsimB
  have h2 : cross B C A ≠ 0 := by rw [cross_cyc]; exact hABC
  have h3 : cross C A B ≠ 0 := by rw [cross_cyc, cross_cyc]; exact hABC
  obtain ⟨hC'AD, hC'BE, uAB⟩ := cevian A B C D E C' hABC hD hE hC'1 hC'2
  obtain ⟨hA'BE, hA'CF, uBC⟩ := cevian B C A E F A' h2 hE hF hA'1 hA'2
  obtain ⟨hB'CF, hB'AD, uCA⟩ := cevian C A B F D B' h3 hF hD hB'1 hB'2
  have hsum := triangle_sum hABC
  -- the three lines are not concurrent, so `A', B', C'` are distinct
  have hall : ¬ (A' = B' ∧ B' = C') := by
    rintro ⟨rfl, rfl⟩
    have h0 : ∠ A' A' A' = π / 2 := by
      simp [EuclideanGeometry.angle]
    rw [h0] at hsimA hsimB hsimC
    linarith [Real.pi_pos]
  have hAC : A' ≠ C' := by
    intro e
    have : C' = B' := uCA C' (e ▸ hA'2) hC'1
    exact hall ⟨e.trans this, this.symm⟩
  have hBC : B' ≠ C' := by
    intro e
    have : B' = A' := uBC B' (e ▸ hC'2) hB'1
    exact hall ⟨this.symm, e⟩
  have hAB : A' ≠ B' := by
    intro e
    have : A' = C' := uAB A' (e ▸ hB'2) hA'1
    exact hall ⟨e, e.symm.trans this⟩
  have e1 := eqn_at A B C D E A' B' C' k l hABC hk.2 hl.1 hD hE hkD hlE hA'1 hB'2 hC'AD hC'BE
    hC'1 hC'2 hAC hBC hsimC
  have e2 := eqn_at B C A E F B' C' A' l m h2 hl.2 hm.1 hE hF hlE hmF hB'1 hC'2 hA'BE hA'CF
    hA'1 hA'2 hAB.symm hAC.symm hsimA
  have e3 := eqn_at C A B F D C' A' B' m k h3 hm.2 hk.1 hF hD hmF hkD hC'1 hA'2 hB'CF hB'AD
    hB'1 hB'2 hBC.symm hAB hsimB
  have L1 := side_len A B C D E F B' C' k l m hABC hD hE hkD hlE hmF hC'AD hC'BE hB'AD hB'CF
    e1 e3
  have L2 := side_len B C A E F D C' A' l m k h2 hE hF hlE hmF hkD hA'BE hA'CF hC'BE hC'AD
    e2 e1
  have L3 := side_len C A B F D E A' B' m k l h3 hF hD hmF hkD hlE hB'CF hB'AD hA'CF hA'BE
    e3 e2
  obtain ⟨hAB0, hBC0, hCA0⟩ := ne_of_cross hABC
  -- `θ = ∠ADC = kA + B`
  have hθ : ∠ A D C = k * ∠ B A C + ∠ C B A := by
    have t := angle_add_angle_add_angle_eq_pi D hAB0.symm
    have r1 : ∠ A B D = ∠ A B C := hD.angle_eq_right A
    have r2 := angle_add_angle_eq_pi_of_angle_eq_pi A hD.angle₁₂₃_eq_pi
    have := angle_comm B D A; have := angle_comm D A B; have := angle_comm A B C
    linarith
  have hθ2 : l * ∠ C B A + ∠ A C B = k * ∠ B A C + ∠ C B A := by linarith
  have hθ3 : m * ∠ A C B + ∠ B A C = k * ∠ B A C + ∠ C B A := by linarith
  have hα := (sin_angle_pos B A C hABC)
  have hβ := (sin_angle_pos C B A h2)
  have hγ := (sin_angle_pos A C B h3)
  have pα : ∠ B A C ≠ 0 := by intro h0; rw [h0, Real.sin_zero] at hα; exact lt_irrefl 0 hα
  have pβ : ∠ C B A ≠ 0 := by intro h0; rw [h0, Real.sin_zero] at hβ; exact lt_irrefl 0 hβ
  have pγ : ∠ A C B ≠ 0 := by intro h0; rw [h0, Real.sin_zero] at hγ; exact lt_irrefl 0 hγ
  refine ⟨∠ A D C, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hθ]; field_simp; ring
  · rw [hθ, ← hθ2]; field_simp; ring
  · rw [hθ, ← hθ3]; field_simp; ring
  · rw [hθ]; exact L1
  · rw [hθ, ← hθ2]; exact L2
  · rw [hθ, ← hθ3]; exact L3

/-- A line from `A` cutting off any proper part `x` of the angle `BAC` meets `BC` internally. -/
private lemma exists_cut (A B C : Plane) (h : cross A B C ≠ 0) (x : ℝ) (hx0 : 0 < x)
    (hx1 : x < ∠ B A C) : ∃ D, Sbtw ℝ B D C ∧ ∠ B A D = x := by
  obtain ⟨hAB0, hBC0, -⟩ := ne_of_cross h
  have hne : ∀ t : ℝ, AffineMap.lineMap B C t ≠ A := by
    intro t ht
    apply h
    have h0 : A 0 = B 0 + t * (C 0 - B 0) := by rw [← ht, lm_apply]
    have h1 : A 1 = B 1 + t * (C 1 - B 1) := by rw [← ht, lm_apply]
    simp only [cross, h0, h1]; ring
  set f : ℝ → ℝ := fun t => ∠ B A (AffineMap.lineMap B C t) with hf
  have hcont : ContinuousOn f (Set.Icc 0 1) := by
    intro t _
    apply ContinuousAt.continuousWithinAt
    have h1 : ContinuousAt (fun y : Plane × Plane × Plane => ∠ y.1 y.2.1 y.2.2)
        (B, A, AffineMap.lineMap B C t) := continuousAt_angle hAB0.symm (hne t)
    have h2 : Continuous (fun s : ℝ => (B, A, AffineMap.lineMap B C s)) :=
      continuous_const.prodMk (continuous_const.prodMk AffineMap.lineMap_continuous)
    exact ContinuousAt.comp (x := t) (f := fun s : ℝ => (B, A, AffineMap.lineMap B C s)) h1
      h2.continuousAt
  have hf0 : f 0 = 0 := by simp [hf, angle_self_of_ne hAB0.symm]
  have hf1 : f 1 = ∠ B A C := by simp [hf]
  obtain ⟨t, ⟨ht0, ht1⟩, hft⟩ := intermediate_value_Icc zero_le_one hcont
    (⟨by rw [hf0]; exact hx0.le, by rw [hf1]; exact hx1.le⟩ : x ∈ Set.Icc (f 0) (f 1))
  have ht0' : t ≠ 0 := by rintro rfl; rw [hf0] at hft; linarith
  have ht1' : t ≠ 1 := by rintro rfl; rw [hf1] at hft; linarith
  refine ⟨AffineMap.lineMap B C t, ?_, hft⟩
  rw [sbtw_lineMap_iff]
  exact ⟨hBC0, lt_of_le_of_ne ht0 (Ne.symm ht0'), lt_of_le_of_ne ht1 ht1'⟩

/-- Two cevians `AD`, `BE` (with `D`, `E` inside the opposite sides) do meet. -/
private lemma cevian_meet (A B C D E : Plane) (hD : Sbtw ℝ B D C) (hE : Sbtw ℝ C E A) :
    ∃ P, P ∈ line[ℝ, A, D] ∧ P ∈ line[ℝ, B, E] := by
  obtain ⟨s, ⟨hs0, hs1⟩, hDs⟩ := hD.wbtw
  obtain ⟨u, ⟨hu0, hu1⟩, hEu⟩ := hE.wbtw
  have hu1' : u ≠ 1 := by rintro rfl; exact hE.ne_right (by rw [← hEu]; simp)
  have hu1 : u < 1 := lt_of_le_of_ne hu1 hu1'
  have hD0 : D 0 = B 0 + s * (C 0 - B 0) := by rw [← hDs, lm_apply]
  have hD1 : D 1 = B 1 + s * (C 1 - B 1) := by rw [← hDs, lm_apply]
  have hE0 : E 0 = C 0 + u * (A 0 - C 0) := by rw [← hEu, lm_apply]
  have hE1 : E 1 = C 1 + u * (A 1 - C 1) := by rw [← hEu, lm_apply]
  have hden : 0 < 1 - u + u * s := by nlinarith
  refine ⟨AffineMap.lineMap B E (s / (1 - u + u * s)),
    mem_line_of (1 - s / (1 - u + u * s) * u) ?_ ?_,
    AffineMap.lineMap_mem_affineSpan_pair _ _ _⟩
  · rw [lm_apply, hD0, hE0]; field_simp; ring
  · rw [lm_apply, hD1, hE1]; field_simp; ring

/-- At the vertex `C' = AD ∩ BE` of the inner triangle, its angle is either
`∠BAD + ∠ABE` or the supplement of that. -/
private lemma angle_cases (A B D E A' B' C' : Plane) (hAB0 : A ≠ B)
    (hA' : A' ∈ line[ℝ, B, E]) (hB' : B' ∈ line[ℝ, A, D])
    (hC'AD : Sbtw ℝ A C' D) (hC'BE : Sbtw ℝ B C' E)
    (hC'1 : C' ∈ line[ℝ, A, D]) (hC'2 : C' ∈ line[ℝ, B, E])
    (hAC : A' ≠ C') (hBC : B' ≠ C') :
    ∠ A' C' B' = ∠ B A D + ∠ A B E ∨ ∠ A' C' B' = π - (∠ B A D + ∠ A B E) := by
  have e1 : ∠ C' A B = ∠ D A B := hC'AD.angle_eq_left B
  have e2 : ∠ C' B A = ∠ E B A := hC'BE.angle_eq_left A
  have htri := angle_add_angle_add_angle_eq_pi C' hAB0.symm
  have hpi := hC'BE.angle₁₂₃_eq_pi
  have hsupp := angle_add_angle_eq_pi_of_angle_eq_pi A hpi
  obtain ⟨a, ha⟩ := sub_eq_smul_of_mem hA' hC'2 hC'BE.ne_right
  have hB'' : B' ∈ line[ℝ, D, A] := by rw [Set.pair_comm]; exact hB'
  have hC'' : C' ∈ line[ℝ, D, A] := by rw [Set.pair_comm]; exact hC'1
  obtain ⟨b, hb⟩ := sub_eq_smul_of_mem hB'' hC'' hC'AD.ne_left
  have ha0 : a ≠ 0 := by
    rintro rfl; apply hAC; rw [zero_smul, sub_eq_zero] at ha; exact ha
  have hb0 : b ≠ 0 := by
    rintro rfl; apply hBC; rw [zero_smul, sub_eq_zero] at hb; exact hb
  have hang' : ∠ A' C' B' = InnerProductGeometry.angle (a • (E - C')) (b • (A - C')) := by
    rw [← ha, ← hb]; rfl
  have hEC'A : ∠ E C' A = InnerProductGeometry.angle (E - C') (A - C') := rfl
  have c1 := angle_comm A B C'
  have c2 := angle_comm B C' A
  have c3 := angle_comm D A B
  have c4 := angle_comm E C' A
  have c5 := angle_comm E B A
  rcases angle_smul_smul_cases (E - C') (A - C') ha0 hb0 with hc | hc
  · left; rw [hang', hc, ← hEC'A]; linarith
  · right; rw [hang', hc, ← hEC'A]; linarith

/-- Converse of `problem69` (Carroll's § 2–3): for every `θ` in Carroll's range
`max(A, B, C) < θ < π - max(A, B, C)`, except `θ = π/2` (where the three lines are the
altitudes, which are concurrent, so there is no inner triangle), the fractions
`k = (θ - B)/A`, `l = (θ - C)/B`, `m = (θ - A)/C` are proper fractions and the lines so drawn
do form a triangle similar to `ABC` with the stated correspondence. -/
theorem problem69_converse (A B C : Plane) (θ k l m : ℝ) (hABC : cross A B C ≠ 0)
    (hθA : ∠ B A C < θ) (hθB : ∠ A B C < θ) (hθC : ∠ A C B < θ)
    (hθA' : θ < π - ∠ B A C) (hθB' : θ < π - ∠ A B C) (hθC' : θ < π - ∠ A C B)
    (hθ : θ ≠ π / 2)
    (hk : k = (θ - ∠ A B C) / ∠ B A C) (hl : l = (θ - ∠ A C B) / ∠ A B C)
    (hm : m = (θ - ∠ B A C) / ∠ A C B) :
    (0 < k ∧ k < 1) ∧ (0 < l ∧ l < 1) ∧ (0 < m ∧ m < 1) ∧
    ∃ D E F A' B' C' : Plane, Sbtw ℝ B D C ∧ Sbtw ℝ C E A ∧ Sbtw ℝ A F B ∧
      ∠ B A D = k * ∠ B A C ∧ ∠ C B E = l * ∠ A B C ∧ ∠ A C F = m * ∠ A C B ∧
      A' ∈ line[ℝ, B, E] ∧ A' ∈ line[ℝ, C, F] ∧ B' ∈ line[ℝ, C, F] ∧ B' ∈ line[ℝ, A, D] ∧
      C' ∈ line[ℝ, A, D] ∧ C' ∈ line[ℝ, B, E] ∧
      ∠ B' A' C' = ∠ B A C ∧ ∠ A' B' C' = ∠ A B C ∧ ∠ A' C' B' = ∠ A C B := by
  obtain ⟨hAB0, hBC0, hCA0⟩ := ne_of_cross hABC
  have h2 : cross B C A ≠ 0 := by rw [cross_cyc]; exact hABC
  have h3 : cross C A B ≠ 0 := by rw [cross_cyc, cross_cyc]; exact hABC
  have hsum := triangle_sum hABC
  have hβc : ∠ A B C = ∠ C B A := angle_comm A B C
  have pα := angle_pos_of_cross B A C hABC
  have pβ := angle_pos_of_cross C B A h2
  have pγ := angle_pos_of_cross A C B h3
  rw [hβc] at hθB hθB' hk hl
  have ekα : k * ∠ B A C = θ - ∠ C B A := by rw [hk]; field_simp
  have elβ : l * ∠ C B A = θ - ∠ A C B := by rw [hl]; field_simp
  have emγ : m * ∠ A C B = θ - ∠ B A C := by rw [hm]; field_simp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hk]; exact div_pos (by linarith) pα
  · rw [hk, div_lt_one pα]; linarith
  · rw [hl]; exact div_pos (by linarith) pβ
  · rw [hl, div_lt_one pβ]; linarith
  · rw [hm]; exact div_pos (by linarith) pγ
  · rw [hm, div_lt_one pγ]; linarith
  obtain ⟨D, hD, hkD⟩ := exists_cut A B C hABC (θ - ∠ C B A) (by linarith) (by linarith)
  obtain ⟨E, hE, hlE⟩ := exists_cut B C A h2 (θ - ∠ A C B) (by linarith) (by linarith)
  obtain ⟨F, hF, hmF⟩ := exists_cut C A B h3 (θ - ∠ B A C) (by linarith) (by linarith)
  obtain ⟨C', hC'1, hC'2⟩ := cevian_meet A B C D E hD hE
  obtain ⟨A', hA'1, hA'2⟩ := cevian_meet B C A E F hE hF
  obtain ⟨B', hB'1, hB'2⟩ := cevian_meet C A B F D hF hD
  obtain ⟨hC'AD, hC'BE, -⟩ := cevian A B C D E C' hABC hD hE hC'1 hC'2
  obtain ⟨hA'BE, hA'CF, -⟩ := cevian B C A E F A' h2 hE hF hA'1 hA'2
  obtain ⟨hB'CF, hB'AD, -⟩ := cevian C A B F D B' h3 hF hD hB'1 hB'2
  have hkD' : ∠ B A D = k * ∠ B A C := by rw [ekα]; exact hkD
  have hlE' : ∠ C B E = l * ∠ C B A := by rw [elβ]; exact hlE
  have hmF' : ∠ A C F = m * ∠ A C B := by rw [emγ]; exact hmF
  have e1 : k * ∠ B A C + (1 - l) * ∠ C B A = ∠ A C B := by linear_combination ekα - elβ
  have e2 : l * ∠ C B A + (1 - m) * ∠ A C B = ∠ B A C := by linear_combination elβ - emγ
  have e3 : m * ∠ A C B + (1 - k) * ∠ B A C = ∠ C B A := by linear_combination emγ - ekα
  have L1 := side_len A B C D E F B' C' k l m hABC hD hE hkD' hlE' hmF' hC'AD hC'BE hB'AD hB'CF
    e1 e3
  have L2 := side_len B C A E F D C' A' l m k h2 hE hF hlE' hmF' hkD' hA'BE hA'CF hC'BE hC'AD
    e2 e1
  have L3 := side_len C A B F D E A' B' m k l h3 hF hD hmF' hkD' hlE' hB'CF hB'AD hA'CF hA'BE
    e3 e2
  rw [ekα, sub_add_cancel] at L1
  rw [elβ, sub_add_cancel] at L2
  rw [emγ, sub_add_cancel] at L3
  have hcos : Real.cos θ ≠ 0 := by
    intro hc
    apply hθ
    apply Real.injOn_cos ⟨by linarith, by linarith⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    rw [hc, Real.cos_pi_div_two]
  have hpos : 0 < |2 * Real.cos θ| := abs_pos.2 (mul_ne_zero two_ne_zero hcos)
  have hBC' : B' ≠ C' := by
    intro e; rw [e, dist_self] at L1
    have := mul_pos hpos (dist_pos.2 hBC0); linarith
  have hCA' : C' ≠ A' := by
    intro e; rw [e, dist_self] at L2
    have := mul_pos hpos (dist_pos.2 hCA0); linarith
  have hAB' : A' ≠ B' := by
    intro e; rw [e, dist_self] at L3
    have := mul_pos hpos (dist_pos.2 hAB0); linarith
  have c1 := angle_cases A B D E A' B' C' hAB0 hA'1 hB'2 hC'AD hC'BE hC'1 hC'2 hCA'.symm hBC'
  have c2 := angle_cases B C E F B' C' A' hBC0 hB'1 hC'2 hA'BE hA'CF hA'1 hA'2 hAB'.symm hCA'
  have c3 := angle_cases C A F D C' A' B' hCA0 hC'1 hA'2 hB'CF hB'AD hB'1 hB'2 hBC'.symm hAB'
  have hsplitA : ∠ B A D + ∠ D A C = ∠ B A C := angle_add_of_ne_of_ne hAB0 hCA0.symm hD.wbtw
  have hsplitB : ∠ C B E + ∠ E B A = ∠ C B A := angle_add_of_ne_of_ne hBC0 hAB0.symm hE.wbtw
  have hsplitC : ∠ A C F + ∠ F C B = ∠ A C B := angle_add_of_ne_of_ne hCA0 hBC0.symm hF.wbtw
  have k1 := angle_comm A B E
  have k2 := angle_comm B C F
  have k3 := angle_comm C A D
  have hin := angle_add_angle_add_angle_eq_pi C' hAB'.symm
  have k4 := angle_comm A' B' C'
  have k5 := angle_comm B' C' A'
  have k6 := angle_comm C' A' B'
  refine ⟨D, E, F, A', B', C', hD, hE, hF, hkD', by rw [hβc]; exact hlE', hmF', hA'1, hA'2,
    hB'1, hB'2, hC'1, hC'2, ?_⟩
  rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2 <;> rcases c3 with c3 | c3 <;>
    refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The hypotheses of `problem69` can all be met: the triangle `A = (2,4)`, `B = (0,0)`,
`C = (4,0)` with the three lines making the angle `θ = arccos (5/13)` with the opposite sides. -/
theorem problem69_nonvacuous : ∃ (A B C D E F A' B' C' : Plane) (k l m : ℝ),
    cross A B C ≠ 0 ∧ (0 < k ∧ k < 1) ∧ (0 < l ∧ l < 1) ∧ (0 < m ∧ m < 1) ∧
    Sbtw ℝ B D C ∧ Sbtw ℝ C E A ∧ Sbtw ℝ A F B ∧
    ∠ B A D = k * ∠ B A C ∧ ∠ C B E = l * ∠ A B C ∧ ∠ A C F = m * ∠ A C B ∧
    A' ∈ line[ℝ, B, E] ∧ A' ∈ line[ℝ, C, F] ∧ B' ∈ line[ℝ, C, F] ∧ B' ∈ line[ℝ, A, D] ∧
    C' ∈ line[ℝ, A, D] ∧ C' ∈ line[ℝ, B, E] ∧
    ∠ B' A' C' = ∠ B A C ∧ ∠ A' B' C' = ∠ A B C ∧ ∠ A' C' B' = ∠ A C B := by
  set A := pt 2 4
  set B := pt 0 0
  set C := pt 4 0
  set D := pt (1 / 3) 0
  set E := pt (58 / 15) (4 / 15)
  set F := pt (22 / 15) (44 / 15)
  set A' := pt (638 / 169) (44 / 169)
  set B' := pt (258 / 169) (484 / 169)
  set C' := pt (58 / 169) (4 / 169)
  have hBC : B ≠ C := fun h => by have := congrArg (· 0) h; norm_num [B, C] at this
  have hCA : C ≠ A := fun h => by have := congrArg (· 0) h; norm_num [A, C] at this
  have hAB : A ≠ B := fun h => by have := congrArg (· 0) h; norm_num [A, B] at this
  have hD : Sbtw ℝ B D C := sbtw_of (1 / 12) (by norm_num) (by norm_num) hBC
    (by norm_num [B, C, D]) (by norm_num [B, C, D])
  have hE : Sbtw ℝ C E A := sbtw_of (1 / 15) (by norm_num) (by norm_num) hCA
    (by norm_num [A, C, E]) (by norm_num [A, C, E])
  have hF : Sbtw ℝ A F B := sbtw_of (4 / 15) (by norm_num) (by norm_num) hAB
    (by norm_num [A, B, F]) (by norm_num [A, B, F])
  -- the cut-off angles are proper parts of the angles of `ABC`
  have sA := angle_add_of_ne_of_ne hAB hCA.symm hD.wbtw
  have sB := angle_add_of_ne_of_ne hBC hAB.symm hE.wbtw
  have sC := angle_add_of_ne_of_ne hCA hBC.symm hF.wbtw
  have p1 := angle_pos_of_cross B A D (by norm_num [cross, A, B, D])
  have p2 := angle_pos_of_cross D A C (by norm_num [cross, A, C, D])
  have p3 := angle_pos_of_cross C B E (by norm_num [cross, B, C, E])
  have p4 := angle_pos_of_cross E B A (by norm_num [cross, A, B, E])
  have p5 := angle_pos_of_cross A C F (by norm_num [cross, A, C, F])
  have p6 := angle_pos_of_cross F C B (by norm_num [cross, B, C, F])
  rw [angle_comm C B A] at sB
  refine ⟨A, B, C, D, E, F, A', B', C', ∠ B A D / ∠ B A C, ∠ C B E / ∠ A B C,
    ∠ A C F / ∠ A C B, by norm_num [cross, A, B, C], ⟨div_pos p1 (by linarith), ?_⟩,
    ⟨div_pos p3 (by linarith), ?_⟩, ⟨div_pos p5 (by linarith), ?_⟩, hD, hE, hF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [div_lt_one (by linarith)]; linarith
  · rw [div_lt_one (by linarith)]; linarith
  · rw [div_lt_one (by linarith)]; linarith
  · exact (div_mul_cancel₀ _ (by linarith : (0:ℝ) < ∠ B A C).ne').symm
  · exact (div_mul_cancel₀ _ (by linarith : (0:ℝ) < ∠ A B C).ne').symm
  · exact (div_mul_cancel₀ _ (by linarith : (0:ℝ) < ∠ A C B).ne').symm
  · exact mem_line_of (165 / 169) (by norm_num [A', B, E]) (by norm_num [A', B, E])
  · exact mem_line_of (15 / 169) (by norm_num [A', C, F]) (by norm_num [A', C, F])
  · exact mem_line_of (165 / 169) (by norm_num [B', C, F]) (by norm_num [B', C, F])
  · exact mem_line_of (48 / 169) (by norm_num [B', A, D]) (by norm_num [B', A, D])
  · exact mem_line_of (168 / 169) (by norm_num [C', A, D]) (by norm_num [C', A, D])
  · exact mem_line_of (15 / 169) (by norm_num [C', B, E]) (by norm_num [C', B, E])
  · unfold EuclideanGeometry.angle
    refine angle_eq_of_inner (c := 100 / 169) (by norm_num) ?_ ?_ ?_ <;>
      simp only [vsub_eq_sub, inner_plane, PiLp.sub_apply] <;> norm_num [A, B, C, A', B', C']
  · unfold EuclideanGeometry.angle
    refine angle_eq_of_inner (c := 100 / 169) (by norm_num) ?_ ?_ ?_ <;>
      simp only [vsub_eq_sub, inner_plane, PiLp.sub_apply] <;> norm_num [A, B, C, A', B', C']
  · unfold EuclideanGeometry.angle
    refine angle_eq_of_inner (c := 100 / 169) (by norm_num) ?_ ?_ ?_ <;>
      simp only [vsub_eq_sub, inner_plane, PiLp.sub_apply] <;> norm_num [A, B, C, A', B', C']

end PillowProblems.P69
