import PillowProblems.Basic

/-!
# Problem 15 (Pure Geometry, Plane)

**Question.** *(dated 3/91)*

> If a Figure be such that the opposite angles of every inscribed Tetragon are supplementary: the Figure is a Circle.

*(Carroll's solution: Chapter III, problem 15; text in `data/problems.json`.)*

**Lean reading.** "Figure" is not defined by Carroll; his proof treats it as a closed oval whose
perimeter, cut by a chord `AC`, falls into two portions on either side of `AC`, and his inscribed
tetragons have their vertices in order round the perimeter. We read it as a convex region: a
compact convex set `K` with non-empty interior, whose perimeter is `frontier K`. An inscribed
tetragon `ABCD` (`InscribedTetragon`) has its four vertices on the perimeter and is a genuine
convex quadrilateral in the order `A, B, C, D`: its diagonals cross (`B`, `D` strictly on opposite
sides of `AC` and `A`, `C` strictly on opposite sides of `BD`, sides measured by `cross`).
The hypothesis is that every such tetragon has `∠ABC + ∠CDA = π` (unoriented angles; the other
pair of opposite angles is the case `BCDA`), and the conclusion that the perimeter is a circle:
`frontier K = sphere O r` with `r > 0`. The proof follows Carroll (fix `A`, `C`, `D` and show
every other perimeter point lies on the circle `ACD`), choosing `A, C` and `B, D` on two
perpendicular chords through an interior point; it also proves what Carroll leaves tacit, that no
three perimeter points are collinear, so that the tetragons used are genuine. Non-convex figures
are not covered. `problem15_nonvacuous` shows the hypotheses are satisfied by a disc.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P15

open EuclideanGeometry
open scoped Real

/-- `ABCD` is a tetragon inscribed in the figure `S`: its four vertices lie on `S` and it is a
genuine (convex, non-degenerate) quadrilateral with the vertices in this order, i.e. its
diagonals cross: `B`, `D` lie strictly on opposite sides of the line `AC`, and `A`, `C` strictly
on opposite sides of the line `BD`. -/
def InscribedTetragon (S : Set Plane) (A B C D : Plane) : Prop :=
  A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ D ∈ S ∧ cross A C B * cross A C D < 0 ∧ cross B D A * cross B D C < 0

/-! ### Coordinates -/

private lemma vec_ext {u v : Plane} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext i; fin_cases i <;> simp [h0, h1]

private lemma inner_coord (u v : Plane) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]; ring

private lemma dist_sq (u v : Plane) : dist u v ^ 2 = (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- `(A - X) · (C - X)`. -/
private def dt (A C X : Plane) : ℝ := (A 0 - X 0) * (C 0 - X 0) + (A 1 - X 1) * (C 1 - X 1)

private lemma cos_angle_eq (A X C : Plane) :
    Real.cos (∠ A X C) = dt A C X / (dist A X * dist C X) := by
  rw [EuclideanGeometry.angle, InnerProductGeometry.cos_angle, inner_coord,
    dist_eq_norm_vsub Plane A X, dist_eq_norm_vsub Plane C X]
  simp [dt]

private lemma lagrange (A X C : Plane) :
    (dist A X * dist C X) ^ 2 = dt A C X ^ 2 + cross A C X ^ 2 := by
  rw [mul_pow, dist_sq, dist_sq]; simp only [dt, cross]; ring

private lemma dist_pos_of_cross {A C X : Plane} (h : cross A C X ≠ 0) :
    0 < dist A X * dist C X := by
  have hA : A ≠ X := by rintro rfl; apply h; simp [cross]
  have hC : C ≠ X := by rintro rfl; apply h; simp [cross]
  exact mul_pos (dist_pos.mpr hA) (dist_pos.mpr hC)

private lemma ne_zero_of_mul_neg {x y : ℝ} (h : x * y < 0) : x ≠ 0 ∧ y ≠ 0 :=
  ⟨fun e => by rw [e, zero_mul] at h; exact lt_irrefl _ h,
    fun e => by rw [e, mul_zero] at h; exact lt_irrefl _ h⟩

/-- If `U`, `W` are on opposite sides of `AC` and `∠AUC + ∠CWA = π`, then `A, U, C, W` are
concyclic, in the algebraic form `dt U * cross W = dt W * cross U`. -/
private lemma alg_of_angle {A C U W : Plane} (hopp : cross A C U * cross A C W < 0)
    (h : ∠ A U C + ∠ C W A = π) : dt A C U * cross A C W = dt A C W * cross A C U := by
  obtain ⟨hU, hW⟩ := ne_zero_of_mul_neg hopp
  have hcos : Real.cos (∠ A U C) = -Real.cos (∠ A W C) := by
    rw [show ∠ A U C = π - ∠ C W A by linarith, Real.cos_pi_sub, EuclideanGeometry.angle_comm C W A]
  rw [cos_angle_eq, cos_angle_eq] at hcos
  have hnU := dist_pos_of_cross hU
  have hnW := dist_pos_of_cross hW
  have hlU := lagrange A U C
  have hlW := lagrange A W C
  set nU := dist A U * dist C U
  set nW := dist A W * dist C W
  set dU := dt A C U
  set dW := dt A C W
  set cU := cross A C U
  set cW := cross A C W
  have hnU' : nU ≠ 0 := hnU.ne'
  have hnW' : nW ≠ 0 := hnW.ne'
  have e : dU * nW = -dW * nU := by
    field_simp at hcos; linarith
  have e2 : dU ^ 2 * cW ^ 2 = dW ^ 2 * cU ^ 2 := by
    linear_combination (dU * nW - dW * nU) * e - dU ^ 2 * hlW + dW ^ 2 * hlU
  have hsign : dU * dW ≤ 0 := by
    have : dU * dW * nW = -(dW ^ 2 * nU) := by linear_combination dW * e
    have h2 : 0 ≤ dW ^ 2 * nU := by positivity
    by_contra hc
    have : 0 < dU * dW * nW := mul_pos (lt_of_not_ge hc) hnW
    linarith
  have hpq : 0 ≤ (dU * cW) * (dW * cU) := by
    have : (dU * cW) * (dW * cU) = (dU * dW) * (cU * cW) := by ring
    rw [this]; exact mul_nonneg_of_nonpos_of_nonpos hsign (by linarith [mul_comm cU cW])
  have hfac : (dU * cW - dW * cU) * (dU * cW + dW * cU) = 0 := by linear_combination e2
  rcases mul_eq_zero.mp hfac with h1 | h1
  · linarith
  · have h3 : dU * cW = -(dW * cU) := by linarith
    rw [h3] at hpq
    have : dW * cU = 0 := by nlinarith
    linarith

/-- Converse of `alg_of_angle` (used only to show that the circle satisfies the hypothesis). -/
private lemma angle_of_alg {A C U W : Plane} (hopp : cross A C U * cross A C W < 0)
    (h : dt A C U * cross A C W = dt A C W * cross A C U) : ∠ A U C + ∠ C W A = π := by
  obtain ⟨hU, hW⟩ := ne_zero_of_mul_neg hopp
  have hnU := dist_pos_of_cross hU
  have hnW := dist_pos_of_cross hW
  have hlU := lagrange A U C
  have hlW := lagrange A W C
  have cU' := cos_angle_eq A U C
  have cW' := cos_angle_eq A W C
  set nU := dist A U * dist C U
  set nW := dist A W * dist C W
  set dU := dt A C U
  set dW := dt A C W
  set cU := cross A C U
  set cW := cross A C W
  -- `nW * cU = -(cW * nU)`
  have hn : nW * cU = -(cW * nU) := by
    have hsq : (nW * cU) ^ 2 = (cW * nU) ^ 2 := by
      linear_combination cU ^ 2 * hlW - cW ^ 2 * hlU - (dU * cW + dW * cU) * h
    have hneg : 0 < (nW * cU) * (-(cW * nU)) := by
      have : (nW * cU) * (-(cW * nU)) = -(cU * cW) * (nW * nU) := by ring
      rw [this]; exact mul_pos (by linarith) (mul_pos hnW hnU)
    have hfac : (nW * cU - -(cW * nU)) * (nW * cU + -(cW * nU)) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfac with h1 | h1
    · linarith
    · exfalso
      have h2 : nW * cU = cW * nU := by linarith
      rw [h2] at hneg; nlinarith [sq_nonneg (cW * nU)]
  have hd : dW * nU = -(dU * nW) := by
    have : (dW * nU + dU * nW) * cU = 0 := by
      linear_combination nU * h.symm + dU * hn
    have := (mul_eq_zero.mp this).resolve_right hU
    linarith
  have hx : Real.cos (∠ A W C) = -Real.cos (∠ A U C) := by
    have hnU' : nU ≠ 0 := hnU.ne'
    have hnW' : nW ≠ 0 := hnW.ne'
    rw [cU', cW']
    field_simp
    linarith
  have hU0 := EuclideanGeometry.angle_nonneg A U C
  have hU1 := EuclideanGeometry.angle_le_pi A U C
  have hW0 := EuclideanGeometry.angle_nonneg A W C
  have hW1 := EuclideanGeometry.angle_le_pi A W C
  have : ∠ A W C = π - ∠ A U C := by
    rw [← Real.arccos_cos hW0 hW1, hx, Real.arccos_neg, Real.arccos_cos hU0 hU1]
  rw [EuclideanGeometry.angle_comm C W A, this]; ring

private lemma neg_of_eq {x p : ℝ} (hp : 0 < p) (h : x = -p) : x < 0 := by
  rw [h]; exact neg_neg_of_pos hp

/-! ### Convexity facts -/

private lemma interior_of_seg {K : Set Plane} (hconv : Convex ℝ K) {z Y : Plane}
    (hz : z ∈ interior K) (hY : Y ∈ K) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < 1) :
    z + τ • (Y - z) ∈ interior K := by
  rcases h0.lt_or_eq with h0 | rfl
  · apply hconv.openSegment_interior_self_subset_interior hz hY
    refine ⟨1 - τ, τ, by linarith, h0, by ring, ?_⟩
    rw [smul_sub, sub_smul, one_smul]; abel
  · simpa using hz

/-- A ray from an interior point cannot meet the figure, and then the region, further out. -/
private lemma ray_unique {K : Set Plane} (hconv : Convex ℝ K) {z v : Plane}
    (hz : z ∈ interior K) {s t : ℝ} (hs : z + s • v ∈ frontier K) (ht : z + t • v ∈ K)
    (hs0 : 0 < s) (hst : s < t) : False := by
  have ht0 : 0 < t := hs0.trans hst
  have := interior_of_seg hconv hz ht (τ := s / t) (div_nonneg hs0.le ht0.le)
    ((div_lt_one ht0).mpr hst)
  rw [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ ht0.ne'] at this
  exact hs.2 this

/-- Every ray from an interior point of a compact set meets its frontier. -/
private lemma ray_frontier {K : Set Plane} (hK : IsCompact K) {z : Plane} (hz : z ∈ interior K)
    {v : Plane} (hv : v ≠ 0) : ∃ t : ℝ, 0 < t ∧ z + t • v ∈ frontier K := by
  set T := {t : ℝ | 0 ≤ t ∧ z + t • v ∈ K} with hTdef
  have hcont : Continuous fun t : ℝ => z + t • v := by fun_prop
  have hclosed : IsClosed T := isClosed_Ici.inter (hK.isClosed.preimage hcont)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall z
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hbdd : BddAbove T := by
    refine ⟨R / ‖v‖, fun t ht => ?_⟩
    have h1 := hR ht.2
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1] at h1
    rw [le_div_iff₀ hvn]; exact h1
  have hne : T.Nonempty := ⟨0, le_refl _, by simpa using interior_subset hz⟩
  have ht0 : sSup T ∈ T := hclosed.csSup_mem hne hbdd
  have hnotint : z + sSup T • v ∉ interior K := by
    intro hint
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hint
    have hδ : 0 < ε / (2 * ‖v‖) := by positivity
    have hmem : sSup T + ε / (2 * ‖v‖) ∈ T := by
      refine ⟨by linarith [ht0.1], interior_subset (hball ?_)⟩
      rw [Metric.mem_ball, dist_eq_norm, add_smul, ← add_assoc, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos hδ]
      have e : ε / (2 * ‖v‖) * ‖v‖ = ε / 2 := by field_simp
      rw [e]; linarith
    have := le_csSup hbdd hmem
    linarith
  refine ⟨sSup T, ?_, (Set.mem_sdiff _).mpr ⟨subset_closure ht0.2, hnotint⟩⟩
  rcases ht0.1.lt_or_eq with h | h
  · exact h
  · exfalso; apply hnotint; rw [← h]; simpa using hz

/-! ### No three points of the figure are collinear -/

private lemma no_three {K : Set Plane} (hconv : Convex ℝ K) (hcpt : IsCompact K) {z : Plane}
    (hz : z ∈ interior K)
    (h : ∀ A B C D, InscribedTetragon (frontier K) A B C D → ∠ A B C + ∠ C D A = π)
    {U W : Plane} {l : ℝ} (hU : U ∈ frontier K) (hW : W ∈ frontier K)
    (hV : AffineMap.lineMap U W l ∈ frontier K) (hl0 : 0 < l) (hl1 : l < 1) (hUW : U ≠ W) :
    False := by
  have hKc : IsClosed K := hcpt.isClosed
  have hN : 0 < (W 0 - U 0) ^ 2 + (W 1 - U 1) ^ 2 := by
    rcases (show 0 ≤ (W 0 - U 0) ^ 2 + (W 1 - U 1) ^ 2 by positivity).lt_or_eq with h' | h'
    · exact h'
    · exfalso; apply hUW
      have e0 : (W 0 - U 0) ^ 2 = 0 := by nlinarith [sq_nonneg (W 0 - U 0), sq_nonneg (W 1 - U 1)]
      have e1 : (W 1 - U 1) ^ 2 = 0 := by nlinarith [sq_nonneg (W 0 - U 0), sq_nonneg (W 1 - U 1)]
      apply vec_ext
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e0; linarith
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e1; linarith
  -- `z` is not on the line `UW`
  have hs : cross U W z ≠ 0 := by
    intro hs0
    obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = ((z 0 - U 0) * (W 0 - U 0) + (z 1 - U 1) * (W 1 - U 1)) /
        ((W 0 - U 0) ^ 2 + (W 1 - U 1) ^ 2) := ⟨_, rfl⟩
    have hμN : μ * ((W 0 - U 0) ^ 2 + (W 1 - U 1) ^ 2) =
        (z 0 - U 0) * (W 0 - U 0) + (z 1 - U 1) * (W 1 - U 1) := by
      rw [hμ]; exact div_mul_cancel₀ _ hN.ne'
    unfold cross at hs0
    have hz0 : z 0 = U 0 + μ * (W 0 - U 0) := by
      have : (z 0 - U 0 - μ * (W 0 - U 0)) * ((W 0 - U 0) ^ 2 + (W 1 - U 1) ^ 2) = 0 := by
        linear_combination (-(W 0 - U 0)) * hμN - (W 1 - U 1) * hs0
      have := (mul_eq_zero.mp this).resolve_right hN.ne'; linarith
    have hz1 : z 1 = U 1 + μ * (W 1 - U 1) := by
      have : (z 1 - U 1 - μ * (W 1 - U 1)) * ((W 0 - U 0) ^ 2 + (W 1 - U 1) ^ 2) = 0 := by
        linear_combination (-(W 1 - U 1)) * hμN + (W 0 - U 0) * hs0
      have := (mul_eq_zero.mp this).resolve_right hN.ne'; linarith
    rcases lt_trichotomy μ l with hlt | heq | hgt
    · have hmem := interior_of_seg hconv hz (hKc.frontier_subset hW)
        (τ := (l - μ) / (1 - μ)) (div_nonneg (by linarith) (by linarith))
        ((div_lt_one (by linarith)).mpr (by linarith))
      apply hV.2
      convert hmem using 1
      apply vec_ext <;> simp [AffineMap.lineMap_apply_module, hz0, hz1] <;>
        field_simp [show (1 - μ) ≠ 0 by intro e; linarith] <;> ring
    · apply hV.2
      convert hz using 1
      apply vec_ext <;> simp [AffineMap.lineMap_apply_module, hz0, hz1, heq] <;> ring
    · have hμ0 : 0 < μ := hl0.trans hgt
      have hmem := interior_of_seg hconv hz (hKc.frontier_subset hU)
        (τ := (μ - l) / μ) (div_nonneg (by linarith) hμ0.le)
        ((div_lt_one hμ0).mpr (by linarith))
      apply hV.2
      convert hmem using 1
      apply vec_ext <;> simp [AffineMap.lineMap_apply_module, hz0, hz1] <;>
        field_simp <;> ring
  have hs2 : 0 < cross U W z ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hs))
  have hzU : z - U ≠ 0 := by
    intro e; rw [sub_eq_zero] at e; exact hU.2 (e ▸ hz)
  have hzW : z - W ≠ 0 := by
    intro e; rw [sub_eq_zero] at e; exact hW.2 (e ▸ hz)
  obtain ⟨t1, ht1, hP⟩ := ray_frontier hcpt hz hzU
  obtain ⟨t2, ht2, hQ⟩ := ray_frontier hcpt hz hzW
  set P := z + t1 • (z - U) with hPdef
  set Q := z + t2 • (z - W) with hQdef
  set V := AffineMap.lineMap U W l with hVdef
  set s := cross U W z with hsdef
  have hP0 : P 0 = z 0 + t1 * (z 0 - U 0) := by simp [hPdef]
  have hP1 : P 1 = z 1 + t1 * (z 1 - U 1) := by simp [hPdef]
  have hQ0 : Q 0 = z 0 + t2 * (z 0 - W 0) := by simp [hQdef]
  have hQ1 : Q 1 = z 1 + t2 * (z 1 - W 1) := by simp [hQdef]
  have hV0 : V 0 = U 0 + l * (W 0 - U 0) := by
    simp [hVdef, AffineMap.lineMap_apply_module]; ring
  have hV1 : V 1 = U 1 + l * (W 1 - U 1) := by
    simp [hVdef, AffineMap.lineMap_apply_module]; ring
  have c1 : cross W Q P = -(t1 * (1 + t2)) * s := by
    simp only [hsdef, cross, hP0, hP1, hQ0, hQ1]; ring
  have c2 : cross W Q U = (1 + t2) * s := by
    simp only [hsdef, cross, hQ0, hQ1]; ring
  have c3 : cross P U W = (1 + t1) * s := by
    simp only [hsdef, cross, hP0, hP1]; ring
  have c4 : cross P U Q = -(t2 * (1 + t1)) * s := by
    simp only [hsdef, cross, hP0, hP1, hQ0, hQ1]; ring
  have c5 : cross W Q V = (1 + t2) * (1 - l) * s := by
    simp only [hsdef, cross, hQ0, hQ1, hV0, hV1]; ring
  have c6 : cross P V W = (1 + t1) * (1 - l) * s := by
    simp only [hsdef, cross, hP0, hP1, hV0, hV1]; ring
  have c7 : cross P V Q = -(t1 * l * (1 + t2) + (1 + t1) * (1 - l) * t2) * s := by
    simp only [hsdef, cross, hP0, hP1, hQ0, hQ1, hV0, hV1]; ring
  have hl1' : 0 < 1 - l := by linarith
  have T1 : InscribedTetragon (frontier K) W P Q U := by
    refine ⟨hW, hP, hQ, hU, ?_, ?_⟩
    · rw [c1, c2]
      have : 0 < t1 * (1 + t2) ^ 2 * s ^ 2 := mul_pos (mul_pos ht1 (by positivity)) hs2
      exact neg_of_eq this (by ring)
    · rw [c3, c4]
      have : 0 < t2 * (1 + t1) ^ 2 * s ^ 2 := mul_pos (mul_pos ht2 (by positivity)) hs2
      exact neg_of_eq this (by ring)
  have T2 : InscribedTetragon (frontier K) W P Q V := by
    refine ⟨hW, hP, hQ, hV, ?_, ?_⟩
    · rw [c1, c5]
      have : 0 < t1 * (1 + t2) ^ 2 * (1 - l) * s ^ 2 :=
        mul_pos (mul_pos (mul_pos ht1 (by positivity)) hl1') hs2
      exact neg_of_eq this (by ring)
    · rw [c6, c7]
      have hpos : 0 < t1 * l * (1 + t2) + (1 + t1) * (1 - l) * t2 := by
        have := mul_pos (mul_pos ht1 hl0) (by positivity : (0 : ℝ) < 1 + t2)
        have := mul_pos (mul_pos (by positivity : (0 : ℝ) < 1 + t1) hl1') ht2
        linarith
      have : 0 < (1 + t1) * (1 - l) * (t1 * l * (1 + t2) + (1 + t1) * (1 - l) * t2) * s ^ 2 :=
        mul_pos (mul_pos (mul_pos (by positivity) hl1') hpos) hs2
      exact neg_of_eq this (by ring)
  have a1 := alg_of_angle T1.2.2.2.2.1 (h _ _ _ _ T1)
  have a2 := alg_of_angle T2.2.2.2.2.1 (h _ _ _ _ T2)
  have hcP : cross W Q P ≠ 0 := (ne_zero_of_mul_neg T1.2.2.2.2.1).1
  have key : l * (1 - l) * cross W Q P * ((W 0 - U 0) ^ 2 + (W 1 - U 1) ^ 2) = 0 := by
    simp only [dt, cross, hV0, hV1] at a1 a2 ⊢
    linear_combination a2 - (1 - l) * a1
  have : l * (1 - l) * cross W Q P * ((W 0 - U 0) ^ 2 + (W 1 - U 1) ^ 2) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero hl0.ne' hl1'.ne') hcP) hN.ne'
  exact this key

/-! ### Diagonals through a common interior point -/

/-- With `A`, `C` on the figure on either side of the interior point `z` along a horizontal line,
and `W` on the figure vertically above or below `z`, any point `X` of the figure strictly on the
other side of `AC` from `W` gives a tetragon whose diagonal `XW` crosses `AC` between `A`, `C`. -/
private lemma crossing {K : Set Plane} (hconv : Convex ℝ K) (hcpt : IsCompact K) {z : Plane}
    (hz : z ∈ interior K)
    (h : ∀ A B C D, InscribedTetragon (frontier K) A B C D → ∠ A B C + ∠ C D A = π)
    {a c w : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hA : z + a • pt 1 0 ∈ frontier K) (hC : z + c • pt (-1) 0 ∈ frontier K)
    (hW : z + w • pt 0 1 ∈ frontier K) {X : Plane} (hX : X ∈ frontier K)
    (hXw : (X 1 - z 1) * w < 0) :
    cross X (z + w • pt 0 1) (z + a • pt 1 0) * cross X (z + w • pt 0 1) (z + c • pt (-1) 0)
      < 0 := by
  have hKc : IsClosed K := hcpt.isClosed
  have hw : w ≠ 0 := by rintro rfl; simp at hXw
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hw))
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = z 1 + w - X 1 := ⟨_, rfl⟩
  have hmw : 0 < m * w := by rw [hm]; linarith [show (z 1 + w - X 1) * w = -((X 1 - z 1) * w) + w ^ 2 by ring]
  have hm0 : m ≠ 0 := by rintro h0; rw [h0, zero_mul] at hmw; exact lt_irrefl _ hmw
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = ((z 1 - X 1) * w) / (m * w) := ⟨_, rfl⟩
  have hν0 : 0 < ν := by rw [hν]; exact div_pos (by linarith [show (z 1 - X 1) * w = -((X 1 - z 1) * w) by ring]) hmw
  have hν1 : ν < 1 := by rw [hν]; exact (div_lt_one hmw).mpr (by rw [hm]; linarith [show (z 1 + w - X 1) * w = (z 1 - X 1) * w + w ^ 2 by ring])
  have hνm : ν * m = z 1 - X 1 := by rw [hν]; field_simp
  have hW0 : (z + w • pt 0 1) 0 = z 0 := by simp
  have hW1 : (z + w • pt 0 1) 1 = z 1 + w := by simp
  have hA0 : (z + a • pt 1 0) 0 = z 0 + a := by simp
  have hA1 : (z + a • pt 1 0) 1 = z 1 := by simp
  have hC0 : (z + c • pt (-1) 0) 0 = z 0 - c := by simp; ring
  have hC1 : (z + c • pt (-1) 0) 1 = z 1 := by simp
  have hYK : AffineMap.lineMap X (z + w • pt 0 1) ν ∈ K :=
    hconv.lineMap_mem (hKc.frontier_subset hX) (hKc.frontier_subset hW) ⟨hν0.le, hν1.le⟩
  have hY0 : (AffineMap.lineMap X (z + w • pt 0 1) ν : Plane) 0 = X 0 + ν * (z 0 - X 0) := by
    simp [AffineMap.lineMap_apply_module]; ring
  have hY1 : (AffineMap.lineMap X (z + w • pt 0 1) ν : Plane) 1 = z 1 := by
    simp [AffineMap.lineMap_apply_module]
    rw [hm] at hνm
    linear_combination hνm
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = X 0 + ν * (z 0 - X 0) - z 0 := ⟨_, rfl⟩
  have hσm : σ * m = (X 0 - z 0) * w := by
    rw [hσ]
    have : ν * m = z 1 - X 1 := hνm
    rw [hm] at this ⊢
    linear_combination (z 0 - X 0) * this
  have hXW : X ≠ z + w • pt 0 1 := by
    intro e
    have : X 1 = z 1 + w := by rw [e, hW1]
    rw [this] at hXw; linarith [show (z 1 + w - z 1) * w = w ^ 2 by ring]
  have hYz : ∀ r : ℝ, σ = r →
      AffineMap.lineMap X (z + w • pt 0 1) ν = z + r • pt 1 0 := by
    intro r e
    apply vec_ext
    · rw [hY0]; simp; linarith
    · rw [hY1]; simp
  have hYz' : ∀ r : ℝ, σ = -r →
      AffineMap.lineMap X (z + w • pt 0 1) ν = z + r • pt (-1) 0 := by
    intro r e
    apply vec_ext
    · rw [hY0]; simp; linarith
    · rw [hY1]; simp
  have hσa : σ < a := by
    rcases lt_trichotomy σ a with h1 | h1 | h1
    · exact h1
    · exfalso
      have hYfr : AffineMap.lineMap X (z + w • pt 0 1) ν ∈ frontier K := by
        rw [hYz a h1]; exact hA
      exact no_three hconv hcpt hz h hX hW hYfr hν0 hν1 hXW
    · exfalso
      exact ray_unique hconv hz hA (show z + σ • pt 1 0 ∈ K by rw [← hYz σ rfl]; exact hYK)
        ha h1
  have hσc : -c < σ := by
    rcases lt_trichotomy σ (-c) with h1 | h1 | h1
    · exfalso
      exact ray_unique hconv hz hC
        (show z + (-σ) • pt (-1) 0 ∈ K by rw [← hYz' (-σ) (by ring)]; exact hYK)
        hc (by linarith)
    · exfalso
      have hYfr : AffineMap.lineMap X (z + w • pt 0 1) ν ∈ frontier K := by
        rw [hYz' c h1]; exact hC
      exact no_three hconv hcpt hz h hX hW hYfr hν0 hν1 hXW
    · exact h1
  have hp : cross X (z + w • pt 0 1) (z + a • pt 1 0) = m * (σ - a) := by
    have : cross X (z + w • pt 0 1) (z + a • pt 1 0) = (X 0 - z 0) * w - a * m := by
      simp only [cross, hW0, hW1, hA0, hA1]; rw [hm]; ring
    rw [this, ← hσm]; ring
  have hq : cross X (z + w • pt 0 1) (z + c • pt (-1) 0) = m * (σ + c) := by
    have : cross X (z + w • pt 0 1) (z + c • pt (-1) 0) = (X 0 - z 0) * w + c * m := by
      simp only [cross, hW0, hW1, hC0, hC1]; rw [hm]; ring
    rw [this, ← hσm]; ring
  rw [hp, hq]
  have hm2 : 0 < m ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hm0))
  have : 0 < m ^ 2 * ((a - σ) * (σ + c)) := mul_pos hm2 (mul_pos (by linarith) (by linarith))
  exact neg_of_eq this (by ring)

/-! ### The theorem -/

/-- If every tetragon inscribed in (the boundary of) a convex figure has supplementary opposite
angles, the boundary of the figure is a circle. -/
theorem problem15 (K : Set Plane) (hconv : Convex ℝ K) (hcpt : IsCompact K)
    (hint : (interior K).Nonempty)
    (h : ∀ A B C D, InscribedTetragon (frontier K) A B C D → ∠ A B C + ∠ C D A = π) :
    ∃ O : Plane, ∃ r : ℝ, 0 < r ∧ frontier K = Metric.sphere O r := by
  obtain ⟨z, hz⟩ := hint
  have hKc : IsClosed K := hcpt.isClosed
  have nz : ∀ x y : ℝ, (x ≠ 0 ∨ y ≠ 0) → pt x y ≠ 0 := by
    intro x y hxy e
    rcases hxy with hx | hy
    · exact hx (by simpa using congrArg (fun v : Plane => v 0) e)
    · exact hy (by simpa using congrArg (fun v : Plane => v 1) e)
  obtain ⟨a, ha, hA⟩ := ray_frontier hcpt hz (nz 1 0 (Or.inl one_ne_zero))
  obtain ⟨c, hc, hC⟩ := ray_frontier hcpt hz (nz (-1) 0 (Or.inl (by norm_num)))
  obtain ⟨d, hd, hD⟩ := ray_frontier hcpt hz (nz 0 1 (Or.inr one_ne_zero))
  obtain ⟨β, hβ, hB⟩ := ray_frontier hcpt hz (nz 0 (-1) (Or.inr (by norm_num)))
  have hB' : z + (-β) • pt 0 1 ∈ frontier K := by
    convert hB using 1; apply vec_ext <;> simp
  obtain ⟨A, hAdef⟩ : ∃ A : Plane, A = z + a • pt 1 0 := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : Plane, C = z + c • pt (-1) 0 := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : Plane, D = z + d • pt 0 1 := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : Plane, B = z + (-β) • pt 0 1 := ⟨_, rfl⟩
  have hA0 : A 0 = z 0 + a := by simp [hAdef]
  have hA1 : A 1 = z 1 := by simp [hAdef]
  have hC0 : C 0 = z 0 - c := by simp [hCdef]; ring
  have hC1 : C 1 = z 1 := by simp [hCdef]
  have hD0 : D 0 = z 0 := by simp [hDdef]
  have hD1 : D 1 = z 1 + d := by simp [hDdef]
  have hB0 : B 0 = z 0 := by simp [hBdef]
  have hB1 : B 1 = z 1 - β := by simp [hBdef]; ring
  have hAf : A ∈ frontier K := hAdef ▸ hA
  have hCf : C ∈ frontier K := hCdef ▸ hC
  have hDf : D ∈ frontier K := hDdef ▸ hD
  have hBf : B ∈ frontier K := hBdef ▸ hB'
  have hcr : ∀ X : Plane, cross A C X = -(a + c) * (X 1 - z 1) := by
    intro X; simp only [cross, hA0, hA1, hC0, hC1]; ring
  have hcrB : cross A C B = (a + c) * β := by rw [hcr, hB1]; ring
  have hcrD : cross A C D = -(a + c) * d := by rw [hcr, hD1]; ring
  have hcD : cross A C D ≠ 0 := by
    rw [hcrD, neg_mul]; exact neg_ne_zero.mpr (by positivity)
  have hcB : cross A C B ≠ 0 := by rw [hcrB]; positivity
  -- the tetragon `ABCD`
  have TB : InscribedTetragon (frontier K) A B C D := by
    refine ⟨hAf, hBf, hCf, hDf, ?_, ?_⟩
    · rw [hcrB, hcrD]
      have : 0 < (a + c) * β * ((a + c) * d) := by positivity
      exact neg_of_eq this (by ring)
    · have e1 : cross B D A = -(a * (d + β)) := by
        simp only [cross, hA0, hA1, hB0, hB1, hD0, hD1]; ring
      have e2 : cross B D C = c * (d + β) := by
        simp only [cross, hC0, hC1, hB0, hB1, hD0, hD1]; ring
      rw [e1, e2]
      have : 0 < a * (d + β) * (c * (d + β)) := by positivity
      exact neg_of_eq this (by ring)
  have hABCD := alg_of_angle TB.2.2.2.2.1 (h _ _ _ _ TB)
  -- every point of the boundary satisfies the equation of the circle through `A`, `C`, `D`
  have hS : ∀ X ∈ frontier K, dt A C X * cross A C D = dt A C D * cross A C X := by
    intro X hX
    rcases lt_trichotomy (X 1) (z 1) with hlt | heq | hgt
    · have hx := crossing hconv hcpt hz h ha hc hA hC hD hX (mul_neg_of_neg_of_pos (by linarith) hd)
      rw [← hAdef, ← hCdef, ← hDdef] at hx
      have T : InscribedTetragon (frontier K) A X C D := by
        refine ⟨hAf, hX, hCf, hDf, ?_, hx⟩
        rw [hcr X, hcrD]
        have : 0 < (a + c) * (z 1 - X 1) * ((a + c) * d) := by
          have : 0 < z 1 - X 1 := by linarith
          positivity
        exact neg_of_eq this (by ring)
      exact alg_of_angle T.2.2.2.2.1 (h _ _ _ _ T)
    · have hcX : cross A C X = 0 := by rw [hcr X, heq]; ring
      rw [hcX, mul_zero]
      -- `X` lies on the line `AC`, hence is `A` or `C`
      have hXK : X ∈ K := hKc.frontier_subset hX
      have hdt : dt A C X = (a - (X 0 - z 0)) * (-c - (X 0 - z 0)) := by
        simp only [dt, hA0, hA1, hC0, hC1, heq]; ring
      rw [hdt]
      rcases lt_trichotomy (X 0 - z 0) 0 with hn | h0 | hp
      · have hXe : X = z + (-(X 0 - z 0)) • pt (-1) 0 := by
          apply vec_ext
          · simp
          · simp [heq]
        rcases lt_trichotomy (-(X 0 - z 0)) c with h1 | h1 | h1
        · exact (ray_unique hconv hz (by rw [← hXe]; exact hX) (hKc.frontier_subset hC) (by linarith) h1).elim
        · rw [show -c - (X 0 - z 0) = 0 by linarith]; ring
        · exact (ray_unique hconv hz hC (by rw [← hXe]; exact hXK) hc h1).elim
      · exfalso
        have : X = z := by
          apply vec_ext
          · linarith
          · exact heq
        exact hX.2 (by rw [this]; exact hz)
      · have hXe : X = z + (X 0 - z 0) • pt 1 0 := by
          apply vec_ext
          · simp
          · simp [heq]
        rcases lt_trichotomy (X 0 - z 0) a with h1 | h1 | h1
        · exact (ray_unique hconv hz (by rw [← hXe]; exact hX) (hKc.frontier_subset hA) hp h1).elim
        · rw [h1]; ring
        · exact (ray_unique hconv hz hA (by rw [← hXe]; exact hXK) ha h1).elim
    · have hx := crossing hconv hcpt hz h ha hc hA hC hB' hX (mul_neg_of_pos_of_neg (by linarith) (by linarith))
      rw [← hAdef, ← hCdef, ← hBdef] at hx
      have T : InscribedTetragon (frontier K) A B C X := by
        refine ⟨hAf, hBf, hCf, hX, ?_, ?_⟩
        · rw [hcrB, hcr X]
          have : 0 < (a + c) * β * ((a + c) * (X 1 - z 1)) := by
            have : 0 < X 1 - z 1 := by linarith
            positivity
          exact neg_of_eq this (by ring)
        · have : cross B X A * cross B X C = cross X B A * cross X B C := by
            simp only [cross]; ring
          rw [this]; exact hx
      have i := alg_of_angle T.2.2.2.2.1 (h _ _ _ _ T)
      have : (dt A C X * cross A C D - dt A C D * cross A C X) * cross A C B = 0 := by
        linear_combination (-(cross A C D)) * i + cross A C X * hABCD
      have := (mul_eq_zero.mp this).resolve_right hcB
      linarith
  -- the circle through `A`, `C`, `D`
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = dt A C D / cross A C D := ⟨_, rfl⟩
  obtain ⟨O, hO⟩ : ∃ O : Plane,
      O = pt ((A 0 + C 0 - k * (C 1 - A 1)) / 2) ((A 1 + C 1 + k * (C 0 - A 0)) / 2) :=
    ⟨_, rfl⟩
  have hcirc : ∀ X ∈ frontier K, dist X O = dist A O := by
    intro X hX
    have e := hS X hX
    have hkX : dt A C X = k * cross A C X := by
      rw [hk]; field_simp; linarith
    have : dist X O ^ 2 = dist A O ^ 2 := by
      rw [dist_sq, dist_sq, hO, pt_zero, pt_one]
      simp only [dt, cross] at hkX
      linear_combination hkX
    exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp this
  -- `z` is strictly inside the circle
  have hAO := dist_sq A O
  have hCO := dist_sq C O
  rw [hcirc C hCf] at hCO
  have hzO : (z 0 - O 0) ^ 2 + (z 1 - O 1) ^ 2 = dist A O ^ 2 - a * c := by
    rw [hA0, hA1] at hAO
    rw [hC0, hC1] at hCO
    have hu : (2 * (z 0 - O 0) - (c - a)) * (a + c) = 0 := by
      linear_combination hCO - hAO
    have hu' := (mul_eq_zero.mp hu).resolve_right (by positivity)
    linear_combination -hAO - a * hu'
  have hr0 : 0 < dist A O := by
    have : 0 < dist A O ^ 2 := by
      linarith [sq_nonneg (z 0 - O 0), sq_nonneg (z 1 - O 1), mul_pos ha hc]
    rcases (dist_nonneg : 0 ≤ dist A O).lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at this; simp at this
  refine ⟨O, dist A O, hr0, ?_⟩
  ext Y
  constructor
  · intro hY; rw [Metric.mem_sphere]; exact hcirc Y hY
  · intro hY
    rw [Metric.mem_sphere] at hY
    have hY2 := dist_sq Y O
    rw [hY] at hY2
    have hYz : Y - z ≠ 0 := by
      intro e; rw [sub_eq_zero] at e; rw [e] at hY2; linarith [mul_pos ha hc]
    obtain ⟨t, ht, hX⟩ := ray_frontier hcpt hz hYz
    have hX2 := dist_sq (z + t • (Y - z)) O
    rw [hcirc _ hX] at hX2
    have hX0 : (z + t • (Y - z)) 0 = z 0 + t * (Y 0 - z 0) := by simp
    have hX1 : (z + t • (Y - z)) 1 = z 1 + t * (Y 1 - z 1) := by simp
    rw [hX0, hX1] at hX2
    have hfac : (t - 1) * (t * ((Y 0 - z 0) ^ 2 + (Y 1 - z 1) ^ 2) + a * c) = 0 := by
      linear_combination -hX2 + t * hY2 + (t - 1) * hzO
    have hpos : 0 < t * ((Y 0 - z 0) ^ 2 + (Y 1 - z 1) ^ 2) + a * c := by positivity
    have ht1 : t = 1 := by
      have := (mul_eq_zero.mp hfac).resolve_right hpos.ne'; linarith
    rw [ht1, one_smul, add_sub_cancel] at hX
    exact hX

/-- The hypotheses of `problem15` are satisfied by a circle (the boundary of a disc): this is
the classical fact that opposite angles of a cyclic quadrilateral are supplementary. -/
theorem problem15_nonvacuous :
    Convex ℝ (Metric.closedBall (0 : Plane) 1) ∧ IsCompact (Metric.closedBall (0 : Plane) 1) ∧
      (interior (Metric.closedBall (0 : Plane) 1)).Nonempty ∧
      ∀ A B C D, InscribedTetragon (frontier (Metric.closedBall (0 : Plane) 1)) A B C D →
        ∠ A B C + ∠ C D A = π := by
  refine ⟨convex_closedBall _ _, isCompact_closedBall _ _,
    ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ one_pos)⟩, ?_⟩
  intro A B C D hT
  rw [frontier_closedBall (0 : Plane) one_ne_zero] at hT
  obtain ⟨hA, hB, hC, hD, h1, -⟩ := hT
  have hs : ∀ X : Plane, X ∈ Metric.sphere (0 : Plane) 1 → X 0 ^ 2 + X 1 ^ 2 = 1 := by
    intro X hX
    rw [Metric.mem_sphere, dist_zero_right] at hX
    have := EuclideanSpace.real_norm_sq_eq X
    rw [hX, Fin.sum_univ_two] at this
    linarith
  have eA := hs A hA
  have eB := hs B hB
  have eC := hs C hC
  have eD := hs D hD
  apply angle_of_alg h1
  linear_combination (norm := skip) (cross A C D) * eB - (cross B C D) * eA -
    (cross A B D) * eC - (cross A C B) * eD
  simp only [dt, cross]
  ring

end PillowProblems.P15
