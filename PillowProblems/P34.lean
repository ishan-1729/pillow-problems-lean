import PillowProblems.Basic

/-!
# Problem 34 (Pure Geometry, Plane)

**Question.** *(dated 21/12/74)*

> From a given Point draw 2 Lines, one to the centre of a given Circle, and the other cutting off from it a Segment containing an angle equal to that between the Lines.

*(Carroll's solution: Chapter III, problem 34; text in `data/problems.json`.)*

**Lean reading.** The circle has centre `C` and radius `r > 0`. The first line is `AC`; the
second is a line through `A` meeting the circle at two points `B ≠ D` (so that a segment is cut
off). "The segment contains an angle equal to it" is read as: some point `X` of the circle other
than `B`, `D` has `∠BXD` equal to the angle between the lines; `X` may lie on either arc, so
either of the two segments cut off by `BD` is allowed. `problem34` treats Carroll's figure: `A`
outside the circle (`r < AC`), `B` the nearer intersection (`B` on the segment `AD`), and the
angle between the lines is `∠CAD`; it proves that the property holds exactly when `CD ⊥ AC`,
which is Carroll's construction (draw `CD ⊥ AC` to the circle and join `AD`), so his lines, one
on each side of `AC`, are the only solutions; `problem34_exists` shows that the construction
can always be carried out. Carroll's "given Point" is not restricted, so `problem34_general`
allows any `A ≠ C` (inside, on, or outside the circle; `A = C` leaves no angle between the
lines), takes either of the two supplementary angles between the lines, and proves that the
property holds exactly when the line passes through an end of the radius perpendicular to `AC`
(`CD ⊥ AC` or `CB ⊥ AC`): Carroll's construction is the complete answer in every position.
Necessity uses the law of sines in the circle (`BD = 2r sin ∠BXD`, from mathlib); sufficiency
takes `X` diametrically opposite the end of that radius.

**Status.** proved
-/

namespace PillowProblems.P34

open EuclideanGeometry
open scoped RealInnerProductSpace

private lemma inner_eq' (x y : Plane) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

private lemma dist_sq' (x y : Plane) : dist x y ^ 2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma norm_sq' (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [← dist_zero_right, dist_sq']; simp

private lemma dist_scale {P Q X Y : Plane} {k : ℝ} (hk : 0 ≤ k) (h0 : P 0 - Q 0 = k * (X 0 - Y 0))
    (h1 : P 1 - Q 1 = k * (X 1 - Y 1)) : dist P Q = k * dist X Y := by
  rw [← sq_eq_sq₀ dist_nonneg (mul_nonneg hk dist_nonneg), mul_pow, dist_sq', dist_sq', h0, h1]
  ring

private lemma seg_coord {p x y : Plane} (h : p ∈ segment ℝ x y) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ p 0 = x 0 + r * (y 0 - x 0) ∧ p 1 = x 1 + r * (y 1 - x 1) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h
  obtain rfl : a = 1 - b := by linarith
  refine ⟨b, hb, by linarith, ?_, ?_⟩ <;> (simp; ring)

/-- The law of sines for a chord: the angle subtended by the chord `BD` at a third point `X` of
the circle has sine `BD / 2r`. -/
private lemma sin_inscribed (C B X D : Plane) {r : ℝ} (hr : 0 < r) (hB : dist B C = r)
    (hX : dist X C = r) (hD : dist D C = r) (hBX : B ≠ X) (hBD : B ≠ D) (hXD : X ≠ D) :
    Real.sin (∠ B X D) * (2 * r) = dist B D := by
  have : Fact (Module.finrank ℝ Plane = 2) := ⟨finrank_euclideanSpace_fin⟩
  let : Module.Oriented ℝ Plane (Fin 2) :=
    ⟨(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation⟩
  have h := EuclideanGeometry.Sphere.dist_div_sin_oangle_eq_two_mul_radius
    (s := ⟨C, r⟩) (p₁ := B) (p₂ := X) (p₃ := D) (EuclideanGeometry.mem_sphere.2 hB)
    (EuclideanGeometry.mem_sphere.2 hX) (EuclideanGeometry.mem_sphere.2 hD) hBX hBD hXD
  have hs : |Real.Angle.sin (∡ B X D)| = Real.sin (∠ B X D) := by
    rw [← Real.Angle.sin_toReal,
      Real.abs_sin_eq_sin_abs_of_abs_le_pi (Real.Angle.abs_toReal_le_pi _),
      ← EuclideanGeometry.angle_eq_abs_oangle_toReal hBX hXD.symm]
  rw [hs] at h
  have hne : Real.sin (∠ B X D) ≠ 0 := by
    intro h0; rw [h0, div_zero] at h; simp at h; linarith
  field_simp at h
  linarith

private lemma p34_nec (A C : Plane) (r : ℝ) (hr : 0 < r) (hA : r < dist A C) (B D : Plane)
    (hB : dist B C = r) (hD : dist D C = r) (hBD : B ≠ D) (hBseg : B ∈ segment ℝ A D)
    (X : Plane) (hX : dist X C = r) (hXB : X ≠ B) (hXD : X ≠ D) (hang : ∠ B X D = ∠ C A D) :
    ⟪D - C, A - C⟫ = 0 := by
  obtain ⟨β, hβ0, hβ1, hB0, hB1⟩ := seg_coord hBseg
  have hβne : 1 - β ≠ 0 := by
    intro h
    apply hBD
    ext i; fin_cases i
    · simp [hB0, show β = 1 by linarith]
    · simp [hB1, show β = 1 by linarith]
  -- squared data in coordinates
  have hBc := congrArg (· ^ 2) hB
  have hDc := congrArg (· ^ 2) hD
  simp only [dist_sq'] at hBc hDc
  rw [hB0, hB1] at hBc
  obtain ⟨d2, hd2⟩ : ∃ d2 : ℝ, d2 = (A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (D 0 - A 0) ^ 2 + (D 1 - A 1) ^ 2 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = (A 0 - C 0) * (D 0 - A 0) + (A 1 - C 1) * (D 1 - A 1) := ⟨_, rfl⟩
  have hd2r : r ^ 2 < d2 := by
    rw [hd2, ← dist_sq']; exact pow_lt_pow_left₀ hA hr.le two_ne_zero
  have hd2pos : 0 < d2 := by nlinarith [pow_pos hr 2]
  have hWpos : 0 < W := by
    rw [hW, ← dist_sq']
    have : D ≠ A := by rintro rfl; linarith
    have := dist_pos.2 this
    positivity
  -- the two intersections with the circle
  have h2g : 2 * g + (1 + β) * W = 0 := by
    have : (1 - β) * (2 * g + (1 + β) * W) = 0 := by
      rw [hg, hW]; linear_combination hDc - hBc
    exact (mul_eq_zero.1 this).resolve_left hβne
  have hβW : β * W = d2 - r ^ 2 := by
    rw [hW, hd2]; rw [hg, hW] at h2g; linear_combination h2g - hDc
  have hgoal : ⟪D - C, A - C⟫ = d2 + g := by
    rw [inner_eq', hd2, hg]; simp only [PiLp.sub_apply]; ring
  rw [hgoal]
  have hsin := sin_inscribed C B X D hr hB hX hD hXB.symm hBD hXD
  rw [hang] at hsin
  have hBDd : dist B D = (1 - β) * dist A D :=
    dist_scale (by linarith) (by rw [hB0]; ring) (by rw [hB1]; ring)
  rw [hBDd] at hsin
  simp only [EuclideanGeometry.angle, InnerProductGeometry.angle, vsub_eq_sub] at hsin
  rw [Real.sin_arccos] at hsin
  set y := ⟪C - A, D - A⟫ / (‖C - A‖ * ‖D - A‖) with hy
  have hy1 : y ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]; exact abs_real_inner_div_norm_mul_norm_le_one _ _
  have hAD : dist A D ^ 2 = W := by rw [dist_sq', hW]; ring
  have hsq : (1 - y ^ 2) * (4 * r ^ 2) = (1 - β) ^ 2 * W := by
    have h2 := congrArg (· ^ 2) hsin
    simp only [mul_pow, Real.sq_sqrt (show 0 ≤ 1 - y ^ 2 by linarith)] at h2
    rw [hAD] at h2
    linear_combination h2
  have hnC : ‖C - A‖ ^ 2 = d2 := by rw [norm_sq', hd2]; simp only [PiLp.sub_apply]; ring
  have hnD : ‖D - A‖ ^ 2 = W := by rw [norm_sq', hW]; simp only [PiLp.sub_apply]
  have hin : ⟪C - A, D - A⟫ = -g := by
    rw [inner_eq', hg]; simp only [PiLp.sub_apply]; ring
  have hy2 : y ^ 2 * (d2 * W) = g ^ 2 := by
    rw [hy, div_pow, mul_pow, hnC, hnD, hin]
    have h1 : d2 ≠ 0 := hd2pos.ne'
    have h2 : W ≠ 0 := hWpos.ne'
    field_simp
  -- E : 4 r² (d² W - g²) = ((1 - β) W)² d²
  have hE : 4 * r ^ 2 * (d2 * W - g ^ 2) = ((1 - β) * W) ^ 2 * d2 := by
    linear_combination (d2 * W) * hsq + 4 * r ^ 2 * hy2
  have hg' : g = -(W + (d2 - r ^ 2)) / 2 := by linear_combination h2g / 2 - hβW / 2
  have h1β : (1 - β) * W = W - (d2 - r ^ 2) := by linear_combination -hβW
  rw [hg', h1β] at hE
  have hF : (W - (d2 + r ^ 2)) * ((d2 + r ^ 2) * W - (d2 - r ^ 2) ^ 2) = 0 := by
    linear_combination -hE
  rcases mul_eq_zero.1 hF with h | h
  · rw [hg']; linear_combination -h / 2
  · exfalso
    have : (d2 - r ^ 2) * (β * (d2 - r ^ 2) - (d2 + r ^ 2)) = 0 := by
      linear_combination (d2 + r ^ 2) * hβW - β * h
    have := (mul_eq_zero.1 this).resolve_left (by linarith)
    linarith [mul_le_of_le_one_left (show 0 ≤ d2 - r ^ 2 by linarith) hβ1, pow_pos hr 2]

private lemma p34_suf (A C : Plane) (r : ℝ) (hr : 0 < r) (hA : r < dist A C) (B D : Plane)
    (hB : dist B C = r) (hD : dist D C = r) (hBD : B ≠ D) (hBseg : B ∈ segment ℝ A D)
    (hperp : ⟪D - C, A - C⟫ = 0) :
    ∃ X : Plane, dist X C = r ∧ X ≠ B ∧ X ≠ D ∧ ∠ B X D = ∠ C A D := by
  obtain ⟨β, hβ0, hβ1, hB0, hB1⟩ := seg_coord hBseg
  have hβne : 1 - β ≠ 0 := by
    intro h
    apply hBD
    ext i; fin_cases i
    · simp [hB0, show β = 1 by linarith]
    · simp [hB1, show β = 1 by linarith]
  -- squared data in coordinates
  have hBc := congrArg (· ^ 2) hB
  have hDc := congrArg (· ^ 2) hD
  simp only [dist_sq'] at hBc hDc
  rw [hB0, hB1] at hBc
  obtain ⟨d2, hd2⟩ : ∃ d2 : ℝ, d2 = (A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (D 0 - A 0) ^ 2 + (D 1 - A 1) ^ 2 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = (A 0 - C 0) * (D 0 - A 0) + (A 1 - C 1) * (D 1 - A 1) := ⟨_, rfl⟩
  have hd2r : r ^ 2 < d2 := by
    rw [hd2, ← dist_sq']; exact pow_lt_pow_left₀ hA hr.le two_ne_zero
  have hd2pos : 0 < d2 := by nlinarith [pow_pos hr 2]
  have hWpos : 0 < W := by
    rw [hW, ← dist_sq']
    have : D ≠ A := by rintro rfl; linarith
    have := dist_pos.2 this
    positivity
  -- the two intersections with the circle
  have h2g : 2 * g + (1 + β) * W = 0 := by
    have : (1 - β) * (2 * g + (1 + β) * W) = 0 := by
      rw [hg, hW]; linear_combination hDc - hBc
    exact (mul_eq_zero.1 this).resolve_left hβne
  have hβW : β * W = d2 - r ^ 2 := by
    rw [hW, hd2]; rw [hg, hW] at h2g; linear_combination h2g - hDc
  have hgoal : ⟪D - C, A - C⟫ = d2 + g := by
    rw [inner_eq', hd2, hg]; simp only [PiLp.sub_apply]; ring
  rw [hgoal] at hperp
  have hae : (A 0 - C 0) * (D 0 - C 0) + (A 1 - C 1) * (D 1 - C 1) = 0 := by
    rw [hd2, hg] at hperp; linear_combination hperp
  have hβ' : (1 - β) * d2 = (1 + β) * r ^ 2 := by
    have : (1 - β) * ((1 - β) * d2 - (1 + β) * r ^ 2) = 0 := by
      rw [hd2]; linear_combination hBc - 2 * β * (1 - β) * hae - β ^ 2 * hDc
    linear_combination (mul_eq_zero.1 this).resolve_left hβne
  refine ⟨C + (C - D), ?_, ?_, ?_, ?_⟩
  · have : dist (C + (C - D)) C = 1 * dist C D := dist_scale zero_le_one
      (by simp only [PiLp.add_apply, PiLp.sub_apply]; ring)
      (by simp only [PiLp.add_apply, PiLp.sub_apply]; ring)
    rw [this, one_mul, dist_comm, hD]
  · intro h
    have h0 := congrArg (fun v : Plane => v 0) h
    have h1 := congrArg (fun v : Plane => v 1) h
    simp only [PiLp.add_apply, PiLp.sub_apply] at h0 h1
    rw [hB0] at h0; rw [hB1] at h1
    have : (1 - β) * d2 = 0 := by
      rw [hd2]
      linear_combination -(A 0 - C 0) * h0 - (A 1 - C 1) * h1 - (1 + β) * hae
    rcases mul_eq_zero.1 this with h' | h'
    · exact hβne h'
    · linarith
  · intro h
    have h0 := congrArg (fun v : Plane => v 0) h
    have h1 := congrArg (fun v : Plane => v 1) h
    simp only [PiLp.add_apply, PiLp.sub_apply] at h0 h1
    have : r ^ 2 = 0 := by
      linear_combination -hDc + (C 0 - D 0) / 2 * h0 + (C 1 - D 1) / 2 * h1
    have : 0 < r ^ 2 := by positivity
    linarith
  · have hinBX : ⟪B - (C + (C - D)), D - (C + (C - D))⟫ = 2 * (1 + β) * r ^ 2 := by
      rw [inner_eq']; simp only [PiLp.add_apply, PiLp.sub_apply]; rw [hB0, hB1]
      linear_combination 2 * (1 - β) * hae + 2 * (1 + β) * hDc
    have hnBX : ‖B - (C + (C - D))‖ ^ 2 = (1 - β) ^ 2 * d2 + (1 + β) ^ 2 * r ^ 2 := by
      rw [norm_sq', hd2]; simp only [PiLp.add_apply, PiLp.sub_apply]; rw [hB0, hB1]
      linear_combination 2 * (1 - β) * (1 + β) * hae + (1 + β) ^ 2 * hDc
    have hnDX : ‖D - (C + (C - D))‖ ^ 2 = 4 * r ^ 2 := by
      rw [norm_sq']; simp only [PiLp.add_apply, PiLp.sub_apply]
      linear_combination 4 * hDc
    have hinCA : ⟪C - A, D - A⟫ = d2 := by
      rw [inner_eq', hd2]; simp only [PiLp.sub_apply]; linear_combination -hae
    have hnCA : ‖C - A‖ ^ 2 = d2 := by
      rw [norm_sq', hd2]; simp only [PiLp.sub_apply]; ring
    have hnDA : ‖D - A‖ ^ 2 = d2 + r ^ 2 := by
      rw [norm_sq', hd2]; simp only [PiLp.sub_apply]; linear_combination hDc - 2 * hae
    have hpos : 0 < (1 - β) ^ 2 * d2 + (1 + β) ^ 2 * r ^ 2 :=
      add_pos_of_nonneg_of_pos (by positivity) (mul_pos (pow_pos (by linarith) 2) (pow_pos hr 2))
    simp only [EuclideanGeometry.angle, InnerProductGeometry.angle, vsub_eq_sub]
    congr 1
    rw [← sq_eq_sq₀ (div_nonneg (by rw [hinBX]; positivity) (by positivity))
      (div_nonneg (by rw [hinCA]; positivity) (by positivity)), div_pow, div_pow, mul_pow,
      mul_pow, hinBX, hinCA, hnBX, hnDX, hnCA, hnDA,
      div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (-4 * r ^ 2 * d2 * ((1 - β) * d2 + (1 + β) * r ^ 2)) * hβ'

/-- **Problem 34.** Let `A` be a point outside the circle of centre `C` and radius `r`, and let a
line from `A` cut the circle at `B` and `D` (`B` the nearer). The chord `BD` cuts off a segment
containing an angle `∠BXD` equal to the angle `∠CAD` between the lines `AC` and `AD` if and
only if `CD ⊥ AC`, i.e. `D` is the end of the radius perpendicular to `AC` (Carroll's
construction). -/
theorem problem34 (A C : Plane) (r : ℝ) (hr : 0 < r) (hA : r < dist A C) (B D : Plane)
    (hB : dist B C = r) (hD : dist D C = r) (hBD : B ≠ D) (hBseg : B ∈ segment ℝ A D) :
    (∃ X : Plane, dist X C = r ∧ X ≠ B ∧ X ≠ D ∧ ∠ B X D = ∠ C A D) ↔
      ⟪D - C, A - C⟫ = 0 := by
  exact ⟨fun ⟨X, hX, hXB, hXD, hang⟩ => p34_nec A C r hr hA B D hB hD hBD hBseg X hX hXB hXD hang,
    p34_suf A C r hr hA B D hB hD hBD hBseg⟩

private lemma line_coord {p x y : Plane} (h : p ∈ line[ℝ, x, y]) :
    ∃ r : ℝ, p 0 = x 0 + r * (y 0 - x 0) ∧ p 1 = x 1 + r * (y 1 - x 1) := by
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 h
  refine ⟨r, ?_, ?_⟩ <;> (rw [← hr, AffineMap.lineMap_apply_module']; simp; ring)

private lemma mem_line_of (p x y : Plane) (r : ℝ) (h0 : p 0 = x 0 + r * (y 0 - x 0))
    (h1 : p 1 = x 1 + r * (y 1 - x 1)) : p ∈ line[ℝ, x, y] := by
  refine mem_affineSpan_pair_iff_exists_lineMap_eq.2 ⟨r, ?_⟩
  rw [AffineMap.lineMap_apply_module']
  ext i; fin_cases i <;> simp [h0, h1] <;> ring

/-- Necessity for an arbitrary given point `A ≠ C`: if `BD = 2r sin ∠CAD`, one of `CB`, `CD`
is perpendicular to `AC`. -/
private lemma p34_nec_gen (A C : Plane) (r : ℝ) (hAC : A ≠ C) (B D : Plane)
    (hB : dist B C = r) (hD : dist D C = r) (hBD : B ≠ D) (hAD : A ≠ D)
    (hBl : B ∈ line[ℝ, A, D]) (hsin : Real.sin (∠ C A D) * (2 * r) = dist B D) :
    ⟪D - C, A - C⟫ = 0 ∨ ⟪B - C, A - C⟫ = 0 := by
  obtain ⟨β, hB0, hB1⟩ := line_coord hBl
  have hβne : 1 - β ≠ 0 := by
    intro h
    apply hBD
    ext i; fin_cases i
    · simp [hB0, show β = 1 by linarith]
    · simp [hB1, show β = 1 by linarith]
  have hBc := congrArg (· ^ 2) hB
  have hDc := congrArg (· ^ 2) hD
  simp only [dist_sq'] at hBc hDc
  rw [hB0, hB1] at hBc
  obtain ⟨d2, hd2⟩ : ∃ d2 : ℝ, d2 = (A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (D 0 - A 0) ^ 2 + (D 1 - A 1) ^ 2 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = (A 0 - C 0) * (D 0 - A 0) + (A 1 - C 1) * (D 1 - A 1) := ⟨_, rfl⟩
  have hd2pos : 0 < d2 := by
    rw [hd2, ← dist_sq']; exact pow_pos (dist_pos.2 hAC) 2
  have hWpos : 0 < W := by
    rw [hW, ← dist_sq']; exact pow_pos (dist_pos.2 hAD.symm) 2
  have h2g : 2 * g + (1 + β) * W = 0 := by
    have : (1 - β) * (2 * g + (1 + β) * W) = 0 := by
      rw [hg, hW]; linear_combination hDc - hBc
    exact (mul_eq_zero.1 this).resolve_left hβne
  have hβW : β * W = d2 - r ^ 2 := by
    rw [hW, hd2]; rw [hg, hW] at h2g; linear_combination h2g - hDc
  have hgoal : ⟪D - C, A - C⟫ = d2 + g := by
    rw [inner_eq', hd2, hg]; simp only [PiLp.sub_apply]; ring
  have hgoalB : ⟪B - C, A - C⟫ = d2 + β * g := by
    rw [inner_eq', hd2, hg]; simp only [PiLp.sub_apply]; rw [hB0, hB1]; ring
  rw [hgoal, hgoalB]
  have hBDd : dist B D = |1 - β| * dist A D := by
    rw [← sq_eq_sq₀ dist_nonneg (mul_nonneg (abs_nonneg _) dist_nonneg), mul_pow, sq_abs,
      dist_sq', dist_sq', hB0, hB1]
    ring
  rw [hBDd] at hsin
  simp only [EuclideanGeometry.angle, InnerProductGeometry.angle, vsub_eq_sub] at hsin
  rw [Real.sin_arccos] at hsin
  set y := ⟪C - A, D - A⟫ / (‖C - A‖ * ‖D - A‖) with hy
  have hy1 : y ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]; exact abs_real_inner_div_norm_mul_norm_le_one _ _
  have hAD2 : dist A D ^ 2 = W := by rw [dist_sq', hW]; ring
  have hsq : (1 - y ^ 2) * (4 * r ^ 2) = (1 - β) ^ 2 * W := by
    have h2 := congrArg (· ^ 2) hsin
    simp only [mul_pow, Real.sq_sqrt (show 0 ≤ 1 - y ^ 2 by linarith), sq_abs] at h2
    rw [hAD2] at h2
    linear_combination h2
  have hnC : ‖C - A‖ ^ 2 = d2 := by rw [norm_sq', hd2]; simp only [PiLp.sub_apply]; ring
  have hnD : ‖D - A‖ ^ 2 = W := by rw [norm_sq', hW]; simp only [PiLp.sub_apply]
  have hin : ⟪C - A, D - A⟫ = -g := by
    rw [inner_eq', hg]; simp only [PiLp.sub_apply]; ring
  have hy2 : y ^ 2 * (d2 * W) = g ^ 2 := by
    rw [hy, div_pow, mul_pow, hnC, hnD, hin]
    have h1 : d2 ≠ 0 := hd2pos.ne'
    have h2 : W ≠ 0 := hWpos.ne'
    field_simp
  have hE : 4 * r ^ 2 * (d2 * W - g ^ 2) = ((1 - β) * W) ^ 2 * d2 := by
    linear_combination (d2 * W) * hsq + 4 * r ^ 2 * hy2
  have hg' : g = -(W + (d2 - r ^ 2)) / 2 := by linear_combination h2g / 2 - hβW / 2
  have h1β : (1 - β) * W = W - (d2 - r ^ 2) := by linear_combination -hβW
  rw [hg', h1β] at hE
  have hF : (W - (d2 + r ^ 2)) * ((d2 + r ^ 2) * W - (d2 - r ^ 2) ^ 2) = 0 := by
    linear_combination -hE
  rcases mul_eq_zero.1 hF with h | h
  · left; rw [hg']; linear_combination -h / 2
  · right
    have : W * (d2 + β * g) = 0 := by
      linear_combination g * hβW + (d2 - r ^ 2) * hg' + h / 2
    exact (mul_eq_zero.1 this).resolve_left hWpos.ne'

/-- Sufficiency for an arbitrary given point `A ≠ C`: if `CD ⊥ AC`, the point `X` opposite `D`
sees the chord `BD` under the angle `∠CAD`. -/
private lemma p34_suf_gen (A C : Plane) (r : ℝ) (hr : 0 < r) (hAC : A ≠ C) (B D : Plane)
    (hB : dist B C = r) (hD : dist D C = r) (hBD : B ≠ D)
    (hBl : B ∈ line[ℝ, A, D]) (hperp : ⟪D - C, A - C⟫ = 0) :
    ∃ X : Plane, dist X C = r ∧ X ≠ B ∧ X ≠ D ∧ ∠ B X D = ∠ C A D := by
  obtain ⟨β, hB0, hB1⟩ := line_coord hBl
  have hβne : 1 - β ≠ 0 := by
    intro h
    apply hBD
    ext i; fin_cases i
    · simp [hB0, show β = 1 by linarith]
    · simp [hB1, show β = 1 by linarith]
  have hBc := congrArg (· ^ 2) hB
  have hDc := congrArg (· ^ 2) hD
  simp only [dist_sq'] at hBc hDc
  rw [hB0, hB1] at hBc
  obtain ⟨d2, hd2⟩ : ∃ d2 : ℝ, d2 = (A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = (A 0 - C 0) * (D 0 - A 0) + (A 1 - C 1) * (D 1 - A 1) := ⟨_, rfl⟩
  have hd2pos : 0 < d2 := by
    rw [hd2, ← dist_sq']; exact pow_pos (dist_pos.2 hAC) 2
  have hgoal : ⟪D - C, A - C⟫ = d2 + g := by
    rw [inner_eq', hd2, hg]; simp only [PiLp.sub_apply]; ring
  rw [hgoal] at hperp
  have hae : (A 0 - C 0) * (D 0 - C 0) + (A 1 - C 1) * (D 1 - C 1) = 0 := by
    rw [hd2, hg] at hperp; linear_combination hperp
  have hβ' : (1 - β) * d2 = (1 + β) * r ^ 2 := by
    have : (1 - β) * ((1 - β) * d2 - (1 + β) * r ^ 2) = 0 := by
      rw [hd2]; linear_combination hBc - 2 * β * (1 - β) * hae - β ^ 2 * hDc
    linear_combination (mul_eq_zero.1 this).resolve_left hβne
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hβlt : β < 1 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (sub_nonneg.2 hc) hd2pos.le]
  have h1β : 0 < 1 + β := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos (sub_pos.2 hβlt) hd2pos, mul_nonneg (neg_nonneg.2 hc) hr2.le]
  refine ⟨C + (C - D), ?_, ?_, ?_, ?_⟩
  · have : dist (C + (C - D)) C = 1 * dist C D := dist_scale zero_le_one
      (by simp only [PiLp.add_apply, PiLp.sub_apply]; ring)
      (by simp only [PiLp.add_apply, PiLp.sub_apply]; ring)
    rw [this, one_mul, dist_comm, hD]
  · intro h
    have h0 := congrArg (fun v : Plane => v 0) h
    have h1 := congrArg (fun v : Plane => v 1) h
    simp only [PiLp.add_apply, PiLp.sub_apply] at h0 h1
    rw [hB0] at h0; rw [hB1] at h1
    have : (1 - β) * d2 = 0 := by
      rw [hd2]
      linear_combination -(A 0 - C 0) * h0 - (A 1 - C 1) * h1 - (1 + β) * hae
    rcases mul_eq_zero.1 this with h' | h'
    · exact hβne h'
    · linarith
  · intro h
    have h0 := congrArg (fun v : Plane => v 0) h
    have h1 := congrArg (fun v : Plane => v 1) h
    simp only [PiLp.add_apply, PiLp.sub_apply] at h0 h1
    have : r ^ 2 = 0 := by
      linear_combination -hDc + (C 0 - D 0) / 2 * h0 + (C 1 - D 1) / 2 * h1
    linarith
  · have hinBX : ⟪B - (C + (C - D)), D - (C + (C - D))⟫ = 2 * (1 + β) * r ^ 2 := by
      rw [inner_eq']; simp only [PiLp.add_apply, PiLp.sub_apply]; rw [hB0, hB1]
      linear_combination 2 * (1 - β) * hae + 2 * (1 + β) * hDc
    have hnBX : ‖B - (C + (C - D))‖ ^ 2 = (1 - β) ^ 2 * d2 + (1 + β) ^ 2 * r ^ 2 := by
      rw [norm_sq', hd2]; simp only [PiLp.add_apply, PiLp.sub_apply]; rw [hB0, hB1]
      linear_combination 2 * (1 - β) * (1 + β) * hae + (1 + β) ^ 2 * hDc
    have hnDX : ‖D - (C + (C - D))‖ ^ 2 = 4 * r ^ 2 := by
      rw [norm_sq']; simp only [PiLp.add_apply, PiLp.sub_apply]
      linear_combination 4 * hDc
    have hinCA : ⟪C - A, D - A⟫ = d2 := by
      rw [inner_eq', hd2]; simp only [PiLp.sub_apply]; linear_combination -hae
    have hnCA : ‖C - A‖ ^ 2 = d2 := by
      rw [norm_sq', hd2]; simp only [PiLp.sub_apply]; ring
    have hnDA : ‖D - A‖ ^ 2 = d2 + r ^ 2 := by
      rw [norm_sq', hd2]; simp only [PiLp.sub_apply]; linear_combination hDc - 2 * hae
    have hpos : 0 < (1 - β) ^ 2 * d2 + (1 + β) ^ 2 * r ^ 2 :=
      add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _) hd2pos.le)
        (mul_pos (pow_pos h1β 2) hr2)
    have hDA : 0 < d2 + r ^ 2 := by linarith
    simp only [EuclideanGeometry.angle, InnerProductGeometry.angle, vsub_eq_sub]
    congr 1
    rw [← sq_eq_sq₀ (div_nonneg (by rw [hinBX]; exact mul_nonneg (by linarith) hr2.le)
        (by positivity))
      (div_nonneg (by rw [hinCA]; exact hd2pos.le) (by positivity)), div_pow, div_pow, mul_pow,
      mul_pow, hinBX, hinCA, hnBX, hnDX, hnCA, hnDA,
      div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (-4 * r ^ 2 * d2 * ((1 - β) * d2 + (1 + β) * r ^ 2)) * hβ'

/-- **Problem 34, any given point.** Let `A` be any point other than the centre `C` (inside, on or
outside the circle), and let a line through `A` meet the circle at the two points `B`, `D`, with
`D ≠ A`. The chord `BD` cuts off a segment containing an angle equal to the angle between the
lines `AC` and `AD` (either of the two supplementary angles between the lines, at a point `X`
of either arc) if and only if one of `CD`, `CB` is perpendicular to `AC`, i.e. the line passes
through an end of the radius perpendicular to `AC` (Carroll's construction). -/
theorem problem34_general (A C : Plane) (r : ℝ) (hr : 0 < r) (hAC : A ≠ C) (B D : Plane)
    (hB : dist B C = r) (hD : dist D C = r) (hBD : B ≠ D) (hAD : A ≠ D)
    (hBl : B ∈ line[ℝ, A, D]) :
    (∃ X : Plane, dist X C = r ∧ X ≠ B ∧ X ≠ D ∧
        (∠ B X D = ∠ C A D ∨ ∠ B X D = Real.pi - ∠ C A D)) ↔
      (⟪D - C, A - C⟫ = 0 ∨ ⟪B - C, A - C⟫ = 0) := by
  constructor
  · rintro ⟨X, hX, hXB, hXD, hang⟩
    have hs := sin_inscribed C B X D hr hB hX hD hXB.symm hBD hXD
    refine p34_nec_gen A C r hAC B D hB hD hBD hAD hBl ?_
    rcases hang with h | h
    · rw [← h]; exact hs
    · rw [← Real.sin_pi_sub, ← h]; exact hs
  · rintro (h | h)
    · obtain ⟨X, hX, hXB, hXD, hang⟩ := p34_suf_gen A C r hr hAC B D hB hD hBD hBl h
      exact ⟨X, hX, hXB, hXD, Or.inl hang⟩
    · obtain ⟨β, hB0, hB1⟩ := line_coord hBl
      have hAB : A ≠ B := by
        rintro rfl
        rw [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at h
        exact hAC h
      have hβ : β ≠ 0 := by
        rintro rfl
        apply hAB
        ext i; fin_cases i
        · simp [hB0]
        · simp [hB1]
      have hDl : D ∈ line[ℝ, A, B] := by
        refine mem_line_of _ _ _ (1 / β) ?_ ?_
        · rw [hB0]; field_simp; ring
        · rw [hB1]; field_simp; ring
      obtain ⟨X, hX, hXD, hXB, hang⟩ :=
        p34_suf_gen A C r hr hAC D B hD hB hBD.symm hDl h
      have hvec : B -ᵥ A = β • (D -ᵥ A) := by
        rw [vsub_eq_sub, vsub_eq_sub]
        ext i; fin_cases i
        · simp [hB0]
        · simp [hB1]
      have hCAB : ∠ C A B = ∠ C A D ∨ ∠ C A B = Real.pi - ∠ C A D := by
        simp only [EuclideanGeometry.angle]
        rw [hvec]
        rcases lt_or_gt_of_ne hβ with hneg | hpos
        · right
          rw [InnerProductGeometry.angle_smul_right_of_neg _ _ hneg,
            InnerProductGeometry.angle_neg_right]
        · left
          exact InnerProductGeometry.angle_smul_right_of_pos _ _ hpos
      refine ⟨X, hX, hXB, hXD, ?_⟩
      rw [angle_comm, hang]
      exact hCAB

private lemma mem_seg_of (p x y : Plane) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (h0 : p 0 = x 0 + r * (y 0 - x 0)) (h1 : p 1 = x 1 + r * (y 1 - x 1)) :
    p ∈ segment ℝ x y := by
  refine ⟨1 - r, r, by linarith, hr0, by ring, ?_⟩
  ext i; fin_cases i <;> simp [h0, h1] <;> ring

/-- **Problem 34, existence.** Carroll's construction can always be carried out: for a point `A`
outside a circle of centre `C`, the point `D` of the circle with `CD ⊥ AC` and the second
intersection `B` of `AD` with the circle give a line `ABD` cutting off a segment that contains
an angle equal to `∠CAD`. -/
theorem problem34_exists (A C : Plane) (r : ℝ) (hr : 0 < r) (hA : r < dist A C) :
    ∃ B D : Plane, dist B C = r ∧ dist D C = r ∧ B ≠ D ∧ B ∈ segment ℝ A D ∧
      ⟪D - C, A - C⟫ = 0 ∧
      ∃ X : Plane, dist X C = r ∧ X ≠ B ∧ X ≠ D ∧ ∠ B X D = ∠ C A D := by
  have hd0 : 0 < dist A C := by linarith
  have hd2 : dist A C ^ 2 = (A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2 := dist_sq' A C
  set d := dist A C with hd
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ * d = r := ⟨r / d, div_mul_cancel₀ _ hd0.ne'⟩
  have hS : 0 < d ^ 2 + r ^ 2 := by positivity
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β * (d ^ 2 + r ^ 2) = d ^ 2 - r ^ 2 :=
    ⟨_, div_mul_cancel₀ _ hS.ne'⟩
  have hrd : r ^ 2 < d ^ 2 := pow_lt_pow_left₀ hA hr.le two_ne_zero
  have hβ0 : 0 ≤ β := by nlinarith
  have hβ1 : β < 1 := by nlinarith
  set D : Plane := pt (C 0 - κ * (A 1 - C 1)) (C 1 + κ * (A 0 - C 0)) with hDdef
  set B : Plane := pt (A 0 + β * (D 0 - A 0)) (A 1 + β * (D 1 - A 1)) with hBdef
  have hDC : dist D C = r := by
    rw [← sq_eq_sq₀ dist_nonneg hr.le, dist_sq']
    simp only [hDdef, pt_zero, pt_one]
    linear_combination (κ * d + r) * hκ - κ ^ 2 * hd2
  have hBC : dist B C = r := by
    rw [← sq_eq_sq₀ dist_nonneg hr.le, dist_sq']
    simp only [hBdef, hDdef, pt_zero, pt_one]
    linear_combination (-(1 - β)) * hβ + β ^ 2 * (κ * d + r) * hκ -
      ((1 - β) ^ 2 + β ^ 2 * κ ^ 2) * hd2
  have hperp : ⟪D - C, A - C⟫ = 0 := by
    rw [inner_eq']; simp only [PiLp.sub_apply, hDdef, pt_zero, pt_one]; ring
  have hBD : B ≠ D := by
    intro h
    have h0 := congrArg (fun v : Plane => v 0) h
    have h1 := congrArg (fun v : Plane => v 1) h
    simp only [hBdef, pt_zero, pt_one] at h0 h1
    have e0 : (1 - β) * (A 0 - D 0) = 0 := by linear_combination h0
    have e1 : (1 - β) * (A 1 - D 1) = 0 := by linear_combination h1
    have hne : (1 - β) ≠ 0 := by linarith
    have hAD : A = D := by
      ext i; fin_cases i
      · have := (mul_eq_zero.1 e0).resolve_left hne; simp; linarith
      · have := (mul_eq_zero.1 e1).resolve_left hne; simp; linarith
    rw [← hAD] at hDC
    linarith [hd]
  have hseg : B ∈ segment ℝ A D :=
    mem_seg_of _ _ _ β hβ0 hβ1.le (by simp [hBdef]) (by simp [hBdef])
  exact ⟨B, D, hBC, hDC, hBD, hseg, hperp, (problem34 A C r hr hA B D hBC hDC hBD hseg).2 hperp⟩

end PillowProblems.P34
