import PillowProblems.Basic

/-!
# Problem 33 (Differential Calculus: Maxima and Minima)

**Question.**

> Inscribe in a given Circle the maximum Tetragon having 2 parallel sides, one double the other.

*(Carroll's solution: Chapter III, problem 33; text in `data/problems.json`.)*

**Lean reading.** The circle has centre `O` and radius `r > 0`, and the tetragon is `ABCD`
with its vertices on the circle (`IsInscribedTrapezoid`). "Two parallel sides, one double the
other" is read as `B - A = 2 • (C - D)`: `AB` is parallel to `DC`, twice as long, and points the
same way, which is what makes `ABCD` a genuine (uncrossed) trapezoid; `C ≠ D` excludes the
degenerate case. Its area `quadArea` is given by the shoelace formula. The theorem says that the
set of areas has a greatest element, the explicit value `(3/8)(√(2+2√13) + 4√(2√13-7)) r²` (so the
maximum is attained), and that every maximal tetragon has `x²/r² = (5 - √13)/8` where `x` is
*half* the shorter side `DC`, i.e. `DC²/r² = (5 - √13)/2`. **Correction.** Carroll writes "Let
`DE = x`; `∴ BC = 2x`" and answers `x²/r² = (5 - √13)/8`; with `x = DE` literally this is wrong by a
factor 4. His area `3x(√(r²-x²) + √(r²-4x²))`, and hence his equation `16x⁴ - 20r²x² + 3r⁴ = 0`
and his root, are right only when `x` is the half-side, so his answer holds with `x = DE/2`, which
is what is proved (together with the literal form, Carroll's `DE` being `DC` here). The proof is
calculus-free: two AM-GM steps (`core`) bound the area and are equalities only at Carroll's
root, which also proves his remark that the other root is inadmissible.

**Status.** proved (corrected)
-/

namespace PillowProblems.P33

open Real

/-- The area of the quadrilateral `ABCD` (vertices in this order), by the shoelace formula:
half the absolute value of the signed areas of `ABC` and `ACD` added. -/
noncomputable def quadArea (A B C D : Plane) : ℝ := |cross A B C + cross A C D| / 2

/-- `ABCD` is a tetragon inscribed in the circle with centre `O` and radius `r` whose sides `AB`
and `DC` are parallel, `AB` being double `DC`: the vector `AB` is twice the vector `DC` (same
direction, so `ABCD` is a genuine trapezoid and not a crossed quadrilateral). -/
def IsInscribedTrapezoid (O : Plane) (r : ℝ) (A B C D : Plane) : Prop :=
  A ∈ Metric.sphere O r ∧ B ∈ Metric.sphere O r ∧ C ∈ Metric.sphere O r ∧
    D ∈ Metric.sphere O r ∧ C ≠ D ∧ B - A = (2 : ℝ) • (C - D)

private lemma dist_sq' (A B : Plane) : dist A B ^ 2 = (A 0 - B 0) ^ 2 + (A 1 - B 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs,
    Real.sq_sqrt (by positivity)]

private lemma sphere_eq {O A : Plane} {r : ℝ} (h : A ∈ Metric.sphere O r) :
    (A 0 - O 0) ^ 2 + (A 1 - O 1) ^ 2 = r ^ 2 := by
  rw [Metric.mem_sphere] at h
  rw [← dist_sq', h]

/-- The one-variable heart of the problem. With `w = x² / r²` (`x` half the shorter side),
`Y = (x/r)·√(1 - x²/r²)` and `Z = (x/r)·√(1 - 4x²/r²)`, the sum `Y + Z` is at most its value
at `w = (5 - √13)/8`, and only there. -/
private lemma core (w Y Z : ℝ) (hw : 0 ≤ w) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hY2 : Y ^ 2 = w * (1 - w)) (hZ2 : Z ^ 2 = w * (1 - 4 * w)) :
    Y + Z ≤ (√(2 + 2 * √13) + 4 * √(2 * √13 - 7)) / 8 ∧
      (Y + Z = (√(2 + 2 * √13) + 4 * √(2 * √13 - 7)) / 8 → w = (5 - √13) / 8) := by
  set s := √13 with hs
  have hs2 : s ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hlo : 3.6 < s := by nlinarith
  have hhi : s < 3.61 := by nlinarith
  set t := (5 - s) / 8 with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  set P := √(2 + 2 * s) / 8 with hP
  set Q := √(2 * s - 7) / 2 with hQ
  have hP0 : 0 < P := by
    rw [hP]; have : 0 < √(2 + 2 * s) := Real.sqrt_pos.mpr (by linarith); linarith
  have hQ0 : 0 < Q := by
    rw [hQ]; have : 0 < √(2 * s - 7) := Real.sqrt_pos.mpr (by linarith); linarith
  have hP2 : P ^ 2 = t * (1 - t) := by
    rw [hP, div_pow, Real.sq_sqrt (by linarith), ht]; linear_combination (1 / 64 : ℝ) * hs2
  have hQ2 : Q ^ 2 = t * (1 - 4 * t) := by
    rw [hQ, div_pow, Real.sq_sqrt (by linarith), ht]; linear_combination (1 / 16 : ℝ) * hs2
  have hquad : 16 * t ^ 2 - 20 * t + 3 = 0 := by rw [ht]; linear_combination (1 / 4 : ℝ) * hs2
  have hPQ : 2 * P * Q = t := by
    have : (2 * P * Q) ^ 2 = t ^ 2 := by
      rw [mul_pow, mul_pow, hP2, hQ2]; linear_combination t ^ 2 * hquad
    exact (pow_left_inj₀ (by positivity) ht0.le two_ne_zero).mp this
  have hrel : (1 - 2 * t) * Q = (8 * t - 1) * P := by
    have h1 : 0 ≤ (1 - 2 * t) * Q := mul_nonneg (by rw [ht]; linarith) hQ0.le
    have h2 : 0 ≤ (8 * t - 1) * P := mul_nonneg (by rw [ht]; linarith) hP0.le
    have : ((1 - 2 * t) * Q) ^ 2 = ((8 * t - 1) * P) ^ 2 := by
      rw [mul_pow, mul_pow, hP2, hQ2]; linear_combination (3 * t ^ 2) * hquad
    exact (pow_left_inj₀ h1 h2 two_ne_zero).mp this
  have hw4 : w ≤ 1 / 4 := by nlinarith [sq_nonneg Z]
  -- the two AM-GM steps
  have hYb : 2 * P * Y ≤ (1 - 2 * t) * w + t := by
    have hR : 0 ≤ (1 - 2 * t) * w + t := by
      have : 0 ≤ 1 - 2 * t := by rw [ht]; linarith
      positivity
    have e : (2 * P * Y) ^ 2 ≤ ((1 - 2 * t) * w + t) ^ 2 := by
      have : ((1 - 2 * t) * w + t) ^ 2 - (2 * P * Y) ^ 2 = (w - t) ^ 2 := by
        rw [mul_pow, mul_pow, hP2, hY2]; ring
      nlinarith [sq_nonneg (w - t)]
    exact (pow_le_pow_iff_left₀ (by positivity) hR two_ne_zero).mp e
  have hZb : 2 * Q * Z ≤ (1 - 8 * t) * w + t := by
    have hR : 0 ≤ (1 - 8 * t) * w + t := by
      have : (1 - 8 * t) * (1 / 4) ≤ (1 - 8 * t) * w :=
        mul_le_mul_of_nonpos_left hw4 (by rw [ht]; linarith)
      rw [ht] at this ⊢; linarith
    have e : (2 * Q * Z) ^ 2 ≤ ((1 - 8 * t) * w + t) ^ 2 := by
      have : ((1 - 8 * t) * w + t) ^ 2 - (2 * Q * Z) ^ 2 = (w - t) ^ 2 := by
        rw [mul_pow, mul_pow, hQ2, hZ2]; ring
      nlinarith [sq_nonneg (w - t)]
    exact (pow_le_pow_iff_left₀ (by positivity) hR two_ne_zero).mp e
  have h1 : Q * (2 * P * Y) ≤ Q * ((1 - 2 * t) * w + t) := mul_le_mul_of_nonneg_left hYb hQ0.le
  have h2 : P * (2 * Q * Z) ≤ P * ((1 - 8 * t) * w + t) := mul_le_mul_of_nonneg_left hZb hP0.le
  have hK : (√(2 + 2 * √13) + 4 * √(2 * √13 - 7)) / 8 = P + Q := by rw [hP, hQ]; ring
  rw [hK]
  have key : t * (Y + Z) = Q * (2 * P * Y) + P * (2 * Q * Z) := by rw [← hPQ]; ring
  have key2 : Q * ((1 - 2 * t) * w + t) + P * ((1 - 8 * t) * w + t) = t * (P + Q) := by
    linear_combination w * hrel
  refine ⟨?_, fun heq => ?_⟩
  · have : t * (Y + Z) ≤ t * (P + Q) := by linarith
    exact le_of_mul_le_mul_left this ht0
  · -- equality forces equality in the first AM-GM step
    have hYe : Q * (2 * P * Y) = Q * ((1 - 2 * t) * w + t) := by
      have : t * (Y + Z) = t * (P + Q) := by rw [heq]
      linarith
    have hYe' : 2 * P * Y = (1 - 2 * t) * w + t := mul_left_cancel₀ hQ0.ne' hYe
    have : (w - t) ^ 2 = 0 := by
      have : ((1 - 2 * t) * w + t) ^ 2 - (2 * P * Y) ^ 2 = (w - t) ^ 2 := by
        rw [mul_pow, mul_pow, hP2, hY2]; ring
      rw [← this, hYe']; ring
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith

/-- The bound in coordinates relative to the centre: `a`, `d` are the position vectors of `A`, `D`
and `u = C - D`, so that `B = A + 2u`, `C = D + u`. -/
private lemma coord_bound (r a0 a1 d0 d1 u0 u1 : ℝ) (hr : 0 < r)
    (hA : a0 ^ 2 + a1 ^ 2 = r ^ 2) (hB : (a0 + 2 * u0) ^ 2 + (a1 + 2 * u1) ^ 2 = r ^ 2)
    (hC : (d0 + u0) ^ 2 + (d1 + u1) ^ 2 = r ^ 2) (hD : d0 ^ 2 + d1 ^ 2 = r ^ 2) :
    |3 * ((u0 * d1 - u1 * d0) - (u0 * a1 - u1 * a0))| / 2 ≤
        3 / 8 * (√(2 + 2 * √13) + 4 * √(2 * √13 - 7)) * r ^ 2 ∧
      (|3 * ((u0 * d1 - u1 * d0) - (u0 * a1 - u1 * a0))| / 2 =
          3 / 8 * (√(2 + 2 * √13) + 4 * √(2 * √13 - 7)) * r ^ 2 →
        (u0 ^ 2 + u1 ^ 2) / 4 / r ^ 2 = (5 - √13) / 8) := by
  set L := u0 ^ 2 + u1 ^ 2 with hL
  have hau : a0 * u0 + a1 * u1 = -L := by
    linear_combination (1 / 4 : ℝ) * hB - (1 / 4 : ℝ) * hA
  have hdu : d0 * u0 + d1 * u1 = -L / 2 := by
    linear_combination (1 / 2 : ℝ) * hC - (1 / 2 : ℝ) * hD
  set δ := u0 * d1 - u1 * d0 with hδ
  set α := u0 * a1 - u1 * a0 with hα
  have hδ2 : δ ^ 2 = L * r ^ 2 - L ^ 2 / 4 := by
    rw [← hD]
    linear_combination (-(d0 * u0 + d1 * u1) + L / 2) * hdu
  have hα2 : α ^ 2 = L * r ^ 2 - L ^ 2 := by
    rw [← hA]
    linear_combination (-(a0 * u0 + a1 * u1) + L) * hau
  have hr2 : 0 < r ^ 2 := by positivity
  set w := L / (4 * r ^ 2) with hw
  set Y := |δ| / (2 * r ^ 2) with hY
  set Z := |α| / (2 * r ^ 2) with hZ
  have hY2 : Y ^ 2 = w * (1 - w) := by
    rw [hY, hw, div_pow, sq_abs, hδ2]; field_simp; ring
  have hZ2 : Z ^ 2 = w * (1 - 4 * w) := by
    rw [hZ, hw, div_pow, sq_abs, hα2]; field_simp; ring
  obtain ⟨hle, heq⟩ := core w Y Z (by positivity) (by positivity) (by positivity) hY2 hZ2
  have harea : |3 * (δ - α)| / 2 ≤ 3 * r ^ 2 * (Y + Z) := by
    rw [hY, hZ, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have := abs_sub δ α
    field_simp
    nlinarith
  have hw' : L / 4 / r ^ 2 = w := by rw [hw]; field_simp
  rw [hw']
  refine ⟨by nlinarith, fun hmax => heq ?_⟩
  have h3 : 3 * r ^ 2 * ((√(2 + 2 * √13) + 4 * √(2 * √13 - 7)) / 8) ≤ 3 * r ^ 2 * (Y + Z) := by
    nlinarith
  have := le_of_mul_le_mul_left h3 (by positivity)
  linarith

/-- Every inscribed trapezoid has area at most the maximum, with equality only for Carroll's
shape. -/
private lemma bound {O : Plane} {r : ℝ} (hr : 0 < r) {A B C D : Plane}
    (h : IsInscribedTrapezoid O r A B C D) :
    quadArea A B C D ≤ 3 / 8 * (√(2 + 2 * √13) + 4 * √(2 * √13 - 7)) * r ^ 2 ∧
      (quadArea A B C D = 3 / 8 * (√(2 + 2 * √13) + 4 * √(2 * √13 - 7)) * r ^ 2 →
        (dist C D / 2) ^ 2 / r ^ 2 = (5 - √13) / 8) := by
  obtain ⟨hA, hB, hC, hD, -, hv⟩ := h
  have hA' := sphere_eq hA
  have hB' := sphere_eq hB
  have hC' := sphere_eq hC
  have hD' := sphere_eq hD
  have hB0 : B 0 = A 0 + 2 * (C 0 - D 0) := by
    have := congrArg (fun v : Plane => v 0) hv; simp at this; linarith
  have hB1 : B 1 = A 1 + 2 * (C 1 - D 1) := by
    have := congrArg (fun v : Plane => v 1) hv; simp at this; linarith
  have key := coord_bound r (A 0 - O 0) (A 1 - O 1) (D 0 - O 0) (D 1 - O 1) (C 0 - D 0)
    (C 1 - D 1) hr hA' (by rw [hB0, hB1] at hB'; linear_combination hB')
    (by linear_combination hC') hD'
  have hcross : cross A B C + cross A C D =
      3 * (((C 0 - D 0) * (D 1 - O 1) - (C 1 - D 1) * (D 0 - O 0)) -
        ((C 0 - D 0) * (A 1 - O 1) - (C 1 - D 1) * (A 0 - O 0))) := by
    simp only [cross]; rw [hB0, hB1]; ring
  rw [quadArea, hcross, div_pow, dist_sq']
  convert key using 3
  ring

/-- **Problem 33.** Among the tetragons `ABCD` inscribed in a circle of radius `r`, with `AB`
parallel to `DC` and double it, the greatest area is
`(3/8)·(√(2 + 2√13) + 4√(2√13 - 7))·r²`, it is attained, and every tetragon attaining it has
half its shorter side `x = DC/2` with `x² / r² = (5 - √13)/8` (Carroll's equation), i.e.
`DC² / r² = (5 - √13)/2`. -/
theorem problem33 (O : Plane) (r : ℝ) (hr : 0 < r) :
    IsGreatest {S | ∃ A B C D, IsInscribedTrapezoid O r A B C D ∧ S = quadArea A B C D}
        (3 / 8 * (√(2 + 2 * √13) + 4 * √(2 * √13 - 7)) * r ^ 2) ∧
      ∀ A B C D, IsInscribedTrapezoid O r A B C D →
        quadArea A B C D = 3 / 8 * (√(2 + 2 * √13) + 4 * √(2 * √13 - 7)) * r ^ 2 →
        (dist C D / 2) ^ 2 / r ^ 2 = (5 - √13) / 8 ∧ dist C D ^ 2 / r ^ 2 = (5 - √13) / 2 := by
  refine ⟨⟨?_, ?_⟩, fun A B C D h hA => ?_⟩
  rotate_left 2
  · have e := (bound hr h).2 hA
    refine ⟨e, ?_⟩
    have e' : dist C D ^ 2 / r ^ 2 = 4 * ((dist C D / 2) ^ 2 / r ^ 2) := by ring
    rw [e', e]; ring
  · -- Carroll's tetragon: the shorter side above the centre, the longer one below it
    set s := √13 with hs
    have hs2 : s ^ 2 = 13 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hlo : 3.6 < s := by nlinarith
    have hhi : s < 3.61 := by nlinarith
    set t := (5 - s) / 8 with ht
    have ht0 : 0 < t := by rw [ht]; linarith
    set x := √t with hx
    set p := √(1 - t) with hp
    set q := √(1 - 4 * t) with hq
    have hx2 : x ^ 2 = t := Real.sq_sqrt ht0.le
    have hp2 : p ^ 2 = 1 - t := Real.sq_sqrt (by rw [ht]; linarith)
    have hq2 : q ^ 2 = 1 - 4 * t := Real.sq_sqrt (by rw [ht]; linarith)
    have hx0 : 0 < x := Real.sqrt_pos.mpr ht0
    have hp0 : 0 ≤ p := Real.sqrt_nonneg _
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hxp : x * p = √(2 + 2 * s) / 8 := by
      have h1 : 0 ≤ √(2 + 2 * s) / 8 := by positivity
      refine (pow_left_inj₀ (by positivity) h1 two_ne_zero).mp ?_
      rw [mul_pow, hx2, hp2, div_pow, Real.sq_sqrt (by linarith), ht]
      linear_combination (-1 / 64 : ℝ) * hs2
    have hxq : x * q = √(2 * s - 7) / 2 := by
      have h1 : 0 ≤ √(2 * s - 7) / 2 := by positivity
      refine (pow_left_inj₀ (by positivity) h1 two_ne_zero).mp ?_
      rw [mul_pow, hx2, hq2, div_pow, Real.sq_sqrt (by linarith), ht]
      linear_combination (-1 / 16 : ℝ) * hs2
    have mem : ∀ X : Plane, (X 0 - O 0) ^ 2 + (X 1 - O 1) ^ 2 = r ^ 2 →
        X ∈ Metric.sphere O r := by
      intro X hX
      rw [Metric.mem_sphere]
      refine (pow_left_inj₀ dist_nonneg hr.le two_ne_zero).mp ?_
      rw [dist_sq', hX]
    refine ⟨pt (O 0 - 2 * r * x) (O 1 - r * q), pt (O 0 + 2 * r * x) (O 1 - r * q),
      pt (O 0 + r * x) (O 1 + r * p), pt (O 0 - r * x) (O 1 + r * p), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · apply mem; simp only [pt_zero, pt_one]; linear_combination (4 * r ^ 2) * hx2 + r ^ 2 * hq2
    · apply mem; simp only [pt_zero, pt_one]; linear_combination (4 * r ^ 2) * hx2 + r ^ 2 * hq2
    · apply mem; simp only [pt_zero, pt_one]; linear_combination r ^ 2 * hx2 + r ^ 2 * hp2
    · apply mem; simp only [pt_zero, pt_one]; linear_combination r ^ 2 * hx2 + r ^ 2 * hp2
    · intro h
      have := congrArg (fun v : Plane => v 0) h
      simp only [pt_zero] at this
      nlinarith [mul_pos hr hx0]
    · ext i
      fin_cases i
      · simp [pt]; ring
      · simp [pt]
    · rw [quadArea]
      simp only [cross, pt_zero, pt_one]
      have e : (O 0 + 2 * r * x - (O 0 - 2 * r * x)) * (O 1 + r * p - (O 1 - r * q)) -
          (O 0 + r * x - (O 0 - 2 * r * x)) * (O 1 - r * q - (O 1 - r * q)) +
          ((O 0 + r * x - (O 0 - 2 * r * x)) * (O 1 + r * p - (O 1 - r * q)) -
          (O 0 - r * x - (O 0 - 2 * r * x)) * (O 1 + r * p - (O 1 - r * q))) =
          6 * r ^ 2 * (x * p + x * q) := by ring
      rw [e, hxp, hxq, abs_of_nonneg (by positivity)]
      ring
  · rintro _ ⟨A, B, C, D, h, rfl⟩
    exact (bound hr h).1


end PillowProblems.P33
