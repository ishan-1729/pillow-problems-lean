import PillowProblems.Basic

/-!
# Problem 20 (Pure Geometry, Plane)

**Question.** *(dated 5/88)*

> In the base of a given Triangle find a Point such that if from it two lines be drawn, terminated by the sides, one being perpendicular to the base and one to the left-hand side, they shall be equal.

*(Carroll's solution: Chapter III, problem 20; text in `data/problems.json`.)*

**Lean reading.** `ABC` is a nondegenerate triangle (`cross A B C ≠ 0`) with base `BC` and
left-hand side `AB`. Following Carroll's figure and his formulas `PQ = PC tan C`,
`PR = PB sin B`, the line from `P ∈ BC` perpendicular to the base is terminated at `Q` on the side
`AC`, and the line perpendicular to `AB` at `R` on the side `AB` (`EqualPerps`); the problem asks
for `PQ = PR`. Fixing these sides is Carroll's reading: if the lines could end on any side,
`P = B` would be a degenerate solution with both lines of length `0`. The tacit hypotheses
`∠C < π/2` and `∠B ≤ π/2` are those of his figure; without them the perpendicular to the base
cannot reach `AC`, or the foot `R` falls outside `AB`. `D` is the foot of the altitude from `A`
(on line `BC`, `AD ⊥ BC`), which Carroll's answer uses. The theorem proves that the solutions are
exactly the points `P` of `BC` with `PC · AB = DC · PB` (Carroll's `PC : PB = DC : AB`) and that
there is exactly one; `problem20_nonvacuous` exhibits a triangle meeting the hypotheses.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P20

open EuclideanGeometry Real
open scoped RealInnerProductSpace

/-- `P` solves Problem 20 for the triangle `ABC` (base `BC`, left-hand side `AB`): `P` lies on
the base, the line from `P` perpendicular to the base ends at `Q` on the side `AC`, the line
from `P` perpendicular to `AB` ends at `R` on `AB`, and `PQ = PR`. -/
def EqualPerps (A B C P : Plane) : Prop :=
  P ∈ segment ℝ B C ∧ ∃ Q ∈ segment ℝ A C, ∃ R ∈ segment ℝ A B,
    ⟪Q - P, C - B⟫ = 0 ∧ ⟪R - P, B - A⟫ = 0 ∧ dist P Q = dist P R

private lemma inner_eq' (x y : Plane) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

private lemma dist_sq' (x y : Plane) : dist x y ^ 2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma dist_scale {P Q X Y : Plane} {k : ℝ} (hk : 0 ≤ k) (h0 : P 0 - Q 0 = k * (X 0 - Y 0))
    (h1 : P 1 - Q 1 = k * (X 1 - Y 1)) : dist P Q = k * dist X Y := by
  rw [← sq_eq_sq₀ dist_nonneg (mul_nonneg hk dist_nonneg), mul_pow, dist_sq', dist_sq', h0, h1]
  ring

private lemma line_coord {p x y : Plane} (h : p ∈ line[ℝ, x, y]) :
    ∃ r : ℝ, p 0 = x 0 + r * (y 0 - x 0) ∧ p 1 = x 1 + r * (y 1 - x 1) := by
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 h
  refine ⟨r, ?_, ?_⟩ <;> (rw [← hr, AffineMap.lineMap_apply_module']; simp; ring)

private lemma seg_coord {p x y : Plane} (h : p ∈ segment ℝ x y) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ p 0 = x 0 + r * (y 0 - x 0) ∧ p 1 = x 1 + r * (y 1 - x 1) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h
  obtain rfl : a = 1 - b := by linarith
  refine ⟨b, hb, by linarith, ?_, ?_⟩ <;> (simp; ring)

private lemma mem_seg_of (p x y : Plane) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (h0 : p 0 = x 0 + r * (y 0 - x 0)) (h1 : p 1 = x 1 + r * (y 1 - x 1)) :
    p ∈ segment ℝ x y := by
  refine ⟨1 - r, r, by linarith, hr0, by ring, ?_⟩
  ext i; fin_cases i <;> simp [h0, h1] <;> ring

/-- The algebra of the analysis: with `u = C - B`, `w = A - B`, `P = B + t u`,
`Q - P = s w + (1 - s - t) u`, `R - P = r w - t u`. -/
private lemma alg_forward {u0 u1 w0 w1 t s r a c m : ℝ}
    (ha2 : a ^ 2 = u0 ^ 2 + u1 ^ 2) (hc2 : c ^ 2 = w0 ^ 2 + w1 ^ 2) (hm : m = u0 * w0 + u1 * w1)
    (ha : 0 < a) (hc : 0 < c) (hX : 0 < a ^ 2 * c ^ 2 - m ^ 2) (ht0 : 0 ≤ t) (hs0 : 0 ≤ s)
    (h1 : (s * w0 + (1 - s - t) * u0) * u0 + (s * w1 + (1 - s - t) * u1) * u1 = 0)
    (h2 : (r * w0 - t * u0) * w0 + (r * w1 - t * u1) * w1 = 0)
    (h3 : (s * w0 + (1 - s - t) * u0) ^ 2 + (s * w1 + (1 - s - t) * u1) ^ 2 =
      (r * w0 - t * u0) ^ 2 + (r * w1 - t * u1) ^ 2) :
    (1 - t) * a ^ 2 * c = (a ^ 2 - m) * t * a := by
  have e1 : a ^ 2 * ((s * w0 + (1 - s - t) * u0) ^ 2 + (s * w1 + (1 - s - t) * u1) ^ 2) =
      s ^ 2 * (a ^ 2 * c ^ 2 - m ^ 2) := by
    rw [ha2, hc2, hm]
    linear_combination ((s * w0 + (1 - s - t) * u0) * u0 + (s * w1 + (1 - s - t) * u1) * u1) * h1
  have e2 : c ^ 2 * ((r * w0 - t * u0) ^ 2 + (r * w1 - t * u1) ^ 2) =
      t ^ 2 * (a ^ 2 * c ^ 2 - m ^ 2) := by
    rw [ha2, hc2, hm]
    linear_combination ((r * w0 - t * u0) * w0 + (r * w1 - t * u1) * w1) * h2
  have e3 : (s ^ 2 * c ^ 2 - t ^ 2 * a ^ 2) * (a ^ 2 * c ^ 2 - m ^ 2) = 0 := by
    linear_combination -c ^ 2 * e1 + a ^ 2 * e2 + a ^ 2 * c ^ 2 * h3
  have e4 : s * c = t * a := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity)]
    have := (mul_eq_zero.1 e3).resolve_right hX.ne'
    linear_combination this
  have e5 : (1 - t) * a ^ 2 = s * (a ^ 2 - m) := by
    rw [ha2, hm]; linear_combination h1
  linear_combination c * e5 + (a ^ 2 - m) * e4

private lemma alg_backward {u0 u1 w0 w1 t a c m : ℝ}
    (ha2 : a ^ 2 = u0 ^ 2 + u1 ^ 2) (hc2 : c ^ 2 = w0 ^ 2 + w1 ^ 2) (hm : m = u0 * w0 + u1 * w1)
    (ha : 0 < a) (hc : 0 < c) (hm0 : 0 ≤ m) (hk : 0 < a ^ 2 - m) (hmac : m ≤ a * c)
    (ht0 : 0 ≤ t) (hR : (1 - t) * a ^ 2 * c = (a ^ 2 - m) * t * a) :
    ∃ s r : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ r ∧ r ≤ 1 ∧
      (s * w0 + (1 - s - t) * u0) * u0 + (s * w1 + (1 - s - t) * u1) * u1 = 0 ∧
      (r * w0 - t * u0) * w0 + (r * w1 - t * u1) * w1 = 0 ∧
      (s * w0 + (1 - s - t) * u0) ^ 2 + (s * w1 + (1 - s - t) * u1) ^ 2 =
        (r * w0 - t * u0) ^ 2 + (r * w1 - t * u1) ^ 2 := by
  have htk : t * (a ^ 2 - m) = (1 - t) * a * c := by
    have : a * (t * (a ^ 2 - m) - (1 - t) * a * c) = 0 := by linear_combination -hR
    have := (mul_eq_zero.1 this).resolve_left ha.ne'
    linear_combination this
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s * c = t * a := ⟨t * a / c, div_mul_cancel₀ _ hc.ne'⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r * c ^ 2 = t * m := ⟨t * m / c ^ 2, div_mul_cancel₀ _ (by positivity)⟩
  have hsd : s = t * a / c := (eq_div_iff hc.ne').2 hs
  have hrd : r = t * m / c ^ 2 := (eq_div_iff (by positivity)).2 hr
  have hK : 0 < a ^ 2 - m + a * c := by nlinarith [mul_pos ha hc]
  have hs0 : 0 ≤ s := by rw [hsd]; positivity
  have hs1 : s ≤ 1 := by
    have h : (c - t * a) * (a ^ 2 - m + a * c) = c * (a * c - m) := by
      linear_combination (-a) * htk
    have : 0 ≤ c - t * a := by
      by_contra hneg; push Not at hneg
      have := mul_neg_of_neg_of_pos hneg hK
      nlinarith [mul_nonneg hc.le (sub_nonneg.2 hmac)]
    rw [hsd, div_le_one hc]; linarith
  have hr0 : 0 ≤ r := by rw [hrd]; positivity
  have hr1 : r ≤ 1 := by
    have h : (c ^ 2 - t * m) * (a ^ 2 - m + a * c) = c * (a + c) * (a * c - m) := by
      linear_combination (-m) * htk
    have : 0 ≤ c ^ 2 - t * m := by
      by_contra hneg; push Not at hneg
      have := mul_neg_of_neg_of_pos hneg hK
      nlinarith [mul_nonneg (mul_nonneg hc.le (add_nonneg ha.le hc.le)) (sub_nonneg.2 hmac)]
    rw [hrd, div_le_one (by positivity)]; linarith
  have h1 : (s * w0 + (1 - s - t) * u0) * u0 + (s * w1 + (1 - s - t) * u1) * u1 = 0 := by
    have : c * (s * m + (1 - s - t) * a ^ 2) = 0 := by
      linear_combination (m - a ^ 2) * hs - a * htk
    have := (mul_eq_zero.1 this).resolve_left hc.ne'
    linear_combination this - s * hm - (1 - s - t) * ha2
  have h2 : (r * w0 - t * u0) * w0 + (r * w1 - t * u1) * w1 = 0 := by
    linear_combination hr - r * hc2 + t * hm
  refine ⟨s, r, hs0, hs1, hr0, hr1, h1, h2, ?_⟩
  have e1 : a ^ 2 * ((s * w0 + (1 - s - t) * u0) ^ 2 + (s * w1 + (1 - s - t) * u1) ^ 2) =
      s ^ 2 * (a ^ 2 * c ^ 2 - m ^ 2) := by
    rw [ha2, hc2, hm]
    linear_combination ((s * w0 + (1 - s - t) * u0) * u0 + (s * w1 + (1 - s - t) * u1) * u1) * h1
  have e2 : c ^ 2 * ((r * w0 - t * u0) ^ 2 + (r * w1 - t * u1) ^ 2) =
      t ^ 2 * (a ^ 2 * c ^ 2 - m ^ 2) := by
    rw [ha2, hc2, hm]
    linear_combination ((r * w0 - t * u0) * w0 + (r * w1 - t * u1) * w1) * h2
  have e3 : (a ^ 2 * c ^ 2) * (((s * w0 + (1 - s - t) * u0) ^ 2 + (s * w1 + (1 - s - t) * u1) ^ 2) -
      ((r * w0 - t * u0) ^ 2 + (r * w1 - t * u1) ^ 2)) = 0 := by
    linear_combination c ^ 2 * e1 - a ^ 2 * e2 + ((a ^ 2 * c ^ 2 - m ^ 2) * (s * c + t * a)) * hs
  have := (mul_eq_zero.1 e3).resolve_left (by positivity)
  linear_combination this

/-- **Problem 20.** For a triangle `ABC` with acute angle `C` and non-obtuse angle `B`, and `D` the
foot of the altitude from `A`, the points of the base solving the problem are exactly those with
`PC : PB = DC : AB` (Carroll's answer), and there is exactly one. -/
theorem problem20 (A B C D : Plane) (hABC : cross A B C ≠ 0)
    (hB : ∠ A B C ≤ π / 2) (hC : ∠ A C B < π / 2)
    (hD : D ∈ line[ℝ, B, C]) (hAD : ⟪A - D, C - B⟫ = 0) :
    (∀ P, EqualPerps A B C P ↔
      (P ∈ segment ℝ B C ∧ dist P C * dist A B = dist D C * dist P B)) ∧
    ∃! P, EqualPerps A B C P := by
  have hcr := hABC
  unfold cross at hcr
  have ha : 0 < dist B C := dist_pos.2 (fun h => hcr (by subst h; ring))
  have hc : 0 < dist A B := dist_pos.2 (fun h => hcr (by subst h; ring))
  have ha2 : dist B C ^ 2 = (C 0 - B 0) ^ 2 + (C 1 - B 1) ^ 2 := by rw [dist_sq']; ring
  have hc2 : dist A B ^ 2 = (A 0 - B 0) ^ 2 + (A 1 - B 1) ^ 2 := by rw [dist_sq']
  set a := dist B C
  set c := dist A B
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (C 0 - B 0) * (A 0 - B 0) + (C 1 - B 1) * (A 1 - B 1) := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by
    by_contra hneg
    push Not at hneg
    have hi : ⟪A -ᵥ B, C -ᵥ B⟫ < 0 := by
      rw [vsub_eq_sub, vsub_eq_sub, inner_eq']; simp only [PiLp.sub_apply]; linarith
    exact absurd (InnerProductGeometry.inner_neg_iff_pi_div_two_lt_angle.1 hi) (not_lt.2 (show InnerProductGeometry.angle (A -ᵥ B) (C -ᵥ B) ≤ π / 2 from hB))
  have hk : 0 < a ^ 2 - m := by
    by_contra hneg
    push Not at hneg
    have hi : ⟪A -ᵥ C, B -ᵥ C⟫ ≤ 0 := by
      rw [vsub_eq_sub, vsub_eq_sub, inner_eq']; simp only [PiLp.sub_apply]
      linarith
    exact absurd (InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.1 hi) (not_le.2 (show InnerProductGeometry.angle (A -ᵥ C) (B -ᵥ C) < π / 2 from hC))
  have hX : 0 < a ^ 2 * c ^ 2 - m ^ 2 := by
    have : a ^ 2 * c ^ 2 - m ^ 2 = ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) ^ 2 := by
      rw [ha2, hc2, hm]; ring
    rw [this]; positivity
  have hmac : m ≤ a * c := by nlinarith [mul_pos ha hc]
  -- the foot of the altitude
  obtain ⟨l, hl0, hl1⟩ := line_coord hD
  have hlm : l * a ^ 2 = m := by
    rw [inner_eq'] at hAD; simp only [PiLp.sub_apply] at hAD
    rw [hl0, hl1] at hAD; rw [ha2, hm]; linear_combination -hAD
  have hl1' : 0 ≤ 1 - l := by nlinarith
  have hDC : dist D C * a = a ^ 2 - m := by
    have : dist D C = (1 - l) * a := by
      exact dist_scale hl1' (by rw [hl0]; ring) (by rw [hl1]; ring)
    rw [this]; linear_combination -hlm
  -- points of the base
  have hPt : ∀ P, P ∈ segment ℝ B C → ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ P 0 = B 0 + t * (C 0 - B 0) ∧
      P 1 = B 1 + t * (C 1 - B 1) ∧ dist P C = (1 - t) * a ∧ dist P B = t * a := by
    intro P hP
    obtain ⟨t, ht0, ht1, h0, h1⟩ := seg_coord hP
    refine ⟨t, ht0, ht1, h0, h1, dist_scale (by linarith) (by rw [h0]; ring) (by rw [h1]; ring),
      ?_⟩
    rw [show a = dist C B from dist_comm _ _]
    exact dist_scale ht0 (by rw [h0]; ring) (by rw [h1]; ring)
  have hratio : ∀ t : ℝ, (1 - t) * a * c = dist D C * (t * a) ↔
      (1 - t) * a ^ 2 * c = (a ^ 2 - m) * t * a := by
    intro t
    constructor
    · intro h; linear_combination a * h + (t * a) * hDC
    · intro h
      have : a * ((1 - t) * a * c - dist D C * (t * a)) = 0 := by
        linear_combination h - (t * a) * hDC
      have := (mul_eq_zero.1 this).resolve_left ha.ne'
      linear_combination this
  have key : ∀ P, EqualPerps A B C P ↔
      (P ∈ segment ℝ B C ∧ dist P C * c = dist D C * dist P B) := by
    intro P
    constructor
    · rintro ⟨hP, Q, hQ, R, hR, h1, h2, h3⟩
      refine ⟨hP, ?_⟩
      obtain ⟨t, ht0, ht1, hP0, hP1, hPC, hPB⟩ := hPt P hP
      obtain ⟨q, hq0, hq1, hQ0, hQ1⟩ := seg_coord hQ
      obtain ⟨p, -, -, hR0, hR1⟩ := seg_coord hR
      rw [inner_eq'] at h1 h2
      simp only [PiLp.sub_apply] at h1 h2
      rw [hP0, hP1, hQ0, hQ1] at h1
      rw [hP0, hP1, hR0, hR1] at h2
      have h3' := congrArg (· ^ 2) h3
      simp only [dist_sq'] at h3'
      rw [hP0, hP1, hQ0, hQ1, hR0, hR1] at h3'
      have := alg_forward (u0 := C 0 - B 0) (u1 := C 1 - B 1) (w0 := A 0 - B 0)
        (w1 := A 1 - B 1) (t := t) (s := 1 - q) (r := 1 - p) ha2 hc2 hm ha hc hX ht0
        (by linarith) (by linear_combination h1) (by linear_combination -h2)
        (by linear_combination h3')
      rw [hPC, hPB]
      exact (hratio t).2 this
    · rintro ⟨hP, hr⟩
      obtain ⟨t, ht0, ht1, hP0, hP1, hPC, hPB⟩ := hPt P hP
      rw [hPC, hPB] at hr
      obtain ⟨s, r, hs0, hs1, hr0, hr1, h1, h2, h3⟩ := alg_backward (u0 := C 0 - B 0)
        (u1 := C 1 - B 1) (w0 := A 0 - B 0) (w1 := A 1 - B 1) ha2 hc2 hm ha hc hm0 hk hmac
        ht0 ((hratio t).1 hr)
      refine ⟨hP, A + (1 - s) • (C - A),
        mem_seg_of _ _ _ (1 - s) (by linarith) (by linarith) (by simp) (by simp),
        A + (1 - r) • (B - A),
        mem_seg_of _ _ _ (1 - r) (by linarith) (by linarith) (by simp) (by simp), ?_, ?_, ?_⟩
      · rw [inner_eq']
        simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        rw [hP0, hP1]; linear_combination h1
      · rw [inner_eq']
        simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        rw [hP0, hP1]; linear_combination -h2
      · rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, dist_sq', dist_sq']
        simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        rw [hP0, hP1]; linear_combination h3
  refine ⟨key, ?_⟩
  have hden : 0 < a ^ 2 - m + a * c := by nlinarith [mul_pos ha hc]
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ * (a ^ 2 - m + a * c) = a * c :=
    ⟨a * c / (a ^ 2 - m + a * c), div_mul_cancel₀ _ hden.ne'⟩
  have ht₀0 : 0 ≤ t₀ := by nlinarith [mul_pos ha hc]
  have ht₀1 : t₀ ≤ 1 := by nlinarith
  have hP₀ : B + t₀ • (C - B) ∈ segment ℝ B C :=
    mem_seg_of _ _ _ t₀ ht₀0 ht₀1 (by simp) (by simp)
  refine ⟨B + t₀ • (C - B), (key _).2 ⟨hP₀, ?_⟩, ?_⟩
  · have hPC : dist (B + t₀ • (C - B)) C = (1 - t₀) * a :=
      dist_scale (by linarith) (by simp; ring) (by simp; ring)
    have hPB : dist (B + t₀ • (C - B)) B = t₀ * a := by
      rw [show a = dist C B from dist_comm _ _]
      exact dist_scale ht₀0 (by simp) (by simp)
    rw [hPC, hPB]
    exact (hratio t₀).2 (by linear_combination (-a) * ht₀)
  · intro P hP
    obtain ⟨hPs, hr⟩ := (key P).1 hP
    obtain ⟨t, -, -, hP0, hP1, hPC, hPB⟩ := hPt P hPs
    rw [hPC, hPB] at hr
    have h := (hratio t).1 hr
    have htt : t = t₀ := by
      have : a * ((t - t₀) * (a ^ 2 - m + a * c)) = 0 := by linear_combination -h - a * ht₀
      have := (mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_left ha.ne')).resolve_right hden.ne'
      linarith
    ext i; fin_cases i <;> simp [hP0, hP1, htt]

private lemma mem_line_of (p x y : Plane) (r : ℝ) (h0 : p 0 = x 0 + r * (y 0 - x 0))
    (h1 : p 1 = x 1 + r * (y 1 - x 1)) : p ∈ line[ℝ, x, y] := by
  refine mem_affineSpan_pair_iff_exists_lineMap_eq.2 ⟨r, ?_⟩
  rw [AffineMap.lineMap_apply_module']
  ext i; fin_cases i <;> simp [h0, h1] <;> ring

/-- The hypotheses of `problem20` are satisfiable: `A = (1, 2)`, `B = (0, 0)`, `C = (3, 0)`,
with altitude foot `D = (1, 0)`. -/
theorem problem20_nonvacuous :
    ∃ A B C D : Plane, cross A B C ≠ 0 ∧ ∠ A B C ≤ π / 2 ∧ ∠ A C B < π / 2 ∧
      D ∈ line[ℝ, B, C] ∧ ⟪A - D, C - B⟫ = 0 := by
  refine ⟨pt 1 2, pt 0 0, pt 3 0, pt 1 0, by norm_num [cross], ?_, ?_,
    mem_line_of _ _ _ (1 / 3) (by norm_num) (by norm_num), by rw [inner_eq']; simp⟩
  · by_contra h
    push Not at h
    have := InnerProductGeometry.inner_neg_iff_pi_div_two_lt_angle.2 h
    rw [vsub_eq_sub, vsub_eq_sub, inner_eq'] at this
    norm_num at this
  · by_contra h
    push Not at h
    have := InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.2 h
    rw [vsub_eq_sub, vsub_eq_sub, inner_eq'] at this
    norm_num at this

end PillowProblems.P20
