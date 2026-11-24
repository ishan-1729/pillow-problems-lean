import PillowProblems.Basic

/-!
# Problem 22 (Trigonometry: Plane)

**Question.** *(dated 4/6/89)*

> Given the 3 'altitudes' of a Triangle: find its (1) sides, (2) angles, (3) area.

**Answer.**

> Calling the given altitudes '\(\alpha\), \(\beta\), \(\gamma\)'; and the fraction \[ \frac{2\alpha^{2} \beta^{2} \gamma^{2} . (\alpha^{2} + \beta^{2} + \gamma^{2}) - (\beta^{4} \gamma^{4} + \gamma^{4} \alpha^{4} + \alpha^{4} \beta^{4})}{4\alpha^{4} \beta^{4} \gamma^{4}} \unicode{x2018}k^2\unicode{x2019},\]
>
> (1) \(\quad a = \dfrac{1}{k\alpha}, \,\,\&c.\)
>
> (2) \(\quad \sin A = k\beta \gamma, \,\,\&c.\)
>
> (3) \(\quad \text{area} = \dfrac{1}{2k}.\)

*(Carroll's solution: Chapter III, problem 22; text in `data/problems.json`.)*

**Lean reading.** The triangle `ABC` is a non-degenerate triangle in the plane (`cross A B C ≠ 0`). "The altitude
from `A` is `α`" is `IsAltitude A B C α`: the perpendicular from `A` meets the line `BC` at a
foot `H` with `AH = α` (the foot may lie outside the segment `BC`); similarly for `β` from `B`
and `γ` from `C`. Carroll's fraction is `kSq α β γ` and `k` is its positive square root
(Carroll's `k = sin A / (βγ)` is positive). The theorem proves that the fraction is positive and
that the sides, the sines of the angles (`∠ B A C` is the angle at `A`, etc.) and the area are
exactly Carroll's expressions; since the sides are determined, so is the triangle up to
congruence. Carroll answers part (2) through the sines, which fix each angle only up to its
supplement; we prove exactly that statement. Conversely, `problem22_exists` shows that any
positive `α, β, γ` with `k² > 0` are the altitudes of some triangle, so Carroll's formulae answer
the question for every admissible set of data; `problem22_nonvacuous` exhibits the 3-4-5
triangle with altitudes `3, 12/5, 4`.

**Status.** proved
-/

namespace PillowProblems.P22

open scoped EuclideanGeometry
open AffineMap

/-- `h` is the altitude of the triangle `ABC` drawn from `A`: the perpendicular from `A` to the
line `BC` meets it at a foot `H`, and `AH = h`. -/
def IsAltitude (A B C : Plane) (h : ℝ) : Prop :=
  ∃ t : ℝ, inner ℝ (A - lineMap B C t) (C - B) = 0 ∧ dist A (lineMap B C t) = h

/-- Carroll's fraction `k²`, in terms of the three altitudes `α, β, γ`. -/
noncomputable def kSq (α β γ : ℝ) : ℝ :=
  (2 * α ^ 2 * β ^ 2 * γ ^ 2 * (α ^ 2 + β ^ 2 + γ ^ 2) -
      (β ^ 4 * γ ^ 4 + γ ^ 4 * α ^ 4 + α ^ 4 * β ^ 4)) / (4 * α ^ 4 * β ^ 4 * γ ^ 4)

private lemma dist_sq' (X Y : Plane) : dist X Y ^ 2 = (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma inner' (X Y : Plane) : inner ℝ X Y = X 0 * Y 0 + X 1 * Y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- An altitude times its base is twice the area. -/
private lemma altitude_mul {A B C : Plane} {h : ℝ} (hh : IsAltitude A B C h) :
    h * dist B C = |cross A B C| := by
  obtain ⟨t, hperp, rfl⟩ := hh
  set H := lineMap B C t with hHdef
  have hHeq : H = t • (C - B) + B := by rw [hHdef, AffineMap.lineMap_apply_module']
  have hH0 : H 0 = t * (C 0 - B 0) + B 0 := by rw [hHeq]; simp
  have hH1 : H 1 = t * (C 1 - B 1) + B 1 := by rw [hHeq]; simp
  have h1 := dist_sq' A H
  have h2 := dist_sq' B C
  rw [inner'] at hperp
  simp only [PiLp.sub_apply] at hperp
  rw [hH0, hH1] at hperp
  have key : (dist A H * dist B C) ^ 2 = cross A B C ^ 2 := by
    rw [mul_pow, h1, h2, hH0, hH1]
    unfold cross
    linear_combination ((A 0 - (t * (C 0 - B 0) + B 0)) * (C 0 - B 0) +
      (A 1 - (t * (C 1 - B 1) + B 1)) * (C 1 - B 1)) * hperp
  rw [← Real.sqrt_sq (by positivity : 0 ≤ dist A H * dist B C), key, Real.sqrt_sq_eq_abs]

private lemma dist_eq_of_sq {X Y : Plane} {r : ℝ} (hr : 0 ≤ r)
    (h : (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 = r ^ 2) : dist X Y = r := by
  rw [← Real.sqrt_sq hr, ← h, ← dist_sq', Real.sqrt_sq dist_nonneg]

/-- `sin A · AB · AC = 2 · area`. -/
private lemma sin_angle_mul (A B C : Plane) :
    Real.sin (∠ B A C) * (dist A B * dist A C) = |cross A B C| := by
  rw [EuclideanGeometry.angle, dist_comm A B, dist_comm A C, dist_eq_norm_vsub Plane B A,
    dist_eq_norm_vsub Plane C A, InnerProductGeometry.sin_angle_mul_norm_mul_norm,
    ← Real.sqrt_sq_eq_abs]
  congr 1
  simp only [vsub_eq_sub, inner']
  simp only [PiLp.sub_apply]
  unfold cross
  ring

/-- **Problem 22.** In a triangle whose altitudes from `A`, `B`, `C` are `α`, `β`, `γ`, with
`k = √(k²)` for Carroll's fraction `k²`: the fraction is positive, the sides are
`a = 1/(kα)`, `b = 1/(kβ)`, `c = 1/(kγ)`, the angles have `sin A = kβγ`, `sin B = kγα`,
`sin C = kαβ`, and the area is `1/(2k)`. -/
theorem problem22 (A B C : Plane) (hABC : cross A B C ≠ 0) (α β γ : ℝ)
    (hα : IsAltitude A B C α) (hβ : IsAltitude B C A β) (hγ : IsAltitude C A B γ) :
    0 < kSq α β γ ∧
    (dist B C = 1 / (Real.sqrt (kSq α β γ) * α) ∧ dist C A = 1 / (Real.sqrt (kSq α β γ) * β) ∧
      dist A B = 1 / (Real.sqrt (kSq α β γ) * γ)) ∧
    (Real.sin (∠ B A C) = Real.sqrt (kSq α β γ) * β * γ ∧
      Real.sin (∠ C B A) = Real.sqrt (kSq α β γ) * γ * α ∧
      Real.sin (∠ A C B) = Real.sqrt (kSq α β γ) * α * β) ∧
    triArea A B C = 1 / (2 * Real.sqrt (kSq α β γ)) := by
  set K := cross A B C with hK
  set Q := |K| with hQ
  have hQ0 : 0 < Q := abs_pos.2 hABC
  have hBCA : cross B C A = K := by rw [hK]; unfold cross; ring
  have hCAB : cross C A B = K := by rw [hK]; unfold cross; ring
  have ha := altitude_mul hα
  have hb := altitude_mul hβ
  have hc := altitude_mul hγ
  rw [← hK, ← hQ] at ha
  rw [hBCA, ← hQ] at hb
  rw [hCAB, ← hQ] at hc
  set a := dist B C with ha_def
  set b := dist C A with hb_def
  set c := dist A B with hc_def
  have ha0 : 0 ≤ a := dist_nonneg
  have hb0 : 0 ≤ b := dist_nonneg
  have hc0 : 0 ≤ c := dist_nonneg
  have ha' : a ≠ 0 := by rintro h; rw [h, mul_zero] at ha; linarith
  have hb' : b ≠ 0 := by rintro h; rw [h, mul_zero] at hb; linarith
  have hc' : c ≠ 0 := by rintro h; rw [h, mul_zero] at hc; linarith
  have hα' : α = Q / a := by field_simp; linarith
  have hβ' : β = Q / b := by field_simp; linarith
  have hγ' : γ = Q / c := by field_simp; linarith
  -- Heron's identity in coordinates
  have hHeron : 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - (a ^ 4 + b ^ 4 + c ^ 4) =
      4 * Q ^ 2 := by
    rw [hQ, sq_abs, ha_def, hb_def, hc_def,
      show dist B C ^ 4 = (dist B C ^ 2) ^ 2 by ring,
      show dist C A ^ 4 = (dist C A ^ 2) ^ 2 by ring,
      show dist A B ^ 4 = (dist A B ^ 2) ^ 2 by ring, dist_sq', dist_sq', dist_sq', hK]
    unfold cross
    ring
  have hk2 : kSq α β γ = 1 / Q ^ 2 := by
    rw [hα', hβ', hγ']
    unfold kSq
    field_simp
    linear_combination hHeron
  have hk : Real.sqrt (kSq α β γ) = 1 / Q := by
    rw [hk2, Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
    field_simp
  have hsA : Real.sin (∠ B A C) * (c * b) = Q := by
    have := sin_angle_mul A B C
    rw [dist_comm A C] at this
    exact this
  have hsB : Real.sin (∠ C B A) * (a * c) = Q := by
    have := sin_angle_mul B C A
    rw [dist_comm B A, hBCA] at this
    exact this
  have hsC : Real.sin (∠ A C B) * (b * a) = Q := by
    have := sin_angle_mul C A B
    rw [dist_comm C B, hCAB] at this
    exact this
  refine ⟨by rw [hk2]; positivity, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hk, hα']; field_simp
  · rw [hk, hβ']; field_simp
  · rw [hk, hγ']; field_simp
  · rw [hk, hβ', hγ']
    field_simp
    linear_combination hsA
  · rw [hk, hγ', hα']
    field_simp
    linear_combination hsB
  · rw [hk, hα', hβ']
    field_simp
    linear_combination hsC
  · rw [hk]
    unfold triArea
    field_simp
    rfl

private lemma lineMap_coord (X Y : Plane) (t : ℝ) (i : Fin 2) :
    (lineMap X Y t : Plane) i = X i + t * (Y i - X i) := by
  simp [AffineMap.lineMap_apply]; ring

/-- In a triangle with `B ≠ C`, the perpendicular from `A` to the line `BC` has length
`|cross A B C| / BC`. -/
private lemma isAltitude_of (A B C : Plane) (hBC : B ≠ C) :
    IsAltitude A B C (|cross A B C| / dist B C) := by
  have hn2 := dist_sq' B C
  have hS' : dist B C ^ 2 = (C 0 - B 0) ^ 2 + (C 1 - B 1) ^ 2 := by rw [hn2]; ring
  have hS0 : (C 0 - B 0) ^ 2 + (C 1 - B 1) ^ 2 ≠ 0 := by
    rw [← hS']; exact pow_ne_zero 2 (dist_ne_zero.2 hBC)
  refine ⟨((A 0 - B 0) * (C 0 - B 0) + (A 1 - B 1) * (C 1 - B 1)) /
    ((C 0 - B 0) ^ 2 + (C 1 - B 1) ^ 2), ?_, ?_⟩
  · rw [inner']
    simp only [PiLp.sub_apply, lineMap_coord]
    field_simp
    ring
  · apply dist_eq_of_sq (by positivity)
    rw [div_pow, sq_abs, hS', lineMap_coord, lineMap_coord]
    unfold cross
    field_simp
    ring

/-- The algebraic identity behind `problem22_exists`. -/
private lemma key_identity {α β γ k : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hk : 0 < k)
    (hk2 : k ^ 2 * (4 * α ^ 4 * β ^ 4 * γ ^ 4) =
      2 * α ^ 2 * β ^ 2 * γ ^ 2 * (α ^ 2 + β ^ 2 + γ ^ 2) -
        (β ^ 4 * γ ^ 4 + γ ^ 4 * α ^ 4 + α ^ 4 * β ^ 4)) :
    ((1 / (k * α)) ^ 2 + (1 / (k * γ)) ^ 2 - (1 / (k * β)) ^ 2) ^ 2 / (2 * (1 / (k * α))) ^ 2
      + α ^ 2 = (1 / (k * γ)) ^ 2 := by
  field_simp
  linear_combination hk2

/-- **Problem 22, existence.** Conversely, any three positive lengths `α, β, γ` for which
Carroll's fraction `k²` is positive are the altitudes of some triangle (so, with `problem22`,
three positive lengths are the altitudes of a triangle exactly when `k² > 0`, and the triangle is
then determined up to congruence by Carroll's formulae). -/
theorem problem22_exists (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hk : 0 < kSq α β γ) :
    ∃ A B C : Plane, cross A B C ≠ 0 ∧ IsAltitude A B C α ∧ IsAltitude B C A β ∧
      IsAltitude C A B γ := by
  obtain ⟨k, hk_def⟩ : ∃ k, k = Real.sqrt (kSq α β γ) := ⟨_, rfl⟩
  have hk0 : 0 < k := by rw [hk_def]; exact Real.sqrt_pos.2 hk
  have hk2 : k ^ 2 = kSq α β γ := by rw [hk_def]; exact Real.sq_sqrt hk.le
  unfold kSq at hk2
  rw [eq_div_iff (by positivity)] at hk2
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / (k * α) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 1 / (k * β) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (k * γ) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  have hc0 : 0 < c := by rw [hc]; positivity
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (a ^ 2 + c ^ 2 - b ^ 2) / (2 * a) := ⟨_, rfl⟩
  have hx1 : x ^ 2 + α ^ 2 = c ^ 2 := by
    rw [hx, div_pow, ha, hb, hc]; exact key_identity hα hβ hγ hk0 hk2
  have hx2 : 2 * a * x = a ^ 2 + c ^ 2 - b ^ 2 := by rw [hx]; field_simp
  have haα : a * α = 1 / k := by rw [ha]; field_simp
  have hBC : dist (pt 0 0) (pt a 0) = a :=
    dist_eq_of_sq ha0.le (by simp only [pt_zero, pt_one]; ring)
  have hCA : dist (pt a 0) (pt x α) = b :=
    dist_eq_of_sq hb0.le (by simp only [pt_zero, pt_one]; linear_combination hx1 - hx2)
  have hAB : dist (pt x α) (pt 0 0) = c :=
    dist_eq_of_sq hc0.le (by simp only [pt_zero, pt_one]; linear_combination hx1)
  have hK1 : cross (pt x α) (pt 0 0) (pt a 0) = a * α := by
    unfold cross; simp only [pt_zero, pt_one]; ring
  have hK2 : cross (pt 0 0) (pt a 0) (pt x α) = a * α := by
    unfold cross; simp only [pt_zero, pt_one]; ring
  have hK3 : cross (pt a 0) (pt x α) (pt 0 0) = a * α := by
    unfold cross; simp only [pt_zero, pt_one]; ring
  refine ⟨pt x α, pt 0 0, pt a 0, by rw [hK1]; positivity, ?_, ?_, ?_⟩
  · have h := isAltitude_of (pt x α) (pt 0 0) (pt a 0) (dist_pos.1 (by rw [hBC]; exact ha0))
    rw [hK1, hBC, abs_of_pos (by positivity)] at h
    convert h using 1
    field_simp
  · have h := isAltitude_of (pt 0 0) (pt a 0) (pt x α) (dist_pos.1 (by rw [hCA]; exact hb0))
    rw [hK2, hCA, abs_of_pos (by positivity), haα, hb] at h
    convert h using 1
    field_simp
  · have h := isAltitude_of (pt a 0) (pt x α) (pt 0 0) (dist_pos.1 (by rw [hAB]; exact hc0))
    rw [hK3, hAB, abs_of_pos (by positivity), haα, hc] at h
    convert h using 1
    field_simp

/-- A concrete triangle (the 3-4-5 right triangle `A = (0,3)`, `B = (0,0)`, `C = (4,0)`) with
altitudes `3`, `12/5`, `4`: the hypotheses of `problem22` are satisfiable. -/
theorem problem22_nonvacuous :
    cross (pt 0 3) (pt 0 0) (pt 4 0) ≠ 0 ∧ IsAltitude (pt 0 3) (pt 0 0) (pt 4 0) 3 ∧
      IsAltitude (pt 0 0) (pt 4 0) (pt 0 3) (12 / 5) ∧
      IsAltitude (pt 4 0) (pt 0 3) (pt 0 0) 4 := by
  refine ⟨?_, ⟨0, ?_, ?_⟩, ⟨16 / 25, ?_, ?_⟩, ⟨1, ?_, ?_⟩⟩
  · unfold cross; simp
  · rw [inner']; norm_num [AffineMap.lineMap_apply_module']
  · apply dist_eq_of_sq (by norm_num); norm_num [AffineMap.lineMap_apply_module']
  · rw [inner']; norm_num [AffineMap.lineMap_apply_module']
  · apply dist_eq_of_sq (by norm_num); norm_num [AffineMap.lineMap_apply_module']
  · rw [inner']; norm_num [AffineMap.lineMap_apply_module']
  · apply dist_eq_of_sq (by norm_num); norm_num [AffineMap.lineMap_apply_module']

end PillowProblems.P22
