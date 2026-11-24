import PillowProblems.Basic

/-!
# Problem 24 (Pure Geometry, Plane)

**Question.** *(dated 5/86)*

> If, from the vertices of a triangle \(ABC\), the lines \(AD\), \(BE\), \(CF\) be drawn, intersecting at \(O\): find the ratio \(\dfrac{DO}{DA}\) in terms of the two ratios \(\dfrac{EO}{EB}\), \(\dfrac{FO}{FC}\).
>
> [Figure: A geometric diagram of triangle ABC with three cevians meeting at interior point O, creating points D, E, F on the sides.]

**Answer.**

> \(\dfrac{DO}{DA} + \dfrac{EO}{EB} + \dfrac{FO}{FC} = 1\); whence any one can be found in terms of the other two.

*(Carroll's solution: Chapter III, problem 24; text in `data/problems.json`.)*

**Lean reading.** The triangle `ABC` is nondegenerate (`cross A B C ≠ 0`). Following Carroll's
figure, `O` is a point strictly inside the triangle, written with positive barycentric weights
`O = α A + β B + γ C`, `α + β + γ = 1`; this is needed, since for an exterior `O` the relation
holds only with signed ratios. `D`, `E`, `F` lie on the lines `BC`, `CA`, `AB` and `O` lies on each
of the lines `AD`, `BE`, `CF` (so `D`, `E`, `F` are the feet of the three cevians through `O`).
The ratios are ratios of lengths, `DO / DA = dist D O / dist D A`, etc. Carroll's answer is the
relation `DO/DA + EO/EB + FO/FC = 1`, stated together with the solved form
`DO/DA = 1 - EO/EB - FO/FC`. The proof shows, as Carroll does with areas, that the three ratios
are the barycentric weights `α`, `β`, `γ`; `problem24_nonvacuous` exhibits the centroid case.

**Status.** proved
-/

namespace PillowProblems.P24

open EuclideanGeometry


private lemma dist_eq' (x y : Plane) : dist x y = Real.sqrt ((x 0 - y 0)^2 + (x 1 - y 1)^2) := by
  simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma line_coord {p x y : Plane} (h : p ∈ line[ℝ, x, y]) :
    ∃ r : ℝ, p 0 = x 0 + r * (y 0 - x 0) ∧ p 1 = x 1 + r * (y 1 - x 1) := by
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 h
  refine ⟨r, ?_, ?_⟩ <;> (rw [← hr, AffineMap.lineMap_apply_module']; simp; ring)

private lemma indep {u0 u1 v0 v1 p q : ℝ} (h : u0 * v1 - v0 * u1 ≠ 0)
    (h0 : p * u0 + q * v0 = 0) (h1 : p * u1 + q * v1 = 0) : p = 0 ∧ q = 0 := by
  constructor
  · have : p * (u0 * v1 - v0 * u1) = 0 := by linear_combination v1 * h0 - v0 * h1
    simpa [h] using this
  · have : q * (u0 * v1 - v0 * u1) = 0 := by linear_combination u0 * h1 - u1 * h0
    simpa [h] using this

/-- The ratio cut off on one cevian: `DO / DA` is the barycentric weight of `A` in `O`. -/
private lemma cevian (A B C D O : Plane) (hABC : cross A B C ≠ 0) (α β γ : ℝ)
    (hβ : 0 < β) (hs : α + β + γ = 1) (hO : O = α • A + β • B + γ • C)
    (hD : D ∈ line[ℝ, B, C]) (hAD : O ∈ line[ℝ, A, D]) (hα : 0 < α) :
    dist D O / dist D A = α := by
  obtain ⟨l, hl0, hl1⟩ := line_coord hD
  obtain ⟨m, hm0, hm1⟩ := line_coord hAD
  have hO0 : O 0 = α * A 0 + β * B 0 + γ * C 0 := by rw [hO]; simp
  have hO1 : O 1 = α * A 1 + β * B 1 + γ * C 1 := by rw [hO]; simp
  unfold cross at hABC
  obtain ⟨e1, e2⟩ := indep (p := β - m * (1 - l)) (q := γ - m * l) hABC
    (by rw [hO0, hl0] at hm0; linear_combination hm0 - A 0 * hs)
    (by rw [hO1, hl1] at hm1; linear_combination hm1 - A 1 * hs)
  have hm : m = 1 - α := by
    linear_combination -e1 - e2 + hs
  have k0 : D 0 - O 0 = α * (D 0 - A 0) := by rw [hm] at hm0; linear_combination -hm0
  have k1 : D 1 - O 1 = α * (D 1 - A 1) := by rw [hm] at hm1; linear_combination -hm1
  have hDA : dist D A ≠ 0 := by
    intro h0
    rw [dist_eq_zero] at h0
    have d0 : D 0 = A 0 := by rw [h0]
    have d1 : D 1 = A 1 := by rw [h0]
    have := (indep (p := β) (q := γ) hABC
      (by rw [hO0, d0] at hm0; linear_combination hm0 - A 0 * hs)
      (by rw [hO1, d1] at hm1; linear_combination hm1 - A 1 * hs)).1
    linarith
  rw [div_eq_iff hDA, dist_eq', dist_eq', k0, k1]
  rw [show (α * (D 0 - A 0)) ^ 2 + (α * (D 1 - A 1)) ^ 2 = α^2 * ((D 0 - A 0) ^ 2 + (D 1 - A 1) ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hα.le]

/-- **Problem 24.** For cevians `AD`, `BE`, `CF` of a triangle meeting at an interior point `O`,
`DO/DA + EO/EB + FO/FC = 1`; hence `DO/DA = 1 - EO/EB - FO/FC`. -/
theorem problem24 (A B C D E F O : Plane) (hABC : cross A B C ≠ 0)
    (hO : ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧ O = α • A + β • B + γ • C)
    (hD : D ∈ line[ℝ, B, C]) (hE : E ∈ line[ℝ, C, A]) (hF : F ∈ line[ℝ, A, B])
    (hAD : O ∈ line[ℝ, A, D]) (hBE : O ∈ line[ℝ, B, E]) (hCF : O ∈ line[ℝ, C, F]) :
    dist D O / dist D A + dist E O / dist E B + dist F O / dist F C = 1 ∧
      dist D O / dist D A = 1 - dist E O / dist E B - dist F O / dist F C := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hs, hO⟩ := hO
  have h1 := cevian A B C D O hABC α β γ hβ hs hO hD hAD hα
  have h2 := cevian B C A E O (by unfold cross at hABC ⊢; intro h; apply hABC; linear_combination h)
    β γ α hγ (by linear_combination hs) (by rw [hO]; abel) hE hBE hβ
  have h3 := cevian C A B F O (by unfold cross at hABC ⊢; intro h; apply hABC; linear_combination h)
    γ α β hα (by linear_combination hs) (by rw [hO]; abel) hF hCF hγ
  rw [h1, h2, h3]
  exact ⟨hs, by linear_combination hs⟩

private lemma mem_line_of (p x y : Plane) (r : ℝ) (h0 : p 0 = x 0 + r * (y 0 - x 0))
    (h1 : p 1 = x 1 + r * (y 1 - x 1)) : p ∈ line[ℝ, x, y] := by
  refine mem_affineSpan_pair_iff_exists_lineMap_eq.2 ⟨r, ?_⟩
  rw [AffineMap.lineMap_apply_module']
  ext i; fin_cases i <;> simp [h0, h1] <;> ring

/-- The hypotheses of `problem24` are satisfiable: the medians of a right isosceles triangle. -/
theorem problem24_nonvacuous :
    ∃ A B C D E F O : Plane, cross A B C ≠ 0 ∧
      (∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧ O = α • A + β • B + γ • C) ∧
      D ∈ line[ℝ, B, C] ∧ E ∈ line[ℝ, C, A] ∧ F ∈ line[ℝ, A, B] ∧
      O ∈ line[ℝ, A, D] ∧ O ∈ line[ℝ, B, E] ∧ O ∈ line[ℝ, C, F] := by
  refine ⟨pt 0 0, pt 1 0, pt 0 1, pt (1/2) (1/2), pt 0 (1/2), pt (1/2) 0, pt (1/3) (1/3),
    by norm_num [cross], ⟨1/3, 1/3, 1/3, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩,
    mem_line_of _ _ _ (1/2) (by norm_num) (by norm_num),
    mem_line_of _ _ _ (1/2) (by norm_num) (by norm_num),
    mem_line_of _ _ _ (1/2) (by norm_num) (by norm_num),
    mem_line_of _ _ _ (2/3) (by norm_num) (by norm_num),
    mem_line_of _ _ _ (2/3) (by norm_num) (by norm_num),
    mem_line_of _ _ _ (2/3) (by norm_num) (by norm_num)⟩
  ext i; fin_cases i <;> simp

end PillowProblems.P24
