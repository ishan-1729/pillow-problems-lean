import PillowProblems.Basic

/-!
# Problem 64 (Pure Geometry, Plane)

**Question.** *(dated 18/12/74)*

> Given a Triangle, and a Point within it such that its distance from one of the sides is less than its distance from either of the others: describe a Circle, with given Point as centre, such that its intercepts on the sides may be equal to the sides of a right-angled Triangle.

*(Carroll's solution: Chapter III, problem 64; text in `data/problems.json`.)*

**Lean reading.** The triangle is nondegenerate (`cross A B C ≠ 0`); `D, E, F` are the feet of the
perpendiculars from `O` on the lines `BC, CA, AB` (`IsFoot`), and `OD < OE`, `OD < OF`. The
hypothesis that `O` lies within the triangle is not needed and is dropped, so the theorem is
slightly stronger than asked. The intercept of the circle on a side is the chord `MN` it cuts
from the line of that side (`Intercept`: two distinct points of the line at distance `r` from
`O`); as in Carroll's solution the circle "cuts all three Lines", and the chord may run past the
ends of the side. This is a reading of "intercepts on the sides": if the intercept had to be the
part of the chord lying on the side segment, Carroll's circle can fail (in the instance of
`problem64_nonvacuous` the chord on the line `AB` runs past `B`, so its part on the side `AB` is
shorter than the chord and the three intercepts no longer satisfy Pythagoras). "Equal to the sides of a right-angled Triangle" is read through Pythagoras and
its converse (`RightTriangleSides`: positive, one square equals the sum of the other two).
`problem64` proves that the circle of radius `√(OE² + OF² - OD²)` (Carroll's `LH`, with
`KL = OD` and `KL² + LH² = GH² + GK² = OE² + OF²`) works, the intercept on `BC` being the
hypotenuse, and that it is the only such circle.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P64

open scoped EuclideanGeometry RealInnerProductSpace

/-- `D` is the foot of the perpendicular from `O` on the line `XY`. -/
def IsFoot (O X Y D : Plane) : Prop :=
  D ∈ line[ℝ, X, Y] ∧ ⟪O - D, Y - X⟫ = 0

/-- The circle with centre `O` and radius `r` cuts the line `XY` in two distinct points `M`, `N`,
and its intercept `MN` on that line has length `ℓ`. -/
def Intercept (O : Plane) (r : ℝ) (X Y : Plane) (ℓ : ℝ) : Prop :=
  ∃ M N : Plane, M ∈ line[ℝ, X, Y] ∧ N ∈ line[ℝ, X, Y] ∧ M ≠ N ∧
    dist M O = r ∧ dist N O = r ∧ dist M N = ℓ

/-- `p, q, r` are the sides of a right-angled triangle (in some order): they are positive and,
by Pythagoras and its converse, the square of one of them is the sum of the squares of the
other two. -/
def RightTriangleSides (p q r : ℝ) : Prop :=
  0 < p ∧ 0 < q ∧ 0 < r ∧ (p ^ 2 = q ^ 2 + r ^ 2 ∨ q ^ 2 = r ^ 2 + p ^ 2 ∨ r ^ 2 = p ^ 2 + q ^ 2)

private lemma inner2 (P Q : Plane) : ⟪P, Q⟫ = P 0 * Q 0 + P 1 * Q 1 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]; ring

private lemma distsq2 (P Q : Plane) : dist P Q ^ 2 = (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]; simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma ext2 {P Q : Plane} (h0 : P 0 = Q 0) (h1 : P 1 = Q 1) : P = Q := by
  ext i; fin_cases i <;> simp [h0, h1]

private lemma mem_line {B C X : Plane} : X ∈ line[ℝ, B, C] ↔ ∃ t : ℝ, X = B + t • (C - B) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  constructor
  · rintro ⟨t, ht⟩; exact ⟨t, by rw [← ht]; abel⟩
  · rintro ⟨t, ht⟩; exact ⟨t, by rw [ht]; abel⟩

/-- Pythagoras along a line: if `D` is the foot from `O` on `XY` and `M = X + μ (Y - X)`,
`D = X + δ (Y - X)`, then `OM² = OD² + (μ - δ)² XY²`. -/
private lemma pyth {O X Y D : Plane} {δ μ : ℝ} (hD : D = X + δ • (Y - X))
    (hperp : ⟪O - D, Y - X⟫ = 0) :
    dist (X + μ • (Y - X)) O ^ 2 = dist O D ^ 2 + (μ - δ) ^ 2 * dist X Y ^ 2 := by
  rw [inner2] at hperp
  rw [distsq2, distsq2, distsq2]
  subst hD
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hperp ⊢
  linear_combination (-2 * (μ - δ)) * hperp

/-- The intercept of a circle on a line: `ℓ > 0`, `ℓ² = 4 (r² - d²)` with `d < r`, where `d` is
the distance of the centre from the line. -/
private lemma chord {O X Y D : Plane} {r ℓ : ℝ} (hXY : X ≠ Y) (hD : IsFoot O X Y D)
    (h : Intercept O r X Y ℓ) : 0 < ℓ ∧ ℓ ^ 2 = 4 * (r ^ 2 - dist O D ^ 2) ∧ dist O D < r := by
  obtain ⟨hδ, hperp⟩ := hD
  obtain ⟨δ, rfl⟩ := mem_line.1 hδ
  obtain ⟨M, N, hM, hN, hMN, hMO, hNO, rfl⟩ := h
  refine ⟨dist_pos.2 hMN, ?_⟩
  obtain ⟨μ, rfl⟩ := mem_line.1 hM
  obtain ⟨ν, rfl⟩ := mem_line.1 hN
  have hL : 0 < dist X Y := dist_pos.2 hXY
  have e1 := pyth (μ := μ) rfl hperp
  have e2 := pyth (μ := ν) rfl hperp
  rw [hMO] at e1; rw [hNO] at e2
  have hμν : μ - ν ≠ 0 := by
    intro h; apply hMN; rw [sub_eq_zero.1 h]
  have hsum : μ + ν - 2 * δ = 0 := by
    have : ((μ - ν) * (μ + ν - 2 * δ)) * dist X Y ^ 2 = 0 := by linear_combination e2 - e1
    exact (mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (by positivity))).resolve_left hμν
  have hMN2 : dist (X + μ • (Y - X)) (X + ν • (Y - X)) ^ 2 = (μ - ν) ^ 2 * dist X Y ^ 2 := by
    rw [distsq2, distsq2]
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  refine ⟨?_, ?_⟩
  · rw [hMN2]
    have : μ - ν = 2 * (μ - δ) := by linear_combination -hsum
    rw [this]; linear_combination -4 * e1
  · have hμδ : μ - δ ≠ 0 := by
      intro h; apply hμν; linear_combination 2 * h - hsum
    have hr : 0 ≤ r := hMO ▸ dist_nonneg
    have : dist O (X + δ • (Y - X)) ^ 2 < r ^ 2 := by
      rw [e1]; have := pow_pos (abs_pos.2 hμδ) 2; rw [sq_abs] at this
      have := mul_pos this (pow_pos hL 2); linarith
    nlinarith [dist_nonneg (x := O) (y := X + δ • (Y - X))]

/-- A circle whose centre is nearer to a line than its radius cuts the line in two points. -/
private lemma exists_chord {O X Y D : Plane} {r : ℝ} (hXY : X ≠ Y) (hD : IsFoot O X Y D)
    (hr : dist O D < r) : ∃ ℓ, Intercept O r X Y ℓ := by
  obtain ⟨hδ, hperp⟩ := hD
  obtain ⟨δ, rfl⟩ := mem_line.1 hδ
  have hL : 0 < dist X Y := dist_pos.2 hXY
  set d := dist O (X + δ • (Y - X))
  have hd : 0 ≤ d := dist_nonneg
  set σ := √(r ^ 2 - d ^ 2) / dist X Y
  have hσ : 0 < σ := div_pos (Real.sqrt_pos.2 (by nlinarith)) hL
  have hσ2 : σ ^ 2 * dist X Y ^ 2 = r ^ 2 - d ^ 2 := by
    simp only [σ, div_pow, Real.sq_sqrt (by nlinarith : 0 ≤ r ^ 2 - d ^ 2)]
    field_simp
  have hrad : ∀ μ, (μ - δ) ^ 2 = σ ^ 2 → dist (X + μ • (Y - X)) O = r := by
    intro μ hμ
    have := pyth (μ := μ) rfl hperp
    rw [hμ, hσ2] at this
    exact (pow_left_inj₀ dist_nonneg (by linarith) two_ne_zero).1 (by rw [this]; ring)
  refine ⟨_, X + (δ + σ) • (Y - X), X + (δ - σ) • (Y - X), mem_line.2 ⟨_, rfl⟩,
    mem_line.2 ⟨_, rfl⟩, ?_, hrad _ (by ring), hrad _ (by ring), rfl⟩
  intro h
  have := congrArg (fun P => dist X P) h
  have h0 := congrArg (· 0) h
  have h1 := congrArg (· 1) h
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at h0 h1
  have : (2 * σ) ^ 2 * dist X Y ^ 2 = 0 := by
    rw [distsq2]; linear_combination (2 * σ * (Y 0 - X 0)) * h0 + (2 * σ * (Y 1 - X 1)) * h1
  have := mul_eq_zero.1 this
  rcases this with h | h
  · nlinarith
  · nlinarith

private lemma ne_of_cross {A B C : Plane} (hT : cross A B C ≠ 0) : A ≠ B ∧ B ≠ C ∧ C ≠ A := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> apply hT <;> simp only [cross] <;> ring

theorem problem64 (A B C O D E F : Plane) (hT : cross A B C ≠ 0)
    (hD : IsFoot O B C D) (hE : IsFoot O C A E) (hF : IsFoot O A B F)
    (hDE : dist O D < dist O E) (hDF : dist O D < dist O F) :
    (∃ ℓ₁ ℓ₂ ℓ₃ : ℝ,
        Intercept O √(dist O E ^ 2 + dist O F ^ 2 - dist O D ^ 2) B C ℓ₁ ∧
        Intercept O √(dist O E ^ 2 + dist O F ^ 2 - dist O D ^ 2) C A ℓ₂ ∧
        Intercept O √(dist O E ^ 2 + dist O F ^ 2 - dist O D ^ 2) A B ℓ₃ ∧
        ℓ₁ ^ 2 = ℓ₂ ^ 2 + ℓ₃ ^ 2 ∧ RightTriangleSides ℓ₁ ℓ₂ ℓ₃) ∧
    ∀ r ℓ₁ ℓ₂ ℓ₃ : ℝ, Intercept O r B C ℓ₁ → Intercept O r C A ℓ₂ → Intercept O r A B ℓ₃ →
      RightTriangleSides ℓ₁ ℓ₂ ℓ₃ → r = √(dist O E ^ 2 + dist O F ^ 2 - dist O D ^ 2) := by
  obtain ⟨hAB, hBC, hCA⟩ := ne_of_cross hT
  have hd1 : 0 ≤ dist O D := dist_nonneg
  have hd12 : dist O D ^ 2 < dist O E ^ 2 := by nlinarith
  have hd13 : dist O D ^ 2 < dist O F ^ 2 := by nlinarith
  constructor
  · set r := √(dist O E ^ 2 + dist O F ^ 2 - dist O D ^ 2)
    have hr2 : r ^ 2 = dist O E ^ 2 + dist O F ^ 2 - dist O D ^ 2 := Real.sq_sqrt (by nlinarith)
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have lt : ∀ x : ℝ, 0 ≤ x → x ^ 2 < r ^ 2 → x < r := fun x hx h => by nlinarith
    obtain ⟨ℓ₁, h₁⟩ := exists_chord hBC hD (lt _ hd1 (by nlinarith))
    obtain ⟨ℓ₂, h₂⟩ := exists_chord hCA hE (lt _ dist_nonneg (by nlinarith))
    obtain ⟨ℓ₃, h₃⟩ := exists_chord hAB hF (lt _ dist_nonneg (by nlinarith))
    obtain ⟨p₁, c₁, -⟩ := chord hBC hD h₁
    obtain ⟨p₂, c₂, -⟩ := chord hCA hE h₂
    obtain ⟨p₃, c₃, -⟩ := chord hAB hF h₃
    have hyp : ℓ₁ ^ 2 = ℓ₂ ^ 2 + ℓ₃ ^ 2 := by rw [c₁, c₂, c₃, hr2]; ring
    exact ⟨ℓ₁, ℓ₂, ℓ₃, h₁, h₂, h₃, hyp, p₁, p₂, p₃, Or.inl hyp⟩
  · intro r ℓ₁ ℓ₂ ℓ₃ h₁ h₂ h₃ hR
    obtain ⟨-, c₁, l₁⟩ := chord hBC hD h₁
    obtain ⟨-, c₂, l₂⟩ := chord hCA hE h₂
    obtain ⟨-, c₃, l₃⟩ := chord hAB hF h₃
    have hr0 : 0 ≤ r := by linarith
    have q₂ : dist O E ^ 2 < r ^ 2 := by nlinarith [dist_nonneg (x := O) (y := E)]
    have q₃ : dist O F ^ 2 < r ^ 2 := by nlinarith [dist_nonneg (x := O) (y := F)]
    obtain ⟨-, -, -, h | h | h⟩ := hR
    · rw [← Real.sqrt_sq hr0]; congr 1; rw [c₁, c₂, c₃] at h; linarith
    · rw [c₁, c₂, c₃] at h; nlinarith
    · rw [c₁, c₂, c₃] at h; nlinarith

/-- The hypotheses are satisfiable: the triangle `(0,6), (0,0), (6,0)` and the point `(2,1)`,
with feet `(2,0)`, `(7/2,5/2)`, `(0,1)` and distances `1 < √(9/2)`, `1 < 2`. -/
theorem problem64_nonvacuous : cross (pt 0 6) (pt 0 0) (pt 6 0) ≠ 0 ∧
    IsFoot (pt 2 1) (pt 0 0) (pt 6 0) (pt 2 0) ∧
    IsFoot (pt 2 1) (pt 6 0) (pt 0 6) (pt (7/2) (5/2)) ∧
    IsFoot (pt 2 1) (pt 0 6) (pt 0 0) (pt 0 1) ∧
    dist (pt 2 1) (pt 2 0) < dist (pt 2 1) (pt (7/2) (5/2)) ∧
    dist (pt 2 1) (pt 2 0) < dist (pt 2 1) (pt 0 1) := by
  have lt : ∀ P Q R S : Plane, dist P Q ^ 2 < dist R S ^ 2 → dist P Q < dist R S :=
    fun P Q R S h => by nlinarith [dist_nonneg (x := P) (y := Q), dist_nonneg (x := R) (y := S)]
  refine ⟨by norm_num [cross], ⟨mem_line.2 ⟨1/3, ?_⟩, ?_⟩, ⟨mem_line.2 ⟨5/12, ?_⟩, ?_⟩,
    ⟨mem_line.2 ⟨5/6, ?_⟩, ?_⟩, lt _ _ _ _ ?_, lt _ _ _ _ ?_⟩
  all_goals first
    | (apply ext2 <;> norm_num [pt])
    | (rw [inner2]; norm_num [pt])
    | (rw [distsq2, distsq2]; norm_num [pt])

end PillowProblems.P64
