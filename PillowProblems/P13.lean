import PillowProblems.Basic

/-!
# Problem 13 (Trigonometry: Plane)

**Question.** *(dated 3/89)*

> Given the lengths of the radii of two intersecting Circles, and the distance between their centres: find the area of the Tetragon formed by the tangents at the points of intersection.

**Answer.**

> If '\(2M\)' = area of Tetragon whose vertices are the Centres and the Points of intersection; and if its sides be '\(a\)', '\(b\)', and its diagonal, joining the Centres, '\(c\)': required area \[ = \frac{32M^{3}}{(b^{2} + c^{2} - a^{2}).(c^{2} + a^{2} - b^{2})}. \]

*(Carroll's solution: Chapter III, problem 13; text in `data/problems.json`.)*

**Lean reading.** The circles have centres `A ≠ B` and meet at the two points `C ≠ D` (so `AD = AC` and
`BD = BC` are the radii `b = AC`, `a = BC`, and `c = AB`). "`X` lies on the tangent at `P` to
the circle about `O`" is `OnTangent O P X` (`XP ⊥ PO`); `E` is on the tangents to circle `A` at
`C` and `D`, `F` on those to circle `B`, and the tetragon formed by the four tangents is `CFDE`.
Areas of tetragons are given by the shoelace formula `quadArea` (Carroll's `2M` is
`quadArea A C B D`); no convexity is assumed. When an angle `CAB` or `CBA` is right the two
tangents are parallel and no such `E` or `F` exists, so the hypotheses cannot hold. Carroll's
expression is correct only for his figure, where both angles of `ABC` at the centres are acute
(`problem13_acute`); if one of them is obtuse the tetragon is a non-convex "dart", the factor
`b² + c² - a²` or `c² + a² - b²` is negative, and Carroll's expression is minus the area
(`problem13_obtuse`, also showing that the hypotheses are satisfiable). The correct general
answer, proved in `problem13`, is the absolute value of Carroll's expression.

**Status.** proved (corrected)
-/

namespace PillowProblems.P13

/-- `X` lies on the tangent at `P` to the circle with centre `O` passing through `P`. -/
def OnTangent (O P X : Plane) : Prop :=
  inner ℝ (X - P) (P - O) = 0

/-- The area of the tetragon (quadrilateral) with vertices `P, Q, R, S` taken in this order,
by the shoelace formula (this is its area whenever the boundary `PQRSP` does not cross itself,
whether the tetragon is convex or not). -/
noncomputable def quadArea (P Q R S : Plane) : ℝ :=
  |cross P Q R + cross P R S| / 2

private lemma dist_sq' (X Y : Plane) : dist X Y ^ 2 = (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma inner' (X Y : Plane) : inner ℝ X Y = X 0 * Y 0 + X 1 * Y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- Twice the signed area of a triangle, in coordinates. -/
private def crossR (x0 x1 y0 y1 z0 z1 : ℝ) : ℝ := (y0 - x0) * (z1 - x1) - (z0 - x0) * (y1 - x1)

/-- Squared distance, in coordinates. -/
private def sq2 (x0 x1 y0 y1 : ℝ) : ℝ := (x0 - y0) ^ 2 + (x1 - y1) ^ 2

/-- A vector orthogonal to `u ≠ 0` is a multiple of `u` turned through a right angle, and a vector
"parallel" to `u` (zero cross product) is a multiple of `u`. -/
private lemma perp_param {x0 x1 u0 u1 : ℝ} (hu : u0 ^ 2 + u1 ^ 2 ≠ 0)
    (h : x0 * u0 + x1 * u1 = 0) : ∃ m : ℝ, x0 = m * u1 ∧ x1 = -(m * u0) := by
  refine ⟨(x0 * u1 - x1 * u0) / (u0 ^ 2 + u1 ^ 2), ?_, ?_⟩
  · field_simp; linear_combination u0 * h
  · field_simp; linear_combination u1 * h

private lemma par_param {x0 x1 u0 u1 : ℝ} (hu : u0 ^ 2 + u1 ^ 2 ≠ 0)
    (h : x0 * u1 - x1 * u0 = 0) : ∃ m : ℝ, x0 = m * u0 ∧ x1 = m * u1 := by
  refine ⟨(x0 * u0 + x1 * u1) / (u0 ^ 2 + u1 ^ 2), ?_, ?_⟩
  · field_simp; linear_combination u1 * h
  · field_simp; linear_combination (-u0) * h

/-- The algebraic core of problem 13, with `A = (a0, a1)`, …, `F = (f0, f1)`. -/
private lemma core (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 f0 f1 : ℝ)
    (hAB : sq2 a0 a1 b0 b1 ≠ 0) (hCD : sq2 c0 c1 d0 d1 ≠ 0)
    (h1 : sq2 a0 a1 d0 d1 = sq2 a0 a1 c0 c1) (h2 : sq2 b0 b1 d0 d1 = sq2 b0 b1 c0 c1)
    (hE1 : (e0 - c0) * (c0 - a0) + (e1 - c1) * (c1 - a1) = 0)
    (hE2 : (e0 - d0) * (d0 - a0) + (e1 - d1) * (d1 - a1) = 0)
    (hF1 : (f0 - c0) * (c0 - b0) + (f1 - c1) * (c1 - b1) = 0)
    (hF2 : (f0 - d0) * (d0 - b0) + (f1 - d1) * (d1 - b1) = 0) :
    (crossR c0 c1 f0 f1 d0 d1 + crossR c0 c1 d0 d1 e0 e1) *
        (sq2 a0 a1 c0 c1 + sq2 a0 a1 b0 b1 - sq2 b0 b1 c0 c1) *
        (sq2 a0 a1 b0 b1 + sq2 b0 b1 c0 c1 - sq2 a0 a1 c0 c1) =
      8 * crossR a0 a1 b0 b1 c0 c1 ^ 3 ∧
    sq2 a0 a1 c0 c1 + sq2 a0 a1 b0 b1 - sq2 b0 b1 c0 c1 ≠ 0 ∧
    sq2 a0 a1 b0 b1 + sq2 b0 b1 c0 c1 - sq2 a0 a1 c0 c1 ≠ 0 ∧
    crossR a0 a1 c0 c1 b0 b1 + crossR a0 a1 b0 b1 d0 d1 = -2 * crossR a0 a1 b0 b1 c0 c1 := by
  unfold crossR sq2 at *
  -- move the origin to `A`
  obtain ⟨u0, rfl⟩ : ∃ u0, b0 = a0 + u0 := ⟨b0 - a0, by ring⟩
  obtain ⟨u1, rfl⟩ : ∃ u1, b1 = a1 + u1 := ⟨b1 - a1, by ring⟩
  obtain ⟨v0, rfl⟩ : ∃ v0, c0 = a0 + v0 := ⟨c0 - a0, by ring⟩
  obtain ⟨v1, rfl⟩ : ∃ v1, c1 = a1 + v1 := ⟨c1 - a1, by ring⟩
  have hu : u0 ^ 2 + u1 ^ 2 ≠ 0 := by
    intro h; apply hAB; linear_combination h
  -- `D` is the reflection of `C` in the line of centres
  obtain ⟨μ, hd0, hd1⟩ := perp_param (x0 := d0 - (a0 + v0)) (x1 := d1 - (a1 + v1)) hu
    (by linear_combination (h1 - h2) / 2)
  obtain rfl : d0 = a0 + v0 + μ * u1 := by linear_combination hd0
  obtain rfl : d1 = a1 + v1 - μ * u0 := by linear_combination hd1
  have hμ : μ ≠ 0 := by
    rintro rfl; apply hCD; ring
  have hμK : μ * (u0 ^ 2 + u1 ^ 2) = 2 * (u0 * v1 - v0 * u1) := by
    have : μ * (μ * (u0 ^ 2 + u1 ^ 2) - 2 * (u0 * v1 - v0 * u1)) = 0 := by
      linear_combination h1
    linear_combination (mul_eq_zero.1 this).resolve_left hμ
  -- `E` lies on the line of centres
  obtain ⟨s, hs0, hs1⟩ := par_param (x0 := e0 - a0) (x1 := e1 - a1) hu (by
    have : μ * ((e0 - a0) * u1 - (e1 - a1) * u0) = 0 := by linear_combination hE2 - hE1 + h1
    exact (mul_eq_zero.1 this).resolve_left hμ)
  obtain rfl : e0 = a0 + s * u0 := by linear_combination hs0
  obtain rfl : e1 = a1 + s * u1 := by linear_combination hs1
  -- `F` lies on the line of centres
  obtain ⟨t, ht0, ht1⟩ := par_param (x0 := f0 - (a0 + u0)) (x1 := f1 - (a1 + u1)) hu (by
    have : μ * ((f0 - (a0 + u0)) * u1 - (f1 - (a1 + u1)) * u0) = 0 := by
      linear_combination hF2 - hF1 + h2
    exact (mul_eq_zero.1 this).resolve_left hμ)
  obtain rfl : f0 = a0 + u0 + t * u0 := by linear_combination ht0
  obtain rfl : f1 = a1 + u1 + t * u1 := by linear_combination ht1
  have hsX : s * (2 * (u0 * v0 + u1 * v1)) = 2 * (v0 ^ 2 + v1 ^ 2) := by
    linear_combination 2 * hE1
  have htY : t * (2 * (u0 * (u0 - v0) + u1 * (u1 - v1))) = -(2 * ((u0 - v0) ^ 2 + (u1 - v1) ^ 2)) := by
    linear_combination (-2) * hF1
  have hv : v0 ^ 2 + v1 ^ 2 ≠ 0 := by
    intro hv
    have h0 : v0 = 0 := by nlinarith
    have h1' : v1 = 0 := by nlinarith
    apply hμ
    have : μ * (u0 ^ 2 + u1 ^ 2) = 0 := by rw [h0, h1'] at hμK; linear_combination hμK
    exact (mul_eq_zero.1 this).resolve_right hu
  have huv : (u0 - v0) ^ 2 + (u1 - v1) ^ 2 ≠ 0 := by
    intro hw
    have h0 : v0 = u0 := by nlinarith
    have h1' : v1 = u1 := by nlinarith
    apply hμ
    have : μ * (u0 ^ 2 + u1 ^ 2) = 0 := by rw [h0, h1'] at hμK; linear_combination hμK
    exact (mul_eq_zero.1 this).resolve_right hu
  have hX : 2 * (u0 * v0 + u1 * v1) ≠ 0 := by
    intro h; rw [h, mul_zero] at hsX; exact hv (by linarith)
  have hY : 2 * (u0 * (u0 - v0) + u1 * (u1 - v1)) ≠ 0 := by
    intro h; rw [h, mul_zero] at htY; exact huv (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination
      (μ * (u0 ^ 2 + u1 ^ 2) * (2 * (u0 * (u0 - v0) + u1 * (u1 - v1)))) * hsX +
      (-(μ * (u0 ^ 2 + u1 ^ 2) * (2 * (u0 * v0 + u1 * v1)))) * htY +
      4 * (u0 * v1 - v0 * u1) ^ 2 * hμK
  · intro h; apply hX; linear_combination h
  · intro h; apply hY; linear_combination h
  · linear_combination -hμK

/-- **Problem 13.** Two circles with centres `A`, `B` (`A ≠ B`) meet at the two points `C ≠ D`.
The tangents to the circle `A` at `C` and `D` meet at `E`, those to the circle `B` at `F`. With
`a = BC`, `b = AC` (the radii), `c = AB`, and `2M` the area of the tetragon `ACBD`, the
tetragon `CFDE` has area `|32 M³ / ((b² + c² - a²)(c² + a² - b²))|`. -/
theorem problem13 (A B C D E F : Plane) (hAB : A ≠ B) (hCD : C ≠ D)
    (hAD : dist A D = dist A C) (hBD : dist B D = dist B C)
    (hEC : OnTangent A C E) (hED : OnTangent A D E)
    (hFC : OnTangent B C F) (hFD : OnTangent B D F) :
    quadArea C F D E =
      |32 * (quadArea A C B D / 2) ^ 3 /
        ((dist A C ^ 2 + dist A B ^ 2 - dist B C ^ 2) *
          (dist A B ^ 2 + dist B C ^ 2 - dist A C ^ 2))| := by
  unfold OnTangent at hEC hED hFC hFD
  rw [inner'] at hEC hED hFC hFD
  simp only [PiLp.sub_apply] at hEC hED hFC hFD
  have hAB' : sq2 (A 0) (A 1) (B 0) (B 1) ≠ 0 := by
    unfold sq2; rw [← dist_sq']; exact pow_ne_zero 2 (dist_ne_zero.2 hAB)
  have hCD' : sq2 (C 0) (C 1) (D 0) (D 1) ≠ 0 := by
    unfold sq2; rw [← dist_sq']; exact pow_ne_zero 2 (dist_ne_zero.2 hCD)
  have h1 : sq2 (A 0) (A 1) (D 0) (D 1) = sq2 (A 0) (A 1) (C 0) (C 1) := by
    unfold sq2; rw [← dist_sq', ← dist_sq', hAD]
  have h2 : sq2 (B 0) (B 1) (D 0) (D 1) = sq2 (B 0) (B 1) (C 0) (C 1) := by
    unfold sq2; rw [← dist_sq', ← dist_sq', hBD]
  obtain ⟨hS, hX, hY, hM⟩ := core (A 0) (A 1) (B 0) (B 1) (C 0) (C 1) (D 0) (D 1) (E 0) (E 1)
    (F 0) (F 1) hAB' hCD' h1 h2 hEC hED hFC hFD
  have e1 : ∀ P Q : Plane, sq2 (P 0) (P 1) (Q 0) (Q 1) = dist P Q ^ 2 := by
    intro P Q; unfold sq2; rw [dist_sq']
  simp only [e1] at hS hX hY
  change (cross C F D + cross C D E) * _ * _ = 8 * cross A B C ^ 3 at hS
  change cross A C B + cross A B D = -2 * cross A B C at hM
  unfold quadArea
  rw [hM]
  set K := cross A B C
  set X := dist A C ^ 2 + dist A B ^ 2 - dist B C ^ 2
  set Y := dist A B ^ 2 + dist B C ^ 2 - dist A C ^ 2
  rw [show cross C F D + cross C D E = 2 * (4 * K ^ 3 / (X * Y)) by
    field_simp; linear_combination hS]
  rw [show |-2 * K| = 2 * |K| by rw [abs_mul]; norm_num,
    show 32 * (2 * |K| / 2 / 2) ^ 3 = 4 * |K| ^ 3 by ring]
  simp only [abs_div, abs_mul, abs_pow, abs_abs]
  ring

/-- When both angles of the triangle `ABC` at the centres are acute (the case of Carroll's
figure, where the tetragon `CFDE` is convex), Carroll's formula holds without the absolute value. -/
theorem problem13_acute (A B C D E F : Plane) (hAB : A ≠ B) (hCD : C ≠ D)
    (hAD : dist A D = dist A C) (hBD : dist B D = dist B C)
    (hEC : OnTangent A C E) (hED : OnTangent A D E)
    (hFC : OnTangent B C F) (hFD : OnTangent B D F)
    (hα : dist B C ^ 2 < dist A C ^ 2 + dist A B ^ 2)
    (hβ : dist A C ^ 2 < dist A B ^ 2 + dist B C ^ 2) :
    quadArea C F D E =
      32 * (quadArea A C B D / 2) ^ 3 /
        ((dist A C ^ 2 + dist A B ^ 2 - dist B C ^ 2) *
          (dist A B ^ 2 + dist B C ^ 2 - dist A C ^ 2)) := by
  rw [problem13 A B C D E F hAB hCD hAD hBD hEC hED hFC hFD, abs_of_nonneg]
  have : 0 ≤ quadArea A C B D := by unfold quadArea; positivity
  apply div_nonneg (by positivity)
  exact mul_nonneg (by linarith) (by linarith)

/-- Carroll's expression fails when an angle at a centre is obtuse. Circles of radii `1` and `√3`
with centres `A = (0,0)`, `B = (1,0)` meet at `C, D = (-1/2, ±√3/2)`, where the angle `CAB` is
`120°`; the tangents give `E = (-2,0)`, `F = (-1,0)`, and Carroll's expression equals minus the
(positive) area of the tetragon `CFDE`. This also shows that the hypotheses of `problem13` are
satisfiable. -/
theorem problem13_obtuse :
    let A := pt 0 0; let B := pt 1 0
    let C := pt (-1 / 2) (Real.sqrt 3 / 2); let D := pt (-1 / 2) (-(Real.sqrt 3 / 2))
    let E := pt (-2) 0; let F := pt (-1) 0
    (A ≠ B ∧ C ≠ D ∧ dist A D = dist A C ∧ dist B D = dist B C ∧ OnTangent A C E ∧
      OnTangent A D E ∧ OnTangent B C F ∧ OnTangent B D F) ∧
    32 * (quadArea A C B D / 2) ^ 3 /
        ((dist A C ^ 2 + dist A B ^ 2 - dist B C ^ 2) *
          (dist A B ^ 2 + dist B C ^ 2 - dist A C ^ 2)) = -quadArea C F D E ∧
    0 < quadArea C F D E := by
  intro A B C D E F
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 3 := by positivity
  have hAC : dist A C ^ 2 = 1 := by
    rw [dist_sq']; simp only [A, C, pt_zero, pt_one]; linear_combination h3 / 4
  have hAD : dist A D ^ 2 = 1 := by
    rw [dist_sq']; simp only [A, D, pt_zero, pt_one]; linear_combination h3 / 4
  have hBC : dist B C ^ 2 = 3 := by
    rw [dist_sq']; simp only [B, C, pt_zero, pt_one]; linear_combination h3 / 4
  have hBD : dist B D ^ 2 = 3 := by
    rw [dist_sq']; simp only [B, D, pt_zero, pt_one]; linear_combination h3 / 4
  have hAB : dist A B ^ 2 = 1 := by
    rw [dist_sq']; simp only [A, B, pt_zero, pt_one]; norm_num
  have hyps : A ≠ B ∧ C ≠ D ∧ dist A D = dist A C ∧ dist B D = dist B C ∧ OnTangent A C E ∧
      OnTangent A D E ∧ OnTangent B C F ∧ OnTangent B D F := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      have := congrArg (fun P : Plane => P 0) h
      simp only [A, B, pt_zero] at this
      norm_num at this
    · intro h
      have := congrArg (fun P : Plane => P 1) h
      simp only [C, D, pt_one] at this
      linarith
    · rw [← Real.sqrt_sq dist_nonneg, hAD, ← hAC, Real.sqrt_sq dist_nonneg]
    · rw [← Real.sqrt_sq dist_nonneg, hBD, ← hBC, Real.sqrt_sq dist_nonneg]
    · unfold OnTangent; rw [inner']; simp only [A, C, E, PiLp.sub_apply, pt_zero, pt_one]
      linear_combination (-1 / 4) * h3
    · unfold OnTangent; rw [inner']; simp only [A, D, E, PiLp.sub_apply, pt_zero, pt_one]
      linear_combination (-1 / 4) * h3
    · unfold OnTangent; rw [inner']; simp only [B, C, F, PiLp.sub_apply, pt_zero, pt_one]
      linear_combination (-1 / 4) * h3
    · unfold OnTangent; rw [inner']; simp only [B, D, F, PiLp.sub_apply, pt_zero, pt_one]
      linear_combination (-1 / 4) * h3
  obtain ⟨hAB', hCD', hAD', hBD', hEC, hED, hFC, hFD⟩ := hyps
  have harea := problem13 A B C D E F hAB' hCD' hAD' hBD' hEC hED hFC hFD
  have hM : 0 < quadArea A C B D := by
    unfold quadArea cross
    simp only [A, B, C, D, pt_zero, pt_one]
    apply div_pos _ (by norm_num)
    apply abs_pos.2
    intro h
    have : Real.sqrt 3 = 0 := by linear_combination -h
    linarith
  have hneg : 32 * (quadArea A C B D / 2) ^ 3 /
      ((dist A C ^ 2 + dist A B ^ 2 - dist B C ^ 2) *
        (dist A B ^ 2 + dist B C ^ 2 - dist A C ^ 2)) < 0 := by
    rw [hAC, hAB, hBC]
    apply div_neg_of_pos_of_neg (by positivity)
    norm_num
  refine ⟨⟨hAB', hCD', hAD', hBD', hEC, hED, hFC, hFD⟩, ?_, ?_⟩
  · rw [harea, abs_of_neg hneg, neg_neg]
  · rw [harea]; exact abs_pos.2 hneg.ne

end PillowProblems.P13
