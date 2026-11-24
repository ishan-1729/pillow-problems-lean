import PillowProblems.Basic

/-!
# Problem 53 (Algebraical Geometry: Plane)

**Question.** *(dated 6/4/89)*

> In a triangular billiard-table, a Point is given by its trilinear co-ordinates. A ball, starting from the given Point, strikes the three sides, and returns to the starting-point. Find, in terms of the trilinear co-ordinates and of the angles of the Triangle, the Point where the ball strikes the second side.

**Answer.**

> The portion, cut off from the second side, is equal to \[ \frac{(\alpha\sin C+\gamma\sin A)(2\gamma\cos A+\beta)}{\alpha\cos C+\gamma\cos A+\beta}+\frac{\beta\cos A+\gamma\cos 2A}{\sin A}. \]

*(Carroll's solution: Chapter III, problem 53; text in `data/problems.json`.)*

**Lean reading.** The table is any nondegenerate triangle `ABC` of the plane
(`cross A B C ≠ 0`) and the given point `P` is strictly inside it (positive barycentric weights
`wA, wB, wC`), as a point of the table must be. Its trilinear co-ordinates `α, β, γ` are its
perpendicular distances `lineDist P B C`, `lineDist P C A`, `lineDist P A B` from `BC`, `CA`,
`AB` (defined as twice the area over the base; `lineDist_eq_infDist` proves this is the distance
to the line), and `A`, `C` are the angles `∠BAC`, `∠ACB`. As in Carroll's figure, the ball strikes `AB`
first (at `Q`), `CA` second (at `R`) and `BC` third (at `S`); reversing the path gives the same
`R`, so this is no loss. `IsBilliardPath` asks each stroke to fall strictly inside its side and
the law of reflection at each cushion, in the form "the direction after the stroke is a positive
multiple of the mirror image (`mirror`) of the direction before it". As in Carroll's answer, the
point on the second side is given by the length `AR` it cuts off from `A`; the theorem proves
Carroll's formula for every such path, so in particular `R` is determined. A path need not exist
for every `P` (the strokes can fall outside the sides), so `problem53_nonvacuous` exhibits a
concrete triangle, point and path. Carroll's denominator `α cos C + γ cos A + β` cannot vanish on
such a path (this is proved inside the argument, not assumed). The proof places `A` at the
origin with `AC` along the first axis and follows Carroll's unfolding: `R` is where the line
from `E` (the mirror image of `P` in `AB`, then in `AC`) to the mirror image of `P` in `BC`
meets `AC`.

**Status.** proved
-/

namespace PillowProblems.P53

open EuclideanGeometry

/-- The mirror image of the vector `v` in a line with direction `w`: a ball travelling with
velocity `v` against a cushion parallel to `w` leaves it with velocity `mirror w v`. -/
noncomputable def mirror (w v : Plane) : Plane := (2 * inner ℝ v w / inner ℝ w w) • w - v

/-- The perpendicular distance of `P` from the line `BC` (twice the area of `PBC` over `BC`). -/
noncomputable def lineDist (P B C : Plane) : ℝ := |cross B C P| / dist B C

/-- The ball starts from `P`, strikes `AB` at `Q`, then `CA` (the second side) at `R`, then `BC`
at `S`, and returns to `P`; at each cushion the direction of travel after the stroke is a
positive multiple of the mirror image of the direction before it (law of reflection). -/
def IsBilliardPath (A B C P Q R S : Plane) : Prop :=
  Sbtw ℝ A Q B ∧ Sbtw ℝ C R A ∧ Sbtw ℝ B S C ∧
    (∃ l : ℝ, 0 < l ∧ R - Q = l • mirror (B - A) (Q - P)) ∧
    (∃ l : ℝ, 0 < l ∧ S - R = l • mirror (A - C) (R - Q)) ∧
    (∃ l : ℝ, 0 < l ∧ P - S = l • mirror (C - B) (S - R))

/-- Frame version: `A = (0,0)`, `C = (b,0)`, `B = (u,v)` with `v > 0`, `P = (x,y)`,
`Q = tq • B`, `R = (r,0)`, `S = C + ts • (B - C)`. -/
private lemma core (b u v x y tq r ts l1 l2 l3 : ℝ) (hb : 0 < b) (hv : 0 < v) (hts : 0 < ts)
    (hl1 : 0 < l1) (hl2 : 0 < l2) (hl3 : 0 < l3)
    (m1x : r - tq * u = l1 * (2 * ((tq * u - x) * u + (tq * v - y) * v) / (u ^ 2 + v ^ 2) * u -
      (tq * u - x)))
    (m1y : 0 - tq * v = l1 * (2 * ((tq * u - x) * u + (tq * v - y) * v) / (u ^ 2 + v ^ 2) * v -
      (tq * v - y)))
    (m2x : b + ts * (u - b) - r = l2 * (2 * ((r - tq * u) * (-b) + (0 - tq * v) * 0) /
      ((-b) ^ 2 + 0 ^ 2) * (-b) - (r - tq * u)))
    (m2y : ts * v - 0 = l2 * (2 * ((r - tq * u) * (-b) + (0 - tq * v) * 0) /
      ((-b) ^ 2 + 0 ^ 2) * 0 - (0 - tq * v)))
    (m3x : x - (b + ts * (u - b)) = l3 * (2 * ((b + ts * (u - b) - r) * (b - u) +
      (ts * v - 0) * (-v)) / ((b - u) ^ 2 + (-v) ^ 2) * (b - u) - (b + ts * (u - b) - r)))
    (m3y : y - ts * v = l3 * (2 * ((b + ts * (u - b) - r) * (b - u) +
      (ts * v - 0) * (-v)) / ((b - u) ^ 2 + (-v) ^ 2) * (-v) - (ts * v - 0))) :
    ((b - x) * v - y * (b - u)) * (b - u) / ((b - u) ^ 2 + v ^ 2) +
        (x * v - y * u) * u / (u ^ 2 + v ^ 2) + y ≠ 0 ∧
    r = (((b - x) * v - y * (b - u)) * v / ((b - u) ^ 2 + v ^ 2) +
          (x * v - y * u) * v / (u ^ 2 + v ^ 2)) *
        (2 * ((x * v - y * u) * u / (u ^ 2 + v ^ 2)) + y) /
        (((b - x) * v - y * (b - u)) * (b - u) / ((b - u) ^ 2 + v ^ 2) +
          (x * v - y * u) * u / (u ^ 2 + v ^ 2) + y) +
      y * u / v + (x * v - y * u) / v * ((u ^ 2 - v ^ 2) / (u ^ 2 + v ^ 2)) := by
  have hC2 : 0 < u ^ 2 + v ^ 2 := by positivity
  have hA2 : 0 < (b - u) ^ 2 + v ^ 2 := by positivity
  -- the mirror images `P₁` of `P` in `AB`, `E` of `P₁` in `AC`, `P₃` of `P` in `BC`
  set kP := 2 * (x * u + y * v) / (u ^ 2 + v ^ 2) with hkP
  set E0 := kP * u - x with hE0
  set E1 := y - kP * v with hE1
  set k3 := 2 * ((x - b) * (b - u) - y * v) / ((b - u) ^ 2 + v ^ 2) with hk3
  set P0 := b + k3 * (b - u) - (x - b) with hP0
  set P1 := k3 * (-v) - y with hP1
  set Sx := b + ts * (u - b) with hSx
  set Sy := ts * v with hSy
  -- step 1: `R - Q = l1 • (Q - P₁)`
  have e1x : r - tq * u = l1 * (tq * u - E0) := by
    rw [m1x, hE0, hkP]; field_simp; ring
  have e1y : 0 - tq * v = l1 * (tq * v + E1) := by
    rw [m1y, hE1, hkP]; field_simp; ring
  -- step 2: `S - R = l2 • (mirror of R - Q in AC)`
  have e2x : Sx - r = l2 * (r - tq * u) := by
    rw [m2x]; field_simp; ring
  have e2y : Sy = l2 * (tq * v) := by
    have := m2y; simp at this; linarith
  -- step 3: `P₃ - S = l3 • (S - R)`
  have e3x : P0 - Sx = l3 * (Sx - r) := by
    rw [hP0, hk3, hSx]
    linear_combination (norm := skip)
      (2 * (b - u) ^ 2 / ((b - u) ^ 2 + v ^ 2) - 1) * m3x +
        (-2 * v * (b - u) / ((b - u) ^ 2 + v ^ 2)) * m3y
    field_simp
    ring
  have e3y : P1 - Sy = l3 * Sy := by
    rw [hP1, hk3, hSy]
    linear_combination (norm := skip)
      (-2 * v * (b - u) / ((b - u) ^ 2 + v ^ 2)) * m3x +
        (2 * v ^ 2 / ((b - u) ^ 2 + v ^ 2) - 1) * m3y
    field_simp
    ring
  -- step 4: `P₃ - R = κ • (R - E)`, hence `R` is where `EP₃` meets `AC`
  have hy : (1 + l1) * P1 = -((1 + l3) * l1 * l2) * E1 := by
    linear_combination (1 + l1) * e3y + (1 + l3) * (1 + l1) * e2y - (1 + l3) * l2 * e1y
  have hx : (1 + l1) * (P0 - r) = ((1 + l3) * l1 * l2) * (r - E0) := by
    linear_combination (1 + l1) * e3x + (1 + l3) * (1 + l1) * e2x + (1 + l3) * l2 * e1x
  have hmain : r * (P1 - E1) = E0 * P1 - P0 * E1 := by
    have h0 : (1 + l1) * (r * (P1 - E1) - (E0 * P1 - P0 * E1)) = 0 := by
      linear_combination (r - E0) * hy + E1 * hx
    have := (mul_eq_zero.mp h0).resolve_left (by linarith)
    linarith
  have hden : P1 - E1 = 2 * (((b - x) * v - y * (b - u)) * (b - u) / ((b - u) ^ 2 + v ^ 2) +
      (x * v - y * u) * u / (u ^ 2 + v ^ 2) + y) := by
    rw [hP1, hE1, hk3, hkP]; field_simp; ring
  have hne : P1 - E1 ≠ 0 := by
    intro h0
    have hP1z : P1 = 0 := by
      have : (1 + l1 + (1 + l3) * l1 * l2) * P1 = 0 := by
        linear_combination hy + (1 + l3) * l1 * l2 * h0
      exact (mul_eq_zero.mp this).resolve_left (by positivity)
    have : (1 + l3) * Sy = 0 := by linear_combination -e3y + hP1z
    have := (mul_eq_zero.mp this).resolve_left (by positivity)
    rw [hSy] at this
    exact absurd this (by positivity)
  refine ⟨fun h0 => hne (by rw [hden, h0]; ring), ?_⟩
  obtain ⟨D, hD⟩ : ∃ D, D = ((b - x) * v - y * (b - u)) * (b - u) / ((b - u) ^ 2 + v ^ 2) +
      (x * v - y * u) * u / (u ^ 2 + v ^ 2) + y := ⟨_, rfl⟩
  rw [← hD] at hden ⊢
  have hD0 : D ≠ 0 := fun h0 => hne (by rw [hden, h0]; ring)
  have key : E0 * P1 - P0 * E1 = 2 * ((((b - x) * v - y * (b - u)) * v / ((b - u) ^ 2 + v ^ 2) +
          (x * v - y * u) * v / (u ^ 2 + v ^ 2)) * (2 * ((x * v - y * u) * u / (u ^ 2 + v ^ 2)) + y))
        + 2 * D * (y * u / v + (x * v - y * u) / v * ((u ^ 2 - v ^ 2) / (u ^ 2 + v ^ 2))) := by
    rw [hE0, hE1, hP0, hP1, hk3, hkP, hD]
    field_simp
    ring
  have hr : r * (2 * D) = E0 * P1 - P0 * E1 := by rw [← hden]; exact hmain
  rw [key] at hr
  rw [eq_div_of_mul_eq (mul_ne_zero two_ne_zero hD0) hr]
  field_simp
  ring

/-- The two components of a vector of the plane in the frame with first axis along `(d0, d1)`
(of length `b`); `σ = ±1` fixes the orientation of the second axis. -/
private noncomputable def fe (d0 d1 b : ℝ) (V : Plane) : ℝ := (V 0 * d0 + V 1 * d1) / b

private noncomputable def fn (d0 d1 b σ : ℝ) (V : Plane) : ℝ := σ * (d0 * V 1 - d1 * V 0) / b

private lemma inner_eq (X W : Plane) : inner ℝ X W = X 0 * W 0 + X 1 * W 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

private lemma dist_sq' (X Y : Plane) : dist X Y ^ 2 = (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs,
    Real.sq_sqrt (by positivity)]

/-- `lineDist P B C` really is the perpendicular distance of `P` from the line `BC`: the distance
from `P` to the nearest point of that line. -/
theorem lineDist_eq_infDist (P B C : Plane) (hBC : B ≠ C) :
    lineDist P B C = Metric.infDist P (line[ℝ, B, C] : Set Plane) := by
  have hd : 0 < dist B C := dist_pos.mpr hBC
  set L := (C 0 - B 0) ^ 2 + (C 1 - B 1) ^ 2 with hL
  have hL' : dist B C ^ 2 = L := by rw [dist_sq']; ring
  have hL0 : 0 < L := by rw [← hL']; positivity
  set m := (C 0 - B 0) * (P 0 - B 0) + (C 1 - B 1) * (P 1 - B 1) with hm
  -- Lagrange identity along the line
  have lag : ∀ t : ℝ, dist P (AffineMap.lineMap B C t) ^ 2 * L =
      cross B C P ^ 2 + (m - t * L) ^ 2 := by
    intro t
    rw [dist_sq']
    simp only [AffineMap.lineMap_apply_module', cross, PiLp.add_apply, PiLp.smul_apply,
      PiLp.sub_apply, smul_eq_mul]
    rw [hL, hm]; ring
  have sq : ∀ t : ℝ, (dist P (AffineMap.lineMap B C t) * dist B C) ^ 2 =
      cross B C P ^ 2 + (m - t * L) ^ 2 := by
    intro t; rw [mul_pow, hL', lag t]
  have key : ∀ t : ℝ, lineDist P B C ≤ dist P (AffineMap.lineMap B C t) := by
    intro t
    rw [lineDist, div_le_iff₀ hd]
    apply (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).mp
    rw [sq_abs, sq t]
    nlinarith [sq_nonneg (m - t * L)]
  have foot : dist P (AffineMap.lineMap B C (m / L)) = lineDist P B C := by
    rw [lineDist, eq_div_iff hd.ne']
    apply (pow_left_inj₀ (by positivity) (abs_nonneg _) two_ne_zero).mp
    rw [sq_abs, sq (m / L), div_mul_cancel₀ _ hL0.ne', sub_self]
    ring
  apply le_antisymm
  · rw [Metric.le_infDist ⟨B, left_mem_affineSpan_pair ℝ B C⟩]
    intro y hy
    obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hy
    exact key t
  · rw [← foot]
    exact Metric.infDist_le_dist_of_mem (AffineMap.lineMap_mem_affineSpan_pair _ _ _)

section frame

variable {d0 d1 b σ : ℝ} (hb : d0 ^ 2 + d1 ^ 2 = b ^ 2) (hb0 : b ≠ 0) (hσ : σ ^ 2 = 1)
include hb hb0 hσ

private lemma inner_frame (X W : Plane) :
    fe d0 d1 b X * fe d0 d1 b W + fn d0 d1 b σ X * fn d0 d1 b σ W = X 0 * W 0 + X 1 * W 1 := by
  have e : fe d0 d1 b X * fe d0 d1 b W + fn d0 d1 b σ X * fn d0 d1 b σ W =
      ((X 0 * d0 + X 1 * d1) * (W 0 * d0 + W 1 * d1) +
        σ ^ 2 * ((d0 * X 1 - d1 * X 0) * (d0 * W 1 - d1 * W 0))) / b ^ 2 := by
    simp only [fe, fn]; ring
  rw [e, div_eq_iff (pow_ne_zero 2 hb0)]
  linear_combination ((d0 * X 1 - d1 * X 0) * (d0 * W 1 - d1 * W 0)) * hσ +
    (X 0 * W 0 + X 1 * W 1) * hb

private lemma cross_frame (X W : Plane) :
    X 0 * W 1 - X 1 * W 0 =
      σ * (fe d0 d1 b X * fn d0 d1 b σ W - fn d0 d1 b σ X * fe d0 d1 b W) := by
  have e : σ * (fe d0 d1 b X * fn d0 d1 b σ W - fn d0 d1 b σ X * fe d0 d1 b W) =
      σ ^ 2 * ((X 0 * d0 + X 1 * d1) * (d0 * W 1 - d1 * W 0) -
        (d0 * X 1 - d1 * X 0) * (W 0 * d0 + W 1 * d1)) / b ^ 2 := by
    simp only [fe, fn]; ring
  rw [e, eq_div_iff (pow_ne_zero 2 hb0)]
  linear_combination -(X 0 * W 1 - X 1 * W 0) * hb -
    ((X 0 * d0 + X 1 * d1) * (d0 * W 1 - d1 * W 0) -
        (d0 * X 1 - d1 * X 0) * (W 0 * d0 + W 1 * d1)) * hσ

/-- The law of reflection, read in the frame. -/
private lemma frame_mirror {V W X : Plane} {l : ℝ} (h : V = l • mirror W X) :
    fe d0 d1 b V = l * (2 * (fe d0 d1 b X * fe d0 d1 b W + fn d0 d1 b σ X * fn d0 d1 b σ W) /
      (fe d0 d1 b W ^ 2 + fn d0 d1 b σ W ^ 2) * fe d0 d1 b W - fe d0 d1 b X) ∧
    fn d0 d1 b σ V = l * (2 * (fe d0 d1 b X * fe d0 d1 b W +
      fn d0 d1 b σ X * fn d0 d1 b σ W) /
      (fe d0 d1 b W ^ 2 + fn d0 d1 b σ W ^ 2) * fn d0 d1 b σ W - fn d0 d1 b σ X) := by
  have hk : 2 * (fe d0 d1 b X * fe d0 d1 b W + fn d0 d1 b σ X * fn d0 d1 b σ W) /
      (fe d0 d1 b W ^ 2 + fn d0 d1 b σ W ^ 2) = 2 * inner ℝ X W / inner ℝ W W := by
    rw [inner_frame hb hb0 hσ, sq, sq, inner_frame hb hb0 hσ, inner_eq, inner_eq]
  rw [hk, h]
  constructor <;> simp only [fe, fn, mirror, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] <;>
    ring

end frame

/-- Cosine and sine of an angle from the inner product and a square root of the Gram
determinant. -/
private lemma angle_vals (X Y : Plane) (hX : 0 < ‖X‖) (hY : 0 < ‖Y‖) (J : ℝ) (hJ : 0 ≤ J)
    (hJ2 : inner ℝ X X * inner ℝ Y Y - inner ℝ X Y * inner ℝ X Y = J ^ 2) :
    Real.cos (InnerProductGeometry.angle X Y) = inner ℝ X Y / (‖X‖ * ‖Y‖) ∧
      Real.sin (InnerProductGeometry.angle X Y) = J / (‖X‖ * ‖Y‖) := by
  have hXY : 0 < ‖X‖ * ‖Y‖ := mul_pos hX hY
  constructor
  · rw [eq_div_iff hXY.ne', InnerProductGeometry.cos_angle_mul_norm_mul_norm]
  · rw [eq_div_iff hXY.ne', InnerProductGeometry.sin_angle_mul_norm_mul_norm, hJ2,
      Real.sqrt_sq hJ]

private lemma norm_sub_eq (X Y : Plane) : ‖X - Y‖ = dist X Y := (dist_eq_norm X Y).symm

/-- Carroll's expression for `AR`, written in the frame co-ordinates `b = AC`, `B = (u, v)`,
`P = (x, y)`. -/
private noncomputable def carrollFrame (b u v x y : ℝ) : ℝ :=
  (((b - x) * v - y * (b - u)) * v / ((b - u) ^ 2 + v ^ 2) +
          (x * v - y * u) * v / (u ^ 2 + v ^ 2)) *
        (2 * ((x * v - y * u) * u / (u ^ 2 + v ^ 2)) + y) /
        (((b - x) * v - y * (b - u)) * (b - u) / ((b - u) ^ 2 + v ^ 2) +
          (x * v - y * u) * u / (u ^ 2 + v ^ 2) + y) +
      y * u / v + (x * v - y * u) / v * ((u ^ 2 - v ^ 2) / (u ^ 2 + v ^ 2))

/-- First half: along a billiard path, `AR` is given by `carrollFrame`. -/
private lemma step1 (A B C P Q R S : Plane) (hpath : IsBilliardPath A B C P Q R S) (σ : ℝ)
    (hσ : σ ^ 2 = 1) (hσK : 0 < σ * ((C 0 - A 0) * (B 1 - A 1) - (C 1 - A 1) * (B 0 - A 0)))
    (hb0 : 0 < dist A C) :
    dist A R = carrollFrame (dist A C) (fe (C 0 - A 0) (C 1 - A 1) (dist A C) (B - A)) (fn (C 0 - A 0) (C 1 - A 1) (dist A C) σ (B - A))
      (fe (C 0 - A 0) (C 1 - A 1) (dist A C) (P - A)) (fn (C 0 - A 0) (C 1 - A 1) (dist A C) σ (P - A)) := by
  obtain ⟨⟨⟨tq, -, hQe⟩, -, -⟩, ⟨⟨tr, ⟨-, htr1⟩, hRe⟩, -, -⟩, ⟨⟨t3, ⟨-, ht31⟩, hSe⟩, -, hSC⟩,
    ⟨l1, hl1, m1⟩, ⟨l2, hl2, m2⟩, ⟨l3, hl3, m3⟩⟩ := hpath
  have coord : ∀ (X Y : Plane) (t : ℝ) (i : Fin 2),
      (AffineMap.lineMap X Y t : Plane) i = X i + t * (Y i - X i) := by
    intro X Y t i
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      smul_eq_mul]
    ring
  have hQ0 : Q 0 = A 0 + tq * (B 0 - A 0) := by rw [← hQe]; exact coord A B tq 0
  have hQ1 : Q 1 = A 1 + tq * (B 1 - A 1) := by rw [← hQe]; exact coord A B tq 1
  have hR0 : R 0 = C 0 + tr * (A 0 - C 0) := by rw [← hRe]; exact coord C A tr 0
  have hR1 : R 1 = C 1 + tr * (A 1 - C 1) := by rw [← hRe]; exact coord C A tr 1
  have hS0 : S 0 = B 0 + t3 * (C 0 - B 0) := by rw [← hSe]; exact coord B C t3 0
  have hS1 : S 1 = B 1 + t3 * (C 1 - B 1) := by rw [← hSe]; exact coord B C t3 1
  have ht3 : t3 ≠ 1 := by
    rintro rfl
    apply hSC
    rw [← hSe, AffineMap.lineMap_apply_one]
  have ht3' : t3 < 1 := lt_of_le_of_ne ht31 ht3
  set d0 := C 0 - A 0 with hd0
  set d1 := C 1 - A 1 with hd1
  set b := dist A C with hbdef
  have hb : d0 ^ 2 + d1 ^ 2 = b ^ 2 := by rw [hbdef, dist_sq']; ring
  have hb0' := hb0.ne'
  obtain ⟨u, hu⟩ : ∃ u, u = fe d0 d1 b (B - A) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = fn d0 d1 b σ (B - A) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = fe d0 d1 b (P - A) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = fn d0 d1 b σ (P - A) := ⟨_, rfl⟩
  rw [← hu, ← hv, ← hx, ← hy]
  have hvpos : 0 < v := by
    rw [hv, fn]; simp only [PiLp.sub_apply]
    exact div_pos (by linarith) hb0
  have eBA : fe d0 d1 b (B - A) = u ∧ fn d0 d1 b σ (B - A) = v := ⟨hu.symm, hv.symm⟩
  -- frame co-ordinates of the vectors that occur
  have ev : ∀ (X : Plane) (e f : ℝ), (X 0 * d0 + X 1 * d1) = e * b →
      (σ * (d0 * X 1 - d1 * X 0)) = f * b → fe d0 d1 b X = e ∧ fn d0 d1 b σ X = f := by
    intro X e f h1 h2
    simp only [fe, fn]
    rw [h1, h2]
    exact ⟨by field_simp, by field_simp⟩
  have uE : u * b = (B 0 - A 0) * d0 + (B 1 - A 1) * d1 := by
    rw [hu, fe]; simp only [PiLp.sub_apply]; field_simp
  have vE : v * b = σ * (d0 * (B 1 - A 1) - d1 * (B 0 - A 0)) := by
    rw [hv, fn]; simp only [PiLp.sub_apply]; field_simp
  have xE : x * b = (P 0 - A 0) * d0 + (P 1 - A 1) * d1 := by
    rw [hx, fe]; simp only [PiLp.sub_apply]; field_simp
  have yE : y * b = σ * (d0 * (P 1 - A 1) - d1 * (P 0 - A 0)) := by
    rw [hy, fn]; simp only [PiLp.sub_apply]; field_simp
  set r := (1 - tr) * b with hr
  set ts := 1 - t3 with hts
  have eRQ := ev (R - Q) (r - tq * u) (0 - tq * v)
    (by simp only [PiLp.sub_apply]; rw [hR0, hR1, hQ0, hQ1, hr]
        linear_combination (1 - tr) * hb + tq * uE)
    (by simp only [PiLp.sub_apply]; rw [hR0, hR1, hQ0, hQ1]
        linear_combination tq * vE)
  have eQP := ev (Q - P) (tq * u - x) (tq * v - y)
    (by simp only [PiLp.sub_apply]; rw [hQ0, hQ1]; linear_combination -tq * uE + xE)
    (by simp only [PiLp.sub_apply]; rw [hQ0, hQ1]; linear_combination -tq * vE + yE)
  have eSR := ev (S - R) (b + ts * (u - b) - r) (ts * v - 0)
    (by simp only [PiLp.sub_apply]; rw [hS0, hS1, hR0, hR1, hr, hts]
        linear_combination (t3 - 1 + tr) * hb - (1 - t3) * uE)
    (by simp only [PiLp.sub_apply]; rw [hS0, hS1, hR0, hR1, hts]
        linear_combination -(1 - t3) * vE)
  have ePS := ev (P - S) (x - (b + ts * (u - b))) (y - ts * v)
    (by simp only [PiLp.sub_apply]; rw [hS0, hS1, hts]
        linear_combination -t3 * hb - xE + (1 - t3) * uE)
    (by simp only [PiLp.sub_apply]; rw [hS0, hS1, hts]
        linear_combination -yE + (1 - t3) * vE)
  have eAC := ev (A - C) (-b) 0
    (by simp only [PiLp.sub_apply]; linear_combination -hb)
    (by simp only [PiLp.sub_apply]; ring)
  have eCB := ev (C - B) (b - u) (-v)
    (by simp only [PiLp.sub_apply]; linear_combination hb + uE)
    (by simp only [PiLp.sub_apply]; linear_combination vE)
  -- the three reflections, in the frame
  obtain ⟨m1x, m1y⟩ := frame_mirror hb hb0' hσ m1
  obtain ⟨m2x, m2y⟩ := frame_mirror hb hb0' hσ m2
  obtain ⟨m3x, m3y⟩ := frame_mirror hb hb0' hσ m3
  rw [eRQ.1, eQP.1, eQP.2, eBA.1, eBA.2] at m1x
  rw [eRQ.2, eQP.1, eQP.2, eBA.1, eBA.2] at m1y
  rw [eSR.1, eRQ.1, eRQ.2, eAC.1, eAC.2] at m2x
  rw [eSR.2, eRQ.1, eRQ.2, eAC.1, eAC.2] at m2y
  rw [ePS.1, eSR.1, eSR.2, eCB.1, eCB.2] at m3x
  rw [ePS.2, eSR.1, eSR.2, eCB.1, eCB.2] at m3y
  obtain ⟨hden, hmain⟩ := core b u v x y tq r ts l1 l2 l3 hb0 hvpos (by rw [hts]; linarith)
    hl1 hl2 hl3 m1x m1y m2x m2y m3x m3y
  -- `AR`
  have hdist : dist A R = r := by
    have h1 : 0 ≤ r := mul_nonneg (by linarith) hb0.le
    refine (pow_left_inj₀ dist_nonneg h1 two_ne_zero).mp ?_
    rw [dist_sq', hR0, hR1, hr]
    linear_combination (1 - tr) ^ 2 * hb
  rw [hdist, hmain]
  rfl

/-- Second half: Carroll's formula in trilinear co-ordinates and angles is `carrollFrame`. -/
private lemma step2 (A B C P : Plane) (wA wB wC : ℝ)
    (hwA : 0 < wA) (hwB : 0 < wB) (hwC : 0 < wC) (hw : wA + wB + wC = 1)
    (hP : P = wA • A + wB • B + wC • C) (σ : ℝ)
    (hσ : σ ^ 2 = 1) (hσK : 0 < σ * ((C 0 - A 0) * (B 1 - A 1) - (C 1 - A 1) * (B 0 - A 0)))
    (hb0 : 0 < dist A C) :
      (lineDist P B C * Real.sin (∠ A C B) + lineDist P A B * Real.sin (∠ B A C)) *
          (2 * lineDist P A B * Real.cos (∠ B A C) + lineDist P C A) /
          (lineDist P B C * Real.cos (∠ A C B) + lineDist P A B * Real.cos (∠ B A C) +
            lineDist P C A) +
        (lineDist P C A * Real.cos (∠ B A C) + lineDist P A B * Real.cos (2 * ∠ B A C)) /
          Real.sin (∠ B A C) = carrollFrame (dist A C) (fe (C 0 - A 0) (C 1 - A 1) (dist A C) (B - A)) (fn (C 0 - A 0) (C 1 - A 1) (dist A C) σ (B - A))
      (fe (C 0 - A 0) (C 1 - A 1) (dist A C) (P - A)) (fn (C 0 - A 0) (C 1 - A 1) (dist A C) σ (P - A)) := by
  have hP0 : P 0 = wA * A 0 + wB * B 0 + wC * C 0 := by rw [hP]; simp
  have hP1 : P 1 = wA * A 1 + wB * B 1 + wC * C 1 := by rw [hP]; simp
  set d0 := C 0 - A 0 with hd0
  set d1 := C 1 - A 1 with hd1
  set b := dist A C with hbdef
  have hb : d0 ^ 2 + d1 ^ 2 = b ^ 2 := by rw [hbdef, dist_sq']; ring
  have hb0' := hb0.ne'
  obtain ⟨u, hu⟩ : ∃ u, u = fe d0 d1 b (B - A) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = fn d0 d1 b σ (B - A) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = fe d0 d1 b (P - A) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = fn d0 d1 b σ (P - A) := ⟨_, rfl⟩
  rw [← hu, ← hv, ← hx, ← hy]
  have hvpos : 0 < v := by
    rw [hv, fn]; simp only [PiLp.sub_apply]
    exact div_pos (by linarith) hb0
  have eBA : fe d0 d1 b (B - A) = u ∧ fn d0 d1 b σ (B - A) = v := ⟨hu.symm, hv.symm⟩
  -- frame co-ordinates of the vectors that occur
  have ev : ∀ (X : Plane) (e f : ℝ), (X 0 * d0 + X 1 * d1) = e * b →
      (σ * (d0 * X 1 - d1 * X 0)) = f * b → fe d0 d1 b X = e ∧ fn d0 d1 b σ X = f := by
    intro X e f h1 h2
    simp only [fe, fn]
    rw [h1, h2]
    exact ⟨by field_simp, by field_simp⟩
  have uE : u * b = (B 0 - A 0) * d0 + (B 1 - A 1) * d1 := by
    rw [hu, fe]; simp only [PiLp.sub_apply]; field_simp
  have vE : v * b = σ * (d0 * (B 1 - A 1) - d1 * (B 0 - A 0)) := by
    rw [hv, fn]; simp only [PiLp.sub_apply]; field_simp
  have xE : x * b = (P 0 - A 0) * d0 + (P 1 - A 1) * d1 := by
    rw [hx, fe]; simp only [PiLp.sub_apply]; field_simp
  have yE : y * b = σ * (d0 * (P 1 - A 1) - d1 * (P 0 - A 0)) := by
    rw [hy, fn]; simp only [PiLp.sub_apply]; field_simp
  have eAC := ev (A - C) (-b) 0
    (by simp only [PiLp.sub_apply]; linear_combination -hb)
    (by simp only [PiLp.sub_apply]; ring)
  have eCB := ev (C - B) (b - u) (-v)
    (by simp only [PiLp.sub_apply]; linear_combination hb + uE)
    (by simp only [PiLp.sub_apply]; linear_combination vE)
  -- the weights of `P`
  have hxw : x = wB * u + wC * b := by
    have : x * b = (wB * u + wC * b) * b := by
      rw [xE, hP0, hP1]; linear_combination (-wB) * uE + wC * hb + (A 0 * d0 + A 1 * d1) * hw
    exact mul_right_cancel₀ hb0' this
  have hyw : y = wB * v := by
    have : y * b = (wB * v) * b := by
      rw [yE, hP0, hP1]; linear_combination (-wB) * vE + σ * (d0 * A 1 - d1 * A 0) * hw
    exact mul_right_cancel₀ hb0' this
  have hNα : 0 < (b - x) * v - y * (b - u) := by
    rw [hxw, hyw]
    have : (b - (wB * u + wC * b)) * v - wB * v * (b - u) = wA * b * v := by
      linear_combination (-(b * v)) * hw
    rw [this]; positivity
  have hNγ : 0 < x * v - y * u := by
    rw [hxw, hyw]
    have : (wB * u + wC * b) * v - wB * v * u = wC * b * v := by ring
    rw [this]; positivity
  have hy0 : 0 < y := by rw [hyw]; positivity
  -- more frame co-ordinates
  have eCA := ev (C - A) b 0
    (by simp only [PiLp.sub_apply]; linear_combination hb)
    (by simp only [PiLp.sub_apply]; ring)
  have eBC := ev (B - C) (u - b) v
    (by simp only [PiLp.sub_apply]; linear_combination -hb - uE)
    (by simp only [PiLp.sub_apply]; linear_combination -vE)
  have ePB := ev (P - B) (x - u) (y - v)
    (by simp only [PiLp.sub_apply]; linear_combination -xE + uE)
    (by simp only [PiLp.sub_apply]; linear_combination -yE + vE)
  have ePC := ev (P - C) (x - b) y
    (by simp only [PiLp.sub_apply]; linear_combination -xE - hb)
    (by simp only [PiLp.sub_apply]; linear_combination -yE)
  have ePA : fe d0 d1 b (P - A) = x ∧ fn d0 d1 b σ (P - A) = y := ⟨hx.symm, hy.symm⟩
  have hinner : ∀ X W : Plane, inner ℝ X W =
      fe d0 d1 b X * fe d0 d1 b W + fn d0 d1 b σ X * fn d0 d1 b σ W := by
    intro X W; rw [inner_eq, inner_frame hb hb0' hσ]
  have hσabs : |σ| = 1 := by
    have : |σ| ^ 2 = 1 ^ 2 := by rw [sq_abs, hσ]; norm_num
    exact (pow_left_inj₀ (abs_nonneg σ) zero_le_one two_ne_zero).mp this
  -- the sides `c = AB` and `a = BC`
  set c := dist A B with hc
  set a := dist B C with ha
  have hc2 : c ^ 2 = u ^ 2 + v ^ 2 := by
    rw [hc, dist_sq']
    have := inner_frame hb hb0' hσ (B - A) (B - A)
    rw [eBA.1, eBA.2] at this
    simp only [PiLp.sub_apply] at this
    linear_combination -this
  have ha2 : a ^ 2 = (b - u) ^ 2 + v ^ 2 := by
    rw [ha, dist_sq']
    have := inner_frame hb hb0' hσ (B - C) (B - C)
    rw [eBC.1, eBC.2] at this
    simp only [PiLp.sub_apply] at this
    linear_combination -this
  have hc0 : 0 < c := by
    have h2 : 0 < c ^ 2 := by rw [hc2]; positivity
    refine lt_of_le_of_ne dist_nonneg (fun h => ?_)
    rw [← h] at h2; simp at h2
  have ha0 : 0 < a := by
    have h2 : 0 < a ^ 2 := by rw [ha2]; positivity
    refine lt_of_le_of_ne dist_nonneg (fun h => ?_)
    rw [← h] at h2; simp at h2
  -- the angles
  have angA := angle_vals (B - A) (C - A)
    (by rw [norm_sub_eq, dist_comm]; exact hc0) (by rw [norm_sub_eq, dist_comm]; exact hb0)
    (v * b) (by positivity)
    (by rw [hinner, hinner, hinner, eBA.1, eBA.2, eCA.1, eCA.2]; ring)
  have angC := angle_vals (A - C) (B - C)
    (by rw [norm_sub_eq]; exact hb0) (by rw [norm_sub_eq]; exact ha0)
    (b * v) (by positivity)
    (by rw [hinner, hinner, hinner, eAC.1, eAC.2, eBC.1, eBC.2]; ring)
  have hAng : ∠ B A C = InnerProductGeometry.angle (B - A) (C - A) := rfl
  have hCng : ∠ A C B = InnerProductGeometry.angle (A - C) (B - C) := rfl
  rw [hinner, eBA.1, eBA.2, eCA.1, eCA.2, norm_sub_eq, norm_sub_eq, dist_comm B A,
    dist_comm C A, ← hc, ← hbdef] at angA
  rw [hinner, eAC.1, eAC.2, eBC.1, eBC.2, norm_sub_eq, norm_sub_eq, ← ha, ← hbdef] at angC
  have hcA : Real.cos (∠ B A C) = u / c := by
    rw [hAng, angA.1]; field_simp; ring
  have hsA : Real.sin (∠ B A C) = v / c := by
    rw [hAng, angA.2]; field_simp
  have hcC : Real.cos (∠ A C B) = (b - u) / a := by
    rw [hCng, angC.1]; field_simp; ring
  have hsC : Real.sin (∠ A C B) = v / a := by
    rw [hCng, angC.2]; field_simp
  -- the trilinear co-ordinates
  have hα : lineDist P B C = ((b - x) * v - y * (b - u)) / a := by
    rw [lineDist, ← ha]
    congr 1
    have := cross_frame hb hb0' hσ (C - B) (P - B)
    rw [eCB.1, eCB.2, ePB.1, ePB.2] at this
    simp only [PiLp.sub_apply] at this
    have e : cross B C P = σ * (-((b - x) * v - y * (b - u))) := by
      simp only [cross]; linear_combination this
    rw [e, abs_mul, hσabs, abs_neg, abs_of_pos hNα, one_mul]
  have hβ : lineDist P C A = y := by
    rw [lineDist, dist_comm, ← hbdef]
    have := cross_frame hb hb0' hσ (A - C) (P - C)
    rw [eAC.1, eAC.2, ePC.1, ePC.2] at this
    simp only [PiLp.sub_apply] at this
    have e : cross C A P = σ * (-(b * y)) := by
      simp only [cross]; linear_combination this
    rw [e, abs_mul, hσabs, abs_neg, abs_of_pos (mul_pos hb0 hy0), one_mul]
    field_simp
  have hγ : lineDist P A B = (x * v - y * u) / c := by
    rw [lineDist, ← hc]
    congr 1
    have := cross_frame hb hb0' hσ (B - A) (P - A)
    rw [eBA.1, eBA.2, ePA.1, ePA.2] at this
    simp only [PiLp.sub_apply] at this
    have e : cross A B P = σ * (-(x * v - y * u)) := by
      simp only [cross]; linear_combination this
    rw [e, abs_mul, hσabs, abs_neg, abs_of_pos hNγ, one_mul]
  -- assemble
  rw [Real.cos_two_mul, hα, hβ, hγ, hcA, hsA, hcC, hsC]
  have P1 : ((b - x) * v - y * (b - u)) / a * (v / a) =
      ((b - x) * v - y * (b - u)) * v / ((b - u) ^ 2 + v ^ 2) := by
    rw [div_mul_div_comm, ← sq, ha2]
  have P2 : (x * v - y * u) / c * (v / c) = (x * v - y * u) * v / (u ^ 2 + v ^ 2) := by
    rw [div_mul_div_comm, ← sq, hc2]
  have P3 : 2 * ((x * v - y * u) / c) * (u / c) = 2 * ((x * v - y * u) * u / (u ^ 2 + v ^ 2)) := by
    rw [mul_assoc, div_mul_div_comm, ← sq, hc2]
  have P4 : ((b - x) * v - y * (b - u)) / a * ((b - u) / a) =
      ((b - x) * v - y * (b - u)) * (b - u) / ((b - u) ^ 2 + v ^ 2) := by
    rw [div_mul_div_comm, ← sq, ha2]
  have P5 : (x * v - y * u) / c * (u / c) = (x * v - y * u) * u / (u ^ 2 + v ^ 2) := by
    rw [div_mul_div_comm, ← sq, hc2]
  have P6 : (y * (u / c) + (x * v - y * u) / c * (2 * (u / c) ^ 2 - 1)) / (v / c) =
      y * u / v + (x * v - y * u) / v * ((u ^ 2 - v ^ 2) / (u ^ 2 + v ^ 2)) := by
    rw [div_pow, hc2]
    have : 0 < u ^ 2 + v ^ 2 := by positivity
    field_simp
    ring
  rw [P3, P1, P2, P4, P5, P6]
  unfold carrollFrame
  ring

/-- **Problem 53.** If the ball goes from `P` to `Q` on `AB`, to `R` on `CA` (the second side),
to `S` on `BC` and back to `P`, obeying the law of reflection at each cushion, then `AR` is given
by Carroll's formula in the trilinear co-ordinates `α, β, γ` of `P` and the angles `A`, `C`. -/
theorem problem53 (A B C P Q R S : Plane) (hABC : cross A B C ≠ 0) (wA wB wC : ℝ)
    (hwA : 0 < wA) (hwB : 0 < wB) (hwC : 0 < wC) (hw : wA + wB + wC = 1)
    (hP : P = wA • A + wB • B + wC • C) (hpath : IsBilliardPath A B C P Q R S) :
    dist A R =
      (lineDist P B C * Real.sin (∠ A C B) + lineDist P A B * Real.sin (∠ B A C)) *
          (2 * lineDist P A B * Real.cos (∠ B A C) + lineDist P C A) /
          (lineDist P B C * Real.cos (∠ A C B) + lineDist P A B * Real.cos (∠ B A C) +
            lineDist P C A) +
        (lineDist P C A * Real.cos (∠ B A C) + lineDist P A B * Real.cos (2 * ∠ B A C)) /
          Real.sin (∠ B A C) := by
  have hAC : A ≠ C := by
    rintro rfl; apply hABC; simp only [cross]; ring
  have hb0 : 0 < dist A C := dist_pos.mpr hAC
  have hK : (C 0 - A 0) * (B 1 - A 1) - (C 1 - A 1) * (B 0 - A 0) ≠ 0 := by
    intro h; apply hABC; simp only [cross]; linear_combination -h
  obtain ⟨σ, hσ, hσK⟩ : ∃ σ : ℝ, σ ^ 2 = 1 ∧
      0 < σ * ((C 0 - A 0) * (B 1 - A 1) - (C 1 - A 1) * (B 0 - A 0)) := by
    rcases hK.lt_or_gt with h | h
    · exact ⟨-1, by norm_num, by linarith⟩
    · exact ⟨1, by norm_num, by linarith⟩
  rw [step1 A B C P Q R S hpath σ hσ hσK hb0,
    step2 A B C P wA wB wC hwA hwB hwC hw hP σ hσ hσK hb0]

/-- The hypotheses of `problem53` can be met: in the triangle `(0,0), (2,4), (4,0)` the ball from
`P = (2,1)` strikes `AB` at `(22/35, 44/35)`, `CA` at `(2,0)` and `BC` at `(118/35, 44/35)`. -/
theorem problem53_nonvacuous : ∃ (A B C P Q R S : Plane) (wA wB wC : ℝ),
    cross A B C ≠ 0 ∧ 0 < wA ∧ 0 < wB ∧ 0 < wC ∧ wA + wB + wC = 1 ∧
      P = wA • A + wB • B + wC • C ∧ IsBilliardPath A B C P Q R S := by
  have sb : ∀ (X Y Z : Plane) (t : ℝ), 0 < t → t < 1 → X ≠ Z →
      AffineMap.lineMap X Z t = Y → Sbtw ℝ X Y Z := by
    intro X Y Z t h0 h1 hXZ h
    exact sbtw_iff_mem_image_Ioo_and_ne.mpr ⟨⟨t, ⟨h0, h1⟩, h⟩, hXZ⟩
  have ne1 : ∀ x y x' y' : ℝ, y ≠ y' → pt x y ≠ pt x' y' := by
    intro x y x' y' h e
    have := congrArg (fun v : Plane => v 1) e
    simp only [pt_one] at this
    exact h this
  have ne0 : ∀ x y x' y' : ℝ, x ≠ x' → pt x y ≠ pt x' y' := by
    intro x y x' y' h e
    have := congrArg (fun v : Plane => v 0) e
    simp only [pt_zero] at this
    exact h this
  refine ⟨pt 0 0, pt 2 4, pt 4 0, pt 2 1, pt (22 / 35) (44 / 35), pt 2 0,
    pt (118 / 35) (44 / 35), 3 / 8, 1 / 4, 3 / 8, ?_, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_, ?_⟩
  · simp only [cross, pt_zero, pt_one]; norm_num
  · ext i
    fin_cases i
    · simp [pt]; norm_num
    · simp [pt]
  refine ⟨sb _ _ _ (11 / 35) (by norm_num) (by norm_num) (ne1 _ _ _ _ (by norm_num)) ?_,
    sb _ _ _ (1 / 2) (by norm_num) (by norm_num) (ne0 _ _ _ _ (by norm_num)) ?_,
    sb _ _ _ (24 / 35) (by norm_num) (by norm_num) (ne1 _ _ _ _ (by norm_num)) ?_,
    ⟨4 / 3, by norm_num, ?_⟩, ⟨1, by norm_num, ?_⟩, ⟨3 / 4, by norm_num, ?_⟩⟩ <;>
  · ext i
    fin_cases i <;>
      simp only [mirror, inner_eq] <;>
      simp [AffineMap.lineMap_apply, pt] <;> norm_num

end PillowProblems.P53
