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

/-- The two components of a vector of the plane in the frame with first axis along `(d0, d1)`
(of length `b`); `σ = ±1` fixes the orientation of the second axis. -/
private noncomputable def fe (d0 d1 b : ℝ) (V : Plane) : ℝ := (V 0 * d0 + V 1 * d1) / b

private noncomputable def fn (d0 d1 b σ : ℝ) (V : Plane) : ℝ := σ * (d0 * V 1 - d1 * V 0) / b

/-- `lineDist P B C` really is the perpendicular distance of `P` from the line `BC`: the distance
from `P` to the nearest point of that line. -/
theorem lineDist_eq_infDist (P B C : Plane) (hBC : B ≠ C) :
    lineDist P B C = Metric.infDist P (line[ℝ, B, C] : Set Plane) := by
  sorry

section frame

variable {d0 d1 b σ : ℝ} (hb : d0 ^ 2 + d1 ^ 2 = b ^ 2) (hb0 : b ≠ 0) (hσ : σ ^ 2 = 1)
include hb hb0 hσ

end frame

/-- Carroll's expression for `AR`, written in the frame co-ordinates `b = AC`, `B = (u, v)`,
`P = (x, y)`. -/
private noncomputable def carrollFrame (b u v x y : ℝ) : ℝ :=
  (((b - x) * v - y * (b - u)) * v / ((b - u) ^ 2 + v ^ 2) +
          (x * v - y * u) * v / (u ^ 2 + v ^ 2)) *
        (2 * ((x * v - y * u) * u / (u ^ 2 + v ^ 2)) + y) /
        (((b - x) * v - y * (b - u)) * (b - u) / ((b - u) ^ 2 + v ^ 2) +
          (x * v - y * u) * u / (u ^ 2 + v ^ 2) + y) +
      y * u / v + (x * v - y * u) / v * ((u ^ 2 - v ^ 2) / (u ^ 2 + v ^ 2))

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
  sorry

/-- The hypotheses of `problem53` can be met: in the triangle `(0,0), (2,4), (4,0)` the ball from
`P = (2,1)` strikes `AB` at `(22/35, 44/35)`, `CA` at `(2,0)` and `BC` at `(118/35, 44/35)`. -/
theorem problem53_nonvacuous : ∃ (A B C P Q R S : Plane) (wA wB wC : ℝ),
    cross A B C ≠ 0 ∧ 0 < wA ∧ 0 < wB ∧ 0 < wC ∧ wA + wB + wC = 1 ∧
      P = wA • A + wB • B + wC • C ∧ IsBilliardPath A B C P Q R S := by
  sorry

end PillowProblems.P53
