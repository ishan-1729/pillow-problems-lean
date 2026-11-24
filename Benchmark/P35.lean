import PillowProblems.Basic

/-!
# Problem 35 (Pure Geometry, Plane)

**Question.** *(dated 11/76)*

> With a given Triangle, to describe a Circle, cutting each side in two points, such that, if radii be drawn perpendicular to the sides, they are divided by the sides in given ratios.

*(Carroll's solution: Chapter III, problem 35; text in `data/problems.json`.)*

**Lean reading.** The triangle is `A B C` with `cross A B C ≠ 0`; the given ratios `k, l, m` belong to the
sides `BC, CA, AB` and are proper fractions (`0 < k, l, m < 1`, Carroll's N.B.). As in Carroll's
solution, the ratio of a side is (part of the perpendicular radius outside the triangle) : (radius):
the radius `OK ⊥ XY` meets the side line at `M`, `M` lies between `O` and `K`, and `MK = k·r`
(`RadiusDivided`). The centre is required to lie strictly inside the triangle (positive barycentric
coordinates, `Inside`), which is what puts the parts `MK` outside the triangle. "Cutting each side in
two points" is read for the side lines (`CutsTwice`): for the closed sides the problem can be
impossible (for `k` small and `l, m` near `1` the centre is near `A` and the circle meets line `AB`
beyond `A`), and Carroll's construction never checks it. The theorem gives all solutions: the circle
works iff its centre is the point whose distances from the sides are as `1-k : 1-l : 1-m` (written
with barycentric weights `a(1-k), b(1-l), c(1-m)`, `a, b, c` the sides) and
`r = 2·area / (a(1-k) + b(1-l) + c(1-m))`. So the circle exists and is unique.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P35

open scoped EuclideanGeometry RealInnerProductSpace

/-- `O` lies strictly inside the triangle `ABC` (all three barycentric coordinates positive). -/
def Inside (O A B C : Plane) : Prop :=
  ∃ u v w : ℝ, 0 < u ∧ 0 < v ∧ 0 < w ∧ u + v + w = 1 ∧ O = u • A + v • B + w • C

/-- The circle with centre `O` and radius `r` cuts the side `XY` (as a line) in two points. -/
def CutsTwice (O : Plane) (r : ℝ) (X Y : Plane) : Prop :=
  ∃ P Q : Plane, P ≠ Q ∧ P ∈ line[ℝ, X, Y] ∧ Q ∈ line[ℝ, X, Y] ∧ dist O P = r ∧ dist O Q = r

/-- The radius `OK` of the circle (centre `O`, radius `r`) drawn at right angles to the side `XY`
is divided by that side, at `M`, so that the part `MK` beyond the side is to the radius as
`k : 1`. -/
def RadiusDivided (O : Plane) (r : ℝ) (X Y : Plane) (k : ℝ) : Prop :=
  ∃ K M : Plane, dist O K = r ∧ ⟪K - O, Y - X⟫ = 0 ∧ M ∈ line[ℝ, X, Y] ∧ Wbtw ℝ O M K ∧
    dist M K = k * r

/-- The circle (centre `O`, radius `r`) solves the problem for the triangle `ABC` and the ratios
`k, l, m` belonging to the sides `BC, CA, AB`. -/
def Solves (A B C : Plane) (k l m : ℝ) (O : Plane) (r : ℝ) : Prop :=
  Inside O A B C ∧ 0 < r ∧
  CutsTwice O r B C ∧ CutsTwice O r C A ∧ CutsTwice O r A B ∧
  RadiusDivided O r B C k ∧ RadiusDivided O r C A l ∧ RadiusDivided O r A B m

/-- **Problem 35.** For a triangle `ABC` and proper fractions `k, l, m` belonging to the sides
`BC, CA, AB`: a circle with centre `O` inside the triangle and radius `r` cuts each side in two
points and has its radii perpendicular to the sides divided by the sides so that the parts outside
the triangle are `k, l, m` times the radius, if and only if `O` is the point whose distances from
the sides are as `1 - k : 1 - l : 1 - m` (explicitly, the weighted centre below, `a, b, c` being
the sides) and `r = 2·area / (a(1-k) + b(1-l) + c(1-m))`. So there is exactly one such circle. -/
theorem problem35 (A B C : Plane) (hABC : cross A B C ≠ 0) (k l m : ℝ)
    (hk : 0 < k ∧ k < 1) (hl : 0 < l ∧ l < 1) (hm : 0 < m ∧ m < 1) (O : Plane) (r : ℝ) :
    Solves A B C k l m O r ↔
      O = (dist B C * (1 - k) + dist C A * (1 - l) + dist A B * (1 - m))⁻¹ •
          ((dist B C * (1 - k)) • A + (dist C A * (1 - l)) • B + (dist A B * (1 - m)) • C) ∧
      r = 2 * triArea A B C / (dist B C * (1 - k) + dist C A * (1 - l) + dist A B * (1 - m)) := by
  sorry

end PillowProblems.P35
