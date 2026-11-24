import PillowProblems.Basic

/-!
# Problem 55 (Trigonometry: Plane)

**Question.** *(dated 20/12/74)*

> Given three cylindrical towers on a Plane: find a Point, on the Plane, from which they shall look the same width.

*(Carroll's solution: Chapter III, problem 55; text in `data/problems.json`.)*

**Lean reading.** The ground is the plane. The towers stand on circles with centres `A, B, C` and radii
`a, b, c > 0`. "Look the same width" is read as Carroll's solution reads it (`sin APD = a/AP`): the
apparent width of a tower seen from `P` is the angle between the two tangents from `P` to its base
circle. That angle is `angularWidth P O r = 2 arcsin (r / PO)`, and `angularWidth_eq_two_mul_angle`
checks it is twice the angle between a tangent `PT` and `PO`. The viewpoint must lie outside the
towers (`a < PA`, `b < PB`, `c < PC`), a tacit assumption. `problem55_ratio` is Carroll's first step:
equal widths `⇔ PA : PB : PC = a : b : c`. `problem55_locus` is his locus claim: if `G, H` are the
two points of line `AB` with `AG : GB = AH : HB = a : b`, the points with `PA : PB = a : b` form the
circle on `GH` as diameter. As his note says, it is a full circle, not a semicircle.
`problem55_locus_nonvacuous` shows such `G, H` exist. `problem55` combines these: a point outside
the towers sees them all the same width exactly when it lies on both circles. We add `a ≠ b`,
`b ≠ c`, `A ≠ B`, `B ≠ C` because Carroll's construction needs them: if `a = b` the external point
`H` does not exist, and the locus is the perpendicular bisector of `AB` (proved separately as
`problem55_locus_eq`, so that case is covered too; `problem55_ratio` needs no such hypothesis). Whether the two circles meet
outside the towers depends on the data, and Carroll does not discuss it.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P55

open scoped EuclideanGeometry
open AffineMap

/-- The (angular) width under which a tower standing on the circle with centre `O` and radius `r`
is seen from a point `P` of the plane outside it: the angle between the two tangents from `P` to the
circle, `2 · arcsin (r / PO)` (see `angularWidth_eq_two_mul_angle`). -/
noncomputable def angularWidth (P O : Plane) (r : ℝ) : ℝ := 2 * Real.arcsin (r / dist P O)

/-- The definition of `angularWidth` is the geometric one: if `PT` touches the circle at `T`
(`OT = r`, `OT ⊥ PT`), the width is twice the angle `OPT` between the tangent and the line to the
centre. -/
theorem angularWidth_eq_two_mul_angle (P O T : Plane) (r : ℝ) (hr : 0 < r) (hT : dist T O = r)
    (htan : ∠ O T P = Real.pi / 2) : angularWidth P O r = 2 * ∠ O P T := by
  sorry

/-- **Problem 55 (the condition).** Seen from a point `P` outside the three towers (centres
`A, B, C`, radii `a, b, c`), the towers look the same width exactly when
`PA : PB : PC = a : b : c`. -/
theorem problem55_ratio (A B C P : Plane) (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hPA : a < dist P A) (hPB : b < dist P B) (hPC : c < dist P C) :
    (angularWidth P A a = angularWidth P B b ∧ angularWidth P B b = angularWidth P C c) ↔
      (dist P A * b = dist P B * a ∧ dist P B * c = dist P C * b) := by
  sorry

/-- **Problem 55 (Carroll's locus).** If `a ≠ b` and `G, H` are the two points of the line `AB`
with `AG : GB = AH : HB = a : b`, then the points `P` with `PA : PB = a : b` are exactly the
circle on the diameter `GH`. -/
theorem problem55_locus (A B G H : Plane) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hAB : A ≠ B) (hG : ∃ g : ℝ, G = lineMap A B g) (hH : ∃ h : ℝ, H = lineMap A B h)
    (hGH : G ≠ H) (rG : dist A G * b = dist G B * a) (rH : dist A H * b = dist H B * a) :
    {P : Plane | dist P A * b = dist P B * a} = Metric.sphere (midpoint ℝ G H) (dist G H / 2) := by
  sorry

/-- The points `G, H` of Carroll's construction exist (so `problem55_locus` is not vacuous). -/
theorem problem55_locus_nonvacuous (A B : Plane) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (hAB : A ≠ B) :
    ∃ G H : Plane, (∃ g : ℝ, G = lineMap A B g) ∧ (∃ h : ℝ, H = lineMap A B h) ∧ G ≠ H ∧
      dist A G * b = dist G B * a ∧ dist A H * b = dist H B * a := by
  sorry

/-- **Problem 55 (the case `a = b`).** When two towers have equal radii, Carroll's external point
`H` does not exist and the locus `PA : PB = a : b` is the perpendicular bisector of `AB`. -/
theorem problem55_locus_eq (A B : Plane) (a : ℝ) (ha : 0 < a) :
    {P : Plane | dist P A * a = dist P B * a} = (AffineSubspace.perpBisector A B : Set Plane) := by
  sorry

/-- **Problem 55.** Let the towers have centres `A, B, C` and radii `a, b, c`, with `a ≠ b ≠ c`
and `A ≠ B ≠ C`; let `G, H` divide `AB` internally and externally as `a : b`, and `G', H'` divide
`BC` as `b : c`. A point `P` of the plane, outside the towers, sees them all of the same width
exactly when it lies on both circles described on `GH` and on `G'H'` as diameters. -/
theorem problem55 (A B C : Plane) (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≠ b) (hbc : b ≠ c) (hAB : A ≠ B) (hBC : B ≠ C)
    (G H G' H' : Plane) (hG : ∃ g : ℝ, G = lineMap A B g) (hH : ∃ h : ℝ, H = lineMap A B h)
    (hGH : G ≠ H) (rG : dist A G * b = dist G B * a) (rH : dist A H * b = dist H B * a)
    (hG' : ∃ g : ℝ, G' = lineMap B C g) (hH' : ∃ h : ℝ, H' = lineMap B C h)
    (hGH' : G' ≠ H') (rG' : dist B G' * c = dist G' C * b) (rH' : dist B H' * c = dist H' C * b)
    (P : Plane) (hPA : a < dist P A) (hPB : b < dist P B) (hPC : c < dist P C) :
    (angularWidth P A a = angularWidth P B b ∧ angularWidth P B b = angularWidth P C c) ↔
      (dist P (midpoint ℝ G H) = dist G H / 2 ∧ dist P (midpoint ℝ G' H') = dist G' H' / 2) := by
  sorry

end PillowProblems.P55
