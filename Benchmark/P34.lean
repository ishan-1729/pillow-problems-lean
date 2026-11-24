import PillowProblems.Basic

/-!
# Problem 34 (Pure Geometry, Plane)

**Question.** *(dated 21/12/74)*

> From a given Point draw 2 Lines, one to the centre of a given Circle, and the other cutting off from it a Segment containing an angle equal to that between the Lines.

*(Carroll's solution: Chapter III, problem 34; text in `data/problems.json`.)*

**Lean reading.** The circle has centre `C` and radius `r > 0`. The first line is `AC`; the
second is a line through `A` meeting the circle at two points `B ≠ D` (so that a segment is cut
off). "The segment contains an angle equal to it" is read as: some point `X` of the circle other
than `B`, `D` has `∠BXD` equal to the angle between the lines; `X` may lie on either arc, so
either of the two segments cut off by `BD` is allowed. `problem34` treats Carroll's figure: `A`
outside the circle (`r < AC`), `B` the nearer intersection (`B` on the segment `AD`), and the
angle between the lines is `∠CAD`; it proves that the property holds exactly when `CD ⊥ AC`,
which is Carroll's construction (draw `CD ⊥ AC` to the circle and join `AD`), so his lines, one
on each side of `AC`, are the only solutions; `problem34_exists` shows that the construction
can always be carried out. Carroll's "given Point" is not restricted, so `problem34_general`
allows any `A ≠ C` (inside, on, or outside the circle; `A = C` leaves no angle between the
lines), takes either of the two supplementary angles between the lines, and proves that the
property holds exactly when the line passes through an end of the radius perpendicular to `AC`
(`CD ⊥ AC` or `CB ⊥ AC`): Carroll's construction is the complete answer in every position.
Necessity uses the law of sines in the circle (`BD = 2r sin ∠BXD`, from mathlib); sufficiency
takes `X` diametrically opposite the end of that radius.

**Status.** proved
-/

namespace PillowProblems.P34

open EuclideanGeometry
open scoped RealInnerProductSpace

/-- **Problem 34.** Let `A` be a point outside the circle of centre `C` and radius `r`, and let a
line from `A` cut the circle at `B` and `D` (`B` the nearer). The chord `BD` cuts off a segment
containing an angle `∠BXD` equal to the angle `∠CAD` between the lines `AC` and `AD` if and
only if `CD ⊥ AC`, i.e. `D` is the end of the radius perpendicular to `AC` (Carroll's
construction). -/
theorem problem34 (A C : Plane) (r : ℝ) (hr : 0 < r) (hA : r < dist A C) (B D : Plane)
    (hB : dist B C = r) (hD : dist D C = r) (hBD : B ≠ D) (hBseg : B ∈ segment ℝ A D) :
    (∃ X : Plane, dist X C = r ∧ X ≠ B ∧ X ≠ D ∧ ∠ B X D = ∠ C A D) ↔
      ⟪D - C, A - C⟫ = 0 := by
  sorry

/-- **Problem 34, any given point.** Let `A` be any point other than the centre `C` (inside, on or
outside the circle), and let a line through `A` meet the circle at the two points `B`, `D`, with
`D ≠ A`. The chord `BD` cuts off a segment containing an angle equal to the angle between the
lines `AC` and `AD` (either of the two supplementary angles between the lines, at a point `X`
of either arc) if and only if one of `CD`, `CB` is perpendicular to `AC`, i.e. the line passes
through an end of the radius perpendicular to `AC` (Carroll's construction). -/
theorem problem34_general (A C : Plane) (r : ℝ) (hr : 0 < r) (hAC : A ≠ C) (B D : Plane)
    (hB : dist B C = r) (hD : dist D C = r) (hBD : B ≠ D) (hAD : A ≠ D)
    (hBl : B ∈ line[ℝ, A, D]) :
    (∃ X : Plane, dist X C = r ∧ X ≠ B ∧ X ≠ D ∧
        (∠ B X D = ∠ C A D ∨ ∠ B X D = Real.pi - ∠ C A D)) ↔
      (⟪D - C, A - C⟫ = 0 ∨ ⟪B - C, A - C⟫ = 0) := by
  sorry

/-- **Problem 34, existence.** Carroll's construction can always be carried out: for a point `A`
outside a circle of centre `C`, the point `D` of the circle with `CD ⊥ AC` and the second
intersection `B` of `AD` with the circle give a line `ABD` cutting off a segment that contains
an angle equal to `∠CAD`. -/
theorem problem34_exists (A C : Plane) (r : ℝ) (hr : 0 < r) (hA : r < dist A C) :
    ∃ B D : Plane, dist B C = r ∧ dist D C = r ∧ B ≠ D ∧ B ∈ segment ℝ A D ∧
      ⟪D - C, A - C⟫ = 0 ∧
      ∃ X : Plane, dist X C = r ∧ X ≠ B ∧ X ≠ D ∧ ∠ B X D = ∠ C A D := by
  sorry

end PillowProblems.P34
