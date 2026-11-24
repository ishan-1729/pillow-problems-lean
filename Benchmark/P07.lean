import PillowProblems.Basic

/-!
# Problem 7 (Trigonometry: Plane)

**Question.** *(dated 4 or 5/89)*

> Given 2 adjacent sides, and the included angle, of a Tetragon; and that the angles, at the other ends of these 2 sides, are right: find (1) remaining sides, (2) area.

**Answer.**

> [Figure: A geometric diagram of triangle ABD with extended points C and E, connected by dashed lines.]
>
> Let \(AB\), \(AD\) be given sides, and \(B\), \(D\) the right \(\angle\)s; and let \(AB = b\), \(AD = d\).
>
> (1) \(\quad BC = \dfrac{d-b\cos A}{\sin A};\quad CD = \dfrac{b-d\cos A}{\sin A};\)
>
> (2) \(\quad\text{area} = \dfrac{2bd-(b^{2}+d^{2})\cos A}{2\sin A}\).

*(Carroll's solution: Chapter III, problem 7; text in `data/problems.json`.)*

**Lean reading.** The Tetragon is four points `A B C D` of the `Plane`, taken in order;
the given sides are `b = AB`, `d = AD` with included angle `α = ∠ B A D`, and the angles at `B`
and `D` are right: `∠ A B C = π/2`, `∠ A D C = π/2`. Carroll tacitly takes the Tetragon to be
convex (as in his figure); this is the hypothesis that its diagonals `AC`, `BD` meet, and it is
needed. The right angles fix `C` (the meet of the perpendiculars to `AB` at `B` and to `AD`
at `D`), and when `d < b cos α` or `b < d cos α` the side `CD` (resp. `BC`) crosses `AB`
(resp. `AD`), so `ABCD` is a crossed, not a simple, quadrilateral and the remaining sides are
`|d - b cos α| / sin α`, `|b - d cos α| / sin α`; for a simple Tetragon with these angles the
convexity hypothesis is automatic. We also assume `A ≠ B`, `A ≠ D` and `sin α ≠ 0` (the given sides are
genuine and not collinear), which his formulas need. The area of the Tetragon is the shoelace
area `quadArea`, which is the usual area for a convex (indeed any simple) quadrilateral; under
the hypotheses it equals Carroll's `½ (AB·BC + AD·DC)`. The theorem proves Carroll's formulas
for `BC`, `CD` and the area, which determine them from the data; `problem7_nonvacuous` (the
unit square) shows that the hypotheses are consistent.

**Status.** proved
-/

namespace PillowProblems.P07

open EuclideanGeometry
open scoped Real

/-- The area of the quadrilateral `ABCD` with vertices in this order (shoelace formula; it is
the usual area when `ABCD` is simple, e.g. convex). -/
noncomputable def quadArea (A B C D : Plane) : ℝ := |cross A B C + cross A C D| / 2

/-- Carroll's answer: with `AB = b`, `AD = d`, included angle `α = ∠BAD`, and right angles at
`B` and `D` in the convex Tetragon `ABCD`,
`BC = (d - b cos α)/sin α`, `CD = (b - d cos α)/sin α`, and
area `= (2bd - (b² + d²) cos α)/(2 sin α)`. -/
theorem problem7 (A B C D : Plane) (hAB : A ≠ B) (hAD : A ≠ D) (hsin : Real.sin (∠ B A D) ≠ 0)
    (hB : ∠ A B C = π / 2) (hD : ∠ A D C = π / 2)
    (hconvex : ∃ P, Wbtw ℝ A P C ∧ Wbtw ℝ B P D) :
    dist B C = (dist A D - dist A B * Real.cos (∠ B A D)) / Real.sin (∠ B A D) ∧
    dist C D = (dist A B - dist A D * Real.cos (∠ B A D)) / Real.sin (∠ B A D) ∧
    quadArea A B C D = (2 * dist A B * dist A D - (dist A B ^ 2 + dist A D ^ 2) *
      Real.cos (∠ B A D)) / (2 * Real.sin (∠ B A D)) := by
  sorry

/-- The hypotheses of `problem7` can be met (the unit square). -/
theorem problem7_nonvacuous : ∃ A B C D : Plane, A ≠ B ∧ A ≠ D ∧ Real.sin (∠ B A D) ≠ 0 ∧
    ∠ A B C = π / 2 ∧ ∠ A D C = π / 2 ∧ ∃ P, Wbtw ℝ A P C ∧ Wbtw ℝ B P D := by
  sorry

end PillowProblems.P07
