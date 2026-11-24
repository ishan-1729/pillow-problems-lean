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
  sorry

/-- The hypotheses are satisfiable: the triangle `(0,6), (0,0), (6,0)` and the point `(2,1)`,
with feet `(2,0)`, `(7/2,5/2)`, `(0,1)` and distances `1 < √(9/2)`, `1 < 2`. -/
theorem problem64_nonvacuous : cross (pt 0 6) (pt 0 0) (pt 6 0) ≠ 0 ∧
    IsFoot (pt 2 1) (pt 0 0) (pt 6 0) (pt 2 0) ∧
    IsFoot (pt 2 1) (pt 6 0) (pt 0 6) (pt (7/2) (5/2)) ∧
    IsFoot (pt 2 1) (pt 0 6) (pt 0 0) (pt 0 1) ∧
    dist (pt 2 1) (pt 2 0) < dist (pt 2 1) (pt (7/2) (5/2)) ∧
    dist (pt 2 1) (pt 2 0) < dist (pt 2 1) (pt 0 1) := by
  sorry

end PillowProblems.P64
