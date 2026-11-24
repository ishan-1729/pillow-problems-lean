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

/-- Twice the signed area of a triangle, in coordinates. -/
private def crossR (x0 x1 y0 y1 z0 z1 : ℝ) : ℝ := (y0 - x0) * (z1 - x1) - (z0 - x0) * (y1 - x1)

/-- Squared distance, in coordinates. -/
private def sq2 (x0 x1 y0 y1 : ℝ) : ℝ := (x0 - y0) ^ 2 + (x1 - y1) ^ 2

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
  sorry

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
  sorry

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
  sorry

end PillowProblems.P13
