import PillowProblems.Basic

/-!
# Problem 15 (Pure Geometry, Plane)

**Question.** *(dated 3/91)*

> If a Figure be such that the opposite angles of every inscribed Tetragon are supplementary: the Figure is a Circle.

*(Carroll's solution: Chapter III, problem 15; text in `data/problems.json`.)*

**Lean reading.** "Figure" is not defined by Carroll; his proof treats it as a closed oval whose
perimeter, cut by a chord `AC`, falls into two portions on either side of `AC`, and his inscribed
tetragons have their vertices in order round the perimeter. We read it as a convex region: a
compact convex set `K` with non-empty interior, whose perimeter is `frontier K`. An inscribed
tetragon `ABCD` (`InscribedTetragon`) has its four vertices on the perimeter and is a genuine
convex quadrilateral in the order `A, B, C, D`: its diagonals cross (`B`, `D` strictly on opposite
sides of `AC` and `A`, `C` strictly on opposite sides of `BD`, sides measured by `cross`).
The hypothesis is that every such tetragon has `∠ABC + ∠CDA = π` (unoriented angles; the other
pair of opposite angles is the case `BCDA`), and the conclusion that the perimeter is a circle:
`frontier K = sphere O r` with `r > 0`. The proof follows Carroll (fix `A`, `C`, `D` and show
every other perimeter point lies on the circle `ACD`), choosing `A, C` and `B, D` on two
perpendicular chords through an interior point; it also proves what Carroll leaves tacit, that no
three perimeter points are collinear, so that the tetragons used are genuine. Non-convex figures
are not covered. `problem15_nonvacuous` shows the hypotheses are satisfied by a disc.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P15

open EuclideanGeometry
open scoped Real

/-- `ABCD` is a tetragon inscribed in the figure `S`: its four vertices lie on `S` and it is a
genuine (convex, non-degenerate) quadrilateral with the vertices in this order, i.e. its
diagonals cross: `B`, `D` lie strictly on opposite sides of the line `AC`, and `A`, `C` strictly
on opposite sides of the line `BD`. -/
def InscribedTetragon (S : Set Plane) (A B C D : Plane) : Prop :=
  A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ D ∈ S ∧ cross A C B * cross A C D < 0 ∧ cross B D A * cross B D C < 0

/-! ### Coordinates -/

/-- `(A - X) · (C - X)`. -/
private def dt (A C X : Plane) : ℝ := (A 0 - X 0) * (C 0 - X 0) + (A 1 - X 1) * (C 1 - X 1)

/-! ### Convexity facts -/

/-! ### No three points of the figure are collinear -/

/-! ### Diagonals through a common interior point -/

/-! ### The theorem -/

/-- If every tetragon inscribed in (the boundary of) a convex figure has supplementary opposite
angles, the boundary of the figure is a circle. -/
theorem problem15 (K : Set Plane) (hconv : Convex ℝ K) (hcpt : IsCompact K)
    (hint : (interior K).Nonempty)
    (h : ∀ A B C D, InscribedTetragon (frontier K) A B C D → ∠ A B C + ∠ C D A = π) :
    ∃ O : Plane, ∃ r : ℝ, 0 < r ∧ frontier K = Metric.sphere O r := by
  sorry

/-- The hypotheses of `problem15` are satisfied by a circle (the boundary of a disc): this is
the classical fact that opposite angles of a cyclic quadrilateral are supplementary. -/
theorem problem15_nonvacuous :
    Convex ℝ (Metric.closedBall (0 : Plane) 1) ∧ IsCompact (Metric.closedBall (0 : Plane) 1) ∧
      (interior (Metric.closedBall (0 : Plane) 1)).Nonempty ∧
      ∀ A B C D, InscribedTetragon (frontier (Metric.closedBall (0 : Plane) 1)) A B C D →
        ∠ A B C + ∠ C D A = π := by
  sorry

end PillowProblems.P15
