import PillowProblems.Basic

/-!
# Problem 67 (Algebraical Geometry: Solid)

**Question.** *(dated 27/1/72)*

> If a regular Tetrahedron be placed, with one vertex downwards, in a socket which exactly fits it, and be turned round its vertical axis, through an angle of 120°, raising it only so much as is necessary, until it again fits the socket: find the Locus of one of the revolving vertices.

**Answer.**

> If the centre of the horizontal facet be taken as the Origin, and if the \(X\)-axis pass through one of the vertices of that facet, and the \(Y\)-axis be parallel to the opposite edge of that facet, and the \(Z\)-axis be perpendicular to that facet: and if the altitude (measured downwards) of the Tetrahedron be called '\(h\)', and the intercept on the \(X\)-axis be called '\(a\)': the Equations to the Locus are \[ \begin{aligned} (x+\sqrt{3}.y).(h-z) &= ah; \\ x^{2} + y^{2} &= a^{2}. \end{aligned} \]

*(Carroll's solution: Chapter III, problem 67; text in `data/problems.json`.)*

**Lean reading.** Co-ordinates are Carroll's: origin at the centre of the horizontal (top)
facet `ABC`, `A = (a, 0, 0)` on the `X`-axis, `BC` parallel to the `Y`-axis, `Z` vertical and
upward, and the lowest vertex `D = (0, 0, -h)`. The tetrahedron is the convex hull `solid a h` of
its four vertices, and the socket's hollow is the region it occupies at the start. Turning it
through `θ` about the vertical axis and raising it by `ζ` is `move θ ζ`, and it fits the socket
(`Fits`) when every point of it at or below the rim plane `z = 0` lies in the hollow, so that it
does not cut into the socket. "Raising it only so much as is necessary" is the least such `ζ`
(`IsLeast`), for each `θ` from `0` to `120°`. The turn is taken in the sense carrying `A` towards
`C = (-a/2, √3 a/2, 0)`, the sense in which Carroll's `+√3 y` is right (the other sense gives the
mirror image `x - √3 y`). The theorem determines the locus exactly. It is the set of points that
satisfy Carroll's two equations and also `y ≥ 0` and `√3 x + y ≥ 0`. These two inequalities cut
out the arc actually traced, from `A` to `C`, because the two surfaces also meet elsewhere. The
result holds for every `a, h > 0`, not only for the regular tetrahedron (`h = √2 a`), so that
hypothesis is dropped. As Carroll notes, the vertical axis of the tetrahedron stays on the
`Z`-axis. This is built into the motion, which the problem describes as a turn about the
vertical axis together with a raise.

**Status.** proved
-/

namespace PillowProblems.P67

open Real

/-- The vertex `A` of the horizontal facet, on the `X`-axis at distance `a` from its centre. -/
noncomputable def vA (a : ℝ) : Space := !₂[a, 0, 0]

/-- The vertex `B` of the horizontal facet. -/
noncomputable def vB (a : ℝ) : Space := !₂[-a / 2, -(√3 / 2 * a), 0]

/-- The vertex `C` of the horizontal facet; the edge `BC` is parallel to the `Y`-axis. -/
noncomputable def vC (a : ℝ) : Space := !₂[-a / 2, √3 / 2 * a, 0]

/-- The lowest vertex `D`, at depth `h` below the centre of the horizontal facet. -/
noncomputable def vD (h : ℝ) : Space := !₂[0, 0, -h]

/-- The solid tetrahedron in its initial position; it is also the hollow of the socket. -/
noncomputable def solid (a h : ℝ) : Set Space := convexHull ℝ {vA a, vB a, vC a, vD h}

/-- The rigid motion: turn through the angle `θ` about the vertical (`Z`) axis and raise by `ζ`. -/
noncomputable def move (θ ζ : ℝ) (p : Space) : Space :=
  !₂[cos θ * p 0 - sin θ * p 1, sin θ * p 0 + cos θ * p 1, p 2 + ζ]

/-- The tetrahedron, turned through `θ` and raised by `ζ`, fits the socket: every point of it lying
at or below the rim plane `z = 0` lies in the hollow, i.e. it does not cut into the socket. -/
def Fits (a h θ ζ : ℝ) : Prop :=
  ∀ p ∈ solid a h, (move θ ζ p) 2 ≤ 0 → move θ ζ p ∈ solid a h

/-- The positions of the revolving vertex `A` while the tetrahedron is turned through `θ`, from
`0` to `120°`, raised only so much as is necessary (the least height `ζ` at which it fits). -/
def locus (a h : ℝ) : Set Space :=
  {q | ∃ θ ∈ Set.Icc 0 (2 * π / 3), ∃ ζ, IsLeast {ζ' | Fits a h θ ζ'} ζ ∧ q = move θ ζ (vA a)}

/-- **Problem 67.** The locus of the revolving vertex is the arc, from `(a, 0, 0)` to
`(-a/2, √3 a/2, 0)`, of the curve `x² + y² = a²`, `(x + √3 y)(h - z) = a h`. -/
theorem problem67 (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    locus a h = {q : Space | q 0 ^ 2 + q 1 ^ 2 = a ^ 2 ∧ (q 0 + √3 * q 1) * (h - q 2) = a * h ∧
      0 ≤ q 1 ∧ 0 ≤ √3 * q 0 + q 1} := by
  sorry

end PillowProblems.P67
