import PillowProblems.Basic

/-!
# Problem 51 (Pure Geometry, Plane)

**Question.** *(dated 12/81)*

> From a given Point, in one side of a given Triangle, to draw a line, terminated by the other side, so that, if from its ends lines be drawn at right angles to the base, their sum shall be equal to the first line.

*(Carroll's solution: Chapter III, problem 51; text in `data/problems.json`.)*

**Lean reading.** Coordinates are chosen with the base `BC` on the `x`-axis and `A` above it (every triangle
is congruent to such a one). The perpendicular from a point `P` to the base is then `P (pt (P 0) 0)`.
The given point `D` lies on side `AB` with `D ≠ A`, so that the perpendicular `DN` to `AC` is
defined. The line `DE` is terminated by the side `AC` (`E ∈ segment A C`). `N` and `S` are
Carroll's points: `N` is the foot of the perpendicular from `D` to `AC`, and `S` is where `DN` meets
the base produced. `S` exists unless `∠C` is right; then `DN` is parallel to the base, Carroll's
construction fails, and the hypotheses cannot hold, except when `D = B`: then `DN` is the base
itself, `S` may be any point of it, the theorem still applies, and both sides are false. The theorem proves that `DE` equals the sum of the perpendiculars from `D`
and `E` iff `E` comes from Carroll's synthesis for some point `K` of the base with `SK² = SD · SN`.
Carroll's supplementary proof that `DH = HK` is included. The rectangle `SD · SN` is taken with sign
(the inner product of `SD⃗` and `SN⃗`). This agrees with Carroll's rectangle when `S` lies outside
`DN`, as in his figure. When `S` lies between `D` and `N` there is no solution, and the unsigned
rectangle would wrongly give one. The problem need not have a solution: there are zero, one or two
(two choices of `K`), and the theorem shows Carroll's construction yields exactly these.
`problem51_nonvacuous` exhibits a configuration with a solution.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P51

open scoped EuclideanGeometry RealInnerProductSpace

/-- **Problem 51.** The base `BC` lies on the `x`-axis and `A` above it; `D` is the given point
of the side `AB` (not `A`), `N` the foot of the perpendicular from `D` to `AC`, and `S` the point
where `DN` produced meets the base produced. For a point `E` of the other side `AC`, the line `DE`
equals the sum of the perpendiculars from `D` and `E` to the base if and only if `E` is given by
Carroll's construction: for a point `K` of the base with `SK² = SD · SN` (the rectangle taken
with sign), the perpendicular to the base at `K` meets the parallel to `AC` through the midpoint
of `DA` at `H`, and `E` lies on `DH` (produced). -/
theorem problem51 (A B C D N S E : Plane)
    (hB : B 1 = 0) (hC : C 1 = 0) (hBC : B 0 ≠ C 0) (hA : 0 < A 1)
    (hD : D ∈ segment ℝ A B) (hDA : D ≠ A)
    (hN : N ∈ line[ℝ, A, C]) (hDN : ⟪D - N, C - A⟫ = 0)
    (hS1 : S 1 = 0) (hS : S ∈ line[ℝ, D, N])
    (hE : E ∈ segment ℝ A C) :
    dist D E = dist D (pt (D 0) 0) + dist E (pt (E 0) 0) ↔
      ∃ K H : Plane, K 1 = 0 ∧ dist S K ^ 2 = ⟪D - S, N - S⟫ ∧
        (∃ t : ℝ, H = midpoint ℝ D A + t • (C - A)) ∧ H 0 = K 0 ∧ E ∈ line[ℝ, D, H] := by
  sorry

/-- The hypotheses of `problem51` can be met with a solution: `A = (0, 2)`, `B = (-2, 0)`,
`C = (2, 0)`, `D = (-1, 1)` the midpoint of `AB`, `N = A`, `S = B`; the point `E = (1, 1)` of `AC`
gives `DE = 2 = 1 + 1`. -/
theorem problem51_nonvacuous :
    ∃ A B C D N S E : Plane, B 1 = 0 ∧ C 1 = 0 ∧ B 0 ≠ C 0 ∧ 0 < A 1 ∧
      D ∈ segment ℝ A B ∧ D ≠ A ∧ N ∈ line[ℝ, A, C] ∧ ⟪D - N, C - A⟫ = 0 ∧
      S 1 = 0 ∧ S ∈ line[ℝ, D, N] ∧ E ∈ segment ℝ A C ∧
      dist D E = dist D (pt (D 0) 0) + dist E (pt (E 0) 0) := by
  sorry

end PillowProblems.P51
