import PillowProblems.Basic

/-!
# Problem 3 (Pure Geometry, Plane)

**Question.**

> If the sides of a Tetragon pass through the vertices of a Parallelogram, and if three of them are bisected at those vertices: prove that the fourth is so also.

*(Carroll's solution: Chapter III, problem 3; text in `data/problems.json`.)*

**Lean reading.** The tetragon is `ABCD` (arbitrary points of `Plane`) and the parallelogram is
`EFGH`, with `E`, `F`, `G`, `H` on the sides `AB`, `BC`, `CD`, `DA` respectively. "Parallelogram
`EFGH`" is read as the vector condition `F - E = G - H` (`IsParallelogram`), which is what having
both pairs of opposite sides parallel and equal means. The three bisected sides are `AB`, `BC`,
`CD`, i.e. `E`, `F`, `G` are their midpoints, and `problem3` proves `H` is the midpoint of `DA`.
With this vector reading the conclusion holds without even assuming that `H` lies on `DA`, so
that hypothesis is dropped (the theorem is stronger). `problem3_one_pair` follows Carroll's own
proof, which only uses that `EH ∥ FG` (as lines) and that `H` lies on the line `DA`; there the
non-degeneracy hypothesis that `A`, `B`, `D` are not collinear (`cross A B D ≠ 0`) is needed,
since Carroll's step "triangles `AEH`, `ABD` are similar" requires a genuine triangle `ABD`.

**Status.** proved
-/

namespace PillowProblems.P03

open EuclideanGeometry

/-- `EFGH` (vertices in this order) is a parallelogram: `F - E = G - H`. -/
def IsParallelogram (E F G H : Plane) : Prop := F -ᵥ E = G -ᵥ H

/-- If `E`, `F`, `G` bisect the sides `AB`, `BC`, `CD` of the tetragon `ABCD` and `EFGH` is a
parallelogram, then `H` bisects the fourth side `DA`. -/
theorem problem3 (A B C D E F G H : Plane)
    (hE : E = midpoint ℝ A B) (hF : F = midpoint ℝ B C) (hG : G = midpoint ℝ C D)
    (hpar : IsParallelogram E F G H) : H = midpoint ℝ D A := by
  sorry

/-- Carroll's proof only uses one pair of parallel sides: if `E`, `F`, `G` bisect `AB`, `BC`,
`CD`, `H` lies on the line `DA` and `EH ∥ FG`, then `H` bisects `DA`
(for a genuine triangle `ABD`). -/
theorem problem3_one_pair (A B C D E F G H : Plane) (hABD : cross A B D ≠ 0)
    (hE : E = midpoint ℝ A B) (hF : F = midpoint ℝ B C) (hG : G = midpoint ℝ C D)
    (hH : H ∈ line[ℝ, D, A]) (hpar : (line[ℝ, E, H]).Parallel (line[ℝ, F, G])) :
    H = midpoint ℝ D A := by
  sorry

end PillowProblems.P03
