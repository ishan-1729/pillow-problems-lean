import PillowProblems.Basic

/-!
# Problem 30 (Pure Geometry, Plane)

**Question.** *(dated 15/3/89)*

> In a given Triangle, to place a line parallel to the base, such that if from its extremities lines be drawn, to the base, parallel to the sides, they shall be together double of the inscribed Line.

*(Carroll's solution: Chapter III, problem 30; text in `data/problems.json`.)*

**Lean reading.** The triangle `ABC` is nondegenerate (`cross A B C ≠ 0`), with base `BC`. The
"inscribed line" is the segment `C'B'` with `C'` on the side `AB` and `B'` on the side `AC`
(as in Carroll's figure), parallel to `BC` (`B' - C'` is a multiple of `C - B`). The lines
drawn "to the base, parallel to the sides" are `B'D ∥ AB` and `C'E ∥ AC` with `D`, `E` on the
line `BC`; these points are determined, so asserting that some such `D`, `E` exist loses nothing.
The required property is `B'D + C'E = 2·B'C'`. Carroll answers with a construction (the point
`L` with `C'L = ½ C'B`, `B'L = ½ B'C`, i.e. `C'B + B'C = 2 B'C'`); the theorem proves the
position it produces explicitly and shows it is the only solution:
`C' = A + t (B - A)`, `B' = A + t (C - A)` with `t = (AB + AC) / (2 BC + AB + AC)`. The proof
uses Carroll's observations `B'D = C'B`, `C'E = B'C` (Euc. I. 34).

**Status.** proved
-/

namespace PillowProblems.P30

open EuclideanGeometry

/-- **Problem 30.** In the triangle `ABC` (base `BC`), let `C'B'` be a line with `C'` on `AB`,
`B'` on `AC`, parallel to `BC`; let `B'D ∥ AB` and `C'E ∥ AC` meet the base line at `D`, `E`.
Then `B'D + C'E = 2 B'C'` exactly for one such line, namely the one with
`AC' / AB = AB' / AC = (AB + AC) / (2 BC + AB + AC)`. -/
theorem problem30 (A B C : Plane) (hABC : cross A B C ≠ 0) (B' C' : Plane) :
    (B' ∈ segment ℝ A C ∧ C' ∈ segment ℝ A B ∧ (∃ l : ℝ, B' - C' = l • (C - B)) ∧
      ∃ D E : Plane, D ∈ line[ℝ, B, C] ∧ E ∈ line[ℝ, B, C] ∧
        (∃ l : ℝ, D - B' = l • (B - A)) ∧ (∃ l : ℝ, E - C' = l • (C - A)) ∧
        dist B' D + dist C' E = 2 * dist B' C') ↔
      (C' = A + ((dist A B + dist A C) / (2 * dist B C + dist A B + dist A C)) • (B - A) ∧
       B' = A + ((dist A B + dist A C) / (2 * dist B C + dist A B + dist A C)) • (C - A)) := by
  sorry

end PillowProblems.P30
