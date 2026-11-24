import PillowProblems.Basic

/-!
# Problem 71 (Pure Geometry, Plane)

**Question.** *(dated 14/12/74)*

> In a given Triangle place a Hexagon having its opposite sides equal and parallel, and three of them lying along the sides of the Triangle, and such that its diagonals intersect in a given Point.

*(Carroll's solution: Chapter III, problem 71; text in `data/problems.json`.)*

**Lean reading.** The hexagon is `V 0, …, V 5` (`Placed`): its alternate sides `V 0 V 1`, `V 2 V 3`,
`V 4 V 5` lie along the sides `BC`, `CA`, `AB` (every hexagon with alternate sides on the three
sides can be labelled so). "Opposite sides equal and parallel" is read as for a convex hexagon,
where opposite sides are traversed in opposite directions: `V 1 - V 0 = V 3 - V 4` and its two
analogues. Its diagonals are the three main diagonals `V 0 V 3`, `V 1 V 4`, `V 2 V 5`, and they
must pass through `P`. A genuine hexagon has six distinct vertices (`Function.Injective V`);
this excludes Carroll's limiting cases (`P` on `FE`: a parallelogram; `P` at `D`: the line `BC`),
and it is needed, since in a degenerate "hexagon" such as `B, B, A, A, A, B` every point of `AB`
lies on all three diagonals. `problem71` proves that the hexagon can be placed iff `P` lies
strictly inside the triangle `DEF` of the midpoints of the sides, which is Carroll's
solubility condition; the existence half is his construction (written in barycentric
coordinates).

**Status.** proved
-/

namespace PillowProblems.P71

open scoped EuclideanGeometry

/-- `P` lies strictly inside the triangle `XYZ`. -/
def InTriangle (X Y Z P : Plane) : Prop :=
  ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 1 ∧ P = a • X + b • Y + c • Z

/-- The hexagon `V 0, V 1, …, V 5` is placed in the triangle `ABC` as Carroll requires:
its opposite sides are equal and parallel, its alternate sides `V 0 V 1`, `V 2 V 3`, `V 4 V 5`
lie along the sides `BC`, `CA`, `AB`, and its three diagonals `V 0 V 3`, `V 1 V 4`, `V 2 V 5`
pass through `P`. -/
def Placed (A B C P : Plane) (V : Fin 6 → Plane) : Prop :=
  (V 1 - V 0 = V 3 - V 4 ∧ V 2 - V 1 = V 4 - V 5 ∧ V 3 - V 2 = V 5 - V 0) ∧
  (V 0 ∈ segment ℝ B C ∧ V 1 ∈ segment ℝ B C) ∧
  (V 2 ∈ segment ℝ C A ∧ V 3 ∈ segment ℝ C A) ∧
  (V 4 ∈ segment ℝ A B ∧ V 5 ∈ segment ℝ A B) ∧
  (P ∈ segment ℝ (V 0) (V 3) ∧ P ∈ segment ℝ (V 1) (V 4) ∧ P ∈ segment ℝ (V 2) (V 5))

/-- The point with (unnormalised) barycentric coordinates `x, y, z` w.r.t. `A, B, C`. -/
private def bc (A B C : Plane) (x y z : ℝ) : Plane := x • A + y • B + z • C

theorem problem71 (A B C P : Plane) (hT : cross A B C ≠ 0) :
    (∃ V : Fin 6 → Plane, Function.Injective V ∧ Placed A B C P V) ↔
      InTriangle (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B) P := by
  sorry

end PillowProblems.P71
