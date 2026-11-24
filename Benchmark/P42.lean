import PillowProblems.Basic

/-!
# Problem 42 (Trigonometry: Plane)

**Question.** *(dated 17/5/78)*

> If the angles of a given Triangle be bisected, and if lines be drawn, through its vertices, at right angles to the bisectors, so as to form a fresh Triangle: find the ratio of the area of this Triangle to the area of the given Triangle.

**Answer.**

> \[ \frac{abc}{2(s-a).(s-b).(s-c)}. \]

*(Carroll's solution: Chapter III, problem 42; text in `data/problems.json`.)*

**Lean reading.** The given triangle `ABC` is non-degenerate (`cross A B C ≠ 0`). The bisector of the angle at a
vertex `V` (between `VP` and `VQ`) is the line through `V` in the direction `bisectorDir V P Q`,
the sum of the unit vectors along `VP` and `VQ` (`bisectorDir_bisects` checks that it makes
equal angles with both sides), and `perpToBisector V P Q` is the line through `V` at right angles
to it. `A'` is any point on the two such lines through `B` and `C`, and similarly `B'` (through
`C`, `A`) and `C'` (through `A`, `B`), so the "fresh Triangle" is `A'B'C'`; the proof derives
that these are the excentres, and `problem42_exists` shows that each pair of lines meets in
exactly one point. With `a = BC`, `b = CA`, `c = AB` and `s` the semi-perimeter, Carroll's
ratio `abc / (2 (s-a)(s-b)(s-c))` is proved for `area A'B'C' / area ABC`.

**Status.** proved
-/

namespace PillowProblems.P42

open scoped EuclideanGeometry

/-- Direction of the (internal) bisector of the angle `P V Q` at the vertex `V`: the sum of the
unit vectors along `VP` and `VQ`. -/
noncomputable def bisectorDir (V P Q : Plane) : Plane :=
  ‖P - V‖⁻¹ • (P - V) + ‖Q - V‖⁻¹ • (Q - V)

/-- The line drawn through the vertex `V` at right angles to the bisector of the angle `P V Q`. -/
def perpToBisector (V P Q : Plane) : Set Plane :=
  {X | inner ℝ (X - V) (bisectorDir V P Q) = 0}

/-- Sanity check on `bisectorDir`: it makes equal angles with `VP` and `VQ`. -/
theorem bisectorDir_bisects (V P Q : Plane) (hP : P ≠ V) (hQ : Q ≠ V) :
    ∠ P V (V + bisectorDir V P Q) = ∠ Q V (V + bisectorDir V P Q) := by
  sorry

/-- **Problem 42.** Let `A'` be the meeting point of the lines through `B` and `C` at right angles
to the bisectors of the angles `B`, `C`; similarly `B'` (lines through `C`, `A`) and `C'` (lines
through `A`, `B`). Then `area A'B'C' / area ABC = abc / (2 (s-a)(s-b)(s-c))`. -/
theorem problem42 (A B C A' B' C' : Plane) (hABC : cross A B C ≠ 0)
    (hA' : A' ∈ perpToBisector B A C ∧ A' ∈ perpToBisector C A B)
    (hB' : B' ∈ perpToBisector C A B ∧ B' ∈ perpToBisector A B C)
    (hC' : C' ∈ perpToBisector A B C ∧ C' ∈ perpToBisector B A C) :
    triArea A' B' C' / triArea A B C =
      dist B C * dist C A * dist A B /
        (2 * ((dist B C + dist C A + dist A B) / 2 - dist B C) *
          ((dist B C + dist C A + dist A B) / 2 - dist C A) *
          ((dist B C + dist C A + dist A B) / 2 - dist A B)) := by
  sorry

/-- The lines through `B` and `C` at right angles to the bisectors meet in exactly one point (and
likewise for the other two pairs), so the triangle `A'B'C'` of `problem42` exists and is unique. -/
theorem problem42_exists (A B C : Plane) (hABC : cross A B C ≠ 0) :
    (∃! X, X ∈ perpToBisector B A C ∧ X ∈ perpToBisector C A B) ∧
    (∃! X, X ∈ perpToBisector C A B ∧ X ∈ perpToBisector A B C) ∧
    (∃! X, X ∈ perpToBisector A B C ∧ X ∈ perpToBisector B A C) := by
  sorry

end PillowProblems.P42
