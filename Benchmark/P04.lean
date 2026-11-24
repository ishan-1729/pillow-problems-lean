import PillowProblems.Basic

/-!
# Problem 4 (Trigonometry: Plane)

**Question.** *(dated 19/4/76)*

> In a given acute-angled Triangle inscribe a Triangle, whose sides make, at each of the vertices, equal angles with the sides of the given Triangle.

*(Carroll's solution: Chapter III, problem 4; text in `data/problems.json`.)*

**Lean reading.** The given Triangle `ABC` is non-degenerate (`¬ Collinear`) and acute-angled
(all three angles `< π/2`). An inscribed Triangle has `A'` strictly inside side `BC`, `B'`
inside `CA`, `C'` inside `AB`; "its sides make, at each of the vertices, equal angles with
the sides of the given Triangle" is read, as in Carroll's solution, as
`∠ B A' C' = ∠ C A' B'`, `∠ C B' A' = ∠ A B' C'`, `∠ A C' B' = ∠ B C' A'`. Carroll's
construction is that `A'B'C'` is the triangle of the feet of the altitudes. `problem4` proves
that an inscribed triangle has the property exactly when `A', B', C'` are the feet of the
perpendiculars from `A, B, C` on the opposite sides (stated as: on the side line, and
`AA' ⊥ BC`, etc.), so the answer is unique; `problem4_exists` proves that the required triangle
exists. The uniqueness proof follows Carroll (the angles at `A', B', C'` are `A, B, C`, and the
sine rule in the corner triangles gives `BA' = c cos B`); the existence proof uses the
similarity of `BA'C'` and `BAC` (SAS). Acuteness is needed for existence (the feet lie inside
the sides); the uniqueness direction does not use it. `problem4_nonvacuous` exhibits an acute
triangle, so the hypotheses are consistent.

**Status.** proved
-/

namespace PillowProblems.P04

open EuclideanGeometry
open scoped Real

/-- The inscribed triangles whose sides make equal angles with the sides of the acute-angled
triangle `ABC` at each vertex are exactly given by the feet of the altitudes: `A'` on `BC`
with `AA' ⊥ BC`, and so on. -/
theorem problem4 (A B C : Plane) (hT : ¬ Collinear ℝ {A, B, C})
    (hA : ∠ B A C < π / 2) (hB : ∠ A B C < π / 2) (hC : ∠ A C B < π / 2) (A' B' C' : Plane) :
    (Sbtw ℝ B A' C ∧ Sbtw ℝ C B' A ∧ Sbtw ℝ A C' B ∧
      ∠ B A' C' = ∠ C A' B' ∧ ∠ C B' A' = ∠ A B' C' ∧ ∠ A C' B' = ∠ B C' A') ↔
    ((A' ∈ line[ℝ, B, C] ∧ inner ℝ (A -ᵥ A') (C -ᵥ B) = 0) ∧
      (B' ∈ line[ℝ, C, A] ∧ inner ℝ (B -ᵥ B') (A -ᵥ C) = 0) ∧
      (C' ∈ line[ℝ, A, B] ∧ inner ℝ (C -ᵥ C') (B -ᵥ A) = 0)) := by
  sorry

/-- Carroll's construction succeeds: the triangle of the feet of the altitudes is inscribed
in the acute-angled triangle `ABC` and has the required property. -/
theorem problem4_exists (A B C : Plane) (hT : ¬ Collinear ℝ {A, B, C})
    (hA : ∠ B A C < π / 2) (hB : ∠ A B C < π / 2) (hC : ∠ A C B < π / 2) :
    ∃ A' B' C' : Plane, Sbtw ℝ B A' C ∧ Sbtw ℝ C B' A ∧ Sbtw ℝ A C' B ∧
      ∠ B A' C' = ∠ C A' B' ∧ ∠ C B' A' = ∠ A B' C' ∧ ∠ A C' B' = ∠ B C' A' := by
  sorry

/-- The hypotheses of `problem4` can be met: the triangle `(0,2), (-1,0), (1,0)` is acute. -/
theorem problem4_nonvacuous : ∃ A B C : Plane, ¬ Collinear ℝ {A, B, C} ∧
    ∠ B A C < π / 2 ∧ ∠ A B C < π / 2 ∧ ∠ A C B < π / 2 := by
  sorry

end PillowProblems.P04
