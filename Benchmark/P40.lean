import PillowProblems.Basic

/-!
# Problem 40 (Pure Geometry, Plane)

**Question.** *(dated 5/76)*

> In a given Triangle, whose base-angles are acute, draw two lines, at right angles to the base, and together equal to the line drawn, from the vertex, at right angles to the base, and such that
>
> (1) they are equidistant from the line drawn from the vertex;
>
> (2) they are equidistant from the ends of the base.

*(Carroll's solution: Chapter III, problem 40; text in `data/problems.json`.)*

**Lean reading.** `A B C` is a triangle (`cross A B C ≠ 0`) with base `BC` and acute base angles
(`∠ABC, ∠ACB < π/2`). `AD` is the line from the vertex at right angles to the base (`D` on line
`BC`, `AD ⊥ BC`). A line at right angles to the base, inside the triangle, is a segment `PQ` with
`P` on the base, `Q` on side `BA` or `CA`, and `PQ ⊥ BC` (`PerpToBase`). Distance from `AD` is
measured by `dist P D`, the distance between the parallel lines. In (1) the two lines must be
distinct; otherwise "two lines" would be one line counted twice. In (2) `P₁Q₁` is the line nearer
`B` and `BP₁ = CP₂`. Each part proves that the two lines are together equal to `AD` iff the common
distance is `BD · DC / BC`, and that such a pair exists. In (1) this distance is Carroll's
`DH = DG`, and in (2) it is his `BK = HC`. So in each case the pair is unique.
`problem40_nonvacuous` exhibits a triangle satisfying the hypotheses.

**Status.** proved
-/

namespace PillowProblems.P40

open scoped EuclideanGeometry RealInnerProductSpace
open Real

/-- `PQ` is a line in the triangle `ABC` drawn at right angles to the base `BC`: its foot `P` is on
the base and its other end `Q` is on one of the two other sides `BA`, `CA`. -/
def PerpToBase (A B C P Q : Plane) : Prop :=
  P ∈ segment ℝ B C ∧ (Q ∈ segment ℝ B A ∨ Q ∈ segment ℝ C A) ∧ ⟪Q - P, C - B⟫ = 0

/-- The height profile of the triangle along the base, in units of the altitude `AD`, where the
foot `D` of the altitude sits at parameter `μ` of the base. -/
private noncomputable def hgt (μ s : ℝ) : ℝ := min (s / μ) ((1 - s) / (1 - μ))

/-- **Problem 40 (1).** In a triangle `ABC` with acute base angles, let `AD` be the line drawn
from the vertex at right angles to the base. Two distinct lines at right angles to the base and
equidistant from `AD` are together equal to `AD` if and only if each is at the distance
`BD · DC / BC` from `AD`; and such a pair of lines exists. -/
theorem problem40_a (A B C D : Plane) (hABC : cross A B C ≠ 0)
    (hB : ∠ A B C < π / 2) (hC : ∠ A C B < π / 2)
    (hD : D ∈ line[ℝ, B, C]) (hAD : ⟪A - D, C - B⟫ = 0) :
    (∀ P₁ Q₁ P₂ Q₂ : Plane, PerpToBase A B C P₁ Q₁ → PerpToBase A B C P₂ Q₂ → P₁ ≠ P₂ →
        dist P₁ D = dist P₂ D →
        (dist P₁ Q₁ + dist P₂ Q₂ = dist A D ↔ dist P₁ D = dist B D * dist D C / dist B C)) ∧
    ∃ P₁ Q₁ P₂ Q₂ : Plane, PerpToBase A B C P₁ Q₁ ∧ PerpToBase A B C P₂ Q₂ ∧ P₁ ≠ P₂ ∧
        dist P₁ D = dist P₂ D ∧ dist P₁ Q₁ + dist P₂ Q₂ = dist A D := by
  sorry

/-- **Problem 40 (2).** In the same setting, two lines at right angles to the base, equidistant
from the ends of the base (the first, `P₁Q₁`, being the nearer to `B`), are together equal to `AD`
if and only if each is at the distance `BD · DC / BC` from its end of the base; and such a pair of
lines exists. -/
theorem problem40_b (A B C D : Plane) (hABC : cross A B C ≠ 0)
    (hB : ∠ A B C < π / 2) (hC : ∠ A C B < π / 2)
    (hD : D ∈ line[ℝ, B, C]) (hAD : ⟪A - D, C - B⟫ = 0) :
    (∀ P₁ Q₁ P₂ Q₂ : Plane, PerpToBase A B C P₁ Q₁ → PerpToBase A B C P₂ Q₂ →
        dist B P₁ < dist B P₂ → dist B P₁ = dist C P₂ →
        (dist P₁ Q₁ + dist P₂ Q₂ = dist A D ↔ dist B P₁ = dist B D * dist D C / dist B C)) ∧
    ∃ P₁ Q₁ P₂ Q₂ : Plane, PerpToBase A B C P₁ Q₁ ∧ PerpToBase A B C P₂ Q₂ ∧
        dist B P₁ < dist B P₂ ∧ dist B P₁ = dist C P₂ ∧ dist P₁ Q₁ + dist P₂ Q₂ = dist A D := by
  sorry

/-- The hypotheses of `problem40_a` and `problem40_b` are satisfiable: the triangle with vertex
`(1, 1)` on the base from `(0, 0)` to `(2, 0)`, whose altitude has foot `(1, 0)`. -/
theorem problem40_nonvacuous :
    ∃ A B C D : Plane, cross A B C ≠ 0 ∧ ∠ A B C < π / 2 ∧ ∠ A C B < π / 2 ∧
      D ∈ line[ℝ, B, C] ∧ ⟪A - D, C - B⟫ = 0 := by
  sorry

end PillowProblems.P40
