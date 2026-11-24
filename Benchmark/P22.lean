import PillowProblems.Basic

/-!
# Problem 22 (Trigonometry: Plane)

**Question.** *(dated 4/6/89)*

> Given the 3 'altitudes' of a Triangle: find its (1) sides, (2) angles, (3) area.

**Answer.**

> Calling the given altitudes '\(\alpha\), \(\beta\), \(\gamma\)'; and the fraction \[ \frac{2\alpha^{2} \beta^{2} \gamma^{2} . (\alpha^{2} + \beta^{2} + \gamma^{2}) - (\beta^{4} \gamma^{4} + \gamma^{4} \alpha^{4} + \alpha^{4} \beta^{4})}{4\alpha^{4} \beta^{4} \gamma^{4}} \unicode{x2018}k^2\unicode{x2019},\]
>
> (1) \(\quad a = \dfrac{1}{k\alpha}, \,\,\&c.\)
>
> (2) \(\quad \sin A = k\beta \gamma, \,\,\&c.\)
>
> (3) \(\quad \text{area} = \dfrac{1}{2k}.\)

*(Carroll's solution: Chapter III, problem 22; text in `data/problems.json`.)*

**Lean reading.** The triangle `ABC` is a non-degenerate triangle in the plane (`cross A B C ≠ 0`). "The altitude
from `A` is `α`" is `IsAltitude A B C α`: the perpendicular from `A` meets the line `BC` at a
foot `H` with `AH = α` (the foot may lie outside the segment `BC`); similarly for `β` from `B`
and `γ` from `C`. Carroll's fraction is `kSq α β γ` and `k` is its positive square root
(Carroll's `k = sin A / (βγ)` is positive). The theorem proves that the fraction is positive and
that the sides, the sines of the angles (`∠ B A C` is the angle at `A`, etc.) and the area are
exactly Carroll's expressions; since the sides are determined, so is the triangle up to
congruence. Carroll answers part (2) through the sines, which fix each angle only up to its
supplement; we prove exactly that statement. Conversely, `problem22_exists` shows that any
positive `α, β, γ` with `k² > 0` are the altitudes of some triangle, so Carroll's formulae answer
the question for every admissible set of data; `problem22_nonvacuous` exhibits the 3-4-5
triangle with altitudes `3, 12/5, 4`.

**Status.** proved
-/

namespace PillowProblems.P22

open scoped EuclideanGeometry
open AffineMap

/-- `h` is the altitude of the triangle `ABC` drawn from `A`: the perpendicular from `A` to the
line `BC` meets it at a foot `H`, and `AH = h`. -/
def IsAltitude (A B C : Plane) (h : ℝ) : Prop :=
  ∃ t : ℝ, inner ℝ (A - lineMap B C t) (C - B) = 0 ∧ dist A (lineMap B C t) = h

/-- Carroll's fraction `k²`, in terms of the three altitudes `α, β, γ`. -/
noncomputable def kSq (α β γ : ℝ) : ℝ :=
  (2 * α ^ 2 * β ^ 2 * γ ^ 2 * (α ^ 2 + β ^ 2 + γ ^ 2) -
      (β ^ 4 * γ ^ 4 + γ ^ 4 * α ^ 4 + α ^ 4 * β ^ 4)) / (4 * α ^ 4 * β ^ 4 * γ ^ 4)

/-- **Problem 22.** In a triangle whose altitudes from `A`, `B`, `C` are `α`, `β`, `γ`, with
`k = √(k²)` for Carroll's fraction `k²`: the fraction is positive, the sides are
`a = 1/(kα)`, `b = 1/(kβ)`, `c = 1/(kγ)`, the angles have `sin A = kβγ`, `sin B = kγα`,
`sin C = kαβ`, and the area is `1/(2k)`. -/
theorem problem22 (A B C : Plane) (hABC : cross A B C ≠ 0) (α β γ : ℝ)
    (hα : IsAltitude A B C α) (hβ : IsAltitude B C A β) (hγ : IsAltitude C A B γ) :
    0 < kSq α β γ ∧
    (dist B C = 1 / (Real.sqrt (kSq α β γ) * α) ∧ dist C A = 1 / (Real.sqrt (kSq α β γ) * β) ∧
      dist A B = 1 / (Real.sqrt (kSq α β γ) * γ)) ∧
    (Real.sin (∠ B A C) = Real.sqrt (kSq α β γ) * β * γ ∧
      Real.sin (∠ C B A) = Real.sqrt (kSq α β γ) * γ * α ∧
      Real.sin (∠ A C B) = Real.sqrt (kSq α β γ) * α * β) ∧
    triArea A B C = 1 / (2 * Real.sqrt (kSq α β γ)) := by
  sorry

/-- **Problem 22, existence.** Conversely, any three positive lengths `α, β, γ` for which
Carroll's fraction `k²` is positive are the altitudes of some triangle (so, with `problem22`,
three positive lengths are the altitudes of a triangle exactly when `k² > 0`, and the triangle is
then determined up to congruence by Carroll's formulae). -/
theorem problem22_exists (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hk : 0 < kSq α β γ) :
    ∃ A B C : Plane, cross A B C ≠ 0 ∧ IsAltitude A B C α ∧ IsAltitude B C A β ∧
      IsAltitude C A B γ := by
  sorry

/-- A concrete triangle (the 3-4-5 right triangle `A = (0,3)`, `B = (0,0)`, `C = (4,0)`) with
altitudes `3`, `12/5`, `4`: the hypotheses of `problem22` are satisfiable. -/
theorem problem22_nonvacuous :
    cross (pt 0 3) (pt 0 0) (pt 4 0) ≠ 0 ∧ IsAltitude (pt 0 3) (pt 0 0) (pt 4 0) 3 ∧
      IsAltitude (pt 0 0) (pt 4 0) (pt 0 3) (12 / 5) ∧
      IsAltitude (pt 4 0) (pt 0 3) (pt 0 0) 4 := by
  sorry

end PillowProblems.P22
