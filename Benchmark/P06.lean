import PillowProblems.Basic

/-!
# Problem 6 (Trigonometry: Plane)

**Question.**

> Given lengths of lines drawn, from vertices of Triangle, to middle points of opposite sides, to find its sides and angles.

**Answer.**

> Calling the sides '\(2a\)', '\(2b\)', '\(2c\)' and the lines '\(\alpha\)', '\(\beta\)', '\(\gamma\)', we have
>
> \(\quad\quad a^{2}=\dfrac{-\alpha^{2}+2\beta^{2}+2\gamma^{2}}{9},\)
>
> \(\quad \cos A= \dfrac{5\alpha^{2}-\beta^{2}-\gamma^{2}}{2\sqrt{2\alpha^{2}-\beta^{2}+2\gamma^{2}}.{\sqrt{2\alpha^{2}+2\beta^{2}-\gamma^{2}}}}\).

*(Carroll's solution: Chapter III, problem 6; text in `data/problems.json`.)*

**Lean reading.** The Triangle is three points `A B C` of the `Plane`; Carroll's sides are
`2a = BC`, `2b = CA`, `2c = AB`, and his lines are the medians `α = A M_A`, `β = B M_B`,
`γ = C M_C`, where `M_A = midpoint ℝ B C` etc. "Find its sides and angles" is read as: the sides
and the cosines of the angles are given by Carroll's formulas in `α, β, γ`. `problem6_sides`
gives `a² = (-α² + 2β² + 2γ²)/9` and its two cyclic companions, and the side lengths
`BC = ⅔ √(-α² + 2β² + 2γ²)` etc. (so the sides, hence the triangle up to congruence, are
determined by the medians). `problem6` gives Carroll's formula for `cos A` and, as he says
("and so for other angles"), the cyclic formulas for `cos B` and `cos C`. The cosine formulas
need the vertices pairwise distinct (otherwise the angle is the junk value `π/2` and the
denominators vanish); no other hypothesis is needed, and the formulas hold even for collinear
triangles.

**Status.** proved
-/

namespace PillowProblems.P06

open EuclideanGeometry

/-- The sides from the medians: with sides `2a = BC, 2b = CA, 2c = AB` and medians
`α, β, γ` from `A, B, C`, `a² = (-α² + 2β² + 2γ²)/9` (and cyclically), so
`BC = ⅔ √(-α² + 2β² + 2γ²)` (and cyclically). -/
theorem problem6_sides (A B C : Plane) :
    (dist B C / 2) ^ 2 = (-dist A (midpoint ℝ B C) ^ 2 + 2 * dist B (midpoint ℝ C A) ^ 2
        + 2 * dist C (midpoint ℝ A B) ^ 2) / 9 ∧
    (dist C A / 2) ^ 2 = (2 * dist A (midpoint ℝ B C) ^ 2 - dist B (midpoint ℝ C A) ^ 2
        + 2 * dist C (midpoint ℝ A B) ^ 2) / 9 ∧
    (dist A B / 2) ^ 2 = (2 * dist A (midpoint ℝ B C) ^ 2 + 2 * dist B (midpoint ℝ C A) ^ 2
        - dist C (midpoint ℝ A B) ^ 2) / 9 ∧
    dist B C = 2 / 3 * Real.sqrt (-dist A (midpoint ℝ B C) ^ 2 + 2 * dist B (midpoint ℝ C A) ^ 2
        + 2 * dist C (midpoint ℝ A B) ^ 2) ∧
    dist C A = 2 / 3 * Real.sqrt (2 * dist A (midpoint ℝ B C) ^ 2 - dist B (midpoint ℝ C A) ^ 2
        + 2 * dist C (midpoint ℝ A B) ^ 2) ∧
    dist A B = 2 / 3 * Real.sqrt (2 * dist A (midpoint ℝ B C) ^ 2 + 2 * dist B (midpoint ℝ C A) ^ 2
        - dist C (midpoint ℝ A B) ^ 2) := by
  sorry

/-- The angles from the medians: Carroll's formula for `cos A`, and the cyclic formulas for
`cos B` and `cos C`. -/
theorem problem6 (A B C : Plane) (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) :
    Real.cos (∠ B A C) = (5 * dist A (midpoint ℝ B C) ^ 2 - dist B (midpoint ℝ C A) ^ 2
        - dist C (midpoint ℝ A B) ^ 2) /
      (2 * Real.sqrt (2 * dist A (midpoint ℝ B C) ^ 2 - dist B (midpoint ℝ C A) ^ 2
        + 2 * dist C (midpoint ℝ A B) ^ 2) *
        Real.sqrt (2 * dist A (midpoint ℝ B C) ^ 2 + 2 * dist B (midpoint ℝ C A) ^ 2
        - dist C (midpoint ℝ A B) ^ 2)) ∧
    Real.cos (∠ C B A) = (5 * dist B (midpoint ℝ C A) ^ 2 - dist C (midpoint ℝ A B) ^ 2
        - dist A (midpoint ℝ B C) ^ 2) /
      (2 * Real.sqrt (2 * dist B (midpoint ℝ C A) ^ 2 - dist C (midpoint ℝ A B) ^ 2
        + 2 * dist A (midpoint ℝ B C) ^ 2) *
        Real.sqrt (2 * dist B (midpoint ℝ C A) ^ 2 + 2 * dist C (midpoint ℝ A B) ^ 2
        - dist A (midpoint ℝ B C) ^ 2)) ∧
    Real.cos (∠ A C B) = (5 * dist C (midpoint ℝ A B) ^ 2 - dist A (midpoint ℝ B C) ^ 2
        - dist B (midpoint ℝ C A) ^ 2) /
      (2 * Real.sqrt (2 * dist C (midpoint ℝ A B) ^ 2 - dist A (midpoint ℝ B C) ^ 2
        + 2 * dist B (midpoint ℝ C A) ^ 2) *
        Real.sqrt (2 * dist C (midpoint ℝ A B) ^ 2 + 2 * dist A (midpoint ℝ B C) ^ 2
        - dist B (midpoint ℝ C A) ^ 2)) := by
  sorry

end PillowProblems.P06
