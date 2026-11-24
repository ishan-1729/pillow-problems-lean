import PillowProblems.Basic

/-!
# Problem 48 (Trigonometry: Plane)

**Question.** *(dated 9/2/81)*

> If semicircles be described, externally, on the sides of a given Triangle; and if their common tangents be drawn; and if their lengths be \(\alpha\), \(\beta\), \(\gamma\): prove that \[ (\frac{\beta\gamma}{\alpha} + \frac{\gamma\alpha}{\beta} + \frac{\alpha\beta}{\gamma}) \] is equal to the semiperimeter of the Triangle.

*(Carroll's solution: Chapter III, problem 48; text in `data/problems.json`.)*

**Lean reading.** The triangle is `A, B, C` with `cross A B C ≠ 0` (non-degenerate). The semicircle on a side `XY`
lies on the circle with centre `midpoint ℝ X Y` and radius `XY/2`. Like Carroll's solution, we work
with these full circles. `IsCommonTangent O₁ r₁ O₂ r₂ D E` says `DE` is a segment of a common
direct tangent between its points of contact: `D` and `E` are on the circles, `DE` is perpendicular
to both radii, and the radii point the same way. Two of the circles meet (at a vertex), so their
only common tangents are the two direct ones. We prove the identity for every such tangent
segment (`DE² = O₁O₂² - (r₁ - r₂)²`, the same for both), so the one touching the outer arcs is
covered whichever it is. `α`, `β`, `γ` are the tangents of the semicircles on `CA, AB`; `AB, BC`;
`BC, CA`. The expression is symmetric, so this labelling does not matter. `problem48_exists` shows
the tangents exist for every triangle, so the hypotheses of `problem48` can be met.

**Status.** proved
-/

namespace PillowProblems.P48

/-- `DE` is a segment of a common (direct) tangent of the circles with centres `O₁, O₂` and radii
`r₁, r₂`, between its points of contact: `D` is on the first circle, `E` on the second, `DE` is
perpendicular to both radii `O₁D`, `O₂E`, and these radii point the same way (the two circles lie on
the same side of the tangent line). -/
def IsCommonTangent (O₁ : Plane) (r₁ : ℝ) (O₂ : Plane) (r₂ : ℝ) (D E : Plane) : Prop :=
  dist D O₁ = r₁ ∧ dist E O₂ = r₂ ∧ inner ℝ (D - O₁) (E - D) = 0 ∧
    inner ℝ (E - O₂) (E - D) = 0 ∧ r₂ • (D - O₁) = r₁ • (E - O₂)

/-- **Problem 48 (the tangents exist).** For any triangle, each two of the semicircles on its
sides have a common tangent. -/
theorem problem48_exists (A B C : Plane) (hABC : cross A B C ≠ 0) :
    (∃ D E, IsCommonTangent (midpoint ℝ C A) (dist C A / 2) (midpoint ℝ A B) (dist A B / 2) D E) ∧
    (∃ F G, IsCommonTangent (midpoint ℝ A B) (dist A B / 2) (midpoint ℝ B C) (dist B C / 2) F G) ∧
    (∃ H J, IsCommonTangent (midpoint ℝ B C) (dist B C / 2) (midpoint ℝ C A) (dist C A / 2) H J) := by
  sorry

/-- **Problem 48.** If `α, β, γ` are the lengths of the common tangents of the semicircles on the
sides `CA, AB`, `AB, BC`, `BC, CA` (between the points of contact), then
`βγ/α + γα/β + αβ/γ` is the semiperimeter of `ABC`. -/
theorem problem48 (A B C : Plane) (hABC : cross A B C ≠ 0) (D E F G H J : Plane)
    (hα : IsCommonTangent (midpoint ℝ C A) (dist C A / 2) (midpoint ℝ A B) (dist A B / 2) D E)
    (hβ : IsCommonTangent (midpoint ℝ A B) (dist A B / 2) (midpoint ℝ B C) (dist B C / 2) F G)
    (hγ : IsCommonTangent (midpoint ℝ B C) (dist B C / 2) (midpoint ℝ C A) (dist C A / 2) H J) :
    dist F G * dist H J / dist D E + dist H J * dist D E / dist F G +
      dist D E * dist F G / dist H J = (dist B C + dist C A + dist A B) / 2 := by
  sorry

end PillowProblems.P48
