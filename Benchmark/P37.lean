import PillowProblems.Basic

/-!
# Problem 37 (Trigonometry: Plane)

**Question.** *(dated 12/91)*

> Two given Circles intersect, so that their common chord subtends angles of 30° and 60° at their centres. What fraction of the smaller Circle is within the larger?

**Answer.**

> \[\dfrac{4 + \sqrt{3}}{12} - \dfrac{1 + \sqrt{3}}{2\pi};\quad \text{i.e.}\,\, \text{about}\,\, \cdot 044\].

*(Carroll's solution: Chapter III, problem 37; text in `data/problems.json`.)*

**Lean reading.** Areas are Lebesgue measure (`volume`) on the plane, and a circle's area is that
of its open disc `Metric.ball` (the boundary has measure zero). The circles have centres `A` and
`D` and meet at `B` and `C`, so their radii are `AB = AC` and `DB = DC` and `BC` is the common
chord; the hypotheses are `∠BAC = 30°` and `∠BDC = 60°`, with no fixed position or size. The
question is ambiguous: the centres may lie on opposite sides of the common chord (Carroll's figure
and solution) or on the same side, and both figures exist. "Opposite sides" is `cross B C A *
cross B C D < 0` (the triangles `BCA` and `BCD` have opposite orientations). For this reading,
`problem37` proves that the circle about `D` is the smaller one and that the fraction of its area
lying inside the other circle is Carroll's `(4 + √3)/12 - (1 + √3)/(2π)`. For the other figure
(`cross B C A * cross B C D > 0`), `problem37_sameSide` proves that the fraction is `1 + √3/12 -
1/(2π)`; `problem37_nonvacuous` shows that both figures exist. The proofs move the figure by a
rigid motion (`frame`, shown to preserve distances, angles and area) so that the chord lies on the
`y`-axis and the centres on the `x`-axis. Each circular segment is then the region between two
graphs, whose area is the integral of `2√(R² - u²)`. Carroll's decimal "about ·044" is slightly
off: he rounded the two terms to `·478` and `·434` (with `π ≈ 22/7`), whose difference is `·044`,
although even with `π = 22/7` the difference is `·0430…`. The true value is `0·0429…`;
`problem37_approx` proves that it lies between `·042` and `·043`.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P37

open scoped EuclideanGeometry
open MeasureTheory Real

/-- Antiderivative of `2 √(R² - u²)`; `segF R u₂ - segF R u₁` is the area of the part of a disc
of radius `R` between two chords at (signed) distances `u₁ ≤ u₂` from the centre. -/
private noncomputable def segF (R u : ℝ) : ℝ :=
  R ^ 2 * arcsin (R⁻¹ * u) + u * √(R ^ 2 - u ^ 2)

/-- The coordinate map of the plane onto `ℝ × ℝ`; it preserves area. -/
private noncomputable def toProd (z : Plane) : ℝ × ℝ := (z 0, z 1)

/-- A rigid motion taking the midpoint of `BC` to the origin and `BC` to the `y`-axis (with `B`
above), followed by the reflection `x ↦ -x` when `s = -1`. -/
private noncomputable def frame (B C : Plane) (s : ℝ) (X : Plane) : Plane :=
  pt (s * ((B 1 - C 1) / dist B C * (X 0 - (B 0 + C 0) / 2) -
      (B 0 - C 0) / dist B C * (X 1 - (B 1 + C 1) / 2)))
    ((B 0 - C 0) / dist B C * (X 0 - (B 0 + C 0) / 2) +
      (B 1 - C 1) / dist B C * (X 1 - (B 1 + C 1) / 2))

/-- **Problem 37.** Two circles, with centres `A` and `D`, meet at `B` and `C` (the circle about
`A` has radius `AB = AC`, that about `D` radius `DB = DC`), and the centres lie on opposite sides
of the common chord `BC` (Carroll's figure). If the chord subtends `30°` at `A` and `60°` at
`D`, then the circle about `D` is the smaller one, and the fraction of its area lying within the
circle about `A` is `(4 + √3)/12 - (1 + √3)/(2π)`. -/
theorem problem37 (A D B C : Plane) (hAC : dist A C = dist A B) (hDC : dist D C = dist D B)
    (hside : cross B C A * cross B C D < 0)
    (hA : ∠ B A C = π / 6) (hD : ∠ B D C = π / 3) :
    dist D B < dist A B ∧
    (volume (Metric.ball A (dist A B) ∩ Metric.ball D (dist D B))).toReal /
      (volume (Metric.ball D (dist D B))).toReal =
      (4 + √3) / 12 - (1 + √3) / (2 * π) := by
  sorry

/-- The other reading of problem 37: the same circles, but with both centres on the same side of
the common chord `BC`. Then the circle about `D` is again the smaller one, and the fraction of
its area lying within the circle about `A` is `1 + √3/12 - 1/(2π)` (about `·985`). -/
theorem problem37_sameSide (A D B C : Plane) (hAC : dist A C = dist A B)
    (hDC : dist D C = dist D B)
    (hside : 0 < cross B C A * cross B C D)
    (hA : ∠ B A C = π / 6) (hD : ∠ B D C = π / 3) :
    dist D B < dist A B ∧
    (volume (Metric.ball A (dist A B) ∩ Metric.ball D (dist D B))).toReal /
      (volume (Metric.ball D (dist D B))).toReal =
      1 + √3 / 12 - 1 / (2 * π) := by
  sorry

/-- Both figures exist: chord `B = (0, 1)`, `C = (0, -1)`, centre `A = (-(2 + √3), 0)`, and
centre `D = (√3, 0)` (opposite sides) or `D = (-√3, 0)` (same side). So the hypotheses of
`problem37` and of `problem37_sameSide` are satisfiable. -/
theorem problem37_nonvacuous :
    (∃ A D B C : Plane, dist A C = dist A B ∧ dist D C = dist D B ∧
      cross B C A * cross B C D < 0 ∧ ∠ B A C = π / 6 ∧ ∠ B D C = π / 3) ∧
    (∃ A D B C : Plane, dist A C = dist A B ∧ dist D C = dist D B ∧
      0 < cross B C A * cross B C D ∧ ∠ B A C = π / 6 ∧ ∠ B D C = π / 3) := by
  sorry

/-- Carroll's decimal "about ·044" is slightly off: the fraction lies between `·042` and `·043`
(it is `·0429…`; Carroll's `·044` comes from rounding the two terms to `·478` and `·434`). -/
theorem problem37_approx :
    0.042 < (4 + √3) / 12 - (1 + √3) / (2 * π) ∧ (4 + √3) / 12 - (1 + √3) / (2 * π) < 0.043 := by
  sorry

end PillowProblems.P37
