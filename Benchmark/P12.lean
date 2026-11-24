import PillowProblems.Basic

/-!
# Problem 12 (Trigonometry: Plane)

**Question.** *(dated 23/1/91)*

> Given the semi-perimeter and the area of a Triangle, and also the volume of the cuboid whose edges are equal to the sides of the Triangle: find the sum of the squares of its sides.

**Answer.**

> If \(s\) = semi-perimeter, \(m\) = area, \(v\) = volume; then \[ a^{2} + b^{2} + c^{2} = 2.(s^{2} - \frac{v}{s} - \frac{m^{2}}{s^{2}}). \]

*(Carroll's solution: Chapter III, problem 12; text in `data/problems.json`.)*

**Lean reading.** The Triangle is three points `A B C` of the `Plane`, with sides
`a = BC`, `b = CA`, `c = AB`; the semi-perimeter is `s = (a + b + c) / 2`, the area is
`m = triArea A B C`, and the cuboid with edges `a, b, c` has volume `v = a * b * c`. The answer
"find the sum of the squares of its sides" is read as the identity
`a² + b² + c² = 2 (s² - v / s - m² / s²)`, which expresses the sum through the three given data.
No hypothesis is needed: for a genuine triangle `s > 0` (Carroll divides by `s`), and the
identity is proved even for degenerate (collinear) triangles, including the totally degenerate
`A = B = C` where `s = 0` and Lean's `x / 0 = 0` makes both sides `0`. The area is
the geometric `triArea`, not Heron's formula: Heron's formula `16 m² = (a+b+c)(-a+b+c)(a-b+c)(a+b-c)`,
which Carroll quotes, is proved along the way (`problem12_heron`).

**Status.** proved
-/

namespace PillowProblems.P12

/-- Heron's formula, in the squared form Carroll uses: `16 m² = (a+b+c)(-a+b+c)(a-b+c)(a+b-c)`. -/
theorem problem12_heron (A B C : Plane) :
    16 * triArea A B C ^ 2 = (dist B C + dist C A + dist A B) * (-dist B C + dist C A + dist A B) *
      (dist B C - dist C A + dist A B) * (dist B C + dist C A - dist A B) := by
  sorry

/-- Given the semi-perimeter `s`, the area `m` and the volume `v = abc` of the cuboid on the
sides, the sum of the squares of the sides is `2 (s² - v/s - m²/s²)`. -/
theorem problem12 (A B C : Plane) :
    dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2 =
      2 * (((dist B C + dist C A + dist A B) / 2) ^ 2
        - dist B C * dist C A * dist A B / ((dist B C + dist C A + dist A B) / 2)
        - triArea A B C ^ 2 / ((dist B C + dist C A + dist A B) / 2) ^ 2) := by
  sorry

end PillowProblems.P12
