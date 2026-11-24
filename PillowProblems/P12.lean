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

private lemma dist_sq' (P Q : Plane) : dist P Q ^ 2 = (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
    Real.dist_eq, sq_abs, sq_abs]

/-- Heron's formula, in the squared form Carroll uses: `16 m² = (a+b+c)(-a+b+c)(a-b+c)(a+b-c)`. -/
theorem problem12_heron (A B C : Plane) :
    16 * triArea A B C ^ 2 = (dist B C + dist C A + dist A B) * (-dist B C + dist C A + dist A B) *
      (dist B C - dist C A + dist A B) * (dist B C + dist C A - dist A B) := by
  have ha := dist_sq' B C
  have hb := dist_sq' C A
  have hc := dist_sq' A B
  have hm : triArea A B C ^ 2 = cross A B C ^ 2 / 4 := by
    unfold triArea; rw [div_pow, sq_abs]; norm_num
  have e : (dist B C + dist C A + dist A B) * (-dist B C + dist C A + dist A B) *
      (dist B C - dist C A + dist A B) * (dist B C + dist C A - dist A B) =
      2 * (dist B C ^ 2 * dist C A ^ 2 + dist C A ^ 2 * dist A B ^ 2 + dist A B ^ 2 * dist B C ^ 2)
        - (dist B C ^ 2) ^ 2 - (dist C A ^ 2) ^ 2 - (dist A B ^ 2) ^ 2 := by ring
  rw [e, ha, hb, hc, hm]
  unfold cross
  ring

/-- Given the semi-perimeter `s`, the area `m` and the volume `v = abc` of the cuboid on the
sides, the sum of the squares of the sides is `2 (s² - v/s - m²/s²)`. -/
theorem problem12 (A B C : Plane) :
    dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2 =
      2 * (((dist B C + dist C A + dist A B) / 2) ^ 2
        - dist B C * dist C A * dist A B / ((dist B C + dist C A + dist A B) / 2)
        - triArea A B C ^ 2 / ((dist B C + dist C A + dist A B) / 2) ^ 2) := by
  have ha := dist_nonneg (x := B) (y := C)
  have hb := dist_nonneg (x := C) (y := A)
  have hc := dist_nonneg (x := A) (y := B)
  have hH := problem12_heron A B C
  have hm : triArea A B C ^ 2 = (dist B C + dist C A + dist A B) * (-dist B C + dist C A + dist A B) *
      (dist B C - dist C A + dist A B) * (dist B C + dist C A - dist A B) / 16 := by
    linarith
  rcases (add_nonneg (add_nonneg ha hb) hc).lt_or_eq with hs | hs
  · rw [hm]
    field_simp
    ring
  · -- degenerate case `A = B = C`: every term vanishes
    have h1 : dist B C = 0 := by linarith
    have h2 : dist C A = 0 := by linarith
    have h3 : dist A B = 0 := by linarith
    rw [hm, h1, h2, h3]
    norm_num

end PillowProblems.P12
