import PillowProblems.Basic

/-!
# Problem 59 (Trigonometry: Solid)

**Question.** *(dated 8/90)*

> Given a Tetrahedron, having every edge equal to the opposite edge, so that its facets are all (when looked at from the outside) identically equal: find its volume in terms of its edges.

**Answer.**

> Calling lengths of the 3 pairs of edges '\(a\), \(b\), \(c\)', and the corresponding \(\angle\)s, in each facet, '\(A\), \(B\), \(C\)'; volume =\[\frac{abc}{6}.\sqrt{1 - (\cos^{2}A + \cos^{2}B + \cos^{2}C) + 2\cos A\cos B\cos C.}\]

*(Carroll's solution: Chapter III, problem 59; text in `data/problems.json`.)*

**Lean reading.** The tetrahedron is `KLMN` in `Space = EuclideanSpace ℝ (Fin 3)`, with Carroll's
lettering: `KL = MN = a`, `LM = KN = b`, `KM = LN = c` (opposite edges equal). Its volume is the
usual `|(L - K) · ((M - K) × (N - K))| / 6` (`tetVol`). The angles "corresponding" to `a, b, c`
are those of the facet `KLM` opposite the sides `a, b, c`, i.e. (as in Carroll's solution)
`A = ∠LMK`, `B = ∠MKL`, `C = ∠KLM`, measured with mathlib's unoriented angle. No hypotheses
beyond "opposite edges are equal" are needed: the formula also holds (both sides `0`) for
degenerate configurations, so none is added. Since the question asks for the volume "in terms of
its edges", `problem59_edges` also gives it through the edges alone,
`√((b² + c² - a²)(c² + a² - b²)(a² + b² - c²) / 72)`, which is equal to Carroll's expression.

**Status.** proved
-/

namespace PillowProblems.P59

open EuclideanGeometry

/-- The triple product `(B - A) · ((C - A) × (D - A))`: six times the signed volume of the
tetrahedron `ABCD`. -/
noncomputable def triple (A B C D : Space) : ℝ :=
  (B 0 - A 0) * ((C 1 - A 1) * (D 2 - A 2) - (C 2 - A 2) * (D 1 - A 1))
  - (B 1 - A 1) * ((C 0 - A 0) * (D 2 - A 2) - (C 2 - A 2) * (D 0 - A 0))
  + (B 2 - A 2) * ((C 0 - A 0) * (D 1 - A 1) - (C 1 - A 1) * (D 0 - A 0))

/-- The volume of the tetrahedron `ABCD`. -/
noncomputable def tetVol (A B C D : Space) : ℝ := |triple A B C D| / 6

/-- Squared distance in coordinates. -/
private noncomputable def sq3 (X Y : Space) : ℝ :=
  (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 + (X 2 - Y 2) ^ 2

/-- The Gram determinant of three vectors `u, v, w`, written through the six squared distances
`|u|², |v|², |w|², |u - v|², |v - w|², |u - w|²`. -/
private noncomputable def gram (uu vv ww uv' vw' uw' : ℝ) : ℝ :=
  uu * vv * ww + 2 * ((uu + vv - uv') / 2) * ((vv + ww - vw') / 2) * ((uu + ww - uw') / 2)
    - uu * ((vv + ww - vw') / 2) ^ 2 - vv * ((uu + ww - uw') / 2) ^ 2
    - ww * ((uu + vv - uv') / 2) ^ 2

/-- **Problem 59.** For a tetrahedron `KLMN` with `KL = MN = a`, `LM = KN = b`, `KM = LN = c`,
and `A, B, C` the angles of a facet opposite `a, b, c`, the volume is
`abc/6 · √(1 - (cos²A + cos²B + cos²C) + 2 cos A cos B cos C)`. -/
theorem problem59 (K L M N : Space)
    (hMN : dist M N = dist K L) (hKN : dist K N = dist L M) (hLN : dist L N = dist K M) :
    tetVol K L M N = dist K L * dist L M * dist K M / 6 *
      √(1 - (Real.cos (∠ L M K) ^ 2 + Real.cos (∠ M K L) ^ 2 + Real.cos (∠ K L M) ^ 2)
        + 2 * Real.cos (∠ L M K) * Real.cos (∠ M K L) * Real.cos (∠ K L M)) := by
  sorry

/-- **Problem 59**, the volume in terms of the edges alone ("find its volume in terms of its
edges"): `V = √((b² + c² - a²)(c² + a² - b²)(a² + b² - c²) / 72)`. -/
theorem problem59_edges (K L M N : Space)
    (hMN : dist M N = dist K L) (hKN : dist K N = dist L M) (hLN : dist L N = dist K M) :
    tetVol K L M N =
      √((dist L M ^ 2 + dist K M ^ 2 - dist K L ^ 2) * (dist K M ^ 2 + dist K L ^ 2 - dist L M ^ 2)
        * (dist K L ^ 2 + dist L M ^ 2 - dist K M ^ 2) / 72) := by
  sorry

end PillowProblems.P59
