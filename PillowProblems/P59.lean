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

private lemma dist_sq_eq (X Y : Space) : dist X Y ^ 2 = sq3 X Y := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [sq3, Real.dist_eq, sq_abs]

/-- The Gram determinant of three vectors `u, v, w`, written through the six squared distances
`|u|², |v|², |w|², |u - v|², |v - w|², |u - w|²`. -/
private noncomputable def gram (uu vv ww uv' vw' uw' : ℝ) : ℝ :=
  uu * vv * ww + 2 * ((uu + vv - uv') / 2) * ((vv + ww - vw') / 2) * ((uu + ww - uw') / 2)
    - uu * ((vv + ww - vw') / 2) ^ 2 - vv * ((uu + ww - uw') / 2) ^ 2
    - ww * ((uu + vv - uv') / 2) ^ 2

private lemma triple_sq (X Y Z W : Space) :
    triple X Y Z W ^ 2 =
      gram (sq3 X Y) (sq3 X Z) (sq3 X W) (sq3 Y Z) (sq3 Z W) (sq3 Y W) := by
  simp only [triple, gram, sq3]
  ring

/-- **Problem 59.** For a tetrahedron `KLMN` with `KL = MN = a`, `LM = KN = b`, `KM = LN = c`,
and `A, B, C` the angles of a facet opposite `a, b, c`, the volume is
`abc/6 · √(1 - (cos²A + cos²B + cos²C) + 2 cos A cos B cos C)`. -/
theorem problem59 (K L M N : Space)
    (hMN : dist M N = dist K L) (hKN : dist K N = dist L M) (hLN : dist L N = dist K M) :
    tetVol K L M N = dist K L * dist L M * dist K M / 6 *
      √(1 - (Real.cos (∠ L M K) ^ 2 + Real.cos (∠ M K L) ^ 2 + Real.cos (∠ K L M) ^ 2)
        + 2 * Real.cos (∠ L M K) * Real.cos (∠ M K L) * Real.cos (∠ K L M)) := by
  -- the law of cosines in the facet `KLM`
  have lA := law_cos L M K
  have lB := law_cos M K L
  have lC := law_cos K L M
  rw [dist_comm L K] at lA
  rw [dist_comm M L, dist_comm M K, dist_comm L K] at lB
  rw [dist_comm M L] at lC
  have e : ∀ {X Y : Space} {r : ℝ}, dist X Y = r → sq3 X Y = r ^ 2 := by
    intro X Y r h; rw [← dist_sq_eq, h]
  have key : triple K L M N ^ 2 = (dist K L * dist L M * dist K M) ^ 2 *
      (1 - (Real.cos (∠ L M K) ^ 2 + Real.cos (∠ M K L) ^ 2 + Real.cos (∠ K L M) ^ 2)
        + 2 * Real.cos (∠ L M K) * Real.cos (∠ M K L) * Real.cos (∠ K L M)) := by
    rw [triple_sq, e (r := dist K L) rfl, e (r := dist K M) rfl, e hKN,
      e (r := dist L M) rfl, e hMN, e hLN]
    generalize dist K L = a at lA lB lC ⊢
    generalize dist L M = b at lA lB lC ⊢
    generalize dist K M = c at lA lB lC ⊢
    generalize Real.cos (∠ L M K) = cA at lA lB lC ⊢
    generalize Real.cos (∠ M K L) = cB at lA lB lC ⊢
    generalize Real.cos (∠ K L M) = cC at lA lB lC ⊢
    simp only [gram]
    linear_combination
      (1 / 2) * (a ^ 2 * (b * c * cA + (b ^ 2 + c ^ 2 - a ^ 2) / 2)
          - 2 * (c * a * cB) * (a * b * cC)) * lA
      + (1 / 2) * (b ^ 2 * (c * a * cB + (c ^ 2 + a ^ 2 - b ^ 2) / 2)
          - (b ^ 2 + c ^ 2 - a ^ 2) * (a * b * cC)) * lB
      + (1 / 2) * (c ^ 2 * (a * b * cC + (a ^ 2 + b ^ 2 - c ^ 2) / 2)
          - (b ^ 2 + c ^ 2 - a ^ 2) * (c ^ 2 + a ^ 2 - b ^ 2) / 2) * lC
  rw [tetVol, ← Real.sqrt_sq_eq_abs, key, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (by positivity)]
  ring

/-- **Problem 59**, the volume in terms of the edges alone ("find its volume in terms of its
edges"): `V = √((b² + c² - a²)(c² + a² - b²)(a² + b² - c²) / 72)`. -/
theorem problem59_edges (K L M N : Space)
    (hMN : dist M N = dist K L) (hKN : dist K N = dist L M) (hLN : dist L N = dist K M) :
    tetVol K L M N =
      √((dist L M ^ 2 + dist K M ^ 2 - dist K L ^ 2) * (dist K M ^ 2 + dist K L ^ 2 - dist L M ^ 2)
        * (dist K L ^ 2 + dist L M ^ 2 - dist K M ^ 2) / 72) := by
  have e : ∀ {X Y : Space} {r : ℝ}, dist X Y = r → sq3 X Y = r ^ 2 := by
    intro X Y r h; rw [← dist_sq_eq, h]
  have key : triple K L M N ^ 2 =
      (dist L M ^ 2 + dist K M ^ 2 - dist K L ^ 2) * (dist K M ^ 2 + dist K L ^ 2 - dist L M ^ 2)
        * (dist K L ^ 2 + dist L M ^ 2 - dist K M ^ 2) / 72 * 6 ^ 2 := by
    rw [triple_sq, e (r := dist K L) rfl, e (r := dist K M) rfl, e hKN,
      e (r := dist L M) rfl, e hMN, e hLN]
    simp only [gram]
    ring
  rw [tetVol, ← Real.sqrt_sq_eq_abs, key, Real.sqrt_mul' _ (sq_nonneg _),
    Real.sqrt_sq (by norm_num)]
  ring

end PillowProblems.P59
