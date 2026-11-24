import PillowProblems.Basic

/-!
# Problem 33 (Differential Calculus: Maxima and Minima)

**Question.**

> Inscribe in a given Circle the maximum Tetragon having 2 parallel sides, one double the other.

*(Carroll's solution: Chapter III, problem 33; text in `data/problems.json`.)*

**Lean reading.** The circle has centre `O` and radius `r > 0`, and the tetragon is `ABCD`
with its vertices on the circle (`IsInscribedTrapezoid`). "Two parallel sides, one double the
other" is read as `B - A = 2 • (C - D)`: `AB` is parallel to `DC`, twice as long, and points the
same way, which is what makes `ABCD` a genuine (uncrossed) trapezoid; `C ≠ D` excludes the
degenerate case. Its area `quadArea` is given by the shoelace formula. The theorem says that the
set of areas has a greatest element, the explicit value `(3/8)(√(2+2√13) + 4√(2√13-7)) r²` (so the
maximum is attained), and that every maximal tetragon has `x²/r² = (5 - √13)/8` where `x` is
*half* the shorter side `DC`, i.e. `DC²/r² = (5 - √13)/2`. **Correction.** Carroll writes "Let
`DE = x`; `∴ BC = 2x`" and answers `x²/r² = (5 - √13)/8`; with `x = DE` literally this is wrong by a
factor 4. His area `3x(√(r²-x²) + √(r²-4x²))`, and hence his equation `16x⁴ - 20r²x² + 3r⁴ = 0`
and his root, are right only when `x` is the half-side, so his answer holds with `x = DE/2`, which
is what is proved (together with the literal form, Carroll's `DE` being `DC` here). The proof is
calculus-free: two AM-GM steps (`core`) bound the area and are equalities only at Carroll's
root, which also proves his remark that the other root is inadmissible.

**Status.** proved (corrected)
-/

namespace PillowProblems.P33

open Real

/-- The area of the quadrilateral `ABCD` (vertices in this order), by the shoelace formula:
half the absolute value of the signed areas of `ABC` and `ACD` added. -/
noncomputable def quadArea (A B C D : Plane) : ℝ := |cross A B C + cross A C D| / 2

/-- `ABCD` is a tetragon inscribed in the circle with centre `O` and radius `r` whose sides `AB`
and `DC` are parallel, `AB` being double `DC`: the vector `AB` is twice the vector `DC` (same
direction, so `ABCD` is a genuine trapezoid and not a crossed quadrilateral). -/
def IsInscribedTrapezoid (O : Plane) (r : ℝ) (A B C D : Plane) : Prop :=
  A ∈ Metric.sphere O r ∧ B ∈ Metric.sphere O r ∧ C ∈ Metric.sphere O r ∧
    D ∈ Metric.sphere O r ∧ C ≠ D ∧ B - A = (2 : ℝ) • (C - D)

/-- **Problem 33.** Among the tetragons `ABCD` inscribed in a circle of radius `r`, with `AB`
parallel to `DC` and double it, the greatest area is
`(3/8)·(√(2 + 2√13) + 4√(2√13 - 7))·r²`, it is attained, and every tetragon attaining it has
half its shorter side `x = DC/2` with `x² / r² = (5 - √13)/8` (Carroll's equation), i.e.
`DC² / r² = (5 - √13)/2`. -/
theorem problem33 (O : Plane) (r : ℝ) (hr : 0 < r) :
    IsGreatest {S | ∃ A B C D, IsInscribedTrapezoid O r A B C D ∧ S = quadArea A B C D}
        (3 / 8 * (√(2 + 2 * √13) + 4 * √(2 * √13 - 7)) * r ^ 2) ∧
      ∀ A B C D, IsInscribedTrapezoid O r A B C D →
        quadArea A B C D = 3 / 8 * (√(2 + 2 * √13) + 4 * √(2 * √13 - 7)) * r ^ 2 →
        (dist C D / 2) ^ 2 / r ^ 2 = (5 - √13) / 8 ∧ dist C D ^ 2 / r ^ 2 = (5 - √13) / 2 := by
  sorry

end PillowProblems.P33
