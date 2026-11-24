import PillowProblems.Basic

/-!
# Problem 24 (Pure Geometry, Plane)

**Question.** *(dated 5/86)*

> If, from the vertices of a triangle \(ABC\), the lines \(AD\), \(BE\), \(CF\) be drawn, intersecting at \(O\): find the ratio \(\dfrac{DO}{DA}\) in terms of the two ratios \(\dfrac{EO}{EB}\), \(\dfrac{FO}{FC}\).
>
> [Figure: A geometric diagram of triangle ABC with three cevians meeting at interior point O, creating points D, E, F on the sides.]

**Answer.**

> \(\dfrac{DO}{DA} + \dfrac{EO}{EB} + \dfrac{FO}{FC} = 1\); whence any one can be found in terms of the other two.

*(Carroll's solution: Chapter III, problem 24; text in `data/problems.json`.)*

**Lean reading.** The triangle `ABC` is nondegenerate (`cross A B C ≠ 0`). Following Carroll's
figure, `O` is a point strictly inside the triangle, written with positive barycentric weights
`O = α A + β B + γ C`, `α + β + γ = 1`; this is needed, since for an exterior `O` the relation
holds only with signed ratios. `D`, `E`, `F` lie on the lines `BC`, `CA`, `AB` and `O` lies on each
of the lines `AD`, `BE`, `CF` (so `D`, `E`, `F` are the feet of the three cevians through `O`).
The ratios are ratios of lengths, `DO / DA = dist D O / dist D A`, etc. Carroll's answer is the
relation `DO/DA + EO/EB + FO/FC = 1`, stated together with the solved form
`DO/DA = 1 - EO/EB - FO/FC`. The proof shows, as Carroll does with areas, that the three ratios
are the barycentric weights `α`, `β`, `γ`; `problem24_nonvacuous` exhibits the centroid case.

**Status.** proved
-/

namespace PillowProblems.P24

open EuclideanGeometry

/-- **Problem 24.** For cevians `AD`, `BE`, `CF` of a triangle meeting at an interior point `O`,
`DO/DA + EO/EB + FO/FC = 1`; hence `DO/DA = 1 - EO/EB - FO/FC`. -/
theorem problem24 (A B C D E F O : Plane) (hABC : cross A B C ≠ 0)
    (hO : ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧ O = α • A + β • B + γ • C)
    (hD : D ∈ line[ℝ, B, C]) (hE : E ∈ line[ℝ, C, A]) (hF : F ∈ line[ℝ, A, B])
    (hAD : O ∈ line[ℝ, A, D]) (hBE : O ∈ line[ℝ, B, E]) (hCF : O ∈ line[ℝ, C, F]) :
    dist D O / dist D A + dist E O / dist E B + dist F O / dist F C = 1 ∧
      dist D O / dist D A = 1 - dist E O / dist E B - dist F O / dist F C := by
  sorry

/-- The hypotheses of `problem24` are satisfiable: the medians of a right isosceles triangle. -/
theorem problem24_nonvacuous :
    ∃ A B C D E F O : Plane, cross A B C ≠ 0 ∧
      (∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧ O = α • A + β • B + γ • C) ∧
      D ∈ line[ℝ, B, C] ∧ E ∈ line[ℝ, C, A] ∧ F ∈ line[ℝ, A, B] ∧
      O ∈ line[ℝ, A, D] ∧ O ∈ line[ℝ, B, E] ∧ O ∈ line[ℝ, C, F] := by
  sorry

end PillowProblems.P24
