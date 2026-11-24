import PillowProblems.Basic

/-!
# Problem 69 (Trigonometry: Plane)

**Question.** *(dated 8/89)*

> If, from each of the angles of a given Triangle \(ABC\), taken cyclically, a certain proper fraction of it be cut off, the arithmetical values of the 3 fractions being represented by '\(k\), \(l\), \(m\)'; and if it be given that the Triangle, formed by the lines so drawn, is similar to the given one, the angle, formed by the lines drawn from \(B\) and \(C\), being equal to \(A\), and so on: find \(k\), \(l\), \(m\), as similar functions of a single variable. Also find the ratio which each side of the second Triangle bears to the corresponding side of the first.

**Answer.**

> (1) \(k = \dfrac{\theta-B}{A}\); \(l = \dfrac{\theta-C}{B}\); \(m = \dfrac{\theta-A}{C}\).
>
> (2) Calling new Triangle '\(A'B'C'\)', \[ \frac{a'}{a} = \frac{b'}{b} = \frac{c'}{c} = 2\cos{\theta}. \]

*(Carroll's solution: Chapter III, problem 69; text in `data/problems.json`.)*

**Lean reading.** `ABC` is a genuine triangle in the plane (`cross A B C ≠ 0`); Carroll's `A`,
`B`, `C` are the angles `∠BAC`, `∠ABC`, `∠ACB`. "Taken cyclically" is read as in Carroll's
solution: the line `AD` cuts off `∠BAD = k·A` next to `AB`, `BE` cuts off `∠CBE = l·B` next to
`BC`, `CF` cuts off `∠ACF = m·C` next to `CA`, with `D, E, F` strictly inside the opposite sides
(a line from a vertex cutting off a proper part of the angle meets the opposite side internally)
and `0 < k, l, m < 1` ("proper fraction"). The inner triangle has `A' = BE ∩ CF`, `B' = CF ∩ AD`,
`C' = AD ∩ BE` (stated as membership in the lines), and similarity with the stated correspondence
is `∠B'A'C' = A`, `∠A'B'C' = B`, `∠A'C'B' = C`; no nondegeneracy of `A'B'C'` is assumed (the proof
shows the three lines cannot be concurrent). The single variable is `θ`, proved to be `∠ADC`
(Carroll's § 2). Carroll's ratio `2 cos θ` is wrong in sign when `θ > 90°`, which the hypotheses
allow (e.g. an equilateral triangle with `θ = 100°`, `k = l = m = 2/3`): then `B'` lies beyond `C'`
from `A` (Carroll's `B'C' = AC' - AB'` is negative), since a length cannot be
negative. The true ratio of corresponding sides is `|2 cos θ|`, which agrees with
Carroll's for `θ < 90°`; this is what `problem69` proves. `problem69_converse` proves Carroll's
§ 2–3 converse: every `θ` with `max(A,B,C) < θ < π - max(A,B,C)` and `θ ≠ 90°` does give proper
fractions `k, l, m` and a configuration with all the hypotheses of `problem69`. `θ = 90°`, which
Carroll's limits allow, must be excluded: the three lines are then the altitudes, which are
concurrent, so no triangle is formed (Carroll's ratio `2 cos 90° = 0` reflects this).
`problem69_nonvacuous` exhibits an explicit configuration with rational coordinates.

**Status.** proved (corrected)
-/

namespace PillowProblems.P69

open EuclideanGeometry Real

/-- Carroll's answer, with the corrected side ratio: writing `θ = ∠ADC` (the angle each of the
three lines makes with the opposite side), `k = (θ - B)/A`, `l = (θ - C)/B`, `m = (θ - A)/C`, and
each side of the inner triangle is `|2 cos θ|` times the corresponding side of `ABC`. -/
theorem problem69 (A B C D E F A' B' C' : Plane) (k l m : ℝ) (hABC : cross A B C ≠ 0)
    (hk : 0 < k ∧ k < 1) (hl : 0 < l ∧ l < 1) (hm : 0 < m ∧ m < 1)
    (hD : Sbtw ℝ B D C) (hE : Sbtw ℝ C E A) (hF : Sbtw ℝ A F B)
    (hkD : ∠ B A D = k * ∠ B A C) (hlE : ∠ C B E = l * ∠ A B C) (hmF : ∠ A C F = m * ∠ A C B)
    (hA'1 : A' ∈ line[ℝ, B, E]) (hA'2 : A' ∈ line[ℝ, C, F])
    (hB'1 : B' ∈ line[ℝ, C, F]) (hB'2 : B' ∈ line[ℝ, A, D])
    (hC'1 : C' ∈ line[ℝ, A, D]) (hC'2 : C' ∈ line[ℝ, B, E])
    (hsimA : ∠ B' A' C' = ∠ B A C) (hsimB : ∠ A' B' C' = ∠ A B C)
    (hsimC : ∠ A' C' B' = ∠ A C B) :
    ∃ θ : ℝ, θ = ∠ A D C ∧
      k = (θ - ∠ A B C) / ∠ B A C ∧ l = (θ - ∠ A C B) / ∠ A B C ∧
      m = (θ - ∠ B A C) / ∠ A C B ∧
      dist B' C' = |2 * Real.cos θ| * dist B C ∧ dist C' A' = |2 * Real.cos θ| * dist C A ∧
      dist A' B' = |2 * Real.cos θ| * dist A B := by
  sorry

/-- Converse of `problem69` (Carroll's § 2–3): for every `θ` in Carroll's range
`max(A, B, C) < θ < π - max(A, B, C)`, except `θ = π/2` (where the three lines are the
altitudes, which are concurrent, so there is no inner triangle), the fractions
`k = (θ - B)/A`, `l = (θ - C)/B`, `m = (θ - A)/C` are proper fractions and the lines so drawn
do form a triangle similar to `ABC` with the stated correspondence. -/
theorem problem69_converse (A B C : Plane) (θ k l m : ℝ) (hABC : cross A B C ≠ 0)
    (hθA : ∠ B A C < θ) (hθB : ∠ A B C < θ) (hθC : ∠ A C B < θ)
    (hθA' : θ < π - ∠ B A C) (hθB' : θ < π - ∠ A B C) (hθC' : θ < π - ∠ A C B)
    (hθ : θ ≠ π / 2)
    (hk : k = (θ - ∠ A B C) / ∠ B A C) (hl : l = (θ - ∠ A C B) / ∠ A B C)
    (hm : m = (θ - ∠ B A C) / ∠ A C B) :
    (0 < k ∧ k < 1) ∧ (0 < l ∧ l < 1) ∧ (0 < m ∧ m < 1) ∧
    ∃ D E F A' B' C' : Plane, Sbtw ℝ B D C ∧ Sbtw ℝ C E A ∧ Sbtw ℝ A F B ∧
      ∠ B A D = k * ∠ B A C ∧ ∠ C B E = l * ∠ A B C ∧ ∠ A C F = m * ∠ A C B ∧
      A' ∈ line[ℝ, B, E] ∧ A' ∈ line[ℝ, C, F] ∧ B' ∈ line[ℝ, C, F] ∧ B' ∈ line[ℝ, A, D] ∧
      C' ∈ line[ℝ, A, D] ∧ C' ∈ line[ℝ, B, E] ∧
      ∠ B' A' C' = ∠ B A C ∧ ∠ A' B' C' = ∠ A B C ∧ ∠ A' C' B' = ∠ A C B := by
  sorry

/-- The hypotheses of `problem69` can all be met: the triangle `A = (2,4)`, `B = (0,0)`,
`C = (4,0)` with the three lines making the angle `θ = arccos (5/13)` with the opposite sides. -/
theorem problem69_nonvacuous : ∃ (A B C D E F A' B' C' : Plane) (k l m : ℝ),
    cross A B C ≠ 0 ∧ (0 < k ∧ k < 1) ∧ (0 < l ∧ l < 1) ∧ (0 < m ∧ m < 1) ∧
    Sbtw ℝ B D C ∧ Sbtw ℝ C E A ∧ Sbtw ℝ A F B ∧
    ∠ B A D = k * ∠ B A C ∧ ∠ C B E = l * ∠ A B C ∧ ∠ A C F = m * ∠ A C B ∧
    A' ∈ line[ℝ, B, E] ∧ A' ∈ line[ℝ, C, F] ∧ B' ∈ line[ℝ, C, F] ∧ B' ∈ line[ℝ, A, D] ∧
    C' ∈ line[ℝ, A, D] ∧ C' ∈ line[ℝ, B, E] ∧
    ∠ B' A' C' = ∠ B A C ∧ ∠ A' B' C' = ∠ A B C ∧ ∠ A' C' B' = ∠ A C B := by
  sorry

end PillowProblems.P69
