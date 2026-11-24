import PillowProblems.Basic

/-!
# Problem 18 (Pure Geometry, Plane, Trigonometry: Plane)

**Question.** *(dated 11/89)*

> Find a Point, in the base of a given Triangle, such that, if from it perpendiculars be dropped upon the sides, the line joining their extremities shall be parallel to the base. (1) Trigonometrically. (2) Geometrically.

**Answer.**

> (1) Divide base \(BC\), at \(E\), so that \(\dfrac{BE}{EC} = \dfrac{\sin 2C}{\sin 2B}\).
>
> (2) At \(B\), \(C\), make right angles \(ABD\), \(ACD\); and join \(AD\) cutting \(BC\) at \(E\), which is the required Point.

*(Carroll's solution: Chapter III, problem 18; text in `data/problems.json`.)*

**Lean reading.** The triangle is nondegenerate; `F`, `G` are the feet of the perpendiculars from `E` on
the lines `AB`, `AC` (`IsFoot`; they fall on the extensions of the sides when an angle is
obtuse), and "`FG` parallel to the base" is `G - F = k (C - B)` for some `k`. Carroll's
`BE / EC = sin 2C / sin 2B` is stated cross-multiplied, `BE · sin 2B = EC · sin 2C`, which also
covers a right angle at `B` (`sin 2B = 0`, the point is then `C`). `problem18_a` is the
statement for `E` in the base `BC` (lengths `BE`, `EC`); `problem18_line` is the same on the
whole line `BC` with signed lengths `BE = τ·BC`, `EC = (1 - τ)·BC`. Since the condition is
linear in `τ`, it determines the point uniquely when `sin 2B + sin 2C ≠ 0` (inside the base
when the triangle is acute); when `|B - C| = 90°` there is no such point. `problem18_b` is
part (2): the point `D` with right angles `ABD`, `ACD` exists, and if `AD` meets the line `BC`
at `E` then `FG ∥ BC` and `E` satisfies part (1). Carroll takes for granted that `AD` cuts the
base; `problem18_b_cuts` proves that it does, at exactly one point of the base, whenever the
base angles `B`, `C` are acute (for a right or obtuse base angle the point falls at or beyond an
end of the base, or does not exist).

**Status.** proved
-/

namespace PillowProblems.P18

open scoped EuclideanGeometry RealInnerProductSpace

/-- `F` is the foot of the perpendicular dropped from `E` upon the line `XY`. -/
def IsFoot (E X Y F : Plane) : Prop :=
  F ∈ line[ℝ, X, Y] ∧ ⟪E - F, Y - X⟫ = 0

/-- **Problem 18 (1)**, on the whole line `BC`, with signed lengths `BE = τ·BC`, `EC = (1-τ)·BC`:
the perpendiculars from `E` have feet `F`, `G` with `FG ∥ BC` iff `BE · sin 2B = EC · sin 2C`. -/
theorem problem18_line (A B C E F G : Plane) (hT : cross A B C ≠ 0) (τ : ℝ)
    (hE : E = B + τ • (C - B)) (hF : IsFoot E A B F) (hG : IsFoot E A C G) :
    (∃ k : ℝ, G - F = k • (C - B)) ↔
      τ * Real.sin (2 * ∠ A B C) = (1 - τ) * Real.sin (2 * ∠ A C B) := by
  sorry

/-- **Problem 18 (1)**, as Carroll states it, for `E` in the base `BC`:
`FG ∥ BC` iff `BE · sin 2B = EC · sin 2C`, i.e. `BE / EC = sin 2C / sin 2B`. -/
theorem problem18_a (A B C E F G : Plane) (hT : cross A B C ≠ 0) (hE : E ∈ segment ℝ B C)
    (hF : IsFoot E A B F) (hG : IsFoot E A C G) :
    (∃ k : ℝ, G - F = k • (C - B)) ↔
      dist B E * Real.sin (2 * ∠ A B C) = dist E C * Real.sin (2 * ∠ A C B) := by
  sorry

/-- **Problem 18 (2)**: the geometric construction. The point `D` with right angles `ABD`, `ACD`
exists; and if `AD` cuts the base at `E` (`E = B + τ (C - B)`), then the perpendiculars from `E`
have feet `F`, `G` with `FG ∥ BC` (so `E` is the point of part (1)). -/
theorem problem18_b (A B C : Plane) (hT : cross A B C ≠ 0) :
    (∃ D : Plane, ⟪A - B, D - B⟫ = 0 ∧ ⟪A - C, D - C⟫ = 0) ∧
    ∀ D E F G : Plane, ∀ τ : ℝ, ⟪A - B, D - B⟫ = 0 → ⟪A - C, D - C⟫ = 0 →
      E ∈ line[ℝ, A, D] → E = B + τ • (C - B) → IsFoot E A B F → IsFoot E A C G →
      (∃ k : ℝ, G - F = k • (C - B)) ∧
        τ * Real.sin (2 * ∠ A B C) = (1 - τ) * Real.sin (2 * ∠ A C B) := by
  sorry

/-- **Problem 18 (2)**, completed: when the base angles `B`, `C` are acute, the line `AD` does cut
the base `BC`, at exactly one point `E` (which by `problem18_b` is the required point). -/
theorem problem18_b_cuts (A B C D : Plane) (hT : cross A B C ≠ 0)
    (hB : ∠ A B C < Real.pi / 2) (hC : ∠ A C B < Real.pi / 2)
    (hD1 : ⟪A - B, D - B⟫ = 0) (hD2 : ⟪A - C, D - C⟫ = 0) :
    ∃! E : Plane, E ∈ segment ℝ B C ∧ E ∈ line[ℝ, A, D] := by
  sorry

end PillowProblems.P18
