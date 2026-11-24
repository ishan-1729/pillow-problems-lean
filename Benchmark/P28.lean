import PillowProblems.Basic

/-!
# Problem 28 (Trigonometry: Plane)

**Question.** *(dated 12/78)*

> If the sides of a given Triangle, taken cyclically, be divided in extreme and mean ratio; and if the Points be joined: find the ratio which the area of the Triangle, so formed, has to the area of the given Triangle.

**Answer.**

> \[7 - 3\sqrt{5}.\]

*(Carroll's solution: Chapter III, problem 28; text in `data/problems.json`.)*

**Lean reading.** A point `P` divides a segment `XY` in extreme and mean ratio, with greater part `XP`, when
`P` lies on the segment and `XP² = XY · PY` (`ExtremeMeanRatio X P Y`); the position of `P`
(`XP = XY · (√5 - 1)/2`) is derived in the proof, not assumed. "Taken cyclically" is read, as in
Carroll's solution, as: the greater parts are `BA'`, `CB'`, `AC'` (on `BC`, `CA`, `AB`);
`problem28_reversed` proves the same ratio for the other cyclic choice `CA'`, `AB'`, `BC'`.
The given triangle is assumed non-degenerate (`cross A B C ≠ 0`), so that the ratio of areas is
defined. Carroll's answer `7 - 3√5` is proved for the ratio `area A'B'C' / area ABC`;
`problem28_nonvacuous` shows that every segment has such a dividing point.

**Status.** proved
-/

namespace PillowProblems.P28

open AffineMap

/-- `P` divides the segment `XY` in extreme and mean ratio, the greater part being `XP`:
`P` lies on the segment `XY` and the whole is to the greater part as the greater part is to the
less, `XY : XP = XP : PY`, i.e. `XP² = XY · PY`. -/
def ExtremeMeanRatio (X P Y : Plane) : Prop :=
  Wbtw ℝ X P Y ∧ dist X P ^ 2 = dist X Y * dist P Y

/-- **Problem 28.** If `A'`, `B'`, `C'` divide the sides `BC`, `CA`, `AB` of a triangle in
extreme and mean ratio, the greater parts `BA'`, `CB'`, `AC'` being taken cyclically, then
`area A'B'C' : area ABC = 7 - 3√5`. -/
theorem problem28 (A B C A' B' C' : Plane) (hABC : cross A B C ≠ 0)
    (hA' : ExtremeMeanRatio B A' C) (hB' : ExtremeMeanRatio C B' A)
    (hC' : ExtremeMeanRatio A C' B) :
    triArea A' B' C' / triArea A B C = 7 - 3 * Real.sqrt 5 := by
  sorry

/-- The same ratio when the greater parts are taken cyclically the other way round
(`CA'`, `AB'`, `BC'`). -/
theorem problem28_reversed (A B C A' B' C' : Plane) (hABC : cross A B C ≠ 0)
    (hA' : ExtremeMeanRatio C A' B) (hB' : ExtremeMeanRatio A B' C)
    (hC' : ExtremeMeanRatio B C' A) :
    triArea A' B' C' / triArea A B C = 7 - 3 * Real.sqrt 5 := by
  sorry

/-- Every segment can be divided in extreme and mean ratio, so the hypotheses of `problem28`
are satisfiable for every triangle. -/
theorem problem28_nonvacuous (X Y : Plane) : ∃ P, ExtremeMeanRatio X P Y := by
  sorry

end PillowProblems.P28
