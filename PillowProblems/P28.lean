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

/-- The golden section of a non-degenerate segment is the point at fraction `(√5 - 1)/2` from
the end carrying the greater part. -/
private lemma eq_lineMap_of_extremeMeanRatio {X P Y : Plane} (hXY : X ≠ Y)
    (h : ExtremeMeanRatio X P Y) : P = lineMap X Y ((Real.sqrt 5 - 1) / 2) := by
  obtain ⟨⟨t, ⟨ht0, ht1⟩, rfl⟩, hd⟩ := h
  have hd0 : 0 < dist X Y := dist_pos.2 hXY
  rw [dist_left_lineMap, dist_lineMap_right, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ht0, abs_of_nonneg (by linarith)] at hd
  have ht : t ^ 2 = 1 - t := by
    have : (t ^ 2 - (1 - t)) * dist X Y ^ 2 = 0 := by linear_combination hd
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h (by positivity)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5' : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have : (t - (Real.sqrt 5 - 1) / 2) * (t + (Real.sqrt 5 + 1) / 2) = 0 := by
    linear_combination ht - h5 / 4
  rcases mul_eq_zero.1 this with h | h
  · rw [show t = (Real.sqrt 5 - 1) / 2 by linarith]
  · exfalso; linarith

private lemma lineMap_coord (X Y : Plane) (t : ℝ) (i : Fin 2) :
    (lineMap X Y t : Plane) i = X i + t * (Y i - X i) := by
  simp [AffineMap.lineMap_apply]; ring

/-- **Problem 28.** If `A'`, `B'`, `C'` divide the sides `BC`, `CA`, `AB` of a triangle in
extreme and mean ratio, the greater parts `BA'`, `CB'`, `AC'` being taken cyclically, then
`area A'B'C' : area ABC = 7 - 3√5`. -/
theorem problem28 (A B C A' B' C' : Plane) (hABC : cross A B C ≠ 0)
    (hA' : ExtremeMeanRatio B A' C) (hB' : ExtremeMeanRatio C B' A)
    (hC' : ExtremeMeanRatio A C' B) :
    triArea A' B' C' / triArea A B C = 7 - 3 * Real.sqrt 5 := by
  have hBC : B ≠ C := by rintro rfl; exact hABC (by unfold cross; ring)
  have hCA : C ≠ A := by rintro rfl; exact hABC (by unfold cross; ring)
  have hAB : A ≠ B := by rintro rfl; exact hABC (by unfold cross; ring)
  rw [eq_lineMap_of_extremeMeanRatio hBC hA', eq_lineMap_of_extremeMeanRatio hCA hB',
    eq_lineMap_of_extremeMeanRatio hAB hC']
  set φ := (Real.sqrt 5 - 1) / 2 with hφ
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hcross : cross (lineMap B C φ) (lineMap C A φ) (lineMap A B φ) =
      (7 - 3 * Real.sqrt 5) * cross A B C := by
    unfold cross
    simp only [lineMap_coord]
    rw [hφ]
    linear_combination (3 / 4 * ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1))) * h5
  have h73 : 0 < 7 - 3 * Real.sqrt 5 := by nlinarith [Real.sqrt_nonneg 5]
  unfold triArea
  rw [hcross, abs_mul, abs_of_pos h73]
  have : 0 < |cross A B C| := abs_pos.2 hABC
  field_simp

/-- The same ratio when the greater parts are taken cyclically the other way round
(`CA'`, `AB'`, `BC'`). -/
theorem problem28_reversed (A B C A' B' C' : Plane) (hABC : cross A B C ≠ 0)
    (hA' : ExtremeMeanRatio C A' B) (hB' : ExtremeMeanRatio A B' C)
    (hC' : ExtremeMeanRatio B C' A) :
    triArea A' B' C' / triArea A B C = 7 - 3 * Real.sqrt 5 := by
  have hswap : ∀ P Q R : Plane, triArea P R Q = triArea P Q R := by
    intro P Q R
    unfold triArea
    rw [show cross P R Q = -cross P Q R by unfold cross; ring, abs_neg]
  have hACB : cross A C B ≠ 0 := by
    rw [show cross A C B = -cross A B C by unfold cross; ring]
    exact neg_ne_zero.2 hABC
  have h := problem28 A C B A' C' B' hACB hA' hC' hB'
  rwa [hswap, hswap A] at h

/-- Every segment can be divided in extreme and mean ratio, so the hypotheses of `problem28`
are satisfiable for every triangle. -/
theorem problem28_nonvacuous (X Y : Plane) : ∃ P, ExtremeMeanRatio X P Y := by
  refine ⟨lineMap X Y ((Real.sqrt 5 - 1) / 2), ?_, ?_⟩
  · have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h1 : 1 ≤ Real.sqrt 5 := by nlinarith [Real.sqrt_nonneg 5]
    have h3 : Real.sqrt 5 ≤ 3 := by nlinarith [Real.sqrt_nonneg 5]
    exact ⟨_, ⟨by linarith, by linarith⟩, rfl⟩
  · have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h1 : 1 ≤ Real.sqrt 5 := by nlinarith [Real.sqrt_nonneg 5]
    have h3 : Real.sqrt 5 ≤ 3 := by nlinarith [Real.sqrt_nonneg 5]
    rw [dist_left_lineMap, dist_lineMap_right, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linear_combination (dist X Y ^ 2 / 4) * h5

end PillowProblems.P28
