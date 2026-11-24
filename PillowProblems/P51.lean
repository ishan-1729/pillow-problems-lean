import PillowProblems.Basic

/-!
# Problem 51 (Pure Geometry, Plane)

**Question.** *(dated 12/81)*

> From a given Point, in one side of a given Triangle, to draw a line, terminated by the other side, so that, if from its ends lines be drawn at right angles to the base, their sum shall be equal to the first line.

*(Carroll's solution: Chapter III, problem 51; text in `data/problems.json`.)*

**Lean reading.** Coordinates are chosen with the base `BC` on the `x`-axis and `A` above it (every triangle
is congruent to such a one). The perpendicular from a point `P` to the base is then `P (pt (P 0) 0)`.
The given point `D` lies on side `AB` with `D ≠ A`, so that the perpendicular `DN` to `AC` is
defined. The line `DE` is terminated by the side `AC` (`E ∈ segment A C`). `N` and `S` are
Carroll's points: `N` is the foot of the perpendicular from `D` to `AC`, and `S` is where `DN` meets
the base produced. `S` exists unless `∠C` is right; then `DN` is parallel to the base, Carroll's
construction fails, and the hypotheses cannot hold, except when `D = B`: then `DN` is the base
itself, `S` may be any point of it, the theorem still applies, and both sides are false. The theorem proves that `DE` equals the sum of the perpendiculars from `D`
and `E` iff `E` comes from Carroll's synthesis for some point `K` of the base with `SK² = SD · SN`.
Carroll's supplementary proof that `DH = HK` is included. The rectangle `SD · SN` is taken with sign
(the inner product of `SD⃗` and `SN⃗`). This agrees with Carroll's rectangle when `S` lies outside
`DN`, as in his figure. When `S` lies between `D` and `N` there is no solution, and the unsigned
rectangle would wrongly give one. The problem need not have a solution: there are zero, one or two
(two choices of `K`), and the theorem shows Carroll's construction yields exactly these.
`problem51_nonvacuous` exhibits a configuration with a solution.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P51

open scoped EuclideanGeometry RealInnerProductSpace

private lemma inner_coord (P Q : Plane) : ⟪P, Q⟫ = P 0 * Q 0 + P 1 * Q 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

private lemma dist_coord (P Q : Plane) :
    dist P Q = Real.sqrt ((P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2) := by
  rw [EuclideanSpace.dist_eq]; simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma dist_foot (P : Plane) : dist P (pt (P 0) 0) = |P 1| := by
  rw [dist_coord]; simp [Real.sqrt_sq_eq_abs]

private lemma seg_param {X Y P : Plane} (h : P ∈ segment ℝ X Y) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ P 0 = X 0 + s * (Y 0 - X 0) ∧ P 1 = X 1 + s * (Y 1 - X 1) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h
  refine ⟨b, hb, by linarith, ?_, ?_⟩ <;>
  · obtain rfl : a = 1 - b := by linarith
    simp; ring

private lemma line_param {X Y P : Plane} (h : P ∈ line[ℝ, X, Y]) :
    ∃ s : ℝ, P 0 = X 0 + s * (Y 0 - X 0) ∧ P 1 = X 1 + s * (Y 1 - X 1) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at h
  obtain ⟨s, rfl⟩ := h
  refine ⟨s, ?_, ?_⟩ <;> simp [AffineMap.lineMap_apply_module'] <;> ring

private lemma line_mem {X Y P : Plane} (s : ℝ) (h0 : P 0 = X 0 + s * (Y 0 - X 0))
    (h1 : P 1 = X 1 + s * (Y 1 - X 1)) : P ∈ line[ℝ, X, Y] := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  refine ⟨s, ?_⟩
  ext i; fin_cases i <;> simp [AffineMap.lineMap_apply_module', h0, h1] <;> ring

/-- The power of `S` with respect to a circle with centre `(κ, h)` through `D` and `N`, when `S`
lies on the line `DN`. -/
private lemma power (xd yd xn yn xs ys κ h τ : ℝ) (hx : xs = xd + τ * (xn - xd))
    (hy : ys = yd + τ * (yn - yd))
    (hNH : (xn - κ) ^ 2 + (yn - h) ^ 2 = (xd - κ) ^ 2 + (yd - h) ^ 2) :
    (xd - xs) * (xn - xs) + (yd - ys) * (yn - ys) =
      (xs - κ) ^ 2 + (ys - h) ^ 2 - ((xd - κ) ^ 2 + (yd - h) ^ 2) := by
  subst hx hy
  linear_combination (-τ) * hNH

/-- **Problem 51.** The base `BC` lies on the `x`-axis and `A` above it; `D` is the given point
of the side `AB` (not `A`), `N` the foot of the perpendicular from `D` to `AC`, and `S` the point
where `DN` produced meets the base produced. For a point `E` of the other side `AC`, the line `DE`
equals the sum of the perpendiculars from `D` and `E` to the base if and only if `E` is given by
Carroll's construction: for a point `K` of the base with `SK² = SD · SN` (the rectangle taken
with sign), the perpendicular to the base at `K` meets the parallel to `AC` through the midpoint
of `DA` at `H`, and `E` lies on `DH` (produced). -/
theorem problem51 (A B C D N S E : Plane)
    (hB : B 1 = 0) (hC : C 1 = 0) (hBC : B 0 ≠ C 0) (hA : 0 < A 1)
    (hD : D ∈ segment ℝ A B) (hDA : D ≠ A)
    (hN : N ∈ line[ℝ, A, C]) (hDN : ⟪D - N, C - A⟫ = 0)
    (hS1 : S 1 = 0) (hS : S ∈ line[ℝ, D, N])
    (hE : E ∈ segment ℝ A C) :
    dist D E = dist D (pt (D 0) 0) + dist E (pt (E 0) 0) ↔
      ∃ K H : Plane, K 1 = 0 ∧ dist S K ^ 2 = ⟪D - S, N - S⟫ ∧
        (∃ t : ℝ, H = midpoint ℝ D A + t • (C - A)) ∧ H 0 = K 0 ∧ E ∈ line[ℝ, D, H] := by
  obtain ⟨δ, hδ0, hδ1, hD0, hD1⟩ := seg_param hD
  obtain ⟨σ, hσ0, hσ1, hE0, hE1⟩ := seg_param hE
  obtain ⟨ν, hN0, hN1⟩ := line_param hN
  obtain ⟨τ, hS0', hS1'⟩ := line_param hS
  rw [hB] at hD1
  rw [hC] at hE1 hN1
  have hδ : δ ≠ 0 := by
    rintro rfl; apply hDA; ext i; fin_cases i <;> simp [hD0, hD1]
  rw [inner_coord] at hDN
  simp only [PiLp.sub_apply] at hDN
  rw [hC] at hDN
  have hyd : 0 ≤ D 1 := by rw [hD1]; nlinarith
  have hye : 0 ≤ E 1 := by rw [hE1]; nlinarith
  rw [dist_foot, dist_foot, abs_of_nonneg hyd, abs_of_nonneg hye, dist_coord,
    Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
  -- `N` is as far as `D` from any point `H` midway between `D` and a point `E` of `AC`
  have hNE : (N 0 - D 0) * (N 0 - E 0) + (N 1 - D 1) * (N 1 - E 1) = 0 := by
    have a0 : N 0 - E 0 = (ν - σ) * (C 0 - A 0) := by rw [hN0, hE0]; ring
    have a1 : N 1 - E 1 = (ν - σ) * (0 - A 1) := by rw [hN1, hE1]; ring
    rw [a0, a1]; linear_combination (σ - ν) * hDN
  have hNH : ∀ h0 h1 : ℝ, 2 * h0 = D 0 + E 0 → 2 * h1 = D 1 + E 1 →
      (N 0 - h0) ^ 2 + (N 1 - h1) ^ 2 = (D 0 - h0) ^ 2 + (D 1 - h1) ^ 2 := by
    intro h0 h1 e0 e1
    linear_combination (-(N 0 - D 0)) * e0 + (-(N 1 - D 1)) * e1 + hNE
  have hmid : ∀ t : ℝ, (midpoint ℝ D A + t • (C - A)) 0 = (D 0 + A 0) / 2 + t * (C 0 - A 0) ∧
      (midpoint ℝ D A + t • (C - A)) 1 = (D 1 + A 1) / 2 + t * (C 1 - A 1) := by
    intro t
    rw [midpoint_eq_smul_add]
    constructor <;> simp <;> ring
  constructor
  · intro hcond
    have e0 : 2 * ((D 0 + E 0) / 2) = D 0 + E 0 := by ring
    have e1 : 2 * ((D 1 + E 1) / 2) = D 1 + E 1 := by ring
    have hpow := power (D 0) (D 1) (N 0) (N 1) (S 0) (S 1) ((D 0 + E 0) / 2) ((D 1 + E 1) / 2) τ
      hS0' hS1' (hNH _ _ e0 e1)
    refine ⟨pt ((D 0 + E 0) / 2) 0, pt ((D 0 + E 0) / 2) ((D 1 + E 1) / 2), by simp, ?_,
      ⟨σ / 2, ?_⟩, by simp, ?_⟩
    · rw [dist_coord, Real.sq_sqrt (by positivity), inner_coord]
      simp only [PiLp.sub_apply, pt_zero, pt_one]
      rw [hpow, hS1]
      linear_combination (1 / 4) * hcond
    · obtain ⟨m0, m1⟩ := hmid (σ / 2)
      ext i; fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, pt_zero]; rw [m0, hE0]; ring
      · simp only [Fin.mk_one, Fin.isValue, pt_one]; rw [m1, hE1, hC]; ring
    · exact line_mem 2 (by simp; ring) (by simp; ring)
  · rintro ⟨K, H, hK1, hSK, ⟨t, hHt⟩, hHK, hEDH⟩
    obtain ⟨m0, m1⟩ := hmid t
    rw [← hHt] at m0 m1
    rw [hC] at m1
    obtain ⟨l, hl0, hl1⟩ := line_param hEDH
    have key : δ * (2 - l) * A 1 * (C 0 - B 0) = 0 := by
      rw [m0, hE0, hD0] at hl0
      rw [m1, hE1, hD1] at hl1
      linear_combination (2 * A 1) * hl0 + (2 * (C 0 - A 0)) * hl1
    have hl : l = 2 := by
      have hcb : C 0 - B 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hBC)
      have := mul_eq_zero.mp key
      rcases this with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact absurd h hδ
          · linarith
        · linarith
      · exact absurd h hcb
    subst hl
    have e0 : 2 * H 0 = D 0 + E 0 := by linarith
    have e1 : 2 * H 1 = D 1 + E 1 := by linarith
    have hpow := power (D 0) (D 1) (N 0) (N 1) (S 0) (S 1) (H 0) (H 1) τ hS0' hS1'
      (hNH _ _ e0 e1)
    rw [dist_coord, Real.sq_sqrt (by positivity), inner_coord] at hSK
    simp only [PiLp.sub_apply] at hSK
    rw [hpow, hK1, ← hHK, hS1] at hSK
    rw [show E 0 = 2 * H 0 - D 0 by linarith, show E 1 = 2 * H 1 - D 1 by linarith]
    linear_combination 4 * hSK

/-- The hypotheses of `problem51` can be met with a solution: `A = (0, 2)`, `B = (-2, 0)`,
`C = (2, 0)`, `D = (-1, 1)` the midpoint of `AB`, `N = A`, `S = B`; the point `E = (1, 1)` of `AC`
gives `DE = 2 = 1 + 1`. -/
theorem problem51_nonvacuous :
    ∃ A B C D N S E : Plane, B 1 = 0 ∧ C 1 = 0 ∧ B 0 ≠ C 0 ∧ 0 < A 1 ∧
      D ∈ segment ℝ A B ∧ D ≠ A ∧ N ∈ line[ℝ, A, C] ∧ ⟪D - N, C - A⟫ = 0 ∧
      S 1 = 0 ∧ S ∈ line[ℝ, D, N] ∧ E ∈ segment ℝ A C ∧
      dist D E = dist D (pt (D 0) 0) + dist E (pt (E 0) 0) := by
  refine ⟨pt 0 2, pt (-2) 0, pt 2 0, pt (-1) 1, pt 0 2, pt (-2) 0, pt 1 1, by simp, by simp,
    by simp; norm_num, by simp, ?_, ?_, left_mem_affineSpan_pair ℝ _ _, ?_, by simp, ?_, ?_, ?_⟩
  · refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; fin_cases i <;> simp [pt]
  · intro h
    have := congrArg (fun P : Plane => P 0) h
    simp at this
  · simp only [inner_coord, PiLp.sub_apply, pt_zero, pt_one]
    norm_num
  · exact line_mem (-1) (by simp; norm_num) (by simp; norm_num)
  · refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; fin_cases i <;> simp [pt]
  · rw [dist_foot, dist_foot, dist_coord]
    simp only [pt_zero, pt_one]
    rw [show ((-1 : ℝ) - 1) ^ 2 + (1 - 1) ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num

end PillowProblems.P51
