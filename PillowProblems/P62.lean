import PillowProblems.Basic

/-!
# Problem 62 (Pure Geometry, Plane)

**Question.** *(dated 12/76)*

> Given two Lines meeting at a Point, and given a Point lying within the angle contained by them: draw a line, through the given Point, and forming, with the given Lines, the least possible Triangle.

*(Carroll's solution: Chapter III, problem 62; text in `data/problems.json`.)*

**Lean reading.** The two given lines meet at `A`; the angle is given by points `B`, `C` on its arms
(`cross A B C ≠ 0`), and `P` lies strictly inside it (`InAngle`: `P = A + s (B - A) + t (C - A)`
with `s, t > 0`). A line through `P` forms a triangle with the given lines as in Carroll's
figure when it cuts both arms, i.e. meets the rays from `A` through `B` and `C` at points
`G, H ≠ A` (`Cuts`); the triangle is `AGH`. This restriction is tacit in Carroll: a line through
`P` meeting one arm and the backward extension of the other cuts off triangles of arbitrarily
small area, so without it there is no least triangle. `problem62` proves that there is exactly
one least triangle, and that a cut is least iff `P` is the midpoint of `GH` (Carroll's `FP = PE`,
which his construction `DE = AD` produces).

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P62

open scoped EuclideanGeometry

/-- `P` lies strictly within the angle `BAC` formed by the lines `AB`, `AC`. -/
def InAngle (A B C P : Plane) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ P = A + s • (B - A) + t • (C - A)

/-- A line through `P` cuts the arms of the angle `BAC`: it meets the ray `AB` (beyond `A`) at `G`
and the ray `AC` (beyond `A`) at `H`, so that it forms with the given lines the triangle `AGH`. -/
def Cuts (A B C P G H : Plane) : Prop :=
  (∃ g : ℝ, 0 < g ∧ G = A + g • (B - A)) ∧ (∃ h : ℝ, 0 < h ∧ H = A + h • (C - A)) ∧
    P ∈ line[ℝ, G, H]

private lemma mem_line {B C X : Plane} : X ∈ line[ℝ, B, C] ↔ ∃ t : ℝ, X = B + t • (C - B) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  constructor
  · rintro ⟨t, ht⟩; exact ⟨t, by rw [← ht]; abel⟩
  · rintro ⟨t, ht⟩; exact ⟨t, by rw [ht]; abel⟩

private lemma indep {A B C : Plane} (hT : cross A B C ≠ 0) {x y : ℝ}
    (h : x • (B - A) + y • (C - A) = 0) : x = 0 ∧ y = 0 := by
  have h0 := congrArg (· 0) h
  have h1 := congrArg (· 1) h
  simp at h0 h1
  unfold cross at hT
  constructor
  · have : x * ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) = 0 := by
      linear_combination (C 1 - A 1) * h0 - (C 0 - A 0) * h1
    exact (mul_eq_zero.1 this).resolve_right hT
  · have : y * ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) = 0 := by
      linear_combination (B 0 - A 0) * h1 - (B 1 - A 1) * h0
    exact (mul_eq_zero.1 this).resolve_right hT

private lemma area_eq (A B C : Plane) (g h : ℝ) (hg : 0 < g) (hh : 0 < h) :
    triArea A (A + g • (B - A)) (A + h • (C - A)) = g * h * (|cross A B C| / 2) := by
  have : cross A (A + g • (B - A)) (A + h • (C - A)) = g * h * cross A B C := by
    simp only [cross, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  rw [triArea, this, abs_mul, abs_mul, abs_of_pos hg, abs_of_pos hh]; ring

/-- Key computation: for a cut `(G, H)` with parameters `g, h`, we have `s/g + t/h = 1`. -/
private lemma cut_rel {A B C : Plane} (hT : cross A B C ≠ 0) {s t g h : ℝ}
    (hP : A + s • (B - A) + t • (C - A) ∈ line[ℝ, A + g • (B - A), A + h • (C - A)]) :
    s * h + t * g = g * h := by
  obtain ⟨r, hr⟩ := mem_line.1 hP
  have := indep hT (x := s - (1 - r) * g) (y := t - r * h) (by
    linear_combination (norm := module) hr)
  obtain ⟨h1, h2⟩ := this
  have e1 : s = (1 - r) * g := by linarith
  have e2 : t = r * h := by linarith
  rw [e1, e2]; ring

theorem problem62 (A B C P : Plane) (hT : cross A B C ≠ 0) (hP : InAngle A B C P) :
    (∃! GH : Plane × Plane, Cuts A B C P GH.1 GH.2 ∧
        ∀ G H, Cuts A B C P G H → triArea A GH.1 GH.2 ≤ triArea A G H) ∧
    ∀ G H, Cuts A B C P G H →
      ((∀ G' H', Cuts A B C P G' H' → triArea A G H ≤ triArea A G' H') ↔
        midpoint ℝ G H = P) := by
  obtain ⟨s, t, hs, ht, rfl⟩ := hP
  have hTa : 0 < |cross A B C| / 2 := by positivity
  -- the cut with `P` as midpoint
  set G₀ := A + (2 * s) • (B - A)
  set H₀ := A + (2 * t) • (C - A)
  have hcut₀ : Cuts A B C (A + s • (B - A) + t • (C - A)) G₀ H₀ := by
    refine ⟨⟨2 * s, by positivity, rfl⟩, ⟨2 * t, by positivity, rfl⟩, ?_⟩
    rw [mem_line]
    exact ⟨1 / 2, by simp only [G₀, H₀]; module⟩
  -- every cut has area at least that of the midpoint cut, with equality only for it
  have key : ∀ G H, Cuts A B C (A + s • (B - A) + t • (C - A)) G H →
      triArea A G₀ H₀ ≤ triArea A G H ∧
        (triArea A G H ≤ triArea A G₀ H₀ → G = G₀ ∧ H = H₀) := by
    rintro G H ⟨⟨g, hg, rfl⟩, ⟨h, hh, rfl⟩, hl⟩
    have rel := cut_rel hT hl
    simp only [G₀, H₀]
    rw [area_eq A B C g h hg hh, area_eq A B C _ _ (by positivity) (by positivity)]
    have hgh : 4 * s * t ≤ g * h := by
      nlinarith [sq_nonneg (s * h - t * g), mul_pos hg hh, mul_pos hs ht]
    refine ⟨by nlinarith, fun hle => ?_⟩
    have heq : g * h = 4 * s * t := by
      have := (mul_le_mul_iff_left₀ hTa).1 (by linarith : g * h * (|cross A B C| / 2) ≤
        (2 * s) * (2 * t) * (|cross A B C| / 2))
      linarith
    have h1 : s * h = t * g := by
      have : (s * h - t * g) ^ 2 = 0 := by
        linear_combination (s * h + t * g + g * h) * rel + g * h * heq
      linarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 this]
    have hg' : g = 2 * s := by
      have : h * (g - 2 * s) = 0 := by nlinarith
      have := (mul_eq_zero.1 this).resolve_left hh.ne'
      linarith
    have hh' : h = 2 * t := by
      have : g * (h - 2 * t) = 0 := by nlinarith
      have := (mul_eq_zero.1 this).resolve_left hg.ne'
      linarith
    exact ⟨by rw [hg'], by rw [hh']⟩
  refine ⟨⟨(G₀, H₀), ⟨hcut₀, fun G H hc => (key G H hc).1⟩, ?_⟩, ?_⟩
  · rintro ⟨G, H⟩ ⟨hc, hmin⟩
    obtain ⟨e1, e2⟩ := (key G H hc).2 (hmin G₀ H₀ hcut₀)
    simp [e1, e2]
  · intro G H hc
    constructor
    · intro hmin
      obtain ⟨e1, e2⟩ := (key G H hc).2 (hmin G₀ H₀ hcut₀)
      rw [e1, e2, midpoint_eq_smul_add]; simp only [G₀, H₀, invOf_eq_inv]; module
    · intro hm G' H' hc'
      obtain ⟨⟨g, hg, rfl⟩, ⟨h, hh, rfl⟩, -⟩ := hc
      rw [midpoint_eq_smul_add, invOf_eq_inv] at hm
      have := indep hT (x := g / 2 - s) (y := h / 2 - t) (by
        linear_combination (norm := module) hm)
      have hg' : g = 2 * s := by linarith [this.1]
      have hh' : h = 2 * t := by linarith [this.2]
      subst hg' hh'
      exact (key G' H' hc').1

/-- The hypotheses are satisfiable: the point `(1, 1)` within the right angle at the origin. -/
theorem problem62_nonvacuous :
    cross (pt 0 0) (pt 1 0) (pt 0 1) ≠ 0 ∧ InAngle (pt 0 0) (pt 1 0) (pt 0 1) (pt 1 1) := by
  refine ⟨by simp [cross], 1, 1, one_pos, one_pos, ?_⟩
  ext i; fin_cases i <;> simp [pt]

end PillowProblems.P62
