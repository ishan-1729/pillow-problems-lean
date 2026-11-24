import PillowProblems.Basic

/-!
# Problem 30 (Pure Geometry, Plane)

**Question.** *(dated 15/3/89)*

> In a given Triangle, to place a line parallel to the base, such that if from its extremities lines be drawn, to the base, parallel to the sides, they shall be together double of the inscribed Line.

*(Carroll's solution: Chapter III, problem 30; text in `data/problems.json`.)*

**Lean reading.** The triangle `ABC` is nondegenerate (`cross A B C ≠ 0`), with base `BC`. The
"inscribed line" is the segment `C'B'` with `C'` on the side `AB` and `B'` on the side `AC`
(as in Carroll's figure), parallel to `BC` (`B' - C'` is a multiple of `C - B`). The lines
drawn "to the base, parallel to the sides" are `B'D ∥ AB` and `C'E ∥ AC` with `D`, `E` on the
line `BC`; these points are determined, so asserting that some such `D`, `E` exist loses nothing.
The required property is `B'D + C'E = 2·B'C'`. Carroll answers with a construction (the point
`L` with `C'L = ½ C'B`, `B'L = ½ B'C`, i.e. `C'B + B'C = 2 B'C'`); the theorem proves the
position it produces explicitly and shows it is the only solution:
`C' = A + t (B - A)`, `B' = A + t (C - A)` with `t = (AB + AC) / (2 BC + AB + AC)`. The proof
uses Carroll's observations `B'D = C'B`, `C'E = B'C` (Euc. I. 34).

**Status.** proved
-/

namespace PillowProblems.P30

open EuclideanGeometry

private lemma dist_eq' (x y : Plane) : dist x y = Real.sqrt ((x 0 - y 0)^2 + (x 1 - y 1)^2) := by
  simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma dist_scale {P Q X Y : Plane} {k : ℝ} (hk : 0 ≤ k) (h0 : P 0 - Q 0 = k * (X 0 - Y 0))
    (h1 : P 1 - Q 1 = k * (X 1 - Y 1)) : dist P Q = k * dist X Y := by
  rw [dist_eq', dist_eq', h0, h1,
    show (k * (X 0 - Y 0)) ^ 2 + (k * (X 1 - Y 1)) ^ 2 = k ^ 2 * ((X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2)
      by ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk]

private lemma line_coord {p x y : Plane} (h : p ∈ line[ℝ, x, y]) :
    ∃ r : ℝ, p 0 = x 0 + r * (y 0 - x 0) ∧ p 1 = x 1 + r * (y 1 - x 1) := by
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 h
  refine ⟨r, ?_, ?_⟩ <;> (rw [← hr, AffineMap.lineMap_apply_module']; simp; ring)

private lemma mem_line_of (p x y : Plane) (r : ℝ) (h0 : p 0 = x 0 + r * (y 0 - x 0))
    (h1 : p 1 = x 1 + r * (y 1 - x 1)) : p ∈ line[ℝ, x, y] := by
  refine mem_affineSpan_pair_iff_exists_lineMap_eq.2 ⟨r, ?_⟩
  rw [AffineMap.lineMap_apply_module']
  ext i; fin_cases i <;> simp [h0, h1] <;> ring

private lemma seg_coord {p x y : Plane} (h : p ∈ segment ℝ x y) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ p 0 = x 0 + r * (y 0 - x 0) ∧ p 1 = x 1 + r * (y 1 - x 1) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h
  obtain rfl : a = 1 - b := by linarith
  refine ⟨b, hb, by linarith, ?_, ?_⟩ <;> (simp; ring)

private lemma mem_seg_of (p x y : Plane) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (h0 : p 0 = x 0 + r * (y 0 - x 0)) (h1 : p 1 = x 1 + r * (y 1 - x 1)) :
    p ∈ segment ℝ x y := by
  refine ⟨1 - r, r, by linarith, hr0, by ring, ?_⟩
  ext i; fin_cases i <;> simp [h0, h1] <;> ring

private lemma vec_coord {p q x y : Plane} {l : ℝ} (h : p - q = l • (x - y)) :
    p 0 - q 0 = l * (x 0 - y 0) ∧ p 1 - q 1 = l * (x 1 - y 1) := by
  constructor
  · have := congrArg (fun v : Plane => v 0) h; simpa using this
  · have := congrArg (fun v : Plane => v 1) h; simpa using this

private lemma indep {u0 u1 v0 v1 p q : ℝ} (h : u0 * v1 - v0 * u1 ≠ 0)
    (h0 : p * u0 + q * v0 = 0) (h1 : p * u1 + q * v1 = 0) : p = 0 ∧ q = 0 := by
  constructor
  · have : p * (u0 * v1 - v0 * u1) = 0 := by linear_combination v1 * h0 - v0 * h1
    simpa [h] using this
  · have : q * (u0 * v1 - v0 * u1) = 0 := by linear_combination u0 * h1 - u1 * h0
    simpa [h] using this

/-- **Problem 30.** In the triangle `ABC` (base `BC`), let `C'B'` be a line with `C'` on `AB`,
`B'` on `AC`, parallel to `BC`; let `B'D ∥ AB` and `C'E ∥ AC` meet the base line at `D`, `E`.
Then `B'D + C'E = 2 B'C'` exactly for one such line, namely the one with
`AC' / AB = AB' / AC = (AB + AC) / (2 BC + AB + AC)`. -/
theorem problem30 (A B C : Plane) (hABC : cross A B C ≠ 0) (B' C' : Plane) :
    (B' ∈ segment ℝ A C ∧ C' ∈ segment ℝ A B ∧ (∃ l : ℝ, B' - C' = l • (C - B)) ∧
      ∃ D E : Plane, D ∈ line[ℝ, B, C] ∧ E ∈ line[ℝ, B, C] ∧
        (∃ l : ℝ, D - B' = l • (B - A)) ∧ (∃ l : ℝ, E - C' = l • (C - A)) ∧
        dist B' D + dist C' E = 2 * dist B' C') ↔
      (C' = A + ((dist A B + dist A C) / (2 * dist B C + dist A B + dist A C)) • (B - A) ∧
       B' = A + ((dist A B + dist A C) / (2 * dist B C + dist A B + dist A C)) • (C - A)) := by
  unfold cross at hABC
  have hBC : 0 < dist B C := by
    rw [dist_pos]; rintro rfl; apply hABC; ring
  have hden : 0 < 2 * dist B C + dist A B + dist A C := by positivity
  constructor
  · rintro ⟨hB', hC', ⟨l, hl⟩, D, E, hD, hE, ⟨l₁, hl₁⟩, ⟨l₂, hl₂⟩, hsum⟩
    obtain ⟨b, hb0, hb1, hb'0, hb'1⟩ := seg_coord hB'
    obtain ⟨s, hs0, hs1, hc'0, hc'1⟩ := seg_coord hC'
    obtain ⟨l0, l1⟩ := vec_coord hl
    obtain ⟨μ, hμ0, hμ1⟩ := line_coord hD
    obtain ⟨ν, hν0, hν1⟩ := line_coord hE
    obtain ⟨m0, m1⟩ := vec_coord hl₁
    obtain ⟨n0, n1⟩ := vec_coord hl₂
    -- the parallel gives the same parameter on both sides
    obtain ⟨e1, e2⟩ := indep (p := l - s) (q := b - l) hABC
      (by rw [hb'0, hc'0] at l0; linear_combination l0)
      (by rw [hb'1, hc'1] at l1; linear_combination l1)
    have hbs : b = s := by linarith
    subst hbs
    obtain ⟨f1, f2⟩ := indep (p := 1 - μ - l₁) (q := μ - b) hABC
      (by rw [hμ0, hb'0] at m0; linear_combination m0)
      (by rw [hμ1, hb'1] at m1; linear_combination m1)
    obtain ⟨g1, g2⟩ := indep (p := 1 - ν - b) (q := ν - l₂) hABC
      (by rw [hν0, hc'0] at n0; linear_combination n0)
      (by rw [hν1, hc'1] at n1; linear_combination n1)
    have d1 : dist B' D = (1 - b) * dist A B := dist_scale (by linarith)
      (by rw [hb'0, hμ0]; linear_combination (B 0 - C 0) * f2)
      (by rw [hb'1, hμ1]; linear_combination (B 1 - C 1) * f2)
    have d2 : dist C' E = (1 - b) * dist A C := dist_scale (by linarith)
      (by rw [hc'0, hν0]; linear_combination (C 0 - B 0) * g1)
      (by rw [hc'1, hν1]; linear_combination (C 1 - B 1) * g1)
    have d3 : dist B' C' = b * dist B C := by
      rw [dist_comm B C]
      exact dist_scale hb0 (by rw [hb'0, hc'0]; ring) (by rw [hb'1, hc'1]; ring)
    rw [d1, d2, d3] at hsum
    have ht : (dist A B + dist A C) / (2 * dist B C + dist A B + dist A C) = b := by
      rw [div_eq_iff hden.ne']; linarith
    rw [ht]
    constructor <;> (ext i; fin_cases i <;> simp [hb'0, hb'1, hc'0, hc'1])
  · rintro ⟨hC', hB'⟩
    set t := (dist A B + dist A C) / (2 * dist B C + dist A B + dist A C) with ht
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hden]; linarith
    have hteq : t * (2 * dist B C + dist A B + dist A C) = dist A B + dist A C := by
      rw [ht]; field_simp
    have hb'0 : B' 0 = A 0 + t * (C 0 - A 0) := by rw [hB']; simp
    have hb'1 : B' 1 = A 1 + t * (C 1 - A 1) := by rw [hB']; simp
    have hc'0 : C' 0 = A 0 + t * (B 0 - A 0) := by rw [hC']; simp
    have hc'1 : C' 1 = A 1 + t * (B 1 - A 1) := by rw [hC']; simp
    refine ⟨mem_seg_of _ _ _ t ht0 ht1 hb'0 hb'1, mem_seg_of _ _ _ t ht0 ht1 hc'0 hc'1,
      ⟨t, ?_⟩, B + t • (C - B), B + (1 - t) • (C - B),
      mem_line_of _ _ _ t (by simp) (by simp), mem_line_of _ _ _ (1 - t) (by simp) (by simp),
      ⟨1 - t, ?_⟩, ⟨1 - t, ?_⟩, ?_⟩
    · ext i; fin_cases i <;> simp [hb'0, hb'1, hc'0, hc'1] <;> ring
    · ext i; fin_cases i <;> simp [hb'0, hb'1] <;> ring
    · ext i; fin_cases i <;> simp [hc'0, hc'1] <;> ring
    · have d1 : dist B' (B + t • (C - B)) = (1 - t) * dist A B :=
        dist_scale (by linarith) (by simp [hb'0]; ring) (by simp [hb'1]; ring)
      have d2 : dist C' (B + (1 - t) • (C - B)) = (1 - t) * dist A C :=
        dist_scale (by linarith) (by simp [hc'0]; ring) (by simp [hc'1]; ring)
      have d3 : dist B' C' = t * dist B C := by
        rw [dist_comm B C]
        exact dist_scale ht0 (by rw [hb'0, hc'0]; ring) (by rw [hb'1, hc'1]; ring)
      rw [d1, d2, d3]; linarith

end PillowProblems.P30
