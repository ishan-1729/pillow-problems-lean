import PillowProblems.Basic

/-!
# Problem 54 (Trigonometry: Plane)

**Question.** *(dated 18/4/86)*

> Cut off, from a given Triangle, by lines parallel to the sides, 3 Triangles, so that the remaining Hexagon may be equilateral. Also find the lengths of its sides in terms of the sides of the given Triangle: and the ratios in which the sides of the given Triangle are divided.

**Answer.**

> Side \(AB\) must be divided at \(D\), \(G\), so that \[ AD :\, DG :\, GB\, \colon\colon\, \frac{1}{a} :\, \frac{1}{c} :\, \frac{1}{b}; \] and similarly for the other sides. Also each side of the Hexagon = \(\dfrac{1}{\tfrac{1}{a} + \tfrac{1}{b} + \tfrac{1}{c}}\).

*(Carroll's solution: Chapter III, problem 54; text in `data/problems.json`.)*

**Lean reading.** The triangle is `A, B, C` with `cross A B C ≠ 0`, and `a = BC`, `b = CA`, `c = AB`. Carroll
names only `D, G` on `AB` (and `E`, `F`, `J` in his figure), so we use: `D, G` on `AB` in the order
`A, D, G, B`; `F, J` on `BC` in the order `B, F, J, C`; `H, E` on `CA` in the order `C, H, E, A`.
Points on a side are given as `lineMap` with a parameter in `[0, 1]`. The cutting lines are parallel
to the sides (`DE ∥ BC`, `GF ∥ CA`, `JH ∥ AB`, each written as a difference vector being a multiple of
the side). This is `IsCut`, and the remaining hexagon is `DGFJHE`. Nothing assumes the cut-off
triangles are non-degenerate; that follows from the hexagon being equilateral. `problem54` derives
every side `= 1 / (1/a + 1/b + 1/c)` and the division ratios
`AD : DG : GB = 1/a : 1/c : 1/b` and, "similarly for the other sides",
`BF : FJ : JC = 1/b : 1/a : 1/c` and `CH : HE : EA = 1/c : 1/b : 1/a`. A ratio
`x : y : z = 1/p : 1/q : 1/r` is written `x·p = y·q = z·r`. These ratios fix the six points, so the
hexagon is unique. `problem54_exists` shows that such a cut exists in every triangle.

**Status.** proved
-/

namespace PillowProblems.P54

open AffineMap

/-- The configuration of the problem in the triangle `ABC`: `D, G` lie on side `AB` in the order
`A, D, G, B`; `F, J` on `BC` in the order `B, F, J, C`; `H, E` on `CA` in the order `C, H, E, A`;
and the cutting lines are parallel to the sides: `DE ∥ BC`, `GF ∥ CA`, `JH ∥ AB`. They cut off the
triangles `ADE`, `BFG`, `CHJ` and leave the hexagon `DGFJHE`. -/
def IsCut (A B C D E F G H J : Plane) : Prop :=
  (∃ d g : ℝ, 0 ≤ d ∧ d ≤ g ∧ g ≤ 1 ∧ D = lineMap A B d ∧ G = lineMap A B g) ∧
  (∃ f j : ℝ, 0 ≤ f ∧ f ≤ j ∧ j ≤ 1 ∧ F = lineMap B C f ∧ J = lineMap B C j) ∧
  (∃ h e : ℝ, 0 ≤ h ∧ h ≤ e ∧ e ≤ 1 ∧ H = lineMap C A h ∧ E = lineMap C A e) ∧
  (∃ t : ℝ, E - D = t • (C - B)) ∧ (∃ t : ℝ, F - G = t • (A - C)) ∧
  (∃ t : ℝ, H - J = t • (B - A))

/-- The hexagon `DGFJHE` is equilateral. -/
def IsEquilateralHex (D G F J H E : Plane) : Prop :=
  dist D G = dist G F ∧ dist G F = dist F J ∧ dist F J = dist J H ∧ dist J H = dist H E ∧
    dist H E = dist E D

private lemma lineMap_apply' (A B : Plane) (t : ℝ) (i : Fin 2) :
    (lineMap A B t : Plane) i = A i + t * (B i - A i) := by
  simp [AffineMap.lineMap_apply]; ring

/-- `B - A` and `C - A` are linearly independent when `ABC` is a triangle. -/
private lemma indep (A B C : Plane) (h : cross A B C ≠ 0) (α β : ℝ)
    (h0 : α * (B 0 - A 0) + β * (C 0 - A 0) = 0) (h1 : α * (B 1 - A 1) + β * (C 1 - A 1) = 0) :
    α = 0 ∧ β = 0 := by
  unfold cross at h
  constructor
  · have : α * ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) = 0 := by
      linear_combination (C 1 - A 1) * h0 - (C 0 - A 0) * h1
    exact (mul_eq_zero.1 this).resolve_right h
  · have : β * ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) = 0 := by
      linear_combination (B 0 - A 0) * h1 - (B 1 - A 1) * h0
    exact (mul_eq_zero.1 this).resolve_right h

private lemma dist_smul_eq (X Y P Q : Plane) (t : ℝ) (h : X - Y = t • (P - Q)) :
    dist Y X = |t| * dist Q P := by
  rw [dist_comm Y X, dist_eq_norm, h, norm_smul, Real.norm_eq_abs, dist_comm, dist_eq_norm]

private lemma dist_lm (A B : Plane) (x y : ℝ) (h : x ≤ y) :
    dist (lineMap A B x : Plane) (lineMap A B y) = (y - x) * dist A B := by
  rw [dist_lineMap_lineMap, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]

private lemma dist_lm_left (A B : Plane) (x : ℝ) (h : 0 ≤ x) :
    dist A (lineMap A B x : Plane) = x * dist A B := by
  have := dist_lm A B 0 x h
  rwa [lineMap_apply_zero, sub_zero] at this

private lemma dist_lm_right (A B : Plane) (x : ℝ) (h : x ≤ 1) :
    dist (lineMap A B x : Plane) B = (1 - x) * dist A B := by
  have := dist_lm A B x 1 h
  rwa [lineMap_apply_one] at this

private lemma cross_cycle (A B C : Plane) : cross B C A = cross A B C := by
  unfold cross; ring

private lemma ne_of_cross {A B C : Plane} (h : cross A B C ≠ 0) : B ≠ C := by
  rintro rfl; apply h; unfold cross; ring

private lemma sides_pos (A B C : Plane) (h : cross A B C ≠ 0) :
    0 < dist B C ∧ 0 < dist C A ∧ 0 < dist A B :=
  ⟨dist_pos.2 (ne_of_cross h), dist_pos.2 (ne_of_cross (by rwa [cross_cycle] : cross B C A ≠ 0)),
    dist_pos.2 (ne_of_cross (by rwa [cross_cycle, cross_cycle] : cross C A B ≠ 0))⟩

/-- **Problem 54.** If three triangles are cut off from `ABC` (sides `a = BC`, `b = CA`,
`c = AB`) by lines parallel to the sides so that the remaining hexagon `DGFJHE` is equilateral,
then each side of the hexagon is `1 / (1/a + 1/b + 1/c)`, and the sides of `ABC` are divided in
the ratios `AD : DG : GB = 1/a : 1/c : 1/b`, `BF : FJ : JC = 1/b : 1/a : 1/c`,
`CH : HE : EA = 1/c : 1/b : 1/a` (a ratio `x : y : z = 1/p : 1/q : 1/r` is written
`x·p = y·q = z·r`). -/
theorem problem54 (A B C D E F G H J : Plane) (hABC : cross A B C ≠ 0)
    (hcut : IsCut A B C D E F G H J) (heq : IsEquilateralHex D G F J H E) :
    (dist D G = 1 / (1 / dist B C + 1 / dist C A + 1 / dist A B) ∧
      dist G F = 1 / (1 / dist B C + 1 / dist C A + 1 / dist A B) ∧
      dist F J = 1 / (1 / dist B C + 1 / dist C A + 1 / dist A B) ∧
      dist J H = 1 / (1 / dist B C + 1 / dist C A + 1 / dist A B) ∧
      dist H E = 1 / (1 / dist B C + 1 / dist C A + 1 / dist A B) ∧
      dist E D = 1 / (1 / dist B C + 1 / dist C A + 1 / dist A B)) ∧
    (dist A D * dist B C = dist D G * dist A B ∧ dist D G * dist A B = dist G B * dist C A) ∧
    (dist B F * dist C A = dist F J * dist B C ∧ dist F J * dist B C = dist J C * dist A B) ∧
    (dist C H * dist A B = dist H E * dist C A ∧ dist H E * dist C A = dist E A * dist B C) := by
  obtain ⟨⟨d, g, d0, dg, g1, rfl, rfl⟩, ⟨f, j, f0, fj, j1, rfl, rfl⟩,
    ⟨h, e, h0, he, e1, rfl, rfl⟩, ⟨t1, ht1⟩, ⟨t2, ht2⟩, ⟨t3, ht3⟩⟩ := hcut
  -- the parallels fix the cut-off triangles: `e = 1 - d`, `f = 1 - g`, `h = 1 - j`
  have p1 := congrArg (· 0) ht1
  have q1 := congrArg (· 1) ht1
  have p2 := congrArg (· 0) ht2
  have q2 := congrArg (· 1) ht2
  have p3 := congrArg (· 0) ht3
  have q3 := congrArg (· 1) ht3
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, lineMap_apply'] at p1 q1 p2 q2 p3 q3
  obtain ⟨r1, r2⟩ := indep A B C hABC (t1 - d) (1 - e - t1) (by linear_combination p1)
    (by linear_combination q1)
  obtain ⟨r3, r4⟩ := indep A B C hABC (1 - f - g) (f + t2) (by linear_combination p2)
    (by linear_combination q2)
  obtain ⟨r5, r6⟩ := indep A B C hABC (-(1 - j) - t3) (1 - h - j) (by linear_combination p3)
    (by linear_combination q3)
  obtain ⟨ha, hb, hc⟩ := sides_pos A B C hABC
  -- the twelve lengths
  have sDG := dist_lm A B d g dg
  have sGF := dist_smul_eq _ _ _ _ _ ht2
  have sFJ := dist_lm B C f j fj
  have sJH := dist_smul_eq _ _ _ _ _ ht3
  have sHE := dist_lm C A h e he
  have sED : dist (lineMap C A e : Plane) (lineMap A B d) = |t1| * dist B C := by
    rw [dist_comm]; exact dist_smul_eq _ _ _ _ _ ht1
  have sAD := dist_lm_left A B d d0
  have sGB := dist_lm_right A B g g1
  have sBF := dist_lm_left B C f f0
  have sJC := dist_lm_right B C j j1
  have sCH := dist_lm_left C A h h0
  have sEA := dist_lm_right C A e e1
  rw [abs_of_nonpos (by linarith : t2 ≤ 0)] at sGF
  rw [abs_of_nonpos (by linarith : t3 ≤ 0)] at sJH
  rw [abs_of_nonneg (by linarith : 0 ≤ t1)] at sED
  obtain ⟨k1, k2, k3, k4, k5⟩ := heq
  rw [sDG, sGF] at k1
  rw [sGF, sFJ] at k2
  rw [sFJ, sJH] at k3
  rw [sJH, sHE] at k4
  rw [sHE, sED] at k5
  rw [sDG, sGF, sFJ, sJH, sHE, sED, sAD, sGB, sBF, sJC, sCH, sEA]
  set a := dist B C
  set b := dist C A
  set c := dist A B
  have ht1 : t1 = d := by linarith
  have he' : e = 1 - d := by linarith
  have ht2 : t2 = -f := by linarith
  have hg : g = 1 - f := by linarith
  have ht3 : t3 = -h := by linarith
  have hj : j = 1 - h := by linarith
  subst ht1 he' ht2 hg ht3 hj
  -- every side equals `ED = d·a`
  have E1 : f * b = t1 * a := by linear_combination k2 + k3 + k4 + k5
  have E3 : (1 - f - t1) * c = t1 * a := by linear_combination k1 + k2 + k3 + k4 + k5
  have E2 : h * c = t1 * a := by linear_combination k4 + k5
  -- `s (ab + bc + ca) = abc`, i.e. `s = 1 / (1/a + 1/b + 1/c)`
  have hs : t1 * a * (a * b + b * c + c * a) = a * b * c := by
    linear_combination (-(a * b)) * E3 - (a * c) * E1
  have hS : t1 * a = 1 / (1 / a + 1 / b + 1 / c) := by
    rw [div_add_div _ _ ha.ne' hb.ne', div_add_div _ _ (by positivity) hc.ne', one_div_div,
      eq_div_iff (by positivity)]
    linear_combination hs
  rw [← hS]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, rfl⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · linear_combination E3
  · linear_combination E1
  · linear_combination k3 + k4 + k5
  · linear_combination k4 + k5
  · linear_combination k5
  · linear_combination c * (-E3)
  · linear_combination c * (E3 - E1)
  · linear_combination a * E1 - a * (k3 + k4 + k5)
  · linear_combination a * (k3 + k4 + k5 - E2)
  · linear_combination b * E2 - b * k5
  · linear_combination b * k5
/-- **Problem 54 (the construction exists).** In every triangle the three parallels can be drawn so
that the remaining hexagon is equilateral (cut `AD = s/a · AB`, `BF = s/b · BC`, `CH = s/c · CA`
with `s = 1 / (1/a + 1/b + 1/c)`). -/
theorem problem54_exists (A B C : Plane) (hABC : cross A B C ≠ 0) :
    ∃ D E F G H J : Plane, IsCut A B C D E F G H J ∧ IsEquilateralHex D G F J H E := by
  obtain ⟨ha, hb, hc⟩ := sides_pos A B C hABC
  set a := dist B C with ha'
  set b := dist C A with hb'
  set c := dist A B with hc'
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 / (1 / a + 1 / b + 1 / c) := ⟨_, rfl⟩
  have sp : 0 < s := by rw [hs]; positivity
  have key : s / a + s / b + s / c = 1 := by rw [hs]; field_simp
  have x0 : 0 < s / a := div_pos sp ha
  have y0 : 0 < s / b := div_pos sp hb
  have z0 : 0 < s / c := div_pos sp hc
  refine ⟨lineMap A B (s / a), lineMap C A (1 - s / a), lineMap B C (s / b),
    lineMap A B (1 - s / b), lineMap C A (s / c), lineMap B C (1 - s / c),
    ⟨⟨s / a, 1 - s / b, x0.le, by linarith, by linarith, rfl, rfl⟩,
     ⟨s / b, 1 - s / c, y0.le, by linarith, by linarith, rfl, rfl⟩,
     ⟨s / c, 1 - s / a, z0.le, by linarith, by linarith, rfl, rfl⟩,
     ⟨s / a, ?_⟩, ⟨-(s / b), ?_⟩, ⟨-(s / c), ?_⟩⟩, ?_⟩
  · ext i; fin_cases i <;> simp [lineMap_apply'] <;> ring
  · ext i; fin_cases i <;> simp [lineMap_apply'] <;> ring
  · ext i; fin_cases i <;> simp [lineMap_apply'] <;> ring
  have sDG := dist_lm A B (s / a) (1 - s / b) (by linarith)
  have sFJ := dist_lm B C (s / b) (1 - s / c) (by linarith)
  have sHE := dist_lm C A (s / c) (1 - s / a) (by linarith)
  have sGF : dist (lineMap A B (1 - s / b) : Plane) (lineMap B C (s / b)) = s / b * b := by
    rw [dist_smul_eq (lineMap B C (s / b)) (lineMap A B (1 - s / b)) A C (-(s / b))
      (by ext i; fin_cases i <;> simp [lineMap_apply'] <;> ring), abs_neg, abs_of_pos y0]
  have sJH : dist (lineMap B C (1 - s / c) : Plane) (lineMap C A (s / c)) = s / c * c := by
    rw [dist_smul_eq (lineMap C A (s / c)) (lineMap B C (1 - s / c)) B A (-(s / c))
      (by ext i; fin_cases i <;> simp [lineMap_apply'] <;> ring), abs_neg, abs_of_pos z0]
  have sED : dist (lineMap C A (1 - s / a) : Plane) (lineMap A B (s / a)) = s / a * a := by
    rw [dist_comm, dist_smul_eq (lineMap C A (1 - s / a)) (lineMap A B (s / a)) C B (s / a)
      (by ext i; fin_cases i <;> simp [lineMap_apply'] <;> ring), abs_of_pos x0]
  have e1 : s / a * a = s := by field_simp
  have e2 : s / b * b = s := by field_simp
  have e3 : s / c * c = s := by field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sDG, sGF, e2]; linear_combination (-c) * key + e3
  · rw [sGF, sFJ, e2]; linear_combination a * key - e1
  · rw [sFJ, sJH, e3]; linear_combination (-a) * key + e1
  · rw [sJH, sHE, e3]; linear_combination b * key - e2
  · rw [sHE, sED, e1]; linear_combination (-b) * key + e2

end PillowProblems.P54
