import PillowProblems.Basic

/-!
# Problem 55 (Trigonometry: Plane)

**Question.** *(dated 20/12/74)*

> Given three cylindrical towers on a Plane: find a Point, on the Plane, from which they shall look the same width.

*(Carroll's solution: Chapter III, problem 55; text in `data/problems.json`.)*

**Lean reading.** The ground is the plane. The towers stand on circles with centres `A, B, C` and radii
`a, b, c > 0`. "Look the same width" is read as Carroll's solution reads it (`sin APD = a/AP`): the
apparent width of a tower seen from `P` is the angle between the two tangents from `P` to its base
circle. That angle is `angularWidth P O r = 2 arcsin (r / PO)`, and `angularWidth_eq_two_mul_angle`
checks it is twice the angle between a tangent `PT` and `PO`. The viewpoint must lie outside the
towers (`a < PA`, `b < PB`, `c < PC`), a tacit assumption. `problem55_ratio` is Carroll's first step:
equal widths `⇔ PA : PB : PC = a : b : c`. `problem55_locus` is his locus claim: if `G, H` are the
two points of line `AB` with `AG : GB = AH : HB = a : b`, the points with `PA : PB = a : b` form the
circle on `GH` as diameter. As his note says, it is a full circle, not a semicircle.
`problem55_locus_nonvacuous` shows such `G, H` exist. `problem55` combines these: a point outside
the towers sees them all the same width exactly when it lies on both circles. We add `a ≠ b`,
`b ≠ c`, `A ≠ B`, `B ≠ C` because Carroll's construction needs them: if `a = b` the external point
`H` does not exist, and the locus is the perpendicular bisector of `AB` (proved separately as
`problem55_locus_eq`, so that case is covered too; `problem55_ratio` needs no such hypothesis). Whether the two circles meet
outside the towers depends on the data, and Carroll does not discuss it.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P55

open scoped EuclideanGeometry
open AffineMap

/-- The (angular) width under which a tower standing on the circle with centre `O` and radius `r`
is seen from a point `P` of the plane outside it: the angle between the two tangents from `P` to the
circle, `2 · arcsin (r / PO)` (see `angularWidth_eq_two_mul_angle`). -/
noncomputable def angularWidth (P O : Plane) (r : ℝ) : ℝ := 2 * Real.arcsin (r / dist P O)

/-- The definition of `angularWidth` is the geometric one: if `PT` touches the circle at `T`
(`OT = r`, `OT ⊥ PT`), the width is twice the angle `OPT` between the tangent and the line to the
centre. -/
theorem angularWidth_eq_two_mul_angle (P O T : Plane) (r : ℝ) (hr : 0 < r) (hT : dist T O = r)
    (htan : ∠ O T P = Real.pi / 2) : angularWidth P O r = 2 * ∠ O P T := by
  have hOT : O ≠ T := by
    intro h; rw [h, dist_self] at hT; exact hr.ne hT
  have hsin := EuclideanGeometry.sin_angle_of_angle_eq_pi_div_two htan (Or.inl hOT)
  have hle := EuclideanGeometry.angle_le_pi_div_two_of_angle_eq_pi_div_two htan
  rw [EuclideanGeometry.angle_comm] at hsin hle
  unfold angularWidth
  rw [dist_comm O T, hT, dist_comm O P] at hsin
  rw [← hsin, Real.arcsin_sin (by linarith [EuclideanGeometry.angle_nonneg O P T,
    Real.pi_pos]) hle]

/-- **Problem 55 (the condition).** Seen from a point `P` outside the three towers (centres
`A, B, C`, radii `a, b, c`), the towers look the same width exactly when
`PA : PB : PC = a : b : c`. -/
theorem problem55_ratio (A B C P : Plane) (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hPA : a < dist P A) (hPB : b < dist P B) (hPC : c < dist P C) :
    (angularWidth P A a = angularWidth P B b ∧ angularWidth P B b = angularWidth P C c) ↔
      (dist P A * b = dist P B * a ∧ dist P B * c = dist P C * b) := by
  have pA : 0 < dist P A := ha.trans hPA
  have pB : 0 < dist P B := hb.trans hPB
  have pC : 0 < dist P C := hc.trans hPC
  have iA : -1 ≤ a / dist P A ∧ a / dist P A ≤ 1 :=
    ⟨by have : 0 ≤ a / dist P A := by positivity
        linarith, (div_le_one pA).2 hPA.le⟩
  have iB : -1 ≤ b / dist P B ∧ b / dist P B ≤ 1 :=
    ⟨by have : 0 ≤ b / dist P B := by positivity
        linarith, (div_le_one pB).2 hPB.le⟩
  have iC : -1 ≤ c / dist P C ∧ c / dist P C ≤ 1 :=
    ⟨by have : 0 ≤ c / dist P C := by positivity
        linarith, (div_le_one pC).2 hPC.le⟩
  unfold angularWidth
  rw [mul_right_inj' two_ne_zero, mul_right_inj' two_ne_zero,
    Real.arcsin_inj iA.1 iA.2 iB.1 iB.2, Real.arcsin_inj iB.1 iB.2 iC.1 iC.2,
    div_eq_div_iff pA.ne' pB.ne', div_eq_div_iff pB.ne' pC.ne']
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

private lemma dist_sq (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma lineMap_apply' (A B : Plane) (t : ℝ) (i : Fin 2) :
    (lineMap A B t : Plane) i = A i + t * (B i - A i) := by
  simp [AffineMap.lineMap_apply]; ring

private lemma midpoint_apply' (x y : Plane) (i : Fin 2) :
    (midpoint ℝ x y : Plane) i = (x i + y i) / 2 := by
  rw [midpoint_eq_smul_add]; simp; ring

/-- The circle of Apollonius, with the two division points written explicitly. -/
private lemma apollonius (A B P : Plane) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    dist P A * b = dist P B * a ↔
      dist P (midpoint ℝ (lineMap A B (a / (a + b))) (lineMap A B (a / (a - b)))) =
        dist (lineMap A B (a / (a + b)) : Plane) (lineMap A B (a / (a - b))) / 2 := by
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  have hab'' : a + b ≠ 0 := by positivity
  have hba : b ^ 2 - a ^ 2 ≠ 0 := by
    intro h
    have : (b - a) * (b + a) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · exact hab (by linarith)
    · linarith
  -- `b²·PA² - a²·PB² = (b² - a²) (PM² - (GH/2)²)`
  have key : (dist P A * b) ^ 2 - (dist P B * a) ^ 2 = (b ^ 2 - a ^ 2) *
      (dist P (midpoint ℝ (lineMap A B (a / (a + b))) (lineMap A B (a / (a - b)))) ^ 2 -
        (dist (lineMap A B (a / (a + b)) : Plane) (lineMap A B (a / (a - b))) / 2) ^ 2) := by
    rw [mul_pow, mul_pow, div_pow, dist_sq, dist_sq, dist_sq, dist_sq]
    simp only [midpoint_apply', lineMap_apply']
    field_simp
    ring
  rw [← sq_eq_sq₀ (by positivity) (by positivity),
    ← sq_eq_sq₀ dist_nonneg (by positivity), ← sub_eq_zero, key, mul_eq_zero, or_iff_right hba,
    sub_eq_zero]

/-- The two points dividing `AB` (internally and externally) in the ratio `a : b`. -/
private lemma division_points (A B : Plane) (a b g : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hAB : A ≠ B) (h : dist A (lineMap A B g : Plane) * b = dist (lineMap A B g : Plane) B * a) :
    g = a / (a + b) ∨ g = a / (a - b) := by
  rw [dist_left_lineMap, dist_lineMap_right, Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hd : 0 < dist A B := dist_pos.2 hAB
  have h' : |g| * b = |1 - g| * a := by
    have := congrArg (· / dist A B) h
    field_simp at this
    linarith
  have h2 : (g * b) ^ 2 = ((1 - g) * a) ^ 2 := by
    rw [mul_pow, mul_pow, ← sq_abs g, ← sq_abs (1 - g), ← mul_pow, ← mul_pow, h']
  have : (g * (a + b) - a) * (g * (a - b) - a) = 0 := by linear_combination -h2
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  rcases mul_eq_zero.1 this with h | h
  · left; field_simp; linarith
  · right; field_simp; linarith

/-- **Problem 55 (Carroll's locus).** If `a ≠ b` and `G, H` are the two points of the line `AB`
with `AG : GB = AH : HB = a : b`, then the points `P` with `PA : PB = a : b` are exactly the
circle on the diameter `GH`. -/
theorem problem55_locus (A B G H : Plane) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hAB : A ≠ B) (hG : ∃ g : ℝ, G = lineMap A B g) (hH : ∃ h : ℝ, H = lineMap A B h)
    (hGH : G ≠ H) (rG : dist A G * b = dist G B * a) (rH : dist A H * b = dist H B * a) :
    {P : Plane | dist P A * b = dist P B * a} = Metric.sphere (midpoint ℝ G H) (dist G H / 2) := by
  obtain ⟨g, rfl⟩ := hG
  obtain ⟨h, rfl⟩ := hH
  have cg := division_points A B a b g ha hb hab hAB rG
  have ch := division_points A B a b h ha hb hab hAB rH
  ext P
  simp only [Set.mem_ofPred_eq, Metric.mem_sphere]
  rcases cg with rfl | rfl <;> rcases ch with rfl | rfl
  · exact absurd rfl hGH
  · exact apollonius A B P a b ha hb hab
  · rw [midpoint_comm, dist_comm (lineMap A B (a / (a - b)) : Plane)]
    exact apollonius A B P a b ha hb hab
  · exact absurd rfl hGH

/-- The points `G, H` of Carroll's construction exist (so `problem55_locus` is not vacuous). -/
theorem problem55_locus_nonvacuous (A B : Plane) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (hAB : A ≠ B) :
    ∃ G H : Plane, (∃ g : ℝ, G = lineMap A B g) ∧ (∃ h : ℝ, H = lineMap A B h) ∧ G ≠ H ∧
      dist A G * b = dist G B * a ∧ dist A H * b = dist H B * a := by
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  have hab'' : a + b ≠ 0 := by positivity
  have e1 : 1 - a / (a + b) = b / (a + b) := by
    rw [one_sub_div hab'', add_sub_cancel_left]
  refine ⟨lineMap A B (a / (a + b)), lineMap A B (a / (a - b)), ⟨_, rfl⟩, ⟨_, rfl⟩, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun X : Plane => dist A X) h
    simp only [dist_left_lineMap, Real.norm_eq_abs] at this
    have hd : 0 < dist A B := dist_pos.2 hAB
    have e : |a / (a + b)| = |a / (a - b)| := mul_right_cancel₀ hd.ne' this
    rcases abs_eq_abs.1 e with e | e
    · field_simp at e; exact hab (by linarith)
    · field_simp at e; linarith
  · rw [dist_left_lineMap, dist_lineMap_right, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < a / (a + b)),
      e1, abs_of_pos (by positivity : 0 < b / (a + b))]
    field_simp
  · rw [dist_left_lineMap, dist_lineMap_right, Real.norm_eq_abs, Real.norm_eq_abs,
      one_sub_div hab', abs_div, abs_div, abs_of_pos ha]
    have : a - b - a = -b := by ring
    rw [this, abs_neg, abs_of_pos hb]
    field_simp

/-- **Problem 55 (the case `a = b`).** When two towers have equal radii, Carroll's external point
`H` does not exist and the locus `PA : PB = a : b` is the perpendicular bisector of `AB`. -/
theorem problem55_locus_eq (A B : Plane) (a : ℝ) (ha : 0 < a) :
    {P : Plane | dist P A * a = dist P B * a} = (AffineSubspace.perpBisector A B : Set Plane) := by
  ext P
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, AffineSubspace.mem_perpBisector_iff_dist_eq]
  exact mul_left_inj' ha.ne'

/-- **Problem 55.** Let the towers have centres `A, B, C` and radii `a, b, c`, with `a ≠ b ≠ c`
and `A ≠ B ≠ C`; let `G, H` divide `AB` internally and externally as `a : b`, and `G', H'` divide
`BC` as `b : c`. A point `P` of the plane, outside the towers, sees them all of the same width
exactly when it lies on both circles described on `GH` and on `G'H'` as diameters. -/
theorem problem55 (A B C : Plane) (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≠ b) (hbc : b ≠ c) (hAB : A ≠ B) (hBC : B ≠ C)
    (G H G' H' : Plane) (hG : ∃ g : ℝ, G = lineMap A B g) (hH : ∃ h : ℝ, H = lineMap A B h)
    (hGH : G ≠ H) (rG : dist A G * b = dist G B * a) (rH : dist A H * b = dist H B * a)
    (hG' : ∃ g : ℝ, G' = lineMap B C g) (hH' : ∃ h : ℝ, H' = lineMap B C h)
    (hGH' : G' ≠ H') (rG' : dist B G' * c = dist G' C * b) (rH' : dist B H' * c = dist H' C * b)
    (P : Plane) (hPA : a < dist P A) (hPB : b < dist P B) (hPC : c < dist P C) :
    (angularWidth P A a = angularWidth P B b ∧ angularWidth P B b = angularWidth P C c) ↔
      (dist P (midpoint ℝ G H) = dist G H / 2 ∧ dist P (midpoint ℝ G' H') = dist G' H' / 2) := by
  rw [problem55_ratio A B C P a b c ha hb hc hPA hPB hPC]
  have l1 := problem55_locus A B G H a b ha hb hab hAB hG hH hGH rG rH
  have l2 := problem55_locus B C G' H' b c hb hc hbc hBC hG' hH' hGH' rG' rH'
  have m1 := Set.ext_iff.1 l1 P
  have m2 := Set.ext_iff.1 l2 P
  simp only [Set.mem_ofPred_eq, Metric.mem_sphere] at m1 m2
  rw [m1, m2]

end PillowProblems.P55
