import PillowProblems.Basic

/-!
# Problem 48 (Trigonometry: Plane)

**Question.** *(dated 9/2/81)*

> If semicircles be described, externally, on the sides of a given Triangle; and if their common tangents be drawn; and if their lengths be \(\alpha\), \(\beta\), \(\gamma\): prove that \[ (\frac{\beta\gamma}{\alpha} + \frac{\gamma\alpha}{\beta} + \frac{\alpha\beta}{\gamma}) \] is equal to the semiperimeter of the Triangle.

*(Carroll's solution: Chapter III, problem 48; text in `data/problems.json`.)*

**Lean reading.** The triangle is `A, B, C` with `cross A B C ≠ 0` (non-degenerate). The semicircle on a side `XY`
lies on the circle with centre `midpoint ℝ X Y` and radius `XY/2`. Like Carroll's solution, we work
with these full circles. `IsCommonTangent O₁ r₁ O₂ r₂ D E` says `DE` is a segment of a common
direct tangent between its points of contact: `D` and `E` are on the circles, `DE` is perpendicular
to both radii, and the radii point the same way. Two of the circles meet (at a vertex), so their
only common tangents are the two direct ones. We prove the identity for every such tangent
segment (`DE² = O₁O₂² - (r₁ - r₂)²`, the same for both), so the one touching the outer arcs is
covered whichever it is. `α`, `β`, `γ` are the tangents of the semicircles on `CA, AB`; `AB, BC`;
`BC, CA`. The expression is symmetric, so this labelling does not matter. `problem48_exists` shows
the tangents exist for every triangle, so the hypotheses of `problem48` can be met.

**Status.** proved
-/

namespace PillowProblems.P48

/-- `DE` is a segment of a common (direct) tangent of the circles with centres `O₁, O₂` and radii
`r₁, r₂`, between its points of contact: `D` is on the first circle, `E` on the second, `DE` is
perpendicular to both radii `O₁D`, `O₂E`, and these radii point the same way (the two circles lie on
the same side of the tangent line). -/
def IsCommonTangent (O₁ : Plane) (r₁ : ℝ) (O₂ : Plane) (r₂ : ℝ) (D E : Plane) : Prop :=
  dist D O₁ = r₁ ∧ dist E O₂ = r₂ ∧ inner ℝ (D - O₁) (E - D) = 0 ∧
    inner ℝ (E - O₂) (E - D) = 0 ∧ r₂ • (D - O₁) = r₁ • (E - O₂)

private lemma inner_eq (x y : Plane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

private lemma dist_sq (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma midpoint_apply' (x y : Plane) (i : Fin 2) :
    (midpoint ℝ x y : Plane) i = (x i + y i) / 2 := by
  rw [midpoint_eq_smul_add]; simp; ring

private lemma cross_cycle (A B C : Plane) : cross B C A = cross A B C := by
  unfold cross; ring

private lemma heron (A B C : Plane) :
    4 * cross A B C ^ 2 = (dist B C + dist C A + dist A B) * (-dist B C + dist C A + dist A B) *
      (dist B C - dist C A + dist A B) * (dist B C + dist C A - dist A B) := by
  have e : ∀ a b c : ℝ, (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) =
      2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 - (a ^ 2) ^ 2 - (b ^ 2) ^ 2 -
        (c ^ 2) ^ 2 := by intros; ring
  rw [e, dist_sq, dist_sq, dist_sq]
  unfold cross; ring

private lemma tri_strict (A B C : Plane) (h : cross A B C ≠ 0) :
    dist B C < dist C A + dist A B := by
  have h1 : dist B C ≤ dist C A + dist A B := by
    have := dist_triangle B A C
    rw [dist_comm B A, dist_comm A C] at this; linarith
  refine lt_of_le_of_ne h1 fun heq => h ?_
  have := heron A B C
  have h0 : (-dist B C + dist C A + dist A B) = 0 := by linarith
  rw [h0] at this
  have : cross A B C ^ 2 = 0 := by linarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

private lemma ne_of_cross {A B C : Plane} (h : cross A B C ≠ 0) : B ≠ C := by
  rintro rfl; apply h; unfold cross; ring

private lemma sides_pos (A B C : Plane) (h : cross A B C ≠ 0) :
    0 < dist B C ∧ 0 < dist C A ∧ 0 < dist A B :=
  ⟨dist_pos.2 (ne_of_cross h), dist_pos.2 (ne_of_cross (by rwa [cross_cycle] : cross B C A ≠ 0)),
    dist_pos.2 (ne_of_cross (by rwa [cross_cycle, cross_cycle] : cross C A B ≠ 0))⟩

/-- The length of a common direct tangent: `DE² = O₁O₂² - (r₁ - r₂)²`. -/
private lemma tangent_sq (O₁ : Plane) (r₁ : ℝ) (O₂ : Plane) (r₂ : ℝ) (D E : Plane)
    (hr : 0 < r₁) (h : IsCommonTangent O₁ r₁ O₂ r₂ D E) :
    dist D E ^ 2 = dist O₁ O₂ ^ 2 - (r₁ - r₂) ^ 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e0 := congrArg (· 0) h5
  have e1 := congrArg (· 1) h5
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at e0 e1
  have q1 : dist D O₁ ^ 2 = r₁ ^ 2 := by rw [h1]
  have q2 : dist E O₂ ^ 2 = r₂ ^ 2 := by rw [h2]
  rw [dist_sq] at q1 q2 ⊢
  rw [dist_sq]
  rw [inner_eq] at h3 h4
  simp only [PiLp.sub_apply] at h3 h4
  have hpq : (D 0 - O₁ 0) * (E 0 - O₂ 0) + (D 1 - O₁ 1) * (E 1 - O₂ 1) = r₁ * r₂ := by
    apply mul_left_cancel₀ hr.ne'
    linear_combination -((D 0 - O₁ 0) * e0 + (D 1 - O₁ 1) * e1) + r₂ * q1
  linear_combination (-1) * q1 + (-1) * q2 + (-2) * h3 + 2 * hpq + 2 * h4

/-- A unit vector `u` with `u · d = k`, when `k² < |d|²`. -/
private lemma unit_vec (d0 d1 k : ℝ) (h : k ^ 2 < d0 ^ 2 + d1 ^ 2) :
    ∃ u0 u1 : ℝ, u0 ^ 2 + u1 ^ 2 = 1 ∧ u0 * d0 + u1 * d1 = k := by
  have hNp : 0 < d0 ^ 2 + d1 ^ 2 := by nlinarith
  have ss : Real.sqrt (d0 ^ 2 + d1 ^ 2 - k ^ 2) ^ 2 = d0 ^ 2 + d1 ^ 2 - k ^ 2 :=
    Real.sq_sqrt (by linarith)
  refine ⟨(k * d0 - Real.sqrt (d0 ^ 2 + d1 ^ 2 - k ^ 2) * d1) / (d0 ^ 2 + d1 ^ 2),
    (k * d1 + Real.sqrt (d0 ^ 2 + d1 ^ 2 - k ^ 2) * d0) / (d0 ^ 2 + d1 ^ 2), ?_, ?_⟩
  · rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (by positivity)]
    linear_combination (d0 ^ 2 + d1 ^ 2) * ss
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hNp.ne']
    ring

/-- Two circles whose centres are further apart than the difference of the radii have a common
direct tangent. -/
private lemma tangent_exists (O₁ : Plane) (r₁ : ℝ) (O₂ : Plane) (r₂ : ℝ)
    (h : (r₁ - r₂) ^ 2 < dist O₁ O₂ ^ 2) (h1 : 0 ≤ r₁) (h2 : 0 ≤ r₂) :
    ∃ D E, IsCommonTangent O₁ r₁ O₂ r₂ D E := by
  rw [dist_sq] at h
  obtain ⟨u0, u1, hu, hud⟩ := unit_vec (O₂ 0 - O₁ 0) (O₂ 1 - O₁ 1) (r₁ - r₂)
    (by nlinarith)
  refine ⟨pt (O₁ 0 + r₁ * u0) (O₁ 1 + r₁ * u1), pt (O₂ 0 + r₂ * u0) (O₂ 1 + r₂ * u1),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← sq_eq_sq₀ dist_nonneg h1, dist_sq]; simp only [pt_zero, pt_one]
    linear_combination r₁ ^ 2 * hu
  · rw [← sq_eq_sq₀ dist_nonneg h2, dist_sq]; simp only [pt_zero, pt_one]
    linear_combination r₂ ^ 2 * hu
  · rw [inner_eq]; simp only [PiLp.sub_apply, pt_zero, pt_one]
    linear_combination r₁ * hud - r₁ * (r₁ - r₂) * hu
  · rw [inner_eq]; simp only [PiLp.sub_apply, pt_zero, pt_one]
    linear_combination r₂ * hud - r₂ * (r₁ - r₂) * hu
  · ext i; fin_cases i <;> simp <;> ring

private lemma mid_dist (X Y Z : Plane) :
    dist (midpoint ℝ Z X) (midpoint ℝ X Y) = dist Y Z / 2 := by
  rw [← sq_eq_sq₀ dist_nonneg (by positivity), div_pow, dist_sq, dist_sq,
    midpoint_apply', midpoint_apply', midpoint_apply', midpoint_apply']
  ring

/-- **Problem 48 (the tangents exist).** For any triangle, each two of the semicircles on its
sides have a common tangent. -/
theorem problem48_exists (A B C : Plane) (hABC : cross A B C ≠ 0) :
    (∃ D E, IsCommonTangent (midpoint ℝ C A) (dist C A / 2) (midpoint ℝ A B) (dist A B / 2) D E) ∧
    (∃ F G, IsCommonTangent (midpoint ℝ A B) (dist A B / 2) (midpoint ℝ B C) (dist B C / 2) F G) ∧
    (∃ H J, IsCommonTangent (midpoint ℝ B C) (dist B C / 2) (midpoint ℝ C A) (dist C A / 2) H J) := by
  have t1 := tri_strict A B C hABC
  have t2 := tri_strict B C A (by rwa [cross_cycle])
  have t3 := tri_strict C A B (by rwa [cross_cycle, cross_cycle])
  have a0 := dist_nonneg (x := B) (y := C)
  have b0 := dist_nonneg (x := C) (y := A)
  have c0 := dist_nonneg (x := A) (y := B)
  refine ⟨tangent_exists _ _ _ _ ?_ (by positivity) (by positivity),
    tangent_exists _ _ _ _ ?_ (by positivity) (by positivity),
    tangent_exists _ _ _ _ ?_ (by positivity) (by positivity)⟩
  · rw [mid_dist]; nlinarith
  · rw [mid_dist]; nlinarith
  · rw [mid_dist]; nlinarith

/-- **Problem 48.** If `α, β, γ` are the lengths of the common tangents of the semicircles on the
sides `CA, AB`, `AB, BC`, `BC, CA` (between the points of contact), then
`βγ/α + γα/β + αβ/γ` is the semiperimeter of `ABC`. -/
theorem problem48 (A B C : Plane) (hABC : cross A B C ≠ 0) (D E F G H J : Plane)
    (hα : IsCommonTangent (midpoint ℝ C A) (dist C A / 2) (midpoint ℝ A B) (dist A B / 2) D E)
    (hβ : IsCommonTangent (midpoint ℝ A B) (dist A B / 2) (midpoint ℝ B C) (dist B C / 2) F G)
    (hγ : IsCommonTangent (midpoint ℝ B C) (dist B C / 2) (midpoint ℝ C A) (dist C A / 2) H J) :
    dist F G * dist H J / dist D E + dist H J * dist D E / dist F G +
      dist D E * dist F G / dist H J = (dist B C + dist C A + dist A B) / 2 := by
  have t1 := tri_strict A B C hABC
  have t2 := tri_strict B C A (by rwa [cross_cycle])
  have t3 := tri_strict C A B (by rwa [cross_cycle, cross_cycle])
  obtain ⟨ha, hb, hc⟩ := sides_pos A B C hABC
  have sα := tangent_sq _ _ _ _ _ _ (by positivity) hα
  have sβ := tangent_sq _ _ _ _ _ _ (by positivity) hβ
  have sγ := tangent_sq _ _ _ _ _ _ (by positivity) hγ
  rw [mid_dist] at sα sβ sγ
  set a := dist B C
  set b := dist C A
  set c := dist A B
  set α := dist D E
  set β := dist F G
  set γ := dist H J
  have p : 0 < -a + b + c := by linarith
  have q : 0 < a - b + c := by linarith
  have r : 0 < a + b - c := by linarith
  have α4 : 4 * α ^ 2 = (a - b + c) * (a + b - c) := by rw [sα]; ring
  have β4 : 4 * β ^ 2 = (a + b - c) * (-a + b + c) := by rw [sβ]; ring
  have γ4 : 4 * γ ^ 2 = (-a + b + c) * (a - b + c) := by rw [sγ]; ring
  have α0 : 0 < α := by
    have : 0 < α ^ 2 := by nlinarith
    exact lt_of_le_of_ne dist_nonneg (fun h => by rw [← h] at this; simp at this)
  have β0 : 0 < β := by
    have : 0 < β ^ 2 := by nlinarith
    exact lt_of_le_of_ne dist_nonneg (fun h => by rw [← h] at this; simp at this)
  have γ0 : 0 < γ := by
    have : 0 < γ ^ 2 := by nlinarith
    exact lt_of_le_of_ne dist_nonneg (fun h => by rw [← h] at this; simp at this)
  have e1 : β * γ = (-a + b + c) / 2 * α := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity)]
    have : 16 * (β * γ) ^ 2 = 16 * ((-a + b + c) / 2 * α) ^ 2 := by
      linear_combination (4 * γ ^ 2) * β4 + ((a + b - c) * (-a + b + c)) * γ4 -
        (-a + b + c) ^ 2 * α4
    linarith
  have e2 : γ * α = (a - b + c) / 2 * β := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity)]
    have : 16 * (γ * α) ^ 2 = 16 * ((a - b + c) / 2 * β) ^ 2 := by
      linear_combination (4 * α ^ 2) * γ4 + ((-a + b + c) * (a - b + c)) * α4 -
        (a - b + c) ^ 2 * β4
    linarith
  have e3 : α * β = (a + b - c) / 2 * γ := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity)]
    have : 16 * (α * β) ^ 2 = 16 * ((a + b - c) / 2 * γ) ^ 2 := by
      linear_combination (4 * β ^ 2) * α4 + ((a - b + c) * (a + b - c)) * β4 -
        (a + b - c) ^ 2 * γ4
    linarith
  rw [e1, e2, e3]
  field_simp
  ring

end PillowProblems.P48
