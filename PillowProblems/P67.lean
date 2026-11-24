import PillowProblems.Basic

/-!
# Problem 67 (Algebraical Geometry: Solid)

**Question.** *(dated 27/1/72)*

> If a regular Tetrahedron be placed, with one vertex downwards, in a socket which exactly fits it, and be turned round its vertical axis, through an angle of 120°, raising it only so much as is necessary, until it again fits the socket: find the Locus of one of the revolving vertices.

**Answer.**

> If the centre of the horizontal facet be taken as the Origin, and if the \(X\)-axis pass through one of the vertices of that facet, and the \(Y\)-axis be parallel to the opposite edge of that facet, and the \(Z\)-axis be perpendicular to that facet: and if the altitude (measured downwards) of the Tetrahedron be called '\(h\)', and the intercept on the \(X\)-axis be called '\(a\)': the Equations to the Locus are \[ \begin{aligned} (x+\sqrt{3}.y).(h-z) &= ah; \\ x^{2} + y^{2} &= a^{2}. \end{aligned} \]

*(Carroll's solution: Chapter III, problem 67; text in `data/problems.json`.)*

**Lean reading.** Co-ordinates are Carroll's: origin at the centre of the horizontal (top)
facet `ABC`, `A = (a, 0, 0)` on the `X`-axis, `BC` parallel to the `Y`-axis, `Z` vertical and
upward, and the lowest vertex `D = (0, 0, -h)`. The tetrahedron is the convex hull `solid a h` of
its four vertices, and the socket's hollow is the region it occupies at the start. Turning it
through `θ` about the vertical axis and raising it by `ζ` is `move θ ζ`, and it fits the socket
(`Fits`) when every point of it at or below the rim plane `z = 0` lies in the hollow, so that it
does not cut into the socket. "Raising it only so much as is necessary" is the least such `ζ`
(`IsLeast`), for each `θ` from `0` to `120°`. The turn is taken in the sense carrying `A` towards
`C = (-a/2, √3 a/2, 0)`, the sense in which Carroll's `+√3 y` is right (the other sense gives the
mirror image `x - √3 y`). The theorem determines the locus exactly. It is the set of points that
satisfy Carroll's two equations and also `y ≥ 0` and `√3 x + y ≥ 0`. These two inequalities cut
out the arc actually traced, from `A` to `C`, because the two surfaces also meet elsewhere. The
result holds for every `a, h > 0`, not only for the regular tetrahedron (`h = √2 a`), so that
hypothesis is dropped. As Carroll notes, the vertical axis of the tetrahedron stays on the
`Z`-axis. This is built into the motion, which the problem describes as a turn about the
vertical axis together with a raise.

**Status.** proved
-/

namespace PillowProblems.P67

open Real

/-- The vertex `A` of the horizontal facet, on the `X`-axis at distance `a` from its centre. -/
noncomputable def vA (a : ℝ) : Space := !₂[a, 0, 0]

/-- The vertex `B` of the horizontal facet. -/
noncomputable def vB (a : ℝ) : Space := !₂[-a / 2, -(√3 / 2 * a), 0]

/-- The vertex `C` of the horizontal facet; the edge `BC` is parallel to the `Y`-axis. -/
noncomputable def vC (a : ℝ) : Space := !₂[-a / 2, √3 / 2 * a, 0]

/-- The lowest vertex `D`, at depth `h` below the centre of the horizontal facet. -/
noncomputable def vD (h : ℝ) : Space := !₂[0, 0, -h]

/-- The solid tetrahedron in its initial position; it is also the hollow of the socket. -/
noncomputable def solid (a h : ℝ) : Set Space := convexHull ℝ {vA a, vB a, vC a, vD h}

/-- The rigid motion: turn through the angle `θ` about the vertical (`Z`) axis and raise by `ζ`. -/
noncomputable def move (θ ζ : ℝ) (p : Space) : Space :=
  !₂[cos θ * p 0 - sin θ * p 1, sin θ * p 0 + cos θ * p 1, p 2 + ζ]

/-- The tetrahedron, turned through `θ` and raised by `ζ`, fits the socket: every point of it lying
at or below the rim plane `z = 0` lies in the hollow, i.e. it does not cut into the socket. -/
def Fits (a h θ ζ : ℝ) : Prop :=
  ∀ p ∈ solid a h, (move θ ζ p) 2 ≤ 0 → move θ ζ p ∈ solid a h

/-- The positions of the revolving vertex `A` while the tetrahedron is turned through `θ`, from
`0` to `120°`, raised only so much as is necessary (the least height `ζ` at which it fits). -/
def locus (a h : ℝ) : Set Space :=
  {q | ∃ θ ∈ Set.Icc 0 (2 * π / 3), ∃ ζ, IsLeast {ζ' | Fits a h θ ζ'} ζ ∧ q = move θ ζ (vA a)}

@[simp] private lemma v3_0 (x y z : ℝ) : (!₂[x, y, z] : Space) 0 = x := rfl
@[simp] private lemma v3_1 (x y z : ℝ) : (!₂[x, y, z] : Space) 1 = y := rfl
@[simp] private lemma v3_2 (x y z : ℝ) : (!₂[x, y, z] : Space) 2 = z := rfl

@[simp] private lemma vA_0 (a : ℝ) : vA a 0 = a := rfl
@[simp] private lemma vA_1 (a : ℝ) : vA a 1 = 0 := rfl
@[simp] private lemma vA_2 (a : ℝ) : vA a 2 = 0 := rfl
@[simp] private lemma move_0 (θ ζ : ℝ) (p : Space) :
    move θ ζ p 0 = cos θ * p 0 - sin θ * p 1 := rfl
@[simp] private lemma move_1 (θ ζ : ℝ) (p : Space) :
    move θ ζ p 1 = sin θ * p 0 + cos θ * p 1 := rfl
@[simp] private lemma move_2 (θ ζ : ℝ) (p : Space) : move θ ζ p 2 = p 2 + ζ := rfl

private lemma space_ext {p q : Space} (h0 : p 0 = q 0) (h1 : p 1 = q 1) (h2 : p 2 = q 2) :
    p = q := by
  ext i; fin_cases i
  · exact h0
  · exact h1
  · exact h2

private lemma s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- The solid tetrahedron as an intersection of four half-spaces. -/
private lemma mem_solid {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (p : Space) :
    p ∈ solid a h ↔ p 2 ≤ 0 ∧ -2 * h * p 0 ≤ a * (h + p 2) ∧
      h * (p 0 + √3 * p 1) ≤ a * (h + p 2) ∧ h * (p 0 - √3 * p 1) ≤ a * (h + p 2) := by
  have hs := s3
  constructor
  · intro hp
    refine (convexHull_min ?_ ?_ : solid a h ⊆ {p : Space | p 2 ≤ 0 ∧ -2 * h * p 0 ≤ a * (h + p 2) ∧
      h * (p 0 + √3 * p 1) ≤ a * (h + p 2) ∧ h * (p 0 - √3 * p 1) ≤ a * (h + p 2)}) hp
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      have hah := mul_pos ha hh
      have e : √3 * (√3 / 2 * a) = 3 / 2 * a := by linear_combination (a / 2) * hs
      show _ ∧ _
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [vA, vB, vC, vD, v3_0, v3_1, v3_2] <;>
        refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
    · intro x hx y hy u v hu hv huv
      obtain rfl : v = 1 - u := by linarith
      simp only [Set.mem_ofPred_eq] at hx hy ⊢
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      obtain ⟨x1, x2, x3, x4⟩ := hx
      obtain ⟨y1, y2, y3, y4⟩ := hy
      refine ⟨by linarith [mul_le_mul_of_nonneg_left x1 hu, mul_le_mul_of_nonneg_left y1 hv],
        by linarith [mul_le_mul_of_nonneg_left x2 hu, mul_le_mul_of_nonneg_left y2 hv],
        by linarith [mul_le_mul_of_nonneg_left x3 hu, mul_le_mul_of_nonneg_left y3 hv],
        by linarith [mul_le_mul_of_nonneg_left x4 hu, mul_le_mul_of_nonneg_left y4 hv]⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hah : 0 < 3 * a * h := by positivity
    have hmem := (convex_convexHull ℝ ({vA a, vB a, vC a, vD h} : Set Space)).sum_mem
      (t := Finset.univ)
      (w := ![(2 * h * p 0 + a * (h + p 2)) / (3 * a * h),
        (a * (h + p 2) - h * (p 0 + √3 * p 1)) / (3 * a * h),
        (a * (h + p 2) - h * (p 0 - √3 * p 1)) / (3 * a * h), -p 2 / h])
      (z := ![vA a, vB a, vC a, vD h])
      (by
        intro i _
        fin_cases i
        · exact div_nonneg (by linarith) hah.le
        · exact div_nonneg (by linarith) hah.le
        · exact div_nonneg (by linarith) hah.le
        · exact div_nonneg (by linarith) hh.le)
      (by
        simp [Fin.sum_univ_four]
        field_simp
        ring)
      (by
        intro i _
        fin_cases i <;> exact subset_convexHull ℝ _ (by simp))
    rw [solid]
    convert hmem using 1
    ext j
    fin_cases j
    · simp [Fin.sum_univ_four, vA, vB, vC, vD]
      field_simp
      ring
    · simp [Fin.sum_univ_four, vA, vB, vC, vD]
      field_simp
      linear_combination (-(2 * h * p 1)) * hs
    · simp [Fin.sum_univ_four, vA, vB, vC, vD]
      field_simp

/-- Trigonometric facts on the range `0 ≤ θ ≤ 120°`; `k = cos θ + √3 sin θ = 2 cos (θ - 60°)`. -/
private lemma trig {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (2 * π / 3)) :
    0 ≤ sin θ ∧ 0 ≤ √3 * cos θ + sin θ ∧ 1 ≤ cos θ + √3 * sin θ := by
  obtain ⟨h0, h1⟩ := hθ
  have hpi := Real.pi_pos
  refine ⟨Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith), ?_, ?_⟩
  · have h := Real.sin_nonneg_of_nonneg_of_le_pi (x := θ + π / 3) (by linarith) (by linarith)
    rw [Real.sin_add, Real.cos_pi_div_three, Real.sin_pi_div_three] at h
    linarith
  · have h : cos (π / 3) ≤ cos |θ - π / 3| :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith)
        (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [Real.cos_abs, Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three] at h
    linarith

private lemma move_coords (θ ζ : ℝ) (p : Space) :
    move θ ζ p 0 = cos θ * p 0 - sin θ * p 1 ∧ move θ ζ p 1 = sin θ * p 0 + cos θ * p 1 ∧
      move θ ζ p 2 = p 2 + ζ := ⟨rfl, rfl, rfl⟩

/-- The tetrahedron turned through `θ` fits at height `ζ` exactly when `ζ ≥ h (k - 1) / k`. -/
private lemma fits_iff {a h θ ζ : ℝ} (ha : 0 < a) (hh : 0 < h) (hθ : θ ∈ Set.Icc 0 (2 * π / 3)) :
    Fits a h θ ζ ↔ h * (cos θ + √3 * sin θ - 1) ≤ (cos θ + √3 * sin θ) * ζ := by
  obtain ⟨hs0, hcs, hk⟩ := trig hθ
  have hs := s3
  have hq : 0 < √3 := by positivity
  set c := cos θ
  set s := sin θ
  set k := c + √3 * s with hkdef
  constructor
  · intro hfit
    by_contra hlt
    replace hlt := not_le.mp hlt
    rcases lt_or_ge ζ 0 with hz | hz
    · have hA : vA a ∈ solid a h := subset_convexHull ℝ _ (by simp)
      have hm := hfit _ hA (by simp only [move_2, vA_2]; linarith)
      rw [mem_solid ha hh] at hm
      obtain ⟨-, -, h3, -⟩ := hm
      simp only [move_0, move_1, move_2, vA_0, vA_1, vA_2] at h3
      have : h * k ≤ h + ζ := by
        have : a * (h * k) ≤ a * (h + ζ) := by rw [hkdef]; linarith
        exact le_of_mul_le_mul_left this ha
      nlinarith
    · rcases lt_or_ge ζ h with hzh | hzh
      · set ρ := a * (h - ζ) / h with hρ
        have hρ0 : 0 ≤ ρ := div_nonneg (mul_nonneg ha.le (by linarith)) hh.le
        have hhρ : h * ρ = a * (h - ζ) := by rw [hρ]; field_simp
        obtain ⟨p0, hp0⟩ : ∃ p0 : Space, p0 = !₂[ρ, 0, -ζ] := ⟨_, rfl⟩
        have e0 : p0 0 = ρ := by rw [hp0]; rfl
        have e1 : p0 1 = 0 := by rw [hp0]; rfl
        have e2 : p0 2 = -ζ := by rw [hp0]; rfl
        have hp : p0 ∈ solid a h := by
          rw [mem_solid ha hh, e0, e1, e2]
          refine ⟨by linarith, ?_, ?_, ?_⟩ <;> nlinarith
        have hm := hfit _ hp (by rw [move_2, e2]; linarith)
        rw [mem_solid ha hh] at hm
        obtain ⟨-, -, h3, -⟩ := hm
        rw [move_0, move_1, move_2, e0, e1, e2] at h3
        have : h * ρ * k ≤ a * h := by rw [hkdef]; nlinarith
        rw [hhρ] at this
        have : (h - ζ) * k ≤ h := by
          have : a * ((h - ζ) * k) ≤ a * h := by linarith
          exact le_of_mul_le_mul_left this ha
        nlinarith
      · nlinarith
  · intro hle p hp hz
    rw [mem_solid ha hh] at hp ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hp
    obtain ⟨e0, e1, e2⟩ := move_coords θ ζ p
    rw [e2] at hz
    rw [e0, e1, e2]
    set x := p 0
    set y := p 1
    set z := p 2
    set R := a * (h + z) with hR
    have hc : 0 ≤ √3 * c + s := hcs
    -- the slack needed: `k R ≤ a (h + z + ζ)`
    have hkR : k * R ≤ a * (h + (z + ζ)) := by
      have h5 : (k - 1) * (h + z) ≤ (k - 1) * (h - ζ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have h6 : (k - 1) * (h + z) ≤ ζ := by nlinarith
      have := mul_le_mul_of_nonneg_left h6 ha.le
      rw [hR]
      nlinarith
    have hk3 : (√3 * c + s) * R + 2 * s * R = √3 * (k * R) := by
      rw [hkdef]; linear_combination (-(s * R)) * hs
    refine ⟨hz, ?_, ?_, ?_⟩
    · have e : √3 * (-2 * h * (c * x - s * y)) = (√3 * c + s) * (-2 * h * x) +
          2 * s * (h * (x + √3 * y)) := by ring
      have b1 := mul_le_mul_of_nonneg_left h2 hc
      have b2 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 2 * s)
      have : √3 * (-2 * h * (c * x - s * y)) ≤ √3 * (k * R) := by linarith
      have := le_of_mul_le_mul_left this hq
      linarith
    · have e : √3 * (h * (c * x - s * y + √3 * (s * x + c * y))) =
          (√3 * c + s) * (h * (x + √3 * y)) + 2 * s * (h * (x - √3 * y)) := by
        linear_combination (h * s * x) * hs
      have b1 := mul_le_mul_of_nonneg_left h3 hc
      have b2 := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 2 * s)
      have : √3 * (h * (c * x - s * y + √3 * (s * x + c * y))) ≤ √3 * (k * R) := by linarith
      have := le_of_mul_le_mul_left this hq
      linarith
    · have e : √3 * (h * (c * x - s * y - √3 * (s * x + c * y))) =
          (√3 * c + s) * (h * (x - √3 * y)) + 2 * s * (-2 * h * x) := by
        linear_combination (-(h * s * x)) * hs
      have b1 := mul_le_mul_of_nonneg_left h4 hc
      have b2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * s)
      have : √3 * (h * (c * x - s * y - √3 * (s * x + c * y))) ≤ √3 * (k * R) := by linarith
      have := le_of_mul_le_mul_left this hq
      linarith

/-- The least height at which the tetrahedron turned through `θ` fits. -/
private lemma isLeast_iff {a h θ ζ : ℝ} (ha : 0 < a) (hh : 0 < h)
    (hθ : θ ∈ Set.Icc 0 (2 * π / 3)) :
    IsLeast {ζ' | Fits a h θ ζ'} ζ ↔
      ζ = h * (cos θ + √3 * sin θ - 1) / (cos θ + √3 * sin θ) := by
  obtain ⟨-, -, hk⟩ := trig hθ
  have hk0 : 0 < cos θ + √3 * sin θ := by linarith
  have key : IsLeast {ζ' | Fits a h θ ζ'}
      (h * (cos θ + √3 * sin θ - 1) / (cos θ + √3 * sin θ)) := by
    refine ⟨?_, ?_⟩
    · show Fits a h θ _
      rw [fits_iff ha hh hθ, mul_div_cancel₀ _ hk0.ne']
    · intro ζ' hζ'
      have := (fits_iff ha hh hθ).mp hζ'
      rw [div_le_iff₀ hk0]
      linarith
  exact ⟨fun hl => hl.unique key, fun e => e ▸ key⟩

/-- **Problem 67.** The locus of the revolving vertex is the arc, from `(a, 0, 0)` to
`(-a/2, √3 a/2, 0)`, of the curve `x² + y² = a²`, `(x + √3 y)(h - z) = a h`. -/
theorem problem67 (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    locus a h = {q : Space | q 0 ^ 2 + q 1 ^ 2 = a ^ 2 ∧ (q 0 + √3 * q 1) * (h - q 2) = a * h ∧
      0 ≤ q 1 ∧ 0 ≤ √3 * q 0 + q 1} := by
  have hs := s3
  ext q
  constructor
  · rintro ⟨θ, hθ, ζ, hl, rfl⟩
    rw [isLeast_iff ha hh hθ] at hl
    subst hl
    obtain ⟨hs0, hcs, hk⟩ := trig hθ
    have hk0 : 0 < cos θ + √3 * sin θ := by linarith
    show _ ∧ _
    simp only [move_0, move_1, move_2, vA_0, vA_1, vA_2, mul_zero, sub_zero, add_zero, zero_add]
    refine ⟨?_, ?_, mul_nonneg hs0 ha.le, ?_⟩
    · have := Real.sin_sq_add_cos_sq θ
      linear_combination a ^ 2 * this
    · field_simp
      ring
    · have e : √3 * (cos θ * a) + sin θ * a = (√3 * cos θ + sin θ) * a := by ring
      rw [e]; exact mul_nonneg hcs ha.le
  · rintro ⟨h1, h2, h3, h4⟩
    set x := q 0 / a with hx
    have hq0 : q 0 = a * x := by rw [hx]; field_simp
    rw [hq0] at h1 h2 h4
    have ha2 : 0 < a ^ 2 := by positivity
    have hx1 : x ^ 2 ≤ 1 := by
      have : a ^ 2 * x ^ 2 ≤ a ^ 2 * 1 := by nlinarith [sq_nonneg (q 1)]
      exact le_of_mul_le_mul_left this ha2
    have hxl : -1 ≤ x := by nlinarith
    have hxu : x ≤ 1 := by nlinarith
    have hxh : -(1 / 2) ≤ x := by
      by_contra hlt
      replace hlt := not_le.mp hlt
      have hq : -(√3 * (a * x)) ≤ q 1 := by linarith
      have h0 : 0 ≤ -(√3 * (a * x)) := by
        have : 0 < √3 * (a * -x) := by have := mul_pos ha (by linarith : 0 < -x); positivity
        linarith
      have hsq := pow_le_pow_left₀ h0 hq 2
      have e : (-(√3 * (a * x))) ^ 2 = 3 * (a ^ 2 * x ^ 2) := by
        linear_combination (a ^ 2 * x ^ 2) * hs
      rw [e] at hsq
      have : a ^ 2 * (4 * x ^ 2) ≤ a ^ 2 * 1 := by nlinarith
      have := le_of_mul_le_mul_left this ha2
      nlinarith
    have hcos : cos (Real.arccos x) = x := Real.cos_arccos hxl hxu
    have hsin : sin (Real.arccos x) = q 1 / a := by
      rw [Real.sin_arccos]
      have : q 1 / a = √((q 1 / a) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      rw [this]
      congr 1
      field_simp
      linarith
    have hθ : Real.arccos x ∈ Set.Icc 0 (2 * π / 3) := by
      refine ⟨Real.arccos_nonneg _, ?_⟩
      have := Real.arccos_le_arccos hxh
      have e : Real.arccos (-(1 / 2)) = 2 * π / 3 := by
        rw [Real.arccos_neg]
        have : Real.arccos (1 / 2) = π / 3 := by
          rw [← Real.cos_pi_div_three,
            Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]
        rw [this]; ring
      linarith
    refine ⟨Real.arccos x, hθ, _, (isLeast_iff ha hh hθ).mpr rfl, ?_⟩
    obtain ⟨-, -, hk⟩ := trig hθ
    rw [hcos, hsin] at hk
    have hk0 : 0 < x + √3 * (q 1 / a) := by linarith
    have e : (x + √3 * (q 1 / a)) * (h - q 2) = h := by
      have : a * ((x + √3 * (q 1 / a)) * (h - q 2)) = a * h := by
        rw [← h2]; field_simp
      exact mul_left_cancel₀ ha.ne' this
    apply space_ext
    · rw [move_0, vA_0, vA_1, hcos, hsin, hq0]; ring
    · rw [move_1, vA_0, vA_1, hcos, hsin]; field_simp; ring
    · rw [move_2, vA_2, hcos, hsin, zero_add, eq_div_iff hk0.ne']
      linear_combination (-1 : ℝ) * e

end PillowProblems.P67
