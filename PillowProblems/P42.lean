import PillowProblems.Basic

/-!
# Problem 42 (Trigonometry: Plane)

**Question.** *(dated 17/5/78)*

> If the angles of a given Triangle be bisected, and if lines be drawn, through its vertices, at right angles to the bisectors, so as to form a fresh Triangle: find the ratio of the area of this Triangle to the area of the given Triangle.

**Answer.**

> \[ \frac{abc}{2(s-a).(s-b).(s-c)}. \]

*(Carroll's solution: Chapter III, problem 42; text in `data/problems.json`.)*

**Lean reading.** The given triangle `ABC` is non-degenerate (`cross A B C ≠ 0`). The bisector of the angle at a
vertex `V` (between `VP` and `VQ`) is the line through `V` in the direction `bisectorDir V P Q`,
the sum of the unit vectors along `VP` and `VQ` (`bisectorDir_bisects` checks that it makes
equal angles with both sides), and `perpToBisector V P Q` is the line through `V` at right angles
to it. `A'` is any point on the two such lines through `B` and `C`, and similarly `B'` (through
`C`, `A`) and `C'` (through `A`, `B`), so the "fresh Triangle" is `A'B'C'`; the proof derives
that these are the excentres, and `problem42_exists` shows that each pair of lines meets in
exactly one point. With `a = BC`, `b = CA`, `c = AB` and `s` the semi-perimeter, Carroll's
ratio `abc / (2 (s-a)(s-b)(s-c))` is proved for `area A'B'C' / area ABC`.

**Status.** proved
-/

namespace PillowProblems.P42

open scoped EuclideanGeometry

/-- Direction of the (internal) bisector of the angle `P V Q` at the vertex `V`: the sum of the
unit vectors along `VP` and `VQ`. -/
noncomputable def bisectorDir (V P Q : Plane) : Plane :=
  ‖P - V‖⁻¹ • (P - V) + ‖Q - V‖⁻¹ • (Q - V)

/-- The line drawn through the vertex `V` at right angles to the bisector of the angle `P V Q`. -/
def perpToBisector (V P Q : Plane) : Set Plane :=
  {X | inner ℝ (X - V) (bisectorDir V P Q) = 0}

/-- Sanity check on `bisectorDir`: it makes equal angles with `VP` and `VQ`. -/
theorem bisectorDir_bisects (V P Q : Plane) (hP : P ≠ V) (hQ : Q ≠ V) :
    ∠ P V (V + bisectorDir V P Q) = ∠ Q V (V + bisectorDir V P Q) := by
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub, add_sub_cancel_left]
  unfold InnerProductGeometry.angle
  congr 1
  unfold bisectorDir
  set x := P - V
  set y := Q - V
  have hx : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hP)
  have hy : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hQ)
  have key : inner ℝ x (‖x‖⁻¹ • x + ‖y‖⁻¹ • y) / ‖x‖ =
      inner ℝ y (‖x‖⁻¹ • x + ‖y‖⁻¹ • y) / ‖y‖ := by
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right,
      inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      real_inner_comm y x]
    field_simp
    ring
  rw [← div_div, ← div_div, key]

private lemma dist_sq' (X Y : Plane) : dist X Y ^ 2 = (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma inner' (X Y : Plane) : inner ℝ X Y = X 0 * Y 0 + X 1 * Y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

private lemma bisectorDir_comm (V P Q : Plane) : bisectorDir V P Q = bisectorDir V Q P := by
  unfold bisectorDir; rw [add_comm]

private lemma perpToBisector_comm (V P Q : Plane) : perpToBisector V P Q = perpToBisector V Q P := by
  unfold perpToBisector; rw [bisectorDir_comm]

private lemma mem_perp {V P Q X : Plane} (hP : P ≠ V) (hQ : Q ≠ V) :
    X ∈ perpToBisector V P Q ↔
      dist Q V * inner ℝ (X - V) (P - V) + dist P V * inner ℝ (X - V) (Q - V) = 0 := by
  have hp : 0 < dist P V := dist_pos.2 hP
  have hq : 0 < dist Q V := dist_pos.2 hQ
  unfold perpToBisector bisectorDir
  rw [Set.mem_ofPred_eq, inner_add_right, inner_smul_right, inner_smul_right, ← dist_eq_norm,
    ← dist_eq_norm]
  constructor
  · intro h
    have : dist P V * dist Q V * ((dist P V)⁻¹ * inner ℝ (X - V) (P - V) +
        (dist Q V)⁻¹ * inner ℝ (X - V) (Q - V)) = 0 := by rw [h, mul_zero]
    field_simp at this
    linear_combination this
  · intro h
    field_simp
    linear_combination h

private lemma solve2 {x0 x1 p0 p1 q0 q1 : ℝ} (h1 : x0 * p0 + x1 * p1 = 0)
    (h2 : x0 * q0 + x1 * q1 = 0) (hd : p0 * q1 - p1 * q0 ≠ 0) : x0 = 0 ∧ x1 = 0 := by
  have e0 : x0 * (p0 * q1 - p1 * q0) = 0 := by linear_combination q1 * h1 - p1 * h2
  have e1 : x1 * (p0 * q1 - p1 * q0) = 0 := by linear_combination p0 * h2 - q0 * h1
  exact ⟨(mul_eq_zero.1 e0).resolve_right hd, (mul_eq_zero.1 e1).resolve_right hd⟩

/-- In a non-degenerate triangle with sides `a, b, c`, `b + c - a`, `c + a - b`, `a + b - c` are
positive (strict triangle inequality), via Heron's identity. -/
private lemma triangle_pos (A B C : Plane) (hK : cross A B C ≠ 0) :
    0 < dist C A + dist A B - dist B C ∧ 0 < dist A B + dist B C - dist C A ∧
      0 < dist B C + dist C A - dist A B := by
  set a := dist B C
  set b := dist C A
  set c := dist A B
  have ha2 : a ^ 2 = (B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2 := dist_sq' B C
  have hb2 : b ^ 2 = (C 0 - A 0) ^ 2 + (C 1 - A 1) ^ 2 := dist_sq' C A
  have hc2 : c ^ 2 = (A 0 - B 0) ^ 2 + (A 1 - B 1) ^ 2 := dist_sq' A B
  have ha : 0 ≤ a := dist_nonneg
  have hb : 0 ≤ b := dist_nonneg
  have hc : 0 ≤ c := dist_nonneg
  have hheron : (a + b + c) * ((b + c - a) * (c + a - b) * (a + b - c)) = 4 * cross A B C ^ 2 := by
    have e : (a + b + c) * ((b + c - a) * (c + a - b) * (a + b - c)) =
        2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - (a ^ 2) ^ 2 - (b ^ 2) ^ 2 -
          (c ^ 2) ^ 2 := by ring
    rw [e, ha2, hb2, hc2]
    unfold cross
    ring
  have hK2 : 0 < 4 * cross A B C ^ 2 := by positivity
  have hs : 0 < a + b + c := by
    by_contra hs
    have : a + b + c = 0 := by linarith
    rw [this, zero_mul] at hheron
    linarith
  have hP : 0 < (b + c - a) * (c + a - b) * (a + b - c) := by
    by_contra hP
    rw [not_lt] at hP
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · by_contra h1
    rw [not_lt] at h1
    have : (b + c - a) * (c + a - b) * (a + b - c) ≤ 0 := by
      rw [mul_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg h1 (mul_nonneg (by linarith) (by linarith))
    linarith
  · by_contra h1
    rw [not_lt] at h1
    have : (b + c - a) * (c + a - b) * (a + b - c) ≤ 0 := by
      rw [mul_comm (b + c - a), mul_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    linarith
  · by_contra h1
    rw [not_lt] at h1
    have : (b + c - a) * (c + a - b) * (a + b - c) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) (by linarith)) (by linarith)
    linarith

/-- The point where the lines through `B` and `C` (at right angles to the bisectors of the angles
`B`, `C`) meet is the excentre opposite `A`: `(b + c - a) X = -a A + b B + c C`. -/
private lemma excentre_iff (A B C X : Plane) (hK : cross A B C ≠ 0) :
    (X ∈ perpToBisector B A C ∧ X ∈ perpToBisector C A B) ↔
      ((dist C A + dist A B - dist B C) * X 0 =
          -dist B C * A 0 + dist C A * B 0 + dist A B * C 0 ∧
        (dist C A + dist A B - dist B C) * X 1 =
          -dist B C * A 1 + dist C A * B 1 + dist A B * C 1) := by
  have hAB : A ≠ B := by rintro rfl; exact hK (by unfold cross; ring)
  have hBC : B ≠ C := by rintro rfl; exact hK (by unfold cross; ring)
  have hCA : C ≠ A := by rintro rfl; exact hK (by unfold cross; ring)
  have hpos := (triangle_pos A B C hK).1
  rw [mem_perp hAB hBC.symm, mem_perp hCA.symm hBC, dist_comm C B, dist_comm A C]
  set a := dist B C
  set b := dist C A
  set c := dist A B
  have ha2 : a ^ 2 = (B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2 := dist_sq' B C
  have hb2 : b ^ 2 = (C 0 - A 0) ^ 2 + (C 1 - A 1) ^ 2 := dist_sq' C A
  have hc2 : c ^ 2 = (A 0 - B 0) ^ 2 + (A 1 - B 1) ^ 2 := dist_sq' A B
  have ha : 0 < a := dist_pos.2 hBC
  have hb : 0 < b := dist_pos.2 hCA
  have hc : 0 < c := dist_pos.2 hAB
  simp only [inner', PiLp.sub_apply]
  constructor
  · rintro ⟨h1, h2⟩
    have hd : (a * (A 0 - B 0) + c * (C 0 - B 0)) * (a * (A 1 - C 1) + b * (B 1 - C 1)) -
        (a * (A 1 - B 1) + c * (C 1 - B 1)) * (a * (A 0 - C 0) + b * (B 0 - C 0)) ≠ 0 := by
      have e : (a * (A 0 - B 0) + c * (C 0 - B 0)) * (a * (A 1 - C 1) + b * (B 1 - C 1)) -
          (a * (A 1 - B 1) + c * (C 1 - B 1)) * (a * (A 0 - C 0) + b * (B 0 - C 0)) =
          a * (a + b + c) * cross A B C := by unfold cross; ring
      rw [e]
      have : 0 < a + b + c := by linarith
      positivity
    have := solve2
      (x0 := (b + c - a) * X 0 - (-a * A 0 + b * B 0 + c * C 0))
      (x1 := (b + c - a) * X 1 - (-a * A 1 + b * B 1 + c * C 1))
      (by linear_combination (b + c - a) * h1 - a ^ 2 * hc2 + c ^ 2 * ha2)
      (by linear_combination (b + c - a) * h2 - a ^ 2 * hb2 + b ^ 2 * ha2) hd
    constructor <;> linarith [this.1, this.2]
  · rintro ⟨hx0, hx1⟩
    constructor
    · have : (b + c - a) * (a * ((X 0 - B 0) * (A 0 - B 0) + (X 1 - B 1) * (A 1 - B 1)) +
          c * ((X 0 - B 0) * (C 0 - B 0) + (X 1 - B 1) * (C 1 - B 1))) = 0 := by
        linear_combination (a * (A 0 - B 0) + c * (C 0 - B 0)) * hx0 +
          (a * (A 1 - B 1) + c * (C 1 - B 1)) * hx1 + a ^ 2 * hc2 - c ^ 2 * ha2
      exact (mul_eq_zero.1 this).resolve_left hpos.ne'
    · have : (b + c - a) * (a * ((X 0 - C 0) * (A 0 - C 0) + (X 1 - C 1) * (A 1 - C 1)) +
          b * ((X 0 - C 0) * (B 0 - C 0) + (X 1 - C 1) * (B 1 - C 1))) = 0 := by
        linear_combination (a * (A 0 - C 0) + b * (B 0 - C 0)) * hx0 +
          (a * (A 1 - C 1) + b * (B 1 - C 1)) * hx1 + a ^ 2 * hb2 - b ^ 2 * ha2
      exact (mul_eq_zero.1 this).resolve_left hpos.ne'

private lemma cross_BCA (A B C : Plane) : cross B C A = cross A B C := by unfold cross; ring
private lemma cross_CAB (A B C : Plane) : cross C A B = cross A B C := by unfold cross; ring

/-- **Problem 42.** Let `A'` be the meeting point of the lines through `B` and `C` at right angles
to the bisectors of the angles `B`, `C`; similarly `B'` (lines through `C`, `A`) and `C'` (lines
through `A`, `B`). Then `area A'B'C' / area ABC = abc / (2 (s-a)(s-b)(s-c))`. -/
theorem problem42 (A B C A' B' C' : Plane) (hABC : cross A B C ≠ 0)
    (hA' : A' ∈ perpToBisector B A C ∧ A' ∈ perpToBisector C A B)
    (hB' : B' ∈ perpToBisector C A B ∧ B' ∈ perpToBisector A B C)
    (hC' : C' ∈ perpToBisector A B C ∧ C' ∈ perpToBisector B A C) :
    triArea A' B' C' / triArea A B C =
      dist B C * dist C A * dist A B /
        (2 * ((dist B C + dist C A + dist A B) / 2 - dist B C) *
          ((dist B C + dist C A + dist A B) / 2 - dist C A) *
          ((dist B C + dist C A + dist A B) / 2 - dist A B)) := by
  have hBCA : cross B C A ≠ 0 := by rwa [cross_BCA]
  have hCAB : cross C A B ≠ 0 := by rwa [cross_CAB]
  obtain ⟨ha0, ha1⟩ := (excentre_iff A B C A' hABC).1 hA'
  obtain ⟨hb0, hb1⟩ := (excentre_iff B C A B' hBCA).1
    ⟨by rw [perpToBisector_comm]; exact hB'.1, hB'.2⟩
  obtain ⟨hc0, hc1⟩ := (excentre_iff C A B C' hCAB).1
    ⟨by rw [perpToBisector_comm]; exact hC'.1, by rw [perpToBisector_comm]; exact hC'.2⟩
  obtain ⟨p1, p2, p3⟩ := triangle_pos A B C hABC
  set a := dist B C
  set b := dist C A
  set c := dist A B
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have hc : 0 < c := by linarith
  have eA0 : A' 0 = (-a * A 0 + b * B 0 + c * C 0) / (b + c - a) := by
    field_simp; linarith
  have eA1 : A' 1 = (-a * A 1 + b * B 1 + c * C 1) / (b + c - a) := by
    field_simp; linarith
  have eB0 : B' 0 = (-b * B 0 + c * C 0 + a * A 0) / (c + a - b) := by
    field_simp; linarith
  have eB1 : B' 1 = (-b * B 1 + c * C 1 + a * A 1) / (c + a - b) := by
    field_simp; linarith
  have eC0 : C' 0 = (-c * C 0 + a * A 0 + b * B 0) / (a + b - c) := by
    field_simp; linarith
  have eC1 : C' 1 = (-c * C 1 + a * A 1 + b * B 1) / (a + b - c) := by
    field_simp; linarith
  have hcross : cross A' B' C' =
      4 * a * b * c / ((b + c - a) * (c + a - b) * (a + b - c)) * cross A B C := by
    unfold cross
    rw [eA0, eA1, eB0, eB1, eC0, eC1]
    field_simp
    ring
  unfold triArea
  rw [hcross, abs_mul, abs_of_pos (by positivity),
    show (a + b + c) / 2 - a = (b + c - a) / 2 by ring,
    show (a + b + c) / 2 - b = (c + a - b) / 2 by ring,
    show (a + b + c) / 2 - c = (a + b - c) / 2 by ring]
  have : 0 < |cross A B C| := abs_pos.2 hABC
  have := p1.ne'
  have := p2.ne'
  have := p3.ne'
  field_simp
  ring

/-- The lines through `B` and `C` at right angles to the bisectors meet in exactly one point (and
likewise for the other two pairs), so the triangle `A'B'C'` of `problem42` exists and is unique. -/
theorem problem42_exists (A B C : Plane) (hABC : cross A B C ≠ 0) :
    (∃! X, X ∈ perpToBisector B A C ∧ X ∈ perpToBisector C A B) ∧
    (∃! X, X ∈ perpToBisector C A B ∧ X ∈ perpToBisector A B C) ∧
    (∃! X, X ∈ perpToBisector A B C ∧ X ∈ perpToBisector B A C) := by
  have key : ∀ A B C : Plane, cross A B C ≠ 0 →
      ∃! X, X ∈ perpToBisector B A C ∧ X ∈ perpToBisector C A B := by
    intro A B C hK
    have hpos := (triangle_pos A B C hK).1
    set a := dist B C
    set b := dist C A
    set c := dist A B
    refine ⟨pt ((-a * A 0 + b * B 0 + c * C 0) / (b + c - a))
      ((-a * A 1 + b * B 1 + c * C 1) / (b + c - a)), (excentre_iff A B C _ hK).2 ⟨?_, ?_⟩, ?_⟩
    · simp only [pt_zero]
      field_simp
      rfl
    · simp only [pt_one]
      field_simp
      rfl
    · intro Y hY
      obtain ⟨h0, h1⟩ := (excentre_iff A B C Y hK).1 hY
      ext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, pt_zero]
        field_simp; linarith
      · simp only [Fin.mk_one, Fin.isValue, pt_one]
        field_simp; linarith
  refine ⟨key A B C hABC, ?_, ?_⟩
  · have := key B C A (by rwa [cross_BCA])
    simpa only [perpToBisector_comm C B A] using this
  · have := key C A B (by rwa [cross_CAB])
    simpa only [perpToBisector_comm A C B, perpToBisector_comm B C A] using this

end PillowProblems.P42
