import PillowProblems.Basic

/-!
# Problem 40 (Pure Geometry, Plane)

**Question.** *(dated 5/76)*

> In a given Triangle, whose base-angles are acute, draw two lines, at right angles to the base, and together equal to the line drawn, from the vertex, at right angles to the base, and such that
>
> (1) they are equidistant from the line drawn from the vertex;
>
> (2) they are equidistant from the ends of the base.

*(Carroll's solution: Chapter III, problem 40; text in `data/problems.json`.)*

**Lean reading.** `A B C` is a triangle (`cross A B C ≠ 0`) with base `BC` and acute base angles
(`∠ABC, ∠ACB < π/2`). `AD` is the line from the vertex at right angles to the base (`D` on line
`BC`, `AD ⊥ BC`). A line at right angles to the base, inside the triangle, is a segment `PQ` with
`P` on the base, `Q` on side `BA` or `CA`, and `PQ ⊥ BC` (`PerpToBase`). Distance from `AD` is
measured by `dist P D`, the distance between the parallel lines. In (1) the two lines must be
distinct; otherwise "two lines" would be one line counted twice. In (2) `P₁Q₁` is the line nearer
`B` and `BP₁ = CP₂`. Each part proves that the two lines are together equal to `AD` iff the common
distance is `BD · DC / BC`, and that such a pair exists. In (1) this distance is Carroll's
`DH = DG`, and in (2) it is his `BK = HC`. So in each case the pair is unique.
`problem40_nonvacuous` exhibits a triangle satisfying the hypotheses.

**Status.** proved
-/

namespace PillowProblems.P40

open scoped EuclideanGeometry RealInnerProductSpace
open Real

/-- `PQ` is a line in the triangle `ABC` drawn at right angles to the base `BC`: its foot `P` is on
the base and its other end `Q` is on one of the two other sides `BA`, `CA`. -/
def PerpToBase (A B C P Q : Plane) : Prop :=
  P ∈ segment ℝ B C ∧ (Q ∈ segment ℝ B A ∨ Q ∈ segment ℝ C A) ∧ ⟪Q - P, C - B⟫ = 0

private lemma seg_param {X Y P : Plane} (h : P ∈ segment ℝ X Y) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ P = X + s • (Y - X) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h
  refine ⟨b, hb, by linarith, ?_⟩
  obtain rfl : a = 1 - b := by linarith
  module

private lemma seg_mem {X Y : Plane} {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    X + s • (Y - X) ∈ segment ℝ X Y :=
  ⟨1 - s, s, by linarith, h0, by ring, by module⟩

/-- The height profile of the triangle along the base, in units of the altitude `AD`, where the
foot `D` of the altitude sits at parameter `μ` of the base. -/
private noncomputable def hgt (μ s : ℝ) : ℝ := min (s / μ) ((1 - s) / (1 - μ))

private lemma hgt_left {μ s : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hs : s ≤ μ) :
    hgt μ s = s / μ := by
  unfold hgt
  apply min_eq_left
  rw [div_le_div_iff₀ hμ0 (by linarith)]
  nlinarith

private lemma hgt_right {μ s : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hs : μ ≤ s) :
    hgt μ s = (1 - s) / (1 - μ) := by
  unfold hgt
  apply min_eq_right
  rw [div_le_div_iff₀ (by linarith) hμ0]
  nlinarith

/-- Every line at right angles to the base has length `hgt μ s · AD`. -/
private lemma perp_len {A B C D P Q : Plane} {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hw : C - B ≠ 0) (hD : D = B + μ • (C - B)) (hAD : ⟪A - D, C - B⟫ = 0)
    (h : PerpToBase A B C P Q) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ P = B + s • (C - B) ∧ dist P Q = hgt μ s * dist A D := by
  obtain ⟨hP, hQ, hperp⟩ := h
  obtain ⟨s, hs0, hs1, rfl⟩ := seg_param hP
  refine ⟨s, hs0, hs1, rfl, ?_⟩
  have hw2 : 0 < ‖C - B‖ ^ 2 := by positivity
  rcases hQ with hQ | hQ
  · obtain ⟨l, hl0, hl1, rfl⟩ := seg_param hQ
    have hQP : B + l • (A - B) - (B + s • (C - B)) = l • (A - D) + (l * μ - s) • (C - B) := by
      rw [hD]; module
    rw [hQP, inner_add_left, inner_smul_left, inner_smul_left, hAD,
      real_inner_self_eq_norm_sq] at hperp
    simp only [RCLike.conj_to_real, mul_zero, zero_add] at hperp
    have hs : s = l * μ := by
      have := mul_eq_zero.mp hperp
      rcases this with h | h
      · linarith
      · linarith
    have hle : s ≤ μ := by rw [hs]; nlinarith
    rw [hgt_left hμ0 hμ1 hle, dist_comm, dist_eq_norm, hQP, hs, sub_self, zero_smul, add_zero,
      norm_smul, Real.norm_of_nonneg hl0, ← dist_eq_norm]
    field_simp
  · obtain ⟨l, hl0, hl1, rfl⟩ := seg_param hQ
    have hQP : C + l • (A - C) - (B + s • (C - B)) =
        l • (A - D) + ((1 - s) - l * (1 - μ)) • (C - B) := by
      rw [hD]; module
    rw [hQP, inner_add_left, inner_smul_left, inner_smul_left, hAD,
      real_inner_self_eq_norm_sq] at hperp
    simp only [RCLike.conj_to_real, mul_zero, zero_add] at hperp
    have hs : 1 - s = l * (1 - μ) := by
      have := mul_eq_zero.mp hperp
      rcases this with h | h
      · linarith
      · linarith
    have hle : μ ≤ s := by nlinarith
    rw [hgt_right hμ0 hμ1 hle, dist_comm, dist_eq_norm, hQP, hs, sub_self, zero_smul, add_zero,
      norm_smul, Real.norm_of_nonneg hl0, ← dist_eq_norm]
    field_simp [show (1 - μ) ≠ 0 by linarith]

/-- Every point of the base carries a line at right angles to the base. -/
private lemma perp_exists {A B C D : Plane} {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hD : D = B + μ • (C - B)) (hAD : ⟪A - D, C - B⟫ = 0) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ Q, PerpToBase A B C (B + s • (C - B)) Q := by
  rcases le_total s μ with hle | hle
  · refine ⟨B + (s / μ) • (A - B), seg_mem hs0 hs1, Or.inl (seg_mem (by positivity) ?_), ?_⟩
    · rw [div_le_one hμ0]; exact hle
    · have hQP : B + (s / μ) • (A - B) - (B + s • (C - B)) = (s / μ) • (A - D) := by
        rw [hD]
        calc B + (s / μ) • (A - B) - (B + s • (C - B))
            = (s / μ) • (A - B) - ((s / μ) * μ) • (C - B) := by
              rw [div_mul_cancel₀ s hμ0.ne']; module
          _ = _ := by module
      rw [hQP, inner_smul_left, hAD, mul_zero]
  · have h1μ : 0 < 1 - μ := by linarith
    refine ⟨C + ((1 - s) / (1 - μ)) • (A - C), seg_mem hs0 hs1,
      Or.inr (seg_mem (div_nonneg (by linarith) h1μ.le) ?_), ?_⟩
    · rw [div_le_one h1μ]; linarith
    · have hQP : C + ((1 - s) / (1 - μ)) • (A - C) - (B + s • (C - B)) =
          ((1 - s) / (1 - μ)) • (A - D) := by
        have e : ((1 - s) / (1 - μ)) * μ = ((1 - s) / (1 - μ)) - (1 - s) := by
          field_simp; ring
        rw [hD]
        calc C + ((1 - s) / (1 - μ)) • (A - C) - (B + s • (C - B))
            = ((1 - s) / (1 - μ)) • (A - B) - (((1 - s) / (1 - μ)) - (1 - s)) • (C - B) := by
              module
          _ = _ := by rw [← e]; module
      rw [hQP, inner_smul_left, hAD, mul_zero]

private lemma dist_base (B C : Plane) (s t : ℝ) :
    dist (B + s • (C - B)) (B + t • (C - B)) = |s - t| * dist B C := by
  rw [dist_eq_norm, dist_eq_norm, show B + s • (C - B) - (B + t • (C - B)) = (s - t) • (C - B) by
    module, norm_smul, Real.norm_eq_abs, ← norm_neg (B - C), neg_sub]

/-- The common setting: the foot `D` of the altitude divides the base at parameter `μ ∈ (0,1)`,
and the altitude `AD` and the base `BC` have positive length. -/
private lemma setting {A B C D : Plane} (hABC : cross A B C ≠ 0) (hB : ∠ A B C < π / 2)
    (hC : ∠ A C B < π / 2) (hD : D ∈ line[ℝ, B, C]) (hAD : ⟪A - D, C - B⟫ = 0) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ D = B + μ • (C - B) ∧ C - B ≠ 0 ∧ 0 < dist A D ∧ 0 < dist B C := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hD
  obtain ⟨μ, rfl⟩ := hD
  rw [AffineMap.lineMap_apply_module'] at hAD ⊢
  have hw : C - B ≠ 0 := by
    intro h
    apply hABC
    have : C = B := sub_eq_zero.mp h
    subst this; simp [cross]
  have hw2 : 0 < ‖C - B‖ ^ 2 := by positivity
  have e1 : ⟪A - B, C - B⟫ = μ * ‖C - B‖ ^ 2 := by
    have : A - (μ • (C - B) + B) = (A - B) - μ • (C - B) := by module
    rw [this, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq] at hAD
    simp only [RCLike.conj_to_real] at hAD
    linarith
  have hBpos : 0 < ⟪A - B, C - B⟫ := by
    by_contra hn
    have := (InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle).mp (not_lt.mp hn)
    exact absurd hB (not_lt.mpr this)
  have hCpos : 0 < ⟪A - C, B - C⟫ := by
    by_contra hn
    have := (InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle).mp (not_lt.mp hn)
    exact absurd hC (not_lt.mpr this)
  have e2 : ⟪A - C, B - C⟫ = (1 - μ) * ‖C - B‖ ^ 2 := by
    have h1 : A - C = (A - B) - (C - B) := by abel
    have h2 : B - C = -(C - B) := by abel
    rw [h1, h2, inner_neg_right, inner_sub_left, real_inner_self_eq_norm_sq, e1]
    ring
  refine ⟨μ, ?_, ?_, by rw [add_comm], hw, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · apply dist_pos.mpr
    intro hA
    apply hABC
    have h0 := congrArg (fun P : Plane => P 0) hA
    have h1 := congrArg (fun P : Plane => P 1) hA
    simp at h0 h1
    simp only [cross]
    rw [h0, h1]; ring
  · rw [dist_pos]; intro h; exact hw (by rw [h, sub_self])

private lemma real_a {μ s₁ s₂ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hne : s₁ ≠ s₂) (heq : |s₁ - μ| = |s₂ - μ|) :
    hgt μ s₁ + hgt μ s₂ = 1 ↔ |s₁ - μ| = μ * (1 - μ) := by
  have hsum : s₁ + s₂ = 2 * μ := by
    rcases abs_eq_abs.mp heq with h | h
    · exact absurd (by linarith) hne
    · linarith
  have h1μ : (1 - μ) ≠ 0 := by linarith
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have ha : s₁ ≤ μ := by linarith
    have hb : μ ≤ s₂ := by linarith
    rw [hgt_left hμ0 hμ1 ha, hgt_right hμ0 hμ1 hb, abs_of_nonpos (by linarith)]
    rw [div_add_div _ _ hμ0.ne' h1μ, div_eq_one_iff_eq (mul_ne_zero hμ0.ne' h1μ)]
    constructor <;> intro h <;> nlinarith
  · have ha : μ ≤ s₁ := by linarith
    have hb : s₂ ≤ μ := by linarith
    rw [hgt_right hμ0 hμ1 ha, hgt_left hμ0 hμ1 hb, abs_of_nonneg (by linarith)]
    rw [div_add_div _ _ h1μ hμ0.ne', div_eq_one_iff_eq (mul_ne_zero h1μ hμ0.ne')]
    constructor <;> intro h <;> nlinarith

private lemma real_b {μ s₁ s₂ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hsum : s₁ + s₂ = 1) (hlt : s₁ < s₂) :
    hgt μ s₁ + hgt μ s₂ = 1 ↔ s₁ = μ * (1 - μ) := by
  have h1μ : (1 - μ) ≠ 0 := by linarith
  by_cases ha : s₁ ≤ μ
  · by_cases hb : μ ≤ s₂
    · rw [hgt_left hμ0 hμ1 ha, hgt_right hμ0 hμ1 hb]
      rw [div_add_div _ _ hμ0.ne' h1μ, div_eq_one_iff_eq (mul_ne_zero hμ0.ne' h1μ)]
      constructor <;> intro h <;> nlinarith
    · rw [not_le] at hb
      rw [hgt_left hμ0 hμ1 ha, hgt_left hμ0 hμ1 hb.le, ← add_div, hsum]
      constructor
      · intro h; rw [div_eq_one_iff_eq hμ0.ne'] at h; linarith
      · intro h; nlinarith
  · rw [not_le] at ha
    rw [hgt_right hμ0 hμ1 ha.le, hgt_right hμ0 hμ1 (by linarith), ← add_div]
    constructor
    · intro h; rw [div_eq_one_iff_eq h1μ] at h; linarith
    · intro h; nlinarith

/-- From `(x + y) * H = H` with `H > 0` to `x + y = 1`, and back. -/
private lemma mul_eq_self_iff {x H : ℝ} (hH : 0 < H) : x * H = H ↔ x = 1 := by
  constructor
  · intro h; exact mul_right_cancel₀ hH.ne' (h.trans (one_mul H).symm)
  · rintro rfl; exact one_mul H

/-- The common lengths along the base, in terms of the parameter `μ` of the foot `D`. -/
private lemma base_lengths {B C D : Plane} {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hDμ : D = B + μ • (C - B)) :
    dist B D * dist D C / dist B C = μ * (1 - μ) * dist B C ∧
      (∀ s, dist (B + s • (C - B)) D = |s - μ| * dist B C) ∧
      (∀ s, dist B (B + s • (C - B)) = |s| * dist B C) ∧
      (∀ s, dist C (B + s • (C - B)) = |1 - s| * dist B C) := by
  have hB : ∀ s, dist B (B + s • (C - B)) = |s| * dist B C := by
    intro s
    have := dist_base B C 0 s
    simpa only [zero_smul, add_zero, zero_sub, abs_neg] using this
  have hC : ∀ s, dist C (B + s • (C - B)) = |1 - s| * dist B C := by
    intro s
    have := dist_base B C 1 s
    simpa only [one_smul, add_sub_cancel] using this
  refine ⟨?_, fun s => by rw [hDμ, dist_base], hB, hC⟩
  rw [hDμ, hB, show dist (B + μ • (C - B)) C = dist C (B + μ • (C - B)) from dist_comm _ _, hC,
    abs_of_pos hμ0, abs_of_pos (by linarith : 0 < 1 - μ)]
  rcases eq_or_ne (dist B C) 0 with h | h
  · rw [h]; simp
  · field_simp

/-- **Problem 40 (1).** In a triangle `ABC` with acute base angles, let `AD` be the line drawn
from the vertex at right angles to the base. Two distinct lines at right angles to the base and
equidistant from `AD` are together equal to `AD` if and only if each is at the distance
`BD · DC / BC` from `AD`; and such a pair of lines exists. -/
theorem problem40_a (A B C D : Plane) (hABC : cross A B C ≠ 0)
    (hB : ∠ A B C < π / 2) (hC : ∠ A C B < π / 2)
    (hD : D ∈ line[ℝ, B, C]) (hAD : ⟪A - D, C - B⟫ = 0) :
    (∀ P₁ Q₁ P₂ Q₂ : Plane, PerpToBase A B C P₁ Q₁ → PerpToBase A B C P₂ Q₂ → P₁ ≠ P₂ →
        dist P₁ D = dist P₂ D →
        (dist P₁ Q₁ + dist P₂ Q₂ = dist A D ↔ dist P₁ D = dist B D * dist D C / dist B C)) ∧
    ∃ P₁ Q₁ P₂ Q₂ : Plane, PerpToBase A B C P₁ Q₁ ∧ PerpToBase A B C P₂ Q₂ ∧ P₁ ≠ P₂ ∧
        dist P₁ D = dist P₂ D ∧ dist P₁ Q₁ + dist P₂ Q₂ = dist A D := by
  obtain ⟨μ, hμ0, hμ1, hDμ, hw, hH, hL⟩ := setting hABC hB hC hD hAD
  obtain ⟨hprod, hPD, -, -⟩ := base_lengths (C := C) hμ0 hμ1 hDμ
  have key : ∀ P₁ Q₁ P₂ Q₂ : Plane, PerpToBase A B C P₁ Q₁ → PerpToBase A B C P₂ Q₂ → P₁ ≠ P₂ →
      dist P₁ D = dist P₂ D →
      (dist P₁ Q₁ + dist P₂ Q₂ = dist A D ↔ dist P₁ D = dist B D * dist D C / dist B C) := by
    intro P₁ Q₁ P₂ Q₂ h₁ h₂ hne heq
    obtain ⟨s₁, -, -, rfl, hd₁⟩ := perp_len hμ0 hμ1 hw hDμ hAD h₁
    obtain ⟨s₂, -, -, rfl, hd₂⟩ := perp_len hμ0 hμ1 hw hDμ hAD h₂
    rw [hPD, hPD] at heq
    have hne' : s₁ ≠ s₂ := by rintro rfl; exact hne rfl
    have heq' : |s₁ - μ| = |s₂ - μ| := mul_right_cancel₀ hL.ne' heq
    rw [hd₁, hd₂, hprod, hPD, ← add_mul, mul_eq_self_iff hH, real_a hμ0 hμ1 hne' heq',
      mul_left_inj' hL.ne']
  refine ⟨key, ?_⟩
  -- the two lines at parameters `μ ∓ μ(1-μ)`
  have h1 : 0 ≤ μ * μ := by positivity
  have h2 : μ * μ ≤ 1 := by nlinarith
  have h3 : 0 ≤ 2 * μ - μ * μ := by nlinarith
  have h4 : 2 * μ - μ * μ ≤ 1 := by nlinarith
  obtain ⟨Q₁, hQ₁⟩ := perp_exists hμ0 hμ1 hDμ hAD h1 h2
  obtain ⟨Q₂, hQ₂⟩ := perp_exists hμ0 hμ1 hDμ hAD h3 h4
  have hne : B + (μ * μ) • (C - B) ≠ B + (2 * μ - μ * μ) • (C - B) := by
    intro h
    have := dist_base B C (μ * μ) (2 * μ - μ * μ)
    rw [h, dist_self] at this
    have h5 : |μ * μ - (2 * μ - μ * μ)| = 0 := by
      rcases mul_eq_zero.mp this.symm with h | h
      · exact h
      · exact absurd h hL.ne'
    rw [abs_eq_zero] at h5
    nlinarith
  have heq : dist (B + (μ * μ) • (C - B)) D = dist (B + (2 * μ - μ * μ) • (C - B)) D := by
    rw [hPD, hPD, abs_of_nonpos (by nlinarith), abs_of_nonneg (by nlinarith)]
    ring
  refine ⟨_, Q₁, _, Q₂, hQ₁, hQ₂, hne, heq, ?_⟩
  rw [key _ _ _ _ hQ₁ hQ₂ hne heq, hPD, hprod, abs_of_nonpos (by nlinarith)]
  ring

/-- **Problem 40 (2).** In the same setting, two lines at right angles to the base, equidistant
from the ends of the base (the first, `P₁Q₁`, being the nearer to `B`), are together equal to `AD`
if and only if each is at the distance `BD · DC / BC` from its end of the base; and such a pair of
lines exists. -/
theorem problem40_b (A B C D : Plane) (hABC : cross A B C ≠ 0)
    (hB : ∠ A B C < π / 2) (hC : ∠ A C B < π / 2)
    (hD : D ∈ line[ℝ, B, C]) (hAD : ⟪A - D, C - B⟫ = 0) :
    (∀ P₁ Q₁ P₂ Q₂ : Plane, PerpToBase A B C P₁ Q₁ → PerpToBase A B C P₂ Q₂ →
        dist B P₁ < dist B P₂ → dist B P₁ = dist C P₂ →
        (dist P₁ Q₁ + dist P₂ Q₂ = dist A D ↔ dist B P₁ = dist B D * dist D C / dist B C)) ∧
    ∃ P₁ Q₁ P₂ Q₂ : Plane, PerpToBase A B C P₁ Q₁ ∧ PerpToBase A B C P₂ Q₂ ∧
        dist B P₁ < dist B P₂ ∧ dist B P₁ = dist C P₂ ∧ dist P₁ Q₁ + dist P₂ Q₂ = dist A D := by
  obtain ⟨μ, hμ0, hμ1, hDμ, hw, hH, hL⟩ := setting hABC hB hC hD hAD
  obtain ⟨hprod, -, hBP, hCP⟩ := base_lengths (C := C) hμ0 hμ1 hDμ
  have key : ∀ P₁ Q₁ P₂ Q₂ : Plane, PerpToBase A B C P₁ Q₁ → PerpToBase A B C P₂ Q₂ →
      dist B P₁ < dist B P₂ → dist B P₁ = dist C P₂ →
      (dist P₁ Q₁ + dist P₂ Q₂ = dist A D ↔ dist B P₁ = dist B D * dist D C / dist B C) := by
    intro P₁ Q₁ P₂ Q₂ h₁ h₂ hlt heq
    obtain ⟨s₁, h10, -, rfl, hd₁⟩ := perp_len hμ0 hμ1 hw hDμ hAD h₁
    obtain ⟨s₂, h20, h21, rfl, hd₂⟩ := perp_len hμ0 hμ1 hw hDμ hAD h₂
    rw [hBP, hBP, abs_of_nonneg h10, abs_of_nonneg h20] at hlt
    rw [hBP, hCP, abs_of_nonneg h10, abs_of_nonneg (by linarith)] at heq
    have hlt' : s₁ < s₂ := lt_of_mul_lt_mul_right hlt hL.le
    have hsum : s₁ + s₂ = 1 := by
      have := mul_right_cancel₀ hL.ne' heq; linarith
    rw [hd₁, hd₂, hprod, hBP, abs_of_nonneg h10, ← add_mul, mul_eq_self_iff hH,
      real_b hμ0 hμ1 hsum hlt', mul_left_inj' hL.ne']
  refine ⟨key, ?_⟩
  have h1 : 0 ≤ μ * (1 - μ) := by nlinarith
  have h2 : μ * (1 - μ) ≤ 1 := by nlinarith
  have h3 : 0 ≤ 1 - μ * (1 - μ) := by nlinarith
  have h4 : 1 - μ * (1 - μ) ≤ 1 := by nlinarith
  obtain ⟨Q₁, hQ₁⟩ := perp_exists hμ0 hμ1 hDμ hAD h1 h2
  obtain ⟨Q₂, hQ₂⟩ := perp_exists hμ0 hμ1 hDμ hAD h3 h4
  have hlt : dist B (B + (μ * (1 - μ)) • (C - B)) < dist B (B + (1 - μ * (1 - μ)) • (C - B)) := by
    rw [hBP, hBP, abs_of_nonneg h1, abs_of_nonneg h3]
    exact mul_lt_mul_of_pos_right (by nlinarith) hL
  have heq : dist B (B + (μ * (1 - μ)) • (C - B)) = dist C (B + (1 - μ * (1 - μ)) • (C - B)) := by
    rw [hBP, hCP, abs_of_nonneg h1, abs_of_nonneg (by nlinarith)]
    ring
  refine ⟨_, Q₁, _, Q₂, hQ₁, hQ₂, hlt, heq, ?_⟩
  rw [key _ _ _ _ hQ₁ hQ₂ hlt heq, hBP, hprod, abs_of_nonneg h1]

private lemma inner_coord (P Q : Plane) : ⟪P, Q⟫ = P 0 * Q 0 + P 1 * Q 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

/-- The hypotheses of `problem40_a` and `problem40_b` are satisfiable: the triangle with vertex
`(1, 1)` on the base from `(0, 0)` to `(2, 0)`, whose altitude has foot `(1, 0)`. -/
theorem problem40_nonvacuous :
    ∃ A B C D : Plane, cross A B C ≠ 0 ∧ ∠ A B C < π / 2 ∧ ∠ A C B < π / 2 ∧
      D ∈ line[ℝ, B, C] ∧ ⟪A - D, C - B⟫ = 0 := by
  refine ⟨pt 1 1, pt 0 0, pt 2 0, pt 1 0, ?_, ?_, ?_, ?_, ?_⟩
  · simp [cross]
  · rw [EuclideanGeometry.angle]
    by_contra h
    rw [not_lt, ← InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle] at h
    simp only [vsub_eq_sub, inner_coord, PiLp.sub_apply, pt_zero, pt_one] at h
    norm_num at h
  · rw [EuclideanGeometry.angle]
    by_contra h
    rw [not_lt, ← InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle] at h
    simp only [vsub_eq_sub, inner_coord, PiLp.sub_apply, pt_zero, pt_one] at h
    norm_num at h
  · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨1 / 2, ?_⟩
    rw [AffineMap.lineMap_apply_module']
    ext i; fin_cases i <;> simp [pt]
  · simp only [inner_coord, PiLp.sub_apply, pt_zero, pt_one]
    norm_num

end PillowProblems.P40
