import PillowProblems.Basic

/-!
# Problem 56 (Trigonometry: Plane)

**Question.** *(dated 27/6/84)*

> Given the 3 altitudes of a Triangle: construct it.

**Answer.**

> [Figure: A geometric diagram of two vertical parallel lines with points D/F and E/G, connected by multiple crossing lines through interior points A, B, C.]
>
> Draw \(BC\), \(CE\), \(BD\) equal to the given altitudes, so as to form right \(\angle\)s at \(B\) and \(C\): and produce \(DB\), \(EC\). Join \(DC\), and draw \(CF \perp\) to it. Join \(EB\), and draw \(BG \perp\) to it. With centre \(B\), and distance \(BF\), describe a circle: with centre \(C\), and distance \(CG\) describe another: let them meet at \(A\): and join \(AB\), \(AC\). Triangle \(ABC\) may be proved to be similar to required Triangle. The rest of the construction is obvious.

*(Carroll's solution: Chapter III, problem 56; text in `data/problems.json`.)*

**Lean reading.** A triangle is three points `A, B, C` of the plane with `cross A B C ≠ 0` (non-degenerate), and
`IsAltitude A B C h` says the altitude from `A` has length `h`: there is a foot `F` on the line `BC`
with `AF ⊥ BC` and `AF = h`; `HasAltitudes A B C ha hb hc` collects the three altitudes.
"Construct it" is read as existence plus uniqueness. `problem56` shows that positive lengths
`ha, hb, hc` are the altitudes of some triangle exactly when `1/ha, 1/hb, 1/hc` satisfy the strict
triangle inequalities; Carroll leaves this condition tacit (it is what makes his two circles meet).
`problem56_unique` shows the triangle is determined up to congruence (its sides are determined).
`problem56_similar` is the key step of Carroll's proof: `a·ha = b·hb = c·hc = 2·area`, so the sides
are proportional to `1/ha, 1/hb, 1/hc`. That is why his auxiliary triangle, with sides
`α, α²/β, α²/γ`, is similar to the required one, which "the rest of the construction" then scales.

**Status.** proved
-/

namespace PillowProblems.P56

open scoped EuclideanGeometry

/-- `h` is the length of the altitude from `A` in the triangle `ABC`: there is a foot `F` on the
line `BC` with `AF ⊥ BC`, and `AF = h`. -/
def IsAltitude (A B C : Plane) (h : ℝ) : Prop :=
  ∃ F : Plane, (∃ t : ℝ, F = AffineMap.lineMap B C t) ∧ inner ℝ (A - F) (C - B) = 0 ∧
    dist A F = h

/-- `ABC` is a (non-degenerate) triangle whose altitudes from `A`, `B`, `C` are `ha`, `hb`, `hc`. -/
def HasAltitudes (A B C : Plane) (ha hb hc : ℝ) : Prop :=
  cross A B C ≠ 0 ∧ IsAltitude A B C ha ∧ IsAltitude B C A hb ∧ IsAltitude C A B hc

private lemma inner_eq (x y : Plane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

private lemma dist_sq (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma lineMap_apply' (A B : Plane) (t : ℝ) (i : Fin 2) :
    (AffineMap.lineMap A B t : Plane) i = A i + t * (B i - A i) := by
  simp [AffineMap.lineMap_apply]; ring

private lemma cross_cycle (A B C : Plane) : cross B C A = cross A B C := by
  unfold cross; ring

/-- Heron's formula, in the form `4 · (2·area)² = (a+b+c)(-a+b+c)(a-b+c)(a+b-c)`. -/
private lemma heron (A B C : Plane) :
    4 * cross A B C ^ 2 = (dist B C + dist C A + dist A B) * (-dist B C + dist C A + dist A B) *
      (dist B C - dist C A + dist A B) * (dist B C + dist C A - dist A B) := by
  have e : ∀ a b c : ℝ, (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) =
      2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 - (a ^ 2) ^ 2 - (b ^ 2) ^ 2 -
        (c ^ 2) ^ 2 := by intros; ring
  rw [e, dist_sq, dist_sq, dist_sq]
  unfold cross; ring

/-- In a non-degenerate triangle each side is less than the sum of the other two. -/
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

/-- The foot of a perpendicular: `AF · BC = 2·area(ABC)`. -/
private lemma alt_mul (A B C F : Plane) (t : ℝ) (hF : F = AffineMap.lineMap B C t)
    (hp : inner ℝ (A - F) (C - B) = 0) : dist A F * dist B C = |cross A B C| := by
  have key : (dist A F * dist B C) ^ 2 = |cross A B C| ^ 2 := by
    rw [sq_abs, mul_pow, dist_sq, dist_sq]
    rw [inner_eq] at hp
    subst hF
    simp only [PiLp.sub_apply, lineMap_apply'] at hp ⊢
    unfold cross
    linear_combination ((A 0 - (B 0 + t * (C 0 - B 0))) * (C 0 - B 0) +
      (A 1 - (B 1 + t * (C 1 - B 1))) * (C 1 - B 1)) * hp
  exact (sq_eq_sq₀ (by positivity) (abs_nonneg _)).1 key

private lemma isAltitude_iff (A B C : Plane) (hBC : B ≠ C) (h : ℝ) :
    IsAltitude A B C h ↔ h = |cross A B C| / dist B C := by
  have hd : 0 < dist B C := dist_pos.2 hBC
  constructor
  · rintro ⟨F, ⟨t, hF⟩, hp, rfl⟩
    rw [← alt_mul A B C F t hF hp]; field_simp
  · rintro rfl
    have hn : (C 0 - B 0) ^ 2 + (C 1 - B 1) ^ 2 ≠ 0 := by
      rw [← dist_sq, dist_comm]; exact (pow_pos hd 2).ne'
    set t := ((A 0 - B 0) * (C 0 - B 0) + (A 1 - B 1) * (C 1 - B 1)) /
      ((C 0 - B 0) ^ 2 + (C 1 - B 1) ^ 2) with ht
    have hp : inner ℝ (A - AffineMap.lineMap B C t) (C - B) = 0 := by
      rw [inner_eq]
      simp only [PiLp.sub_apply, lineMap_apply']
      rw [ht]; field_simp; ring
    refine ⟨_, ⟨t, rfl⟩, hp, ?_⟩
    rw [← alt_mul A B C _ t rfl hp]; field_simp

private lemma ne_of_cross {A B C : Plane} (h : cross A B C ≠ 0) : B ≠ C := by
  rintro rfl; apply h; unfold cross; ring

private lemma sides_pos (A B C : Plane) (h : cross A B C ≠ 0) :
    0 < dist B C ∧ 0 < dist C A ∧ 0 < dist A B :=
  ⟨dist_pos.2 (ne_of_cross h), dist_pos.2 (ne_of_cross (by rwa [cross_cycle] : cross B C A ≠ 0)),
    dist_pos.2 (ne_of_cross (by rwa [cross_cycle, cross_cycle] : cross C A B ≠ 0))⟩

/-- In a triangle with altitudes `ha, hb, hc` the sides are `|2·area| / h`. -/
private lemma sides (A B C : Plane) (ha hb hc : ℝ) (H : HasAltitudes A B C ha hb hc) :
    ha = |cross A B C| / dist B C ∧ hb = |cross A B C| / dist C A ∧
      hc = |cross A B C| / dist A B := by
  obtain ⟨h0, h1, h2, h3⟩ := H
  have h0' : cross B C A ≠ 0 := by rwa [cross_cycle]
  have h0'' : cross C A B ≠ 0 := by rwa [cross_cycle, cross_cycle]
  refine ⟨(isAltitude_iff A B C (ne_of_cross h0) ha).1 h1, ?_, ?_⟩
  · rw [(isAltitude_iff B C A (ne_of_cross h0') hb).1 h2, cross_cycle]
  · rw [(isAltitude_iff C A B (ne_of_cross h0'') hc).1 h3, cross_cycle, cross_cycle]

/-- **Problem 56 (Carroll's key step).** In any triangle the sides are inversely proportional to
the altitudes (`a · ha = b · hb = c · hc`, each being twice the area); so the triangle with sides
`1/ha, 1/hb, 1/hc` is similar to the required one. -/
theorem problem56_similar (A B C : Plane) (ha hb hc : ℝ) (H : HasAltitudes A B C ha hb hc) :
    dist B C * ha = 2 * triArea A B C ∧ dist C A * hb = 2 * triArea A B C ∧
      dist A B * hc = 2 * triArea A B C := by
  have h0 := H.1
  obtain ⟨e1, e2, e3⟩ := sides A B C ha hb hc H
  obtain ⟨hBC, hCA, hAB⟩ := sides_pos A B C h0
  unfold triArea
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; field_simp
  · rw [e2]; field_simp
  · rw [e3]; field_simp

/-- **Problem 56 (existence).** Three given lengths `ha, hb, hc > 0` are the altitudes of some
triangle exactly when their reciprocals satisfy the strict triangle inequalities (Carroll's two
circles then meet). -/
theorem problem56 (ha hb hc : ℝ) (pa : 0 < ha) (pb : 0 < hb) (pc : 0 < hc) :
    (∃ A B C : Plane, HasAltitudes A B C ha hb hc) ↔
      (1 / ha < 1 / hb + 1 / hc ∧ 1 / hb < 1 / hc + 1 / ha ∧ 1 / hc < 1 / ha + 1 / hb) := by
  constructor
  · rintro ⟨A, B, C, H⟩
    have h0 := H.1
    obtain ⟨e1, e2, e3⟩ := sides A B C ha hb hc H
    have hK : 0 < |cross A B C| := abs_pos.2 h0
    have t1 := tri_strict A B C h0
    have t2 := tri_strict B C A (by rwa [cross_cycle])
    have t3 := tri_strict C A B (by rwa [cross_cycle, cross_cycle])
    obtain ⟨hBC, hCA, hAB⟩ := sides_pos A B C h0
    rw [e1, e2, e3]
    simp only [one_div_div]
    refine ⟨?_, ?_, ?_⟩
    · rw [← add_div]; exact div_lt_div_of_pos_right t1 hK
    · rw [← add_div]; exact div_lt_div_of_pos_right (by linarith) hK
    · rw [← add_div]; exact div_lt_div_of_pos_right (by linarith) hK
  · rintro ⟨t1, t2, t3⟩
    set u := 1 / ha with hu
    set v := 1 / hb with hv
    set w := 1 / hc with hw
    have up : 0 < u := by positivity
    have vp : 0 < v := by positivity
    have wp : 0 < w := by positivity
    set x := (u ^ 2 + w ^ 2 - v ^ 2) / (2 * u) with hx
    have hy2 : 0 < w ^ 2 - x ^ 2 := by
      have e : w ^ 2 - x ^ 2 =
          (v - u + w) * (v + u - w) * (u + w - v) * (u + v + w) / (4 * u ^ 2) := by
        rw [hx]; field_simp; ring
      rw [e]
      have : 0 < v - u + w := by linarith
      have : 0 < v + u - w := by linarith
      have : 0 < u + w - v := by linarith
      positivity
    set y := Real.sqrt (w ^ 2 - x ^ 2) with hy
    have yp : 0 < y := Real.sqrt_pos.2 hy2
    have yy : y ^ 2 = w ^ 2 - x ^ 2 := Real.sq_sqrt hy2.le
    set l := 1 / (u * y) with hl
    have lp : 0 < l := by positivity
    refine ⟨pt (l * x) (l * y), pt 0 0, pt (l * u) 0, ?_⟩
    have hcr : cross (pt (l * x) (l * y)) (pt 0 0) (pt (l * u) 0) = l := by
      unfold cross; simp only [pt_zero, pt_one]
      rw [hl]; field_simp; ring
    have hcr' : |cross (pt (l * x) (l * y)) (pt 0 0) (pt (l * u) 0)| = l := by
      rw [hcr, abs_of_pos lp]
    have dBC : dist (pt 0 0) (pt (l * u) 0) = l * u := by
      rw [← sq_eq_sq₀ dist_nonneg (by positivity), dist_sq]; simp only [pt_zero, pt_one]; ring
    have dCA : dist (pt (l * u) 0) (pt (l * x) (l * y)) = l * v := by
      rw [← sq_eq_sq₀ dist_nonneg (by positivity), dist_sq]; simp only [pt_zero, pt_one]
      have : (u - x) ^ 2 + y ^ 2 = v ^ 2 := by rw [yy, hx]; field_simp; ring
      linear_combination l ^ 2 * this
    have dAB : dist (pt (l * x) (l * y)) (pt 0 0) = l * w := by
      rw [← sq_eq_sq₀ dist_nonneg (by positivity), dist_sq]; simp only [pt_zero, pt_one]
      linear_combination l ^ 2 * yy
    have hl0 : l ≠ 0 := lp.ne'
    refine ⟨by rw [hcr]; exact hl0, ?_, ?_, ?_⟩
    · rw [isAltitude_iff _ _ _ (ne_of_cross (by rw [hcr]; exact hl0)), hcr', dBC, hu]
      field_simp
    · have h' : cross (pt 0 0) (pt (l * u) 0) (pt (l * x) (l * y)) ≠ 0 := by
        rw [cross_cycle, hcr]; exact hl0
      rw [isAltitude_iff _ _ _ (ne_of_cross h'), cross_cycle, hcr', dCA, hv]
      field_simp
    · have h' : cross (pt (l * u) 0) (pt (l * x) (l * y)) (pt 0 0) ≠ 0 := by
        rw [cross_cycle, cross_cycle, hcr]; exact hl0
      rw [isAltitude_iff _ _ _ (ne_of_cross h'), cross_cycle, cross_cycle, hcr', dAB, hw]
      field_simp

/-- **Problem 56 (uniqueness).** The triangle is determined by its altitudes up to congruence:
two triangles with the same altitudes have the same sides. -/
theorem problem56_unique (A B C A' B' C' : Plane) (ha hb hc : ℝ)
    (H : HasAltitudes A B C ha hb hc) (H' : HasAltitudes A' B' C' ha hb hc) :
    dist B C = dist B' C' ∧ dist C A = dist C' A' ∧ dist A B = dist A' B' := by
  -- with `K = 2·area`, the sides are `K/ha, K/hb, K/hc`, and Heron's formula fixes `K`
  have key : ∀ (A B C : Plane), HasAltitudes A B C ha hb hc →
      dist B C = |cross A B C| * (1 / ha) ∧ dist C A = |cross A B C| * (1 / hb) ∧
      dist A B = |cross A B C| * (1 / hc) ∧ 0 < |cross A B C| ∧
      |cross A B C| ^ 2 * ((1 / ha + 1 / hb + 1 / hc) * (-(1 / ha) + 1 / hb + 1 / hc) *
        (1 / ha - 1 / hb + 1 / hc) * (1 / ha + 1 / hb - 1 / hc)) = 4 := by
    intro A B C H
    have h0 := H.1
    obtain ⟨e1, e2, e3⟩ := sides A B C ha hb hc H
    have hK : 0 < |cross A B C| := abs_pos.2 h0
    obtain ⟨hBC, hCA, hAB⟩ := sides_pos A B C h0
    have f1 : dist B C = |cross A B C| * (1 / ha) := by rw [e1]; field_simp
    have f2 : dist C A = |cross A B C| * (1 / hb) := by rw [e2]; field_simp
    have f3 : dist A B = |cross A B C| * (1 / hc) := by rw [e3]; field_simp
    refine ⟨f1, f2, f3, hK, ?_⟩
    have hr := heron A B C
    rw [← sq_abs, f1, f2, f3] at hr
    have hK2 : |cross A B C| ^ 2 ≠ 0 := by positivity
    apply mul_left_cancel₀ hK2
    linear_combination -hr
  obtain ⟨a1, a2, a3, aK, aQ⟩ := key A B C H
  obtain ⟨b1, b2, b3, bK, bQ⟩ := key A' B' C' H'
  have hKK : |cross A B C| = |cross A' B' C'| := by
    have hQ : ((1 / ha + 1 / hb + 1 / hc) * (-(1 / ha) + 1 / hb + 1 / hc) *
        (1 / ha - 1 / hb + 1 / hc) * (1 / ha + 1 / hb - 1 / hc)) ≠ 0 := by
      intro h0; rw [h0] at aQ; norm_num at aQ
    have : |cross A B C| ^ 2 = |cross A' B' C'| ^ 2 :=
      mul_right_cancel₀ hQ (aQ.trans bQ.symm)
    exact (sq_eq_sq₀ aK.le bK.le).1 this
  refine ⟨?_, ?_, ?_⟩
  · rw [a1, b1, hKK]
  · rw [a2, b2, hKK]
  · rw [a3, b3, hKK]

end PillowProblems.P56
