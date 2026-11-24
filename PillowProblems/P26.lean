import PillowProblems.Basic

/-!
# Problem 26 (Pure Geometry, Plane)

**Question.** *(dated 4/89)*

> Within a given Triangle place a similar Triangle, whose area shall have to its area a given ratio less than unity, whose sides shall be parallel to its sides, and whose vertices shall be equidistant from its vertices.

*(Carroll's solution: Chapter III, problem 26; text in `data/problems.json`.)*

**Lean reading.** `ABC` is a nondegenerate triangle (`cross A B C ≠ 0`). "Similar, with sides
parallel to its sides" is modelled as `B' - A'`, `C' - B'`, `A' - C'` being multiples of
`B - A`, `C - B`, `A - C` (similarity then follows). The area condition is
`triArea A'B'C' = ρ · triArea ABC` with `0 < ρ < 1`, and the vertices are equidistant:
`AA' = BB' = CC'`. "Within" means each of `A'`, `B'`, `C'` lies in the closed triangle
(`convexHull`). `D` is any point equidistant from `A`, `B`, `C` (Carroll's intersection of the
perpendicular bisectors); the answer is not built into it. `problem26_all` shows, with no
further assumption, that the solutions without the "within" condition are exactly the
homotheties of centre `D` and ratio `±√ρ`. Carroll's reading is that the placed triangle keeps
the orientation of `ABC` (sides parallel in the same sense, `SidesParallelSameSense`); under it
`problem26` proves that a solution exists exactly when the circumcentre `D` lies within `ABC`
(no obtuse angle), and that it is then Carroll's triangle `A' = D + √ρ (A - D)`, …, uniquely.
Carroll does not notice that for an obtuse-angled triangle his construction leaves the triangle
and there is no solution at all. `problem26_literal` treats the literal reading, where the ratio
`-√ρ` (a triangle turned half round, which Carroll does not consider) is a further solution
whenever its vertices lie within `ABC` (e.g. for small `ρ` in an acute triangle).

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P26

open EuclideanGeometry

private lemma dist_sq' (x y : Plane) : dist x y ^ 2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

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

private lemma indepT {u0 u1 v0 v1 p q : ℝ} (h : u0 * v1 - v0 * u1 ≠ 0)
    (h0 : p * u0 + q * u1 = 0) (h1 : p * v0 + q * v1 = 0) : p = 0 ∧ q = 0 := by
  constructor
  · have : p * (u0 * v1 - v0 * u1) = 0 := by linear_combination v1 * h0 - u1 * h1
    simpa [h] using this
  · have : q * (u0 * v1 - v0 * u1) = 0 := by linear_combination u0 * h1 - v0 * h0
    simpa [h] using this

/-- The sides of `A'B'C'` are parallel to the corresponding sides of `ABC`. -/
def SidesParallel (A B C A' B' C' : Plane) : Prop :=
  (∃ l : ℝ, B' - A' = l • (B - A)) ∧ (∃ l : ℝ, C' - B' = l • (C - B)) ∧
    (∃ l : ℝ, A' - C' = l • (A - C))

/-- The sides of `A'B'C'` are parallel to, and point the same way as, the corresponding sides
of `ABC` (so `A'B'C'` is not turned half round). -/
def SidesParallelSameSense (A B C A' B' C' : Plane) : Prop :=
  (∃ l : ℝ, 0 < l ∧ B' - A' = l • (B - A)) ∧ (∃ l : ℝ, 0 < l ∧ C' - B' = l • (C - B)) ∧
    (∃ l : ℝ, 0 < l ∧ A' - C' = l • (A - C))

private lemma core (A B C D A' B' C' : Plane) (hABC : cross A B C ≠ 0)
    (hDB : dist D A = dist D B) (hDC : dist D A = dist D C) {ρ : ℝ} (hρ1 : ρ < 1)
    (hpar : SidesParallel A B C A' B' C') (harea : triArea A' B' C' = ρ * triArea A B C)
    (hB : dist A A' = dist B B') (hC : dist A A' = dist C C') :
    ∃ k : ℝ, k ^ 2 = ρ ∧ B' - A' = k • (B - A) ∧
      A' = D + k • (A - D) ∧ B' = D + k • (B - D) ∧ C' = D + k • (C - D) := by
  obtain ⟨⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩⟩ := hpar
  obtain ⟨p1, p1'⟩ := vec_coord h1
  obtain ⟨p2, p2'⟩ := vec_coord h2
  obtain ⟨p3, p3'⟩ := vec_coord h3
  have hc := hABC
  unfold cross at hc
  obtain ⟨e1, e2⟩ := indep (p := l1 - l2) (q := l2 - l3) hc
    (by linear_combination -p1 - p2 - p3) (by linear_combination -p1' - p2' - p3')
  have hl2 : l2 = l1 := by linarith
  have hl3 : l3 = l1 := by linarith
  rw [hl2] at h2 p2 p2'
  rw [hl3] at h3 p3 p3'
  have q0 : B' 0 = A' 0 + l1 * (B 0 - A 0) := by linear_combination p1
  have q1 : B' 1 = A' 1 + l1 * (B 1 - A 1) := by linear_combination p1'
  have r0 : C' 0 = A' 0 + l1 * (C 0 - A 0) := by linear_combination p1 + p2
  have r1 : C' 1 = A' 1 + l1 * (C 1 - A 1) := by linear_combination p1' + p2'
  have hcr : cross A' B' C' = l1 ^ 2 * cross A B C := by
    unfold cross; rw [q0, q1, r0, r1]; ring
  have hl1 : l1 ^ 2 = ρ := by
    unfold triArea at harea
    rw [hcr, abs_mul, abs_of_nonneg (sq_nonneg l1)] at harea
    have : 0 < |cross A B C| := abs_pos.2 hABC
    field_simp at harea
    nlinarith
  have hκ : 1 - l1 ≠ 0 := by
    intro h; obtain rfl : l1 = 1 := by linarith
    linarith
  have sB := congrArg (· ^ 2) hB
  have sC := congrArg (· ^ 2) hC
  have tB := congrArg (· ^ 2) hDB
  have tC := congrArg (· ^ 2) hDC
  simp only [dist_sq'] at sB sC tB tC
  rw [q0, q1] at sB
  rw [r0, r1] at sC
  obtain ⟨f0, f1⟩ := indepT (p := A' 0 - l1 * A 0 - (1 - l1) * D 0)
    (q := A' 1 - l1 * A 1 - (1 - l1) * D 1) hc
    (by
      have : 2 * (1 - l1) * ((A' 0 - l1 * A 0 - (1 - l1) * D 0) * (B 0 - A 0) +
          (A' 1 - l1 * A 1 - (1 - l1) * D 1) * (B 1 - A 1)) = 0 := by
        linear_combination sB - (1 - l1) ^ 2 * tB
      simpa [hκ] using this)
    (by
      have : 2 * (1 - l1) * ((A' 0 - l1 * A 0 - (1 - l1) * D 0) * (C 0 - A 0) +
          (A' 1 - l1 * A 1 - (1 - l1) * D 1) * (C 1 - A 1)) = 0 := by
        linear_combination sC - (1 - l1) ^ 2 * tC
      simpa [hκ] using this)
  refine ⟨l1, hl1, h1, ?_, ?_, ?_⟩ <;>
    (ext i; fin_cases i <;> simp [q0, q1, r0, r1] <;> first | linear_combination f0 | linear_combination f1)

private lemma cross_hom (A B C D : Plane) (k : ℝ) :
    cross (D + k • (A - D)) (D + k • (B - D)) (D + k • (C - D)) = k ^ 2 * cross A B C := by
  unfold cross; simp; ring

private lemma dist_hom (A D : Plane) (k : ℝ) : dist A (D + k • (A - D)) = |1 - k| * dist D A := by
  rw [dist_eq_norm, show A - (D + k • (A - D)) = (1 - k) • (A - D) by module, norm_smul,
    Real.norm_eq_abs, ← dist_eq_norm, dist_comm]

/-- **Problem 26, all solutions.** With `D` the circumcentre of `ABC`, a triangle `A'B'C'` with
sides parallel to those of `ABC`, area `ρ` times that of `ABC` (`0 < ρ < 1`) and
`AA' = BB' = CC'` is the image of `ABC` under the homothety of centre `D` and ratio `√ρ` or
`-√ρ`. -/
theorem problem26_all (A B C D : Plane) (hABC : cross A B C ≠ 0)
    (hD : dist D A = dist D B ∧ dist D B = dist D C) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (A' B' C' : Plane) :
    (SidesParallel A B C A' B' C' ∧ triArea A' B' C' = ρ * triArea A B C ∧
        dist A A' = dist B B' ∧ dist B B' = dist C C') ↔
      ∃ k : ℝ, (k = √ρ ∨ k = -√ρ) ∧
        A' = D + k • (A - D) ∧ B' = D + k • (B - D) ∧ C' = D + k • (C - D) := by
  constructor
  · rintro ⟨hpar, harea, h1, h2⟩
    obtain ⟨k, hk, -, hA', hB', hC'⟩ :=
      core A B C D A' B' C' hABC hD.1 (hD.1.trans hD.2) hρ1 hpar harea h1 (h1.trans h2)
    refine ⟨k, ?_, hA', hB', hC'⟩
    have : k ^ 2 = (√ρ) ^ 2 := by rw [Real.sq_sqrt hρ0.le, hk]
    exact sq_eq_sq_iff_eq_or_eq_neg.1 this
  · rintro ⟨k, hk, rfl, rfl, rfl⟩
    have hk2 : k ^ 2 = ρ := by rcases hk with rfl | rfl <;> simp [Real.sq_sqrt hρ0.le]
    refine ⟨⟨⟨k, by module⟩, ⟨k, by module⟩, ⟨k, by module⟩⟩, ?_, ?_, ?_⟩
    · unfold triArea; rw [cross_hom, abs_mul, abs_of_nonneg (sq_nonneg _), hk2]; ring
    · rw [dist_hom, dist_hom, hD.1]
    · rw [dist_hom, dist_hom, hD.2]

private lemma cross_affine (x y Q R : Plane) (a b : ℝ) (hab : a + b = 1) :
    cross (a • x + b • y) Q R = a * cross x Q R + b * cross y Q R := by
  obtain rfl : b = 1 - a := by linarith
  unfold cross; simp; ring

/-- The closed triangle `PQR` lies in the closed half-plane of `QR` containing `P`. -/
private lemma hull_halfplane (P Q R : Plane) :
    ∀ X ∈ convexHull ℝ ({P, Q, R} : Set Plane), 0 ≤ cross X Q R * cross P Q R := by
  intro X hX
  have hconv : Convex ℝ {X : Plane | 0 ≤ cross X Q R * cross P Q R} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [cross_affine x y Q R a b hab]
    nlinarith [mul_nonneg ha hx, mul_nonneg hb hy]
  refine convexHull_min ?_ hconv hX
  intro Y hY
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY
  simp only [Set.mem_ofPred_eq]
  rcases hY with rfl | rfl | rfl
  · exact mul_self_nonneg _
  · have : cross Y Y R = 0 := by unfold cross; ring
    rw [this, zero_mul]
  · have : cross Y Q Y = 0 := by unfold cross; ring
    rw [this, zero_mul]

/-- If the three images of the vertices under the homothety of centre `D` and ratio `s < 1`
lie in the closed triangle, so does `D`. -/
private lemma center_mem_hull (A B C D : Plane) (hABC : cross A B C ≠ 0) (s : ℝ) (hs1 : s < 1)
    (hA : D + s • (A - D) ∈ convexHull ℝ ({A, B, C} : Set Plane))
    (hB : D + s • (B - D) ∈ convexHull ℝ ({A, B, C} : Set Plane))
    (hC : D + s • (C - D) ∈ convexHull ℝ ({A, B, C} : Set Plane)) :
    D ∈ convexHull ℝ ({A, B, C} : Set Plane) := by
  have e1 : ({B, C, A} : Set Plane) = {A, B, C} := by ext; simp; tauto
  have e2 : ({C, A, B} : Set Plane) = {A, B, C} := by ext; simp; tauto
  have hα := hull_halfplane A B C _ hB
  have hβ := hull_halfplane B C A _ (e1 ▸ hC)
  have hγ := hull_halfplane C A B _ (e2 ▸ hA)
  have c1 : cross (D + s • (B - D)) B C = (1 - s) * cross D B C := by unfold cross; simp; ring
  have c2 : cross (D + s • (C - D)) C A = (1 - s) * cross D C A := by unfold cross; simp; ring
  have c3 : cross (D + s • (A - D)) A B = (1 - s) * cross D A B := by unfold cross; simp; ring
  have k2 : cross B C A = cross A B C := by unfold cross; ring
  have k3 : cross C A B = cross A B C := by unfold cross; ring
  rw [c1] at hα; rw [c2, k2] at hβ; rw [c3, k3] at hγ
  have h1s : 0 < 1 - s := by linarith
  have ha := (mul_nonneg_iff_of_pos_left h1s).1 (by rw [← mul_assoc]; exact hα)
  have hb := (mul_nonneg_iff_of_pos_left h1s).1 (by rw [← mul_assoc]; exact hβ)
  have hc := (mul_nonneg_iff_of_pos_left h1s).1 (by rw [← mul_assoc]; exact hγ)
  have hK2 : 0 < cross A B C ^ 2 := by positivity
  have hw : ∀ t : ℝ, 0 ≤ t * cross A B C → 0 ≤ t / cross A B C := by
    intro t ht
    rw [show t / cross A B C = t * cross A B C / cross A B C ^ 2 by field_simp]
    exact div_nonneg ht hK2.le
  have hmem := (convex_convexHull ℝ ({A, B, C} : Set Plane)).sum_mem (t := Finset.univ)
    (w := ![cross D B C / cross A B C, cross D C A / cross A B C, cross D A B / cross A B C])
    (z := ![A, B, C]) ?_ ?_ ?_
  · convert hmem using 1
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    ext i; fin_cases i <;> simp <;> field_simp <;> unfold cross <;> ring
  · intro i _; fin_cases i
    · exact hw _ ha
    · exact hw _ hb
    · exact hw _ hc
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    field_simp; unfold cross; ring
  · intro i _; fin_cases i <;> exact subset_convexHull ℝ _ (by simp)

/-- **Problem 26.** The triangles within `ABC`, with sides parallel to its sides in the same
sense, area `ρ` times its area and vertices equidistant from its vertices, are as follows: there
is one exactly when the circumcentre `D` lies within `ABC` (no obtuse angle), and it is then
Carroll's, `A' = D + √ρ (A - D)`, `B' = D + √ρ (B - D)`, `C' = D + √ρ (C - D)`
(`DB' = k · DB`, `k = √ρ`). For an obtuse-angled triangle there is none. -/
theorem problem26 (A B C D : Plane) (hABC : cross A B C ≠ 0)
    (hD : dist D A = dist D B ∧ dist D B = dist D C)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (A' B' C' : Plane) :
    (SidesParallelSameSense A B C A' B' C' ∧ triArea A' B' C' = ρ * triArea A B C ∧
        dist A A' = dist B B' ∧ dist B B' = dist C C' ∧
        A' ∈ convexHull ℝ {A, B, C} ∧ B' ∈ convexHull ℝ {A, B, C} ∧
        C' ∈ convexHull ℝ {A, B, C}) ↔
      (D ∈ convexHull ℝ {A, B, C} ∧
        A' = D + √ρ • (A - D) ∧ B' = D + √ρ • (B - D) ∧ C' = D + √ρ • (C - D)) := by
  have hs0 : 0 < √ρ := Real.sqrt_pos.2 hρ0
  have hs1 : √ρ < 1 := (Real.sqrt_lt' one_pos).2 (by simpa using hρ1)
  constructor
  · rintro ⟨⟨⟨l1, hl1, h1⟩, ⟨l2, -, h2⟩, ⟨l3, -, h3⟩⟩, harea, hd1, hd2, hA'in, hB'in, hC'in⟩
    obtain ⟨k, hk, hkp, hA', hB', hC'⟩ := core A B C D A' B' C' hABC hD.1 (hD.1.trans hD.2) hρ1
      ⟨⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩⟩ harea hd1 (hd1.trans hd2)
    obtain ⟨e0, e1⟩ := vec_coord h1
    obtain ⟨f0, f1⟩ := vec_coord hkp
    have hc := hABC
    unfold cross at hc
    have hlk : l1 - k = 0 := (indep (p := l1 - k) (q := 0) hc
      (by linear_combination f0 - e0) (by linear_combination f1 - e1)).1
    have hk' : k = √ρ := by
      rw [← hk, Real.sqrt_sq (by linarith)]
    subst hk'
    refine ⟨center_mem_hull A B C D hABC _ hs1 (hA' ▸ hA'in) (hB' ▸ hB'in) (hC' ▸ hC'in),
      hA', hB', hC'⟩
  · rintro ⟨hDin, hA', hB', hC'⟩
    obtain ⟨⟨⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩⟩, harea, hd1, hd2⟩ :=
      (problem26_all A B C D hABC hD ρ hρ0 hρ1 A' B' C').2 ⟨√ρ, Or.inl rfl, hA', hB', hC'⟩
    have hmem : ∀ X ∈ ({A, B, C} : Set Plane), D + √ρ • (X - D) ∈ convexHull ℝ {A, B, C} :=
      fun X hX => (convex_convexHull ℝ _).add_smul_sub_mem hDin (subset_convexHull ℝ _ hX)
        ⟨hs0.le, hs1.le⟩
    subst hA' hB' hC'
    refine ⟨⟨⟨√ρ, hs0, by module⟩, ⟨√ρ, hs0, by module⟩, ⟨√ρ, hs0, by module⟩⟩, harea, hd1, hd2,
      hmem A (by simp), hmem B (by simp), hmem C (by simp)⟩

/-- **Problem 26, literal reading.** If "sides parallel" allows the placed triangle to be turned
half round, the solutions within `ABC` are Carroll's triangle (when the circumcentre `D` lies
within `ABC`) and, in addition, the image of `ABC` under the homothety of centre `D` and ratio
`-√ρ`, whenever that image lies within `ABC`. -/
theorem problem26_literal (A B C D : Plane) (hABC : cross A B C ≠ 0)
    (hD : dist D A = dist D B ∧ dist D B = dist D C)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (A' B' C' : Plane) :
    (SidesParallel A B C A' B' C' ∧ triArea A' B' C' = ρ * triArea A B C ∧
        dist A A' = dist B B' ∧ dist B B' = dist C C' ∧
        A' ∈ convexHull ℝ {A, B, C} ∧ B' ∈ convexHull ℝ {A, B, C} ∧
        C' ∈ convexHull ℝ {A, B, C}) ↔
      ((D ∈ convexHull ℝ {A, B, C} ∧
          A' = D + √ρ • (A - D) ∧ B' = D + √ρ • (B - D) ∧ C' = D + √ρ • (C - D)) ∨
        (A' = D + (-√ρ) • (A - D) ∧ B' = D + (-√ρ) • (B - D) ∧ C' = D + (-√ρ) • (C - D) ∧
          A' ∈ convexHull ℝ {A, B, C} ∧ B' ∈ convexHull ℝ {A, B, C} ∧
          C' ∈ convexHull ℝ {A, B, C})) := by
  have hs1 : √ρ < 1 := (Real.sqrt_lt' one_pos).2 (by simpa using hρ1)
  have hs0 : 0 < √ρ := Real.sqrt_pos.2 hρ0
  constructor
  · rintro ⟨hpar, harea, hd1, hd2, hA'in, hB'in, hC'in⟩
    obtain ⟨k, hk, hA', hB', hC'⟩ :=
      (problem26_all A B C D hABC hD ρ hρ0 hρ1 A' B' C').1 ⟨hpar, harea, hd1, hd2⟩
    rcases hk with rfl | rfl
    · exact Or.inl ⟨center_mem_hull A B C D hABC _ hs1 (hA' ▸ hA'in) (hB' ▸ hB'in)
        (hC' ▸ hC'in), hA', hB', hC'⟩
    · exact Or.inr ⟨hA', hB', hC', hA'in, hB'in, hC'in⟩
  · rintro (h | ⟨hA', hB', hC', hA'in, hB'in, hC'in⟩)
    · obtain ⟨⟨⟨l1, -, h1⟩, ⟨l2, -, h2⟩, ⟨l3, -, h3⟩⟩, rest⟩ :=
        (problem26 A B C D hABC hD ρ hρ0 hρ1 A' B' C').2 h
      exact ⟨⟨⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩⟩, rest⟩
    · obtain ⟨hpar, harea, hd1, hd2⟩ :=
        (problem26_all A B C D hABC hD ρ hρ0 hρ1 A' B' C').2 ⟨-√ρ, Or.inr rfl, hA', hB', hC'⟩
      exact ⟨hpar, harea, hd1, hd2, hA'in, hB'in, hC'in⟩

/-- The hypotheses of `problem26` are satisfiable (a right isosceles triangle). -/
theorem problem26_nonvacuous :
    ∃ A B C D : Plane, cross A B C ≠ 0 ∧ (dist D A = dist D B ∧ dist D B = dist D C) ∧
      D ∈ convexHull ℝ {A, B, C} := by
  refine ⟨pt 0 0, pt 2 0, pt 0 2, pt 1 1, by norm_num [cross], ⟨?_, ?_⟩, ?_⟩
  · rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, dist_sq', dist_sq']; norm_num
  · rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, dist_sq', dist_sq']; norm_num
  · refine segment_subset_convexHull (x := pt 2 0) (y := pt 0 2) (by simp) (by simp) ⟨1/2, 1/2, by norm_num, by norm_num,
      by norm_num, ?_⟩
    ext i; fin_cases i <;> simp

end PillowProblems.P26
