import PillowProblems.Basic

/-!
# Problem 63 (Trigonometry: Solid)

**Question.** *(dated 3, 4/9/90)*

> Given 2 equal Squares, in different horizontal planes, having their centres in the same vertical line, and so placed that the sides of each are parallel to the diagonals of the other, and at such a distance apart that, by joining neighbouring vertices, 8 equilateral Triangles are formed: find the volume of the solid thus enclosed.

**Answer.**

> If each side of each Square = 2, the volume = \[ \frac{8.2^{\tfrac{1}{4}}.(\sqrt{2}+1)}{3}. \]

*(Carroll's solution: Chapter III, problem 63; text in `data/problems.json`.)*

**Lean reading.** As in Carroll's answer the squares have side `2`. Up to a rigid motion we take
the common vertical line to be the `z`-axis, the lower square in the plane `z = 0` with vertices
`L i = (±1, ±1, 0)`, and the upper square in the plane `z = h` (`h > 0` is the unknown distance
apart); its sides are parallel to the diagonals of the lower one, so its vertices are
`U h i = (±√2, 0, h), (0, ±√2, h)` (both 45° turns give this same square). "Neighbouring
vertices" are joined: the lower vertex `L i` lies between `U h i` and `U h (i+1)`, so the eight
triangles are `L i L (i+1) U (i+1)` and `U i U (i+1) L i`. The volume of the enclosed solid (a
square antiprism) is computed as in Carroll's solution: it is convex and contains its centre
`O = (0, 0, h/2)`, so it is the union of the pyramids with apex `O` over its ten faces; each is a
tetrahedron (a square face is cut into two triangles) whose volume is
`|(B - A) · ((C - A) × (D - A))| / 6`. The theorem proves both that the triangles are equilateral
exactly when `h = 2^{3/4}` (Carroll's `LM`), and that the volume is then Carroll's value.

**Status.** proved
-/

namespace PillowProblems.P63

/-- The point `(x, y, z)` of space. -/
noncomputable def sp (x y z : ℝ) : Space := !₂[x, y, z]

@[simp] private lemma sp_zero (x y z : ℝ) : sp x y z 0 = x := rfl
@[simp] private lemma sp_one (x y z : ℝ) : sp x y z 1 = y := rfl
@[simp] private lemma sp_two (x y z : ℝ) : sp x y z 2 = z := rfl

/-- The triple product `(B - A) · ((C - A) × (D - A))`: six times the signed volume of the
tetrahedron `ABCD`. -/
noncomputable def triple (A B C D : Space) : ℝ :=
  (B 0 - A 0) * ((C 1 - A 1) * (D 2 - A 2) - (C 2 - A 2) * (D 1 - A 1))
  - (B 1 - A 1) * ((C 0 - A 0) * (D 2 - A 2) - (C 2 - A 2) * (D 0 - A 0))
  + (B 2 - A 2) * ((C 0 - A 0) * (D 1 - A 1) - (C 1 - A 1) * (D 0 - A 0))

/-- The volume of the tetrahedron `ABCD`. -/
noncomputable def tetVol (A B C D : Space) : ℝ := |triple A B C D| / 6

/-- The vertices of the lower square (side `2`, centre on the `z`-axis, in the plane `z = 0`),
in cyclic order. -/
noncomputable def L : Fin 4 → Space :=
  ![sp 1 1 0, sp (-1) 1 0, sp (-1) (-1) 0, sp 1 (-1) 0]

/-- The vertices of the upper square (side `2`, centre on the `z`-axis, in the plane `z = h`,
sides parallel to the diagonals of the lower square), in cyclic order. -/
noncomputable def U (h : ℝ) : Fin 4 → Space :=
  ![sp √2 0 h, sp 0 √2 h, sp (-√2) 0 h, sp 0 (-√2) h]

/-- The centre of the solid. -/
noncomputable def O (h : ℝ) : Space := sp 0 0 (h / 2)

/-- The triangle `PQR` is equilateral. -/
def Equilateral (P Q R : Space) : Prop := dist P Q = dist Q R ∧ dist Q R = dist R P

/-- Joining neighbouring vertices of the two squares gives eight equilateral triangles. -/
def EightEquilateral (h : ℝ) : Prop :=
  ∀ i : Fin 4, Equilateral (L i) (L (i + 1)) (U h (i + 1)) ∧ Equilateral (U h i) (U h (i + 1)) (L i)

/-- The volume of the solid enclosed by the two squares and the eight triangles: the sum of the
pyramids with apex the centre `O h` on its faces (each square face cut into two triangles). -/
noncomputable def solidVol (h : ℝ) : ℝ :=
  (∑ i : Fin 4, (tetVol (O h) (L i) (L (i + 1)) (U h (i + 1))
      + tetVol (O h) (U h i) (U h (i + 1)) (L i)))
    + (tetVol (O h) (L 0) (L 1) (L 2) + tetVol (O h) (L 0) (L 2) (L 3))
    + (tetVol (O h) (U h 0) (U h 1) (U h 2) + tetVol (O h) (U h 0) (U h 2) (U h 3))

private lemma dist_sp (x y z x' y' z' : ℝ) :
    dist (sp x y z) (sp x' y' z') = √((x - x') ^ 2 + (y - y') ^ 2 + (z - z') ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp [Real.dist_eq, sq_abs]

private lemma r2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private lemma baseL (i : Fin 4) : dist (L i) (L (i + 1)) = 2 := by
  have : √4 = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  fin_cases i <;> simp [L, dist_sp] <;> norm_num [this]

private lemma baseU (h : ℝ) (i : Fin 4) : dist (U h i) (U h (i + 1)) = 2 := by
  have : √4 = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  fin_cases i <;> simp [U, dist_sp] <;> rw [← this] <;> congr 1 <;> linarith [r2]

private lemma lat1 (h : ℝ) (i : Fin 4) : dist (L i) (U h i) = √(4 - 2 * √2 + h ^ 2) := by
  fin_cases i <;> simp [L, U, dist_sp] <;> congr 1 <;> linarith [r2]

private lemma lat2 (h : ℝ) (i : Fin 4) :
    dist (L i) (U h (i + 1)) = √(4 - 2 * √2 + h ^ 2) := by
  fin_cases i <;> simp [L, U, dist_sp] <;> congr 1 <;> linarith [r2]

private lemma lat1' (h : ℝ) (i : Fin 4) : dist (U h i) (L i) = √(4 - 2 * √2 + h ^ 2) := by
  rw [dist_comm, lat1]

private lemma lat2' (h : ℝ) (i : Fin 4) :
    dist (U h (i + 1)) (L i) = √(4 - 2 * √2 + h ^ 2) := by
  rw [dist_comm, lat2]

private lemma eight_iff (h : ℝ) : EightEquilateral h ↔ 2 = √(4 - 2 * √2 + h ^ 2) := by
  simp only [EightEquilateral, Equilateral, baseL, baseU, lat1, lat2', and_true,
    and_self, forall_const]

private lemma vol_eq (h : ℝ) (hh : 0 < h) : solidVol h = 4 * h * (√2 + 2) / 3 := by
  have hr := r2
  have rpos : 0 < √2 := by positivity
  have a1 : ∀ i : Fin 4, tetVol (O h) (L i) (L (i + 1)) (U h (i + 1)) = (h * √2 + h) / 6 := by
    intro i
    rw [tetVol, abs_of_pos] <;> fin_cases i <;> simp [L, U, O, triple] <;> ring_nf <;>
      nlinarith [mul_pos hh rpos]
  have a2 : ∀ i : Fin 4, tetVol (O h) (U h i) (U h (i + 1)) (L i) = (h * √2 + h) / 6 := by
    intro i
    rw [tetVol, abs_of_neg] <;> fin_cases i <;> simp [L, U, O, triple] <;> ring_nf <;>
      nlinarith [mul_pos hh rpos]
  have a3 : tetVol (O h) (L 0) (L 1) (L 2) = 2 * h / 6 := by
    rw [tetVol, abs_of_neg] <;> simp [L, O, triple] <;> ring_nf
    nlinarith
  have a4 : tetVol (O h) (L 0) (L 2) (L 3) = 2 * h / 6 := by
    rw [tetVol, abs_of_neg] <;> simp [L, O, triple] <;> ring_nf
    nlinarith
  have a5 : tetVol (O h) (U h 0) (U h 1) (U h 2) = 2 * h / 6 := by
    rw [tetVol, abs_of_pos] <;> simp [U, O, triple] <;> ring_nf <;> nlinarith
  have a6 : tetVol (O h) (U h 0) (U h 2) (U h 3) = 2 * h / 6 := by
    rw [tetVol, abs_of_pos] <;> simp [U, O, triple] <;> ring_nf <;> nlinarith
  rw [solidVol, a3, a4, a5, a6]
  simp only [a1, a2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- **Problem 63.** With squares of side `2`: the eight triangles are equilateral exactly when
the squares are `2^{3/4}` apart, and the volume of the solid is then `8 · 2^{1/4} · (√2 + 1) / 3`. -/
theorem problem63 :
    (∀ h : ℝ, 0 < h → (EightEquilateral h ↔ h = (2 : ℝ) ^ ((3 : ℝ) / 4))) ∧
      ∀ h : ℝ, 0 < h → EightEquilateral h →
        solidVol h = 8 * (2 : ℝ) ^ ((1 : ℝ) / 4) * (√2 + 1) / 3 := by
  set t : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4) with ht
  have tpos : 0 < t := by positivity
  have t4 : t ^ 4 = 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have t3 : (2 : ℝ) ^ ((3 : ℝ) / 4) = t ^ 3 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have t2 : √2 = t ^ 2 := by
    rw [Real.sqrt_eq_rpow, ht, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have key : ∀ h : ℝ, 0 < h → (EightEquilateral h ↔ h = (2 : ℝ) ^ ((3 : ℝ) / 4)) := by
    intro h hh
    rw [eight_iff, t3, t2]
    constructor
    · intro H
      have hX : 0 ≤ 4 - 2 * t ^ 2 + h ^ 2 := by
        nlinarith [show t ^ 2 < 2 by nlinarith [sq_nonneg (t ^ 2)]]
      have h4 : 4 - 2 * t ^ 2 + h ^ 2 = 4 := by
        rw [← Real.sq_sqrt hX, ← H]; norm_num
      have : h ^ 2 = (t ^ 3) ^ 2 := by nlinarith
      exact (pow_left_inj₀ hh.le (by positivity) two_ne_zero).mp this
    · rintro rfl
      rw [show 4 - 2 * t ^ 2 + (t ^ 3) ^ 2 = 2 ^ 2 by nlinarith, Real.sqrt_sq (by norm_num)]
  refine ⟨key, fun h hh H => ?_⟩
  rw [vol_eq h hh, (key h hh).mp H, t3, t2]
  linear_combination (4 * t / 3) * t4

end PillowProblems.P63
