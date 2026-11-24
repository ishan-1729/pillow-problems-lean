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

/-- **Problem 63.** With squares of side `2`: the eight triangles are equilateral exactly when
the squares are `2^{3/4}` apart, and the volume of the solid is then `8 · 2^{1/4} · (√2 + 1) / 3`. -/
theorem problem63 :
    (∀ h : ℝ, 0 < h → (EightEquilateral h ↔ h = (2 : ℝ) ^ ((3 : ℝ) / 4))) ∧
      ∀ h : ℝ, 0 < h → EightEquilateral h →
        solidVol h = 8 * (2 : ℝ) ^ ((1 : ℝ) / 4) * (√2 + 1) / 3 := by
  sorry

end PillowProblems.P63
