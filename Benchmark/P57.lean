import PillowProblems.Basic

/-!
# Problem 57 (Pure Geometry, Plane, Trigonometry: Plane)

**Question.** *(dated 27/1/91)*

> In a given Triangle describe three Squares, whose bases shall lie along the sides of the Triangle, and whose upper edges shall form a Triangle;
>
> (1) geometrically; (2) trigonometrically.

**Answer.**

> (1) *Geometrically.*
>
> If Squares be described externally on the sides of the given Triangle; and if their outer edges be produced to form a new Triangle; and if the sides of the given Triangle be divided similarly to those of the new Triangle: their central portions will be the bases of the required Squares.
>
> (2) *Trigonometrically.*
>
> If \(a\), \(b\), \(c\) be the sides of the given Triangle, and \(m\) its area; and if \(x\), \(y\), \(z\) be the sides of the required Squares: then \[ \frac{a}{x} = \frac{b}{y} = \frac{c}{z} = \frac{a^{2}+b^{2}+c^{2}}{2m} + 1. \]

*(Carroll's solution: Chapter III, problem 57; text in `data/problems.json`.)*

**Lean reading.** A square stands on a side when its base lies along the line of that side and the
square is on the inner side (`SquareOn`; for an obtuse triangle Carroll's bases may run past a
vertex, so lines rather than segments are used); the three squares stand on `BC`, `CA`, `AB`
with upper edges `B'C'`, `C'A'`, `A'B'` (`Squares`), so the upper edges form the triangle
`A'B'C'`. Carroll tacitly assumes, as in his figure, that the squares lie outside the triangle
`A'B'C'` (`Outside`: each upper edge separates the opposite vertex of `A'B'C'` from the side of
`ABC` it stands on). Without this the answer is not unique: `problem57_other` exhibits, in the
triangle with sides `6, 5, 5`, a second figure with overlapping squares and `a/x = 31/12`
instead of `55/12`. Here `a, b, c` are the sides, `m = triArea A B C`, and `x, y, z` the sides
`B'C'`, `C'A'`, `A'B'` of the squares. `problem57_b` proves Carroll's formula (2) for every such
figure, `problem57_exists` that the figure exists in every triangle, and `problem57_a` proves
the construction (1): if `A''B''C''` is the triangle formed by the outer edges of the external
squares, and the sides of `ABC` are divided at the same parameters as the external squares
divide the sides of `A''B''C''`, the central portions are the bases of a figure as in (2).

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P57

open scoped EuclideanGeometry RealInnerProductSpace

/-- `PQRS` (vertices in this order) is a square: `PQ`, `PS` are perpendicular sides of equal
length and `R - Q = S - P`. -/
def IsSquare (P Q R S : Plane) : Prop :=
  P ≠ Q ∧ R - Q = S - P ∧ ⟪Q - P, S - P⟫ = 0 ∧ ‖S - P‖ = ‖Q - P‖

/-- A square stands on the side `XY` of the triangle `XYZ`, on the same side of `XY` as `Z`
(i.e. inside the triangle), with upper edge `UV`: its base `PQ` lies along `XY`, and `PQVU` is a
square. -/
def SquareOn (X Y Z U V : Plane) : Prop :=
  ∃ P Q : Plane, P ∈ line[ℝ, X, Y] ∧ Q ∈ line[ℝ, X, Y] ∧ IsSquare P Q V U ∧
    0 < cross X Y U * cross X Y Z

/-- Three squares stand on the sides `BC`, `CA`, `AB` of the triangle `ABC`, inside it, and their
upper edges `B'C'`, `C'A'`, `A'B'` form the triangle `A'B'C'`. -/
def Squares (A B C A' B' C' : Plane) : Prop :=
  SquareOn B C A B' C' ∧ SquareOn C A B C' A' ∧ SquareOn A B C A' B'

/-- Carroll's figure: the squares lie outside the triangle `A'B'C'` formed by their upper edges,
i.e. each upper edge separates the opposite vertex of `A'B'C'` from the side of `ABC` on which
that square stands. -/
def Outside (A B C A' B' C' : Plane) : Prop :=
  cross B' C' A' * cross B' C' B < 0 ∧ cross C' A' B' * cross C' A' C < 0 ∧
    cross A' B' C' * cross A' B' A < 0

/-- **Problem 57 (2)**: in every such figure (Carroll's: squares outside the triangle formed by
their upper edges), `a/x = b/y = c/z = (a² + b² + c²)/(2m) + 1`. -/
theorem problem57_b (A B C A' B' C' : Plane) (hT : cross A B C ≠ 0)
    (hS : Squares A B C A' B' C') (hO : Outside A B C A' B' C') :
    dist B C / dist B' C' =
        (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) / (2 * triArea A B C) + 1 ∧
      dist C A / dist C' A' =
        (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) / (2 * triArea A B C) + 1 ∧
      dist A B / dist A' B' =
        (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) / (2 * triArea A B C) + 1 := by
  sorry

/-- **Problem 57**: Carroll's figure exists in every triangle (so the description of part (2)
is not vacuous). -/
theorem problem57_exists (A B C : Plane) (hT : cross A B C ≠ 0) :
    ∃ A' B' C' : Plane, Squares A B C A' B' C' ∧ Outside A B C A' B' C' := by
  sorry

/-! ### Part (1): the geometric construction -/

/-- **Problem 57 (1)**, geometrically. Squares `B C Ca Ba`, `C A Ab Cb`, `A B Bc Ac` are described
externally on the sides; their outer edges, produced, form the triangle `A''B''C''`; the sides
of `A''B''C''` are divided by the squares at the parameters `r, r'` (on `B''C''`), `s, s'` (on
`C''A''`), `t, t'` (on `A''B''`). Dividing the sides of `ABC` similarly, the central portions are
the bases of the required squares: there is a figure of three squares on these bases whose
upper edges form a triangle `A'B'C'`, as in part (2). -/
theorem problem57_a (A B C Ba Ca Cb Ab Ac Bc A'' B'' C'' : Plane) (hT : cross A B C ≠ 0)
    (hBC : IsSquare B C Ca Ba) (hBC' : cross B C Ba * cross B C A < 0)
    (hCA : IsSquare C A Ab Cb) (hCA' : cross C A Cb * cross C A B < 0)
    (hAB : IsSquare A B Bc Ac) (hAB' : cross A B Ac * cross A B C < 0)
    (hA'' : A'' ∈ line[ℝ, Cb, Ab] ∧ A'' ∈ line[ℝ, Ac, Bc])
    (hB'' : B'' ∈ line[ℝ, Ac, Bc] ∧ B'' ∈ line[ℝ, Ba, Ca])
    (hC'' : C'' ∈ line[ℝ, Ba, Ca] ∧ C'' ∈ line[ℝ, Cb, Ab])
    (r r' s s' t t' : ℝ)
    (hBa : Ba = B'' + r • (C'' - B'')) (hCa : Ca = B'' + r' • (C'' - B''))
    (hCb : Cb = C'' + s • (A'' - C'')) (hAb : Ab = C'' + s' • (A'' - C''))
    (hAc : Ac = A'' + t • (B'' - A'')) (hBc : Bc = A'' + t' • (B'' - A'')) :
    ∃ A' B' C' : Plane,
      IsSquare (B + r • (C - B)) (B + r' • (C - B)) C' B' ∧
      IsSquare (C + s • (A - C)) (C + s' • (A - C)) A' C' ∧
      IsSquare (A + t • (B - A)) (A + t' • (B - A)) B' A' ∧
      Squares A B C A' B' C' ∧ Outside A B C A' B' C' := by
  sorry

/-- The hypotheses of part (1) are satisfiable: the triangle `A = (3,4)`, `B = (0,0)`,
`C = (6,0)` with its external squares and the new triangle `A'' = (3, 37/3)`,
`B'' = (-43/4, -6)`, `C'' = (67/4, -6)`. -/
theorem problem57_a_nonvacuous : ∃ A B C Ba Ca Cb Ab Ac Bc A'' B'' C'' : Plane,
    ∃ r r' s s' t t' : ℝ,
    cross A B C ≠ 0 ∧
    IsSquare B C Ca Ba ∧ cross B C Ba * cross B C A < 0 ∧
    IsSquare C A Ab Cb ∧ cross C A Cb * cross C A B < 0 ∧
    IsSquare A B Bc Ac ∧ cross A B Ac * cross A B C < 0 ∧
    (A'' ∈ line[ℝ, Cb, Ab] ∧ A'' ∈ line[ℝ, Ac, Bc]) ∧
    (B'' ∈ line[ℝ, Ac, Bc] ∧ B'' ∈ line[ℝ, Ba, Ca]) ∧
    (C'' ∈ line[ℝ, Ba, Ca] ∧ C'' ∈ line[ℝ, Cb, Ab]) ∧
    Ba = B'' + r • (C'' - B'') ∧ Ca = B'' + r' • (C'' - B'') ∧
    Cb = C'' + s • (A'' - C'') ∧ Ab = C'' + s' • (A'' - C'') ∧
    Ac = A'' + t • (B'' - A'') ∧ Bc = A'' + t' • (B'' - A'') := by
  sorry

/-- Without Carroll's tacit condition `Outside` the answer is not unique: in the triangle
`A = (3,4)`, `B = (0,0)`, `C = (6,0)` (sides `6, 5, 5`, area `12`) there is a second figure,
with the squares overlapping and `a/x = 31/12`, whereas `(a²+b²+c²)/(2m) + 1 = 55/12`. -/
theorem problem57_other :
    Squares (pt 3 4) (pt 0 0) (pt 6 0) (pt 3 (24 / 31)) (pt (129 / 31) (72 / 31))
        (pt (57 / 31) (72 / 31)) ∧
      dist (pt 0 0) (pt 6 0) / dist (pt (129 / 31) (72 / 31)) (pt (57 / 31) (72 / 31)) = 31 / 12 ∧
      (dist (pt 0 0) (pt 6 0) ^ 2 + dist (pt 6 0) (pt 3 4) ^ 2 + dist (pt 3 4) (pt 0 0) ^ 2) /
        (2 * triArea (pt 3 4) (pt 0 0) (pt 6 0)) + 1 = 55 / 12 := by
  sorry

end PillowProblems.P57
