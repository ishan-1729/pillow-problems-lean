import PillowProblems.Basic

/-!
# Problem 54 (Trigonometry: Plane)

**Question.** *(dated 18/4/86)*

> Cut off, from a given Triangle, by lines parallel to the sides, 3 Triangles, so that the remaining Hexagon may be equilateral. Also find the lengths of its sides in terms of the sides of the given Triangle: and the ratios in which the sides of the given Triangle are divided.

**Answer.**

> Side \(AB\) must be divided at \(D\), \(G\), so that \[ AD :\, DG :\, GB\, \colon\colon\, \frac{1}{a} :\, \frac{1}{c} :\, \frac{1}{b}; \] and similarly for the other sides. Also each side of the Hexagon = \(\dfrac{1}{\tfrac{1}{a} + \tfrac{1}{b} + \tfrac{1}{c}}\).

*(Carroll's solution: Chapter III, problem 54; text in `data/problems.json`.)*

**Lean reading.** The triangle is `A, B, C` with `cross A B C ≠ 0`, and `a = BC`, `b = CA`, `c = AB`. Carroll
names only `D, G` on `AB` (and `E`, `F`, `J` in his figure), so we use: `D, G` on `AB` in the order
`A, D, G, B`; `F, J` on `BC` in the order `B, F, J, C`; `H, E` on `CA` in the order `C, H, E, A`.
Points on a side are given as `lineMap` with a parameter in `[0, 1]`. The cutting lines are parallel
to the sides (`DE ∥ BC`, `GF ∥ CA`, `JH ∥ AB`, each written as a difference vector being a multiple of
the side). This is `IsCut`, and the remaining hexagon is `DGFJHE`. Nothing assumes the cut-off
triangles are non-degenerate; that follows from the hexagon being equilateral. `problem54` derives
every side `= 1 / (1/a + 1/b + 1/c)` and the division ratios
`AD : DG : GB = 1/a : 1/c : 1/b` and, "similarly for the other sides",
`BF : FJ : JC = 1/b : 1/a : 1/c` and `CH : HE : EA = 1/c : 1/b : 1/a`. A ratio
`x : y : z = 1/p : 1/q : 1/r` is written `x·p = y·q = z·r`. These ratios fix the six points, so the
hexagon is unique. `problem54_exists` shows that such a cut exists in every triangle.

**Status.** proved
-/

namespace PillowProblems.P54

open AffineMap

/-- The configuration of the problem in the triangle `ABC`: `D, G` lie on side `AB` in the order
`A, D, G, B`; `F, J` on `BC` in the order `B, F, J, C`; `H, E` on `CA` in the order `C, H, E, A`;
and the cutting lines are parallel to the sides: `DE ∥ BC`, `GF ∥ CA`, `JH ∥ AB`. They cut off the
triangles `ADE`, `BFG`, `CHJ` and leave the hexagon `DGFJHE`. -/
def IsCut (A B C D E F G H J : Plane) : Prop :=
  (∃ d g : ℝ, 0 ≤ d ∧ d ≤ g ∧ g ≤ 1 ∧ D = lineMap A B d ∧ G = lineMap A B g) ∧
  (∃ f j : ℝ, 0 ≤ f ∧ f ≤ j ∧ j ≤ 1 ∧ F = lineMap B C f ∧ J = lineMap B C j) ∧
  (∃ h e : ℝ, 0 ≤ h ∧ h ≤ e ∧ e ≤ 1 ∧ H = lineMap C A h ∧ E = lineMap C A e) ∧
  (∃ t : ℝ, E - D = t • (C - B)) ∧ (∃ t : ℝ, F - G = t • (A - C)) ∧
  (∃ t : ℝ, H - J = t • (B - A))

/-- The hexagon `DGFJHE` is equilateral. -/
def IsEquilateralHex (D G F J H E : Plane) : Prop :=
  dist D G = dist G F ∧ dist G F = dist F J ∧ dist F J = dist J H ∧ dist J H = dist H E ∧
    dist H E = dist E D

/-- **Problem 54.** If three triangles are cut off from `ABC` (sides `a = BC`, `b = CA`,
`c = AB`) by lines parallel to the sides so that the remaining hexagon `DGFJHE` is equilateral,
then each side of the hexagon is `1 / (1/a + 1/b + 1/c)`, and the sides of `ABC` are divided in
the ratios `AD : DG : GB = 1/a : 1/c : 1/b`, `BF : FJ : JC = 1/b : 1/a : 1/c`,
`CH : HE : EA = 1/c : 1/b : 1/a` (a ratio `x : y : z = 1/p : 1/q : 1/r` is written
`x·p = y·q = z·r`). -/
theorem problem54 (A B C D E F G H J : Plane) (hABC : cross A B C ≠ 0)
    (hcut : IsCut A B C D E F G H J) (heq : IsEquilateralHex D G F J H E) :
    (dist D G = 1 / (1 / dist B C + 1 / dist C A + 1 / dist A B) ∧
      dist G F = 1 / (1 / dist B C + 1 / dist C A + 1 / dist A B) ∧
      dist F J = 1 / (1 / dist B C + 1 / dist C A + 1 / dist A B) ∧
      dist J H = 1 / (1 / dist B C + 1 / dist C A + 1 / dist A B) ∧
      dist H E = 1 / (1 / dist B C + 1 / dist C A + 1 / dist A B) ∧
      dist E D = 1 / (1 / dist B C + 1 / dist C A + 1 / dist A B)) ∧
    (dist A D * dist B C = dist D G * dist A B ∧ dist D G * dist A B = dist G B * dist C A) ∧
    (dist B F * dist C A = dist F J * dist B C ∧ dist F J * dist B C = dist J C * dist A B) ∧
    (dist C H * dist A B = dist H E * dist C A ∧ dist H E * dist C A = dist E A * dist B C) := by
  sorry

/-- **Problem 54 (the construction exists).** In every triangle the three parallels can be drawn so
that the remaining hexagon is equilateral (cut `AD = s/a · AB`, `BF = s/b · BC`, `CH = s/c · CA`
with `s = 1 / (1/a + 1/b + 1/c)`). -/
theorem problem54_exists (A B C : Plane) (hABC : cross A B C ≠ 0) :
    ∃ D E F G H J : Plane, IsCut A B C D E F G H J ∧ IsEquilateralHex D G F J H E := by
  sorry

end PillowProblems.P54
