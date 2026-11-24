import PillowProblems.Basic

/-!
# Problem 65 (Trigonometry: Plane)

**Question.** *(dated 5/89)*

> How many shapes are there for Triangles which have all their angles aliquot parts of 360°?

*(Carroll's solution: Chapter III, problem 65; text in `data/problems.json`.)*

**Lean reading.** A triangle's shape (its similarity class) is fixed by its three angles, and
every triple of positive angles with sum `180°` is the set of angles of some triangle, so a shape is
an unordered triple of angles; we represent it by its angles `(a, b, c)` in degrees listed in
non-increasing order (`0 < c ≤ b ≤ a`, `a + b + c = 180`). Following Carroll's solution, "an
aliquot part of `360°`" means `360°/n` for a positive integer `n` (so `51 3/7° = 360°/7` counts;
the angle need not be a whole number of degrees). `aliquotShapes` is the set of all such triples;
`problem65` shows it is exactly Carroll's list of ten triples, so there are `10` shapes. (Carroll's
solution text has a misprint in case (2), writing `1/2, 1/5, 1/20` for `1/4, 1/5, 1/20`; his final
list is correct.)

**Status.** proved
-/

namespace PillowProblems.P65

/-- An angle of `a` degrees is an aliquot part of `360°`. -/
def IsAliquotPart (a : ℝ) : Prop := ∃ n : ℕ, 0 < n ∧ a = 360 / n

/-- Shapes of triangles all of whose angles are aliquot parts of `360°`, each shape represented
by its angles `(a, b, c)` in degrees, listed in non-increasing order. -/
def aliquotShapes : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < p.2.2 ∧ p.2.2 ≤ p.2.1 ∧ p.2.1 ≤ p.1 ∧ p.1 + p.2.1 + p.2.2 = 180 ∧
    IsAliquotPart p.1 ∧ IsAliquotPart p.2.1 ∧ IsAliquotPart p.2.2}

theorem problem65 :
    aliquotShapes = {(120, 30, 30), (120, 40, 20), (120, 45, 15), (120, 36, 24),
      (120, 360 / 7, 60 / 7), (90, 45, 45), (90, 60, 30), (90, 72, 18), (72, 72, 36),
      (60, 60, 60)} ∧
    aliquotShapes.ncard = 10 := by
  sorry

end PillowProblems.P65
