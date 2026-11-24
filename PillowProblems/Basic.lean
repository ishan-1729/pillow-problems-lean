import Mathlib

/-!
# *Pillow-Problems*: shared conventions

Lewis Carroll (C. L. Dodgson), *Curiosa Mathematica, Part II: Pillow-Problems thought out
during wakeful hours*, 4th edition, Macmillan 1895 (Project Gutenberg #79080).

Each problem lives in its own file `PillowProblems/PNN.lean`. That file quotes Carroll's question,
and his answer where he gives one separately, verbatim. A **Lean reading** paragraph explains
how the problem is modelled, and a **Status** line says what is proved. The main theorem is
called `problemN`, with suffixes `problemN_a`, `problemN_b`, … for problems with several parts.

This file fixes the conventions that several problems share, so that they are modelled the same
way throughout.

* **The plane** is `Plane := EuclideanSpace ℝ (Fin 2)`, so `dist` is the Euclidean distance (not the
  sup distance of `ℝ × ℝ`). Angles are mathlib's unoriented `EuclideanGeometry.angle`
  (`∠ A B C`, in radians, in `[0, π]`). Solid problems use `Space := EuclideanSpace ℝ (Fin 3)`.
* **Area** of a triangle is `triArea A B C`, half the absolute value of the cross product.
* **Construction problems** ("in a given Triangle to place a line …") are read as: the object
  Carroll's construction produces exists and has the required property. Where Carroll's answer
  determines it uniquely, uniqueness is proved as well.
* **"Find" problems** are read as: Carroll's answer is correct. Where it is natural, the theorem
  also shows the answer is complete (every solution is of Carroll's form).
* **Chances** are probabilities in a finite model of equally likely, or explicitly weighted,
  cases (`chance`), which is how Carroll computes them. The model and every assumption Carroll
  makes tacitly ("the bag shaken", "at random") are spelled out in the Lean reading.
-/

namespace PillowProblems

open scoped EuclideanGeometry

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Euclidean three-dimensional space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The point `(x, y)` of the plane. -/
noncomputable def pt (x y : ℝ) : Plane := !₂[x, y]

@[simp] lemma pt_zero (x y : ℝ) : pt x y 0 = x := rfl
@[simp] lemma pt_one (x y : ℝ) : pt x y 1 = y := rfl

/-- Twice the signed area of the triangle `ABC` (positive when `A, B, C` are anticlockwise). -/
noncomputable def cross (A B C : Plane) : ℝ :=
  (B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)

/-- The area of the triangle `ABC`. -/
noncomputable def triArea (A B C : Plane) : ℝ := |cross A B C| / 2

/-- The chance of the event `E` when the cases `Ω` occur with the (nonnegative) weights `w`:
the total weight of `E` divided by the total weight. With `w = 1` every case is equally likely. -/
def chance {Ω : Type*} [Fintype Ω] (w : Ω → ℚ) (E : Ω → Prop) [DecidablePred E] : ℚ :=
  (∑ x ∈ Finset.univ.filter E, w x) / ∑ x, w x

/-- The chance of `E` among equally likely cases. -/
def uniformChance {Ω : Type*} [Fintype Ω] (E : Ω → Prop) [DecidablePred E] : ℚ :=
  chance (fun _ => 1) E

lemma uniformChance_eq {Ω : Type*} [Fintype Ω] (E : Ω → Prop) [DecidablePred E] :
    uniformChance E = (Finset.univ.filter E).card / Fintype.card Ω := by
  simp [uniformChance, chance]

end PillowProblems
