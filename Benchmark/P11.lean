import PillowProblems.Basic

/-!
# Problem 11 (Trigonometry: Plane)

**Question.** *(dated 31/3/82)*

> A Triangle \(ABC\) has another \(A'B'C'\) inscribed in it, so that \(\angle BA′C′ = \angle CB′A′ = \angle AC′B′ = \theta\); thus making it similar to the first Triangle. Find ratio between homologous sides. And solve for "\(\theta = 90°\)".
>
> [Figure: A geometric diagram of triangle ABC with interior points and a smaller inscribed triangle A'B'C' formed by connecting midpoints or cevians, with labeled intersection point O.]
>
> The Triangles can be proved similar thus:— \[ \begin{array}{c} \angle C′A′B′ + \angle B′A′C = \text{supp. of}~ \theta,\\ \angle B′A′C + \angle A′CB′ = \text{supp. of}~ \theta;\\ \therefore \text{these pairs are equal};~ \therefore \angle C′A′B′ = C. \end{array} \]
>
> Hence \(\angle A′B′C′ = A,~ \text{and}~ \angle B′C′A′ = B.\)
>
> Let \(C′A′ = ka;~\therefore A′B′ = kb,~ \text{and}~ B′C′ = kc\). We have to find \(k\).

**Answer.**

> The required ratio is equal to \[ \frac{\sin A \sin B \sin C}{\sin \theta (1 + \cos A \cos B \cos C) + \cos \theta \sin A \sin B \sin C}. \]
>
> If \(\theta = 90°\), this = \(\dfrac{\sin A \sin B \sin C}{1 + \cos A \cos B \cos C}.\)

*(Carroll's solution: Chapter III, problem 11; text in `data/problems.json`.)*

**Lean reading.** `A B C` is a genuine triangle (`¬ Collinear`), and the inscribed triangle
has `A'` strictly inside side `BC`, `B'` inside `CA`, `C'` inside `AB`, with
`∠ B A' C' = ∠ C B' A' = ∠ A C' B' = θ`. Writing `A, B, C` for the angles `∠ B A C`, `∠ A B C`,
`∠ A C B`, the theorem `problem11` proves `C'A' = k·a`, `A'B' = k·b`, `B'C' = k·c` with
`a = BC, b = CA, c = AB` and `k` Carroll's ratio; in particular the triangles are similar
(SSS), so the similarity asserted in the question is proved, not assumed. Carroll obtains
`A'B' = kb` from the similarity; here instead all three sides are found at once from the
six sine-rule relations in the corner triangles (a linear system in `C'A', A'B', B'C'` whose
determinant is positive), which avoids adding unoriented angles at `A'`. `problem11_right` is the
case `θ = 90°`. No hypothesis on `θ` is needed: it is a geometric angle, and the configuration
forces `0 < θ < π`; `problem11_nonvacuous` exhibits the configuration (equilateral triangle,
medial triangle, `θ = π/3`), and `problem11_right_nonvacuous` exhibits the case `θ = 90°`
(equilateral triangle, `BA' = CB' = AC' = BC/3`).

**Status.** proved
-/

namespace PillowProblems.P11

open EuclideanGeometry
open scoped Real

/-- Carroll's answer: the ratio of homologous sides of the inscribed triangle `A'B'C'` to the
triangle `ABC` is `sin A sin B sin C / (sin θ (1 + cos A cos B cos C) + cos θ sin A sin B sin C)`. -/
theorem problem11 (A B C A' B' C' : Plane) (θ : ℝ) (hABC : ¬ Collinear ℝ {A, B, C})
    (hA' : Sbtw ℝ B A' C) (hB' : Sbtw ℝ C B' A) (hC' : Sbtw ℝ A C' B)
    (h1 : ∠ B A' C' = θ) (h2 : ∠ C B' A' = θ) (h3 : ∠ A C' B' = θ) :
    let k := Real.sin (∠ B A C) * Real.sin (∠ A B C) * Real.sin (∠ A C B) /
      (Real.sin θ * (1 + Real.cos (∠ B A C) * Real.cos (∠ A B C) * Real.cos (∠ A C B)) +
        Real.cos θ * (Real.sin (∠ B A C) * Real.sin (∠ A B C) * Real.sin (∠ A C B)))
    dist C' A' = k * dist B C ∧ dist A' B' = k * dist C A ∧ dist B' C' = k * dist A B := by
  sorry

/-- Corollary (`θ = 90°`): the ratio is `sin A sin B sin C / (1 + cos A cos B cos C)`. -/
theorem problem11_right (A B C A' B' C' : Plane) (hABC : ¬ Collinear ℝ {A, B, C})
    (hA' : Sbtw ℝ B A' C) (hB' : Sbtw ℝ C B' A) (hC' : Sbtw ℝ A C' B)
    (h1 : ∠ B A' C' = π / 2) (h2 : ∠ C B' A' = π / 2) (h3 : ∠ A C' B' = π / 2) :
    let k := Real.sin (∠ B A C) * Real.sin (∠ A B C) * Real.sin (∠ A C B) /
      (1 + Real.cos (∠ B A C) * Real.cos (∠ A B C) * Real.cos (∠ A C B))
    dist C' A' = k * dist B C ∧ dist A' B' = k * dist C A ∧ dist B' C' = k * dist A B := by
  sorry

/-- The hypotheses of `problem11` can be met: the medial triangle of an equilateral triangle,
with `θ = π/3`. -/
theorem problem11_nonvacuous : ∃ A B C A' B' C' : Plane, ∃ θ : ℝ, ¬ Collinear ℝ {A, B, C} ∧
    Sbtw ℝ B A' C ∧ Sbtw ℝ C B' A ∧ Sbtw ℝ A C' B ∧
    ∠ B A' C' = θ ∧ ∠ C B' A' = θ ∧ ∠ A C' B' = θ := by
  sorry

/-- The hypotheses of `problem11_right` can be met: in the equilateral triangle
`B = (0,0)`, `C = (1,0)`, `A = (1/2, √3/2)`, take `BA' = CB' = AC' = 1/3`. -/
theorem problem11_right_nonvacuous : ∃ A B C A' B' C' : Plane, ¬ Collinear ℝ {A, B, C} ∧
    Sbtw ℝ B A' C ∧ Sbtw ℝ C B' A ∧ Sbtw ℝ A C' B ∧
    ∠ B A' C' = π / 2 ∧ ∠ C B' A' = π / 2 ∧ ∠ A C' B' = π / 2 := by
  sorry

end PillowProblems.P11
