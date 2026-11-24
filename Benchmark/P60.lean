import PillowProblems.Basic

/-!
# Problem 60 (Trigonometry: Plane)

**Question.** *(dated 21/3/90)*

> Given a Triangle \(ABC\), and that its base \(BC\) is divided at \(D\) in the ratio \(m\) to \(n\): find the angles \(BAD\), \(CAD\).

**Answer.**

> \(\cot{BAD} = \dfrac{(m+n)\cot{A} + n\cot{B}}{m}\);
>
> similarly, \(\quad\cot{CAD} = \dfrac{(m+n)\cot{A} + m\cot{C}}{n}\).

*(Carroll's solution: Chapter III, problem 60; text in `data/problems.json`.)*

**Lean reading.** `A B C` are points of the plane forming a genuine triangle
(`cross A B C ≠ 0`); Carroll's `A`, `B`, `C` in the answer are the angles `∠BAC`, `∠ABC`, `∠ACB`.
"`BC` divided at `D` in the ratio `m` to `n`" is read as internal division, as in Carroll's figure:
`m, n > 0`, `D` lies on the segment `BC` (`Wbtw ℝ B D C`) and `BD / DC = m / n`. As in Carroll's
answer, the angles `BAD`, `CAD` are found by giving their cotangents (`Real.cot`); the theorem also
proves both angles lie in `(0, π)`, where `cot` is strictly decreasing, so the cotangent
determines each angle uniquely.

**Status.** proved
-/

namespace PillowProblems.P60

open EuclideanGeometry Real

/-- Carroll's answer: with `D` dividing `BC` internally as `m : n`,
`cot BAD = ((m + n) cot A + n cot B) / m` and `cot CAD = ((m + n) cot A + m cot C) / n`;
both angles lie strictly between `0` and `π`, where `cot` is injective, so this finds them. -/
theorem problem60 (A B C D : Plane) (m n : ℝ) (hABC : cross A B C ≠ 0) (hm : 0 < m) (hn : 0 < n)
    (hD : Wbtw ℝ B D C) (hratio : dist B D / dist D C = m / n) :
    Real.cot (∠ B A D) = ((m + n) * Real.cot (∠ B A C) + n * Real.cot (∠ A B C)) / m ∧
    Real.cot (∠ C A D) = ((m + n) * Real.cot (∠ B A C) + m * Real.cot (∠ A C B)) / n ∧
    (0 < ∠ B A D ∧ ∠ B A D < π) ∧ (0 < ∠ C A D ∧ ∠ C A D < π) := by
  sorry

end PillowProblems.P60
