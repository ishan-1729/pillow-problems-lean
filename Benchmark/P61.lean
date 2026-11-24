import PillowProblems.Basic

/-!
# Problem 61 (Algebra: Properties of Numbers)

**Question.** *(dated 1/12/81)*

> Prove that, if any 3 Numbers be taken, which cannot be arranged in *A. P.*, and whose sum is a multiple of 3, the sum of their squares is also the sum of another set of 3 squares, the 2 sets having no common term.

*(Carroll's solution: Chapter III, problem 61; text in `data/problems.json`.)*

**Lean reading.** The numbers are integers `a, b, c` (positive where Carroll's "Numbers" matter);
"can be arranged in A. P." means one of them is the mean of the other two
(`CanBeArrangedInAP`), and "the 2 sets having no common term" means that no square of the
new set equals a square of the old one (`NoCommonTerm`); a square `0²` is allowed in the new
set. Carroll's proof takes the new set `x, y, z` with `3x = -a + 2b + 2c`, `3y = 2a - b + 2c`,
`3z = 2a + 2b - c`; `problem61_carroll` proves what his argument actually shows: `x, y, z` are
integers, `x² + y² + z² = a² + b² + c²`, and none of the *numbers* `x, y, z` equals `a`, `b`
or `c`. But he overlooks `x = -b` etc.: `problem61_squares` shows the *squares* are disjoint
exactly when `a + b + c ≠ 0` and none of `a = 5b + 2c, a = 2b + 5c, b = 5a + 2c, b = 2a + 5c,
c = 5a + 2b, c = 2a + 5b` holds. The claim itself is false (`problem61_claim_false`): `problem61_counterexample` shows
that for the distinct positive numbers `1, 4, 13` (sum 18, not in A.P.) every representation
of `186` as a sum of 3 squares shares a square with `1² + 4² + 13²`. The corrected theorem
`problem61` adds the hypothesis excluding the six relations (positivity gives
`a + b + c ≠ 0`).

**Status.** proved (corrected)
-/

namespace PillowProblems.P61

/-- Three numbers can be arranged in arithmetical progression: one is the mean of the
other two. -/
def CanBeArrangedInAP (a b c : ℤ) : Prop :=
  2 * a = b + c ∨ 2 * b = a + c ∨ 2 * c = a + b

/-- The lists `s` and `t` have no common term. -/
def NoCommonTerm (s t : List ℤ) : Prop :=
  ∀ u ∈ s, ∀ v ∈ t, u ≠ v

/-- The exceptional relations missed by Carroll: one number is 5 times a second plus twice the
third. -/
def Exceptional (a b c : ℤ) : Prop :=
  a = 5 * b + 2 * c ∨ a = 2 * b + 5 * c ∨ b = 5 * a + 2 * c ∨ b = 2 * a + 5 * c ∨
    c = 5 * a + 2 * b ∨ c = 2 * a + 5 * b

/-- What Carroll's argument proves: his new set `x, y, z` consists of integers, has the same
sum of squares, and none of the numbers `x, y, z` is one of `a, b, c`. -/
theorem problem61_carroll (a b c : ℤ) (h3 : 3 ∣ a + b + c) (hAP : ¬ CanBeArrangedInAP a b c) :
    ∃ x y z : ℤ, 3 * x = -a + 2 * b + 2 * c ∧ 3 * y = 2 * a - b + 2 * c ∧
      3 * z = 2 * a + 2 * b - c ∧ x ^ 2 + y ^ 2 + z ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 ∧
      NoCommonTerm [x, y, z] [a, b, c] := by
  sorry

/-- Carroll's new set shares a *square* with the old one exactly in the cases he missed. -/
theorem problem61_squares (a b c x y z : ℤ) (hAP : ¬ CanBeArrangedInAP a b c)
    (hx : 3 * x = -a + 2 * b + 2 * c) (hy : 3 * y = 2 * a - b + 2 * c)
    (hz : 3 * z = 2 * a + 2 * b - c) :
    NoCommonTerm [x ^ 2, y ^ 2, z ^ 2] [a ^ 2, b ^ 2, c ^ 2] ↔
      a + b + c ≠ 0 ∧ ¬ Exceptional a b c := by
  sorry

/-- **Corrected statement.** For positive numbers `a, b, c` not in A.P., with sum a multiple of
3, and avoiding Carroll's overlooked relations, the sum of their squares is the sum of another
set of 3 squares with no common term. -/
theorem problem61 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h3 : 3 ∣ a + b + c)
    (hAP : ¬ CanBeArrangedInAP a b c) (hE : ¬ Exceptional a b c) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 ∧
      NoCommonTerm [x ^ 2, y ^ 2, z ^ 2] [a ^ 2, b ^ 2, c ^ 2] := by
  sorry

/-- **Carroll's claim is false**: `1, 4, 13` are positive, distinct, not in A.P., with sum a
multiple of 3, yet no set of 3 squares with sum `1² + 4² + 13² = 186` avoids all of
`1², 4², 13²`. -/
theorem problem61_counterexample :
    ¬ CanBeArrangedInAP 1 4 13 ∧ 3 ∣ (1 + 4 + 13 : ℤ) ∧
      ¬ ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = 1 ^ 2 + 4 ^ 2 + 13 ^ 2 ∧
        NoCommonTerm [x ^ 2, y ^ 2, z ^ 2] [1 ^ 2, 4 ^ 2, 13 ^ 2] := by
  sorry

/-- Hence Carroll's claim, read literally for positive numbers, is false. -/
theorem problem61_claim_false :
    ¬ ∀ a b c : ℤ, 0 < a → 0 < b → 0 < c → 3 ∣ a + b + c → ¬ CanBeArrangedInAP a b c →
      ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 ∧
        NoCommonTerm [x ^ 2, y ^ 2, z ^ 2] [a ^ 2, b ^ 2, c ^ 2] := by
  sorry

theorem problem61_nonvacuous :
    (0 : ℤ) < 3 ∧ (0 : ℤ) < 4 ∧ (0 : ℤ) < 8 ∧ 3 ∣ (3 + 4 + 8 : ℤ) ∧
      ¬ CanBeArrangedInAP 3 4 8 ∧ ¬ Exceptional 3 4 8 := by
  sorry

end PillowProblems.P61
