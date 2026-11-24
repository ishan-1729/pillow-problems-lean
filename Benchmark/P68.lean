import PillowProblems.Basic

/-!
# Problem 68 (Algebra: Equational Problems)

**Question.** *(dated 28/2/89)*

> Five friends agreed to form themselves into a Wine-Company (Limited). They contributed equal amounts of wine, which had been bought at the same price. They then elected one of themselves to act as Treasurer; and another of them undertook to act as Salesman, and to sell the wine at 10% over cost-price.
>
> The first day the Salesman drank one bottle, sold some, and handed over the receipts to the Treasurer.
>
> The second day he drank none, but pocketed the profits on one bottle sold, and handed over the rest of the receipts to the Treasurer.
>
> That night the Treasurer visited the Cellars, and counted the remaining wine. "It will fetch just £11," he muttered to himself as he left the Cellars.
>
> The third day the Salesman drank one bottle, pocketed the profits on another, and handed over the rest of the receipts to the Treasurer.
>
> The wine was now all gone: the Company held a Meeting, and found to their chagrin that their profits (i. e. the Treasurer's receipts, less the original value of the wine) only cleared 6*d.* a bottle on the whole stock. These profits had accrued in 3 equal sums on the 3 days (i. e. the Treasurer's receipts for the day, less the original value of the wine taken out during the day, had come to the same amount every time); but of course only the Salesman knew this.
>
> (1) How much wine had they bought? (2) At what price?

**Answer.**

> (1) 5 dozen; (2) 8/4 a bottle.

*(Carroll's solution: Chapter III, problem 68; text in `data/problems.json`.)*

**Lean reading.** Money is in pence (£1 = 240d., 1s. = 12d.) and rational; a bottle costs `c > 0` and sells for
`11c/10`. The three days take `x`, `y`, `z` bottles out of the cellar, and the story fixes the
Treasurer's receipts as in `receipts₁`–`receipts₃` (a drunk bottle brings nothing; "pocketing the
profits on one bottle" withholds `c/10`). "Contributed equal amounts of wine" is read, as in
Carroll's solution, as each friend giving the same whole number `b` of bottles, so the stock is
`5 * b`; without it there is a second solution (48 bottles at 10s. a bottle,
`problem68_needs_five`), which Carroll discards for exactly this reason. The facts that the Salesman drank or sold at least one bottle a
day are not needed as hypotheses; the unique solution satisfies them (`problem68_nonvacuous`).

**Status.** proved
-/

namespace PillowProblems.P68

/-- Sale price of a bottle costing `c` pence: 10% over cost price. -/
def salePrice (c : ℚ) : ℚ := c * 11 / 10

/-- The profit on one bottle sold (what the Salesman pockets when he "pockets the profits
 on one bottle"). -/
def profitPerBottle (c : ℚ) : ℚ := salePrice c - c

/-- Day 1: `x` bottles taken out; the Salesman drinks one and hands over the price of the rest. -/
def receipts₁ (x : ℕ) (c : ℚ) : ℚ := ((x : ℚ) - 1) * salePrice c
/-- Day 2: `y` bottles taken out and sold; the Salesman pockets the profit on one of them. -/
def receipts₂ (y : ℕ) (c : ℚ) : ℚ := (y : ℚ) * salePrice c - profitPerBottle c
/-- Day 3: `z` bottles taken out; the Salesman drinks one, sells the rest and pockets the
profit on one of those sold. -/
def receipts₃ (z : ℕ) (c : ℚ) : ℚ := ((z : ℚ) - 1) * salePrice c - profitPerBottle c

/-- The data of the story: each of the five friends contributed `b` bottles; `x, y, z` bottles
left the cellar on the three days (so `x + y + z = 5 * b`, the whole stock); each bottle cost
`c > 0` pence; on the second night the remaining `z` bottles would fetch £11 = 2640d.; the total
profit (Treasurer's receipts less cost of the whole stock) is 6d. a bottle; and the three daily
profits (receipts less cost of the bottles taken out that day) are equal. -/
def WineCompany (b x y z : ℕ) (c : ℚ) : Prop :=
  0 < c ∧
  x + y + z = 5 * b ∧
  (z : ℚ) * salePrice c = 11 * 240 ∧
  receipts₁ x c + receipts₂ y c + receipts₃ z c - ((x + y + z : ℕ) : ℚ) * c = 6 * ((x + y + z : ℕ) : ℚ) ∧
  receipts₁ x c - x * c = receipts₂ y c - y * c ∧
  receipts₂ y c - y * c = receipts₃ z c - z * c

/-- They bought 5 dozen bottles at 8s. 4d. (= 100d.) a bottle, and this is the only possibility. -/
theorem problem68 (b x y z : ℕ) (c : ℚ) (h : WineCompany b x y z c) :
    x + y + z = 5 * 12 ∧ c = 8 * 12 + 4 := by
  sorry

/-- The story is consistent: 23, 13 and 24 bottles on the three days, at 100d. a bottle. -/
theorem problem68_nonvacuous : WineCompany 12 23 13 24 100 := by
  sorry

/-- Why the stock must be read as a multiple of 5: dropping only that condition, 19, 9 and 20
bottles at 120d. (10s.) a bottle satisfy every other condition of the story, but 48 bottles
cannot be shared equally among five friends. -/
theorem problem68_needs_five :
    (0 : ℚ) < 120 ∧ (20 : ℕ) * salePrice 120 = 11 * 240 ∧
      receipts₁ 19 120 + receipts₂ 9 120 + receipts₃ 20 120 - ((19 + 9 + 20 : ℕ) : ℚ) * 120 =
        6 * ((19 + 9 + 20 : ℕ) : ℚ) ∧
      receipts₁ 19 120 - (19 : ℕ) * 120 = receipts₂ 9 120 - (9 : ℕ) * 120 ∧
      receipts₂ 9 120 - (9 : ℕ) * 120 = receipts₃ 20 120 - (20 : ℕ) * 120 ∧
      ∀ b : ℕ, 19 + 9 + 20 ≠ 5 * b := by
  sorry

end PillowProblems.P68
