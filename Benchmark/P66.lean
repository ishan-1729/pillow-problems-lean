import PillowProblems.Basic

/-!
# Problem 66 (Algebra: Chances)

**Question.** *(dated 9/89)*

> Given that there are 2 counters in a bag, as to which all that was originally known was that each was either white or black. Also given that the experiment has been tried, a certain number of times, of drawing a counter, looking at it, and replacing it; that it has been white every time; and that, as a result, the chance of drawing white, next time, is \(\dfrac{\alpha}{\alpha + \beta}\). Also given that the same experiment is repeated \(m\) times more, and that it still continues to be white every time. What would then be the chance of drawing white?

**Answer.**

> \[ \frac{2^{m}.(\alpha-\beta)+\beta}{2^{m}.(\alpha-\beta)+2\beta}. \]

*(Carroll's solution: Chapter III, problem 66; text in `data/problems.json`.)*

**Lean reading.** One experiment of `L = n + m + 1` draws with replacement is a finite space
`Outcome L`: the colours of the two counters (`true` = white) and, for each draw, which counter
is drawn. Each draw picks either counter with chance `1/2`, independently ("drawing … and
replacing it"); a colouring `c` has prior weight `p c`. "All that was originally known was that
each was either white or black" is read, as in Carroll's other problems, as the four colourings
being equally likely (`p = 1`); this is `problem66`. `chanceNextWhite p L j` is the conditional
chance (made explicit as `condChance`) that draw `j` is white given that draws `0, …, j-1` were
all white, so the given chance is `chanceNextWhite p (n+m+1) n = α/(α+β)` and the asked one is
`chanceNextWhite p (n+m+1) (n+m)`. We assume `n ≥ 1` ("a certain number of times … white every
time"): Carroll's solution uses that the counters "must be either both white, or one white and
one black", which needs at least one white draw, and for `n = 0` his formula is false (it gives
`1/2` for every `m`). Under the uniform prior `α/(α+β)` is forced to be `(2^n+1)/(2^n+2)`
(`chanceNextWhite_uniform`; `problem66_nonvacuous`, and `problem66_example` is Carroll's example
`9/10 ↦ 257/258`), so, to match the generality of Carroll's argument, which treats
`k = α/(α+β)` as arbitrary, `problem66_general` proves the same formula for any nonnegative
prior, assuming only that the observed white draws had positive chance.

**Status.** proved
-/

namespace PillowProblems.P66

/-- The colours of the two counters (`true` = white). -/
abbrev Colouring := Fin 2 → Bool

/-- One run of `L` draws with replacement: the colours of the two counters, and, for each draw,
which of the two counters is drawn. -/
abbrev Outcome (L : ℕ) := Colouring × (Fin L → Fin 2)

/-- Draw `i` gives a white counter. -/
def IsWhite {L : ℕ} (ω : Outcome L) (i : Fin L) : Prop := ω.1 (ω.2 i) = true

instance {L : ℕ} (ω : Outcome L) (i : Fin L) : Decidable (IsWhite ω i) := by
  unfold IsWhite; infer_instance

/-- The draws before draw `j` (draws `0, …, j-1`) all give white. -/
def WhiteBefore {L : ℕ} (j : ℕ) (ω : Outcome L) : Prop := ∀ i : Fin L, i.val < j → IsWhite ω i

instance {L : ℕ} (j : ℕ) : DecidablePred (WhiteBefore (L := L) j) := fun ω => by
  unfold WhiteBefore; infer_instance

/-- The weight of a case when the colouring `c` has prior weight `p c` and each draw picks
either counter with chance `1/2`, independently. -/
def weight {L : ℕ} (p : Colouring → ℚ) (ω : Outcome L) : ℚ := p ω.1

/-- The chance of `E` given `C`. -/
def condChance {Ω : Type*} [Fintype Ω] (w : Ω → ℚ) (E C : Ω → Prop) [DecidablePred E]
    [DecidablePred C] : ℚ :=
  chance w (fun x => E x ∧ C x) / chance w C

/-- The chance that draw `j` is white, given that all the draws before it were white. -/
def chanceNextWhite (p : Colouring → ℚ) (L : ℕ) (j : Fin L) : ℚ :=
  condChance (weight p) (fun ω => IsWhite ω j) (WhiteBefore j)

/-- The number of white counters. -/
private def wc (c : Colouring) : ℕ := (Finset.univ.filter fun k => c k = true).card

private def P2 (p : Colouring → ℚ) : ℚ := ∑ c, p c * (if wc c = 2 then 1 else 0)

private def P1 (p : Colouring → ℚ) : ℚ := ∑ c, p c * (if wc c = 1 then 1 else 0)

/-- **Carroll's solution, for any prior.** Whatever the original chances `p` of the colourings
(nonnegative weights), if the `n ≥ 1` white draws observed so far were possible and leave the
chance `α/(α+β)` of white next time, then after `m` further white draws the chance of white is
`(2^m(α-β)+β)/(2^m(α-β)+2β)`. -/
theorem problem66_general (p : Colouring → ℚ) (hp : ∀ c, 0 ≤ p c) (n m : ℕ) (hn : 1 ≤ n)
    (hpos : 0 < chance (weight p) (WhiteBefore (L := n + m + 1) n)) (α β : ℚ)
    (hk : chanceNextWhite p (n + m + 1) ⟨n, by omega⟩ = α / (α + β)) :
    chanceNextWhite p (n + m + 1) ⟨n + m, by omega⟩ =
      (2 ^ m * (α - β) + β) / (2 ^ m * (α - β) + 2 * β) := by
  sorry

/-- With the colourings equally likely, after `j ≥ 1` white draws the chance of white next time
is `(2^j+1)/(2^j+2)`. -/
theorem chanceNextWhite_uniform (L j : ℕ) (hj : 1 ≤ j) (hjL : j < L) :
    chanceNextWhite (fun _ => 1) L ⟨j, hjL⟩ = (2 ^ j + 1) / (2 ^ j + 2) := by
  sorry

/-- **Carroll's answer.** With the colourings of the two counters originally equally likely: if
after `n ≥ 1` white draws the chance of white next time is `α/(α+β)`, then after `m` more white
draws it is `(2^m(α-β)+β)/(2^m(α-β)+2β)`. -/
theorem problem66 (n m : ℕ) (hn : 1 ≤ n) (α β : ℚ)
    (hk : chanceNextWhite (fun _ => 1) (n + m + 1) ⟨n, by omega⟩ = α / (α + β)) :
    chanceNextWhite (fun _ => 1) (n + m + 1) ⟨n + m, by omega⟩ =
      (2 ^ m * (α - β) + β) / (2 ^ m * (α - β) + 2 * β) := by
  sorry

/-- The hypothesis of `problem66` can be met: after `n` white draws the chance is
`(2^n+1)/((2^n+1)+1)`, i.e. `α = 2^n+1`, `β = 1`. -/
theorem problem66_nonvacuous (n m : ℕ) (hn : 1 ≤ n) :
    chanceNextWhite (fun _ => 1) (n + m + 1) ⟨n, by omega⟩ =
      (2 ^ n + 1) / ((2 ^ n + 1) + 1) := by
  sorry

/-- Carroll's example: if the chance is `9/10` (this happens after `3` white draws) and the
experiment is repeated `5` times more, the chance becomes `257/258`. -/
theorem problem66_example :
    chanceNextWhite (fun _ => 1) (3 + 5 + 1) ⟨3, by omega⟩ = 9 / (9 + 1) ∧
      chanceNextWhite (fun _ => 1) (3 + 5 + 1) ⟨3 + 5, by omega⟩ = 257 / 258 := by
  sorry

end PillowProblems.P66
