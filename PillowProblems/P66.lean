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

private lemma card_pi_white (c : Colouring) (L j : ℕ) (hj : j ≤ L) :
    (Finset.univ.filter (fun s : Fin L → Fin 2 => ∀ i : Fin L, i.val < j → c (s i) = true)).card
      = wc c ^ j * 2 ^ (L - j) := by
  have : Finset.univ.filter (fun s : Fin L → Fin 2 => ∀ i : Fin L, i.val < j → c (s i) = true)
      = Fintype.piFinset (fun i : Fin L =>
          if i.val < j then Finset.univ.filter (fun k => c k = true) else Finset.univ) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      split_ifs with hi
      · simpa using h i hi
      · simp
    · intro h i hi
      simpa [hi] using h i
  rw [this, Fintype.card_piFinset]
  have h2 : ∀ i : Fin L, (if i.val < j then Finset.univ.filter (fun k => c k = true)
      else Finset.univ).card = if i.val < j then wc c else 2 := by
    intro i; split_ifs <;> simp [wc]
  simp only [h2]
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < j then wc c else 2) L, Finset.prod_ite,
    Finset.prod_const, Finset.prod_const]
  congr 2
  · have : (Finset.range L).filter (· < j) = Finset.range j := by
      ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, Finset.card_range]
  · have : (Finset.range L).filter (fun x => ¬ x < j) = Finset.Ico j L := by
      ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [this, Nat.card_Ico]

private lemma sum_whiteBefore (p : Colouring → ℚ) (L j : ℕ) (hj : j ≤ L) :
    ∑ ω ∈ Finset.univ.filter (WhiteBefore (L := L) j), weight p ω
      = ∑ c, p c * (wc c : ℚ) ^ j * 2 ^ (L - j) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h := card_pi_white c L j hj
  rw [← Finset.sum_filter]
  simp only [weight]
  rw [Finset.sum_const, nsmul_eq_mul]
  have e : (Finset.univ.filter fun s : Fin L → Fin 2 => WhiteBefore j (c, s)) =
      Finset.univ.filter (fun s : Fin L → Fin 2 => ∀ i : Fin L, i.val < j → c (s i) = true) := by
    ext s
    rw [Finset.mem_filter, Finset.mem_filter]
    exact Iff.rfl
  rw [e, h]
  push_cast
  ring

private lemma wc_pow (c : Colouring) (j : ℕ) (hj : 1 ≤ j) :
    (wc c : ℚ) ^ j = 2 ^ j * (if wc c = 2 then 1 else 0) + (if wc c = 1 then 1 else 0) := by
  have h : wc c ≤ 2 := by
    unfold wc; exact (Finset.card_filter_le _ _).trans (by simp)
  interval_cases h' : wc c <;> simp [zero_pow (by omega : j ≠ 0)]

private lemma sum_whiteBefore' (p : Colouring → ℚ) (L j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ L) :
    ∑ ω ∈ Finset.univ.filter (WhiteBefore (L := L) j), weight p ω
      = (2 ^ j * P2 p + P1 p) * 2 ^ (L - j) := by
  rw [sum_whiteBefore p L j hj, P2, P1, add_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [wc_pow c j hj1]
  ring

private lemma chanceNext_eq (p : Colouring → ℚ) (L j : ℕ) (hj1 : 1 ≤ j) (hjL : j < L)
    (hT : ∑ ω : Outcome L, weight p ω ≠ 0) :
    chanceNextWhite p L ⟨j, hjL⟩ = (2 ^ (j + 1) * P2 p + P1 p) / (2 * (2 ^ j * P2 p + P1 p)) := by
  unfold chanceNextWhite condChance chance
  have hE : Finset.univ.filter (fun ω : Outcome L => IsWhite ω ⟨j, hjL⟩ ∧ WhiteBefore j ω) =
      Finset.univ.filter (WhiteBefore (L := L) (j + 1)) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact h2 i hi
      · have : i = ⟨j, hjL⟩ := Fin.ext hi
        subst this; exact h1
    · intro h
      exact ⟨h _ (by simp), fun i hi => h i (by omega)⟩
  rw [hE, sum_whiteBefore' p L (j + 1) (by omega) (by omega),
    sum_whiteBefore' p L j hj1 hjL.le, div_div_div_cancel_right₀ hT,
    show L - j = (L - (j + 1)) + 1 by omega, pow_succ (2 : ℚ) (L - (j + 1)),
    show (2 ^ j * P2 p + P1 p) * (2 ^ (L - (j + 1)) * 2) =
      (2 * (2 ^ j * P2 p + P1 p)) * 2 ^ (L - (j + 1)) by ring,
    mul_div_mul_right _ _ (by positivity)]

private lemma alg (a b α β : ℚ) (m : ℕ) (ha : 0 ≤ a) (hab : 0 < a + b)
    (hk : (2 * a + b) / (2 * (a + b)) = α / (α + β)) :
    (2 ^ m * 2 * a + b) / (2 * (2 ^ m * a + b)) =
      (2 ^ m * (α - β) + β) / (2 ^ m * (α - β) + 2 * β) := by
  have hpos : 0 < (2 * a + b) / (2 * (a + b)) := by
    apply div_pos <;> linarith
  have hD : α + β ≠ 0 := by
    intro h; rw [h, div_zero] at hk; linarith
  have hα : α ≠ 0 := by
    intro h; rw [h, zero_div] at hk; linarith
  rw [div_eq_div_iff (by positivity) hD] at hk
  have key : b * (α - β) = 2 * a * β := by linear_combination -hk
  have h2m : (1 : ℚ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have ham : a ≤ 2 ^ m * a := le_mul_of_one_le_left ha h2m
  have hden : 0 < 2 * (2 ^ m * a + b) := by linarith
  have hX : 2 ^ m * (α - β) + 2 * β ≠ 0 := by
    intro hX
    by_cases hβ : β = 0
    · subst hβ
      have hb0 : b = 0 := by
        have : b * α = 0 := by linear_combination key
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h hα
      have : (2 : ℚ) ^ m * α = 0 := by linear_combination hX
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (by positivity)
      · exact hα h
    · have h1 : β * (2 ^ m * a + b) = 0 := by
        linear_combination (b / 2) * hX - 2 ^ m / 2 * key
      rcases mul_eq_zero.mp h1 with h | h
      · exact hβ h
      · linarith
  rw [div_eq_div_iff hden.ne' hX]
  linear_combination (-(2 : ℚ) ^ m) * key

/-- **Carroll's solution, for any prior.** Whatever the original chances `p` of the colourings
(nonnegative weights), if the `n ≥ 1` white draws observed so far were possible and leave the
chance `α/(α+β)` of white next time, then after `m` further white draws the chance of white is
`(2^m(α-β)+β)/(2^m(α-β)+2β)`. -/
theorem problem66_general (p : Colouring → ℚ) (hp : ∀ c, 0 ≤ p c) (n m : ℕ) (hn : 1 ≤ n)
    (hpos : 0 < chance (weight p) (WhiteBefore (L := n + m + 1) n)) (α β : ℚ)
    (hk : chanceNextWhite p (n + m + 1) ⟨n, by omega⟩ = α / (α + β)) :
    chanceNextWhite p (n + m + 1) ⟨n + m, by omega⟩ =
      (2 ^ m * (α - β) + β) / (2 ^ m * (α - β) + 2 * β) := by
  have hT0 : 0 ≤ ∑ ω : Outcome (n + m + 1), weight p ω :=
    Finset.sum_nonneg fun ω _ => hp ω.1
  have hT : ∑ ω : Outcome (n + m + 1), weight p ω ≠ 0 := by
    intro h; rw [chance, h, div_zero] at hpos; exact lt_irrefl _ hpos
  have hN : 0 < (2 ^ n * P2 p + P1 p) * 2 ^ (n + m + 1 - n) := by
    rw [← sum_whiteBefore' p (n + m + 1) n hn (by omega)]
    rw [chance] at hpos
    exact (div_pos_iff_of_pos_right (lt_of_le_of_ne hT0 (Ne.symm hT))).mp hpos
  have hab : 0 < 2 ^ n * P2 p + P1 p := pos_of_mul_pos_left hN (by positivity)
  have hP2 : 0 ≤ P2 p :=
    Finset.sum_nonneg fun c _ => mul_nonneg (hp c) (by split_ifs <;> norm_num)
  rw [chanceNext_eq p _ n hn (by omega) hT] at hk
  rw [chanceNext_eq p _ (n + m) (by omega) (by omega) hT]
  have := alg (2 ^ n * P2 p) (P1 p) α β m (mul_nonneg (by positivity) hP2) hab
    (by rw [← hk]; ring)
  rw [← this]
  ring

private lemma sum_col (f : Colouring → ℚ) :
    ∑ c, f c = f ![true, true] + f ![true, false] + f ![false, true] + f ![false, false] := by
  rw [← (piFinTwoEquiv (fun _ => Bool)).symm.sum_comp f, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have e : ∀ a b : Bool, (piFinTwoEquiv (fun _ => Bool)).symm (a, b) = ![a, b] := by
    intro a b; ext i; fin_cases i <;> rfl
  simp only [e]
  ring

private lemma wc_vals : wc ![true, true] = 2 ∧ wc ![true, false] = 1 ∧
    wc ![false, true] = 1 ∧ wc ![false, false] = 0 := by
  decide

private lemma P2_one : P2 (fun _ => 1) = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := wc_vals
  rw [P2, sum_col]; simp [h1, h2, h3, h4]

private lemma P1_one : P1 (fun _ => 1) = 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := wc_vals
  rw [P1, sum_col]; simp [h1, h2, h3, h4]; norm_num

/-- With the colourings equally likely, after `j ≥ 1` white draws the chance of white next time
is `(2^j+1)/(2^j+2)`. -/
theorem chanceNextWhite_uniform (L j : ℕ) (hj : 1 ≤ j) (hjL : j < L) :
    chanceNextWhite (fun _ => 1) L ⟨j, hjL⟩ = (2 ^ j + 1) / (2 ^ j + 2) := by
  have hT : ∑ ω : Outcome L, weight (fun _ => (1 : ℚ)) ω ≠ 0 := by
    simp [weight]
  rw [chanceNext_eq _ L j hj hjL hT, P2_one, P1_one]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **Carroll's answer.** With the colourings of the two counters originally equally likely: if
after `n ≥ 1` white draws the chance of white next time is `α/(α+β)`, then after `m` more white
draws it is `(2^m(α-β)+β)/(2^m(α-β)+2β)`. -/
theorem problem66 (n m : ℕ) (hn : 1 ≤ n) (α β : ℚ)
    (hk : chanceNextWhite (fun _ => 1) (n + m + 1) ⟨n, by omega⟩ = α / (α + β)) :
    chanceNextWhite (fun _ => 1) (n + m + 1) ⟨n + m, by omega⟩ =
      (2 ^ m * (α - β) + β) / (2 ^ m * (α - β) + 2 * β) := by
  refine problem66_general _ (fun _ => zero_le_one) n m hn ?_ α β hk
  rw [chance, sum_whiteBefore' _ _ n hn (by omega), P2_one, P1_one]
  apply div_pos (by positivity)
  simp [weight]

/-- The hypothesis of `problem66` can be met: after `n` white draws the chance is
`(2^n+1)/((2^n+1)+1)`, i.e. `α = 2^n+1`, `β = 1`. -/
theorem problem66_nonvacuous (n m : ℕ) (hn : 1 ≤ n) :
    chanceNextWhite (fun _ => 1) (n + m + 1) ⟨n, by omega⟩ =
      (2 ^ n + 1) / ((2 ^ n + 1) + 1) := by
  rw [chanceNextWhite_uniform _ _ hn]
  ring

/-- Carroll's example: if the chance is `9/10` (this happens after `3` white draws) and the
experiment is repeated `5` times more, the chance becomes `257/258`. -/
theorem problem66_example :
    chanceNextWhite (fun _ => 1) (3 + 5 + 1) ⟨3, by omega⟩ = 9 / (9 + 1) ∧
      chanceNextWhite (fun _ => 1) (3 + 5 + 1) ⟨3 + 5, by omega⟩ = 257 / 258 := by
  have h : chanceNextWhite (fun _ => 1) (3 + 5 + 1) ⟨3, by omega⟩ = 9 / (9 + 1) := by
    rw [chanceNextWhite_uniform _ _ (by norm_num)]; norm_num
  refine ⟨h, ?_⟩
  rw [problem66 3 5 (by norm_num) 9 1 h]
  norm_num

end PillowProblems.P66
