import PillowProblems.Basic

/-!
# Problem 45 (Algebra: Chances)

**Question.** *(dated 5/84)*

> If an infinite number of rods be broken: find the chance that one at least is broken in the middle.

**Answer.**

> \[ \cdot 6321207 \quad \&c. \]

*(Carroll's solution: Chapter III, problem 45; text in `data/problems.json`.)*

**Lean reading.** Read literally with a continuous break point, each rod breaks exactly at
its middle with chance `0`, so the question has no content; we formalize Carroll's reading from
his solution. At stage `n = 2k+1` (odd, so that there is a middle point) there are `n` rods, each
rod can break only at one of `n` equally frangible points, the rods break independently, and all
`n^n` cases (`Breaks k`) are equally likely; `chanceMiddle k` is the chance that some rod breaks at
the middle point. Carroll's "infinite number of rods" is the limit `n → ∞`, in which the number
of rods and the number of break points grow together, exactly as in his solution.
`chanceMiddle_eq` is his finite formula `1 - (1 - 1/n)^n`, `problem45` proves the limit is
`1 - e⁻¹` (his `1 - (1 - 0)^(1/0)`), and `problem45_decimal` gives its decimal value. Carroll's
exact answer is right, but his decimal `·6321207 &c.` is not: `1 - e⁻¹ = ·63212055…`, so the
seventh decimal is `5` (`6` rounded), not `7` (his step `3·0861612 - 2·7182818 = ·3678793`
should give `·3678794`).

**Status.** proved (corrected)
-/

namespace PillowProblems.P45

open Filter Topology Real

/-- The `n`-th stage of Carroll's model, with `n = 2k+1` odd: there are `n` rods, each rod can
break only at one of `n` equally frangible points `0, …, n-1`, and the rods break independently.
A case is the list of break points of the `n` rods. -/
abbrev Breaks (k : ℕ) := Fin (2 * k + 1) → Fin (2 * k + 1)

/-- The middle point of a rod divided into `2k+2` equal parts by `2k+1` points. -/
def middle (k : ℕ) : Fin (2 * k + 1) := ⟨k, by omega⟩

/-- The event that at least one rod is broken in the middle. -/
def someMiddle (k : ℕ) (f : Breaks k) : Prop := ∃ i, f i = middle k

instance (k : ℕ) : DecidablePred (someMiddle k) := fun f => by unfold someMiddle; infer_instance

/-- The chance, at stage `n = 2k+1`, that at least one rod is broken in the middle. -/
def chanceMiddle (k : ℕ) : ℚ := uniformChance (someMiddle k)

private lemma card_some (k : ℕ) :
    ((Finset.univ.filter (someMiddle k)).card : ℚ) =
      (2 * k + 1 : ℚ) ^ (2 * k + 1) - (2 * k : ℚ) ^ (2 * k + 1) := by
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Breaks k)))
    (someMiddle k)
  have h2 : (Finset.univ.filter fun f : Breaks k => ¬ someMiddle k f) =
      Fintype.piFinset (fun _ => Finset.univ.erase (middle k)) := by
    ext f; simp [someMiddle, Fintype.mem_piFinset]
  rw [h2, Fintype.card_piFinset] at h1
  simp only [Finset.mem_univ, Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin,
    Finset.prod_const, Fintype.card_pi] at h1
  rw [eq_sub_iff_add_eq]
  have h3 : 2 * k + 1 - 1 = 2 * k := by omega
  rw [h3] at h1
  exact_mod_cast h1

/-- Carroll's finite formula: at stage `n = 2k+1` the chance is `1 - (1 - 1/n)^n`. -/
theorem chanceMiddle_eq (k : ℕ) :
    chanceMiddle k = 1 - (1 - 1 / (2 * k + 1 : ℚ)) ^ (2 * k + 1) := by
  rw [chanceMiddle, uniformChance_eq, card_some]
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ]
  have hpos : (0 : ℚ) < 2 * k + 1 := by positivity
  push_cast
  have hne : (2 * k + 1 : ℚ) ≠ 0 := hpos.ne'
  rw [show (1 : ℚ) - 1 / (2 * k + 1) = 2 * k / (2 * k + 1) by field_simp; ring, div_pow,
    sub_div, div_self (pow_ne_zero _ hne)]

/-- Carroll's answer, exactly: as the number of rods (and of possible break points) tends to
infinity, the chance tends to `1 - (1 - 0)^(1/0) = 1 - e⁻¹`. -/
theorem problem45 :
    Tendsto (fun k => (chanceMiddle k : ℝ)) atTop (𝓝 (1 - exp (-1))) := by
  have h := (Real.tendsto_one_add_div_pow_exp (-1)).comp
    (tendsto_atTop_atTop_of_monotone (fun a b hab => by simp only; omega : Monotone fun k : ℕ => 2 * k + 1)
      (fun b => ⟨b, by omega⟩))
  have h2 := h.const_sub 1
  refine h2.congr (fun k => ?_)
  simp only [Function.comp, chanceMiddle_eq]
  push_cast
  ring

/-- The decimal value: `1 - e⁻¹ = ·6321205…`, so Carroll's seventh decimal (`·6321207`) is wrong. -/
theorem problem45_decimal :
    (0.6321205 : ℝ) < 1 - exp (-1) ∧ 1 - exp (-1) < 0.6321206 ∧
      ¬ ((0.6321207 : ℝ) ≤ 1 - exp (-1) ∧ 1 - exp (-1) < 0.6321208) := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  have he : exp (-1) = (exp 1)⁻¹ := Real.exp_neg 1
  have hpos : 0 < exp 1 := exp_pos 1
  rw [he]
  refine ⟨?_, ?_, ?_⟩
  · rw [← sub_pos]
    have : (exp 1)⁻¹ < 1 / 2.7182818283 := by
      rw [inv_eq_one_div]; exact one_div_lt_one_div_of_lt (by norm_num) h1
    linarith
  · have : 1 / 2.7182818286 < (exp 1)⁻¹ := by
      rw [inv_eq_one_div]; exact one_div_lt_one_div_of_lt hpos h2
    norm_num at this ⊢
    linarith
  · rintro ⟨h, -⟩
    have : 1 / 2.7182818286 < (exp 1)⁻¹ := by
      rw [inv_eq_one_div]; exact one_div_lt_one_div_of_lt hpos h2
    norm_num at this h ⊢
    linarith

end PillowProblems.P45
