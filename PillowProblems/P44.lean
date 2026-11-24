import PillowProblems.Basic

/-!
# Problem 44 (Algebra: Properties of Numbers)

**Question.** *(dated 18/3/81)*

> If \(a\), \(b\) be two numbers prime to each other, a value may be found for \(n\) which will make \((a^{n} - 1)\) a multiple of \(b\).

*(Carroll's solution: Chapter III, problem 44; text in `data/problems.json`.)*

**Lean reading.** `a, b` are integers (this includes Carroll's whole numbers) with
`IsCoprime a b`, and the claim is that some *positive* exponent `n` makes `b ∣ aⁿ - 1`
(`n = 0` would make the statement trivial, so positivity is required). Carroll's proof via
circulating decimals in radix `a` is replaced by Euler's theorem in `ZMod |b|`, with
`n = φ(|b|)`; the case `b = 0` (where `a = ±1`) is handled with `n = 2`.
`problem44_examples` checks Carroll's three examples, together with the fact that each of his
values of `n` (the period of `1/b` in radix `a`) is the least one.

**Status.** proved
-/

namespace PillowProblems.P44

/-- If `a, b` are coprime, some positive power of `a` is `≡ 1 (mod b)`. -/
theorem problem44 (a b : ℤ) (h : IsCoprime a b) : ∃ n : ℕ, 0 < n ∧ b ∣ a ^ n - 1 := by
  rcases eq_or_ne b 0 with rfl | hb
  · have : IsUnit a := isCoprime_zero_right.1 h
    refine ⟨2, two_pos, ?_⟩
    rcases Int.isUnit_iff.1 this with rfl | rfl <;> norm_num
  · set m := b.natAbs with hm
    have hm0 : m ≠ 0 := Int.natAbs_ne_zero.2 hb
    have : NeZero m := ⟨hm0⟩
    obtain ⟨u, v, huv⟩ := h
    have hb0 : ((b : ℤ) : ZMod m) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Int.natAbs_dvd.2 dvd_rfl
    have hunit : IsUnit ((a : ℤ) : ZMod m) := by
      refine IsUnit.of_mul_eq_one ((u : ℤ) : ZMod m) ?_
      have := congrArg (fun t : ℤ => (t : ZMod m)) huv
      push_cast at this
      rw [hb0] at this
      linear_combination this
    refine ⟨Nat.totient m, Nat.totient_pos.2 (Nat.pos_of_ne_zero hm0), ?_⟩
    have key : ((a : ℤ) : ZMod m) ^ Nat.totient m = 1 := by
      have := congrArg Units.val (ZMod.pow_totient hunit.unit)
      rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at this
    have : ((a ^ Nat.totient m - 1 : ℤ) : ZMod m) = 0 := by
      push_cast; rw [key]; ring
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    exact Int.natAbs_dvd.1 this

/-- Carroll's examples: `10⁶ - 1` is a multiple of 7, `8² - 1` of 9, `7¹² - 1` of 13, and in each
case no smaller positive exponent works. -/
theorem problem44_examples :
    (7 ∣ 10 ^ 6 - 1 ∧ ∀ n < 6, 0 < n → ¬ 7 ∣ 10 ^ n - 1) ∧
      (9 ∣ 8 ^ 2 - 1 ∧ ∀ n < 2, 0 < n → ¬ 9 ∣ 8 ^ n - 1) ∧
      (13 ∣ 7 ^ 12 - 1 ∧ ∀ n < 12, 0 < n → ¬ 13 ∣ 7 ^ n - 1) := by
  decide

end PillowProblems.P44
