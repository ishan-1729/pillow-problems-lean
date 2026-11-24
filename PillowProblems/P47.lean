import PillowProblems.Basic

/-!
# Problem 47 (Algebra: Indeterminate Equations)

**Question.** *(dated 12/90)*

> Solve the 2 Indeterminate Equations
>
> \[ \left. \begin{array}{c} \frac{x}{y} = x - z;\\ \frac{x}{z} = x - y;\\ \end{array} \right\} \left. \begin{array}{c} \qquad \text{(1)}\\ \qquad \text{(2)}\\ \end{array} \right. \] and find the limits, if any, between which the *real* values lie.

**Answer.**

> One set of values is 0, 0, 0.
>
> A 2nd set is \(x = y = 0\); \(z\) has any value.
>
> A 3rd is \(x = z = 0\); \(y\) has any value.
>
> And the 4th set is \(x = \dfrac{k^{2}}{k - 1}\), \(y = z = k\); where \(k\) has any value.
>
> If \(x\) has any positive value less than 4, \(y\) and \(z\) are unreal.

*(Carroll's solution: Chapter III, problem 47; text in `data/problems.json`.)*

**Lean reading.** The unknowns are real. Carroll's answer admits `x = y = 0`
with `z` arbitrary, where `x/y` is `0/0`, so he reads the equations cleared of fractions:
`Eqns x y z` is `x = y(x - z) ∧ x = z(x - y)` (`strictEqns_iff` shows this agrees with the
quotient form whenever `y, z ≠ 0`). `problem47_a` proves that the solutions are exactly Carroll's
four sets; in the fourth set we add `k ≠ 1`, since for `k = 1` his `x = k²/(k-1)` is infinite
(Carroll's "unless `x` be infinite"), not a real solution. "The limits between which the real
values lie" is read, as in his solution, as the set of values each unknown takes: `problem47_b`
shows `x` ranges over exactly `x ≤ 0` or `x ≥ 4` (so no real solution has `0 < x < 4`), and
`problem47_c` that `y` and `z` take every real value; `problem47_d` proves Carroll's
"`y` and `z` are unreal" over `ℂ`: for real `0 < x < 4` complex solutions exist and in all of
them `y, z` have nonzero imaginary part. As a supplement, `problem47_strict` shows
that if `y = 0` or `z = 0` is forbidden only the fourth set (with `k ≠ 0, 1`) remains.

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P47

/-- Carroll's equations `x/y = x - z`, `x/z = x - y`, cleared of fractions as he treats them
(so that `0/0` is admitted as "any value"): `x = y(x - z)` and `x = z(x - y)`. -/
def Eqns (x y z : ℝ) : Prop := x = y * (x - z) ∧ x = z * (x - y)

/-- The equations in the strict sense: `y, z ≠ 0` and the quotients are genuine quotients. -/
def StrictEqns (x y z : ℝ) : Prop := y ≠ 0 ∧ z ≠ 0 ∧ x / y = x - z ∧ x / z = x - y

/-- Where the denominators are nonzero, the two readings agree. -/
theorem strictEqns_iff (x y z : ℝ) : StrictEqns x y z ↔ y ≠ 0 ∧ z ≠ 0 ∧ Eqns x y z := by
  unfold StrictEqns Eqns
  constructor
  · rintro ⟨hy, hz, h1, h2⟩
    refine ⟨hy, hz, ?_, ?_⟩
    · rw [div_eq_iff hy] at h1; linarith
    · rw [div_eq_iff hz] at h2; linarith
  · rintro ⟨hy, hz, h1, h2⟩
    refine ⟨hy, hz, ?_, ?_⟩
    · rw [div_eq_iff hy]; linarith
    · rw [div_eq_iff hz]; linarith

/-- The solutions: Carroll's four sets of values, and no others. In the fourth set `k ≠ 1`
(for `k = 1` his `x = k²/(k-1)` is infinite). -/
theorem problem47_a (x y z : ℝ) :
    Eqns x y z ↔
      (x = 0 ∧ y = 0 ∧ z = 0) ∨
      (x = 0 ∧ y = 0) ∨
      (x = 0 ∧ z = 0) ∨
      (∃ k : ℝ, k ≠ 1 ∧ x = k ^ 2 / (k - 1) ∧ y = k ∧ z = k) := by
  unfold Eqns
  constructor
  · rintro ⟨h1, h2⟩
    have hxyz : x * (y - z) = 0 := by linear_combination h2 - h1
    rcases mul_eq_zero.1 hxyz with hx | hyz
    · subst hx
      have : y * z = 0 := by linear_combination h1
      rcases mul_eq_zero.1 this with hy | hz
      · exact Or.inr (Or.inl ⟨rfl, hy⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, hz⟩))
    · have hzy : z = y := by linarith
      subst hzy
      have hk : z ≠ 1 := by
        rintro rfl
        linarith
      refine Or.inr (Or.inr (Or.inr ⟨z, hk, ?_, rfl, rfl⟩))
      have : z - 1 ≠ 0 := sub_ne_zero.2 hk
      field_simp
      linarith
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨k, hk, hx, hy, hz⟩)
    · norm_num
    · norm_num
    · norm_num
    · rw [hx, hy, hz]
      have : k - 1 ≠ 0 := sub_ne_zero.2 hk
      constructor <;> field_simp <;> ring

private lemma exists_k {x : ℝ} (hx : x ≤ 0 ∨ 4 ≤ x) :
    ∃ k : ℝ, k ^ 2 - x * k + x = 0 := by
  have hd : 0 ≤ x ^ 2 - 4 * x := by rcases hx with hx | hx <;> nlinarith
  refine ⟨(x + Real.sqrt (x ^ 2 - 4 * x)) / 2, ?_⟩
  have hs := Real.sq_sqrt hd
  linear_combination hs / 4

/-- The limits of the real values: `x` takes exactly the values `x ≤ 0` and `x ≥ 4`; in
particular, for `0 < x < 4` there are no real `y, z`. -/
theorem problem47_b :
    {x : ℝ | ∃ y z, Eqns x y z} = Set.Iic 0 ∪ Set.Ici 4 ∧
    ∀ x : ℝ, 0 < x → x < 4 → ¬ ∃ y z, Eqns x y z := by
  have key : {x : ℝ | ∃ y z, Eqns x y z} = Set.Iic 0 ∪ Set.Ici 4 := by
    ext x
    rw [Set.mem_union, Set.mem_Iic, Set.mem_Ici]
    constructor
    · rintro ⟨y, z, h1, h2⟩
      by_contra hc
      simp only [not_or, not_le] at hc
      have hxyz : x * (y - z) = 0 := by linear_combination h2 - h1
      rcases mul_eq_zero.1 hxyz with hx | hyz
      · linarith [hc.1]
      · have hzy : z = y := by linarith
        subst hzy
        -- `z² - x z + x = 0` has no real root when `0 < x < 4`
        nlinarith [sq_nonneg (2 * z - x), hc.1, hc.2]
    · intro hx
      obtain ⟨k, hk⟩ := exists_k hx
      exact ⟨k, k, by constructor <;> linear_combination hk⟩
  refine ⟨key, ?_⟩
  intro x h0 h4 hex
  have : x ∈ {x : ℝ | ∃ y z, Eqns x y z} := hex
  rw [key] at this
  rcases this with h | h
  · exact absurd (Set.mem_Iic.1 h) (not_le.2 h0)
  · exact absurd (Set.mem_Ici.1 h) (not_le.2 h4)

/-- `y` and `z` may have any real values. -/
theorem problem47_c :
    {y : ℝ | ∃ x z, Eqns x y z} = Set.univ ∧ {z : ℝ | ∃ x y, Eqns x y z} = Set.univ := by
  constructor
  · exact Set.eq_univ_of_forall fun y => ⟨0, 0, by unfold Eqns; constructor <;> ring⟩
  · exact Set.eq_univ_of_forall fun z => ⟨0, 0, by unfold Eqns; constructor <;> ring⟩

/-- Carroll's equations over `ℂ`, cleared of fractions as in `Eqns`. -/
def EqnsC (x y z : ℂ) : Prop := x = y * (x - z) ∧ x = z * (x - y)

/-- Carroll's last sentence: if `x` has a positive value less than `4`, then `y` and `z` are
unreal — there are complex solutions, and in every one of them `y` and `z` are not real. -/
theorem problem47_d (x : ℝ) (h0 : 0 < x) (h4 : x < 4) :
    (∃ y z : ℂ, EqnsC x y z) ∧ ∀ y z : ℂ, EqnsC x y z → y.im ≠ 0 ∧ z.im ≠ 0 := by
  constructor
  · have hd : 0 ≤ 4 * x - x ^ 2 := by nlinarith
    have hs := Real.sq_sqrt hd
    set s := Real.sqrt (4 * x - x ^ 2)
    refine ⟨⟨x / 2, s / 2⟩, ⟨x / 2, s / 2⟩, ?_, ?_⟩ <;>
      apply Complex.ext <;> simp <;> nlinarith
  · rintro y z ⟨h1, h2⟩
    have hxyz : (x : ℂ) * (y - z) = 0 := by linear_combination h2 - h1
    have hx : (x : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    have hyz : y = z := by
      have := (mul_eq_zero.1 hxyz).resolve_left hx
      linear_combination this
    subst hyz
    have hq : y * y - x * y + x = 0 := by linear_combination h1
    have hre := congrArg Complex.re hq
    have him := congrArg Complex.im hq
    simp at hre him
    have : y.im ≠ 0 := by
      intro hb
      rw [hb] at hre
      nlinarith [sq_nonneg (2 * y.re - x)]
    exact ⟨this, this⟩

/-- Under the strict reading (`y, z ≠ 0`), only Carroll's fourth set survives, with `k ≠ 0, 1`. -/
theorem problem47_strict (x y z : ℝ) :
    StrictEqns x y z ↔ ∃ k : ℝ, k ≠ 0 ∧ k ≠ 1 ∧ x = k ^ 2 / (k - 1) ∧ y = k ∧ z = k := by
  rw [strictEqns_iff, problem47_a]
  constructor
  · rintro ⟨hy, hz, ⟨-, h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨k, hk, hx, hyk, hzk⟩⟩
    · exact absurd h hy
    · exact absurd h hy
    · exact absurd h hz
    · exact ⟨k, hyk ▸ hy, hk, hx, hyk, hzk⟩
  · rintro ⟨k, hk0, hk1, hx, hy, hz⟩
    exact ⟨hy ▸ hk0, hz ▸ hk0, Or.inr (Or.inr (Or.inr ⟨k, hk1, hx, hy, hz⟩))⟩

end PillowProblems.P47
