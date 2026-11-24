import PillowProblems.Basic

/-!
# Problem 8 (Algebra: Equational Problems)

**Question.** *(dated 3/89)*

> Some men sat in a circle, so that each had 2 neighbours; and each had a certain number of shillings. The first had 1/ more than the second, who had 1/ more than the third, and so on. The first gave 1/ to the second, who gave 2/ to the third, and so on, each giving 1/ more than he received, as long as possible. There were then 2 neighbours, one of whom had 4 times as much as the other. How many men were there? And how much had the poorest man at first?

**Answer.**

> 7 men; 2 shillings.

*(Carroll's solution: Chapter III, problem 8; text in `data/problems.json`.)*

**Lean reading.** The men are numbered `0, …, m - 1` round the circle (`0` is "the first"), with
`3 ≤ m` so that each has two distinct neighbours; their initial shillings `w` drop by 1/ from
each man to the next (`Descending`), so the last man is the poorest. The passing is simulated
step by step exactly as told (`holdings`): at step `t` the man `t % m` hands `t + 1` shillings,
counting what he has just received, to the next man, and it stops at the first step `T` at which
he cannot (`StopsAt`; `problem8_terminates` shows such a `T` always exists). Holdings are
integers so that the simulation is a total function; before `T` no one ever goes negative.
The theorem is an iff: the stopped position has two neighbours in the ratio 4 : 1 exactly when
there are 7 men and the poorest started with 2/, so Carroll's answer is the only one.

**Status.** proved
-/

namespace PillowProblems.P08

/-- Step `t` of the passing (counting from `0`): man `t % m` hands `t + 1` shillings to his
neighbour `(t + 1) % m`. So the first man gives 1/ to the second, who gives 2/ to the third, and so
on round the circle, each giving 1/ more than he received. -/
def transfer (m : ℕ) (h : ℕ → ℤ) (t : ℕ) : ℕ → ℤ := fun i =>
  h i - (if i = t % m then ((t : ℤ) + 1) else 0) + (if i = (t + 1) % m then ((t : ℤ) + 1) else 0)

/-- What every man holds after the first `t` steps, the men starting with `w i` shillings. -/
def holdings (m : ℕ) (w : ℕ → ℕ) : ℕ → ℕ → ℤ
  | 0 => fun i => (w i : ℤ)
  | t + 1 => transfer m (holdings m w t) t

/-- At step `t` the man whose turn it is can hand on `t + 1` shillings. -/
def CanGive (m : ℕ) (w : ℕ → ℕ) (t : ℕ) : Prop := (t : ℤ) + 1 ≤ holdings m w t (t % m)

/-- The passing goes on "as long as possible": every step before `T` can be made, step `T`
cannot. -/
def StopsAt (m : ℕ) (w : ℕ → ℕ) (T : ℕ) : Prop := (∀ t < T, CanGive m w t) ∧ ¬ CanGive m w T

/-- "The first had 1/ more than the second, who had 1/ more than the third, and so on". -/
def Descending (m : ℕ) (w : ℕ → ℕ) : Prop := ∀ i, i + 1 < m → w i = w (i + 1) + 1

/-- Two neighbours, one of whom has 4 times as much as the other. -/
def FourfoldNeighbours (m : ℕ) (h : ℕ → ℤ) : Prop :=
  ∃ i < m, h i = 4 * h ((i + 1) % m) ∨ h ((i + 1) % m) = 4 * h i

private lemma turns_succ (m t i : ℕ) (hi : i < m) :
    (t + 1 + (m - 1 - i)) / m = (t + (m - 1 - i)) / m + if i = t % m then 1 else 0 := by
  have hm : 0 < m := by omega
  rw [show t + 1 + (m - 1 - i) = (t + (m - 1 - i)) + 1 by omega, Nat.succ_div]
  congr 1
  have key : m ∣ t + (m - 1 - i) + 1 ↔ t % m = i := by
    have ht := Nat.div_add_mod t m
    have hr := Nat.mod_lt t hm
    rw [show t + (m - 1 - i) + 1 = m * (t / m) + (t % m + (m - i)) by omega,
      Nat.dvd_add_right (dvd_mul_right m (t / m))]
    constructor
    · rintro ⟨k, hk⟩
      rcases k with _ | _ | k
      · omega
      · omega
      · rw [show m * (k + 1 + 1) = m * k + 2 * m by ring] at hk
        omega
    · intro h; exact ⟨1, by omega⟩
  have key' : m ∣ t + (m - 1 - i) + 1 ↔ i = t % m := key.trans eq_comm
  simp only [key']

private lemma holdings_eq (m : ℕ) (w : ℕ → ℕ) (t i : ℕ) (hi : i < m) :
    holdings m w t i =
      (w i : ℤ) - ((t + (m - 1 - i)) / m : ℕ) + (if i = t % m then (t : ℤ) else 0) := by
  induction t with
  | zero =>
    simp [holdings, Nat.div_eq_of_lt (show m - 1 - i < m by omega)]
  | succ t ih =>
    show transfer m (holdings m w t) t i = _
    simp only [transfer, ih, turns_succ m t i hi]
    split_ifs <;> push_cast <;> ring

private lemma w_eq (m : ℕ) (w : ℕ → ℕ) (hw : Descending m w) (i : ℕ) (hi : i < m) :
    w i = w (m - 1) + (m - 1 - i) := by
  have key : ∀ j, j ≤ m - 1 → w (m - 1 - j) = w (m - 1) + j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have := hw (m - 1 - (j + 1)) (by omega)
      rw [show m - 1 - (j + 1) + 1 = m - 1 - j by omega] at this
      rw [this, ih (by omega)]; ring
  have := key (m - 1 - i) (by omega)
  rwa [show m - 1 - (m - 1 - i) = i by omega] at this

private lemma canGive_iff (m : ℕ) (w : ℕ → ℕ) (hm : 0 < m) (hw : Descending m w) (t : ℕ) :
    CanGive m w t ↔ t / m + 1 + t % m ≤ w (m - 1) + (m - 1) := by
  have hr := Nat.mod_lt t hm
  unfold CanGive
  rw [holdings_eq m w t (t % m) hr, ite_eq_left rfl, w_eq m w hw _ hr]
  have hdiv : (t + (m - 1 - t % m)) / m = t / m := by
    have ht := Nat.div_add_mod t m
    rw [show t + (m - 1 - t % m) = m * (t / m) + (m - 1) by omega, Nat.mul_add_div hm,
      Nat.div_eq_of_lt (by omega : m - 1 < m)]
    simp
  rw [hdiv]
  omega

private lemma stop_time (m : ℕ) (w : ℕ → ℕ) (hm : 0 < m) (hw : Descending m w) (T : ℕ) :
    StopsAt m w T ↔ T = m * w (m - 1) + (m - 1) := by
  set k := w (m - 1) with hk
  have cant : ¬ CanGive m w (m * k + (m - 1)) := by
    rw [canGive_iff m w hm hw, ← hk]
    have hdiv : (m * k + (m - 1)) / m = k := by
      rw [Nat.mul_add_div hm, Nat.div_eq_of_lt (by omega : m - 1 < m)]; simp
    have hdm := Nat.div_add_mod (m * k + (m - 1)) m
    rw [hdiv] at hdm ⊢
    omega
  have can : ∀ t < m * k + (m - 1), CanGive m w t := by
    intro t ht
    rw [canGive_iff m w hm hw, ← hk]
    have hdm := Nat.div_add_mod t m
    have hr := Nat.mod_lt t hm
    rcases lt_or_ge (t / m) k with hq | hq
    · omega
    · have h2 : t / m ≤ k := by
        by_contra hc
        push Not at hc
        have := Nat.mul_le_mul_left m (show k + 1 ≤ t / m by omega)
        rw [Nat.mul_add, Nat.mul_one] at this
        omega
      have hq' : t / m = k := le_antisymm h2 hq
      rw [hq'] at hdm ⊢
      omega
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy T (m * k + (m - 1)) with h | h | h
    · exact absurd (can T h) h2
    · exact h
    · exact absurd (h1 _ h) cant
  · rintro rfl; exact ⟨can, cant⟩

private lemma final_holdings (m : ℕ) (w : ℕ → ℕ) (hm : 0 < m) (hw : Descending m w) (i : ℕ)
    (hi : i < m) :
    holdings m w (m * w (m - 1) + (m - 1)) i =
      if i = m - 1 then (m : ℤ) * w (m - 1) + m - 1 else (m : ℤ) - 2 - i := by
  set k := w (m - 1) with hk
  have hmod : (m * k + (m - 1)) % m = m - 1 := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
  rw [holdings_eq m w _ i hi, hmod, w_eq m w hw i hi, ← hk]
  by_cases h : i = m - 1
  · subst h
    have hdiv : (m * k + (m - 1) + (m - 1 - (m - 1))) / m = k := by
      rw [show m - 1 - (m - 1) = 0 by omega, Nat.add_zero, Nat.mul_add_div hm,
        Nat.div_eq_of_lt (by omega : m - 1 < m)]; simp
    rw [hdiv, ite_eq_left rfl, ite_eq_left rfl]
    have : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    simp only [Nat.sub_self]
    push_cast [this]
    ring
  · have hdiv : (m * k + (m - 1) + (m - 1 - i)) / m = k + 1 := by
      rw [show m * k + (m - 1) + (m - 1 - i) = m * (k + 1) + (m - 2 - i) by
        rw [Nat.mul_add]; omega, Nat.mul_add_div hm, Nat.div_eq_of_lt (by omega : m - 2 - i < m)]
    rw [hdiv, ite_eq_right h, ite_eq_right h]
    push_cast
    omega

/-- The final position has two neighbours, one with 4 times as much as the other, exactly when
there are 7 men and the poorest had 2 shillings at first. -/
theorem problem8 (m : ℕ) (w : ℕ → ℕ) (T : ℕ) (hm : 3 ≤ m) (hw : Descending m w)
    (hT : StopsAt m w T) :
    FourfoldNeighbours m (holdings m w T) ↔ m = 7 ∧ IsLeast (w '' Set.Iio m) 2 := by
  have hm0 : 0 < m := by omega
  rw [(stop_time m w hm0 hw T).mp hT]
  have hleast : IsLeast (w '' Set.Iio m) (w (m - 1)) := by
    refine ⟨⟨m - 1, by simp; omega, rfl⟩, ?_⟩
    rintro _ ⟨i, hi, rfl⟩
    rw [w_eq m w hw i hi]; omega
  have hiff : IsLeast (w '' Set.Iio m) 2 ↔ w (m - 1) = 2 :=
    ⟨fun h => hleast.unique h, fun h => h ▸ hleast⟩
  rw [hiff]
  have F := final_holdings m w hm0 hw
  set k := w (m - 1) with hk
  have hm3 : (3 : ℤ) ≤ m := by exact_mod_cast hm
  have hk0 : (0 : ℤ) ≤ k := by positivity
  constructor
  · rintro ⟨i, hi, h⟩
    rcases lt_trichotomy (i + 2) m with h3 | h3 | h3
    · rw [Nat.mod_eq_of_lt (by omega), F i hi, F (i + 1) (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)] at h
      push_cast at h
      omega
    · rw [Nat.mod_eq_of_lt (by omega), F i hi, F (i + 1) (by omega), ite_eq_right (by omega),
        ite_eq_left (by omega)] at h
      have hi2 : (i : ℤ) = m - 2 := by omega
      rw [hi2] at h
      rcases h with h | h <;> nlinarith
    · have hi' : i = m - 1 := by omega
      rw [hi', show m - 1 + 1 = m by omega, Nat.mod_self, F (m - 1) (by omega), F 0 hm0,
        ite_eq_left rfl, ite_eq_right (by omega)] at h
      push_cast at h
      rcases h with h | h
      · have hk2 : k ≤ 2 := by
          by_contra hc
          have : (3 : ℤ) ≤ k := by exact_mod_cast (show 3 ≤ k by omega)
          nlinarith
        interval_cases k
        · push_cast at h; omega
        · push_cast at h; omega
        · push_cast at h
          exact ⟨by omega, rfl⟩
      · nlinarith
  · rintro ⟨rfl, hk2⟩
    refine ⟨6, by norm_num, Or.inl ?_⟩
    rw [F 6 (by norm_num), F ((6 + 1) % 7) (by norm_num), hk2]
    norm_num

/-- The passing always stops. -/
theorem problem8_terminates (m : ℕ) (w : ℕ → ℕ) (hm : 0 < m) (hw : Descending m w) :
    ∃ T, StopsAt m w T :=
  ⟨_, (stop_time m w hm hw _).mpr rfl⟩

/-- The situation of the problem occurs (7 men holding 8/, 7/, …, 2/). -/
theorem problem8_nonvacuous :
    ∃ (w : ℕ → ℕ) (T : ℕ), Descending 7 w ∧ StopsAt 7 w T ∧
      FourfoldNeighbours 7 (holdings 7 w T) := by
  have hw : Descending 7 (fun i => 8 - i) := by
    intro i hi; simp only; omega
  obtain ⟨T, hT⟩ := problem8_terminates 7 _ (by norm_num) hw
  refine ⟨_, T, hw, hT, ?_⟩
  rw [problem8 7 _ T (by norm_num) hw hT]
  refine ⟨rfl, ⟨6, by simp, rfl⟩, ?_⟩
  rintro _ ⟨i, hi, rfl⟩
  simp only [Set.mem_Iio] at hi
  show 2 ≤ 8 - i
  omega

end PillowProblems.P08
