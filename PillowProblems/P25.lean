import PillowProblems.Basic

/-!
# Problem 25 (Algebra: Equational Problems)

**Question.** *(dated 7/2/76)*

> If '\(\epsilon\)', '\(\alpha\)', '\(\lambda\)' represent proper fractions; and if, in a certain hospital, '\(\epsilon\)' of the patients have lost an eye, '\(\alpha\)' an arm, and '\(\lambda\)' a leg: what is the least possible number who have lost all three?

**Answer.**

> \[\epsilon + \alpha + \lambda - 2.\]

*(Carroll's solution: Chapter III, problem 25; text in `data/problems.json`.)*

**Lean reading.** The patients are `Fin N` (`0 < N`) and `E, A, L` are the sets who have lost an eye, an
arm, a leg, with `|E| = ε N`, `|A| = α N`, `|L| = ℓ N` (`ℓ` stands for Carroll's λ, a reserved
word in Lean). Like Carroll's answer, the "number" is measured as a fraction of all patients. The
hypotheses `ε, α, ℓ ≤ 1` and "`ε N`, `α N`, `ℓ N` are whole numbers" are needed for such a
hospital to exist; "proper" (`0 < ε < 1` etc.) is not needed. Carroll's answer `ε + α + λ - 2`
is right only when `ε + α + λ ≥ 2`; otherwise it is negative and the least possible fraction is
`0` (e.g. `ε = α = λ = 1/2`, `problem25_formula_fails`). So the theorem proves the least possible
fraction is `max (ε + α + ℓ - 2) 0` (`problem25`), which is Carroll's value when
`ε + α + ℓ ≥ 2` (`problem25_carroll`). The minimising arrangement is Carroll's row: the
`EA`-class is made as small as possible and the `L`-class starts from the other end.

**Status.** proved (corrected)
-/

namespace PillowProblems.P25

/-- The possible fractions of the `N` patients who have lost all three, when the fractions `ε`,
`α`, `ℓ` of them have lost an eye, an arm, a leg. -/
def allThreeFractions (N : ℕ) (ε α ℓ : ℚ) : Set ℚ :=
  {q | ∃ E A L : Finset (Fin N), (E.card : ℚ) = ε * N ∧ (A.card : ℚ) = α * N ∧
    (L.card : ℚ) = ℓ * N ∧ q = ((E ∩ A ∩ L).card : ℚ) / N}

private lemma card_filter_val (N : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun i : Fin N => p i.val)).card = ((Finset.range N).filter p).card := by
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hi ⊢
    exact ⟨i.isLt, hi⟩
  · intro i _ j _ h; exact Fin.ext h
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    exact ⟨⟨j, hj.1⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hj.2, rfl⟩

private lemma lower_bound (N : ℕ) (E A L : Finset (Fin N)) :
    E.card + A.card + L.card ≤ (E ∩ A ∩ L).card + 2 * N := by
  have h1 := Finset.card_union_add_card_inter E A
  have h2 := Finset.card_union_add_card_inter (E ∩ A) L
  have h3 : (E ∪ A).card ≤ N := by simpa using Finset.card_le_univ (E ∪ A)
  have h4 : (E ∩ A ∪ L).card ≤ N := by simpa using Finset.card_le_univ (E ∩ A ∪ L)
  omega

private lemma construction (N e a l : ℕ) (he : e ≤ N) (ha : a ≤ N) (hl : l ≤ N) :
    ∃ E A L : Finset (Fin N), E.card = e ∧ A.card = a ∧ L.card = l ∧
      (E ∩ A ∩ L).card = e + a + l - 2 * N := by
  set x := e + a - N with hx
  refine ⟨Finset.univ.filter (fun i : Fin N => i.val < e),
    Finset.univ.filter (fun i : Fin N => i.val < x ∨ (e ≤ i.val ∧ i.val < e + a - x)),
    Finset.univ.filter (fun i : Fin N => N - l ≤ i.val), ?_, ?_, ?_, ?_⟩
  · rw [card_filter_val N (fun j => j < e)]
    rw [show (Finset.range N).filter (· < e) = Finset.range e by
      ext j; simp; omega]
    simp
  · rw [card_filter_val N (fun j => j < x ∨ (e ≤ j ∧ j < e + a - x))]
    rw [show (Finset.range N).filter (fun j => j < x ∨ (e ≤ j ∧ j < e + a - x)) =
        Finset.range x ∪ Finset.Ico e (e + a - x) by ext j; simp; omega]
    rw [Finset.card_union_of_disjoint]
    · simp; omega
    · rw [Finset.disjoint_left]; intro j h1 h2; simp at h1 h2; omega
  · rw [card_filter_val N (fun j => N - l ≤ j)]
    rw [show (Finset.range N).filter (fun j => N - l ≤ j) = Finset.Ico (N - l) N by
      ext j; simp; omega]
    simp; omega
  · rw [show Finset.univ.filter (fun i : Fin N => i.val < e) ∩
        Finset.univ.filter (fun i : Fin N => i.val < x ∨ (e ≤ i.val ∧ i.val < e + a - x)) ∩
        Finset.univ.filter (fun i : Fin N => N - l ≤ i.val) =
        Finset.univ.filter (fun i : Fin N => i.val < e ∧ (i.val < x ∨ (e ≤ i.val ∧ i.val < e + a - x)) ∧ N - l ≤ i.val) by
      ext i; simp]
    rw [card_filter_val N (fun j => j < e ∧ (j < x ∨ (e ≤ j ∧ j < e + a - x)) ∧ N - l ≤ j)]
    rw [show (Finset.range N).filter (fun j => j < e ∧ (j < x ∨ (e ≤ j ∧ j < e + a - x)) ∧ N - l ≤ j) =
        Finset.Ico (N - l) x by ext j; simp; omega]
    simp; omega

/-- The least possible fraction who have lost all three is `max (ε + α + ℓ - 2) 0`. -/
theorem problem25 (N : ℕ) (hN : 0 < N) (ε α ℓ : ℚ) (hε : ε ≤ 1) (hα : α ≤ 1) (hℓ : ℓ ≤ 1)
    (hεN : ∃ e : ℕ, (e : ℚ) = ε * N) (hαN : ∃ a : ℕ, (a : ℚ) = α * N)
    (hℓN : ∃ l : ℕ, (l : ℚ) = ℓ * N) :
    IsLeast (allThreeFractions N ε α ℓ) (max (ε + α + ℓ - 2) 0) := by
  obtain ⟨e, he⟩ := hεN
  obtain ⟨a, ha⟩ := hαN
  obtain ⟨l, hl⟩ := hℓN
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have heN : e ≤ N := by
    have : (e : ℚ) ≤ N := by rw [he]; nlinarith
    exact_mod_cast this
  have haN : a ≤ N := by
    have : (a : ℚ) ≤ N := by rw [ha]; nlinarith
    exact_mod_cast this
  have hlN : l ≤ N := by
    have : (l : ℚ) ≤ N := by rw [hl]; nlinarith
    exact_mod_cast this
  constructor
  · obtain ⟨E, A, L, hE, hA, hL, hT⟩ := construction N e a l heN haN hlN
    refine ⟨E, A, L, by rw [hE, he], by rw [hA, ha], by rw [hL, hl], ?_⟩
    rw [hT]
    rcases le_total (2 * N) (e + a + l) with h | h
    · rw [Nat.cast_sub h]; push_cast
      rw [he, ha, hl, max_eq_left]
      · rw [eq_div_iff hNq.ne']; ring
      · have : (2 * N : ℚ) ≤ e + a + l := by exact_mod_cast h
        rw [he, ha, hl] at this
        nlinarith
    · rw [Nat.sub_eq_zero_of_le h, max_eq_right]
      · simp
      · have : (e + a + l : ℚ) ≤ 2 * N := by exact_mod_cast h
        rw [he, ha, hl] at this
        nlinarith
  · rintro q ⟨E, A, L, hE, hA, hL, rfl⟩
    apply max_le
    · rw [le_div_iff₀ hNq]
      have := lower_bound N E A L
      have h' : (E.card + A.card + L.card : ℚ) ≤ (E ∩ A ∩ L).card + 2 * N := by exact_mod_cast this
      rw [hE, hA, hL] at h'
      linarith
    · positivity

/-- Carroll's answer: when `ε + α + ℓ ≥ 2` the least possible fraction is `ε + α + ℓ - 2`. -/
theorem problem25_carroll (N : ℕ) (hN : 0 < N) (ε α ℓ : ℚ) (hε : ε ≤ 1) (hα : α ≤ 1) (hℓ : ℓ ≤ 1)
    (hεN : ∃ e : ℕ, (e : ℚ) = ε * N) (hαN : ∃ a : ℕ, (a : ℚ) = α * N)
    (hℓN : ∃ l : ℕ, (l : ℚ) = ℓ * N) (h2 : 2 ≤ ε + α + ℓ) :
    IsLeast (allThreeFractions N ε α ℓ) (ε + α + ℓ - 2) := by
  have := problem25 N hN ε α ℓ hε hα hℓ hεN hαN hℓN
  rwa [max_eq_left (by linarith)] at this

/-- Without `ε + α + ℓ ≥ 2` Carroll's formula fails: with `ε = α = ℓ = 1/2` the least fraction
is `0`, not `-1/2`. -/
theorem problem25_formula_fails :
    IsLeast (allThreeFractions 2 (1/2) (1/2) (1/2)) 0 ∧
      ¬ IsLeast (allThreeFractions 2 (1/2) (1/2) (1/2)) (1/2 + 1/2 + 1/2 - 2) := by
  have h := problem25 2 (by norm_num) (1/2) (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
    ⟨1, by norm_num⟩ ⟨1, by norm_num⟩ ⟨1, by norm_num⟩
  norm_num at h
  refine ⟨h, fun h' => ?_⟩
  have := h.unique h'
  norm_num at this

end PillowProblems.P25
