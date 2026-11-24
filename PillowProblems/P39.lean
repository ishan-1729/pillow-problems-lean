import PillowProblems.Basic

/-!
# Problem 39 (Algebra: Equational Problems)

**Question.** *(dated 16/3/78)*

> \(A\) and \(B\) begin, at 6 a. m. on the same day, to walk along a road in the same direction, \(B\) having a start of 14 miles, and each walking from 6 a. m. to 6 p. m. daily. \(A\) walks 10 miles, at a uniform pace, the first day, 9 the second, 8 the third, and so on: \(B\) walks 2 miles, at a uniform pace, the first day, 4 the second, 6 the third, and so on. When and where are they together?

**Answer.**

> They meet at end of 2*d.* 6*h.*, and at end of 4*d.*: and the distances are 23 miles, and 34 miles.

*(Carroll's solution: Chapter III, problem 39; text in `data/problems.json`.)*

**Lean reading.** A moment is given as `(n, h)`: `n` whole days and `h ∈ [0, 24)` hours after 6
a.m. on the first day. Each walks his `k`-th day's distance at a uniform pace from 6 a.m. to
6 p.m. (the first 12 hours) and stands still overnight (`walked`). A's `k`-th day's distance is
`11 - k` while that is positive and `0` afterwards (the "and so on" sequence ends after the tenth
day). B's is `2k`. Positions are measured from A's starting point, with B starting 14 miles
ahead. `problem39` lists every moment at which they are together: `(2, 6)`, Carroll's "2*d.* 6*h.*"
(noon of the third day), and every moment from `(3, 12)` to `(4, 0)` inclusive. Carroll's "end of
4*d.*" is 6 p.m. of the fourth day, when they meet; since neither walks at night, they stay
together until 6 a.m. of the fifth day. `problem39_where` gives the places, 23 and 34 miles.

**Status.** proved
-/

namespace PillowProblems.P39

open Finset

/-- The miles A walks on his `k`-th day (`k ≥ 1`): 10, 9, 8, …, and nothing once that reaches 0. -/
noncomputable def distA (k : ℕ) : ℝ := max (11 - (k : ℝ)) 0

/-- The miles B walks on his `k`-th day: 2, 4, 6, …. -/
noncomputable def distB (k : ℕ) : ℝ := 2 * k

/-- Miles walked `n` days and `h` hours (`0 ≤ h < 24`) after 6 a.m. on the first day, walking
the `k`-th day's distance `d k` at a uniform pace from 6 a.m. to 6 p.m. and resting at night. -/
noncomputable def walked (d : ℕ → ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  ∑ k ∈ range n, d (k + 1) + d (n + 1) * (min h 12 / 12)

/-- A's position, measured from A's starting point. -/
noncomputable def posA (n : ℕ) (h : ℝ) : ℝ := walked distA n h

/-- B's position: he starts 14 miles ahead. -/
noncomputable def posB (n : ℕ) (h : ℝ) : ℝ := 14 + walked distB n h

private lemma sumB (n : ℕ) : ∑ k ∈ range n, distB (k + 1) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; simp [distB]; ring

private lemma distA_nonneg (k : ℕ) : 0 ≤ distA k := le_max_right _ _

private lemma sumA_ten (n : ℕ) : ∑ k ∈ range (n + 10), distA (k + 1) = 55 := by
  induction n with
  | zero => simp [sum_range_succ, distA]; norm_num
  | succ n ih =>
    rw [show n + 1 + 10 = (n + 10) + 1 by ring, sum_range_succ, ih]
    simp [distA]
    have : (11 : ℝ) - (n + 10 + 1 : ℕ) ≤ 0 := by push_cast; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    push_cast at this
    linarith [max_eq_right this]

private lemma sumA_le (n : ℕ) : ∑ k ∈ range n, distA (k + 1) ≤ 55 := by
  rw [← sumA_ten n]
  exact sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun k _ _ => distA_nonneg _)

/-- They are together exactly at 2 days 6 hours (noon of the third day), and from 6 p.m. of the
fourth day (`n = 3`, `h = 12`: the end of the fourth day's walk) to 6 a.m. of the fifth. -/
theorem problem39 (n : ℕ) (h : ℝ) (h0 : 0 ≤ h) (h24 : h < 24) :
    (posA n h = posB n h ↔ (n = 2 ∧ h = 6) ∨ (n = 3 ∧ 12 ≤ h) ∨ (n = 4 ∧ h = 0)) := by
  have hm0 : 0 ≤ min h 12 / 12 := by positivity
  have hm1 : min h 12 / 12 ≤ 1 := by
    rw [div_le_one (by norm_num)]; exact min_le_right _ _
  constructor
  · intro H
    by_cases hn : n ≤ 5
    · rcases le_total h 12 with hh | hh
      · have hmin : min h 12 = h := min_eq_left hh
        interval_cases n <;>
          simp [posA, posB, walked, sum_range_succ, distA, distB, hmin] at H ⊢ <;>
          norm_num at H <;> linarith
      · have hmin : min h 12 = 12 := min_eq_right hh
        interval_cases n <;>
          simp [posA, posB, walked, sum_range_succ, distA, distB, hmin] at H ⊢
        all_goals norm_num at H
        linarith
    · exfalso
      have hn' : 6 ≤ n := by omega
      have hA : posA n h ≤ 55 := by
        have := sumA_le (n + 1)
        rw [sum_range_succ] at this
        unfold posA walked
        nlinarith [distA_nonneg (n + 1)]
      have hB : 56 ≤ posB n h := by
        unfold posB walked
        rw [sumB]
        have : (6 : ℝ) ≤ n := by exact_mod_cast hn'
        have : 0 ≤ distB (n + 1) := by unfold distB; positivity
        nlinarith
      linarith [h24]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, hh⟩ | ⟨rfl, rfl⟩)
    · simp [posA, posB, walked, sum_range_succ, distA, distB]; norm_num
    · simp [posA, posB, walked, sum_range_succ, distA, distB, min_eq_right hh]; norm_num
    · simp [posA, posB, walked, sum_range_succ, distA, distB]; norm_num

/-- Where they are together: 23 miles and 34 miles from A's start. -/
theorem problem39_where :
    posA 2 6 = 23 ∧ (∀ h : ℝ, 12 ≤ h → posA 3 h = 34) ∧ posA 4 0 = 34 := by
  refine ⟨?_, fun h hh => ?_, ?_⟩
  · simp [posA, walked, sum_range_succ, distA]; norm_num
  · simp [posA, walked, sum_range_succ, distA, min_eq_right hh]; norm_num
  · simp [posA, walked, sum_range_succ, distA]; norm_num

end PillowProblems.P39
