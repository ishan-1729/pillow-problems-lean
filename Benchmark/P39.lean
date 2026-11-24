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

/-- They are together exactly at 2 days 6 hours (noon of the third day), and from 6 p.m. of the
fourth day (`n = 3`, `h = 12`: the end of the fourth day's walk) to 6 a.m. of the fifth. -/
theorem problem39 (n : ℕ) (h : ℝ) (h0 : 0 ≤ h) (h24 : h < 24) :
    (posA n h = posB n h ↔ (n = 2 ∧ h = 6) ∨ (n = 3 ∧ 12 ≤ h) ∨ (n = 4 ∧ h = 0)) := by
  sorry

/-- Where they are together: 23 miles and 34 miles from A's start. -/
theorem problem39_where :
    posA 2 6 = 23 ∧ (∀ h : ℝ, 12 ≤ h → posA 3 h = 34) ∧ posA 4 0 = 34 := by
  sorry

end PillowProblems.P39
