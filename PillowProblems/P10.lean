import PillowProblems.Basic

/-!
# Problem 10 (Algebra: Chances)

**Question.** *(dated 8/90)*

> A triangular billiard-table has 3 pockets, one in each corner, one of which will hold only one ball, while each of the others will hold two. There are 3 balls on the table, each containing a single coin. The table is tilted up, so that the balls run into one corner, it is not known which. The 'expectation', as to the contents of the pocket, is \(\dfrac{2}{6}\). What are the coins?

**Answer.**

> Either 2 florins and a sixpence; or else a half-crown and 2 shillings.

*(Carroll's solution: Chapter III, problem 10; text in `data/problems.json`.)*

**Lean reading.** The balls are numbered `0, 1, 2` and ball `i` holds the coin `coins i`. The
corners are numbered so that corner `0` has the pocket holding one ball and corners `1, 2` have the
pockets holding two. "It is not known which" corner is read as each corner having chance `1/3`.
Carroll tacitly assumes that the pocket is filled to capacity and that every set of balls of that
size is equally likely to be the one in it; so the elementary cases `(corner, set of balls in the
pocket)` carry the weights `pocketWeight`. The 'expectation' is the weighted mean of the value of
the pocket's contents, in pence; `2/6` (two shillings and sixpence) is `30` pence, and
`problem10_expectation` derives Carroll's intermediate result that the expectation is `5/9` of the
total, so the coins must total `54d`. The question does not say which coins are allowed; we take
the British coins current in 1890 (the problem's date), from the farthing to the sovereign (Maundy
money and the gold £2 and £5 pieces left out; the latter exceed `54d` anyway). Carroll's answer is
incomplete: the double florin (4s., struck 1887–1890 and still current in 1895) gives a third
solution, a double florin and two threepenny pieces (`48d + 3d + 3d = 54d`), which his "Either …
or else …" omits. So `problem10` states the corrected full answer (exactly three solutions), and
`problem10_carroll` shows that Carroll's two solutions are exactly the solutions once the double
florin is excluded, as his solution tacitly does.

**Status.** proved (corrected)
-/

namespace PillowProblems.P10

/-- The British coins current in 1890 (Maundy money excluded). -/
inductive Coin
  | farthing
  | halfpenny
  | penny
  | threepence
  | sixpence
  | shilling
  | florin
  | halfCrown
  | doubleFlorin
  | crown
  | halfSovereign
  | sovereign
  deriving DecidableEq, Repr

open Coin

instance : Fintype Coin :=
  ⟨{farthing, halfpenny, penny, threepence, sixpence, shilling, florin, halfCrown, doubleFlorin,
    crown, halfSovereign, sovereign}, by intro x; cases x <;> simp⟩

/-- The value of a coin in farthings. -/
def farthings : Coin → ℕ
  | farthing => 1
  | halfpenny => 2
  | penny => 4
  | threepence => 12
  | sixpence => 24
  | shilling => 48
  | florin => 96
  | halfCrown => 120
  | doubleFlorin => 192
  | crown => 240
  | halfSovereign => 480
  | sovereign => 960

/-- The value of a coin in pence. -/
def pence (c : Coin) : ℚ := farthings c / 4

/-- The number of balls the pocket at each corner holds: corner `0` holds one, the others two. -/
def capacity : Fin 3 → ℕ := ![1, 2, 2]

/-- An elementary case: the corner the balls run into, and the set of balls in its pocket. -/
abbrev Outcome := Fin 3 × Finset (Fin 3)

/-- The weight of an elementary case: each corner has chance `1/3`; the pocket is filled to its
capacity, every set of balls of that size being equally likely; other sets have weight `0`. -/
def pocketWeight (ω : Outcome) : ℚ :=
  1 / 3 * (if ω.2.card = capacity ω.1 then
    1 / ((Finset.univ.filter fun T : Finset (Fin 3) => T.card = capacity ω.1).card : ℚ) else 0)

/-- The expectation of `X` when the cases are weighted by `w`. -/
def expectation {Ω : Type*} [Fintype Ω] (w : Ω → ℚ) (X : Ω → ℚ) : ℚ :=
  (∑ ω, w ω * X ω) / ∑ ω, w ω

/-- The 'expectation' as to the contents of the pocket, in pence, when ball `i` holds the coin
`coins i`. -/
def pocketExpectation (coins : Fin 3 → Coin) : ℚ :=
  expectation pocketWeight (fun ω => ∑ i ∈ ω.2, pence (coins i))

private lemma univ_finset : (Finset.univ : Finset (Finset (Fin 3))) =
    {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide

private lemma filter_card (k : Fin 3) :
    (Finset.univ.filter fun T : Finset (Fin 3) => T.card = capacity k).card = 3 := by
  fin_cases k <;> decide

private lemma sum_finset3 {M : Type*} [AddCommMonoid M] (f : Finset (Fin 3) → M) :
    ∑ S, f S = f ∅ + (f {0} + (f {1} + (f {2} + (f {0, 1} + (f {0, 2} + (f {1, 2} +
      f {0, 1, 2})))))) := by
  rw [univ_finset, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]

/-- Carroll's computation: the expectation is `5/9` of the total value of the three coins. -/
theorem problem10_expectation (coins : Fin 3 → Coin) :
    pocketExpectation coins = 5 / 9 * (pence (coins 0) + pence (coins 1) + pence (coins 2)) := by
  simp only [pocketExpectation, expectation, pocketWeight, filter_card]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, sum_finset3]
  simp (config := {decide := true})
  ring

private lemma expectation_eq_30_iff (coins : Fin 3 → Coin) :
    pocketExpectation coins = 30 ↔
      farthings (coins 0) + farthings (coins 1) + farthings (coins 2) = 216 := by
  rw [problem10_expectation]
  simp only [pence]
  constructor
  · intro h
    have h' : ((farthings (coins 0) + farthings (coins 1) + farthings (coins 2) : ℕ) : ℚ) = 216 := by
      push_cast
      linarith
    exact_mod_cast h'
  · intro h
    have h' : ((farthings (coins 0) + farthings (coins 1) + farthings (coins 2) : ℕ) : ℚ) = 216 := by
      exact_mod_cast h
    push_cast at h'
    linarith

private lemma sum216_iff : ∀ a b d : Coin,
    farthings a + farthings b + farthings d = 216 ↔
      (({a, b, d} : Multiset Coin) = {florin, florin, sixpence} ∨
        ({a, b, d} : Multiset Coin) = {halfCrown, shilling, shilling} ∨
        ({a, b, d} : Multiset Coin) = {doubleFlorin, threepence, threepence}) := by
  decide

/-- **Problem 10**, Carroll's answer (coinage without the double florin). If no coin is a double
florin, the expectation as to the contents of the pocket is `2/6` (30 pence) exactly when the coins
are 2 florins and a sixpence, or a half-crown and 2 shillings. -/
theorem problem10_carroll (coins : Fin 3 → Coin) (h : ∀ i, coins i ≠ doubleFlorin) :
    pocketExpectation coins = 30 ↔
      (({coins 0, coins 1, coins 2} : Multiset Coin) = {florin, florin, sixpence} ∨
        ({coins 0, coins 1, coins 2} : Multiset Coin) = {halfCrown, shilling, shilling}) := by
  rw [expectation_eq_30_iff, sum216_iff]
  have h3 : ({coins 0, coins 1, coins 2} : Multiset Coin) ≠
      {doubleFlorin, threepence, threepence} := by
    intro hm
    have hmem : doubleFlorin ∈ ({coins 0, coins 1, coins 2} : Multiset Coin) := by
      rw [hm]; simp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
    rcases hmem with h0 | h0 | h0
    · exact h 0 h0.symm
    · exact h 1 h0.symm
    · exact h 2 h0.symm
  tauto

/-- **Problem 10** (corrected). With the British coinage of 1890 the expectation as to the contents
of the pocket is `2/6` (30 pence) exactly when the coins are 2 florins and a sixpence, a half-crown
and 2 shillings, or (the solution Carroll misses) a double florin and 2 threepenny pieces. -/
theorem problem10 (coins : Fin 3 → Coin) :
    pocketExpectation coins = 30 ↔
      (({coins 0, coins 1, coins 2} : Multiset Coin) = {florin, florin, sixpence} ∨
        ({coins 0, coins 1, coins 2} : Multiset Coin) = {halfCrown, shilling, shilling} ∨
        ({coins 0, coins 1, coins 2} : Multiset Coin) = {doubleFlorin, threepence, threepence}) := by
  rw [expectation_eq_30_iff, sum216_iff]

/-- Both of Carroll's solutions, and the double-florin one he misses, do give expectation `2/6`;
Carroll's solutions satisfy the hypothesis of `problem10_carroll`. -/
example : pocketExpectation ![florin, florin, sixpence] = 30 ∧
    pocketExpectation ![halfCrown, shilling, shilling] = 30 ∧
    pocketExpectation ![doubleFlorin, threepence, threepence] = 30 ∧
    (∀ i, (![florin, florin, sixpence] : Fin 3 → Coin) i ≠ doubleFlorin) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [problem10_expectation]; norm_num [pence, farthings]
  · rw [problem10_expectation]; norm_num [pence, farthings]
  · rw [problem10_expectation]; norm_num [pence, farthings]
  · decide

end PillowProblems.P10
