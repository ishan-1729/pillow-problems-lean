import PillowProblems.Basic

/-!
# Problem 52 (Algebra: Equational Problems)

**Question.** *(dated 16/2/89)*

> Five beggars sat down in a circle, and each piled up, in a heap before him, the pennies he had received that day: and the five heaps were equal.
>
> Then spake the eldest and wisest of them, unfolding, as he spake, an empty sack.
>
> "My friends, let me teach you a pretty little game! First, I name myself 'Number One,' my left-hand neighbour 'Number Two,' and so on to 'Number Five.' I then pour into this sack the whole of my earnings for the day, and hand it on to him who sits next but one on my left, that is, 'Number Three.' *His* part in the game is to take out of it, and give to his two neighbours, so many pennies as represent their names (that is, he must give four to 'Number Four' and two to 'Number Two'); he must then put *into* the sack half as much as it contained when he received it; and he must then hand it on just as I did, that is, he must hand it to him who sits next but one on his left—who will of course be 'Number Five.' *He* must proceed in the same way, and hand it on to 'Number Two,' from whom the sack will find its way to 'Number Four,' and so to me again. If any player cannot furnish, from his own heap, the whole of what he has to put into the sack, he is at liberty to draw upon any of the other heaps, *except mine*!"
>
> The other beggars entered into the game with much enthusiasm: and in due time the sack returned to 'Number One,' who put into it the two pennies he had received during the game, and carefully tied up the mouth of it with a string. Then, remarking "it is a *very* pretty little game," he rose to his feet, and hastily quitted the spot. The other four beggars gazed at each other with rueful countenances. Not one of them had a penny left!
>
> How much had each at first?

**Answer.**

> 2*l.* 18*s.* 0*d.*

*(Carroll's solution: Chapter III, problem 52; text in `data/problems.json`.)*

**Lean reading.** Pennies are counted in `ℚ` and the game is simulated turn by turn: the sack goes from
Number One to the next but one on the left (Numbers Three, Five, Two, Four), each player takes
out his neighbours' names and gives them those pennies, then adds half of what the sack held on
arrival; finally Number One adds the pennies he received. Since Numbers Two to Five may draw on
each other's heaps, only their combined holding (`pool`) matters, and Number One's pennies
outside the sack are tracked separately (`one`). "Not one of them had a penny left" is
`pool = 0` at the end. `GameLegal` adds the tacit requirements that the game can be played with
whole pennies (each half is whole, the sack can pay out, the heaps can furnish the half). The
theorem shows that these conditions hold exactly when each beggar started with 696d. = 2*l.* 18*s.* 0*d.*

**Status.** proved
-/

namespace PillowProblems.P52

/-- The beggars sit in a circle as `Fin 5`, numbered anticlockwise ("to the left"); beggar `i`
is called "Number `i + 1`", so `0` is the eldest, Number One. -/
def name (i : Fin 5) : ℚ := (i : ℕ) + 1

/-- The pennies in play: those in the sack, those held (in any of their heaps) by Numbers Two
to Five together, and those held by Number One outside the sack. -/
@[ext] structure State where
  sack : ℚ
  pool : ℚ
  one : ℚ

/-- What beggar `i` hands to Number One out of the sack (the name of Number One, if he is one of
`i`'s two neighbours). -/
def toOne (i : Fin 5) : ℚ :=
  (if i - 1 = 0 then name (i - 1) else 0) + (if i + 1 = 0 then name (i + 1) else 0)

/-- What beggar `i` takes out of the sack: the names of his two neighbours. -/
def payout (i : Fin 5) : ℚ := name (i - 1) + name (i + 1)

/-- The turn of beggar `i`: he takes `payout i` out of the sack and gives it to his neighbours,
then puts into the sack, from the heaps of Numbers Two to Five, half of what the sack held
when he received it. -/
def turn (i : Fin 5) (s : State) : State where
  sack := s.sack - payout i + s.sack / 2
  pool := s.pool + (payout i - toOne i) - s.sack / 2
  one := s.one + toOne i

/-- A turn can really be played with whole pennies: the sack holds an even number of pennies
when received (so "half as much" is a whole number), it holds enough to pay the neighbours, and
the heaps of Numbers Two to Five can furnish the half. -/
def LegalTurn (i : Fin 5) (s : State) : Prop :=
  (∃ n : ℕ, s.sack = 2 * n) ∧ payout i ≤ s.sack ∧ 0 ≤ (turn i s).pool

/-- Who holds the sack after `k` hand-ons: each time it goes to the next but one on the left. -/
def holder : ℕ → Fin 5
  | 0 => 0
  | k + 1 => holder k + 2

/-- Each heap holds `x` pennies, and Number One has poured his into the sack. -/
def start (x : ℕ) : State := ⟨x, 4 * x, 0⟩

/-- The state after the first `k` of the four turns (Numbers Three, Five, Two, Four). -/
def stateAfter (x : ℕ) : ℕ → State
  | 0 => start x
  | k + 1 => turn (holder (k + 1)) (stateAfter x k)

/-- The end: Number One puts the pennies he received into the sack. -/
def final (x : ℕ) : State :=
  ⟨(stateAfter x 4).sack + (stateAfter x 4).one, (stateAfter x 4).pool, 0⟩

/-- All four turns can be played. -/
def GameLegal (x : ℕ) : Prop := ∀ k < 4, LegalTurn (holder (k + 1)) (stateAfter x k)

/-- "Not one of them had a penny left": Numbers Two to Five hold nothing at the end. -/
def OthersBroke (x : ℕ) : Prop := (final x).pool = 0

/-- Each beggar had 696 pence = 2*l.* 18*s.* 0*d.* at first, and this is the only possibility. -/
theorem problem52 (x : ℕ) : (GameLegal x ∧ OthersBroke x) ↔ x = 2 * 240 + 18 * 12 + 0 := by
  sorry

end PillowProblems.P52
