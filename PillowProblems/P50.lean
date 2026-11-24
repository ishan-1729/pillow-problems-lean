import PillowProblems.Basic

/-!
# Problem 50 (Algebra: Chances)

**Question.**

> There are 2 bags, \(H\) and \(K\), each containing 2 counters: and it is known that each counter is either black or white. A white counter is added to bag \(H\), the bag is shaken up, and one counter transferred (without looking at it) to bag \(K\), where the process is repeated, a counter being transferred to bag \(H\). What is now the chance of drawing a white counter from bag \(H\)?

**Answer.**

> Seventeen-twentysevenths.

*(Carroll's solution: Chapter III, problem 50; text in `data/problems.json`.)*

**Lean reading.** The whole experiment is one finite space of equally likely cases `Outcome`:
the colours of the two counters originally in `H` and of the two in `K` (`true` = white), the
counter drawn from `H` (one of its 3 after the white one is added), the counter drawn from `K`
(one of its 3 after the transfer), and the counter finally drawn from `H` (one of its 3 after the
return transfer). "Each counter is either black or white", with nothing else known, is read as
Carroll reads it: each counter is independently white or black with chance `1/2`, so that
`H` holds 2 W, 1 W 1 B, 2 B with chances `1/4, 1/2, 1/4`; "shaken up" means each counter in a bag
is equally likely to be drawn. The contents after each transfer are computed from the outcome
(`hAfterAdd`, `kAfterTransfer`, `hFinal`), and the theorem says the chance that the final draw
from `H` is white is `17/27`. No hypotheses are needed.

**Status.** proved
-/

namespace PillowProblems.P50

/-- A colour: `true` is white, `false` is black. -/
abbrev Colour := Bool

/-- One run of the experiment: the original colours of the two counters in `H` and of the two in
`K`, then which of the 3 counters is drawn from `H`, which of the 3 counters is then drawn from
`K`, and which of the 3 counters is finally drawn from `H`. All cases are equally likely. -/
abbrev Outcome := (Colour × Colour) × (Colour × Colour) × Fin 3 × Fin 3 × Fin 3

/-- Bag `H` after the white counter is added: its two original counters and a white one. -/
def hAfterAdd (ω : Outcome) : Fin 3 → Colour := ![ω.1.1, ω.1.2, true]

/-- The counter transferred from `H` to `K`. -/
def firstTransfer (ω : Outcome) : Colour := hAfterAdd ω ω.2.2.1

/-- Bag `K` after receiving the transferred counter. -/
def kAfterTransfer (ω : Outcome) : Fin 3 → Colour := ![ω.2.1.1, ω.2.1.2, firstTransfer ω]

/-- The counter transferred back from `K` to `H`. -/
def secondTransfer (ω : Outcome) : Colour := kAfterTransfer ω ω.2.2.2.1

/-- Bag `H` at the end: the two counters left in it after the first transfer, and the counter
transferred back from `K`. -/
def hFinal (ω : Outcome) : Fin 3 → Colour :=
  ![hAfterAdd ω (ω.2.2.1.succAbove 0), hAfterAdd ω (ω.2.2.1.succAbove 1), secondTransfer ω]

/-- The event that the counter finally drawn from `H` is white. -/
def finalWhite (ω : Outcome) : Prop := hFinal ω ω.2.2.2.2 = true

instance : DecidablePred finalWhite := fun ω => by unfold finalWhite; infer_instance

/-- Carroll's first step: the counter transferred from `H` to `K` is white with chance `2/3`. -/
theorem firstTransfer_white : uniformChance (fun ω => firstTransfer ω = true) = 2 / 3 := by
  rw [uniformChance_eq]
  have h : (Finset.univ.filter (fun ω => firstTransfer ω = true)).card = 288 := by decide +kernel
  rw [h]
  simp
  norm_num

/-- Carroll's second step: the counter transferred back from `K` to `H` is white with chance
`5/9`. -/
theorem secondTransfer_white : uniformChance (fun ω => secondTransfer ω = true) = 5 / 9 := by
  rw [uniformChance_eq]
  have h : (Finset.univ.filter (fun ω => secondTransfer ω = true)).card = 240 := by decide +kernel
  rw [h]
  simp
  norm_num

/-- Carroll's answer: the chance of drawing a white counter from `H` is `17/27`. -/
theorem problem50 : uniformChance finalWhite = 17 / 27 := by
  rw [uniformChance_eq]
  have h : (Finset.univ.filter finalWhite).card = 272 := by decide +kernel
  rw [h]
  simp
  norm_num

end PillowProblems.P50
