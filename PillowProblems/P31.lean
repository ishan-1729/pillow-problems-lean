import PillowProblems.Basic

/-!
# Problem 31 (Arithmetic)

**Question.** *(dated 14/3/89)*

> On July 1, at 8 a.m. by my watch, it was 8*h.* 4*m.* by my clock. I took the watch to Greenwich, and, when it said 'noon', the true time was 12*h.* 5*m.* That evening, when the watch said '6*h.*', the clock said '5*h.* 59*m.*'
>
> On July 30, at 9 a.m. by my watch, it was 8*h.* 57*m.* by my clock. At Greenwich, when the watch said '12*h.* 10*m.*', the true time was 12*h.* 5*m.* That evening, when the watch said '7*h.*' the clock said '6*h.* 58*m.*'
>
> My watch is only wound up for each journey, and goes uniformly during any one day: the clock is always going, and goes uniformly.
>
> How am I to know when it is *true* noon on July 31?

**Answer.**

> When the clock says '12*h.* 2*m.* \(29 \tfrac{277}{288} sec.\)'

*(Carroll's solution: Chapter III, problem 31; text in `data/problems.json`.)*

**Lean reading.** True time `t` is measured in minutes after midnight beginning
July 1 (`dayStart d` is midnight beginning July `d`); readings `h h. m m.` are taken on the
24-hour reckoning (`hm h m`), so 'that evening … 6 h.' is `hm 18 0`. "Goes uniformly" is read as
"the reading is an affine function of true time" (`Uniform`). The clock, always going, is one
affine function `clock` whose reading on July `d` is `clock t - dayStart d`; this assumes,
tacitly as Carroll does, that the clock is only minutes wrong, so each reading belongs to the day
on which it is taken. The watch, rewound for each journey, is a separate affine function
`watch₁`, `watch₃₀` on each of the two days; the instants `s₁ … s₄` of the four watch/clock
comparisons are unknown. The theorem derives (with no extra hypotheses) that the clock says
Carroll's `12 h. 2 m. 29 277/288 sec.` at true noon on July 31 and at no other instant, which is
how one "knows" true noon; `problem31_nonvacuous` shows the data are consistent.

**Status.** proved
-/

namespace PillowProblems.P31

/-- The time of day `h` hours `m` minutes, in minutes after midnight (24-hour reckoning). -/
def hm (h m : ℝ) : ℝ := 60 * h + m

/-- The instant of midnight beginning July `d`, in minutes of true time after midnight
beginning July 1. -/
def dayStart (d : ℕ) : ℝ := 1440 * ((d : ℝ) - 1)

/-- A timepiece *goes uniformly*: its reading is an affine function of true time. -/
def Uniform (f : ℝ → ℝ) : Prop := ∃ a b : ℝ, ∀ t, f t = a + b * t

/-- True noon on July 31 is the one instant at which the clock says
`12 h. 2 m. 29 277/288 sec.` -/
theorem problem31 (clock watch₁ watch₃₀ : ℝ → ℝ)
    (hc : Uniform clock) (hw₁ : Uniform watch₁) (hw₃₀ : Uniform watch₃₀)
    (s₁ s₂ s₃ s₄ : ℝ)
    -- July 1
    (h₁ : watch₁ s₁ = hm 8 0) (h₁' : clock s₁ = dayStart 1 + hm 8 4)
    (h₂ : watch₁ (dayStart 1 + hm 12 5) = hm 12 0)
    (h₃ : watch₁ s₂ = hm 18 0) (h₃' : clock s₂ = dayStart 1 + hm 17 59)
    -- July 30
    (h₄ : watch₃₀ s₃ = hm 9 0) (h₄' : clock s₃ = dayStart 30 + hm 8 57)
    (h₅ : watch₃₀ (dayStart 30 + hm 12 5) = hm 12 10)
    (h₆ : watch₃₀ s₄ = hm 19 0) (h₆' : clock s₄ = dayStart 30 + hm 18 58) :
    ∀ t, clock t = dayStart 31 + hm 12 2 + (29 + 277 / 288) / 60 ↔
      t = dayStart 31 + hm 12 0 := by
  obtain ⟨a, b, hc⟩ := hc
  obtain ⟨p, q, hw₁⟩ := hw₁
  obtain ⟨P, Q, hw₃₀⟩ := hw₃₀
  simp only [hc, hw₁, hw₃₀, hm, dayStart] at *
  norm_num at *
  -- July 1: at true `12 h. 5 m.` the clock said `12 h. 2 m.`
  have X₁ : a + b * 725 = 722 := by
    linear_combination h₁' + (1 / 600) * ((-b * (725 - s₁)) * (h₃ - h₁)
      + (b * (s₂ - s₁)) * (h₂ - h₁) + 240 * (h₃' - h₁'))
  -- July 30: at true `12 h. 5 m.` the clock said `12 h. 7 m. 19 sec.`
  have X₂ : a + b * 42485 = 41760 + 537 + 114190 / 600 := by
    linear_combination h₄' + (1 / 600) * ((-b * (42485 - s₃)) * (h₆ - h₄)
      + (b * (s₄ - s₃)) * (h₅ - h₄) + 190 * (h₆' - h₄'))
  have hb : b = 1 + 11 / 86400 := by linarith
  intro t
  subst hb
  constructor
  · intro h; linarith
  · intro h; subst h; linarith

/-- The data are consistent: a uniform clock and two uniform watches realising all of them. -/
theorem problem31_nonvacuous :
    ∃ (clock watch₁ watch₃₀ : ℝ → ℝ) (s₁ s₂ s₃ s₄ : ℝ),
      Uniform clock ∧ Uniform watch₁ ∧ Uniform watch₃₀ ∧
      watch₁ s₁ = hm 8 0 ∧ clock s₁ = dayStart 1 + hm 8 4 ∧
      watch₁ (dayStart 1 + hm 12 5) = hm 12 0 ∧
      watch₁ s₂ = hm 18 0 ∧ clock s₂ = dayStart 1 + hm 17 59 ∧
      watch₃₀ s₃ = hm 9 0 ∧ clock s₃ = dayStart 30 + hm 8 57 ∧
      watch₃₀ (dayStart 30 + hm 12 5) = hm 12 10 ∧
      watch₃₀ s₄ = hm 19 0 ∧ clock s₄ = dayStart 30 + hm 18 58 := by
  refine ⟨fun t => 722 + 86411 / 86400 * (t - 725),
    fun t => 720 + 600 * 86411 / (595 * 86400) * (t - 725),
    fun t => 730 + 600 * 86411 / (601 * 86400) * (t - 42485),
    725 - 240 / (600 * 86411 / (595 * 86400)), 725 + 360 / (600 * 86411 / (595 * 86400)),
    42485 - 190 / (600 * 86411 / (601 * 86400)), 42485 + 410 / (600 * 86411 / (601 * 86400)),
    ⟨722 - 86411 / 86400 * 725, 86411 / 86400, fun t => by ring⟩,
    ⟨720 - 600 * 86411 / (595 * 86400) * 725, 600 * 86411 / (595 * 86400), fun t => by ring⟩,
    ⟨730 - 600 * 86411 / (601 * 86400) * 42485, 600 * 86411 / (601 * 86400), fun t => by ring⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [hm, dayStart]

end PillowProblems.P31
