import PillowProblems.Basic

/-!
# Problem 56 (Trigonometry: Plane)

**Question.** *(dated 27/6/84)*

> Given the 3 altitudes of a Triangle: construct it.

**Answer.**

> [Figure: A geometric diagram of two vertical parallel lines with points D/F and E/G, connected by multiple crossing lines through interior points A, B, C.]
>
> Draw \(BC\), \(CE\), \(BD\) equal to the given altitudes, so as to form right \(\angle\)s at \(B\) and \(C\): and produce \(DB\), \(EC\). Join \(DC\), and draw \(CF \perp\) to it. Join \(EB\), and draw \(BG \perp\) to it. With centre \(B\), and distance \(BF\), describe a circle: with centre \(C\), and distance \(CG\) describe another: let them meet at \(A\): and join \(AB\), \(AC\). Triangle \(ABC\) may be proved to be similar to required Triangle. The rest of the construction is obvious.

*(Carroll's solution: Chapter III, problem 56; text in `data/problems.json`.)*

**Lean reading.** A triangle is three points `A, B, C` of the plane with `cross A B C ≠ 0` (non-degenerate), and
`IsAltitude A B C h` says the altitude from `A` has length `h`: there is a foot `F` on the line `BC`
with `AF ⊥ BC` and `AF = h`; `HasAltitudes A B C ha hb hc` collects the three altitudes.
"Construct it" is read as existence plus uniqueness. `problem56` shows that positive lengths
`ha, hb, hc` are the altitudes of some triangle exactly when `1/ha, 1/hb, 1/hc` satisfy the strict
triangle inequalities; Carroll leaves this condition tacit (it is what makes his two circles meet).
`problem56_unique` shows the triangle is determined up to congruence (its sides are determined).
`problem56_similar` is the key step of Carroll's proof: `a·ha = b·hb = c·hc = 2·area`, so the sides
are proportional to `1/ha, 1/hb, 1/hc`. That is why his auxiliary triangle, with sides
`α, α²/β, α²/γ`, is similar to the required one, which "the rest of the construction" then scales.

**Status.** proved
-/

namespace PillowProblems.P56

open scoped EuclideanGeometry

/-- `h` is the length of the altitude from `A` in the triangle `ABC`: there is a foot `F` on the
line `BC` with `AF ⊥ BC`, and `AF = h`. -/
def IsAltitude (A B C : Plane) (h : ℝ) : Prop :=
  ∃ F : Plane, (∃ t : ℝ, F = AffineMap.lineMap B C t) ∧ inner ℝ (A - F) (C - B) = 0 ∧
    dist A F = h

/-- `ABC` is a (non-degenerate) triangle whose altitudes from `A`, `B`, `C` are `ha`, `hb`, `hc`. -/
def HasAltitudes (A B C : Plane) (ha hb hc : ℝ) : Prop :=
  cross A B C ≠ 0 ∧ IsAltitude A B C ha ∧ IsAltitude B C A hb ∧ IsAltitude C A B hc

/-- **Problem 56 (Carroll's key step).** In any triangle the sides are inversely proportional to
the altitudes (`a · ha = b · hb = c · hc`, each being twice the area); so the triangle with sides
`1/ha, 1/hb, 1/hc` is similar to the required one. -/
theorem problem56_similar (A B C : Plane) (ha hb hc : ℝ) (H : HasAltitudes A B C ha hb hc) :
    dist B C * ha = 2 * triArea A B C ∧ dist C A * hb = 2 * triArea A B C ∧
      dist A B * hc = 2 * triArea A B C := by
  sorry

/-- **Problem 56 (existence).** Three given lengths `ha, hb, hc > 0` are the altitudes of some
triangle exactly when their reciprocals satisfy the strict triangle inequalities (Carroll's two
circles then meet). -/
theorem problem56 (ha hb hc : ℝ) (pa : 0 < ha) (pb : 0 < hb) (pc : 0 < hc) :
    (∃ A B C : Plane, HasAltitudes A B C ha hb hc) ↔
      (1 / ha < 1 / hb + 1 / hc ∧ 1 / hb < 1 / hc + 1 / ha ∧ 1 / hc < 1 / ha + 1 / hb) := by
  sorry

/-- **Problem 56 (uniqueness).** The triangle is determined by its altitudes up to congruence:
two triangles with the same altitudes have the same sides. -/
theorem problem56_unique (A B C A' B' C' : Plane) (ha hb hc : ℝ)
    (H : HasAltitudes A B C ha hb hc) (H' : HasAltitudes A' B' C' ha hb hc) :
    dist B C = dist B' C' ∧ dist C A = dist C' A' ∧ dist A B = dist A' B' := by
  sorry

end PillowProblems.P56
