import PillowProblems.Basic

/-!
# Problem 65 (Trigonometry: Plane)

**Question.** *(dated 5/89)*

> How many shapes are there for Triangles which have all their angles aliquot parts of 360°?

*(Carroll's solution: Chapter III, problem 65; text in `data/problems.json`.)*

**Lean reading.** A triangle's shape (its similarity class) is fixed by its three angles, and
every triple of positive angles with sum `180°` is the set of angles of some triangle, so a shape is
an unordered triple of angles; we represent it by its angles `(a, b, c)` in degrees listed in
non-increasing order (`0 < c ≤ b ≤ a`, `a + b + c = 180`). Following Carroll's solution, "an
aliquot part of `360°`" means `360°/n` for a positive integer `n` (so `51 3/7° = 360°/7` counts;
the angle need not be a whole number of degrees). `aliquotShapes` is the set of all such triples;
`problem65` shows it is exactly Carroll's list of ten triples, so there are `10` shapes. (Carroll's
solution text has a misprint in case (2), writing `1/2, 1/5, 1/20` for `1/4, 1/5, 1/20`; his final
list is correct.)

**Status.** proved
-/

namespace PillowProblems.P65

/-- An angle of `a` degrees is an aliquot part of `360°`. -/
def IsAliquotPart (a : ℝ) : Prop := ∃ n : ℕ, 0 < n ∧ a = 360 / n

/-- Shapes of triangles all of whose angles are aliquot parts of `360°`, each shape represented
by its angles `(a, b, c)` in degrees, listed in non-increasing order. -/
def aliquotShapes : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < p.2.2 ∧ p.2.2 ≤ p.2.1 ∧ p.2.1 ≤ p.1 ∧ p.1 + p.2.1 + p.2.2 = 180 ∧
    IsAliquotPart p.1 ∧ IsAliquotPart p.2.1 ∧ IsAliquotPart p.2.2}

private lemma nat_solutions {x y z : ℕ} (hx : 0 < x) (hxy : x ≤ y) (hyz : y ≤ z)
    (h : 2 * (y * z + x * z + x * y) = x * y * z) :
    (x, y, z) = (3, 7, 42) ∨ (x, y, z) = (3, 8, 24) ∨ (x, y, z) = (3, 9, 18) ∨
    (x, y, z) = (3, 10, 15) ∨ (x, y, z) = (3, 12, 12) ∨ (x, y, z) = (4, 5, 20) ∨
    (x, y, z) = (4, 6, 12) ∨ (x, y, z) = (4, 8, 8) ∨ (x, y, z) = (5, 5, 10) ∨
    (x, y, z) = (6, 6, 6) := by
  have hy : 0 < y := by omega
  have hz : 0 < z := by omega
  have hx6 : x ≤ 6 := by
    by_contra hc
    rw [not_le] at hc
    have h1 : x * y * z ≥ 7 * (y * z) := by
      have := Nat.mul_le_mul_right (y * z) hc
      nlinarith
    nlinarith [Nat.mul_le_mul hxy hyz, Nat.mul_le_mul hxy (le_refl z), Nat.mul_le_mul (le_refl x) hyz]
  simp only [Prod.mk.injEq]
  interval_cases x
  · nlinarith
  · nlinarith
  · have : y ≤ 12 := by nlinarith
    interval_cases y <;> simp <;> omega
  · have : y ≤ 8 := by nlinarith
    interval_cases y <;> simp <;> omega
  · have : y ≤ 6 := by nlinarith
    interval_cases y <;> simp <;> omega
  · obtain rfl : y = 6 := by nlinarith
    simp only [true_and]
    omega

theorem problem65 :
    aliquotShapes = {(120, 30, 30), (120, 40, 20), (120, 45, 15), (120, 36, 24),
      (120, 360 / 7, 60 / 7), (90, 45, 45), (90, 60, 30), (90, 72, 18), (72, 72, 36),
      (60, 60, 60)} ∧
    aliquotShapes.ncard = 10 := by
  have hset : aliquotShapes = {(120, 30, 30), (120, 40, 20), (120, 45, 15), (120, 36, 24),
      (120, 360 / 7, 60 / 7), (90, 45, 45), (90, 60, 30), (90, 72, 18), (72, 72, 36),
      (60, 60, 60)} := by
    ext ⟨a, b, c⟩
    simp only [aliquotShapes, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hc, hcb, hba, hsum, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ⟨z, hz, rfl⟩⟩
      have hxr : (0 : ℝ) < x := by exact_mod_cast hx
      have hyr : (0 : ℝ) < y := by exact_mod_cast hy
      have hzr : (0 : ℝ) < z := by exact_mod_cast hz
      have hxy : x ≤ y := by
        have : (x : ℝ) ≤ y := by
          rw [div_le_div_iff₀ hyr hxr] at hba; nlinarith
        exact_mod_cast this
      have hyz : y ≤ z := by
        have : (y : ℝ) ≤ z := by
          rw [div_le_div_iff₀ hzr hyr] at hcb; nlinarith
        exact_mod_cast this
      have heq : 2 * (y * z + x * z + x * y) = x * y * z := by
        have : (2 * (y * z + x * z + x * y) : ℝ) = x * y * z := by
          field_simp at hsum; linarith
        exact_mod_cast this
      rcases nat_solutions hx hxy hyz heq with h | h | h | h | h | h | h | h | h | h <;>
        simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;> norm_num
    · rintro (h | h | h | h | h | h | h | h | h | h) <;> obtain ⟨rfl, rfl, rfl⟩ := h
      · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, ⟨3, by norm_num⟩,
          ⟨12, by norm_num⟩, ⟨12, by norm_num⟩⟩
      · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, ⟨3, by norm_num⟩,
          ⟨9, by norm_num⟩, ⟨18, by norm_num⟩⟩
      · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, ⟨3, by norm_num⟩,
          ⟨8, by norm_num⟩, ⟨24, by norm_num⟩⟩
      · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, ⟨3, by norm_num⟩,
          ⟨10, by norm_num⟩, ⟨15, by norm_num⟩⟩
      · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, ⟨3, by norm_num⟩,
          ⟨7, by norm_num⟩, ⟨42, by norm_num⟩⟩
      · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, ⟨4, by norm_num⟩,
          ⟨8, by norm_num⟩, ⟨8, by norm_num⟩⟩
      · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, ⟨4, by norm_num⟩,
          ⟨6, by norm_num⟩, ⟨12, by norm_num⟩⟩
      · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, ⟨4, by norm_num⟩,
          ⟨5, by norm_num⟩, ⟨20, by norm_num⟩⟩
      · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, ⟨5, by norm_num⟩,
          ⟨5, by norm_num⟩, ⟨10, by norm_num⟩⟩
      · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, ⟨6, by norm_num⟩,
          ⟨6, by norm_num⟩, ⟨6, by norm_num⟩⟩
  refine ⟨hset, ?_⟩
  rw [hset]
  repeat rw [Set.ncard_insert_of_notMem (by norm_num)]
  rw [Set.ncard_singleton]

end PillowProblems.P65
