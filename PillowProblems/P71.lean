import PillowProblems.Basic

/-!
# Problem 71 (Pure Geometry, Plane)

**Question.** *(dated 14/12/74)*

> In a given Triangle place a Hexagon having its opposite sides equal and parallel, and three of them lying along the sides of the Triangle, and such that its diagonals intersect in a given Point.

*(Carroll's solution: Chapter III, problem 71; text in `data/problems.json`.)*

**Lean reading.** The hexagon is `V 0, …, V 5` (`Placed`): its alternate sides `V 0 V 1`, `V 2 V 3`,
`V 4 V 5` lie along the sides `BC`, `CA`, `AB` (every hexagon with alternate sides on the three
sides can be labelled so). "Opposite sides equal and parallel" is read as for a convex hexagon,
where opposite sides are traversed in opposite directions: `V 1 - V 0 = V 3 - V 4` and its two
analogues. Its diagonals are the three main diagonals `V 0 V 3`, `V 1 V 4`, `V 2 V 5`, and they
must pass through `P`. A genuine hexagon has six distinct vertices (`Function.Injective V`);
this excludes Carroll's limiting cases (`P` on `FE`: a parallelogram; `P` at `D`: the line `BC`),
and it is needed, since in a degenerate "hexagon" such as `B, B, A, A, A, B` every point of `AB`
lies on all three diagonals. `problem71` proves that the hexagon can be placed iff `P` lies
strictly inside the triangle `DEF` of the midpoints of the sides, which is Carroll's
solubility condition; the existence half is his construction (written in barycentric
coordinates).

**Status.** proved
-/

namespace PillowProblems.P71

open scoped EuclideanGeometry

/-- `P` lies strictly inside the triangle `XYZ`. -/
def InTriangle (X Y Z P : Plane) : Prop :=
  ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 1 ∧ P = a • X + b • Y + c • Z

/-- The hexagon `V 0, V 1, …, V 5` is placed in the triangle `ABC` as Carroll requires:
its opposite sides are equal and parallel, its alternate sides `V 0 V 1`, `V 2 V 3`, `V 4 V 5`
lie along the sides `BC`, `CA`, `AB`, and its three diagonals `V 0 V 3`, `V 1 V 4`, `V 2 V 5`
pass through `P`. -/
def Placed (A B C P : Plane) (V : Fin 6 → Plane) : Prop :=
  (V 1 - V 0 = V 3 - V 4 ∧ V 2 - V 1 = V 4 - V 5 ∧ V 3 - V 2 = V 5 - V 0) ∧
  (V 0 ∈ segment ℝ B C ∧ V 1 ∈ segment ℝ B C) ∧
  (V 2 ∈ segment ℝ C A ∧ V 3 ∈ segment ℝ C A) ∧
  (V 4 ∈ segment ℝ A B ∧ V 5 ∈ segment ℝ A B) ∧
  (P ∈ segment ℝ (V 0) (V 3) ∧ P ∈ segment ℝ (V 1) (V 4) ∧ P ∈ segment ℝ (V 2) (V 5))

/-- The point with (unnormalised) barycentric coordinates `x, y, z` w.r.t. `A, B, C`. -/
private def bc (A B C : Plane) (x y z : ℝ) : Plane := x • A + y • B + z • C

private lemma indep {A B C : Plane} (hT : cross A B C ≠ 0) {x y : ℝ}
    (h : x • (B - A) + y • (C - A) = 0) : x = 0 ∧ y = 0 := by
  have h0 := congrArg (· 0) h
  have h1 := congrArg (· 1) h
  simp at h0 h1
  unfold cross at hT
  constructor
  · have : x * ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) = 0 := by
      linear_combination (C 1 - A 1) * h0 - (C 0 - A 0) * h1
    exact (mul_eq_zero.1 this).resolve_right hT
  · have : y * ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) = 0 := by
      linear_combination (B 0 - A 0) * h1 - (B 1 - A 1) * h0
    exact (mul_eq_zero.1 this).resolve_right hT

/-- Barycentric coordinates are unique. -/
private lemma bc_inj {A B C : Plane} (hT : cross A B C ≠ 0) {x y z x' y' z' : ℝ}
    (hs : x + y + z = x' + y' + z') (h : bc A B C x y z = bc A B C x' y' z') :
    x = x' ∧ y = y' ∧ z = z' := by
  unfold bc at h
  obtain ⟨h1, h2⟩ := indep hT (x := y - y') (y := z - z') (by
    have hA : (x - x') • A = (y' - y + (z' - z)) • A := by rw [show x - x' = y' - y + (z' - z) by linarith]
    linear_combination (norm := module) h - hA)
  refine ⟨by linarith, by linarith, by linarith⟩

private lemma seg {X Y Q : Plane} (h : Q ∈ segment ℝ X Y) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ Q = a • X + b • Y := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h; exact ⟨a, b, ha, hb, hab, rfl⟩

theorem problem71 (A B C P : Plane) (hT : cross A B C ≠ 0) :
    (∃ V : Fin 6 → Plane, Function.Injective V ∧ Placed A B C P V) ↔
      InTriangle (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B) P := by
  constructor
  · rintro ⟨V, hinj, ⟨e1, e2, e3⟩, ⟨s0, s1⟩, ⟨s2, s3⟩, ⟨s4, s5⟩, d03, d14, -⟩
    obtain ⟨a0, b0, ha0, hb0, h0, hV0⟩ := seg s0
    obtain ⟨a1, b1, ha1, hb1, h1, hV1⟩ := seg s1
    obtain ⟨a2, b2, ha2, hb2, h2, hV2⟩ := seg s2
    obtain ⟨a3, b3, ha3, hb3, h3, hV3⟩ := seg s3
    obtain ⟨a4, b4, ha4, hb4, h4, hV4⟩ := seg s4
    obtain ⟨a5, b5, ha5, hb5, h5, hV5⟩ := seg s5
    obtain ⟨c0, d0, hc0, hd0, hcd0, hP0⟩ := seg d03
    obtain ⟨c1, d1, hc1, hd1, hcd1, hP1⟩ := seg d14
    rw [hV0, hV1, hV3, hV4] at e1
    rw [hV1, hV2, hV4, hV5] at e2
    rw [hV0, hV2, hV3, hV5] at e3
    rw [hV0, hV3] at hP0
    rw [hV1, hV4] at hP1
    obtain ⟨f1, f2, f3⟩ := bc_inj hT (x := a4) (y := a1 + b4) (z := b1) (x' := b3) (y' := a0)
      (z' := a3 + b0) (by linarith) (by unfold bc; linear_combination (norm := module) e1)
    obtain ⟨g1, g2, g3⟩ := bc_inj hT (x := b2 + a5) (y := b5) (z := a2) (x' := a4)
      (y' := b4 + a1) (z' := b1) (by linarith)
      (by unfold bc; linear_combination (norm := module) e2)
    obtain ⟨q1, q2, q3⟩ := bc_inj hT (x := d0 * b3) (y := c0 * a0) (z := c0 * b0 + d0 * a3)
      (x' := d1 * a4) (y' := c1 * a1 + d1 * b4) (z' := c1 * b1)
      (by linear_combination c0 * h0 + d0 * h3 + hcd0 - c1 * h1 - d1 * h4 - hcd1)
      (by unfold bc; linear_combination (norm := module) hP1 - hP0)
    -- consequences of the hexagon being genuine (its six vertices distinct)
    have ne : ∀ i j : Fin 6, V i = V j → i ≠ j → False := fun i j h hij => hij (hinj h)
    have n01 : a0 ≠ a1 := by
      intro h; apply ne 0 1 _ (by decide)
      rw [hV0, hV1, h, show b0 = b1 by linarith]
    have nα : b3 ≠ 0 := by
      intro h
      apply ne 0 4 _ (by decide)
      rw [hV0, hV4, show a0 = 1 by linarith, show b0 = 0 by linarith, show a4 = 0 by linarith,
        show b4 = 1 by linarith]; simp
    have lA : b3 ≠ 1 := by
      intro h
      apply ne 3 4 _ (by decide)
      rw [hV3, hV4, show a3 = 0 by linarith, h, show a4 = 1 by linarith,
        show b4 = 0 by linarith]; simp
    have lB : a0 ≠ 1 := by
      intro h
      apply ne 0 5 _ (by decide)
      rw [hV0, hV5, h, show b0 = 0 by linarith, show a5 = 0 by linarith,
        show b5 = 1 by linarith]; simp
    have lC : b1 ≠ 1 := by
      intro h
      apply ne 1 2 _ (by decide)
      rw [hV1, hV2, h, show a1 = 0 by linarith, show a2 = 1 by linarith,
        show b2 = 0 by linarith]; simp
    -- the diagonals bisect each other, so `P` is their common midpoint
    have hd : d0 = d1 := by
      have : (d0 - d1) * b3 = 0 := by linear_combination q1 + d1 * f1
      linarith [(mul_eq_zero.1 this).resolve_right nα]
    have hc : c0 = 1 / 2 ∧ d0 = 1 / 2 := by
      have : (c0 - d0) * (a0 - a1) = 0 := by
        rw [← hd, show c1 = c0 by linarith, show b4 = a0 - a1 by linarith] at q2
        linear_combination q2
      have := (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 n01)
      constructor <;> linarith
    obtain ⟨rfl, rfl⟩ := hc
    have hsum : b3 + a0 + b1 = 2 := by linarith
    have hA : (b3 + a0 + b1) • A = (2 : ℝ) • A := by rw [hsum]
    have hB : (b3 + a0 + b1) • B = (2 : ℝ) • B := by rw [hsum]
    have hC0 : (a0 + b0) • C = (1 : ℝ) • C := by rw [h0]
    have hC3 : (a3 + b3) • C = (1 : ℝ) • C := by rw [h3]
    refine ⟨1 - b3, 1 - a0, 1 - b1, ?_, ?_, ?_, by linarith, ?_⟩
    · have := lt_of_le_of_ne (by linarith : b3 ≤ 1) lA; linarith
    · have := lt_of_le_of_ne (by linarith : a0 ≤ 1) lB; linarith
    · have := lt_of_le_of_ne (by linarith : b1 ≤ 1) lC; linarith
    · simp only [midpoint_eq_smul_add, invOf_eq_inv]
      linear_combination (norm := module) hP0 + (1 / 2 : ℝ) • hA + (1 / 2 : ℝ) • hB +
        (1 / 2 : ℝ) • hC0 + (1 / 2 : ℝ) • hC3
  · rintro ⟨l, m, n, hl, hm, hn, hs, hP⟩
    obtain rfl : n = 1 - l - m := by linarith
    refine ⟨![bc A B C 0 (1 - m) m, bc A B C 0 (1 - l - m) (l + m), bc A B C (1 - l - m) 0 (l + m),
      bc A B C (1 - l) 0 l, bc A B C (1 - l) l 0, bc A B C m (1 - m) 0], ?_, ?_⟩
    · intro i j h
      fin_cases i <;> fin_cases j <;>
        first
        | rfl
        | (exfalso; obtain ⟨h1, h2, h3⟩ := bc_inj hT (by ring) h; linarith)
    · simp only [Placed, Fin.isValue, Matrix.cons_val, bc]
      simp only [midpoint_eq_smul_add, invOf_eq_inv] at hP
      refine ⟨⟨by module, by module, by module⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · exact ⟨1 - m, m, by linarith, by linarith, by ring, by module⟩
      · exact ⟨1 - l - m, l + m, by linarith, by linarith, by ring, by module⟩
      · exact ⟨l + m, 1 - l - m, by linarith, by linarith, by ring, by module⟩
      · exact ⟨l, 1 - l, by linarith, by linarith, by ring, by module⟩
      · exact ⟨1 - l, l, by linarith, by linarith, by ring, by module⟩
      · exact ⟨m, 1 - m, by linarith, by linarith, by ring, by module⟩
      · exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by rw [hP]; module⟩
      · exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by rw [hP]; module⟩
      · exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by rw [hP]; module⟩

end PillowProblems.P71
