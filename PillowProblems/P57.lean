import PillowProblems.Basic

/-!
# Problem 57 (Pure Geometry, Plane, Trigonometry: Plane)

**Question.** *(dated 27/1/91)*

> In a given Triangle describe three Squares, whose bases shall lie along the sides of the Triangle, and whose upper edges shall form a Triangle;
>
> (1) geometrically; (2) trigonometrically.

**Answer.**

> (1) *Geometrically.*
>
> If Squares be described externally on the sides of the given Triangle; and if their outer edges be produced to form a new Triangle; and if the sides of the given Triangle be divided similarly to those of the new Triangle: their central portions will be the bases of the required Squares.
>
> (2) *Trigonometrically.*
>
> If \(a\), \(b\), \(c\) be the sides of the given Triangle, and \(m\) its area; and if \(x\), \(y\), \(z\) be the sides of the required Squares: then \[ \frac{a}{x} = \frac{b}{y} = \frac{c}{z} = \frac{a^{2}+b^{2}+c^{2}}{2m} + 1. \]

*(Carroll's solution: Chapter III, problem 57; text in `data/problems.json`.)*

**Lean reading.** A square stands on a side when its base lies along the line of that side and the
square is on the inner side (`SquareOn`; for an obtuse triangle Carroll's bases may run past a
vertex, so lines rather than segments are used); the three squares stand on `BC`, `CA`, `AB`
with upper edges `B'C'`, `C'A'`, `A'B'` (`Squares`), so the upper edges form the triangle
`A'B'C'`. Carroll tacitly assumes, as in his figure, that the squares lie outside the triangle
`A'B'C'` (`Outside`: each upper edge separates the opposite vertex of `A'B'C'` from the side of
`ABC` it stands on). Without this the answer is not unique: `problem57_other` exhibits, in the
triangle with sides `6, 5, 5`, a second figure with overlapping squares and `a/x = 31/12`
instead of `55/12`. Here `a, b, c` are the sides, `m = triArea A B C`, and `x, y, z` the sides
`B'C'`, `C'A'`, `A'B'` of the squares. `problem57_b` proves Carroll's formula (2) for every such
figure, `problem57_exists` that the figure exists in every triangle, and `problem57_a` proves
the construction (1): if `A''B''C''` is the triangle formed by the outer edges of the external
squares, and the sides of `ABC` are divided at the same parameters as the external squares
divide the sides of `A''B''C''`, the central portions are the bases of a figure as in (2).

**Status.** proved (Carroll's reading)
-/

namespace PillowProblems.P57

open scoped EuclideanGeometry RealInnerProductSpace

/-- `PQRS` (vertices in this order) is a square: `PQ`, `PS` are perpendicular sides of equal
length and `R - Q = S - P`. -/
def IsSquare (P Q R S : Plane) : Prop :=
  P ≠ Q ∧ R - Q = S - P ∧ ⟪Q - P, S - P⟫ = 0 ∧ ‖S - P‖ = ‖Q - P‖

/-- A square stands on the side `XY` of the triangle `XYZ`, on the same side of `XY` as `Z`
(i.e. inside the triangle), with upper edge `UV`: its base `PQ` lies along `XY`, and `PQVU` is a
square. -/
def SquareOn (X Y Z U V : Plane) : Prop :=
  ∃ P Q : Plane, P ∈ line[ℝ, X, Y] ∧ Q ∈ line[ℝ, X, Y] ∧ IsSquare P Q V U ∧
    0 < cross X Y U * cross X Y Z

/-- Three squares stand on the sides `BC`, `CA`, `AB` of the triangle `ABC`, inside it, and their
upper edges `B'C'`, `C'A'`, `A'B'` form the triangle `A'B'C'`. -/
def Squares (A B C A' B' C' : Plane) : Prop :=
  SquareOn B C A B' C' ∧ SquareOn C A B C' A' ∧ SquareOn A B C A' B'

/-- Carroll's figure: the squares lie outside the triangle `A'B'C'` formed by their upper edges,
i.e. each upper edge separates the opposite vertex of `A'B'C'` from the side of `ABC` on which
that square stands. -/
def Outside (A B C A' B' C' : Plane) : Prop :=
  cross B' C' A' * cross B' C' B < 0 ∧ cross C' A' B' * cross C' A' C < 0 ∧
    cross A' B' C' * cross A' B' A < 0

private lemma inner2 (P Q : Plane) : ⟪P, Q⟫ = P 0 * Q 0 + P 1 * Q 1 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]; ring

private lemma normsq2 (P : Plane) : ‖P‖ ^ 2 = P 0 ^ 2 + P 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]; simp [Fin.sum_univ_two]

private lemma distsq2 (P Q : Plane) : dist P Q ^ 2 = (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]; simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma ext2 {P Q : Plane} (h0 : P 0 = Q 0) (h1 : P 1 = Q 1) : P = Q := by
  ext i; fin_cases i <;> simp [h0, h1]

private lemma mem_line {B C X : Plane} : X ∈ line[ℝ, B, C] ↔ ∃ t : ℝ, X = B + t • (C - B) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  constructor
  · rintro ⟨t, ht⟩; exact ⟨t, by rw [← ht]; abel⟩
  · rintro ⟨t, ht⟩; exact ⟨t, by rw [ht]; abel⟩

/-- Every point is the barycentre of `A, B, C` with weights the signed areas. -/
private lemma recon (A B C X : Plane) (i : Fin 2) :
    cross A B C * X i = cross B C X * A i + cross C A X * B i + cross A B X * C i := by
  have : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases this with rfl | rfl <;> simp only [cross] <;> ring

private lemma cross_sum (A B C X : Plane) :
    cross B C X + cross C A X + cross A B X = cross A B C := by
  simp only [cross]; ring

/-- A square `PQVU` with base `PQ` along `XY`: `U`, `V` are equally far from `XY`, and the square
of that height (times `XY²`) is `XY² · UV²`. -/
private lemma sq_core {X Y U V P Q : Plane} (hP : P ∈ line[ℝ, X, Y]) (hQ : Q ∈ line[ℝ, X, Y])
    (hsq : IsSquare P Q V U) :
    cross X Y V = cross X Y U ∧ cross X Y U ^ 2 = dist X Y ^ 2 * dist U V ^ 2 ∧
      dist U V = dist P Q := by
  obtain ⟨hPQ, h1, h2, h3⟩ := hsq
  have hUV' : U - V = P - Q := by
    rw [← sub_eq_zero, show U - V - (P - Q) = (U - P) - (V - Q) by abel, h1, sub_self]
  have e3 : dist U V = dist P Q := by rw [dist_eq_norm, dist_eq_norm, hUV']
  obtain ⟨p, rfl⟩ := mem_line.1 hP
  obtain ⟨q, rfl⟩ := mem_line.1 hQ
  have hV : V = U + (q - p) • (Y - X) := by
    rw [show V = (V - (X + q • (Y - X))) + (X + q • (Y - X)) by abel, h1]; module
  have hUV : dist U V = |q - p| * dist X Y := by
    rw [hV, dist_eq_norm, show U - (U + (q - p) • (Y - X)) = (q - p) • (X - Y) by module,
      norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
  have hqp : q - p ≠ 0 := by
    intro h; apply hPQ; rw [show q = p by linarith]
  refine ⟨?_, ?_, e3⟩
  · rw [hV]; simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  · rw [hUV, mul_pow, sq_abs]
    rw [inner2] at h2
    have h3' : ‖U - (X + p • (Y - X))‖ ^ 2 = ‖X + q • (Y - X) - (X + p • (Y - X))‖ ^ 2 := by
      rw [h3]
    rw [normsq2, normsq2] at h3'
    rw [distsq2]
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h2 h3'
    simp only [cross]
    have hperp : (Y 0 - X 0) * (U 0 - (X 0 + p * (Y 0 - X 0))) +
        (Y 1 - X 1) * (U 1 - (X 1 + p * (Y 1 - X 1))) = 0 := by
      have : (q - p) * ((Y 0 - X 0) * (U 0 - (X 0 + p * (Y 0 - X 0))) +
          (Y 1 - X 1) * (U 1 - (X 1 + p * (Y 1 - X 1)))) = 0 := by linear_combination h2
      exact (mul_eq_zero.1 this).resolve_left hqp
    linear_combination ((Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2) * h3' -
      ((Y 0 - X 0) * (U 0 - (X 0 + p * (Y 0 - X 0))) +
        (Y 1 - X 1) * (U 1 - (X 1 + p * (Y 1 - X 1)))) * hperp

/-- What a square on `XY` with upper edge `UV` tells us: `U`, `V` are equally far from `XY`,
at distance equal to the side `UV` of the square, on the side of `Z`. -/
private lemma sq_cross {X Y Z U V : Plane} (h : SquareOn X Y Z U V) :
    cross X Y V = cross X Y U ∧ cross X Y U ^ 2 = dist X Y ^ 2 * dist U V ^ 2 ∧
      0 < cross X Y U * cross X Y Z ∧ 0 < dist U V := by
  obtain ⟨P, Q, hP, hQ, hsq, hs⟩ := h
  obtain ⟨e1, e2, e3⟩ := sq_core hP hQ hsq
  exact ⟨e1, e2, hs, e3 ▸ dist_pos.2 hsq.1⟩

/-- Conversely, such data give a square on `XY`. -/
private lemma squareOn_of {X Y Z U V : Plane} {ρ : ℝ} (hXY : X ≠ Y) (hρ : ρ ≠ 0)
    (hV : V = U + ρ • (Y - X)) (hU : cross X Y U ^ 2 = ρ ^ 2 * (dist X Y ^ 2) ^ 2)
    (hside : 0 < cross X Y U * cross X Y Z) : SquareOn X Y Z U V := by
  have hL : 0 < (Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2 := by
    have := dist_pos.2 hXY; have h := distsq2 X Y; nlinarith
  have hL0 := hL.ne'
  have hU' : cross X Y U ^ 2 = ρ ^ 2 * ((Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2) ^ 2 := by
    rw [hU, distsq2]; ring
  -- the feet of `U`, `V` on `XY`
  have hUP : U - (U - (cross X Y U / ((Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2)) •
      pt (-(Y 1 - X 1)) (Y 0 - X 0)) = (cross X Y U / ((Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2)) •
      pt (-(Y 1 - X 1)) (Y 0 - X 0) := by abel
  have hQP : (V - (cross X Y U / ((Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2)) •
      pt (-(Y 1 - X 1)) (Y 0 - X 0)) - (U - (cross X Y U / ((Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2)) •
      pt (-(Y 1 - X 1)) (Y 0 - X 0)) = ρ • (Y - X) := by rw [hV]; abel
  refine ⟨U - (cross X Y U / ((Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2)) • pt (-(Y 1 - X 1)) (Y 0 - X 0),
    V - (cross X Y U / ((Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2)) • pt (-(Y 1 - X 1)) (Y 0 - X 0),
    ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, hside⟩
  · rw [mem_line]
    refine ⟨((U 0 - X 0) * (Y 0 - X 0) + (U 1 - X 1) * (Y 1 - X 1)) /
      ((Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2), ext2 ?_ ?_⟩ <;>
    · simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero,
        pt_one]
      field_simp
      ring
  · rw [mem_line]
    refine ⟨((U 0 - X 0) * (Y 0 - X 0) + (U 1 - X 1) * (Y 1 - X 1)) /
      ((Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2) + ρ, ext2 ?_ ?_⟩ <;>
    · rw [hV]
      simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero,
        pt_one]
      field_simp
      ring
  · intro h
    have h' := congrArg (fun P => P - (U - (cross X Y U / ((Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2)) •
      pt (-(Y 1 - X 1)) (Y 0 - X 0))) h
    simp only [sub_self] at h'
    rw [hQP] at h'
    rcases smul_eq_zero.1 h'.symm with h1 | h1
    · exact hρ h1
    · exact hXY (sub_eq_zero.1 h1).symm
  · simp only [sub_sub_cancel]
  · rw [hQP, hUP, inner2]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one]
    ring
  · rw [hQP, hUP]
    apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    rw [normsq2, normsq2]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one]
    field_simp
    linear_combination ((Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2) * hU'

/-- If two of the heights agree as the squares say, the triangle `A'B'C'` is homothetic to `ABC`:
`B' - C' = ρ (B - C)` with `ρ = (T - κ_a - κ_b - κ_c) / T`. -/
private lemma side_rel (A B C A' B' C' : Plane) (hT : cross A B C ≠ 0)
    (h1 : cross B C C' = cross B C B') (h2 : cross A B B' = cross A B A') :
    B' - C' = ((cross A B C - cross B C B' - cross C A C' - cross A B A') / cross A B C) •
      (B - C) := by
  have sB := cross_sum A B C B'
  have sC := cross_sum A B C C'
  have key : ∀ i, (B' i - C' i) * cross A B C =
      (cross A B C - cross B C B' - cross C A C' - cross A B A') * (B i - C i) := by
    intro i
    have rB := recon A B C B' i
    have rC := recon A B C C' i
    linear_combination rB - rC + (C i - A i) * h1 + (C i - B i) * h2 + B i * sB - C i * sC
  apply ext2 <;>
  · simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hT]
    exact key _

private lemma outside_rel (A B C A' B' C' : Plane) (ρ : ℝ) (h1 : B' - C' = ρ • (B - C))
    (h2 : A' - B' = ρ • (A - B)) :
    cross B' C' A' * cross B' C' B = -(ρ ^ 3) * (cross A B C * cross B C B') := by
  have hC : C' = B' - ρ • (B - C) := by rw [← h1]; abel
  have hA : A' = B' + ρ • (A - B) := by rw [← h2]; abel
  subst hC hA
  simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private lemma ne_of_cross {A B C : Plane} (hT : cross A B C ≠ 0) : A ≠ B ∧ B ≠ C ∧ C ≠ A := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> apply hT <;> simp only [cross] <;> ring

private lemma sign_eq {x y T : ℝ} (h : x ^ 2 = y ^ 2) (hx : 0 < x * T) (hy : 0 < y * T) :
    x = y := by
  have : (x - y) * (x + y) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · nlinarith

private lemma height {κ d ρ T : ℝ} (hT : T ≠ 0) (hρ : 0 < ρ) (hd : 0 < d)
    (hk : κ ^ 2 = d ^ 2 * (ρ * d) ^ 2) (hs : 0 < κ * T) : κ * |T| = ρ * d ^ 2 * T := by
  have hM : |T| ^ 2 = T ^ 2 := sq_abs T
  have hM0 : 0 < |T| := abs_pos.2 hT
  apply sign_eq (T := T)
  · linear_combination |T| ^ 2 * hk + ρ ^ 2 * d ^ 4 * hM
  · have := mul_pos hs hM0; convert this using 1; ring
  · have := mul_pos (mul_pos hρ (pow_pos hd 2)) (mul_self_pos.2 hT); convert this using 1; ring

/-- The heart of part (2): every Carroll configuration is the image of `ABC` under a homothety
of ratio `ρ = |T| / (|T| + a² + b² + c²)`, `|T| = 2m`. -/
private lemma main (A B C A' B' C' : Plane) (hT : cross A B C ≠ 0)
    (hS : Squares A B C A' B' C') (hO : cross B' C' A' * cross B' C' B < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ρ * (|cross A B C| + (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2)) = |cross A B C| ∧
      dist B' C' = ρ * dist B C ∧ dist C' A' = ρ * dist C A ∧ dist A' B' = ρ * dist A B := by
  obtain ⟨sa, sb, sc⟩ := hS
  obtain ⟨a1, a2, a3, -⟩ := sq_cross sa
  obtain ⟨b1, b2, b3, -⟩ := sq_cross sb
  obtain ⟨c1, c2, c3, -⟩ := sq_cross sc
  have eA : cross B C A = cross A B C := by simp only [cross]; ring
  have eB : cross C A B = cross A B C := by simp only [cross]; ring
  rw [eA] at a3; rw [eB] at b3
  have r1 := side_rel A B C A' B' C' hT a1 c1
  have r2 := side_rel B C A B' C' A' (by rw [eA]; exact hT) b1 a1
  have r3 := side_rel C A B C' A' B' (by rw [eB]; exact hT) c1 b1
  rw [eA] at r2; rw [eB] at r3
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = (cross A B C - cross B C B' - cross C A C' - cross A B A') /
      cross A B C := ⟨_, rfl⟩
  rw [← hρdef] at r1
  have e2 : (cross A B C - cross C A C' - cross A B A' - cross B C B') / cross A B C = ρ := by
    rw [hρdef]; ring
  have e3 : (cross A B C - cross A B A' - cross B C B' - cross C A C') / cross A B C = ρ := by
    rw [hρdef]; ring
  rw [e2] at r2; rw [e3] at r3
  have o := outside_rel A B C A' B' C' ρ r1 r3
  rw [o] at hO
  have hk : 0 < cross A B C * cross B C B' := by rw [mul_comm]; exact a3
  have h3 : 0 < ρ ^ 3 := by
    have : 0 < ρ ^ 3 * (cross A B C * cross B C B') := by linarith
    exact (pos_iff_pos_of_mul_pos this).2 hk
  have hρ : 0 < ρ := by
    rcases lt_or_ge 0 ρ with h | h
    · exact h
    · exfalso
      have : ρ ^ 3 ≤ 0 := by have := sq_nonneg ρ; nlinarith
      linarith
  have dist_of : ∀ P Q R S : Plane, P - Q = ρ • (R - S) → dist P Q = ρ * dist R S := by
    intro P Q R S h
    rw [dist_eq_norm, h, norm_smul, Real.norm_eq_abs, abs_of_pos hρ, ← dist_eq_norm]
  have dx := dist_of _ _ _ _ r1
  have dy := dist_of _ _ _ _ r2
  have dz := dist_of _ _ _ _ r3
  refine ⟨ρ, hρ, ?_, dx, dy, dz⟩
  -- the heights in terms of `ρ`
  obtain ⟨hAB, hBC, hCA⟩ := ne_of_cross hT
  rw [dx] at a2; rw [dy] at b2; rw [dz] at c2
  have ha := height hT hρ (dist_pos.2 hBC) a2 a3
  have hb := height hT hρ (dist_pos.2 hCA) b2 b3
  have hc := height hT hρ (dist_pos.2 hAB) c2 c3
  have hR : ρ * cross A B C = cross A B C - cross B C B' - cross C A C' - cross A B A' := by
    rw [hρdef, div_mul_cancel₀ _ hT]
  have : (ρ * (|cross A B C| + (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2)) - |cross A B C|) *
      cross A B C = 0 := by
    linear_combination |cross A B C| * hR - ha - hb - hc
  linarith [(mul_eq_zero.1 this).resolve_right hT]

/-- **Problem 57 (2)**: in every such figure (Carroll's: squares outside the triangle formed by
their upper edges), `a/x = b/y = c/z = (a² + b² + c²)/(2m) + 1`. -/
theorem problem57_b (A B C A' B' C' : Plane) (hT : cross A B C ≠ 0)
    (hS : Squares A B C A' B' C') (hO : Outside A B C A' B' C') :
    dist B C / dist B' C' =
        (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) / (2 * triArea A B C) + 1 ∧
      dist C A / dist C' A' =
        (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) / (2 * triArea A B C) + 1 ∧
      dist A B / dist A' B' =
        (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) / (2 * triArea A B C) + 1 := by
  obtain ⟨ρ, hρ, hk, dx, dy, dz⟩ := main A B C A' B' C' hT hS hO.1
  obtain ⟨hAB, hBC, hCA⟩ := ne_of_cross hT
  have h2m : 2 * triArea A B C = |cross A B C| := by unfold triArea; ring
  have hM0 : 0 < |cross A B C| := abs_pos.2 hT
  rw [h2m, dx, dy, dz]
  have r : ∀ d : ℝ, 0 < d → d / (ρ * d) =
      (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) / |cross A B C| + 1 := by
    intro d hd
    have hρ0 : ρ ≠ 0 := hρ.ne'
    rw [show d / (ρ * d) = 1 / ρ by field_simp]
    field_simp
    linarith [hk]
  exact ⟨r _ (dist_pos.2 hBC), r _ (dist_pos.2 hCA), r _ (dist_pos.2 hAB)⟩

/-- Carroll's figure, explicitly: the image of `ABC` under the homothety of ratio
`ρ = |T| / (|T| + a² + b² + c²)` about the symmedian point. -/
private lemma fig (A B C : Plane) (hT : cross A B C ≠ 0) (M S ρ : ℝ) (hM : M = |cross A B C|)
    (hS : S = dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) (hρ : ρ = M / (M + S)) (B' : Plane)
    (hB' : B' = B + (ρ / M) • (dist B C ^ 2 • (A - B) + dist A B ^ 2 • (C - B))) :
    Squares A B C (B' + ρ • (A - B)) B' (B' + ρ • (C - B)) ∧
      Outside A B C (B' + ρ • (A - B)) B' (B' + ρ • (C - B)) := by
  obtain ⟨hAB, hBC, hCA⟩ := ne_of_cross hT
  have eA : cross B C A = cross A B C := by simp only [cross]; ring
  have eB : cross C A B = cross A B C := by simp only [cross]; ring
  have hM0 : 0 < M := hM ▸ abs_pos.2 hT
  have hM2 : M ^ 2 = cross A B C ^ 2 := by rw [hM, sq_abs]
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hMS : M + S ≠ 0 := (by linarith : 0 < M + S).ne'
  have hMne' : M ≠ 0 := hM0.ne'
  have hρ0 : 0 < ρ := by rw [hρ]; exact div_pos hM0 (by linarith)
  have hρ1 : 1 - ρ = ρ / M * S := by rw [hρ]; field_simp; ring
  obtain ⟨C', hC'⟩ : ∃ C' : Plane, C' = B' + ρ • (C - B) := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ A' : Plane, A' = B' + ρ • (A - B) := ⟨_, rfl⟩
  have kB : cross B C B' = ρ / M * dist B C ^ 2 * cross A B C := by
    rw [hB']; simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have kA : cross A B A' = ρ / M * dist A B ^ 2 * cross A B C := by
    rw [hA', hB']; simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have kC : cross C A C' = ρ / M * dist C A ^ 2 * cross A B C := by
    rw [hC', hB']; simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) * hρ1 +
      (ρ / M * ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1))) * hS
  have hsq : ∀ d : ℝ, (ρ / M * d ^ 2 * cross A B C) ^ 2 = ρ ^ 2 * (d ^ 2) ^ 2 := by
    intro d
    rw [show (ρ / M * d ^ 2 * cross A B C) ^ 2 = ρ ^ 2 * (d ^ 2) ^ 2 * (cross A B C ^ 2 / M ^ 2)
      by ring, ← hM2, div_self (pow_ne_zero 2 hM0.ne'), mul_one]
  have hpos : ∀ d : ℝ, 0 < d → 0 < ρ / M * d ^ 2 * cross A B C * cross A B C := by
    intro d hd
    have := mul_pos (mul_pos (div_pos hρ0 hM0) (pow_pos hd 2)) (mul_self_pos.2 hT)
    convert this using 1; ring
  have r1 : B' - C' = ρ • (B - C) := by rw [hC']; module
  have r2 : C' - A' = ρ • (C - A) := by rw [hC', hA']; module
  have r3 : A' - B' = ρ • (A - B) := by rw [hA']; module
  rw [← hC', ← hA']
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact squareOn_of hBC hρ0.ne' hC' (by rw [kB, hsq])
      (by rw [kB, eA]; exact hpos _ (dist_pos.2 hBC))
  · exact squareOn_of hCA hρ0.ne' (by rw [hA', hC']; module) (by rw [kC, hsq])
      (by rw [kC, eB]; exact hpos _ (dist_pos.2 hCA))
  · exact squareOn_of hAB hρ0.ne' (by rw [hA']; module) (by rw [kA, hsq])
      (by rw [kA]; exact hpos _ (dist_pos.2 hAB))
  · rw [outside_rel A B C A' B' C' ρ r1 r3, kB]
    have := mul_pos (pow_pos hρ0 3) (hpos _ (dist_pos.2 hBC))
    nlinarith
  · rw [outside_rel B C A B' C' A' ρ r2 r1, kC, eA]
    have := mul_pos (pow_pos hρ0 3) (hpos _ (dist_pos.2 hCA))
    nlinarith
  · rw [outside_rel C A B C' A' B' ρ r3 r2, kA, eB]
    have := mul_pos (pow_pos hρ0 3) (hpos _ (dist_pos.2 hAB))
    nlinarith

/-- **Problem 57**: Carroll's figure exists in every triangle (so the description of part (2)
is not vacuous). -/
theorem problem57_exists (A B C : Plane) (hT : cross A B C ≠ 0) :
    ∃ A' B' C' : Plane, Squares A B C A' B' C' ∧ Outside A B C A' B' C' := by
  exact ⟨_, _, _, fig A B C hT _ _ _ rfl rfl rfl _ rfl⟩

/-! ### Part (1): the geometric construction -/

/-- Two points with the same signed distances from two non-parallel lines coincide. -/
private lemma uniq {X Y Z P Q : Plane} (h : cross X Y Z ≠ 0) (h1 : cross X Y P = cross X Y Q)
    (h2 : cross Y Z P = cross Y Z Q) : P = Q := by
  have k0 : (P 0 - Q 0) * cross X Y Z = 0 := by
    simp only [cross] at h1 h2 ⊢
    linear_combination (Z 0 - Y 0) * h1 - (Y 0 - X 0) * h2
  have k1 : (P 1 - Q 1) * cross X Y Z = 0 := by
    simp only [cross] at h1 h2 ⊢
    linear_combination (Z 1 - Y 1) * h1 - (Y 1 - X 1) * h2
  apply ext2
  · linarith [(mul_eq_zero.1 k0).resolve_right h]
  · linarith [(mul_eq_zero.1 k1).resolve_right h]

/-- Points of a line parallel to `XY` are equally far from `XY`. -/
private lemma on_par {X Y U V W : Plane} (hV : V = U + (Y - X)) (hW : W ∈ line[ℝ, U, V]) :
    cross X Y W = cross X Y U := by
  obtain ⟨t, rfl⟩ := mem_line.1 hW
  rw [hV]; simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- A square `XYVU` erected on `XY`, on the side away from the point with `cross X Y · = T`:
its outer edge is `UV = XY` translated, at distance `XY` beyond the line. -/
private lemma ext_sq {X Y U V : Plane} {T : ℝ} (hsq : IsSquare X Y V U)
    (hs : cross X Y U * T < 0) (hT : T ≠ 0) :
    V = U + (Y - X) ∧ cross X Y U * |T| = -(dist X Y ^ 2) * T := by
  have hX : X ∈ line[ℝ, X, Y] := mem_line.2 ⟨0, by simp⟩
  have hY : Y ∈ line[ℝ, X, Y] := mem_line.2 ⟨1, by simp⟩
  obtain ⟨-, e2, e3⟩ := sq_core hX hY hsq
  rw [e3] at e2
  have hd : 0 < dist X Y := dist_pos.2 hsq.1
  refine ⟨by rw [show V = (V - Y) + Y by abel, hsq.2.1]; abel, ?_⟩
  apply sign_eq (T := -T)
  · linear_combination |T| ^ 2 * e2 + dist X Y ^ 4 * sq_abs T
  · have := mul_pos (neg_pos.2 hs) (abs_pos.2 hT); convert this using 1; ring
  · have := mul_pos (pow_pos hd 2) (mul_self_pos.2 hT); convert this using 1; ring

/-- A homothety of positive ratio maps squares to squares. -/
private lemma sq_map {W X Y Z : Plane} (hsq : IsSquare W X Y Z) {ρ : ℝ} (hρ : 0 < ρ)
    (O B₀ : Plane) :
    IsSquare (O + ρ • (W - B₀)) (O + ρ • (X - B₀)) (O + ρ • (Y - B₀)) (O + ρ • (Z - B₀)) := by
  obtain ⟨h0, h1, h2, h3⟩ := hsq
  have d : ∀ P Q : Plane, (O + ρ • (P - B₀)) - (O + ρ • (Q - B₀)) = ρ • (P - Q) := by
    intros; module
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; apply h0
    have := d X W; rw [h, sub_self] at this
    rcases smul_eq_zero.1 this.symm with h' | h'
    · exact absurd h' hρ.ne'
    · exact (sub_eq_zero.1 h').symm
  · rw [d, d, h1]
  · rw [d, d, real_inner_smul_left, real_inner_smul_right, h2]; simp
  · rw [d, d, norm_smul, norm_smul, h3]

/-- The square `WXYZ` read from `Z` backwards. -/
private lemma sq_rev {W X Y Z : Plane} (hsq : IsSquare W X Y Z) : IsSquare Z Y X W := by
  obtain ⟨h0, h1, h2, h3⟩ := hsq
  have e : Y - Z = X - W := by
    rw [← sub_eq_zero, show Y - Z - (X - W) = (Y - X) - (Z - W) by abel, h1, sub_self]
  have e' : W - Z = -(Z - W) := by abel
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; apply h0; rw [h, sub_self] at e; exact (sub_eq_zero.1 e.symm).symm
  · rw [← neg_sub Y X, h1, neg_sub]
  · rw [e, e', inner_neg_right, h2, neg_zero]
  · rw [e, e', norm_neg, h3]

/-- **Problem 57 (1)**, geometrically. Squares `B C Ca Ba`, `C A Ab Cb`, `A B Bc Ac` are described
externally on the sides; their outer edges, produced, form the triangle `A''B''C''`; the sides
of `A''B''C''` are divided by the squares at the parameters `r, r'` (on `B''C''`), `s, s'` (on
`C''A''`), `t, t'` (on `A''B''`). Dividing the sides of `ABC` similarly, the central portions are
the bases of the required squares: there is a figure of three squares on these bases whose
upper edges form a triangle `A'B'C'`, as in part (2). -/
theorem problem57_a (A B C Ba Ca Cb Ab Ac Bc A'' B'' C'' : Plane) (hT : cross A B C ≠ 0)
    (hBC : IsSquare B C Ca Ba) (hBC' : cross B C Ba * cross B C A < 0)
    (hCA : IsSquare C A Ab Cb) (hCA' : cross C A Cb * cross C A B < 0)
    (hAB : IsSquare A B Bc Ac) (hAB' : cross A B Ac * cross A B C < 0)
    (hA'' : A'' ∈ line[ℝ, Cb, Ab] ∧ A'' ∈ line[ℝ, Ac, Bc])
    (hB'' : B'' ∈ line[ℝ, Ac, Bc] ∧ B'' ∈ line[ℝ, Ba, Ca])
    (hC'' : C'' ∈ line[ℝ, Ba, Ca] ∧ C'' ∈ line[ℝ, Cb, Ab])
    (r r' s s' t t' : ℝ)
    (hBa : Ba = B'' + r • (C'' - B'')) (hCa : Ca = B'' + r' • (C'' - B''))
    (hCb : Cb = C'' + s • (A'' - C'')) (hAb : Ab = C'' + s' • (A'' - C''))
    (hAc : Ac = A'' + t • (B'' - A'')) (hBc : Bc = A'' + t' • (B'' - A'')) :
    ∃ A' B' C' : Plane,
      IsSquare (B + r • (C - B)) (B + r' • (C - B)) C' B' ∧
      IsSquare (C + s • (A - C)) (C + s' • (A - C)) A' C' ∧
      IsSquare (A + t • (B - A)) (A + t' • (B - A)) B' A' ∧
      Squares A B C A' B' C' ∧ Outside A B C A' B' C' := by
  have eA : cross B C A = cross A B C := by simp only [cross]; ring
  have eB : cross C A B = cross A B C := by simp only [cross]; ring
  obtain ⟨M, hM⟩ : ∃ M, M = |cross A B C| := ⟨_, rfl⟩
  have hM0 : 0 < M := hM ▸ abs_pos.2 hT
  have hMne : M ≠ 0 := hM0.ne'
  obtain ⟨S, hS⟩ : ∃ S, S = dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2 := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hMS : M + S ≠ 0 := (by linarith : 0 < M + S).ne'
  have hMne' : M ≠ 0 := hM0.ne'
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = M / (M + S) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; exact div_pos hM0 (by linarith)
  have hρ1 : 1 - ρ = ρ / M * S := by rw [hρ]; field_simp; ring
  obtain ⟨B', hB'⟩ : ∃ B' : Plane,
      B' = B + (ρ / M) • (dist B C ^ 2 • (A - B) + dist A B ^ 2 • (C - B)) := ⟨_, rfl⟩
  obtain ⟨hfS, hfO⟩ := fig A B C hT M S ρ hM hS hρ B' hB'
  -- the external squares
  rw [eA] at hBC'; rw [eB] at hCA'
  obtain ⟨vBC, kBa⟩ := ext_sq hBC hBC' hT
  obtain ⟨vCA, kCb⟩ := ext_sq hCA hCA' hT
  obtain ⟨vAB, kAc⟩ := ext_sq hAB hAB' hT
  rw [← hM] at kBa kCb kAc
  have hT' : cross B C A ≠ 0 := by rw [eA]; exact hT
  have hT'' : cross C A B ≠ 0 := by rw [eB]; exact hT
  -- the vertices of the new triangle
  have eB'' : B'' = B - (1 / M) • (dist B C ^ 2 • (A - B) + dist A B ^ 2 • (C - B)) := by
    apply uniq hT
    · rw [on_par vAB hB''.1]
      apply mul_right_cancel₀ hM0.ne'
      rw [kAc]
      simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp; ring
    · rw [on_par vBC hB''.2]
      apply mul_right_cancel₀ hM0.ne'
      rw [kBa]
      simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp; ring
  have eC'' : C'' = C - (1 / M) • (dist B C ^ 2 • (A - C) + dist C A ^ 2 • (B - C)) := by
    apply uniq hT'
    · rw [on_par vBC hC''.1]
      apply mul_right_cancel₀ hM0.ne'
      rw [kBa]
      simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp; ring
    · rw [on_par vCA hC''.2]
      apply mul_right_cancel₀ hM0.ne'
      rw [kCb]
      simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp; ring
  have eA'' : A'' = A - (1 / M) • (dist C A ^ 2 • (B - A) + dist A B ^ 2 • (C - A)) := by
    apply uniq hT''
    · rw [on_par vCA hA''.1]
      apply mul_right_cancel₀ hM0.ne'
      rw [kCb]
      simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp; ring
    · rw [on_par vAB hA''.2]
      apply mul_right_cancel₀ hM0.ne'
      rw [kAc]
      simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp; ring
  -- the homothety `X ↦ B' + ρ (X - B)` maps `A''B''C''` onto `ABC`
  have e1 : (1 - ρ) • (C - B) = (ρ / M * S) • (C - B) := by rw [hρ1]
  have e2 : S • (C - B) = (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) • (C - B) := by rw [hS]
  have e1' : (1 - ρ) • (A - B) = (ρ / M * S) • (A - B) := by rw [hρ1]
  have e2' : S • (A - B) = (dist B C ^ 2 + dist C A ^ 2 + dist A B ^ 2) • (A - B) := by rw [hS]
  have hhB : B' + ρ • (B'' - B) = B := by rw [eB'', hB']; module
  have hhC : B' + ρ • (C'' - B) = C := by
    rw [eC'', hB']; linear_combination (norm := module) -e1 - (ρ / M) • e2
  have hhA : B' + ρ • (A'' - B) = A := by
    rw [eA'', hB']; linear_combination (norm := module) -e1' - (ρ / M) • e2'
  have pBa : B' + ρ • (Ba - B) = B + r • (C - B) := by
    rw [hBa]; linear_combination (norm := module) (1 - r) • hhB + r • hhC
  have pCa : B' + ρ • (Ca - B) = B + r' • (C - B) := by
    rw [hCa]; linear_combination (norm := module) (1 - r') • hhB + r' • hhC
  have pCb : B' + ρ • (Cb - B) = C + s • (A - C) := by
    rw [hCb]; linear_combination (norm := module) (1 - s) • hhC + s • hhA
  have pAb : B' + ρ • (Ab - B) = C + s' • (A - C) := by
    rw [hAb]; linear_combination (norm := module) (1 - s') • hhC + s' • hhA
  have pAc : B' + ρ • (Ac - B) = A + t • (B - A) := by
    rw [hAc]; linear_combination (norm := module) (1 - t) • hhA + t • hhB
  have pBc : B' + ρ • (Bc - B) = A + t' • (B - A) := by
    rw [hBc]; linear_combination (norm := module) (1 - t') • hhA + t' • hhB
  have pB : B' + ρ • (B - B) = B' := by simp
  refine ⟨B' + ρ • (A - B), B', B' + ρ • (C - B), ?_, ?_, ?_, hfS, hfO⟩
  · have := sq_rev (sq_map hBC hρ0 B' B)
    rwa [pBa, pCa, pB] at this
  · have := sq_rev (sq_map hCA hρ0 B' B)
    rwa [pCb, pAb] at this
  · have := sq_rev (sq_map hAB hρ0 B' B)
    rwa [pAc, pBc, pB] at this

/-- The hypotheses of part (1) are satisfiable: the triangle `A = (3,4)`, `B = (0,0)`,
`C = (6,0)` with its external squares and the new triangle `A'' = (3, 37/3)`,
`B'' = (-43/4, -6)`, `C'' = (67/4, -6)`. -/
theorem problem57_a_nonvacuous : ∃ A B C Ba Ca Cb Ab Ac Bc A'' B'' C'' : Plane,
    ∃ r r' s s' t t' : ℝ,
    cross A B C ≠ 0 ∧
    IsSquare B C Ca Ba ∧ cross B C Ba * cross B C A < 0 ∧
    IsSquare C A Ab Cb ∧ cross C A Cb * cross C A B < 0 ∧
    IsSquare A B Bc Ac ∧ cross A B Ac * cross A B C < 0 ∧
    (A'' ∈ line[ℝ, Cb, Ab] ∧ A'' ∈ line[ℝ, Ac, Bc]) ∧
    (B'' ∈ line[ℝ, Ac, Bc] ∧ B'' ∈ line[ℝ, Ba, Ca]) ∧
    (C'' ∈ line[ℝ, Ba, Ca] ∧ C'' ∈ line[ℝ, Cb, Ab]) ∧
    Ba = B'' + r • (C'' - B'') ∧ Ca = B'' + r' • (C'' - B'') ∧
    Cb = C'' + s • (A'' - C'') ∧ Ab = C'' + s' • (A'' - C'') ∧
    Ac = A'' + t • (B'' - A'') ∧ Bc = A'' + t' • (B'' - A'') := by
  have sq : ∀ P Q R S : Plane, P ≠ Q → R - Q = S - P → ⟪Q - P, S - P⟫ = 0 →
      ‖S - P‖ ^ 2 = ‖Q - P‖ ^ 2 → IsSquare P Q R S := fun P Q R S h1 h2 h3 h4 =>
    ⟨h1, h2, h3, (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h4⟩
  have ne : ∀ x y x' y' : ℝ, x ≠ x' → pt x y ≠ pt x' y' := by
    intro x y x' y' h e; exact h (by simpa using congrArg (· 0) e)
  refine ⟨pt 3 4, pt 0 0, pt 6 0, pt 0 (-6), pt 6 (-6), pt 10 3, pt 7 7, pt (-1) 7, pt (-4) 3,
    pt 3 (37 / 3), pt (-43 / 4) (-6), pt (67 / 4) (-6), 43 / 110, 67 / 110, 27 / 55, 39 / 55,
    16 / 55, 28 / 55, ?_, sq _ _ _ _ (ne _ _ _ _ (by norm_num)) ?_ ?_ ?_, ?_,
    sq _ _ _ _ (ne _ _ _ _ (by norm_num)) ?_ ?_ ?_, ?_,
    sq _ _ _ _ (ne _ _ _ _ (by norm_num)) ?_ ?_ ?_, ?_,
    ⟨mem_line.2 ⟨7 / 3, ?_⟩, mem_line.2 ⟨-4 / 3, ?_⟩⟩,
    ⟨mem_line.2 ⟨13 / 4, ?_⟩, mem_line.2 ⟨-43 / 24, ?_⟩⟩,
    ⟨mem_line.2 ⟨67 / 24, ?_⟩, mem_line.2 ⟨-9 / 4, ?_⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (norm_num [cross, pt]; done)
    | (apply ext2 <;> norm_num [pt])
    | (rw [inner2]; norm_num [pt])
    | (rw [normsq2, normsq2]; norm_num [pt])

private lemma dist_of_sq {P Q : Plane} {d : ℝ} (hd : 0 ≤ d) (h : dist P Q ^ 2 = d ^ 2) :
    dist P Q = d :=
  (pow_left_inj₀ dist_nonneg hd two_ne_zero).1 h

/-- Without Carroll's tacit condition `Outside` the answer is not unique: in the triangle
`A = (3,4)`, `B = (0,0)`, `C = (6,0)` (sides `6, 5, 5`, area `12`) there is a second figure,
with the squares overlapping and `a/x = 31/12`, whereas `(a²+b²+c²)/(2m) + 1 = 55/12`. -/
theorem problem57_other :
    Squares (pt 3 4) (pt 0 0) (pt 6 0) (pt 3 (24 / 31)) (pt (129 / 31) (72 / 31))
        (pt (57 / 31) (72 / 31)) ∧
      dist (pt 0 0) (pt 6 0) / dist (pt (129 / 31) (72 / 31)) (pt (57 / 31) (72 / 31)) = 31 / 12 ∧
      (dist (pt 0 0) (pt 6 0) ^ 2 + dist (pt 6 0) (pt 3 4) ^ 2 + dist (pt 3 4) (pt 0 0) ^ 2) /
        (2 * triArea (pt 3 4) (pt 0 0) (pt 6 0)) + 1 = 55 / 12 := by
  have ne : ∀ x y x' y' : ℝ, x ≠ x' → pt x y ≠ pt x' y' := by
    intro x y x' y' h e; exact h (by simpa using congrArg (· 0) e)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · refine squareOn_of (ρ := -12 / 31) (ne _ _ _ _ (by norm_num)) (by norm_num) ?_ ?_ ?_
    · apply ext2 <;> norm_num [pt]
    · rw [distsq2]; norm_num [cross, pt]
    · norm_num [cross, pt]
  · refine squareOn_of (ρ := -12 / 31) (ne _ _ _ _ (by norm_num)) (by norm_num) ?_ ?_ ?_
    · apply ext2 <;> norm_num [pt]
    · rw [distsq2]; norm_num [cross, pt]
    · norm_num [cross, pt]
  · refine squareOn_of (ρ := -12 / 31) (ne _ _ _ _ (by norm_num)) (by norm_num) ?_ ?_ ?_
    · apply ext2 <;> norm_num [pt]
    · rw [distsq2]; norm_num [cross, pt]
    · norm_num [cross, pt]
  · rw [dist_of_sq (d := 6) (by norm_num) (by rw [distsq2]; norm_num [pt]),
      dist_of_sq (d := 72 / 31) (by norm_num) (by rw [distsq2]; norm_num [pt])]
    norm_num
  · rw [distsq2, distsq2, distsq2]
    norm_num [triArea, cross, pt]

end PillowProblems.P57
