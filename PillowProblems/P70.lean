import PillowProblems.Basic

/-!
# Problem 70 (Trigonometry: Solid)

**Question.**

> Let an equilateral and equiangular Tetrahedron be placed with one facet in front: and suppose a series of triangles, equal to that facet, constructed in the Plane containing that facet, and having a base common with it; and that they are all wrapped round the Tetrahedron as far as they will go. Find (1) the locus of their vertices; (2) the situation of the vertex of the one whose left-hand base-angle is 15°; (3) the left-hand base-angle of the one which (wrapped round towards the right) covers portions of all four facets of the Tetrahedron, and whose vertex coincides with *its* vertex; (4) the left-hand base-angle of the one which (similarly treated) occupies all four facets, and then the front and right-hand facet for the second time, and whose vertex coincides with the distal vertex of the base of the Tetrahedron.

**Answer.**

> (1) Down the back-edge; up again; and so on. (2) about \(\cdot 7\) of the way down the back-edge. (3) About \(18 \cdot 65°\). (4) About \(14 \cdot 53°\).

*(Carroll's solution: Chapter III, problem 70; text in `data/problems.json`.)*

**Lean reading.** The tetrahedron is the regular tetrahedron of edge `1` given by `pos`, with
vertices `BL, BR` (left and right ends of the base of the front facet), `Tp` (top) and `Bk` (the
distal vertex of the base); the front facet is `BL BR Tp`, the back edge is `Tp Bk`. In the plane
of the front facet the facet is `(0,0), (1,0), (½, √3/2)`. "Triangles equal to that facet, having a
base common with it" are read as triangles on the base `(0,0)–(1,0)` of equal area, on the same
side as the facet (hypotheses `triArea … = …` and `0 < V 1`); their vertices then lie on the line
`y = √3/2` (`vertex_height`), as Carroll notes. Following Carroll's solution, the strip
`0 ≤ y ≤ √3/2` is cut into unit equilateral triangles; a wrapping (`Wrapping`) records on which
vertex of the tetrahedron each lattice point of the strip lands, subject to: every strip triangle
lies on a facet, and crossing an edge the paper passes on to the *other* facet through that edge
("as far as they will go"); it starts with the facet itself on the front facet (`Starts`). The
upper edge is laid isometrically along the edges joining the images of consecutive lattice points
(`wrapUp`). Every such wrapping is shown to be the same one (and one exists,
`problem70_nonvacuous`), so the theorems quantify over all of them. The "left-hand base-angle" is
the angle at `(0,0)` between the vertex and `(1,0)`. (1) is `problem70_1`: the vertices are
exactly the points of the upper edge `y = √3/2`, and that edge runs down the back edge, up again,
and so on (with `back_edge_descends`: `Tp` is above `Bk`). (2): the vertex is reached after going
down the back edge and up again, then lies exactly `√3 - 1 ≈ ·73` of the way down it, so
Carroll's "about ·7" is right (`problem70_2_nonvacuous` shows such a triangle exists). (3), (4):
"covers portions of" a facet means that the interiors of the triangle and of a strip triangle
lying on that facet meet (`covers`, `coversFacet`). Question (3) is ill-posed: read literally
(vertex on `Tp`, portions of all four facets covered, and "wrapped round towards the right",
modelled as `½ ≤ V 0`, i.e. the triangle does not lean left of the facet), it is satisfied by
every triangle with vertex `(2j + ½, √3/2)`, `j ≥ 1`, and `problem70_3` proves exactly this. Carroll's
solution ("down the back-edge, and up again") takes the *first* of them, the only one whose
covered strip triangles are exactly `0–3` (front, right, base, left). For (4) the text lists the
facets occupied, front, right, base, left, front, right, so the covered strip triangles are read
as exactly `0–5`, with vertex on `Bk` (here "towards the right" follows and needs no
hypothesis). These are proved to be the triangles with vertex `(5/2, √3/2)` and `(7/2, √3/2)`, whose
base-angles are `arctan (√3/5)` and `arctan (√3/7)`, exactly as in Carroll's solution.
**Carroll's numerical answers to (3) and (4) are wrong.**
`arctan (√3/5) ≈ 19·11°`, not `18·65°` (he evaluated `sin = √84/28 ≈ ·327` as `·32` before
interpolating), and `arctan (√3/7) ≈ 13·90°`, not `14·53°` (`sin ≈ ·240` lies about `0·4`, not
half, of the way from `sin 11·54°` to `sin 17·46°`). The theorems prove
`19° < arctan (√3/5) < 19·2°` and `13·8° < arctan (√3/7) < 14°`, which exclude Carroll's values.

**Status.** proved (corrected)
-/

namespace PillowProblems.P70

open EuclideanGeometry Real

/-! ### The tetrahedron -/

/-- The four vertices of the tetrahedron: the left and right ends of the base of the front facet,
its top, and the back ("distal") vertex of the base. -/
inductive Vtx
  | BL | BR | Tp | Bk
  deriving DecidableEq

instance : Fintype Vtx := ⟨{.BL, .BR, .Tp, .Bk}, fun x => by cases x <;> decide⟩

/-- The point `(x, y, z)` of space. -/
noncomputable def sp (x y z : ℝ) : Space := !₂[x, y, z]

/-- The regular tetrahedron of edge `1` standing on the plane `z = 0`, with front facet
`BL BR Tp` facing the viewer (who looks in the `+y` direction, `x` increasing to the right). -/
noncomputable def pos : Vtx → Space
  | .BL => sp 0 0 0
  | .BR => sp 1 0 0
  | .Tp => sp (1 / 2) (√3 / 6) (√6 / 3)
  | .Bk => sp (1 / 2) (√3 / 2) 0

/-- The facets, as sets of vertices. -/
def facetFront : Finset Vtx := {.BL, .BR, .Tp}
/-- The right-hand facet. -/
def facetRight : Finset Vtx := {.BR, .Tp, .Bk}
/-- The base. -/
def facetBase : Finset Vtx := {.BL, .BR, .Bk}
/-- The left-hand facet. -/
def facetLeft : Finset Vtx := {.BL, .Tp, .Bk}

/-! ### The plane of the front facet, and the wrapping -/

/-- The height of the front facet (edge `1`). -/
noncomputable def width : ℝ := √3 / 2

/-- Lattice points of the strip `0 ≤ y ≤ width` cut into unit equilateral triangles: on the
base line, `(m, 0)` … -/
noncomputable def lower (m : ℤ) : Plane := pt m 0

/-- … and on the upper line, `(m + ½, width)`. The front facet is `lower 0, lower 1, upper 0`. -/
noncomputable def upper (m : ℤ) : Plane := pt (m + 1 / 2) width

/-- The `k`-th triangle of the strip: `k = 2m` is the base-down triangle
`lower m, lower (m+1), upper m`, `k = 2m+1` the base-up triangle
`lower (m+1), upper (m+1), upper m`. -/
noncomputable def stripTri (k : ℤ) : Plane × Plane × Plane :=
  if k % 2 = 0 then (lower (k / 2), lower (k / 2 + 1), upper (k / 2))
  else (lower (k / 2 + 1), upper (k / 2 + 1), upper (k / 2))

/-- A wrapping of the strip round the tetrahedron, recorded by the vertex of the tetrahedron on
which each lattice point lands. Each strip triangle lies flat on a facet (its three corners land
on three different vertices), and the paper, crossing an edge of the strip triangulation, passes
on to the *other* facet through that edge (the two corners opposite a common edge land on
different vertices): this is wrapping "as far as it will go". -/
structure Wrapping where
  lo : ℤ → Vtx
  up : ℤ → Vtx
  down_facet : ∀ m, lo m ≠ lo (m + 1) ∧ lo (m + 1) ≠ up m ∧ up m ≠ lo m
  up_facet : ∀ m, lo (m + 1) ≠ up m ∧ up m ≠ up (m + 1) ∧ up (m + 1) ≠ lo (m + 1)
  turn_down_up : ∀ m, lo m ≠ up (m + 1)
  turn_up_down : ∀ m, up m ≠ lo (m + 2)

/-- The wrapping starts with the strip's first triangle on the front facet, base on base. -/
def Wrapping.Starts (c : Wrapping) : Prop := c.lo 0 = .BL ∧ c.lo 1 = .BR ∧ c.up 0 = .Tp

/-- Where the point `(x, width)` of the strip's upper edge lands: the upper edge between
`upper m` and `upper (m+1)` is laid isometrically along the edge joining their images. -/
noncomputable def wrapUp (c : Wrapping) (x : ℝ) : Space :=
  AffineMap.lineMap (pos (c.up ⌊x - 1 / 2⌋)) (pos (c.up (⌊x - 1 / 2⌋ + 1)))
    (Int.fract (x - 1 / 2))

/-- The facet on which the `k`-th strip triangle lies. -/
def facet (c : Wrapping) (k : ℤ) : Finset Vtx :=
  if k % 2 = 0 then {c.lo (k / 2), c.lo (k / 2 + 1), c.up (k / 2)}
  else {c.lo (k / 2 + 1), c.up (k / 2 + 1), c.up (k / 2)}

/-- The open triangle (interior) with corners `P, Q, R`. -/
def openTri (P Q R : Plane) : Set Plane :=
  {p | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 1 ∧ p = a • P + b • Q + c • R}

/-- The triangle on the common base `(0,0)–(1,0)` with vertex `V` covers a portion of the `k`-th
strip triangle (their interiors meet). -/
def covers (V : Plane) (k : ℤ) : Prop :=
  (openTri (pt 0 0) (pt 1 0) V ∩
    openTri (stripTri k).1 (stripTri k).2.1 (stripTri k).2.2).Nonempty

/-- In the wrapping `c`, the triangle on the common base with vertex `V` covers a portion of the
facet `F` of the tetrahedron: it covers a portion of some strip triangle lying on `F`. -/
def coversFacet (c : Wrapping) (V : Plane) (F : Finset Vtx) : Prop :=
  ∃ k, covers V k ∧ facet c k = F

/-! ### The wrapping is forced -/

private def LO (m : ℤ) : Vtx := if Even m then .BL else .BR
private def UP (m : ℤ) : Vtx := if Even m then .Tp else .Bk

private lemma forced (c : Wrapping) (hc : c.Starts) (m : ℤ) :
    c.lo m = LO m ∧ c.up m = UP m ∧ c.lo (m + 1) = LO (m + 1) := by
  obtain ⟨h0, h1, h2⟩ := hc
  have up_step : ∀ m, c.lo m = LO m ∧ c.up m = UP m ∧ c.lo (m + 1) = LO (m + 1) →
      c.lo (m + 1) = LO (m + 1) ∧ c.up (m + 1) = UP (m + 1) ∧
        c.lo (m + 1 + 1) = LO (m + 1 + 1) := by
    rintro m ⟨ha, hb, hd⟩
    have e1 := (c.up_facet m).2.1
    have e2 := (c.up_facet m).2.2
    have e3 := c.turn_down_up m
    have f1 := (c.down_facet (m + 1)).1
    have f2 := (c.down_facet (m + 1)).2.1
    have f3 := c.turn_up_down m
    rw [show m + 2 = m + 1 + 1 by ring] at f3
    rw [ha] at e3; rw [hb] at e1 f3; rw [hd] at e2 f1
    have hU : c.up (m + 1) = UP (m + 1) := by
      by_cases he : Even m <;>
        simp only [LO, UP, he, Int.even_add_one, not_true_eq_false, not_false_eq_true,
          ↓reduceIte] at e1 e2 e3 ⊢ <;>
        generalize c.up (m + 1) = x at e1 e2 e3 ⊢ <;> revert x <;> decide
    rw [hU] at f2
    refine ⟨hd, hU, ?_⟩
    by_cases he : Even m <;>
      simp only [LO, UP, he, Int.even_add_one, not_true_eq_false, not_false_eq_true,
        ↓reduceIte] at f1 f2 f3 ⊢ <;>
      generalize c.lo (m + 1 + 1) = x at f1 f2 f3 ⊢ <;> revert x <;> decide
  have down_step : ∀ m, c.lo (m + 1) = LO (m + 1) ∧ c.up (m + 1) = UP (m + 1) ∧
      c.lo (m + 1 + 1) = LO (m + 1 + 1) →
      c.lo m = LO m ∧ c.up m = UP m ∧ c.lo (m + 1) = LO (m + 1) := by
    rintro m ⟨ha, hb, hd⟩
    have e1 := (c.down_facet m).2.1
    have e2 := (c.up_facet m).2.1
    have e3 := c.turn_up_down m
    have f1 := (c.down_facet m).1
    have f2 := c.turn_down_up m
    have f3 := (c.down_facet m).2.2
    rw [show m + 2 = m + 1 + 1 by ring] at e3
    rw [ha] at e1 f1; rw [hb] at e2 f2; rw [hd] at e3
    have hU : c.up m = UP m := by
      by_cases he : Even m <;>
        simp only [LO, UP, he, Int.even_add_one, not_true_eq_false, not_false_eq_true,
          ↓reduceIte] at e1 e2 e3 ⊢ <;>
        generalize c.up m = x at e1 e2 e3 ⊢ <;> revert x <;> decide
    rw [hU] at f3
    refine ⟨?_, hU, ha⟩
    by_cases he : Even m <;>
      simp only [LO, UP, he, Int.even_add_one, not_true_eq_false, not_false_eq_true,
        ↓reduceIte] at f1 f2 f3 ⊢ <;>
      generalize c.lo m = x at f1 f2 f3 ⊢ <;> revert x <;> decide
  have base : c.lo 0 = LO 0 ∧ c.up 0 = UP 0 ∧ c.lo (0 + 1) = LO (0 + 1) := by
    refine ⟨by simp [LO, h0], by simp [UP, h2], ?_⟩
    rw [zero_add, h1]; simp [LO]
  refine Int.induction_on m base (fun n ih => up_step _ ih) (fun n ih => down_step _ ?_)
  rw [sub_add_cancel]; exact ih

private lemma up_eq (c : Wrapping) (hc : c.Starts) (m : ℤ) :
    c.up m = if Even m then .Tp else .Bk := (forced c hc m).2.1

private lemma lo_eq (c : Wrapping) (hc : c.Starts) (m : ℤ) :
    c.lo m = if Even m then .BL else .BR := (forced c hc m).1

/-- The assumptions on a wrapping are consistent. -/
theorem problem70_nonvacuous : ∃ c : Wrapping, c.Starts := by
  have key : ∀ m : ℤ, (LO m ≠ LO (m + 1) ∧ LO (m + 1) ≠ UP m ∧ UP m ≠ LO m) ∧
      (LO (m + 1) ≠ UP m ∧ UP m ≠ UP (m + 1) ∧ UP (m + 1) ≠ LO (m + 1)) ∧
      LO m ≠ UP (m + 1) ∧ UP m ≠ LO (m + 2) := by
    intro m
    rw [show m + 2 = m + 1 + 1 by ring]
    by_cases he : Even m
    · have h1 : ¬Even (m + 1) := fun h => Int.even_add_one.mp h he
      have h3 : Even (m + 1 + 1) := Int.even_add_one.mpr h1
      simp only [LO, UP, he, h1, h3, ↓reduceIte]; decide
    · have h1 : Even (m + 1) := Int.even_add_one.mpr he
      have h3 : ¬Even (m + 1 + 1) := fun h => Int.even_add_one.mp h h1
      simp only [LO, UP, he, h1, h3, ↓reduceIte]; decide
  exact ⟨⟨LO, UP, fun m => (key m).1, fun m => (key m).2.1, fun m => (key m).2.2.1,
    fun m => (key m).2.2.2⟩, by simp [Wrapping.Starts, LO, UP]⟩

/-! ### Part (1): the locus of the vertices -/

private lemma wrapUp_eq (c : Wrapping) (m : ℤ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    wrapUp c (m + 1 / 2 + t) = AffineMap.lineMap (pos (c.up m)) (pos (c.up (m + 1))) t := by
  have e : (m : ℝ) + 1 / 2 + t - 1 / 2 = m + t := by ring
  rw [wrapUp, e, Int.floor_intCast_add, Int.fract_intCast_add, Int.floor_eq_zero_iff.mpr ⟨ht0, ht1⟩,
    Int.fract_eq_self.mpr ⟨ht0, ht1⟩, add_zero]

/-- The point `(m + ½ + t, width)` of the upper edge of the strip lands on the back edge. -/
private lemma locus (c : Wrapping) (hc : c.Starts) (m : ℤ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    wrapUp c (m + 1 / 2 + t) =
      if Even m then AffineMap.lineMap (pos .Tp) (pos .Bk) t
      else AffineMap.lineMap (pos .Bk) (pos .Tp) t := by
  rw [wrapUp_eq c m ht0 ht1, up_eq c hc, up_eq c hc]
  by_cases he : Even m
  · have h1 : ¬Even (m + 1) := fun h => Int.even_add_one.mp h he
    simp only [he, h1, ↓reduceIte]
  · have h1 : Even (m + 1) := Int.even_add_one.mpr he
    simp only [he, h1, ↓reduceIte]

private lemma sp_two (x y z : ℝ) : sp x y z 2 = z := rfl

/-- The back edge `Tp Bk` does go down: `Tp` is the top of the tetrahedron, `Bk` is on the
ground. -/
theorem back_edge_descends : pos .Bk 2 < pos .Tp 2 := by
  simp only [pos, sp_two]; positivity

private lemma dist_sp (x y z x' y' z' : ℝ) :
    dist (sp x y z) (sp x' y' z') = √((x - x') ^ 2 + (y - y') ^ 2 + (z - z') ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp [sp, Real.dist_eq, sq_abs]

/-- `pos` is a regular tetrahedron of edge `1`. -/
theorem pos_regular (u v : Vtx) (h : u ≠ v) : dist (pos u) (pos v) = 1 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  cases u <;> cases v <;> simp only [ne_eq, not_true_eq_false] at h <;>
    simp only [pos, dist_sp] <;> rw [Real.sqrt_eq_one] <;> ring_nf <;> linarith

/-! ### Angles and areas -/

private lemma angle_eq (V : Plane) :
    ∠ V (pt 0 0) (pt 1 0) = Real.arccos (V 0 / √(V 0 ^ 2 + V 1 ^ 2)) := by
  rw [EuclideanGeometry.angle, InnerProductGeometry.angle]
  have h1 : V -ᵥ pt 0 0 = V := by ext i; fin_cases i <;> simp [pt]
  have h2 : pt 1 0 -ᵥ pt 0 0 = pt 1 0 := by ext i; fin_cases i <;> simp [pt]
  rw [h1, h2]
  congr 1
  simp [EuclideanSpace.norm_eq, PiLp.inner_apply, Fin.sum_univ_two, pt]

private lemma arccos_eq_arctan {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    Real.arccos (x / √(x ^ 2 + y ^ 2)) = arctan (y / x) := by
  rw [Real.arctan_eq_arccos (div_nonneg hy hx.le)]
  congr 1
  rw [div_pow, one_add_div (pow_ne_zero 2 hx.ne'), Real.sqrt_div' _ (sq_nonneg x),
    Real.sqrt_sq hx.le, inv_div]

/-- A triangle of the series: on the base `(0,0)–(1,0)`, on the same side as the facet, and
equal (in area) to the facet. Its vertex is then on the upper edge of the strip. -/
private lemma vertex_height {V : Plane}
    (hA : triArea (pt 0 0) (pt 1 0) V = triArea (pt 0 0) (pt 1 0) (pt (1 / 2) width))
    (hV : 0 < V 1) : V 1 = width := by
  have hw : 0 < width := by unfold width; positivity
  simp only [triArea, cross, pt_zero, pt_one] at hA
  rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at hA
  linarith

/-- **Problem 70 (1).** Before folding, the vertices of the triangles of the series (on the
common base, on the facet's side, equal in area to the facet) are exactly the points of the
upper edge `y = width` of the strip. Wrapped round, the point `(m + ½ + t, width)` of that edge
lands on the back edge `Tp Bk` of the tetrahedron: a fraction `t` of the way down it from the top
if `m` is even, a fraction `t` of the way up it from the bottom if `m` is odd — "down the
back-edge; up again; and so on". -/
theorem problem70_1 (c : Wrapping) (hc : c.Starts) :
    (∀ V : Plane, 0 < V 1 →
      (triArea (pt 0 0) (pt 1 0) V = triArea (pt 0 0) (pt 1 0) (pt (1 / 2) width) ↔
        V 1 = width)) ∧
    ∀ (m : ℤ) (t : ℝ), 0 ≤ t → t < 1 →
      wrapUp c (m + 1 / 2 + t) =
        if Even m then AffineMap.lineMap (pos .Tp) (pos .Bk) t
        else AffineMap.lineMap (pos .Bk) (pos .Tp) t := by
  refine ⟨fun V hV => ⟨fun h => vertex_height h hV, fun h => ?_⟩,
    fun m t h0 h1 => locus c hc m t h0 h1⟩
  simp only [triArea, cross, pt_zero, pt_one, h]
  ring_nf

/-! ### Parts (3), (4): covering -/

private lemma openTri_coords {P Q R p : Plane} (h : p ∈ openTri P Q R) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 1 ∧
      p 0 = a * P 0 + b * Q 0 + c * R 0 ∧ p 1 = a * P 1 + b * Q 1 + c * R 1 := by
  obtain ⟨a, b, c, ha, hb, hc, hs, rfl⟩ := h
  exact ⟨a, b, c, ha, hb, hc, hs, by simp, by simp⟩

private lemma mem_openTri {P Q R p : Plane} (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hs : a + b + c = 1) (h0 : p 0 = a * P 0 + b * Q 0 + c * R 0)
    (h1 : p 1 = a * P 1 + b * Q 1 + c * R 1) : p ∈ openTri P Q R := by
  refine ⟨a, b, c, ha, hb, hc, hs, ?_⟩
  ext i; fin_cases i <;> simp [h0, h1]

private lemma stripTri_even (m : ℤ) : stripTri (2 * m) = (lower m, lower (m + 1), upper m) := by
  have h1 : 2 * m % 2 = 0 := by omega
  have h2 : 2 * m / 2 = m := by omega
  simp [stripTri, h1, h2]

private lemma stripTri_odd (m : ℤ) :
    stripTri (2 * m + 1) = (lower (m + 1), upper (m + 1), upper m) := by
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  simp [stripTri, h1, h2]

/-- The linear facts behind a covering: a common interior point, in barycentric coordinates
`(·, b, c)` of the triangle and `(a', b', c')` of the strip triangle. -/
private lemma covers_facts {V : Plane} (hV : V 1 = width) {k : ℤ} (h : covers V k) :
    ∃ b c : ℝ, 0 < b ∧ 0 < c ∧ b + c < 1 ∧ ∃ m : ℤ, ∃ a' b' c' : ℝ,
      0 < a' ∧ 0 < b' ∧ 0 < c' ∧ a' + b' + c' = 1 ∧
      ((k = 2 * m ∧ b + c * V 0 = a' * m + b' * (m + 1) + c' * (m + 1 / 2) ∧ c = c') ∨
       (k = 2 * m + 1 ∧ b + c * V 0 = a' * (m + 1) + b' * (m + 3 / 2) + c' * (m + 1 / 2) ∧
          c = b' + c')) := by
  have hw : 0 < width := by unfold width; positivity
  obtain ⟨p, hp1, hp2⟩ := h
  obtain ⟨a, b, c, ha, hb, hc, hs, e0, e1⟩ := openTri_coords hp1
  simp only [pt_zero, pt_one, hV] at e0 e1
  refine ⟨b, c, hb, hc, by linarith, ?_⟩
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · rw [stripTri_even] at hp2
    obtain ⟨a', b', c', ha', hb', hc', hs', f0, f1⟩ := openTri_coords hp2
    simp only [lower, upper, pt_zero, pt_one] at f0 f1
    refine ⟨m, a', b', c', ha', hb', hc', hs', Or.inl ⟨rfl, ?_, ?_⟩⟩
    · push_cast at f0; linarith
    · have : (c - c') * width = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
  · rw [stripTri_odd] at hp2
    obtain ⟨a', b', c', ha', hb', hc', hs', f0, f1⟩ := openTri_coords hp2
    simp only [lower, upper, pt_zero, pt_one] at f0 f1
    refine ⟨m, a', b', c', ha', hb', hc', hs', Or.inr ⟨rfl, ?_, ?_⟩⟩
    · push_cast at f0; linarith
    · have : (c - (b' + c')) * width = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith

/-- A triangle leaning to the right meets no strip triangle to the left of the front facet. -/
private lemma not_covers_neg {V : Plane} (hV : V 1 = width) (hv : 1 / 2 ≤ V 0) {k : ℤ}
    (hk : k < 0) : ¬ covers V k := by
  intro h
  obtain ⟨b, c, hb, hc, hbc, m, a', b', c', ha', hb', hc', hs', H⟩ := covers_facts hV h
  have hsum : a' * m + b' * m + c' * m = m := by linear_combination (m : ℝ) * hs'
  have hcv : 0 ≤ c * (V 0 - 1 / 2) := mul_nonneg hc.le (by linarith)
  rcases H with ⟨rfl, e, rfl⟩ | ⟨rfl, e, he⟩
  · have : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
    nlinarith
  · have : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
    nlinarith

/-- A triangle whose vertex is at most `n + ½` along meets no strip triangle beyond the
`2n`-th. -/
private lemma not_covers_far {V : Plane} (hV : V 1 = width) (n : ℤ) (hn : 1 ≤ n)
    (hv : V 0 ≤ n + 1 / 2) {k : ℤ} (hk : 2 * n ≤ k) : ¬ covers V k := by
  intro h
  obtain ⟨b, c, hb, hc, hbc, m, a', b', c', ha', hb', hc', hs', H⟩ := covers_facts hV h
  have hsum : a' * m + b' * m + c' * m = m := by linear_combination (m : ℝ) * hs'
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcv : c * (V 0 - 1 / 2) ≤ c * n := mul_le_mul_of_nonneg_left (by linarith) hc.le
  have hbn : b ≤ b * n := by nlinarith
  have hlt : (n : ℝ) * (b + c) < n := by nlinarith
  rcases H with ⟨rfl, e, rfl⟩ | ⟨rfl, e, he⟩
  · have : (n : ℝ) ≤ m := by exact_mod_cast (show n ≤ m by omega)
    nlinarith
  · have : (n : ℝ) ≤ m := by exact_mod_cast (show n ≤ m by omega)
    nlinarith

/-- To cover a portion of the base-up strip triangle `2n + 1`, the vertex must be beyond
`n + ½`. -/
private lemma reach_of_covers {V : Plane} (hV : V 1 = width) (n : ℤ) (hn : 1 ≤ n)
    (h : covers V (2 * n + 1)) : (n : ℝ) + 1 / 2 < V 0 := by
  obtain ⟨b, c, hb, hc, hbc, m, a', b', c', ha', hb', hc', hs', H⟩ := covers_facts hV h
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rcases H with ⟨hk, -, -⟩ | ⟨hk, e, -⟩
  · exact absurd hk (by omega)
  · have hm : m = n := by omega
    rw [hm] at e
    have hsum : a' * n + b' * n + c' * n = n := by linear_combination (n : ℝ) * hs'
    by_contra hv'
    have hv := le_of_not_gt hv'
    have h1 : c * V 0 ≤ c * (n + 1 / 2) := mul_le_mul_of_nonneg_left hv hc.le
    have h2 : b ≤ b * (n + 1 / 2) := by nlinarith
    have h3 : (b + c) * (n + 1 / 2) < n + 1 / 2 := by nlinarith
    nlinarith

/-- A witness for a covering. -/
private lemma wit {V : Plane} {k : ℤ} (x η a b c a' b' c' : ℝ)
    (ha : 0 < a := by norm_num) (hb : 0 < b := by norm_num) (hc : 0 < c := by norm_num)
    (hs : a + b + c = 1 := by norm_num) (ha' : 0 < a' := by norm_num)
    (hb' : 0 < b' := by norm_num) (hc' : 0 < c' := by norm_num)
    (hs' : a' + b' + c' = 1 := by norm_num)
    (e0 : x = a * pt 0 0 0 + b * pt 1 0 0 + c * V 0 := by simp <;> ring)
    (e1 : η * width = a * pt 0 0 1 + b * pt 1 0 1 + c * V 1 := by simp <;> ring)
    (f0 : x = a' * (stripTri k).1 0 + b' * (stripTri k).2.1 0 + c' * (stripTri k).2.2 0 := by
      simp [stripTri, lower, upper] <;> ring)
    (f1 : η * width =
      a' * (stripTri k).1 1 + b' * (stripTri k).2.1 1 + c' * (stripTri k).2.2 1 := by
      simp [stripTri, lower, upper] <;> ring) :
    covers V k :=
  ⟨pt x (η * width), mem_openTri a b c ha hb hc hs e0 e1, mem_openTri a' b' c' ha' hb' hc' hs' f0 f1⟩

/-- Beyond `4` along, the triangle reaches the strip triangle `4` (the base, second time). -/
private lemma covers_four {v : ℝ} (hv : 4 < v) : covers (pt v width) 4 := by
  have hv0 : 0 < v := by linarith
  refine wit (5 / 2) (2 / v) (1 / 2 - 2 / v) (1 / 2) (2 / v) ((1 - 2 / v) / 2)
    ((1 - 2 / v) / 2) (2 / v) ?_ (by norm_num) (div_pos two_pos hv0) (by ring) ?_ ?_
    (div_pos two_pos hv0) (by ring) ?_ (by simp) ?_ ?_
  · rw [sub_pos, div_lt_iff₀ hv0]; linarith
  · apply div_pos _ two_pos; rw [sub_pos, div_lt_iff₀ hv0]; linarith
  · apply div_pos _ two_pos; rw [sub_pos, div_lt_iff₀ hv0]; linarith
  · simp only [pt_zero]
    field_simp
    ring
  · simp [stripTri, lower, upper]
    ring
  · simp [stripTri, lower, upper]

/-- Beyond `13/3` along, the triangle reaches the strip triangle `6` (the base, second time). -/
private lemma covers_six {v : ℝ} (hv : 13 / 3 < v) : covers (pt v width) 6 := by
  have hv0 : 0 < v := by linarith
  refine wit (7 / 2) (13 / 4 / v) (3 / 4 - 13 / 4 / v) (1 / 4) (13 / 4 / v)
    ((1 - 13 / 4 / v) / 2) ((1 - 13 / 4 / v) / 2) (13 / 4 / v) ?_ (by norm_num)
    (div_pos (by norm_num) hv0) (by ring) ?_ ?_ (div_pos (by norm_num) hv0) (by ring) ?_ (by simp)
    ?_ ?_
  · rw [sub_pos, div_lt_iff₀ hv0]; linarith
  · apply div_pos _ two_pos; rw [sub_pos, div_lt_iff₀ hv0]; linarith
  · apply div_pos _ two_pos; rw [sub_pos, div_lt_iff₀ hv0]; linarith
  · simp only [pt_zero]
    field_simp
    ring
  · simp [stripTri, lower, upper]
    ring
  · simp [stripTri, lower, upper]

/-- A covering of the base-down strip triangle `2m`, witnessed by the point `(X, η·width)`. -/
private lemma covers_down {x : ℝ} (m : ℤ) (η X : ℝ) (hη : 0 < η)
    (h1 : η * x < X) (h2 : X < η * x + 1 - η) (h3 : m + η / 2 < X) (h4 : X < m + 1 - η / 2) :
    covers (pt x width) (2 * m) := by
  refine ⟨pt X (η * width), mem_openTri (1 - (X - η * x) - η) (X - η * x) η (by linarith)
    (by linarith) hη (by ring) (by simp) (by simp), ?_⟩
  rw [stripTri_even]
  exact mem_openTri (m + 1 - X - η / 2) (X - m - η / 2) η (by linarith) (by linarith) hη
    (by ring) (by simp [lower, upper]; ring) (by simp [lower, upper])

/-- A covering of the base-up strip triangle `2m + 1`, witnessed by the point `(X, η·width)`. -/
private lemma covers_up {x : ℝ} (m : ℤ) (η X : ℝ) (hη : 0 < η)
    (h1 : η * x < X) (h2 : X < η * x + 1 - η) (h3 : m + 1 - η / 2 < X)
    (h4 : X < m + 1 + η / 2) :
    covers (pt x width) (2 * m + 1) := by
  refine ⟨pt X (η * width), mem_openTri (1 - (X - η * x) - η) (X - η * x) η (by linarith)
    (by linarith) hη (by ring) (by simp) (by simp), ?_⟩
  rw [stripTri_odd]
  exact mem_openTri (1 - η) (η / 2 + (X - m - 1)) (η / 2 - (X - m - 1)) (by linarith)
    (by linarith) (by linarith) (by ring) (by simp [lower, upper]; ring)
    (by simp [lower, upper]; ring)

/-- A triangle whose vertex is at least `5/2` along covers strip triangles `0, 1, 2, 3`. -/
private lemma covers_first_four {x : ℝ} (hx : 5 / 2 ≤ x) :
    covers (pt x width) 0 ∧ covers (pt x width) 1 ∧ covers (pt x width) 2 ∧
      covers (pt x width) 3 := by
  have hx0 : 0 < x := by linarith
  have eta : ∀ s : ℝ, 0 < s → ∃ η : ℝ, 0 < η ∧ η * x = s ∧ η * (5 / 2) ≤ s := by
    intro s hs
    refine ⟨s / x, div_pos hs hx0, div_mul_cancel₀ s hx0.ne', ?_⟩
    rw [div_mul_eq_mul_div, div_le_iff₀ hx0]; nlinarith
  obtain ⟨η0, p0, e0, b0⟩ := eta (1 / 4) (by norm_num)
  obtain ⟨η1, p1, e1, b1⟩ := eta (1 / 2) (by norm_num)
  obtain ⟨η2, p2, e2, b2⟩ := eta 1 (by norm_num)
  obtain ⟨η3, p3, e3, b3⟩ := eta (7 / 4) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using covers_down 0 η0 (1 / 2) p0 (by linarith) (by linarith) (by push_cast; linarith)
      (by push_cast; linarith)
  · simpa using covers_up 0 η1 1 p1 (by linarith) (by linarith) (by push_cast; linarith)
      (by push_cast; linarith)
  · simpa using covers_down 1 η2 (3 / 2) p2 (by linarith) (by linarith) (by push_cast; linarith)
      (by push_cast; linarith)
  · simpa using covers_up 1 η3 2 p3 (by linarith) (by linarith) (by push_cast; linarith)
      (by push_cast; linarith)

/-- The facets on which the first six strip triangles lie. -/
private lemma facet_vals (c : Wrapping) (hc : c.Starts) :
    facet c 0 = facetFront ∧ facet c 1 = facetRight ∧ facet c 2 = facetBase ∧
      facet c 3 = facetLeft ∧ facet c 4 = facetFront ∧ facet c 5 = facetRight := by
  simp [facet, lo_eq c hc, up_eq c hc, facetFront, facetRight, facetBase, facetLeft,
    Int.even_iff]
  decide

/-- If the vertex lands on `Tp` or `Bk`, it is an upper lattice point of the strip. -/
private lemma wrap_at_vertex (c : Wrapping) (hc : c.Starts) (x : ℝ) (v : Vtx)
    (hv : v = .Tp ∨ v = .Bk) (h : wrapUp c x = pos v) :
    x = ⌊x - 1 / 2⌋ + 1 / 2 ∧ c.up ⌊x - 1 / 2⌋ = v := by
  obtain ⟨m, t, ht0, ht1, hx, hm⟩ : ∃ (m : ℤ) (t : ℝ), 0 ≤ t ∧ t < 1 ∧
      x = m + 1 / 2 + t ∧ ⌊x - 1 / 2⌋ = m :=
    ⟨⌊x - 1 / 2⌋, Int.fract (x - 1 / 2), Int.fract_nonneg _, Int.fract_lt_one _,
      by linarith [Int.floor_add_fract (x - 1 / 2)], rfl⟩
  rw [hm]
  rw [hx, wrapUp_eq c m ht0 ht1] at h
  have h6 : 0 < √6 / 3 := by positivity
  have comp : ∀ (A B : Space) (s : ℝ),
      (AffineMap.lineMap A B s : Space) 2 = A 2 + s * (B 2 - A 2) := by
    intro A B s; simp [AffineMap.lineMap_apply]; ring
  have h2 := congrArg (fun p : Space => p 2) h
  simp only [comp] at h2
  rw [up_eq c hc, up_eq c hc] at h2
  rw [up_eq c hc]
  by_cases he : Even m
  · have he1 : ¬ Even (m + 1) := fun h => Int.even_add_one.mp h he
    simp only [he, he1, ↓reduceIte] at h2 ⊢
    rcases hv with rfl | rfl
    · simp only [pos, sp_two] at h2
      have h0 : t * (√6 / 3) = 0 := by linarith
      have ht : t = 0 := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · exact h'
        · linarith
      exact ⟨by rw [hx, ht]; ring, rfl⟩
    · simp only [pos, sp_two] at h2
      have h0 : (1 - t) * (√6 / 3) = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h' | h' <;> linarith
  · have he1 : Even (m + 1) := Int.even_add_one.mpr he
    simp only [he, he1, ↓reduceIte] at h2 ⊢
    rcases hv with rfl | rfl
    · simp only [pos, sp_two] at h2
      have h0 : (1 - t) * (√6 / 3) = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h' | h' <;> linarith
    · simp only [pos, sp_two] at h2
      have h0 : t * (√6 / 3) = 0 := by linarith
      have ht : t = 0 := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · exact h'
        · linarith
      exact ⟨by rw [hx, ht]; ring, rfl⟩

/-! ### Numerical bounds -/

private lemma tan_lt_of {a lo hi s : ℝ} (hlo0 : 0 ≤ lo) (hlo : lo ≤ a) (hhi : a ≤ hi)
    (hhi1 : hi ≤ 1) (hs : 0 ≤ s)
    (key : hi - lo ^ 3 / 6 + hi ^ 5 / 100 < s * (1 - hi ^ 2 / 2 - hi ^ 4 * (5 / 96))) :
    Real.sin a < s * Real.cos a := by
  have ha : |a| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hs1 := Real.sin_bound ha
  have hc1 := Real.cos_bound ha
  rw [abs_of_nonneg (by linarith : 0 ≤ a)] at hs1 hc1
  have e3 : lo ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ hlo0 hlo 3
  have e4 : a ^ 4 ≤ hi ^ 4 := pow_le_pow_left₀ (by linarith) hhi 4
  have e2 : a ^ 2 ≤ hi ^ 2 := pow_le_pow_left₀ (by linarith) hhi 2
  have e5 : a ^ 5 ≤ hi ^ 5 := pow_le_pow_left₀ (by linarith) hhi 5
  have hsin : Real.sin a ≤ a - a ^ 3 / 6 + a ^ 5 / 100 := by linarith [(abs_le.mp hs1).2]
  have hcos : 1 - a ^ 2 / 2 - a ^ 4 * (5 / 96) ≤ Real.cos a := by linarith [(abs_le.mp hc1).1]
  have : s * (1 - hi ^ 2 / 2 - hi ^ 4 * (5 / 96)) ≤ s * Real.cos a :=
    mul_le_mul_of_nonneg_left (by linarith) hs
  linarith

private lemma lt_tan_of {a lo hi s : ℝ} (hlo0 : 0 ≤ lo) (hlo : lo ≤ a) (hhi : a ≤ hi)
    (hhi1 : hi ≤ 1) (hs : 0 ≤ s)
    (key : s * (1 - lo ^ 2 / 2 + hi ^ 4 * (5 / 96)) < lo - hi ^ 3 / 6 - hi ^ 5 / 100) :
    s * Real.cos a < Real.sin a := by
  have ha : |a| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hs1 := Real.sin_bound ha
  have hc1 := Real.cos_bound ha
  rw [abs_of_nonneg (by linarith : 0 ≤ a)] at hs1 hc1
  have e3 : a ^ 3 ≤ hi ^ 3 := pow_le_pow_left₀ (by linarith) hhi 3
  have e4 : a ^ 4 ≤ hi ^ 4 := pow_le_pow_left₀ (by linarith) hhi 4
  have e2 : lo ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hlo0 hlo 2
  have e5 : a ^ 5 ≤ hi ^ 5 := pow_le_pow_left₀ (by linarith) hhi 5
  have hsin : a - a ^ 3 / 6 - a ^ 5 / 100 ≤ Real.sin a := by linarith [(abs_le.mp hs1).1]
  have hcos : Real.cos a ≤ 1 - a ^ 2 / 2 + a ^ 4 * (5 / 96) := by linarith [(abs_le.mp hc1).2]
  have : s * Real.cos a ≤ s * (1 - lo ^ 2 / 2 + hi ^ 4 * (5 / 96)) :=
    mul_le_mul_of_nonneg_left (by linarith) hs
  linarith

/-- `d·π/180 < arctan s`, from a bound on `tan`. -/
private lemma deg_lt_arctan {d lo hi s : ℝ} (hd : 0 < d) (hd' : d < 90)
    (hlo0 : 0 ≤ lo) (hlo : lo ≤ d * 3.1415 / 180) (hhi : d * 3.1416 / 180 ≤ hi) (hhi1 : hi ≤ 1)
    (hs : 0 ≤ s)
    (key : hi - lo ^ 3 / 6 + hi ^ 5 / 100 < s * (1 - hi ^ 2 / 2 - hi ^ 4 * (5 / 96))) :
    d < arctan s * 180 / π := by
  have p1 := Real.pi_gt_d4
  have p2 := Real.pi_lt_d4
  set a := d * π / 180 with ha
  have ha1 : -(π / 2) < a := by rw [ha]; nlinarith
  have ha2 : a < π / 2 := by rw [ha]; nlinarith
  have hcos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨ha1, ha2⟩
  have hlt : Real.sin a < s * Real.cos a :=
    tan_lt_of hlo0 (by rw [ha]; nlinarith) (by rw [ha]; nlinarith) hhi1 hs key
  have htan : Real.tan a < s := by
    rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcos]; exact hlt
  have : a < arctan s := by
    rw [← Real.arctan_tan ha1 ha2]; exact Real.arctan_strictMono htan
  rw [lt_div_iff₀ Real.pi_pos]
  rw [ha] at this
  linarith

/-- `arctan s < d·π/180`, from a bound on `tan`. -/
private lemma arctan_lt_deg {d lo hi s : ℝ} (hd : 0 < d) (hd' : d < 90)
    (hlo0 : 0 ≤ lo) (hlo : lo ≤ d * 3.1415 / 180) (hhi : d * 3.1416 / 180 ≤ hi) (hhi1 : hi ≤ 1)
    (hs : 0 ≤ s)
    (key : s * (1 - lo ^ 2 / 2 + hi ^ 4 * (5 / 96)) < lo - hi ^ 3 / 6 - hi ^ 5 / 100) :
    arctan s * 180 / π < d := by
  have p1 := Real.pi_gt_d4
  have p2 := Real.pi_lt_d4
  set a := d * π / 180 with ha
  have ha1 : -(π / 2) < a := by rw [ha]; nlinarith
  have ha2 : a < π / 2 := by rw [ha]; nlinarith
  have hcos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨ha1, ha2⟩
  have hlt : s * Real.cos a < Real.sin a :=
    lt_tan_of hlo0 (by rw [ha]; nlinarith) (by rw [ha]; nlinarith) hhi1 hs key
  have htan : s < Real.tan a := by
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos]; exact hlt
  have : arctan s < a := by
    rw [← Real.arctan_tan ha1 ha2]; exact Real.arctan_strictMono htan
  rw [div_lt_iff₀ Real.pi_pos]
  rw [ha] at this
  linarith

private lemma sqrt3_bounds : 1.732 < √3 ∧ √3 < 1.7321 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ √3 := Real.sqrt_nonneg 3
  constructor <;> nlinarith

/-! ### Part (2) -/

/-- **Problem 70 (2).** The triangle of the series whose left-hand base-angle is `15°`: its
vertex is at `(½ + 2 + (√3 - 1), width)`, i.e. after going down the back edge and up again, it
lands `√3 - 1` (about `·73`) of the way down the back edge. -/
theorem problem70_2 (c : Wrapping) (hc : c.Starts) (V : Plane)
    (hA : triArea (pt 0 0) (pt 1 0) V = triArea (pt 0 0) (pt 1 0) (pt (1 / 2) width))
    (hV : 0 < V 1) (hθ : ∠ V (pt 0 0) (pt 1 0) = π / 12) :
    V 0 = 1 / 2 + 2 + (√3 - 1) ∧
      wrapUp c (V 0) = AffineMap.lineMap (pos .Tp) (pos .Bk) (√3 - 1) ∧
      7 / 10 < √3 - 1 ∧ √3 - 1 < 3 / 4 := by
  have hV1 := vertex_height hA hV
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨s1, s2⟩ := sqrt3_bounds
  have hw2 : width ^ 2 = 3 / 4 := by unfold width; rw [div_pow, h3]; norm_num
  rw [angle_eq, hV1] at hθ
  set x := V 0 with hxdef
  have hSpos : 0 < √(x ^ 2 + width ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hS2 : √(x ^ 2 + width ^ 2) ^ 2 = x ^ 2 + width ^ 2 := Real.sq_sqrt (by positivity)
  have hu : |x / √(x ^ 2 + width ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos hSpos, div_le_one hSpos]
    exact Real.abs_le_sqrt (by nlinarith)
  have hk : x / √(x ^ 2 + width ^ 2) = Real.cos (π / 12) := by
    rw [← hθ, Real.cos_arccos (abs_le.mp hu).1 (abs_le.mp hu).2]
  have hkpos : 0 < Real.cos (π / 12) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hk2 : Real.cos (π / 12) ^ 2 = 1 / 2 + √3 / 4 := by
    rw [Real.cos_sq, show 2 * (π / 12) = π / 6 by ring, Real.cos_pi_div_six]; ring
  have hxk : x = Real.cos (π / 12) * √(x ^ 2 + width ^ 2) := by
    rw [← hk, div_mul_cancel₀ _ hSpos.ne']
  have hxpos : 0 < x := by rw [hxk]; exact mul_pos hkpos hSpos
  have E : x ^ 2 * (1 / 2 - √3 / 4) = (1 / 2 + √3 / 4) * (3 / 4) := by
    have : x ^ 2 = Real.cos (π / 12) ^ 2 * (x ^ 2 + width ^ 2) := by
      calc x ^ 2 = (Real.cos (π / 12) * √(x ^ 2 + width ^ 2)) ^ 2 := by rw [← hxk]
        _ = Real.cos (π / 12) ^ 2 * √(x ^ 2 + width ^ 2) ^ 2 := by ring
        _ = Real.cos (π / 12) ^ 2 * (x ^ 2 + width ^ 2) := by rw [hS2]
    rw [hk2, hw2] at this
    linear_combination this
  have key : (x ^ 2 - (√3 + 3 / 2) ^ 2) * (1 / 2 - √3 / 4) = 0 := by
    linear_combination E + (1 / 4) * (√3 + 1) * h3
  have hx : x = √3 + 3 / 2 := by
    rcases mul_eq_zero.mp key with h | h
    · exact (pow_left_inj₀ hxpos.le (by positivity) two_ne_zero).mp (by linarith)
    · linarith
  have hV0 : x = 1 / 2 + 2 + (√3 - 1) := by rw [hx]; ring
  refine ⟨hV0, ?_, by linarith, by linarith⟩
  rw [hV0, show (1 / 2 + 2 + (√3 - 1) : ℝ) = ((2 : ℤ) : ℝ) + 1 / 2 + (√3 - 1) by push_cast; ring,
    locus c hc 2 _ (by linarith) (by linarith)]
  simp [show Even (2 : ℤ) from even_two]

/-- The hypotheses of `problem70_2` are satisfiable: the triangle with vertex
`(√3 + 3/2, width)` is of the series and has left-hand base-angle `15°`. -/
theorem problem70_2_nonvacuous :
    ∃ V : Plane, triArea (pt 0 0) (pt 1 0) V = triArea (pt 0 0) (pt 1 0) (pt (1 / 2) width) ∧
      0 < V 1 ∧ ∠ V (pt 0 0) (pt 1 0) = π / 12 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hw : 0 < width := by unfold width; positivity
  refine ⟨pt (√3 + 3 / 2) width, ?_, by simpa using hw, ?_⟩
  · simp only [triArea, cross, pt_zero, pt_one]
    ring_nf
  · rw [angle_eq]
    simp only [pt_zero, pt_one]
    have hxpos : 0 < √3 + 3 / 2 := by positivity
    have hkpos : 0 < Real.cos (π / 12) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hk2 : Real.cos (π / 12) ^ 2 = 1 / 2 + √3 / 4 := by
      rw [Real.cos_sq, show 2 * (π / 12) = π / 6 by ring, Real.cos_pi_div_six]; ring
    have hS : (√3 + 3 / 2) ^ 2 + width ^ 2 = ((√3 + 3 / 2) / Real.cos (π / 12)) ^ 2 := by
      rw [div_pow, eq_div_iff (pow_ne_zero 2 hkpos.ne'), hk2]
      unfold width
      linear_combination (5 / 16 * √3 + 3 / 8) * h3
    rw [hS, Real.sqrt_sq (div_pos hxpos hkpos).le, div_div_cancel₀ hxpos.ne',
      Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

/-! ### Part (3) -/

/-- The triangles wrapped towards the right whose vertex lands on `Tp` and which cover portions
of all four facets are those with vertex `(2j + ½, width)`, `j ≥ 1`. -/
private lemma tp_all_four (c : Wrapping) (hc : c.Starts) (V : Plane)
    (hA : triArea (pt 0 0) (pt 1 0) V = triArea (pt 0 0) (pt 1 0) (pt (1 / 2) width))
    (hV : 0 < V 1) (hr : 1 / 2 ≤ V 0) :
    (wrapUp c (V 0) = pos .Tp ∧
        ∀ F ∈ [facetFront, facetRight, facetBase, facetLeft], coversFacet c V F) ↔
      ∃ j : ℕ, 1 ≤ j ∧ V = pt (2 * j + 1 / 2) width := by
  have hV1 := vertex_height hA hV
  have hVeq : V = pt (V 0) width := by
    ext i; fin_cases i <;> simp [hV1]
  obtain ⟨f0, f1, f2, f3, -, -⟩ := facet_vals c hc
  constructor
  · rintro ⟨hw, hcov⟩
    obtain ⟨hx, hup⟩ := wrap_at_vertex c hc (V 0) .Tp (Or.inl rfl) hw
    set m := ⌊V 0 - 1 / 2⌋
    have hev : Even m := by
      by_contra hne; rw [up_eq c hc] at hup; simp only [hne, ↓reduceIte] at hup
      exact absurd hup (by decide)
    obtain ⟨r, hr'⟩ := hev
    have hm0 : (0 : ℝ) ≤ m := by linarith
    have hm0' : 0 ≤ m := by exact_mod_cast hm0
    have hm_ne : m ≠ 0 := by
      intro hm
      have hmR : (m : ℝ) = 0 := by exact_mod_cast hm
      obtain ⟨k, hk, hkF⟩ := hcov facetBase (by simp)
      have k0 : 0 ≤ k := by
        by_contra h; exact not_covers_neg hV1 (by linarith) (by omega) hk
      have k2 : k < 2 := by
        by_contra h
        exact not_covers_far hV1 1 le_rfl (by push_cast; linarith) (by omega) hk
      interval_cases k
      · rw [f0] at hkF; exact absurd hkF (by decide)
      · rw [f1] at hkF; exact absurd hkF (by decide)
    have hr0 : 0 ≤ r := by omega
    refine ⟨r.toNat, by omega, ?_⟩
    rw [hVeq, hx]
    congr 1
    have h1 : ((r.toNat : ℤ) : ℝ) = r := by rw [Int.toNat_of_nonneg hr0]
    have h2 : (m : ℝ) = r + r := by exact_mod_cast hr'
    rw [Int.cast_natCast] at h1
    rw [h1, h2]; ring
  · rintro ⟨j, hj, rfl⟩
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    obtain ⟨c0, c1, c2, c3⟩ := covers_first_four (x := 2 * j + 1 / 2) (by linarith)
    refine ⟨?_, ?_⟩
    · have h := locus c hc (2 * (j : ℤ)) 0 le_rfl one_pos
      rw [pt_zero, show (2 * (j : ℝ) + 1 / 2) = ((2 * (j : ℤ) : ℤ) : ℝ) + 1 / 2 + 0 by
        push_cast; ring, h]
      simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro F (rfl | rfl | rfl | rfl)
      · exact ⟨0, c0, f0⟩
      · exact ⟨1, c1, f1⟩
      · exact ⟨2, c2, f2⟩
      · exact ⟨3, c3, f3⟩

/-- **Problem 70 (3)** (corrected). The triangles of the series (on the common base, equal to the
facet) wrapped towards the right whose vertex lands on the top vertex `Tp` of the tetrahedron and
which cover portions of all four facets are those with vertex `(2j + ½, width)`, `j ≥ 1`; the
first of them, Carroll's, is the one with vertex `(5/2, width)`, the only one covering exactly
the strip triangles `0, 1, 2, 3` (lying on the front, right, base and left facets). Its left-hand
base-angle is `arctan (√3/5)`, which is between `19°` and `19·2°` — not Carroll's `18·65°`. -/
theorem problem70_3 (c : Wrapping) (hc : c.Starts) :
    (∀ V : Plane,
      triArea (pt 0 0) (pt 1 0) V = triArea (pt 0 0) (pt 1 0) (pt (1 / 2) width) → 0 < V 1 →
      1 / 2 ≤ V 0 →
      ((wrapUp c (V 0) = pos .Tp ∧
          ∀ F ∈ [facetFront, facetRight, facetBase, facetLeft], coversFacet c V F) ↔
        ∃ j : ℕ, 1 ≤ j ∧ V = pt (2 * j + 1 / 2) width)) ∧
    (∀ V : Plane,
      triArea (pt 0 0) (pt 1 0) V = triArea (pt 0 0) (pt 1 0) (pt (1 / 2) width) → 0 < V 1 →
      ((wrapUp c (V 0) = pos .Tp ∧ {k : ℤ | covers V k} = Set.Icc 0 3) ↔
        V = pt (5 / 2) width)) ∧
    [facet c 0, facet c 1, facet c 2, facet c 3] = [facetFront, facetRight, facetBase, facetLeft] ∧
    ∠ (pt (5 / 2) width) (pt 0 0) (pt 1 0) = arctan (√3 / 5) ∧
    19 < arctan (√3 / 5) * 180 / π ∧ arctan (√3 / 5) * 180 / π < 19.2 := by
  obtain ⟨s1, s2⟩ := sqrt3_bounds
  refine ⟨fun V hA hV hr => tp_all_four c hc V hA hV hr, fun V hA hV => ?_, ?_, ?_, ?_, ?_⟩
  · have hV1 := vertex_height hA hV
    have hVeq : V = pt (V 0) width := by
      ext i; fin_cases i <;> simp [hV1]
    constructor
    · rintro ⟨hw, hcov⟩
      obtain ⟨hx, hup⟩ := wrap_at_vertex c hc (V 0) .Tp (Or.inl rfl) hw
      set m := ⌊V 0 - 1 / 2⌋
      have hev : Even m := by
        by_contra hne; rw [up_eq c hc] at hup; simp only [hne, ↓reduceIte] at hup
        exact absurd hup (by decide)
      have h3 : covers V 3 := by
        have : (3 : ℤ) ∈ {k : ℤ | covers V k} := by rw [hcov]; simp
        exact this
      have h4 : ¬ covers V 4 := by
        intro h
        have : (4 : ℤ) ∈ {k : ℤ | covers V k} := h
        rw [hcov] at this; simp at this
      have r3 := reach_of_covers hV1 1 le_rfl (by simpa using h3)
      have r4 : V 0 ≤ 4 := by
        by_contra hgt'
        have hgt := lt_of_not_ge hgt'
        exact h4 (by rw [hVeq]; exact covers_four hgt)
      have hm1 : (1 : ℝ) < m := by push_cast at r3; linarith
      have hm2 : (m : ℝ) ≤ 7 / 2 := by linarith
      have hm1' : 1 < m := by exact_mod_cast hm1
      have hm2' : m < 4 := by
        have : (m : ℝ) < 4 := by linarith
        exact_mod_cast this
      obtain ⟨r, hr⟩ := hev
      have hm : m = 2 := by omega
      rw [hVeq, hx, hm]; norm_num
    · rintro rfl
      refine ⟨?_, ?_⟩
      · have h := locus c hc 2 0 le_rfl one_pos
        rw [show ((2 : ℤ) : ℝ) + 1 / 2 + 0 = 5 / 2 by norm_num] at h
        simp only [even_two, ↓reduceIte, AffineMap.lineMap_apply_zero] at h
        simpa using h
      · ext k
        rw [Set.mem_Icc]
        change covers _ k ↔ _
        constructor
        · intro h
          by_contra hk
          rcases not_and_or.mp hk with hk | hk
          · exact not_covers_neg (by simp) (by norm_num) (by omega) h
          · exact not_covers_far (by simp) 2 (by norm_num) (by norm_num)
              (by omega) h
        · rintro ⟨hk0, hk3⟩
          interval_cases k
          · exact wit (7 / 10 : ℝ) (1 / 5 : ℝ) (3 / 5 : ℝ) (1 / 5 : ℝ) (1 / 5 : ℝ) (1 / 5 : ℝ)
              (3 / 5 : ℝ) (1 / 5 : ℝ)
          · exact wit (1 : ℝ) (13 / 40 : ℝ) (39 / 80 : ℝ) (3 / 16 : ℝ) (13 / 40 : ℝ)
              (27 / 40 : ℝ) (13 / 80 : ℝ) (13 / 80 : ℝ)
          · exact wit (3 / 2 : ℝ) (1 / 2 : ℝ) (1 / 4 : ℝ) (1 / 4 : ℝ) (1 / 2 : ℝ) (1 / 4 : ℝ)
              (1 / 4 : ℝ) (1 / 2 : ℝ)
          · exact wit (37 / 20 : ℝ) (27 / 40 : ℝ) (13 / 80 : ℝ) (13 / 80 : ℝ) (27 / 40 : ℝ)
              (13 / 40 : ℝ) (3 / 16 : ℝ) (39 / 80 : ℝ)
  · simp [facet, lo_eq c hc, up_eq c hc, facetFront, facetRight, facetBase, facetLeft,
      Int.even_iff]
    decide
  · rw [angle_eq]
    simp only [pt_zero, pt_one]
    rw [arccos_eq_arctan (x := 5 / 2) (y := width) (by norm_num) (by unfold width; positivity)]
    congr 1; unfold width; ring
  · exact deg_lt_arctan (lo := 0.3316) (hi := 0.33162) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by positivity)
      (by nlinarith)
  · exact arctan_lt_deg (lo := 0.33509) (hi := 0.33511) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by positivity)
      (by nlinarith)

/-! ### Part (4) -/

/-- **Problem 70 (4)** (corrected). The triangle of the series whose vertex lands on the back
vertex `Bk` of the base and which covers portions of the facets front, right, base, left, front,
right (strip triangles `0, …, 5`) is the one with vertex `(7/2, width)`; its left-hand base-angle
is `arctan (√3/7)`, which is between `13·8°` and `14°` — not Carroll's `14·53°`. -/
theorem problem70_4 (c : Wrapping) (hc : c.Starts) :
    (∀ V : Plane,
      triArea (pt 0 0) (pt 1 0) V = triArea (pt 0 0) (pt 1 0) (pt (1 / 2) width) → 0 < V 1 →
      ((wrapUp c (V 0) = pos .Bk ∧ {k : ℤ | covers V k} = Set.Icc 0 5) ↔
        V = pt (7 / 2) width)) ∧
    [facet c 0, facet c 1, facet c 2, facet c 3, facet c 4, facet c 5] =
      [facetFront, facetRight, facetBase, facetLeft, facetFront, facetRight] ∧
    ∠ (pt (7 / 2) width) (pt 0 0) (pt 1 0) = arctan (√3 / 7) ∧
    13.8 < arctan (√3 / 7) * 180 / π ∧ arctan (√3 / 7) * 180 / π < 14 := by
  obtain ⟨s1, s2⟩ := sqrt3_bounds
  refine ⟨fun V hA hV => ?_, ?_, ?_, ?_, ?_⟩
  · have hV1 := vertex_height hA hV
    have hVeq : V = pt (V 0) width := by
      ext i; fin_cases i <;> simp [hV1]
    constructor
    · rintro ⟨hw, hcov⟩
      obtain ⟨hx, hup⟩ := wrap_at_vertex c hc (V 0) .Bk (Or.inr rfl) hw
      set m := ⌊V 0 - 1 / 2⌋
      have hodd : ¬ Even m := by
        intro he; rw [up_eq c hc] at hup; simp only [he, ↓reduceIte] at hup
        exact absurd hup (by decide)
      have h5 : covers V 5 := by
        have : (5 : ℤ) ∈ {k : ℤ | covers V k} := by rw [hcov]; simp
        exact this
      have h6 : ¬ covers V 6 := by
        intro h
        have : (6 : ℤ) ∈ {k : ℤ | covers V k} := h
        rw [hcov] at this; simp at this
      have r5 := reach_of_covers hV1 2 (by norm_num) (by simpa using h5)
      have r6 : V 0 ≤ 13 / 3 := by
        by_contra hgt'
        have hgt := lt_of_not_ge hgt'
        exact h6 (by rw [hVeq]; exact covers_six hgt)
      have hm1 : (2 : ℝ) < m := by push_cast at r5; linarith
      have hm2 : (m : ℝ) < 4 := by linarith
      have hm1' : 2 < m := by exact_mod_cast hm1
      have hm2' : m < 4 := by exact_mod_cast hm2
      have hm : m = 3 := by
        rcases Int.even_or_odd m with h | h
        · exact absurd h hodd
        · obtain ⟨r, hr⟩ := h; omega
      rw [hVeq, hx, hm]; norm_num
    · rintro rfl
      refine ⟨?_, ?_⟩
      · have h := locus c hc 3 0 le_rfl one_pos
        rw [show ((3 : ℤ) : ℝ) + 1 / 2 + 0 = 7 / 2 by norm_num] at h
        simp only [show ¬ Even (3 : ℤ) by decide, ↓reduceIte, AffineMap.lineMap_apply_zero] at h
        simpa using h
      · ext k
        rw [Set.mem_Icc]
        change covers _ k ↔ _
        constructor
        · intro h
          by_contra hk
          rcases not_and_or.mp hk with hk | hk
          · exact not_covers_neg (by simp) (by norm_num) (by omega) h
          · exact not_covers_far (by simp) 3 (by norm_num) (by norm_num)
              (by omega) h
        · rintro ⟨hk0, hk5⟩
          interval_cases k
          · exact wit (27 / 40 : ℝ) (3 / 20 : ℝ) (7 / 10 : ℝ) (3 / 20 : ℝ) (3 / 20 : ℝ)
              (1 / 4 : ℝ) (3 / 5 : ℝ) (3 / 20 : ℝ)
          · exact wit (1 : ℝ) (1 / 4 : ℝ) (5 / 8 : ℝ) (1 / 8 : ℝ) (1 / 4 : ℝ) (3 / 4 : ℝ)
              (1 / 8 : ℝ) (1 / 8 : ℝ)
          · exact wit (59 / 40 : ℝ) (13 / 40 : ℝ) (27 / 80 : ℝ) (27 / 80 : ℝ) (13 / 40 : ℝ)
              (29 / 80 : ℝ) (5 / 16 : ℝ) (13 / 40 : ℝ)
          · exact wit (2 : ℝ) (1 / 2 : ℝ) (1 / 4 : ℝ) (1 / 4 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ)
              (1 / 4 : ℝ) (1 / 4 : ℝ)
          · exact wit (99 / 40 : ℝ) (13 / 20 : ℝ) (3 / 20 : ℝ) (1 / 5 : ℝ) (13 / 20 : ℝ)
              (1 / 5 : ℝ) (3 / 20 : ℝ) (13 / 20 : ℝ)
          · exact wit (11 / 4 : ℝ) (3 / 4 : ℝ) (1 / 8 : ℝ) (1 / 8 : ℝ) (3 / 4 : ℝ) (1 / 4 : ℝ)
              (1 / 8 : ℝ) (5 / 8 : ℝ)
  · simp [facet, lo_eq c hc, up_eq c hc, facetFront, facetRight, facetBase, facetLeft,
      Int.even_iff]
    decide
  · rw [angle_eq]
    simp only [pt_zero, pt_one]
    rw [arccos_eq_arctan (x := 7 / 2) (y := width) (by norm_num) (by unfold width; positivity)]
    congr 1; unfold width; ring
  · exact deg_lt_arctan (lo := 0.24084) (hi := 0.24086) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by positivity)
      (by nlinarith)
  · exact arctan_lt_deg (lo := 0.24433) (hi := 0.24435) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by positivity)
      (by nlinarith)

end PillowProblems.P70
