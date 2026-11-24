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

/-- The assumptions on a wrapping are consistent. -/
theorem problem70_nonvacuous : ∃ c : Wrapping, c.Starts := by
  sorry

/-! ### Part (1): the locus of the vertices -/

/-- The back edge `Tp Bk` does go down: `Tp` is the top of the tetrahedron, `Bk` is on the
ground. -/
theorem back_edge_descends : pos .Bk 2 < pos .Tp 2 := by
  sorry

/-- `pos` is a regular tetrahedron of edge `1`. -/
theorem pos_regular (u v : Vtx) (h : u ≠ v) : dist (pos u) (pos v) = 1 := by
  sorry

/-! ### Angles and areas -/

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
  sorry

/-! ### Parts (3), (4): covering -/

/-! ### Numerical bounds -/

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
  sorry

/-- The hypotheses of `problem70_2` are satisfiable: the triangle with vertex
`(√3 + 3/2, width)` is of the series and has left-hand base-angle `15°`. -/
theorem problem70_2_nonvacuous :
    ∃ V : Plane, triArea (pt 0 0) (pt 1 0) V = triArea (pt 0 0) (pt 1 0) (pt (1 / 2) width) ∧
      0 < V 1 ∧ ∠ V (pt 0 0) (pt 1 0) = π / 12 := by
  sorry

/-! ### Part (3) -/

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
  sorry

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
  sorry

end PillowProblems.P70
