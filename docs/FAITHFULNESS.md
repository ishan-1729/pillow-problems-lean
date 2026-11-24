# Faithfulness notes

Every problem file quotes Carroll's question, and his answer where he gives one separately. It then explains in a **Lean reading** paragraph how the question was modelled, which tacit assumptions were made explicit, and every departure from the text. This file collects the conventions that apply across problems and lists every place where the formalization disagrees with Carroll, or has to choose between readings of his text.

## Conventions (`PillowProblems/Basic.lean`)

| Carroll | Lean |
|---|---|
| a figure in the plane | points of `Plane := EuclideanSpace ℝ (Fin 2)`, so `dist` is Euclidean, not the sup metric of `ℝ × ℝ`; angles are mathlib's unoriented `∠` in radians |
| solids | `Space := EuclideanSpace ℝ (Fin 3)`; volumes by decomposition into tetrahedra |
| area of a triangle | `triArea A B C = |cross A B C| / 2` |
| "construct …" | the object Carroll's construction gives exists and has the property; uniqueness is proved where his answer determines the object |
| "find …" | Carroll's answer is *the* answer: usually an `↔`, or a characterization of all solutions, not just a check that his answer works |
| chances | probabilities in an explicit finite model of equally likely or weighted cases (`chance`, `uniformChance`), conditioning on what was observed. The model describes the experiment; the answer is never built into it |

Statements that need non-degeneracy hypotheses (a non-degenerate triangle, `sin A ≠ 0`, …) state them, and where the hypotheses could be inconsistent a `problemN_nonvacuous` example shows they can all hold.

## Status vocabulary

- **proved:** the question, read literally, is formalized and Carroll's answer is proved, at full strength where the question asks to "find" something.
- **proved (Carroll's reading):** the question is ambiguous or ill-posed as worded. The formalization follows the reading Carroll's own solution uses and says what the alternatives are. Often it also proves what happens under the other readings.
- **proved (corrected):** Carroll's answer, or part of it, is wrong. The file proves the correct statement, says exactly what is wrong, and usually proves Carroll's version under the assumptions it really needs.

## Where Carroll is wrong (11 problems)

| No. | What is wrong |
|---|---|
| 10 | With the British coins current when the problem was dated (8/90), a third set of coins also works: a double florin (struck 1887–90) and two threepenny bits. Carroll's "Either … or else …" misses it. |
| 13 | The area formula holds only when both angles at the centres are acute (his figure). Otherwise the tetragon is a non-convex "dart" and the formula gives minus the area. |
| 25 | The least possible fraction is `max(ε+α+λ−2, 0)`, not `ε+α+λ−2`, which is negative when `ε+α+λ < 2`. |
| 33 | The answer is right only if `x` is *half* of DE. With `DE = x`, as written, it is off by a factor of 4. |
| 41 | (1) should be **1/2**, not 7/12. "At least one white" is already implied by drawing two whites. Carroll's prior (1/8, 3/8, 3/8, 1/8) is the one for "one particular counter is known to be white"; `problem41_carroll` shows that under that information the chance is indeed 7/12. |
| 43 | Only the `+` root of Carroll's quadratic is admissible. The `−` root makes the angle obtuse. |
| 45 | `1 − 1/e = 0.6321205…`, not `.6321207`: a subtraction slip in the 7th decimal place. The question, read with continuous break points, also needs Carroll's discretization to have any content. |
| 61 | False as stated. His proof shows that the new *numbers* differ from the old ones, not that their *squares* do. Counterexample (1, 4, 13): the only other representations of 186 = 1 + 16 + 169 as a sum of three squares both share a square with it. The corrected theorem adds the conditions that are actually needed. |
| 69 | The ratio `2 cos θ` is wrong for θ > 90°, which his own limits allow; the correct ratio is `|2 cos θ|`. |
| 70 | (3) and (4): the angles `tan⁻¹(√3/5)` and `tan⁻¹(√3/7)` are right, but their degree values are about 19.11° and 13.90°, not 18.65° and 14.53° (interpolation errors in a sine table). |
| 72 | Carroll's deliberate paradox. Every chance he computes is proved correct, and the file proves that his conclusion ("one is black, the other white") does not follow: the bag is BW with chance only 1/2. |

## Where the text needs a reading (15 problems)

| No. | Reading chosen (Carroll's) and alternatives |
|---|---|
| 15 | "Figure" is read as a convex region. Carroll's proof needs the perimeter to be an oval; non-convex figures are not covered. |
| 20 | Assumes angle C acute and angle B not obtuse, as in his figure. Otherwise the perpendiculars miss the sides he uses. |
| 26 | Has no solution in an obtuse triangle (the circumcentre lies outside), which Carroll does not mention; the theorem assumes it. `problem26_literal` characterizes the literal reading. |
| 29 | "Squares" must be non-zero for the given numbers but may be 0 in the result. Both uniform readings make the claim false, and both counterexamples are proved. |
| 35 | Points on the closed sides may not exist; the construction is formalized on the side lines. |
| 37 | Ambiguous: the centres may lie on opposite sides of the common chord (Carroll's reading) or on the same side. Both are computed. His decimal "about ·044" is 0.0429…, because he used π ≈ 22/7. |
| 38 | "One proves to be red" is read as one *particular* counter seen red (Carroll: 49/72). "At least one red" gives 49/95, also proved. |
| 46 | "Inscribe" on the side lines. The degenerate angles δ = A and δ + A = π are excluded. |
| 47 | `k = 1` must be excluded from the fourth family; Carroll's solution notes this case. |
| 51 | The rectangle SD·SN is taken with sign. There are 0, 1 or 2 solutions. |
| 55 | Needs a ≠ b and b ≠ c; otherwise the locus is a line, not a circle. |
| 57 | Unique only under the tacit condition of his figure. Otherwise a second, negative-ratio figure exists. |
| 58 | Ill-posed: there is no uniform distribution on an infinite plane. Formalized in Carroll's reading (the longest side AB fixed and C uniform over the region where AB is longest), where the chance `3/(8 − 6√3/π)` is proved with mathlib's measure theory. Other readings give other answers. |
| 62 | The line must cut both arms of the angle. Otherwise there is no least triangle, since the infimum of the area is 0. |
| 64 | "Intercept" means the chord cut from the *line* of each side. Restricted to the side segments, Carroll's circle can fail, as the file's example shows. |

## How the statements were checked

1. Each subject group was formalized by one agent and then reviewed by a separate adversarial agent. The reviewer compared every statement with Carroll's question, answer and full solution in `data/problems.json`, and independently checked whether Carroll's answer is right. It looked for statements that are unfaithful, weaker or stronger than asked, vacuous, or that have the answer built into a definition, and fixed what it found.
2. `scripts/AxiomsAudit.lean` checks that every declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. It fails if any depends on `sorryAx`.
3. `scripts/problem_table.py --check` checks that every problem has a status and a `problemN` theorem, and that no "proved" file contains `sorry`.

Review is not proof of faithfulness. If you find a statement that does not say what Carroll asked, please open an issue.
