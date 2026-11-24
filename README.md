# Lewis Carroll's *Pillow-Problems* in Lean 4

All 72 problems of Lewis Carroll's *Curiosa Mathematica, Part II: Pillow-Problems thought out during wakeful hours* (4th edition, 1895; public domain, [Project Gutenberg #79080](https://www.gutenberg.org/ebooks/79080)), formalized in Lean 4 and mathlib with complete proofs. The repo also has a **benchmark** copy of every statement, with the proofs removed.

The problems are what Carroll worked out in his head at night: algebra, number theory, chances (probability), plane and solid geometry and trigonometry. Each file quotes Carroll's question and answer, states the problem in Lean, and proves his answer, or the right answer where his is wrong.

## Status

| Status | Problems |
|---|---|
| proved | 46 |
| proved (Carroll's reading): the question is ambiguous or ill-posed, so the formalization follows how his solution reads it | 15 |
| proved (corrected): Carroll's answer is wrong, and the correct one is proved | 11 |
| **total** | **72**, with no `sorry` |

- Every declaration depends only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`, checked by `scripts/AxiomsAudit.lean`.
- The per-problem map is in [docs/PROBLEMS.md](docs/PROBLEMS.md).

**Some of Carroll's errors** (full list with explanations in [docs/FAITHFULNESS.md](docs/FAITHFULNESS.md)):
- **No. 41:** the "seven-twelfths" should be one-half. His prior is the one for "a particular counter is white", not "at least one is white". Both are proved.
- **No. 61:** a claim about sums of three squares is false. Counterexample (1, 4, 13), checked by `decide`.
- **No. 10:** a third solution his answer misses: a double florin and two threepenny bits.
- **No. 72:** his famous paradox ("ascertain the colours without looking"). Every chance he computes is proved correct, and so is the fact that his conclusion does not follow.
- **Nos. 45 and 70:** numerical slips: a wrong 7th decimal place, and wrong degree values for correct angles.

## Benchmark

`Benchmark/PNN.lean` contains each problem's definitions and theorem statements, character for character as in the reference solutions, with every proof replaced by `sorry`.

- It has 72 problems and 196 theorems, for evaluating automated or human provers.
- It is generated from the solutions by `scripts/make_benchmark.py`, and CI checks that it is up to date and compiles.

```lean
/-- **Problem 5.** After a white counter has been drawn, the chance of drawing a white counter
is two-thirds. -/
theorem problem5 : condChance (fun _ : Outcome => (1 : ℚ)) nextWhite drawnWhite = 2 / 3 := by
  sorry
```

## Reading a problem

```lean
/-!
# Problem 5 (Algebra: Chances)

**Question.** *(dated 8/9/87)*

> A bag contains one counter, known to be either white or black. A white counter is put in,
> the bag shaken, and a counter drawn out, which proves to be white. What is now the chance
> of drawing a white counter?

**Answer.**

> Two-thirds.

**Lean reading.** How the problem is modelled, what Carroll leaves tacit, and any departure.

**Status.** proved
-/
```

The main theorem is `problemN`, with `problemN_a`, `problemN_b`, … for problems that have several parts. Shared conventions are in `PillowProblems/Basic.lean`:
- the Euclidean plane;
- triangle areas;
- chances in finite models;
- how "construct" and "find" problems are read.

## Layout

```
PillowProblems.lean        root: imports every problem
PillowProblems/Basic.lean  shared conventions (Plane, Space, triArea, chance, …)
PillowProblems/P01.lean … P72.lean   one file per problem
Benchmark/                 the same statements with `sorry` proofs (generated)
data/problems.json         Carroll's questions, answers and full solutions, extracted from the Gutenberg source
docs/PROBLEMS.md           generated problem map
docs/FAITHFULNESS.md       conventions, Carroll's errors, readings of ambiguous problems
docs/SOURCES.md            bibliography and copyright
scripts/                   extraction, skeletons, problem map, benchmark generator, axiom audit, checker
```

## Building

Lean v4.36.0 and mathlib v4.36.0 are pinned in `lean-toolchain` and `lakefile.toml`.

```sh
lake exe cache get                        # download prebuilt mathlib
lake build                                # all 72 problems
lake build Benchmark                      # the sorry'd statements
lake env lean scripts/AxiomsAudit.lean    # axiom audit
python3 scripts/problem_table.py --check  # regenerate docs/PROBLEMS.md and check statuses
```

**Memory:** every problem imports all of mathlib, and `lake build` builds as many files at once as the machine has CPU threads. On a machine with many cores and less than about 32 GB of RAM, either build a few modules at a time (`lake build PillowProblems.P01 PillowProblems.P02 PillowProblems.P03`, …) or check a single file with `python3 scripts/check.py PillowProblems/P05.lean`.

On Windows, keep the repo at a short path such as `D:\Projects\pillow-problems-lean`, because of the 260-character path limit.

## Contributing

Lean checks the proofs, not whether each statement says what Carroll asked. If you find a misreading, please open an issue.

## License

- Lean code and documentation: [Apache License 2.0](LICENSE).
- Quotations from the 1895 text are in the public domain; see [docs/SOURCES.md](docs/SOURCES.md).
