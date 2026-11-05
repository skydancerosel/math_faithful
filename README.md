# Faithful formalization: Milnor's two books in Lean 4

Two of John Milnor's books, formalized completely against Mathlib, with a human-readable layer on
top that shows, statement by statement, that the formal results say what the book says.

| | *Topology from the Differentiable Viewpoint* | *Morse Theory* |
|---|---|---|
| Folder | the repository root (`Milnor/`) | [`Morse/`](Morse/README.md) |
| Lean | 177 files, 63,000 lines | 238 files, 98,000 lines |
| Theorems with `#print axioms` | 175 (`Milnor/Test.lean`) | 1,498 (`Morse/Morse/Test.lean`) |
| Coverage | every numbered result, the Appendix and all seventeen problems; one statement not formalized here (that the Poincaré–Hopf integer is the Euler characteristic, which needs homology: proved in the Morse project, which builds it) | every chapter and the Appendix; the remaining gaps are listed in [`Morse/README.md`](Morse/README.md) |

No `sorry` anywhere. Every theorem depends only on the three standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

Toolchain: Lean `v4.33.1`, Mathlib `v4.33.1`.

## Why "faithful"

A green `lake build` shows that the formal statements are proved. It does not show that they are
the statements of the book. Hypotheses get added, definitions differ from the textbook ones,
and a theorem gets proved in a special case. This project makes that gap visible and checks it.
Each book has four reports:

| Report | Question it answers | Milnor | Morse |
|---|---|---|---|
| **Verified edition** | *What* is proved: every machine-checked result in plain mathematical language, with all its hypotheses, and a numbered sign-off list for a mathematician who does not read Lean | [`Exposition/Verification.md`](Exposition/Verification.md) (110 items) | [`Morse/Exposition/Verification.md`](Morse/Exposition/Verification.md) (396 items) |
| **Proof by proof** | *How* it is proved: the formal proofs retold as mathematics, with a trace tag `⟦File · declaration⟧` on every step, resolved mechanically against the sources | [`Exposition/ProofByProof.md`](Exposition/ProofByProof.md) (142 pp., 1,810 tags) | [`Morse/Exposition/ProofByProof.md`](Morse/Exposition/ProofByProof.md) (452 pp., 7,442 tags) |
| **Comparison** | *How it differs from the book*: each result of the book beside the formal statement, with the difference labelled (as in the book, hypotheses explicit, stronger, narrower, restated, value differs, not formalized) | [`Exposition/Comparison.md`](Exposition/Comparison.md) (111 rows) | `Morse/Exposition/cmp/*.json` (452 items) |
| **Round-trip audit** | *Is the comparison right*: Milnor's statements formalized blind, by a model that never saw the project's theorems, then proved equivalent (or not) to the project's statements in Lean; definitions checked against blind textbook definitions | — | [`Morse/RoundTrip/REPORT.md`](Morse/RoundTrip/REPORT.md) (348 statements, 116 definitions) |

Each book also has an expanded exposition (`Exposition/Chapter*.md`, with PDFs): Milnor's proofs
with every step filled in, written for advanced undergraduates. *Morse Theory* also has
[*the Shortest Path*](Morse/Exposition/ShortestPath.md): the main theorems and exactly the results
their formal proofs use, read off the Lean dependency graph.

## What the formalization found in the books

- *Topology from the Differentiable Viewpoint*, §8 Problem 15: with the book's conventions taken
  literally, the Hopf fibration has Hopf invariant −1, not +1. This was checked by hand,
  numerically, and in Lean (`Milnor/Chapter8/HopfSign.lean`).
- *Topology from the Differentiable Viewpoint*, p. 50: the theorem for closed non-orientable
  manifolds, which Milnor states without proof, is proved in full: two maps `M → Sᵐ` are homotopic
  iff they have the same degree mod 2 (`Milnor/Chapter7/HopfMod2.lean`). Proving it required
  orientability theory and the classification of one-manifolds, neither of which Mathlib had.
- *Morse Theory*, p. 94: as we read its definition, the map `h` in Milnor's proof of Theorem 17.1
  is not continuous for his metric; an explicit counterexample is machine-checked
  (`Morse.milnor_h_not_continuous`). Theorem 17.1 itself holds and is proved by a modified
  argument (`Morse.theorem_17_1`).
- *Morse Theory*: hidden hypotheses, among them `a` not a critical value in Theorem 16.3, and
  Hausdorffness and second countability throughout. There are also possible misprints, for example the critical set in example (d) on p. 9, which the
  text calls the `x`-axis, is the `y`-axis. The full list, with what was confirmed or withdrawn on review, is
  [`Morse/Exposition/Findings.md`](Morse/Exposition/Findings.md).
- In both books: every hypothesis Milnor uses silently is made explicit and labelled in the
  comparison.

## Infrastructure that Mathlib does not have, built here

- the inverse function theorem on manifolds;
- Sard's theorem;
- submanifolds and manifolds with boundary by slice charts;
- orientations, the Brouwer degree and Poincaré–Hopf;
- framed cobordism and the Pontryagin construction;
- the classification of one-manifolds;
- smooth dependence of flows on initial conditions;
- relative singular homology with excision and Mayer–Vietoris;
- homotopy groups under cell attachment;
- the long exact homotopy sequence of a bundle;
- the Levi-Civita connection, geodesics and Hopf–Rinow for submanifolds;
- the Morse index theorem;
- Bott periodicity.

## Checking it

```bash
lake exe cache get                      # Mathlib, once
lake build                              # the Milnor project
lake env lean Milnor/Test.lean          # axioms of the 175 main theorems

cd Morse                                # Morse depends on the root by a Lake path dependency
lake exe cache get
lake build
lake env lean -DmaxSynthPendingDepth=3 Morse/Test.lean   # axioms of the 1,498 theorems
```

The reports are checked mechanically against the sources:

- `python3 Exposition/check_trace.py Exposition/ProofByProof.md` reports no unresolved trace tags;
- `python3 Morse/Exposition/check_names.py` reports that every Lean name cited in a report exists.

## Status

- **Formalization:** complete for *Topology from the Differentiable Viewpoint*. For *Morse
  Theory*, every chapter and the Appendix are formalized. A short list of
  remaining items is in [`Morse/README.md`](Morse/README.md#status), for example real Bott
  periodicity as group isomorphisms (it is proved as bijections) and integral homology of `ℂPⁿ`.
- **Reports:** complete for both books.
- **Sign-off:** the verified editions are written so that a mathematician who does not read Lean
  can check each statement. That review is in progress, on the sign-off pages
  `Exposition/milnor-signoff.html` and `Morse/Exposition/morse-signoff.html` (each item with the
  book's statement beside the verified one, a tick box and notes; built by
  `Morse/Exposition/build_signoff.py`), whose state is exported to `Exposition/SIGNOFF.md` and
  `Morse/Exposition/SIGNOFF.md`.

## Next: compactness

[`Exposition/Roadmap.md`](Exposition/Roadmap.md) proposes formalizing the compactness theorems of
geometric analysis: bubbling, concentration-compactness, critical points at infinity, and Gromov
and SFT compactness. It sets an order of attack. The two books here are the substrate that
programme needs: Sard, degree theory, Morse theory and the path-space machinery. The same faithful
layer (verified edition, proof by proof, comparison, audit) is what would make such a
formalization checkable by the analysts who use these theorems.

Part I of Hofer–Wysocki–Zehnder's *Polyfold and Fredholm Theory*, formalized with the same layer,
was begun in this repository as `Polyfold/` and has its own repository since 5 November 2026:
[`polyfold_faithful`](https://github.com/skydancerosel/polyfold_faithful).

## Authorship, provenance and license

**Author:** Yongzhong Xu, Kinglake Research LLC. Cite it with the `CITATION.cff` at the root.

**How it was made.** The Lean, the expositions, the reports and the audit were written by Claude
(Anthropic's models, in Claude Code sessions) under the author's direction: the author chose the
books, set the standard of faithfulness and the plan, reviewed the findings against the printed
books, and is signing off the verified editions (`Exposition/SIGNOFF.md`,
`Morse/Exposition/SIGNOFF.md`). The development history, which is not published, records the
model that wrote each commit. Nothing here
rests on the model's word: every theorem is checked by Lean against Mathlib, with its axioms printed
(`Test.lean`), every trace tag of the proof-by-proof reports is resolved against the sources by a
script, and the comparison's labels were tested in Lean by the round-trip audit, which found that in
most cases the formal statement and Milnor's differ in scope in ways a label does not capture
(`Morse/RoundTrip/REPORT.md`).

**License.** The Lean code is under the [Apache License 2.0](LICENSE), the license of Mathlib. The
prose (the expositions, the verified editions, the proof-by-proof reports, the comparisons, the
audit reports and the figures) is under [CC BY 4.0](LICENSE-CC-BY-4.0). Milnor's two books remain
the copyright of their publishers: the expositions paraphrase them, and the page images used for
checking are not distributed.

## Layout

| Path | What |
|---|---|
| `Milnor/ChapterN/`, `Milnor/Appendix/` | Lean sources of *Topology from the Differentiable Viewpoint* |
| `Milnor/Test.lean` | `#print axioms` for the main theorems |
| `Exposition/` | exposition chapters, verified edition, proof by proof, comparison (Markdown, PDF, HTML) and their build and check scripts |
| `Morse/` | the *Morse Theory* project; see [`Morse/README.md`](Morse/README.md) |
| `DocstringErrata.md`, `Leftovers.md` | docstring corrections; the items closed after the first comparison |
| `HISTORY.md` | the dated development log of the Milnor project, with its design decisions |
