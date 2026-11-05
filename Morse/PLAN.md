# Plan and status

The same pipeline as the Milnor project (`github.com/skydancerosel/math_faithful`). Status as of
2026-10-04: 238 Lean files, about 98,000 lines, 1,498 theorems checked in `Morse/Test.lean`, all on
the three standard axioms, no `sorry`.

## 1. Exposition

| Step | Status |
|---|---|
| 15 chapters + Appendix (`Exposition/Chapter*.md`): physical opening, complete proofs, one figure, one application, silent assumptions | done; every chapter independently reviewed against the scan |
| PDFs (`build.py`) and the single-page web edition (`build_book.py`) | done; web edition published privately (https://claude.ai/artifact/Nap97EqZwj1ZjHek4DG4zW, version 8, republished 2026-10-05 with the "Checked by machine" paragraphs of Chapters 3, 5 and 10–15 rewritten; PDFs rebuilt) |
| `Findings.md`: gaps, hidden hypotheses and slips, each confirmed, withdrawn, or marked *(scan?)* | ongoing; headline: Milnor's proof of 17.1 contains a false claim (machine-checked) |

## 2. Formalization (submanifolds of `ℝᴷ`; compact abstract manifolds via Whitney)

| Part | Content | Status |
|---|---|---|
| I §§1–2 | Morse lemma, Hessian and index (local and on manifolds), flows (Lemma 2.4), the torus | done |
| I §3 | Theorems 3.1, 3.2, 3.5 (as iterated cell attachments), Lemmas 3.6–3.7, Remarks 3.3–3.4 | done |
| I §§4–5 | Reeb; Morse inequalities and `χ` in singular homology over any field; Corollary 5.4 | done, including `ℂPⁿ` (Milnor's `Σ c_j|z_j|²`, Proposition B, Theorem 3.5 cells, homology over any field: `Morse/Chapter3/ProjectiveSpace.lean`, `ProjectiveMorse.lean`) (integral homology, non-compact manifolds not done) |
| I §6 | focal points, Theorem 6.6, Corollaries 6.7–6.8, Lemma 6.9; compact abstract manifolds | done |
| I §7 | the index bound behind Lefschetz; Theorem 7.2 (closed complex submanifolds: countable cell complex, cells of dim `≤ k`); Theorem 7.1 over a field | done, including Corollary 7.3 over a field with pure dimension and Hypothesis (N) (`Morse/Chapter5/HyperplaneSection.lean`, `ProjectiveSection.lean`) and Theorem 7.4 (`Morse/Chapter5/LefschetzHomotopy.lean`) (7.1 over `ℤ` not done) |
| II §§8–10 | Levi-Civita, parallel transport, curvature, geodesics, exp, Gauss lemma, 10.4, Hopf–Rinow | done |
| III §§11–15 | energy, variation formulas, Jacobi fields, the Morse index theorem | done |
| III §§16–17 | broken geodesics, Theorem 16.3, Theorem 17.1 (repaired proof), Theorem 17.3, the path space of `Sⁿ`; Milnor's `h` proved discontinuous | done (Corollary 17.2 for closed `N`, via 17.3, 18.2 and Lemma 17.D; loop-space form of 17.4 and its homology) |
| III §§18–19 | non-conjugate points, Cartan–Hadamard (19.2), 19.3 (first half), Myers, 19.6 for non-conjugate endpoints | done (19.6 for all endpoints; π₁ torsion-free not done) |
| Appendix | telescopes, Theorem A (in general, without closedness), cell towers | done (Example 2 needs Whitehead) |
| IV §§20–24 | algebra: bi-invariant curvature, index counts for `SU(2m)`, Clifford modules, Lemma 24.8 | done |
| IV §§20–21 | `U(n)`, `SU(n)`, `O(n)` as submanifolds; geodesics, curvature, conjugate points; the `SU(2m)` index formula through the index theorem; Lemma 23.1 (homotopy equivalence; homeomorphism after the separation quotient) | done |
| IV §22 | Theorem 22.1, Corollaries 22.2 (also as groups) and 22.3 (Freudenthal, also as groups and the onto half) | done |
| IV §§23–24 | Theorem 23.3, unitary periodicity (`i ≤ 2m − 2`, also as groups), Theorem 23.5 (`≅ ℤ` as groups); §24 at finite stages: Lemma 24.4, the index bounds for all `k ≤ 7`, Theorem 22.1 componentwise, winding components for `k = 2, 6`, `Ω₈(16r) ≅ O(r)`, the eight-step chain, Theorem 24.7 (`πᵢO(n) ≅ πᵢ₊₈O(n′)`, `i + 2 ≤ n`, `i + 10 ≤ n′`) | done (bijections of sets for §24; the limit spaces `Ω_k`, the table of `πᵢO` and group isomorphisms for real periodicity not done) |

## 3. Infrastructure missing from Mathlib, built here

| Piece | Status |
|---|---|
| Smooth dependence of flows on initial conditions | done (`Morse/Flow/`) |
| Relative singular homology, exact sequences of pairs and triples, homotopy invariance, Eilenberg–Steenrod pretheory | done (`Morse/Homology/`) |
| Barycentric subdivision, small simplices, excision, Mayer–Vietoris | done |
| Homology of disks, spheres and cell attachments | done |
| Homotopy groups under cell attachment, the push-off lemma, loop-space shift | done (`Morse/Homotopy/`) |
| Homotopy lifting for locally trivial bundles and the long exact homotopy sequence; `πᵢ(Sⁿ) = 0` for `i < n` | done |
| The bundles of Bott periodicity: `U(m+1) → S^{2m+1}`, Stiefel → Grassmannian (`πᵢ(G_m(ℂ^{2m})) ≅ πᵢ₋₁(U(m))`), orthogonal analogues; the Grassmannian as `Stiefel/U(m)` and as the space of `m`-dimensional subspaces | done |
| Whitehead's theorem, cellular approximation | not needed so far (only for the literal "CW complex" wording) |
| Nash embedding | not planned (every space the book applies the theory to is a submanifold of a matrix space) |

## 4. Reports

| Report | Status |
|---|---|
| `Exposition/Verification.md` (verified edition) | 16 sections, 396 sign-off items, every cited name resolved (2,092); Chapter 13 (§22) added, Chapters 3, 5, 10, 11, 12, 14, 15 extended with new V-items after the existing ones (Chapter 15: V15.21–V15.46 for the geometry and topology of §24; V3.41–V3.43 for $\mathbb CP^n$; V5.13–V5.19 for Theorems 7.1, 7.2, 7.4 and Corollary 7.3; V10.28–V10.30 for Corollary 17.2 and the loop-space form of 17.4); PDF rebuilt |
| `DocstringErrata.md` | maintained; the open rows of 2026-10-03 are fixed (cleanup pass of 2026-10-04, with the page citations of §§23–24 checked against the scan); no open row |
| `Exposition/ProofByProof.md` (formal proofs retold as mathematics) | Parts 0–XIII done: 266,531 words, 452 pages (local build, Palatino), 7,442 trace tags naming 5,665 declarations, 0 unresolved; Part XIII covers §§20–24 and late additions to Parts III, V, IX, X; web edition published privately (https://claude.ai/artifact/BcXexY9ZNAxJoesrskHxDh, version 2, republished 2026-10-05) |
| `Exposition/Comparison.md` and its web edition (Milnor beside Lean) | Chapters 1–15 and the Appendix done: 452 items, 61 of them not formalized (`cmp/ch12-15.json`: 110 items for §§20–24, of which 46 for §24; 13 rows for the late additions to Chapters 3, 5, 10); published privately (https://claude.ai/artifact/2gCU32LTuUBs2kSzQgSJBd, version 2, republished 2026-10-05) |
| Sign-off of the verified edition by a mathematician | pending |
| Push to GitHub | done: the folder `Morse/` of `github.com/skydancerosel/math_faithful` (`main`); Milnor is a path dependency on the repository root |


## 5. Audit (round trip and definitions; `RoundTrip/`)

| Layer | Status |
|---|---|
| 1. Round trip: blind Lean statements of Milnor, implications with the formal statements, compared with the comparison's labels; the definitions against textbook ones; failure labels | **Done** (2026-10-05): 348 items (layer 1, with the embedded special case for §§8–19), 116 definitions (layer 2, all agree), labels (layer 3); `RoundTrip/REPORT.md` |
| 2. Definition audit: the ~120 project definitions under the headline theorems, each round-tripped against a textbook definition | **Done** (2026-10-05): all 116 agree (`RoundTrip/L2/`) |
| 3. Failure taxonomy as automatic labels | **Done** (2026-10-05): `RoundTrip/layer3_labels.json` |
