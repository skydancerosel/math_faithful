# How to write a part of "Morse Theory, proof by proof"

*Morse Theory, proof by proof* retells the **formal proofs** of this project as mathematics: every
definition as the formalization actually makes it, every proof step by step as the Lean proof
goes, in ordinary mathematical language, with a **trace tag** on every step of substance. It is the
detailed companion of the verified edition: where `Verification.md` says *what* is proved, this
book says *how*. The model is the Milnor project's `ProofByProof.md`
(`../Exposition/ProofByProof.md`) — read its Prologue, Part 0 (to see how
definitions are stated) and one part (e.g. its Part I) before writing.

## The trace tag

`⟦Chapter2/Regular · theorem_3_1⟧` names a file and a declaration in it that proves (or defines)
what the sentence says. The path is relative to `Morse/` (this project), or begins with
`Milnor/` for the Milnor dependency (`../Milnor/…`) or `Mathlib/` for Mathlib.
The declaration is written as it is declared in the file (the name after `theorem`/`def`/…,
possibly qualified by an enclosing namespace that the file opens, e.g. `BrokenSetup.theorem_16_3`
if needed). Tag generously: every definition, every lemma used, every step of substance. A
paragraph of proof typically carries several tags. Check every tag mechanically:
`python3 Exposition/check_trace.py Exposition/pbp/<your file>.md` from the project root must report
0 unresolved.

## Shape of a part

```
## Part N. Title (Milnor §a–§b)

One or two paragraphs: what this part proves, in which setting, and how the formal route differs
from Milnor's (if it does).

### N.1 Subsection title

Definitions first, as the formalization makes them, each tagged. Then each result: its statement in
words with every hypothesis of the formal statement, then its proof, step by step as the Lean proof
goes — the construction, the key estimates, the lemmas invoked (tagged), the case distinctions, the
places where the formal proof needs something Milnor does not say (say so, and tag the lemma that
supplies it). Where the formal proof takes a different route from Milnor's, say so and explain why.
Explain everything: a reader who knows the mathematics but not Lean should be able to follow every
step and see where each fact comes from.

### N.2 …
```

- Number subsections `N.1`, `N.2`, … within your part; theorems keep Milnor's numbers (Theorem 3.1,
  Lemma 16.1, …).
- Math in `$…$` / `$$…$$` (pandoc Markdown); no Lean syntax in the prose except declaration names
  inside trace tags and, sparingly, in backticks.
- Refer to definitions of Part 0 as "(§0.k)", to other parts as "(Part N, §N.k)".
- Do not quote the book at length (it is under copyright); short phrases at most, with pages.
- Length: as long as it takes to explain every proof in full — typically 8,000–15,000 words per
  part. Detailed, not padded.

## Part 0's sections (for cross-references)

0.1 The companion foundations (manifolds, charts, smooth maps, the manifold derivative, slice
submanifolds — recalled from the Milnor project's Part 0, cited not repeated) · 0.2 Critical points,
the Hessian, nullity and index, Morse functions · 0.3 Submanifolds of a Euclidean space: tangent
spaces, the tangent projection, the induced metric · 0.4 Sublevel sets, strong deformation retracts,
homotopy equivalences · 0.5 Cell attachments and cell complexes (finite and countable types) ·
0.6 Singular chains, homology, relative homology, Betti numbers · 0.7 Homotopy groups and induced
maps · 0.8 Paths, energy, the path spaces Ω and Ω*, Milnor's metric · 0.9 Geodesics, the exponential
map, Jacobi fields, conjugate points, the index form `E_**` · 0.10 Flows of vector fields.

## Parts and their sources

| File | Part | Lean sources |
|---|---|---|
| `pbp/part00.md` | Part 0. The formal definitions | definitions across `Morse/` |
| `pbp/part01.md` | Part I. Critical points and the lemma of Morse (§§1–2) | `Chapter1/`, `Flow/` |
| `pbp/part02.md` | Part II. Sublevel sets and attached cells (§3) | `Chapter2/` |
| `pbp/part03.md` | Part III. Reeb, the torus, the Euler number, focal points (§§4–6) | `Chapter3/{Reeb*,Torus*,EulerChar*}`, `Chapter4/` |
| `pbp/part04.md` | Part IV. Homology and the Morse inequalities (§5) | `Chapter3/Inequalities`, `Homology/` |
| `pbp/part05.md` | Part V. Lefschetz, connections and curvature (§§7–9) | `Chapter5/`, `Chapter6/` |
| `pbp/part06.md` | Part VI. Geodesics and completeness (§10) | `Chapter7/` |
| `pbp/part07.md` | Part VII. Energy, variations, Jacobi fields and the index theorem (§§11–15) | `Chapter8/`, `Chapter9/` |
| `pbp/part08.md` | Part VIII. Broken geodesics (§16) | `Chapter10/` (§16 files) |
| `pbp/part09.md` | Part IX. The full path space and the fundamental theorem (§17) | `Chapter10/` (§17 files, `MilnorH`) |
| `pbp/part10.md` | Part X. Non-conjugate points, topology and curvature (§§18–19) | `Chapter11/` |
| `pbp/part11.md` | Part XI. The Appendix: monotone unions | `Appendix/` |
| `pbp/part12.md` | Part XII. Homotopy groups, cells and fibre bundles | `Homotopy/` |
| `pbp/part13.md` | Part XIII. Lie groups, symmetric spaces and periodicity (§§20–24) | `Chapter12/`, `Chapter14/`, `Chapter15/` |
