# Exposition conventions (mirroring the Milnor *Topology from the Differentiable Viewpoint* project)

Source: J. Milnor, *Morse Theory* (Princeton, 1963), scanned as `../../MorseTheory.pdf`.
Page images: `pages/p-NN.png`, two book pages per image. Book page `b` is on image
`p-NN` with `NN ≈ floor(b/2) + 3` (check the printed page number; it can drift by one).
Exemplar chapters in the finished Milnor project (read at least one before writing):
`/Volumes/tara-mini/math conversion /Milnor/Exposition/Chapter4.md` and `Chapter6.md`
(note the trailing space in `math conversion `).

## The companion volume

The finished Milnor TDV exposition (`../Exposition/`, at the root of this repository,
`github.com/skydancerosel/math_faithful`) is cited as the *companion volume*. Results proved there (inverse function theorem, regular values, Sard and Brown, manifolds
with boundary, degree, Poincaré–Hopf, the index of a non-degenerate zero, the ε-neighbourhood
theorem, Hadamard's lemma, the Hopf theorem, framed cobordism) are stated precisely and cited as
"proved in Chapter k of the companion volume", not re-proved. Its Lean formalization is a Lake
dependency of this project, so the same results are available to the Lean files.

## Chapter plan

| File | Milnor sections | Book pages |
|---|---|---|
| Chapter1.md | §1 Introduction, §2 Definitions and lemmas (Morse lemma) | 1–12 |
| Chapter2.md | §3 Homotopy type in terms of critical values | 12–24 |
| Chapter3.md | §4 Examples, §5 The Morse inequalities | 25–32 |
| Chapter4.md | §6 Manifolds in Euclidean space: existence of non-degenerate functions | 32–38 |
| Chapter5.md | §7 The Lefschetz theorem on hyperplane sections | 39–42 |
| Chapter6.md | §8 Covariant differentiation, §9 The curvature tensor | 43–54 |
| Chapter7.md | §10 Geodesics and completeness | 55–66 |
| Chapter8.md | §11 Path space, §12 Energy, §13 Hessian of the energy | 67–76 |
| Chapter9.md | §14 Jacobi fields, §15 The index theorem | 77–87 |
| Chapter10.md | §16 Finite-dimensional approximation, §17 Topology of the full path space | 88–97 |
| Chapter11.md | §18 Existence of non-conjugate points, §19 Topology and curvature | 98–108 |
| Chapter12.md | §20 Symmetric spaces, §21 Lie groups as symmetric spaces | 109–117 |
| Chapter13.md | §22 Whole manifolds of minimal geodesics | 118–123 |
| Chapter14.md | §23 Bott periodicity for the unitary group | 124–132 |
| Chapter15.md | §24 Periodicity for the orthogonal group | 133–148 |
| Appendix.md | Appendix: the homotopy type of a monotone union | 149–153 |

## Shape of every chapter

1. Title line `# Chapter N. <short title>: <subtitle>` and an italic line
   `*Milnor, "Morse Theory", §k–§l, rewritten for a first-year graduate student who wants to know what
   the theorem is for. Every proof is complete.*`, then `---`.
2. `## 0. <a physical or concrete question>`: opens with a question a scientist or engineer could ask
   (mountain passes and lakes, a molecule's energy landscape, light rays and focal points, a
   spinning top, a robot's configuration space...), explains why this chapter answers it, and
   announces the application at the end.
3. Numbered sections `## 1. <topic> (Milnor pp. a–b)`, following Milnor's order, giving **every**
   definition, lemma and theorem of his sections with **complete proofs**. Where Milnor writes "it is
   easy to see", "clearly", "one verifies", supply the argument. Where he relies on a fact outside
   the book (ODE existence and smooth dependence, partitions of unity, Sard, cellular homology,
   Hopf–Rinow pieces, Lie theory...), state it precisely and say where it is proved; prove it if it
   is short.
   Statements in bold: `**Lemma 2.2 (Morse lemma).**`, keeping Milnor's numbering where he has one.
   Proofs start with `*Proof.*` and end with `$\square$`.
   Remarks on gaps in Milnor's text go in blockquotes starting `> **Milnor's text skips…**` or
   `> **A hidden hypothesis.**`.
4. Exactly one figure: a subsection `### An interactive look at …` describing what the reader sees
   and what to drag, followed by `<div id="<name>-figure"></div>` and the line
   `*(In the printed version this figure is a still image; the interactive version is in the web
   edition.)*` followed, on its own line, by `![](figN-<name>.png)`.
   Deliver `figN-<name>.py` (matplotlib, writes `figN-<name>.png`, 150 dpi, ≤ 7 inches wide, no
   seaborn) and `figN-<name>.js` (plain JavaScript, no libraries, that finds the div by id and draws
   an interactive canvas or SVG with sliders; must work at 360 px width; colours via CSS variables
   `--fg`, `--bg`, `--accent`, `--muted` with fallbacks).
5. `## k. Application: …`: a real application worked through with numbers or a concrete
   computation (e.g. counting conformers of a molecule, saddle points in a mountain range, the
   number of geodesics between two points on a sphere or a torus, focal points of a lens, the
   stability of a soap film, the energy landscape of a pendulum or a double pendulum, K-theory and
   vector bundles over spheres for the Bott chapters...). Be honest: no invented data; if
   quoting a physical fact, it must be standard.
6. `## k+1. Summary of what was silently assumed, now made explicit`: a table
   `| Where | Milnor says | What is actually needed |` with page numbers.
7. Last paragraph: `**Checked by machine.** Not yet: this chapter has not been formalized.` (to be
   updated once Lean files exist).

## Mathematics formatting

Pandoc Markdown with TeX math: `$…$` inline, `$$…$$` display (no `\begin{align}` outside `$$`;
use `\begin{aligned}` inside `$$`). No raw LaTeX environments outside math, no HTML except the
figure div. Use `\mathbb{R}`, `M^a = f^{-1}(-\infty, a]`, `\lambda` for the index, `E_{**}` for the
Hessian of the energy, `\Omega` for path spaces, as Milnor does. British or American spelling, but
consistent within a chapter (Milnor project used "neighbourhood").

Length: about 5,000–9,000 words per chapter (the reviewed chapters run 6,000–9,000 by `wc -w`, math included). Tone: direct, precise, no
filler, no exclamation marks, no emojis.
