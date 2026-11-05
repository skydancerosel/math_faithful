# How to write a chapter of "Morse Theory, the shortest path"

*Morse Theory, the shortest path* (`Exposition/ShortestPath.md`, assembled from
`Exposition/shortest/sNN.md`) proves the main theorems of Milnor's *Morse Theory* and nothing else.
What "nothing else" means is not a matter of taste: it is read off the Lean dependency graph. The
main theorems are the declarations listed in `TARGETS` of `Exposition/shortest/deps.py`
(the lemma of Morse; Theorems 3.1, 3.2, 3.5; the existence of Morse functions; the Morse
inequalities; the index theorem; Theorems 17.1 and 17.3; Theorem 22.1; Bott periodicity for the
unitary and the orthogonal group). A declaration of this project is *on the path* when the formal
proof of some main theorem uses it, directly or through other project declarations; 3,888 of the
6,287 project declarations are (and 147 of the 1,799 of the Milnor project). A result of the verified
edition is on the path when one of the declarations it cites is. Everything on the path is proved
or stated here; everything off it is left out.

The reader knows analysis in several variables, linear algebra, point-set topology and what a
smooth manifold is, at the level of a first graduate year. Everything else the path needs is either
proved in the text or stated precisely as an assumed fact (Chapter 0 lists the assumed facts:
Mathlib and the companion volume).

## Your inputs

- `Exposition/shortest/data/chNN.md`, **the list for your chapter**: the results on the path in
  dependency order (verified-edition number, title, the main theorems that need it, its on-path
  declarations, the declarations of the same result that are off the path, the on-path results it
  uses), the results of the same Milnor sections that are off the path, and every on-path Lean
  declaration described in your chapter, by file.
- `Exposition/pbp/partNN.md`, *Morse Theory, proof by proof*: the formal proofs retold as
  mathematics, with trace tags. Your main source: it says how each result is actually proved. Part
  0 (`part00.md`) has the definitions.
- `Exposition/verification/chNN.md`, the verified edition: the exact statement of each result with
  all its hypotheses (V-items).
- The Lean files themselves (`Morse/**/*.lean`): the ground truth for every statement.
- `Exposition/ChapterN.md`, the expanded exposition of Milnor: his proofs in full, for context.

## What to write

`Exposition/shortest/sNN.md` (NN = your chapter number, two digits), in this shape:

```
## 3. Morse functions exist

One paragraph: what the chapter proves, in which setting, which main theorems need it, and — in
one sentence — what of the corresponding Milnor sections is left out because no main theorem needs
it (name the results, e.g. "Lemmas 6.3 and 6.9 and Corollary 6.7 are not needed").

### 3.1 Subsection title

**Definition (focal point).** … ⟦Chapter4/Focal · IsFocalPoint⟧

**Theorem 6.6** (almost every $L_p$ is a Morse function) [V4.12]. Statement with every hypothesis
of the formal statement. ⟦Chapter4/Focal · ae_isMorseFunction_normSq_sub⟧

*Proof.* … $\square$
```

1. **Every result listed as on the path in your data file appears**, labelled by its
   verified-edition number in square brackets right after its name: `**Lemma 16.1** [V10.2].`.
   Results without a Milnor number get a short descriptive name: `**Lemma (one crossing)**
   [V2.3].` You may merge several V-items into one statement (label it `[V2.3, V2.4]`), split one
   into several, and reorder within the dependency order. When the data file lists off-path
   declarations for an on-path result, state and prove only the on-path part.
2. **No result that is off the path appears** as a labelled result. If the introduction mentions
   what is left out, do it in one sentence, without labels.
3. **Proofs are complete in substance and short in form**: the construction, the estimate, the
   case distinction, the lemma that makes it work, every step a careful reader could not supply in
   a minute; routine verifications are named, not carried out ("a direct computation", "by the
   chain rule"). Follow the formal proof (the proof by proof), not Milnor's, where they differ; say
   so in one clause when the difference matters ("Milnor's map $h$ is not continuous; the formal
   proof replaces it by …").
4. **Standard infrastructure** that the formalization had to build because Mathlib lacks it
   (relative singular homology, excision and subdivision; homotopy lifting and the exact sequence of
   a fibration; mapping telescopes; smooth dependence of flows on initial conditions; …) is stated
   precisely as `**Fact** (title) [Vx.y].` with its tags and a proof idea of one to three
   sentences, and marked "(standard)". The reader may take these on trust; the point is to say
   exactly what is used.
5. **Hidden hypotheses** the formal proof needs and Milnor does not state get one sentence, in a
   blockquote `> **Hidden hypothesis.** …`, only when they matter for correctness.
6. **Trace tags.** Right after each statement, tag its main declarations: `⟦Chapter2/Regular ·
   theorem_3_1⟧` (path relative to `Morse/`, or `Milnor/…`, or `Mathlib/…`; the name as declared in
   the file, possibly qualified by an enclosing namespace). In proofs, tag the key lemmas, sparingly
   (about one tag per 60–100 words). **Every tag must resolve and be on the path**:
   `python3 Exposition/shortest/check.py Exposition/shortest/sNN.md --chapter N` (from `Morse/`)
   must report 0 unresolved, 0 off the path, full coverage, and no off-path result labelled. Tags
   into Mathlib are allowed (and welcome for the facts the path assumes).
7. **Cross-references.** To a result of another chapter: by its verified-edition number, "[V1.8]"
   (the build turns it into a link); within your chapter you may also write "(§3.1)". To Milnor:
   "Milnor p. 35". Do not invent numbers for other chapters' sections.
8. **No motivation sections, no applications, no figures, no history, no tables of what Milnor
   skips.** Short, dense, precise. Chapter headings `## N. Title`, sections `### N.k Title`.
9. **Math**: pandoc Markdown, `$…$` and `$$…$$`; no Lean syntax in the prose except inside trace
   tags; no `\begin{align}` outside `$$`; no quotation of the book beyond a short phrase.

## The global setting (state it once in Chapter 1, use it everywhere)

- $V$ is a finite-dimensional real inner product space (the "Euclidean space"); a manifold is a
  *slice submanifold* $N \subseteq V$ modelled on $Z$ (dimension $n = \dim Z$), in the sense of the
  companion volume; $T_xN$ its tangent space, $P_x$ the orthogonal projection onto it.
- A function on $N$ is the restriction $f = F|_N$ of a smooth $F : V \to \mathbb R$. Critical
  points, Hessian, index and nullity are those of Chapter 1, computed in any chart.
- Riemannian geometry is that of the induced metric. "Complete" is replaced by "closed in $V$",
  which makes the closed Riemannian balls compact.
- Cell complexes are iterated adjunction spaces (finitely or countably many cells, attached along
  arbitrary maps), not CW-complexes.
- Homology is singular homology with coefficients in a field $\mathbb k$.
- Homotopy groups are Mathlib's $\pi_i(X, x)$; "≅" between them means a bijection (not claimed to
  respect base points) unless "as groups" is said.
- Paths are maps $\mathbb R \to V$ used on $[0, 1]$; $\Omega(N; p, q)$ is the space of piecewise
  smooth paths in $N$ from $p$ to $q$ with Milnor's metric (a pseudometric), $E$ the energy,
  $E_{**}$ its Hessian at a geodesic, $\Omega^d$ the paths of least energy $d$.

## Lengths (words, including formulas)

| Chapter | Title | Budget |
|---|---|---|
| 1 | Critical points and the lemma of Morse | 2,000 |
| 2 | Sublevel sets and attached cells | 3,000 |
| 3 | Morse functions exist | 1,800 |
| 4 | Homology and the Morse inequalities | 3,000 |
| 5 | Geodesics on a submanifold | 3,500 |
| 6 | Energy, Jacobi fields and the index theorem | 4,500 |
| 7 | The path space and the fundamental theorem | 5,500 |
| 8 | Whole manifolds of minimal geodesics | 2,500 |
| 9 | Bott periodicity for the unitary group | 4,500 |
| 10 | Bott periodicity for the orthogonal group | 5,500 |

A budget is a ceiling, not a target; going over by more than 15% means the chapter is not short.
