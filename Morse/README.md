# Milnor, *Morse Theory*, in Lean 4

A formalization of Milnor's *Morse Theory* (Annals of Mathematics Studies 51, Princeton 1963;
based on lecture notes by M. Spivak and R. Wells) against Mathlib, together with the expanded
prose needed to make each argument fully rigorous. This is the sister project of the
formalization of Milnor's *Topology from the Differentiable Viewpoint* (the root of this
repository, `..`), and it is built on top of it: Sard's theorem, the inverse function theorem on manifolds, Hadamard's lemma,
slice submanifolds, normal bundles, tubular neighbourhoods, orientations, degrees and the
Poincaré–Hopf theorem are imported from there rather than reproved.

## Three parts

1. **The book rewritten.** *Morse Theory, Rewritten* is Milnor's book with all the details filled
   in and some applications, written for advanced undergraduates.
   - Each numbered result carries a note saying whether it has been checked by machine, with its
     number in the verified edition and how the checked statement compares with Milnor's. The notes
     are added when the book is built (`Exposition/checked_marks.py`, from the comparison's data).
   - The chapters are `Exposition/Chapter1.md`–`Chapter15.md` and `Appendix.md`, with a PDF beside
     each.
   - The web edition is `Exposition/morse-theory-rewritten.html`.
   - The gaps, hidden hypotheses and possible misprints we found, as we read the book, are in
     `Exposition/Findings.md`.
2. **The Lean verification and its faithfulness checks.** *Morse Theory, Checked* is the
   formalization, `Morse/`, together with four reports that check that it says what Milnor says.
   `Morse/Test.lean` prints the axioms of every theorem. The verified edition is the place to start:
   - the verified edition says *what* is proved;
   - the proof by proof says *how*;
   - the comparison says *how it differs from Milnor*;
   - the round trip *independently checks the comparison's verdicts*.

   The four reports:
   - **Proof by proof** retells the formal proofs as mathematics, with a trace tag on every step. It
     is `Exposition/ProofByProof.md` (and `.pdf`), with the web edition
     `Exposition/morse-proof-by-proof.html`.
   - **The comparison**, *Morse Theory beside Lean*, sets every result of the book beside the
     statement the machine checked. Its data is `Exposition/cmp/*.json` and its web edition
     `Exposition/morse-beside-lean.html`.
   - **The verified edition**, `Exposition/Verification.md` (and `.pdf`), restates every
     machine-checked result in plain language with all its hypotheses, and ends with the sign-off
     list.
   - **The round-trip audit**, in `RoundTrip/` with its report in `RoundTrip/REPORT.md`, has
     Milnor's statements formalized blind and proved equivalent, or not, to the project's, and
     checks the definitions under the main theorems against blind textbook definitions. It is
     complete.
3. **The shortest path.** *Morse Theory, the Shortest Path* proves the main theorems and nothing
   else: exactly the results their formal proofs use, read off the Lean dependency graph. It is
   shortest for these formal proofs, not the shortest possible: a different proof could need less.
   - The text is `Exposition/ShortestPath.md` (and `.pdf`), with the web edition
     `Exposition/morse-shortest-path.html`.
   - It is built by `Exposition/build_shortest_path.py` from `Exposition/shortest/`.

Toolchain: Lean `v4.33.1`, Mathlib `v4.33.1` (the same as the Milnor project).

```bash
cd Morse             # build from this folder
lake exe cache get   # once
lake build
```

To check a single file use `lake build Morse.Chapter2.Regular` (module name), or
`lake env lean -DmaxSynthPendingDepth=3 Morse/Chapter2/Regular.lean`: plain `lake env lean` does not
pass the `leanOptions` of `lakefile.toml` and reports spurious failures in a few files.

This project is the folder `Morse/` of the repository `github.com/skydancerosel/math_faithful`, whose root is the Milnor project. Milnor is a Lake path dependency (`[[require]] name =
"Milnor"`, `path = ".."` in `lakefile.toml`), so Morse always builds against the Milnor sources of the
same checkout; Lake builds them in place (`../.lake/build`). Milnor's declarations live in the
namespace `Milnor` and are imported as `import Milnor.Chapter3.Sard` etc.

## Layout

| Path | What |
|---|---|
| `Morse/ChapterN/*.lean` | Lean sources, one folder per chapter of the exposition |
| `Morse/Test.lean` | `#print axioms` for every main theorem |
| `Exposition/ChapterN.md` | the expanded prose, chapter by chapter (see `Exposition/STYLE.md`) |
| `Exposition/build.py` | builds `ChapterN.pdf` (pandoc + XeLaTeX) and `web/ChapterN.html` (interactive figures) |
| `Exposition/figN-*.py`, `figN-*.js` | static (matplotlib) and interactive (plain JS) version of each chapter's figure |
| `Exposition/pages/` | page images of the scanned book, two book pages per image; not in git (copyright, size): regenerate with `pdftoppm -r 110 -png ../MorseTheory.pdf Exposition/pages/p` |
| `Exposition/build_book.py` | builds the single-page web edition `Exposition/morse-theory-rewritten.html` (all chapters, contents rail, interactive figures) |
| `Exposition/Findings.md` | gaps, hidden hypotheses and possible misprints found in the book, with what was confirmed or withdrawn on review |
| `Exposition/REVIEW.md` | the checklist each chapter was independently reviewed against |
| `Exposition/Verification.md` (and `.pdf`) | the verified edition: every machine-checked result restated in plain language with all its hypotheses, the hidden hypotheses and deviations from the book, what is not verified, and a numbered sign-off list; assembled by `Exposition/build_verification.py` from `Exposition/verification/chNN.md` (format in `Exposition/VERIFY.md`) |
| `Exposition/check_names.py` | checks that every Lean name cited in a report exists (`python3 Exposition/check_names.py Exposition/Verification.md`) |

## Chapters of the exposition

| Chapter | Milnor | Book pages |
|---|---|---|
| 1 | §1 Introduction, §2 Definitions and lemmas (the Morse lemma) | 1–12 |
| 2 | §3 Homotopy type in terms of critical values | 12–24 |
| 3 | §4 Examples, §5 The Morse inequalities | 25–32 |
| 4 | §6 Manifolds in Euclidean space: existence of non-degenerate functions | 32–38 |
| 5 | §7 The Lefschetz theorem on hyperplane sections | 39–42 |
| 6 | §8 Covariant differentiation, §9 The curvature tensor | 43–54 |
| 7 | §10 Geodesics and completeness | 55–66 |
| 8 | §11 The path space, §12 The energy of a path, §13 The Hessian of the energy | 67–76 |
| 9 | §14 Jacobi fields, §15 The index theorem | 77–87 |
| 10 | §16 A finite-dimensional approximation, §17 The topology of the full path space | 88–97 |
| 11 | §18 Existence of non-conjugate points, §19 Topology and curvature | 98–108 |
| 12 | §20 Symmetric spaces, §21 Lie groups as symmetric spaces | 109–117 |
| 13 | §22 Whole manifolds of minimal geodesics | 118–123 |
| 14 | §23 The Bott periodicity theorem for the unitary group | 124–132 |
| 15 | §24 The periodicity theorem for the orthogonal group | 133–148 |
| A | Appendix: the homotopy type of a monotone union | 149–153 |

## Status

Work started 2026-10-01; status as of 2026-10-06: 238 Lean files, about 98,000 lines, 1,498 theorems checked in `Morse/Test.lean`, no `sorry`, only the three standard axioms. The round-trip audit is complete (348 blind statements, 116 definitions; `RoundTrip/REPORT.md`). Formalization status is tracked per result below. `PLAN.md` has the plan; `HANDOFF.md` has what remains and how to resume.

| Milnor | File | Status |
|---|---|---|
| §2 p. 5, Lemma 2.1 (Hadamard), coordinate and second-order forms | `Morse/Chapter1/Hadamard.lean` (on `Milnor.exists_hadamard`) | proved |
| §2 pp. 4–5, critical points, Hessian, nullity, index; independence of coordinates | `Morse/Chapter1/Nondegenerate.lean` | proved (in a normed space, i.e. in local coordinates) |
| §2 p. 6, Lemma 2.2 (the Morse lemma), and λ = index | `Morse/Chapter1/{SquareRoot,MorseLemma}.lean` | proved (local coordinates) |
| §2 p. 8, Corollary 2.3 (non-degenerate critical points are isolated) | `Morse/Chapter1/Nondegenerate.lean` | proved (needs only `C²` at `p`) |
| §2 pp. 8–9, examples (a), (c), (d), (e) of degenerate critical points | `Morse/Chapter1/Examples.lean` | proved; (b) not done |
| §2 on manifolds: critical points, Hessian, index, nullity; independence of the chart (`f` only `C²` at `p`); Milnor's p. 4 criteria as theorems | `Morse/Chapter1/Manifold.lean` | proved |
| §2 on manifolds: Corollary 2.3, critical set closed and discrete, finitely many critical points in a compact set, the Morse lemma in a smooth chart and its converse | `Morse/Chapter1/ManifoldMorse.lean` | proved (no Hausdorff hypothesis needed) |
| §2 on submanifolds `N ⊆ ℝᴷ` (the Milnor project's slice submanifolds): criticality iff the gradient is normal, Hessian through slice charts, the p. 35 criterion and p. 36 Hessian formula for `L_p` | `Morse/Chapter1/ManifoldSubmanifold.lean` | proved |
| §2 pp. 10–11, Lemma 2.4 (compactly supported fields generate 1-parameter groups) | `Morse/Flow/{Global,Nemytskii,Volterra,Smooth}.lean` | proved for `M = E` a finite-dimensional normed space (`Morse.lemma_2_4`); global flow of any bounded Lipschitz field; `Cⁿ` dependence on `(t, x)` for `Cⁿ` fields, `1 ≤ n ≤ ∞` |
| §3 pp. 12–13, Theorem 3.1: no critical values in `[a, b]`, `f⁻¹[a, b]` compact ⇒ a diffeomorphism carries `M^a` onto `M^b`, `M^a` is a strong deformation retract of `M^b`, the inclusion is a homotopy equivalence | `Morse/Chapter2/{Crossing,Regular}.lean` (`Morse.theorem_3_1`) | proved for `M` a finite-dimensional inner product space |
| §3, Theorem 3.1 on submanifolds `N ⊆ ℝᴷ` (not necessarily closed), `f` the restriction of a smooth function | `Morse/Chapter2/Submanifold.lean` (`Morse.theorem_3_1_submanifold`) | proved |
| §3 p. 13, the (unnumbered) Remark after Theorem 3.1: compactness of `f⁻¹[a, b]` cannot be omitted (`ℂ ∖ {i}`, `f = ‖z‖²`) | `Morse/Chapter2/Remark.lean` (`Morse.RemarkP13.remark_p13`) | proved |
| §3 pp. 14–19, Theorem 3.2: for small `ε`, `M^{c+ε}` deformation retracts onto `M^{c−ε} ∪ e^λ` (an embedded closed λ-disk meeting `M^{c−ε}` exactly in its boundary sphere), and is homotopy equivalent to the pushout `D^λ ⊔_{S^{λ−1}} M^{c−ε}` | `Morse/Chapter2/{CellModel,CellAttach,CellAdjunction}.lean` (`Morse.theorem_3_2`, `Morse.theorem_3_2_attach`) | proved for `M = ℝⁿ` (a finite-dimensional inner product space), with Milnor's `μ` constructed explicitly; on submanifolds see the next rows |
| §3, Theorem 3.2 on submanifolds `N ⊆ ℝᴷ` (`f = F|N`): `N^{c+ε}` deformation retracts onto `N^{c−ε} ∪ e^λ` and is homotopy equivalent to the pushout `D^λ ⊔_{S^{λ−1}} N^{c−ε}`; Milnor's construction inside one chart of any Hausdorff space | `Morse/Chapter2/{CellPatch,CellAttachSubmanifold}.lean` (`Morse.theorem_3_2_submanifold`, `Morse.theorem_3_2_attach_submanifold`) | proved |
| §3 p. 19, Remark 3.3 (several critical points on one level), on submanifolds | `Morse/Chapter2/SeveralCritical.lean` (`Morse.remark_3_3_submanifold`) | proved |
| §3 pp. 20–21, Lemmas 3.6 and 3.7 (homotopic attaching maps give homotopy equivalent spaces; a homotopy equivalence extends over an attached cell), with Milnor's explicit formulas | `Morse/Chapter2/Attaching.lean` (`Morse.lemma_3_6`, `Morse.lemma_3_7`) | proved |
| §3 pp. 20–22, Theorem 3.5 for compact `N ⊆ ℝᴷ`: `N` has the homotopy type of a space built from the empty set by attaching exactly `C_λ` cells of dimension `λ`, in order of critical value | `Morse/Chapter2/CWType.lean` (`Morse.theorem_3_5`, `Morse.theorem_3_5_count'`) | proved; the attaching maps are not made cellular (Mathlib has no cellular approximation), so the result is an iterated adjunction space rather than a CW complex; the non-compact case needs Whitehead's theorem |
| §3 p. 20, Remark 3.4: `M^c` is a strong deformation retract of `M^{c+ε}`, and `M^{c−ε} ∪ e^λ` is one of `M^c` | `Morse/Chapter2/CriticalLevel.lean` | proved for `M = ℝⁿ` |
| §4 p. 25, Theorem 4.1 (Reeb): a compact submanifold `N ⊆ ℝᴷ` carrying a function with exactly two critical points, both non-degenerate, is homeomorphic to the sphere `Sⁿ`; also for intrinsic smooth `f` | `Morse/Chapter3/{ReebGluing,ReebMorse,Reeb}.lean` (`Morse.reeb`, `Morse.reeb_of_contMDiff`) | proved; with the reusable gluing lemma (two closed `n`-balls meeting in their boundary sphere make `Sⁿ`, by Alexander's trick); Remarks 1–2 are notes only |
| §1 pp. 1–3, the torus standing on a plane: a compact surface in `ℝ³`; the height function has exactly four critical points, all non-degenerate, of indices 0, 1, 1, 2; its Euler number is `0` (by Morse theory, and independently by a nowhere-zero field); Theorem 3.1 between critical levels | `Morse/Chapter3/{TorusSurface,Torus}.lean` (`Morse.Torus.isCriticalPointM_height_iff`, `Morse.Torus.critCount_height`, `Morse.isEulerNumber_torus`) | proved; the identification of each sublevel set (disc, cylinder, …) and the cell attachments of p. 2 are not written out for the torus |
| §5 p. 29, `Σ (−1)^λ C_λ = χ(M)`, without homology: for a compact submanifold `N ⊆ ℝᴷ⁺¹` (`dim N ≥ 1`) the alternating count of critical points of every Morse function equals the Poincaré–Hopf integer of the Milnor project; hence it is the same for all Morse functions; `1 + (−1)ⁿ` on `Sⁿ` | `Morse/Chapter3/EulerChar{Algebra,Gradient,,Sphere}.lean` (`Morse.exists_eulerNumber_eq_sum_critCount`) | proved; via `sgn det = (−1)^index` and the tangential gradient, whose index at a critical point of index λ is `(−1)^λ`; `χ` is not yet identified with the homological Euler characteristic |
| §5 pp. 28–31, subadditive functions (Lemma 5.1), `S_λ` subadditive (Lemma 5.3), weak (Theorem 5.2) and strong inequalities, Euler characteristic, Corollary 5.4, lacunary principle | `Morse/Chapter3/Inequalities.lean` | proved for any `FiltrationHomology` (finite-dimensional groups of pairs with the exact sequence of every triple); no instance from singular homology yet, since Mathlib has no relative homology, long exact sequence or excision; Theorems 3.1–3.2 enter as the hypothesis that each step attaches cells |
| §6 pp. 32–38, Theorem 6.1 / Corollary 6.2 (Sard on manifolds: critical values of a smooth map into `ℝⁿ` are null; focal points are null), the endpoint map `E` on the normal bundle, focal points and multiplicities (Milnor's Lemmas 6.3–6.5, Assertion 6.4) | `Morse/Chapter4/{Sard,NormalBundle,Focal,Curvature}.lean` | proved for slice submanifolds `M ⊆ ℝⁿ`; Sard for smooth (not `C¹`) maps |
| §6, Theorem 6.6: for almost every `p ∈ ℝⁿ`, `L_p = ‖x − p‖²` restricted to `M` is a Morse function (for every Haar measure); Corollary 6.7: a closed submanifold carries a Morse function with compact sublevel sets; Lemma 6.9: the index of `L_p` at `q` is the number of focal points on `[q, p]` with multiplicity | `Morse/Chapter4/{Existence,Compact,Curvature}.lean` (`Morse.ae_isMorseFunction_normSq_sub`, `Morse.indexM_normSq_sub_eq_finsum_focalMult`) | proved |
| §6, Corollary 6.8: `f + ⟨a, ·⟩` is a Morse function for almost every `a`; uniform approximation of any smooth `f` with its derivatives by Morse functions | `Morse/Chapter4/{Approximation,Uniform}.lean` | proved, without Milnor's hypothesis that `f` is bounded |
| Abstract compact manifolds (Milnor's setting), via Mathlib's Whitney embedding: the image of a smooth embedding with injective derivative is a slice submanifold and the embedding is a diffeomorphism onto it; the Morse notions are diffeomorphism invariant. Hence every compact Hausdorff manifold has a Morse function; `χ(M)` with `Σ(−1)^λ C_λ(f) = χ(M)` for every Morse function, independent of the embedding; Reeb's theorem; Theorem 3.1; Corollary 6.8 | `Morse/Chapter4/{WhitneySlice,WhitneyInvariance,Whitney}.lean` (`Morse.sum_critCount_eq_eulerNumberM`, `Morse.reeb_of_compactSpace`, `Morse.theorem_3_1_of_compactSpace`) | proved for compact `M`; non-compact `M` needs a Whitney embedding Mathlib does not have; 3.2 and 3.5 not yet transferred |
| §7 pp. 39–41, the index bound for complex submanifolds: a form `G − Re B` (`G ≥ 0` and `i`-invariant, `B` complex bilinear) has index `≤ dim_ℂ`; the Andreotti–Frankel identity; Assertions 1–2; in holomorphic coordinates, the Hessian of `‖w(z) − p‖²` has index `≤ k` | `Morse/Chapter5/IndexBound.lean` | proved (algebraic core; Theorems 7.1–7.4 are in the §7 Lefschetz row below) |
| §9 pp. 51–54, Lemma 9.3 (4) from (1)–(3) (the octahedron), sectional curvature depends only on the plane and determines `R` (polarization), constant curvature | `Morse/Chapter6/CurvatureAlgebra.lean` | proved (algebraic) |
| §8, Milnor's symmetric connection = Mathlib's `torsion = 0`, Corollary 8.4 = `IsMetricCompatible`, Milnor's `R` = − Kobayashi–Nomizu's; uniqueness half of Lemma 8.6 (Koszul formula) | `Morse/Chapter6/Connection.lean` | proved; existence of the Levi-Civita connection and parallel transport not in Mathlib |
| §§8–9 for submanifolds `N ⊆ ℝᴷ` with the induced metric: the projection `P_q` onto `T_qN` is smooth; the Levi-Civita connection `P(dY(X))` with Milnor's rules (1)–(4), Corollary 8.4, symmetry, and Lemma 8.6 (existence and uniqueness, Koszul); the second fundamental form; the curvature `R(X,Y)Z = II(Y, II(X,Z)) − II(X, II(Y,Z))`, the Gauss equation (Milnor's sign), Lemma 9.3 | `Morse/Chapter6/{Projection,Submanifold}.lean` | proved |
| §8 pp. 44–46, covariant derivative along curves, Lemmas 8.1–8.3: parallel fields exist, are smooth and unique; parallel transport is a linear isometry `T_{c(t₀)}N ≃ T_{c(t₁)}N`; Lemmas 8.7 and 9.2; the round sphere has `II = −⟨v, w⟩q` and sectional curvature 1 | `Morse/Chapter6/{LinearODE,Parallel,Surface,SphereCurvature}.lean` | proved |
| §10 pp. 55–64 for submanifolds `N ⊆ ℝᴷ`: geodesics (existence, uniqueness, smooth dependence; Theorem 10.1, Lemma 10.2), the exponential map smooth near the zero section with `d(exp_q)₀ = id` and a diffeomorphism from a ball, uniformly normal neighbourhoods (Lemma 10.3), the Gauss lemma, Theorem 10.4 (short geodesics are shortest, with the sharp equality case: an equal-length path is a monotone reparametrization), Corollaries 10.7–10.8, the distance `ρ` and its topology | `Morse/Chapter7/*.lean` (`Morse.theorem_10_4`, `Morse.gauss_lemma`, `Morse.corollary_10_8`) | proved |
| §10 pp. 62–64, Theorem 10.9 (Hopf–Rinow) and Corollary 10.10 with its converse, for connected submanifolds `N ⊆ ℝᴷ`: four conditions are equivalent (metric completeness; geodesic completeness; `exp_p` defined on all of `T_pN` for one `p`; bounded sets have compact closure), and then any two points are joined by a minimal geodesic; `ρ` is a continuous metric, finite on connected `N`, inducing `N`'s topology; every closed `N` (so every compact one, and `Sⁿ`) is complete | `Morse/Chapter7/{Metric,GeodesicFlow,HopfRinow}.lean` (`Morse.hopf_rinow`, `Morse.theorem_10_9'`, `Morse.corollary_10_10`) | proved |
| §§11–13, 14.1 for submanifolds `N ⊆ ℝᴷ` (the path space used through variations): `L² ≤ (b − a)E` with equality iff constant speed; variations and their fields (`TΩ_ω`); Lemma 11.A (every field vanishing at the ends is a variation field, via `exp`, no completeness needed); the first variation formula (12.2′) at every `u` and Theorem 12.2; Corollary 12.3 (critical paths are exactly the geodesics); the second variation formula, Theorem 13.1, with Milnor's sign of `R`; `E_**` as a symmetric bilinear form on `TΩ_γ` matching his definition through variations (13.4, 13.5, 13.6: minimal geodesics have `E_** ≥ 0`); Theorem 14.1 (the null space of `E_**` is the space of Jacobi fields vanishing at the ends) | `Morse/Chapter8/{Piecewise,Energy,FirstVariation,Critical,SecondVariation,Hessian,Jacobi}.lean` (`Morse.first_variation`, `Morse.corollary_12_3`, `Morse.second_variation`, `Morse.theorem_14_1`) | proved |
| §§14–15 for submanifolds `N ⊆ ℝᴷ`: the Jacobi fields along a geodesic form a space of dimension `2n`, determined by `J(s)` and `DJ/dt(s)`; the nullity of `E_**` is the multiplicity of the conjugate point (Theorem 14.1), less than `n` (Remark 14.2); Lemmas 14.3–14.4 and Remarks 14.5–14.6 (Jacobi fields are the variation fields of variations through geodesics; free end values at non-conjugate points); Lemma 15.4 (index and nullity reduce to broken Jacobi fields, hence are finite); **Theorem 15.1, the Morse index theorem**: the index of `E_**` equals the number of conjugate points `γ(t)`, `0 < t < 1`, counted with multiplicity, and there are finitely many; Corollary 15.2 | `Morse/Chapter9/*.lean` (`Morse.theorem_15_1`, `Morse.finrank_jacobiSpace`, `Morse.theorem_14_1_nullity`, `Morse.corollary_15_2`) | proved; `λ(τ)` via fields supported in `[0, τ]`, positivity on `T′` by a Poincaré estimate; the examples (the sphere) not formalized |
| §16 pp. 88–92 for complete submanifolds `N ⊆ ℝᴷ`: broken geodesics and their break points (Lemma 16.1, an open subset of `N^m`), `B^a` compact, the critical points of `E′ = E|B` are exactly the unbroken geodesics, with the index and nullity of `E_**` (Theorem 16.2); Theorem 16.3: `B^a` has the homotopy type of a cell complex with one `λ`-cell for each geodesic of index `λ` and energy `≤ a`; `B^a` is a strong deformation retract of `Ω^a` with Milnor's metric, so `Ω^a` itself has that homotopy type | `Morse/Chapter10/*.lean` (`Morse.BrokenSetup.lemma_16_1`, `Morse.BrokenSetup.theorem_16_2_index`, `Morse.BrokenSetup.theorem_16_2_deformationRetract`, `Morse.BrokenSetup.theorem_16_3_Omega_count`) | proved (paths as functions on `ℝ`, so `d` is a pseudometric; `a` assumed not a critical value, which 16.3 needs and omits) |
| §17 pp. 93–97: **Theorem 17.1** (the inclusion of piecewise smooth paths, with Milnor's metric, into continuous paths is a homotopy equivalence — with a modified proof, since Milnor's `h`, as we read it, is not continuous; no completeness needed); **Theorem 17.3, the fundamental theorem of Morse theory** (`N` closed in `ℝᴷ`, `p, q` non-conjugate: `Ω(N; p, q)` has the homotopy type of a countable cell complex with one `λ`-cell for each geodesic of index `λ`); Corollary 17.4 (for `q ≠ ±p`, `Ω(Sⁿ; p, q)` has one cell in each dimension `k(n − 1)`) and its homology (`n ≥ 3`, any field: `b_i = 1` if `(n − 1) ∣ i`, else `0`); Remark 17.5 (`ℝⁿ⁺¹ ∖ 0` shows completeness is needed) | `Morse/Chapter10/{RelativeCells,FundamentalTheorem,SublevelHomology,PathHomology,SphereGeodesics,SpherePaths,Incomplete,FullPathSpace,FullPathDeform,GoodBalls,GoodJoin,FullPathOmega,FullPathTheorem}.lean` (`Morse.theorem_17_1`, `Morse.theorem_17_3`, `Morse.corollary_17_4`, `Morse.bettiNumber_sphere_paths`) | proved; 17.3 for continuous paths, the loop-space form of 17.4 (moving an endpoint), `n = 2`, and Corollary 17.2 not yet |
| §17 p. 94, **the step of Milnor's proof of 17.1 that does not hold as we read it, machine-checked**: for `M = ℝ`, `p = q = 0`, `f = |·|` and the admissible choice `ε₂ ≡ 1`, Milnor's map `h : Ω* → Ω` (defined exactly as on p. 94) is not continuous at `ω_{λ*}`, `λ* = √3/2`, for his metric `d`: `ω_λ → ω_{λ*}` uniformly while `E(h(ω_λ)) ≥ (27/64)δ^{−1/3} → ∞` | `Morse/Chapter10/MilnorH.lean` (`Morse.milnor_h_not_continuous`) | proved; Theorem 17.1 itself is true (`Morse.theorem_17_1`, by the modified proof) |
| §18 pp. 98–99 for submanifolds `N ⊆ ℝᴷ`: `exp` is smooth on its whole (open) domain; Theorem 18.1 (`exp_q(v)` is conjugate to `q` along `t ↦ exp_q(tv)` iff `d(exp_q)_v` is singular, with multiplicity = nullity); the conjugate locus of `p` is the set of critical values of `exp_p`, hence null (Corollary 18.2), and non-conjugate points are dense — no completeness needed | `Morse/Chapter11/{ExpSmooth,NonConjugate}.lean` (`Morse.theorem_18_1`, `Morse.corollary_18_2`, `Morse.dense_compl_conjLocus`) | proved |
| §19 pp. 100–108, the parts that need only the index theorem: Lemma 19.1 (sectional curvature `≤ 0` ⇒ no conjugate points, `E_**` positive definite); the Ricci tensor; Myers' theorem 19.4 (`Ric ≥ (n−1)/r²`, `n ≥ 2` ⇒ a geodesic longer than `πr` is not minimal) and Corollary 19.5 (diameter `≤ πr`, a complete `N` is compact); the unit sphere; Theorem 19.6's index bound (longer than `kπr` ⇒ index `≥ k`) | `Morse/Chapter11/{Curvature,Myers,LongGeodesics}.lean` (`Morse.lemma_19_1`, `Morse.theorem_19_4`, `Morse.corollary_19_5`, `Morse.theorem_19_6_index`) | proved; Theorem 19.2, Corollary 19.3 and the homotopy conclusions of 19.6 need §§16–17 |
| §21 pp. 112–117, a Lie algebra with an ad-invariant inner product: `∇_X Y = ½[X, Y]`, `R(X, Y)Z = ¼[[X, Y], Z]` (Milnor's sign), `⟨R(X,Y)X, Y⟩ = ¼‖[X,Y]‖² ≥ 0`; `K_V = −¼ ad_V²` self-adjoint and positive semidefinite, with even multiplicities; `tr K_V = −¼ · Killing` | `Morse/Chapter12/BiInvariant.lean` | proved (algebraic) |
| §23 pp. 124–132, geodesics from `I` to `−I` in `SU(2m)`: the index is `Σ_{k_i > k_j}(k_i − k_j − 2)` (from the spectrum of `K_A`); minimal iff all `k = ±1`; Lemma 23.2 (`λ ≥ 2m + 2` otherwise); index `0` for `k = (3, 1, …, 1)` in `U(n)`; the matrix facts (`exp(diag) = −I`, `A² = −π² ⇔ A = iπ(2P − I)`) | `Morse/Chapter14/{IndexCount,SUMatrices}.lean` | proved; the topology is in `Morse/Chapter14/{MinimalPaths,MinimalRetract,Periodicity,PeriodicityGroups,CircleGroup}.lean` (row below) |
| §24 pp. 133–148, complex structures and Clifford modules: `Ω_k(n)` compact, Lemma 24.4 (iii), the odd steps of 24.6, explicit anticommuting structures on `ℝ¹⁶` and `ℝ^{16r}` (and vector fields on spheres), Lemma 24.2 (`λ ≥ 2m − 2`), Lemma 24.8 (minimal modules have dimension `m_k`; unique up to linear isomorphism for `k ≢ 3 mod 4`) | `Morse/Chapter15/{Relations,ComplexStructure,Clifford,CliffordModules,MinimalModules}.lean` | proved; the topology is in the rest of `Morse/Chapter15/` (row below); the two classes for `k = 3, 7` not formalized |
| Homology infrastructure (not in Mathlib): relative singular homology for pairs with coefficients in any abelian category with coproducts; the long exact sequences of a pair and of a triple, with naturality of `δ`; homotopy invariance for pairs; `H(B, A) ≅ H(X, A)` for a strong deformation retract `B`; singular homology as an instance of Mathlib's Eilenberg–Steenrod `HomologyPretheory` with homotopy invariance | `Morse/Homology/{Relative,RelativeHomotopy,RelativeRetract,Triple,Pretheory}.lean` (`Morse.Homology.relHomology`, `Morse.Homology.relHomology_map_eq_of_homotopy`, `Morse.Homology.singularHomologyPretheory`) | proved |
| Homology infrastructure: chains as combinations of maps `Δⁿ → X` (naturally isomorphic to Mathlib's), barycentric subdivision with `∂T + T∂ = 1 − S` and the diameter bound `(n/(n+1))^k`, the small-simplex theorem (a chain homotopy equivalence), **excision** (`(X∖Z, A∖Z) → (X, A)` an isomorphism when `closure Z ⊆ interior A`, and the open-cover form), the Mayer–Vietoris sequence | `Morse/Homology/{ModuleComplex,Simplex,LinearChains,AffineSimplex,Subdivision,SmallChains,Excision,MayerVietoris}.lean` (`Morse.Homology.excision`, `Morse.Homology.excision_of_union`, `Morse.Homology.smallChainsHomotopyEquiv`) | proved; naturality of the Mayer–Vietoris connecting map not yet |
| Homology of disks, spheres and cell attachments: `H_i(Dⁿ, Sⁿ⁻¹)` is `R` for `i = n` and `0` otherwise; `dim H_i(Sⁿ) = [i = 0] + [i = n]` over a field; for a closed `Y` and a cell `χ : Dᵏ → X` (continuous, injective, meeting `Y` exactly in its boundary sphere, `X = Y ∪ χ(Dᵏ)`), `H_i(X, Y) ≅ H_i(Dᵏ, Sᵏ⁻¹)`; with several disjoint cells, `dim H_i(X, Y)` is the number of cells of dimension `i` | `Morse/Homology/{CellExcision,Spheres,CellAttach}.lean` (`Morse.Homology.finrank_sphereHomology`, `Morse.Homology.relHomology_cellAttach_iso`, `Morse.Homology.finrank_relHomology_cellsAttach`) | proved |
| §5 in singular homology, with no hypotheses left (Theorem 5.2, Corollary 5.4): for a compact submanifold `N ⊆ ℝᴷ` (and, through the Whitney embedding, any compact manifold) and a Morse function, over every field `𝕜`: a filtration by regular values whose steps have `dim H_j` = number of critical points of index `j`; the weak inequalities `b_λ ≤ C_λ`, the strong inequalities, and `Σ(−1)^i b_i = Σ(−1)^λ C_λ`; the lacunary principle; the Poincaré–Hopf number of `N` and `χ(M)` equal the homological Euler characteristic `Σ(−1)^i b_i` (for every field); Betti numbers of a compact manifold are finite and vanish above the dimension; examples: two critical points (`b₀ = bₙ = 1`), the torus, `Sⁿ` | `Morse/Homology/{TripleFiltration,MorseHomologyBasic,MorseHomologyCells,MorseHomology,MorseHomologyManifold}.lean` (`Morse.Homology.bettiNumber_le_critCount`, `Morse.Homology.sum_bettiNumber_eq_sum_critCount`, `Morse.Homology.eulerNumberM_eq_sum_bettiNumber`) | proved; `ℂPⁿ` as the trace-1 Hermitian projections with Milnor's `Σ c_j|z_j|²` (`Morse/Chapter3/{ProjectiveSpace,ProjectiveMorse}.lean`, `Morse.bettiNumber_complexProjectiveSpace`); integral homology not done |
| Appendix pp. 149–153: telescopes, the homotopy direct limit, Examples 1 and 3; **Theorem A** (a map that restricts to homotopy equivalences `X_i → Y_i` between homotopy direct limits is a homotopy equivalence) with Milnor's two cases and corrected formula `(4t − 3)u`, and in general with no closedness hypothesis; the Corollary; mapping telescopes; cell towers and the topological part of Theorem 17.3 (a space exhausted by sublevel sets homotopy equivalent to compatible finite cell complexes has the homotopy type of the countable complex, modelled by the mapping telescope) | `Morse/Appendix/{Telescope,Examples,TheoremA,MappingTelescope,MonotoneUnion}.lean` (`Morse.theoremA`, `Morse.theoremA_general`, `Morse.isCountableCellComplexType_of_sublevel`) | proved; Example 2 needs Whitehead's theorem; the phantom-map counterexample of the Remark not formalized |
| Homotopy-group infrastructure (not in Mathlib): induced maps on `π_N`, change of basepoint, invariance under homotopy equivalences; the push-off lemma (a map of a cube of dimension `< λ` into a space with a `λ`-cell attached is homotopic rel the outside to one missing a point of the cell); **attaching cells of dimension `≥ λ` induces bijections on `πᵢ` for `i ≤ λ − 2` and surjections for `i = λ − 1`** (one cell, finitely many, embedded cells, countable towers and mapping telescopes); the relative form used by Theorem 22.1; `π_{i+1}(ΩX) ≅ π_{i+2}(X)` as groups and `Ω(X; p, q) ≃ Ω(X; p, p)` for path-connected `X` | `Morse/Homotopy/{Basic,ChangeOfBase,PushOff,CellAttach,Telescope,RelCells,LoopSpace}.lean` (`Morse.Homotopy.bijective_homotopyGroupMap_cellInl`, `Morse.Homotopy.bijective_homotopyGroupMap_of_cellTower`, `Morse.Homotopy.homotopyGroupPiLoopMulEquiv`) | proved; change of basepoint as a group isomorphism (`Morse/Homotopy/ChangeOfBaseGroup.lean`, `Morse.Homotopy.changeBaseMulEquiv`); Whitehead's theorem not needed so far |
| §19 pp. 100–108, the parts that need §17: `exp_p` is a covering map when `N` is complete without conjugate points; **Theorem 19.2** (Cartan–Hadamard: complete, simply connected, curvature `≤ 0` ⇒ unique geodesics and `N` diffeomorphic to `ℝⁿ`); Corollary 19.3, first half (`πᵢ(N) = 0` for `i > 1`); one geodesic in each homotopy class of paths (p. 103); the path space homotopy equivalent to a countable discrete set (contractible if `N` is simply connected); **Theorem 19.6** for non-conjugate endpoints (compact, positive-definite Ricci tensor ⇒ finitely many cells in each dimension, finite-dimensional homology of `Ω`) | `Morse/Chapter11/{ExpCovering,CartanHadamard,PositiveRicci,RicciHomology}.lean` (`Morse.isCoveringMap_expToN`, `Morse.theorem_19_2`, `Morse.corollary_19_3`, `Morse.theorem_19_6`) | proved; **Theorem 19.6 for all endpoints** in `Morse/Chapter11/PositiveRicciAll.lean` (`Morse.theorem_19_6_all`); π₁ torsion-free (second half of 19.3) not formalized |
| Fibre bundles (not in Mathlib): `IsLocallyTrivial` maps (and Mathlib's `FiberBundle`s) are Serre fibrations (homotopy lifting for cubes relative to the open box); **the long exact homotopy sequence** `… → πₙ(F) → πₙ(E) → πₙ(B) → πₙ₋₁(F) → …` with exactness at every place down to `π₀`, group-homomorphism versions; the forms Milnor's §23 uses (if `πᵢ(E) = 0` for `i ≤ k`, then `∂ : π_{j+1}(B) ≅ π_j(F)` for `j + 1 ≤ k`; if `πᵢ(B) = 0` for `i ≤ k`, then `πᵢ(F) ≅ πᵢ(E)` for `i + 1 ≤ k`); `πᵢ(Sⁿ) = 0` for `i < n`, real and complex spheres | `Morse/Homotopy/{Fibration,HomotopyLifting,ExactSequence,ExactSequenceIso,Spheres}.lean` (`Morse.Homotopy.IsLocallyTrivial.isSerreFibration`, `Morse.Homotopy.exact_base`, `Morse.Homotopy.bijective_boundaryMapPi_of_le`, `Morse.Homotopy.subsingleton_pi_sphere`) | proved |

| §7 pp. 39–42, **Lefschetz**: Theorem 7.1 (`H_i(M) = 0` for `i > k`, over a field) and 7.2 (a closed complex submanifold of `ℂⁿ` has the homotopy type of a countable cell complex of dimension `≤ k`); Corollary 7.3 and **Theorem 7.4** (`H_r` and `π_r` of `V ∩ P → V` bijective below `k`, onto at `k`) for closed `V ⊆ ℂPⁿ` whose affine part is a complex submanifold of dimension `k` (pure dimension built in), under hypothesis (N) | `Morse/Chapter5/{ComplexIndex,Lefschetz,LefschetzSlab,HyperplaneSection,ProjectiveSection,LefschetzHomotopy}.lean` (`Morse.theorem_7_1`, `Morse.theorem_7_2`, `Morse.corollary_7_3`, `Morse.theorem_7_4`) | proved; homology over fields; no Lefschetz duality used (the exposition's route) |
| §17 p. 95, Corollary 17.2 (`Ω(N; p, q)` has the homotopy type of a countable cell complex, for closed `N`) and Corollary 17.4 for loops (`Ω(Sⁿ; p, p)`, cells in dimensions `k(n − 1)`) | `Morse/Chapter10/CWType.lean` (`Morse.corollary_17_2`, `Morse.corollary_17_4_loop`) | proved (via 18.2 and 17.3, not Milnor's 1959 paper) |
| §§20–21 pp. 109–117 on matrix groups: `U(n)`, `SU(n)`, `O(n)` as slice submanifolds with the bi-invariant metric; geodesics `t ↦ g exp(tA)`, the curvature, Jacobi fields and conjugate points through Theorem 20.5; **Lemma 23.1** (`A ↦ ½(I − (i/π)A)` from the minimal velocities onto the Grassmannian of trace-`m` projections) | `Morse/Chapter12/{MatrixInner,MatrixGroups,GroupGeodesics,GroupJacobi,SUJacobi,SUIndex,SUMinimal}.lean` (`Morse.lemma_23_1`, `Morse.isMinimalGeodesic_exp_iff`, `Morse.riemDist_one_neg_one`) | proved |
| §22 pp. 118–123: Lemma 22.4, Lemma 22.5 (manifold of minima), **Theorem 22.1** (`πᵢ(Ω^d) → πᵢ(Ω)` bijective for `i ≤ λ₀ − 2`, onto for `i = λ₀ − 1`), also one open-closed piece of `Ω` at a time; Corollary 22.2 (`πᵢ(Ω^d) ≅ π_{i+1}(M)`, as groups for `i ≥ 1`); **Corollary 22.3** (Freudenthal, `πᵢ(Sⁿ) ≅ π_{i+1}(Sⁿ⁺¹)` for `i ≤ 2n − 2`, onto for `i = 2n − 1`) | `Morse/Chapter13/{Perturbation,Compression,ManifoldOfMinima,MinimalDeform,Theorem22,Corollaries,CorollaryGroups,SphereMinimal,Freudenthal,Componentwise}.lean` (`Morse.theorem_22_1`, `Morse.corollary_22_2`, `Morse.corollary_22_3`, `Morse.theorem_22_1_clopen`) | proved; Hanner's theorem is replaced by the hypothesis that `Ω^d` is a neighbourhood retract, discharged by explicit retractions in every application |
| §23 pp. 124–132, the topology: the minimal geodesics `I → −I` in `SU(2m)` are `minVel` (homotopy equivalence; homeomorphism after the separation quotient), with an explicit neighbourhood retraction; **Theorem 23.3** (`πᵢ G_m(ℂ^{2m}) ≅ π_{i+1} SU(2m)`, `i ≤ 2m`); **Bott periodicity for `U`**: `π_{i−1} U(m) ≅ π_{i+1} U(m)` for `1 ≤ i ≤ 2m − 2`, stable form `πᵢ U(n) ≅ π_{i+2} U(n′)`; Theorem 23.5 (`πⱼ U(m)` is `0` or `ℤ` by parity, `j ≤ 2m − 1`, as groups); `π₁(S¹) ≅ ℤ` as groups | `Morse/Chapter14/{MinimalPaths,MinimalRetract,Periodicity,PeriodicityGroups,CircleGroup}.lean` (`Morse.theorem_23_3`, `Morse.periodicity_theorem`, `Morse.periodicity_theorem_stable`, `Morse.theorem_23_5_mulEquiv`) | proved |
| §24 pp. 133–148, the topology: the strata of `Ω_k(n)` as totally geodesic slice submanifolds; Lemma 24.4 (minimal geodesics `J → −J` form `Ω_{k+1}(n)`, homotopy equivalence), explicit retraction by polar decomposition; the index bounds for `k ≢ 2 (mod 4)` (`≥ n/m_{k+1} − 1`) and `k = 2, 6` (`≥ (ν − |c|)/4` on the winding component `Ω^{(c)}`); **Theorem 24.3** and the finite-stage **Theorem 24.5** (`πᵢ Ω_{k+1}(n) ≅ π_{i+1} Ω_k(n)` for `i ≤ n/m_{k+1} − 3`, componentwise for `k = 2, 6`); stabilization `J ↦ J ⊕ J′_k`; `Ω₈(16r) ≅ O(r)`; the eight-step chain; **Theorem 24.7** (`πᵢ O(n) ≅ π_{i+8} O(n′)` for `i + 2 ≤ n`, `i + 10 ≤ n′`) | `Morse/Chapter15/{TotallyGeodesic,OmegaManifold,OmegaMinimal,OmegaRetract,OmegaKilling,OmegaIntertwiners,InvariantSplitting,SplittingClifford,SplittingData,IndexBound,FiniteStage,Winding,OmegaWinding,SplittingTwo,SplittingTwoData,KillingTwo,IndexBoundTwo,FiniteStageTwo,Stabilization,EightCommutant,OmegaEight,BottChain,StablePeriodicity,OmegaComponents}.lean` (`Morse.theorem_24_3`, `Morse.theorem_24_5_two_six`, `Morse.bott_periodicity_finite`, `Morse.theorem_24_7`) | proved as bijections of pointed sets (group isomorphisms not done); the limit spaces `Ω_k` and the table of `πᵢ O` not formalized; Lemma 24.8 only for `k ≤ 8`, enough for periodicity |
| The bundles of §§23–24: local sections of orbit maps give local trivializations (Steenrod §7); `U(m) → U(m+k) → V_k(𝕜^{m+k})`, Stiefel → Grassmannian, `U(m+1) → S^{2m+1}` and the orthogonal analogues, for `𝕜 = ℂ, ℝ` at once; connectivity of Stiefel manifolds; **Lemma 23.4** (stability `πᵢ U(m) ≅ πᵢ U(m+k)` for `i < 2m`; `π_{j+1} G_m(ℂ^{2m}) ≅ πⱼ U(m)` for `j + 1 ≤ 2m`, as groups for `j ≥ 1`), `πᵢ SU ≅ πᵢ U` (`i ≥ 2`), `πᵢ SO ≅ πᵢ O` (`i ≥ 1`); the Grassmannian of projections as `Stiefel/U(m)` and as the space of `m`-dimensional subspaces | `Morse/Homotopy/{Homogeneous,Stiefel,Grassmannian,BundleHomotopy,BundlesUnitary,BundlesOrthogonal,GrassmannianQuotient}.lean` (`Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl_complex`, `Morse.Homotopy.grassmannianPiEquiv`, `Morse.Homotopy.stiefelQuotientHomeomorph`) | proved |
| **Audit** (`RoundTrip/`): blind Lean statements of Milnor's results written without sight of the formal ones, and machine-checked implications with the formal statements, scored against the comparison's labels; a no-peeking checker (`#rt_check`) and the definition closure of the headline theorems (`#rt_defs`) | `RoundTrip/{Check,Glue,Bridge}.lean`, `RoundTrip/Blind/`, `RoundTrip/Items/`, `RoundTrip/REPORT.md`, `RoundTrip/RESUME.md` | complete (2026-10-05): layer 1, all 348 labelled items round-tripped, §§8–19 also in the embedded special case through `RoundTrip/Bridge.lean`; layer 2, the 116 textbook notions under the numbered theorems checked against blind textbook definitions (`RoundTrip/L2/`); layer 3, failure labels (`RoundTrip/layer3_labels.json`) |

## Design decisions

**Built on the Milnor project.** Everything that *Topology from the Differentiable Viewpoint*
already proves is imported, not reproved: Hadamard's lemma (`Milnor.exists_hadamard`), the
inverse function theorem on manifolds, Sard's theorem, slice submanifolds and their normal
bundles, the ε-neighbourhood theorem, and the Poincaré–Hopf theorem with the index of a
non-degenerate zero.

**The Morse lemma by one application of the inverse function theorem.** Milnor diagonalizes the
Hessian family by induction, taking square roots of smooth functions. Here the change of
coordinates is found in one step. The map `T ↦ B₀(T·,T·) + B₀(T·,·) − B₀(·,T·)` has invertible
derivative at the identity, so the inverse function theorem gives a smooth family `T(x)` with
`B₀(T(x)·, T(x)·) = B(x)`. Sylvester's law, from Mathlib, then gives the `±Σyᵢ²` form, with λ the
index of the Hessian (`Morse.morse_lemma`, `Morse.index_eq_of_morse_chart`).

**The index is Mathlib's `sigNeg`.** Milnor's definition, the maximal dimension of a subspace on
which the Hessian is negative definite, is proved equal to Mathlib's `sigNeg` of the quadratic
form (`Morse.index_isGreatest`).

**Smooth dependence on initial conditions via the inverse function theorem in `C([0,1], E)`.**
Milnor quotes the smooth dependence of solutions of ODEs on initial conditions as "well known"
(p. 10); Mathlib (v4.33.1) has local existence and uniqueness but no smooth dependence. The flow
line through `x` on `[0, 1]` is the solution of `Ψ(γ) = x`, `Ψ(γ) = γ − ∫₀^· X(γ)`. When `X` has
Lipschitz constant `c < 1`, `Ψ` is a homeomorphism of `C([0,1], E)` with everywhere invertible
derivative (Neumann series), and the Nemytskii operator `γ ↦ X ∘ γ` is as smooth as `X`, so
`Ψ⁻¹` and hence the time-one map are smooth (`Morse/Flow/{Nemytskii,Volterra,Smooth}.lean`).
General times follow by `φ_t = (φ_{t/N})^N`, and joint smoothness in `(t, x)` from the flow of
`(x, τ) ↦ (ρ(τ) X(x), 0)` on `E × ℝ`. Milnor's iteration of `φ_{ε₀/2}` is replaced by
Picard–Lindelöf on arbitrarily long intervals, which bounded fields allow.

**What we found in the book.** The main point is Milnor's proof of Theorem 17.1: as we read it, his
map `h` (p. 94) is not continuous, with a machine-checked counterexample
(`Morse.milnor_h_not_continuous`); the theorem itself is proved by a modified argument. Smaller
ones: in example (d) of p. 9 the critical set of `x²`, which the text calls the `x`-axis, is the
`y`-axis; Theorem 16.3 needs `a` not a critical value. The full list
is `Exposition/Findings.md`.
