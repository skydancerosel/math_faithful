# Milnor project: development log

The dated record of the formalization of *Topology from the Differentiable Viewpoint*, moved
here from the README on 2026-10-12. Counts and "Next" items are as of each entry; the README has
the current state.

## Status table (2026-09-08, chapters 1–5 only)

| Milnor | File | Status |
|---|---|---|
| §1 p. 4, inverse function theorem (manifold form, used p. 7) | `Milnor/Chapter1/InverseFunction.lean` | proved |
| §1 pp. 7–8, regular points / values, critical points / values | `Milnor/Chapter1/RegularValue.lean` | proved |
| §1 p. 8, `f⁻¹(y)` finite for `M` compact, `y` regular | `Milnor/Chapter1/RegularValue.lean` | proved |
| §1 p. 8, `#f⁻¹(y)` locally constant | `Milnor/Chapter1/RegularValue.lean` | proved |
| §1 p. 9, the counting argument | `Milnor/Chapter1/Counting.lean` | proved |
| §1 p. 8, the compact surface `S²` | `Milnor/Chapter1/RiemannSphere.lean` | proved, as `ℂ ∪ {∞}` (see below) |
| §1 pp. 8–9, fundamental theorem of algebra | `Milnor/Chapter1/FTA.lean` | proved |
| §1 pp. 1–7, manifolds as subsets of `ℝᵏ`, tangent spaces | — | not started (see below) |
| §3 pp. 16–19, **Sard's theorem** | `Milnor/Chapter3/*.lean` | proved |
| §2 p. 10, regular values dense in `ℝᵖ` | `Milnor/Chapter3/Sard.lean` | proved |
| §2 p. 11, **Brown's corollary** on manifolds | `Milnor/Chapter2/Brown.lean` | proved |
| submanifolds via slice charts (infrastructure for §2) | `Milnor/Chapter2/Submanifold.lean` | proved |
| §2 pp. 11–12, Lemmas 1–2 (preimage of a regular value is a submanifold; its tangent space is `ker df`) | `Milnor/Chapter2/LevelSet.lean` | proved |
| manifolds with boundary via half-slice charts; half-space model with corners (infrastructure for §2) | `Milnor/Chapter2/Boundary.lean` | proved |
| §2 pp. 12–13, Lemmas 3–4 (`{g ≥ 0}` has boundary `g⁻¹(0)`; level sets in a manifold with boundary) | `Milnor/Chapter2/WithBoundary.lean` | proved |
| §2 p. 12, the disk `Dᵐ` has boundary `Sᵐ⁻¹` | `Milnor/Chapter2/Disk.lean` | proved |
| §2 pp. 13–15, Brouwer fixed point theorem | `Milnor/Chapter2/{Corestrict,Retraction,Brouwer}.lean` | proved |
| §4 pp. 20–21, Lemma 4 for the cylinder, the Homotopy Lemma | `Milnor/Chapter4/{Cylinder,Homotopy}.lean` | proved |
| §4 p. 22, the Homogeneity Lemma (via bump diffeomorphisms, not flows) | `Milnor/Chapter4/{BumpDiffeo,Homogeneity}.lean` | proved |
| §4 pp. 21–23, Theorems A and B, the degree mod 2, nonzero degree ⇒ onto | `Milnor/Chapter4/Degree.lean` | proved |
| §5 p. 26, orientations of manifolds, sign of a derivative (infrastructure) | `Milnor/Chapter5/{OrSign,Orient,DegreeAt}.lean` | proved |
| §5 p. 27, Lemma 1 (ambient form, boundary presented by a function) | `Milnor/Chapter5/{ChartFun,MonoAt,LevelArc,ArcSign,LemmaOne}.lean` | proved |
| §5 p. 28, Theorems A and B, the Brouwer degree | `Milnor/Chapter5/{HomotopyInv,Degree}.lean` | proved |
| §5 pp. 29–30, boundary orientation of a level set, the antipodal map, the hairy ball theorem | `Milnor/Chapter5/{LevelOrient,HairyBall}.lean` | proved |

No `sorry`. Every theorem depends only on `propext`, `Classical.choice`, `Quot.sound`
(check with `lake env lean Milnor/Test.lean`).

Expanded prose for each chapter is in `Exposition/` (Markdown source; PDF built with pandoc and
XeLaTeX; web pages with interactive figures published as artifacts). From chapter 4 on the prose
is the primary deliverable: chapters are written around a physical question and an application,
with Milnor's proofs complete, and Lean is used only as a silent check where it is cheap.
Chapter 4 (`Exposition/Chapter4.md`): the degree modulo 2, the homotopy and homogeneity lemmas in
full, an interactive version of Milnor's Figure 6, and the odd-number theorem for gravitational
lenses. Chapter 4 is now fully formalized (see "Chapter 4 verified" below).

Chapters 1–3 were rewritten (2026-09-08) in the same exposition-first mode as chapter 4, and the
former combined "Chapters 2 and 3" file was split. Each chapter opens with a physical question,
proves Milnor's results in full, carries one interactive figure in the web edition (static in the
PDF), and closes with an application: chapter 1 the two-link robot arm (`Exposition/Chapter1.md`,
`fig1-arm.png`), chapter 2 Brouwer via the crumpled map and stationary distributions of Markov
chains (`Exposition/Chapter2.md`, `fig2-brouwer.png`), chapter 3 caustics on a pool floor and the
rainbow as a critical value (`Exposition/Chapter3.md`, `fig3-caustic.png`). Lean identifiers no
longer appear in the prose; each chapter ends with a one-paragraph note saying which results are
machine-checked. Build: `python3 build.py 1 2 3` in the session scratchpad (pandoc + XeLaTeX,
matplotlib for the static figures).


## Sard's theorem: layout of the proof

Milnor's §3, coordinate-free, with the induction on `n = dim E` running over abstract
finite-dimensional real normed spaces so that hyperplanes need no coordinates.

| File | Content |
|---|---|
| `Chapter3/Basic.lean` | critical set `C`, the sets `Cₖ`; `C` closed in `U` (surjectivity is open); a set of Hausdorff dimension `< dim F` is Haar-null; the induction statement |
| `Chapter3/Step3.lean` | Taylor-type bound by induction on `k` from the mean value inequality; `f(Cₖ ∩ K)` null via Hölder maps and Hausdorff dimension (replaces Milnor's cube count) |
| `Chapter3/Straighten.lean` | Milnor's `h(x) = (w(x), x₂, …, xₙ)`, coordinate-free, via the manifold inverse function theorem of chapter 1 |
| `Chapter3/Step2.lean` | `f(Cₖ ∖ Cₖ₊₁)` null; the countable-cover lemma |
| `Chapter3/Step1.lean` | `f(C ∖ C₁)` null: splitting of the target, the block-matrix remark, Fubini |
| `Chapter3/Sard.lean` | the induction; `sard` and the density corollary |

## Design decisions

**Abstract manifolds, not subsets of `ℝᵏ`.** Milnor's manifolds are subsets `M ⊆ ℝᵏ` with local
parametrizations; Mathlib's are abstract spaces with charts. All statements here are in Mathlib's
language so that they can be upstreamed. Milnor's §1 pp. 1–7 (tangent spaces as images of `dgᵤ`,
well-definedness of `dfₓ`) becomes, in this setting, a *bridge*: a submanifold of `ℝᵏ` in Milnor's
sense is a manifold in Mathlib's sense, and the two notions of tangent space and derivative agree.
That bridge is not yet written.

**Hausdorffness is assumed where Milnor uses it silently.** Subsets of `ℝᵏ` are automatically
Hausdorff; abstract manifolds are not. `T1Space N` is needed for `f⁻¹(y)` to be closed, and
`T2Space M`, `T2Space N` for the local-constancy argument. Each theorem states exactly what it
needs.

**Regular point means `dfₓ` surjective** (Milnor's §2 definition) from the start. In the
same-dimension case this is equivalent to `dfₓ` invertible (Milnor's §1 definition);
`IsRegularPoint.isInvertible_mfderiv` proves the equivalence.

**The manifold inverse function theorem is new.** Mathlib (v4.33.1) proves the Euclidean inverse
function theorem but lists the manifold version as a TODO. `InverseFunction.lean` proves it. One
subtlety it exposes: for `C^∞` maps, Mathlib's "smooth at `x`" does not imply smooth on a
neighbourhood of `x`, so the theorem assumes smoothness on a neighbourhood. For Milnor, whose maps
are smooth everywhere, this costs nothing.

**`S²` is modelled as the Riemann sphere `ℂ ∪ {∞}`.** Milnor uses the unit sphere in `ℝ³` and
stereographic projection only as a device to compactify `ℂ`. We use Mathlib's one-point
compactification `OnePoint ℂ` with charts `z` and `1/z`. This is the same manifold, and it
removes the complex conjugation from Milnor's formula for `Q`: the polynomial read in the chart
`1/z` at both ends is `wⁿ / P̃(w)` with `P̃` the reversed polynomial. The diffeomorphism
`S² ≃ ℂ ∪ {∞}` given by stereographic projection is a natural later addition but is not needed.

**Submanifolds are defined by slice charts.** Milnor never needs a general notion of submanifold:
his Lemma 1 produces, around each point of `f⁻¹(y)`, a diffeomorphism under which `f⁻¹(y)` is a
linear slice. `Milnor.IsSliceSubmanifold` takes exactly that as the definition, and
`Milnor/Chapter2/Submanifold.lean` turns it into a Mathlib manifold structure once and for all.
Manifolds with boundary are handled the same way (`Milnor.IsHalfSliceSubmanifold`), with the
half-space `{(t, z) | t ≥ 0} ⊆ ℝ × Z` as the model with corners. A half-slice chart is required to
send exactly the designated boundary set to `{t = 0}`, so Milnor's "it is not hard to show that
`∂X` is well defined" (an invariance-of-domain statement) is never needed and is not proved.

**Sard's theorem is stated for smooth (`C^∞`) maps**, as in Milnor. Steps 1 and 2 use derivatives
of all orders in the induction, so tracking the sharp differentiability class `C^{n-p+1}` was
not attempted.

**Step 3 uses Hausdorff dimension instead of Milnor's cube count.** The Taylor bound shows `f` is
Hölder of exponent `k+1` on `Cₖ ∩ K`; Mathlib knows that Hölder maps divide Hausdorff dimension.
Milnor's cube subdivision is exactly the proof of that fact, so this is a reuse, not a different
argument.

## Statements to sign off (for a mathematician who does not read Lean)

Each is stated in ordinary language; the Lean name is given so a Lean reader can check the match.

1. `Milnor.isLocalDiffeomorphAt_of_isInvertible_mfderiv`. Let `M`, `N` be `C^n` manifolds without
   boundary modelled on Banach spaces over `ℝ` or `ℂ`, `n ≥ 1`, and `f : M → N` be `C^n` on a
   neighbourhood of `x`. If `df_x` is a continuous linear isomorphism, then `f` restricts to a
   `C^n` diffeomorphism from an open neighbourhood of `x` onto an open neighbourhood of `f(x)`.
2. `Milnor.IsRegularValue.finite_preimage`. Let `M`, `N` be manifolds of the same finite
   dimension, `M` compact, `N` `T1`, `f : M → N` smooth, `y` a regular value. Then `f⁻¹(y)` is
   finite.
3. `Milnor.IsRegularValue.eventually_ncard_preimage_eq`. Same hypotheses with `M`, `N` Hausdorff.
   Then there is a neighbourhood `V` of `y` such that `#f⁻¹(y') = #f⁻¹(y)` for every `y' ∈ V`
   (not only for regular `y'`; this is what Milnor's proof gives).
4. `Milnor.subset_range_of_isPreconnected`. Same hypotheses. If `R` is a connected set of regular
   values and some point of `R` is in the image of `f`, then all of `R` is in the image of `f`.
5. `Milnor.RiemannSphere.instIsManifold`. `ℂ ∪ {∞}` with the charts `z` and `1/z` is a smooth
   real 2-manifold.
6. `Milnor.RiemannSphere.contMDiff_polyMap`. A nonconstant polynomial, extended by `∞ ↦ ∞`, is a
   smooth map `ℂ ∪ {∞} → ℂ ∪ {∞}`.
7. `Milnor.fundamental_theorem_of_algebra`. Every complex polynomial of positive degree has a root.
8. `Milnor.sard`. Let `E`, `F` be finite-dimensional real normed spaces, `U ⊆ E` open, `f : U → F`
   smooth, `C` the set of points of `U` where `df` is not surjective. Then `f(C)` has measure zero
   for every Haar measure on `F`.
9. `Milnor.dense_regularValues`. Let `M`, `N` be smooth manifolds without boundary, `M` second
   countable, and `f : M → N` smooth. Then the set of `y ∈ N` such that `df_x` is surjective for
   every `x ∈ f⁻¹(y)` is dense in `N`.
10. `Milnor.isSliceSubmanifold_preimage`. Let `f : M → N` be smooth between boundaryless
    manifolds of dimensions `m ≥ n`, and `y` a regular value. Then `f⁻¹(y)`, with the subspace
    topology, is a smooth manifold of dimension `m - n` (charts: the `ℝᵐ⁻ⁿ`-component of Milnor's
    map `F = (f, L)`), and the inclusion `f⁻¹(y) → M` is smooth.
11. `Milnor.mem_range_mfderiv_val_iff`. In that situation, a vector `v ∈ TMₓ`, `x ∈ f⁻¹(y)`, is
    tangent to `f⁻¹(y)` (is the image of a tangent vector of `f⁻¹(y)` under the inclusion) if
    and only if `dfₓ(v) = 0`.
12. `Milnor.isHalfSliceSubmanifold_of_regularValue`. Let `g : M → ℝ` be smooth on a boundaryless
    manifold with `0` a regular value. Then `{g ≥ 0}` is a smooth manifold with boundary in
    Mathlib's sense, and its boundary is exactly `g⁻¹(0)`.
13. `Milnor.isHalfSliceSubmanifold_levelSet`. With `X = {g ≥ 0}` as above, `f : M → N` smooth,
    `y` a regular value of `f`, and, at every point of `f⁻¹(y) ∩ g⁻¹(0)`, some vector killed by
    `df` but not by `dg` (Milnor's "regular for `f|∂X`"), the set `f⁻¹(y) ∩ X` is a manifold
    with boundary `f⁻¹(y) ∩ g⁻¹(0)`.
14. `Milnor.isHalfSliceSubmanifold_unitDisk`. The closed unit ball in `ℝᵐ⁺¹` is a manifold with
    boundary the unit sphere.

## Next

* Appendix (classification of compact 1-manifolds: finite unions of circles and closed
  intervals, hence an even number of boundary points), then Brouwer (§2, Lemmas 5–6, plus
  Weierstrass approximation). This is the one remaining hole in chapters 1–3.
* Chapter 4 (mod 2 degree), which needs only what is now proved plus the homotopy lemma.
* Milnor §1 pp. 1–7 as a bridge from embedded submanifolds of `ℝᵏ` to Mathlib manifolds.

## The whole book, in exposition-first mode (2026-09-08, evening)

`Exposition/` now covers all of Milnor: Chapter1–8.md, Appendix.md, each with a PDF and a web
edition, plus Roadmap.md (a planning document on formalizing the compactness theorems of
geometric analysis). Chapters 5–7 follow the same pattern as 1–4: physical opening (calm point of
the wind; the weather-map identity H + L − C = 2; the north curve of a magnetization texture), all
of Milnor's proofs in full, one interactive figure (signed crossings; a spinning globe of random
weather with its highs, lows and cols found numerically; the Pontryagin manifold of a torus
direction field), and an application (quantized superfluid circulation; nematic-shell defects;
skyrmions and hopfions). Chapter 8 solves all seventeen of Milnor's problems. The Appendix proves
the classification of 1-manifolds. None of chapters 4–8 or the Appendix is formalized; chapters
1–3 are. Build: `python3 build.py 1 2 3 5 6 7 A 8 R` in the session scratchpad after
`python3 figs.py; python3 figs2.py`.

## Appendix verified (2026-09-16)

`Milnor/Appendix/OneManifold.lean` (1,704 lines) proves, for a compact Hausdorff *topological*
1-manifold with boundary (charted space modelled on a homeomorphic copy of `[0,∞)`, boundary
compatible with every chart), that the boundary is finite with an even number of points
(`Milnor.OneManifold.even_ncard_boundary`). `Milnor/Appendix/HalfSpace.lean` specializes this to
the half-slice submanifolds of Chapter 2 over a zero-dimensional `Z`
(`Milnor.IsHalfSliceSubmanifold.even_ncard_boundary`). Proof strategy differs from Milnor's:
arcs (homeomorphisms onto intervals) instead of arc-length parametrizations; the overlap of an
arc from a boundary point with any arc is an interval (no circle case); finite-cover induction
instead of Zorn; parity via a fixed-point-free involution. Axioms: propext, Classical.choice,
Quot.sound. `Exposition/Verification.md` is the "machine-checked edition" report.
Next: Lemmas 5–6 and Brouwer (needs corestriction into slice submanifolds and Lemma 4 for maps
on open neighbourhoods).

## Brouwer verified (2026-09-16)

`Milnor/Chapter2/Corestrict.lean` (corestriction of smooth maps to slice submanifolds),
`Retraction.lean` (Milnor's Lemma 6 formula: smooth, norm one, fixes the sphere, defined on the
disk when there is no fixed point), `Brouwer.lean` (`exists_fixedPoint_of_contDiff`: smooth
Brouwer via Lemma 4 + the Appendix, with the retraction extended to all of `E` by a smooth cutoff
and the auxiliary model spaces taken as subspaces of `E` because Sard/Brown force equal universes;
`exists_fixedPoint`: continuous Brouwer via Stone–Weierstrass on the subalgebra of smooth
functions). Total 6,116 lines, standard axioms. Next: chapter 4 (Lemma 4 on cylinders, homogeneity
via bump diffeomorphisms, deg mod 2).

## Chapter 4 verified (2026-09-16)

`Milnor/Chapter1/RegularValue.lean` gained `eventually_isRegularValue_and_ncard` (regular values
near a regular value are regular with the same count). `Milnor/Chapter4/Cylinder.lean`: Lemma 4
with two boundary functions (`isHalfSliceSubmanifold_levelSet_two`), glued from the one-function
version by a locality lemma. `Homotopy.lean`: the transversality condition at the ends of the
cylinder and the Homotopy Lemma (`homotopy_lemma`), homotopies being smooth maps on `M × ℝ`.
`BumpDiffeo.lean`: `u ↦ u + φ(u) • c` is a diffeomorphism of the model space (Lipschitz
injectivity, contraction-principle surjectivity, inverse function theorem for the inverse).
`Homogeneity.lean`: transport through `extChartAt`, the `Isotopic` relation (refl/trans/symm),
local homogeneity, and `isotopic_of_preconnected` (the Homogeneity Lemma). `Degree.lean`:
Theorem B (`even_ncard_add_ncard_of_isRegularValue`), `degMod2 : ZMod 2`, Theorem A
(`degMod2_eq_of_homotopy`), `surjective_of_degMod2_ne_zero`. Total 7,075 lines, standard axioms
(13 theorems checked in `Test.lean`). Next: chapter 5 (orientations, Brouwer degree), the largest
piece of missing infrastructure.

## Chapter 5 verified (2026-09-16)

Orientations are defined from scratch (Mathlib has none on manifolds): `Milnor/Chapter5/OrSign.lean`
(the sign of a linear map between oriented spaces via top forms; product orientation of `E × ℝ`;
block formulas), `Orient.lean` (`Orient I M n`: chart-continuous choice of tangent orientations;
`signAt`; local constancy near a regular point), `DegreeAt.lean` (`degAt`, locally constant).
Lemma 1 is proved in ambient form (`lemmaOne_ambient`: signed count of `(f, g)` over
`f⁻¹(y) ∩ {g = 0}` vanishes) via chart functions along the level-set arcs (`ChartFun`, `MonoAt`,
`LevelArc`, `ArcSign`, `LemmaOne`). `HomotopyInv.lean`: Theorem A on the cylinder `{t(1-t) ≥ 0}`.
`Degree.lean`: isotopies (now with every slice a diffeomorphism, `Isotopic` strengthened in
chapter 4) preserve orientation, Theorem B, `deg`, homotopy invariance, surjectivity, `deg_id`.
`LevelOrient.lean`: the boundary orientation of `g⁻¹(0) ⊆ E` is chart-continuous.
`HairyBall.lean`: the sphere as an oriented compact connected manifold, `deg_antip = (-1)^(n+1)`,
`hairy_ball` (even `n`, smooth fields) and its converse `exists_nonvanishing_field`. Total
10,148 lines, 20 theorems in `Test.lean`, standard axioms.

## Chapter 6 verified (2026-09-16)

`Milnor/Chapter6/`: `Index.lean` (index of an isolated zero as the degree of the sphere map;
radius and homotopy invariance), `Extend.lean` (extension of a local field by a cut-off),
`LevelOrientM.lean` / `LevelSignM.lean` / `LevelZero.lean` (the level-set orientation on any
manifold with Euclidean charts, the bridge lemma, Lemma 1 of §5 in boundary form on an open
set, `Orient.neg`, product rule), `LevelMap.lean` (`signAt_levelOrientM_map'`: sign of a map
between level sets = sgn c × ambient sign), `Compose.lean` / `SignLemmas.lean` / `Opens.lean` /
`RegularOpen.lean` (degree of compositions with bijections, open-subset bookkeeping, regular
values open and dense), `Region.lean` (`sum_indexAt_eq_deg`: index sum = degree over the
boundary of a region), `Hopf.lean` (`hopf_lemma`), `DetSign.lean` / `Radial.lean` /
`Invariance1.lean` / `Invariance.lean` (Milnor's Lemma 1 `index_eq_of_diffeo`, with Lemma 2
replaced by the sign computation `signAt_nv0_linear` for the radial map), `Tubular1–4.lean`
(the ε-neighbourhood theorem `Tub.tubular` by the nearest-point equation and the inverse
function theorem; the region `N_{ε/2}` and the extended field), `PoincareHopf.lean`
(`Tub.indexN`, `Tub.poincare_hopf`: for a compact submanifold of ℝ^{K+1} there is an integer
equal to the index sum of every tangent field with finitely many zeros). Not formalized: Lemma
2, the chart definition of the index, the Euler characteristic. Total 15,261 lines, 29 theorems
in `Test.lean`, standard axioms. Next: chapter 7 (framed cobordism).

## Chapter 7 verified through Theorems A and B (2026-09-17)

`Milnor/Chapter7/` (8,957 lines, 35 files): framed submanifolds and framed cobordism
(`Framed.lean`: cobordisms are submanifolds of `M × ℝ` with product ends), the Pontryagin
manifold with the pseudo-inverse framing (`Pontryagin.lean`), Lemma 3 (`Cobordism.lean`),
smooth path-connectivity of `GL⁺` and Lemma 1 (`GLplus.lean`, `BasisPath.lean`, `Lemma1.lean`),
framed cobordism as an equivalence relation (`Transport.lean`, `Equiv.lean`), rotations of the
sphere, openness of regular values and Lemma 2 (`Rotation.lean`, `RegOpen.lean`, `Compose.lean`,
`RotHomotopy.lean`, `Lemma2.lean`), Theorem A first half (`ThmA.lean`), the product
neighbourhood theorem (`ProdNbhd.lean`, `ProdNbhd2.lean` abstract; `ProdNbhdM.lean`,
`TubeData.lean`, `ProdNbhdS.lean` concrete; `Clamp.lean`), the collapse map (`StdMap.lean`,
`Collapse.lean`), identification of the framing (`PontFrame.lean`, `Identify.lean`), Theorem B
(`ThmB.lean`), the uniform Taylor estimate (`Taylor.lean`), the stereographic straight-line
homotopy (`Stereo.lean`), smooth homotopy as an equivalence relation (`Homotopy.lean`), Lemma 4
(`Deform.lean`, `SamePont.lean`), the map of a cobordism (`CobMap.lean`) and Theorem A second
half (`ThmAconv.lean`). Not yet: the Hopf theorem. Total 24,234 lines, 48 theorems in
`Test.lean`, standard axioms. See `Exposition/Verification.md` §8.

## Chapter 7 complete: the Hopf theorem (2026-09-17)

The Hopf theorem (`Milnor/Chapter7/Hopf.lean`: `hopf_homotopic`, maps of equal degree are
smoothly homotopic; `exists_map_of_deg`, every integer is a degree) for compact connected
oriented `M ⊆ ℝᴷ⁺¹` of dimension `m ≥ 1`. Supporting files (4,903 lines): `Hopf0.lean` (sign
of a framed point, signed count = degree), `ThmBsupp.lean`/`Scale.lean` (Theorem B with control
of the support), `Glue.lean` (gluing a chart-local homotopy), `Neighbour.lean`/`Segment.lean`/
`Chain.lean` (the neighbour lemma in a connected space, chains), `TuplePath.lean`/`MoveMap.lean`/
`MoveAux.lean`/`MoveH.lean`/`Move.lean` (moving a framed point), `CancelMap.lean`/`CancelH.lean`/
`Cancel.lean`/`CancelStep.lean` (cancelling a pair), `Reach.lean` (reaching a component),
`Gather.lean` (gathering along chains), `Main.lean` (equal counts ⇒ framed cobordant),
`AddPoint.lean` (adding a point), `Chapter5/OrSignAlg.lean` (orientation-sign algebra).
Chapter 7: 56 files, 13,784 lines. Total 29,137 lines, 55 theorems in `Test.lean`, standard
axioms. See `Exposition/Verification.md` §8 (V7.12–V7.17).

## Chapter 8 complete: the seventeen problems (2026-09-17)

All seventeen problems of Milnor §8 are formalized in `Milnor/Chapter8/` (namespace
`Milnor.Problems`; 31 files, 16,166 lines). Main results, by problem: 1 `deg_comp`; 2
`deg_polyMap`; 3 `homotopic_of_norm_sub_lt_two`; 4–5 `exists_smooth_approx`,
`smoothHomotopic_of_homotopic`, `exists_homotopic_const_of_lt`; 6–7 `exists_fixedPoint_of_deg_ne`,
`exists_antipodal_of_odd_deg`; 8–9 `isSliceSubmanifold_prod`, `isSliceSubmanifold_graph`; 10
`isSliceSubmanifold_tangentBundle`, `tangentMap_comp`; 11 `exists_normalTube_diffeomorph`; 12
`normalRetraction_nearest`, `smoothHomotopic_of_homotopic_mfld`; 13 `linkingNumber_symm`,
`linkingNumber_eq_zero_of_bounds`, `linkingNumberSph_eq`; 14 `linkPre_self_eventually_eq`,
`linkPre_eq_of_norm_lt`, `linkPre_eq_hopfInvariant`, `hopfInvariant_eq_of_smoothHomotopic`; 15
`hopfInvariant_eq_zero_of_odd`, `hopfInvariant_comp`, `hopfInvariant_hopfMap`; 16
`isSliceSubmanifold_inter`, `exists_transverse_deformation`; 17 `exists_intersection_product`,
`cohomotopyGroup`.

Tools built along the way: local zero sets of submersions (`LocalSlice.lean`), local degrees with
compact preimages (`ProperDegree.lean`), product orientations (`OrientProd.lean`), frame
orientations and Milnor's orientation of the sphere as a boundary (`OrientFrame.lean`),
genericity lemmas (`Generic.lean`), preimage orientations (`PreimOrient.lean`), linking numbers as
local degrees (`LinkAlg.lean`, `LinkDegree.lean`).

Findings: with the book's conventions taken literally, the Hopf fibration has Hopf invariant −1,
not 1 (checked by hand, numerically, and in Lean; `HopfSign.lean`). Hidden hypotheses: `k > 0`
for linking numbers, positive dimensions for linking numbers in the sphere, `p ≥ 2` for the Hopf
invariant, `p, q ≥ 1` for the intersection product. The mixed form of Problem 14 a) (two
different maps) needs the preimages disjoint; Milnor's single-map form does not.

Project: 45,303 lines; `lake build` passes (8,856 jobs); `Milnor/Test.lean` checks 103 theorems,
all depending only on the standard axioms. See `Exposition/Verification.md` §9 (V8.0–V8.17′,
sign-off items 63–83).

## The proof in words (2026-09-18)

`Exposition/ProofByProof.md` (PDF: `ProofByProof.pdf`, 142 pages) is *Milnor, proof by proof*: the
formal proofs of all of Milnor, the Appendix and the seventeen problems, retold as mathematics
(about 80,000 words: a prologue, Part 0 and Parts I to XII). Part 0 defines everything the book
uses from scratch: charts, atlases, smooth maps, the derivative `mfderiv`, tangent spaces,
submanifolds, regular values, orientations, degrees, homotopies and framed cobordisms, each as
Mathlib or this project actually defines it. Every
step of substance carries a trace tag `⟦File · declaration⟧`; the 1,810 tags cite 1,236 distinct
declarations and are resolved mechanically against the sources (0 unresolved; rerun with
`python3 Exposition/check_trace.py Exposition/ProofByProof.md`). The concordance at
the end lists each cited declaration with its line and its exact formal statement. Twelve writers
drafted the parts from the Lean sources; six independent reviewers checked each part against the
code and against Milnor's text.

Writing it was also an audit. `Exposition/Verification.md` was corrected throughout: Milnor's own
theorem letters (§4, §5, §7), missing hypotheses (Hausdorff, preconnected, nonempty, dimension
conditions), wrong cross-references, the sign (−1)^{n+1} in V5.3, the converse field in V5.10, the
size paragraphs, and informal remarks now flagged as not machine-checked. Sign-off items 9, 10, 15,
16, 20, 36, 38, 41 and 44 changed wording and need re-signing; unsigned items 45, 49, 55, 57–60, 62
and 82 were reworded. The retelling's "Checked by machine" notes (Chapters 2, 4–8, Appendix) and
the sign in Chapter 8, Problem 15 were updated, and all PDFs rebuilt. Stale Lean docstrings, old
theorem letters in file names, and unneeded hypotheses are listed in `DocstringErrata.md`; none
affects a proof.

## Milnor beside Lean: the comparison edition (2026-09-28)

`Exposition/Comparison.md` puts every result of the book beside the statement that was actually
proved. 111 rows: the 110 verified items V1.1 to V8.17′, each with Milnor's statement in his own
terms and page, the formal statement with every hypothesis written out, and a strip naming what
differs; plus one thing the book states that the formalization does not prove. 366 declarations
are cited and every one was resolved mechanically in the sources.

The kind of difference is labelled: as in the book 1, hypotheses explicit 21, stronger 22,
narrower 13, restated 31, not in the book 21, value differs 1 (the Hopf invariant of the Hopf
fibration, −1 against Milnor's +1), not formalized 1. The web edition
(`Exposition/milnor-beside-lean.html`, built by `Exposition/build_comparison.py` from
`Exposition/Comparison.json` and `Exposition/comparison-head.html`) puts the two statements in
columns, filters by label, searches the text, and opens the exact Lean statement with its file and
line when a declaration is clicked.

Nine writers drafted the rows from the book PDF, the verified edition and the Lean sources. Their
reading corrected the verified edition again, in eleven places: Milnor's Lemma 4 of §7 is on p. 47,
the transversality sentence quoted in V4.2 is not in the book, the second clause of Lemma 2 of §2
(the orthogonal complement) is not formalized, V5.3 leaves Milnor's reduction to V5.4, the sign of
the antipodal map holds for every n ≥ 0 while its degree needs n ≥ 1, the ε-neighbourhood theorem
is Problems 11 and 12 on p. 52, Poincaré–Hopf is proved for finitely many zeros where Milnor
assumes them nondegenerate (his Lemma 5 is not formalized), Milnor's framings are defined on
p. 41, and his proof of Theorem A of §7 omits the step that Lemma 1 supplies. Sign-off items 32 and
41 were expanded and need re-signing with 9, 10, 15, 16, 20, 36, 38, 41 and 44. Seven wrong page
citations in Lean docstrings are listed in `DocstringErrata.md`.

## The leftovers formalized (2026-09-28)

`Leftovers.md` tracks the six things the book states that the formalization did not prove, listed as
rows G.1 to G.6 of the comparison edition. Five of the six are now closed, and the sixth has its
first two stages done.

New files, in the order they were written:

| what | file | lines |
|---|---|---|
| Lemma 2 of §2, second clause (p. 11) | `Chapter2/Normal.lean` | 142 |
| Lemma 4 of §6, the index at a non-degenerate zero (p. 36) | `Chapter6/Nondegenerate.lean` | 262 |
| Hadamard's lemma, and smoothness of a parametric integral | `Chapter6/Hadamard.lean` | 199 |
| Lemma 2 of §6, isotopy to the identity (p. 33) | `Chapter7/Isotopy.lean` | 474 |
| Lemma 5 and the chart definition of the index (pp. 33, 37) | `Chapter6/ChartIndex.lean` | 929 |
| the Poincaré–Hopf integer of `Sⁿ` is `1 + (−1)ⁿ` (p. 39) | `Chapter6/EulerSphere.lean` | 699 |
| orientation transport, chains, transport sections | `Chapter7/OrientTransport.lean` | 494 |
| the chart-level dichotomy, and why its converse needs more | `Chapter7/Orientable.lean` | 364 |
| the exact dichotomy for loops of balls | `Chapter7/OrientBall.lean` | 643 |
| the chart sign, replacing the sign against an orientation | `Chapter7/ChartSign.lean` | 548 |
| the ball-chain sign dictionary, cocycle lemma, avoidance | `Chapter7/BallChainSign.lean` | 780 |
| the punctured-manifold theorem and the punctured dichotomy | `Chapter7/Puncture.lean` | 722 |
| sliding a framed point, and the frame flip | `Chapter7/Slide.lean` | 561 |
| sign-free cancellation | `Chapter7/CancelFree.lean` | 265 |
| the count modulo 2, and the bridge to the mod 2 degree | `Chapter7/CountMod2.lean` | 242 |
| **Milnor's theorem of p. 50** | `Chapter7/HopfMod2.lean` | 259 |
| Appendix Lemma 1 in general form | `Appendix/TwoComponents.lean` | 463 |
| the one-dimensional setup, and `BoundaryCompatible` for free | `Appendix/Smooth/Setup.lean` | 820 |

The headline is the last theorem of §7, which Milnor states without proof: for a closed connected
non-orientable manifold `M` of dimension `m ≥ 2`, two smooth maps `M → Sᵐ` are smoothly homotopic
if and only if they have the same degree modulo 2. Its easy half needs no orientation at all; its
substantial half needs orientations only on the target sphere. The hypothesis `m ≥ 2` is
mathematically vacuous, since a connected one-manifold is orientable, and it enters at exactly one
point, so it can be dropped in one line once the classification of one-manifolds is formalized.

What that took, besides the framed machinery already in place: orientability of a manifold, which
neither Mathlib nor this project had in any form. Transport of an orientation across a chart; the
observation that a loop of charts can reverse an orientation on an orientable manifold, because a
chart domain can be disconnected, with a counterexample on the real line; the exact dichotomy for
loops of round balls, where the transport sign is constant; the chart sign, which replaces "the sign
of a frame against an orientation" by "the determinant sign of a frame read in one chart"; and the
theorem that a connected non-orientable manifold of dimension at least two stays non-orientable
after finitely many points are removed, which is what lets a framed point be slid around a reversing
loop without colliding with the others.

Two smaller things are worth recording. Mathlib has no theorem that an integral over a fixed
interval depends smoothly on a parameter; `Chapter6/Hadamard.lean` proves it, with no
finite-dimensionality and no local compactness, and that is what makes Milnor's isotopy smooth at
`t = 0`. And for smooth one-manifolds the Appendix's compatibility hypothesis, that every chart
sends exactly the boundary points to coordinate zero, is now a theorem rather than an assumption.

Still not formalized: the identification of the Poincaré–Hopf integer with the Euler
characteristic, which needs homology theory Mathlib does not have, and — the one other item —
the agreement of the two definitions of the index at an arbitrary isolated zero, which needs a
suspension formula for the degree that Milnor does not prove either.

The project is now 62,849 lines in 176 files, up from 45,303 in 149. `lake build` passes (8,883
jobs) and `Milnor/Test.lean` checks 175 theorems, every one depending only on propext,
Classical.choice and Quot.sound.

## Milnor's Appendix theorem, and a hypothesis removed (2026-09-28, later)

`Exposition/PlanOneManifold.md` planned the classification of one-manifolds in nine stages and
estimated 4,000 lines; the result is 9,276, in `Appendix/TwoComponents.lean` (463) and the nine
files of `Appendix/Smooth/` (8,813). **A connected Hausdorff σ-compact smooth one-manifold is
diffeomorphic to exactly one of `Circle`, `Icc 0 1`, `Ici 0` and `ℝ`**, and in the project's own
vocabulary every component of a compact one-manifold with boundary is a circle or an interval, the
components with a boundary point are exactly the intervals, each contributes exactly two boundary
points, and the boundary is finite of even cardinality — derived from the classification, with the
pairing realised by the two ends of one arc-length parametrization. The old parity theorem is left
in place, since Chapters 2 and 4 cite it.

All six exclusions are proved, by two invariants: compactness settles four, and the number of
boundary points — a diffeomorphism invariant — settles the remaining one inside each compactness
class. σ-compactness is necessary and is spent at exactly one point, the existence of the length
element: a manifold carrying a Riemannian metric is metrizable, so the long line carries none, and
Milnor's arc length has nothing to start from. He gets the hypothesis free by sitting in Euclidean
space and spends it silently when he restricts the Euclidean metric.

Where the plan was wrong, twice, and both times structurally. The existing topological extension
theorem cannot be reused with smoothness added: its conclusion is an existential that forgets the
witness's coordinate, so it cannot deliver an arc that extends the given one, and it had to be
restated — after which about 75 lines of its proof *disappear*, because with unit-speed arcs the two
branches are the same affine function on the whole overlap and there is no junction to be continuous
at. And the exhaustion by arcs does not exist in the boundaryless case at all, since every arc of a
manifold with empty boundary has an open target while the extension needs a half-open one; the
replacement is to drop injectivity and work with unit-speed *curves* on the line, whose engine is a
propagation lemma: two of them agreeing near one time agree on a whole interval.

With the classification in hand, the last vacuous hypothesis in the project is gone.
`Chapter7/OneManifoldOrientable.lean` (564 lines) orients the four models, transports orientability
along any smooth map with everywhere-invertible derivative, and concludes that every connected
σ-compact smooth one-manifold over a boundaryless model is orientable. So **Milnor's theorem of
p. 50 now carries no dimension hypothesis at all**: for a closed connected non-orientable smooth
`m`-manifold in a Euclidean space, two smooth maps to `Sᵐ` are smoothly homotopic if and only if
they have the same degree modulo 2.

The written record is in step: `Exposition/Verification.md` has items V.B to V.J and V7.27, V7.28,
with sign-off items 100 to 110; `Exposition/Comparison.md` has 111 rows and one remaining gap.
