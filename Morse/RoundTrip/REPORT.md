# Round-trip audit of the comparison labels — report

Status: 2026-10-05. **Layer 1 is complete**: every labelled item of the comparison
(`Exposition/cmp/*.json`, the 30 + 43 items labelled *extra* excluded) has a blind statement of Milnor
(`RoundTrip/Blind/`, 348 files) and a prover record (`RoundTrip/Items/<id>.{lean,json}`); Milnor
§§8–19 also have the *embedded special case* (below). Layer 2 (definitions) and layer 3 (labels)
are reported at the end. Everything compiles with no `sorry`; every proved direction passes
`#rt_check` (or `#rt_check_soft`, noted in the item's JSON).

## Method

For each item:

1. **Blind statement B.** A model shown only Milnor's statement as the comparison quotes it (never
   the project's Lean, the verdict or the exposition) writes Milnor's claim as `RoundTrip.<id>.B`,
   in Milnor's generality (abstract manifolds, his notion of homotopy type, …). It may use Mathlib
   and the project's *definitions* (types and docstrings), not its theorems. Prompt:
   `harness/BLIND_PROMPT.md`.
2. **A.** The conjunction of the types of the theorems the comparison cites (`type_of%`, universes
   at 0). Definitions in a statement that are data (homeomorphisms, homotopy equivalences) are read
   as `Nonempty` of their types.
3. **Proofs.** A separate prover, not told the label, tries `A → B` and `B → A` in Lean.
   `#rt_check` (`RoundTrip/Check.lean`) rejects any proof that uses the item's own theorems,
   directly or through project lemmas built on them, and any proof containing `sorryAx`.
   `#rt_overlap` lists lemmas of A's proof that a `B → A` proof reuses. Prompt:
   `harness/PROVER_PROMPT.md`.
4. **Embedded special case (Milnor §§8–19).** Milnor's B quantifies over abstract Riemannian
   manifolds; the project formalizes submanifolds `N ⊆ V` of a Euclidean space with the induced
   metric. `RoundTrip/Bridge.lean` packages a slice submanifold as a Mathlib Riemannian manifold
   (`Bridge.Sub hN`, the induced metric and Levi-Civita connection `Bridge.conn`) with a dictionary
   to the project's vocabulary; `B_emb` is B instantiated there (`B → B_emb` is proved in each
   file), and the prover compares `B_emb` with A. Prompt: `harness/EMBEDDED_ADDENDUM.md`.
5. **Score.** Expected relation from the label: *same / explicit / restated* → equivalent;
   *stronger* → A ⇒ B only; *narrower* → B ⇒ A only; *sign* → not equivalent.

Known limits. (i) Both A and B are usually theorems, so a failed direction can mean "different" or
"not proved here"; provers mark the second `effort_only`. (ii) A direction proved without using its
hypothesis (the conclusion proved outright) says nothing; such directions are flagged
(`uses_hypothesis: false`) and excluded from the "proved directions" table below. (iii) The blind
statements inherit what the comparison quotes as Milnor's statement, which sometimes includes
steps of his proof. (iv) Provers' `relation` field is their judgement of *content* (it is
`incomparable` when each side has content the other lacks, even if both directions were proved
with one side partly outright); the first table below is computed from the proved, non-vacuous
directions only.

## What changed in this session (2026-10-05, local)

* Batches `p4a`–`p7b` (113 items), the 111 items added to the comparison since (§§20–24, ℂPⁿ,
  §7, Corollaries 17.2, 17.4, Theorem 19.6): blind statements and proofs.
* Two systematic bugs of the blind preludes were found and fixed by re-blinding:
  - `nrm q w := ‖(w : TangentSpace _ q)‖` is the Euclidean norm of ℝⁿ (the ascription does not
    change the type of `w`). A Lean scan of all 237 blind B's found 9 that depend on it
    (V7.9–V7.16, V7.10′); all were re-blinded and re-proved. None is refuted any more.
  - The §16 path space Ω consisted of maps ℝ → M constrained only on [0,1], so every
    injectivity/homeomorphism claim out of Ω was false (V10.4–V10.6, refuted with an embedded
    counter-model). Re-blinded with paths normalized outside [0,1]; no longer refuted.
* The embedded special case for §§8–19 (the second pass over §§8–10 and every later item).
* `RoundTrip/EnergyC2.lean` (Fable 5.1): parametric interval integrals of Cⁿ functions are Cⁿ;
  the energy of a `Morse.IsVariation` is C^∞ in the parameters; Milnor's variational E_** (a
  Fréchet mixed partial) equals `Morse.energyHessian`. This removed the blocker of a dozen §§13–15
  items. With it, `Items/V9_23.lean` proves that Milnor's variational index λ equals the project's
  `indexUpTo` / `formIndex energyHessian` on embedded manifolds (`Emb.lamEq`, `Emb.lamEqOne`),
  which discharged an assumed hypothesis in 11 items.
* Harness: `$RT_DIR` scratch folder; `#rt_check_soft` (a banned theorem reached only through the
  abstracted proof fields `D._proof_N` of a definition D is listed for review instead of failing);
  `#rt_check` fails on `sorryAx` (a proof that failed to elaborate used to pass).

## Results, layer 1

348 items: the 237 of the comparison's first version and 111 added since. Rows of the chapter
table are the exposition's chapters: V1–V5 = Milnor §§1–7, V6–V7 = §§8–10, V8–V9 = §§11–15,
V10 = §§16–17, V11 = §§18–19, V12 = §§20–21, V13 = §22, V14 = §23, V15 = §24, VA = the Appendix.

**Proved directions, ignoring vacuous ones** (a direction proved without using its hypothesis is
not counted): 58 equivalent, 52 A ⇒ B only, 16 B ⇒ A only, 211 neither, 11 with B false. 

| label \ proved | equivalent | A ⇒ B only | B ⇒ A only | neither | B false | n |
|---|---|---|---|---|---|---|
| same | 6 | 2 | 0 | 10 | 0 | 18 |
| explicit | 8 | 4 | 1 | 17 | 5 | 35 |
| restated | 19 | 24 | 4 | 78 | 3 | 128 |
| stronger | 9 | 17 | 3 | 37 | 0 | 66 |
| narrower | 14 | 5 | 8 | 68 | 2 | 97 |
| sign | 2 | 0 | 0 | 1 | 1 | 4 |

**The provers' judgement of content** (`relation`):

| label \ content | equivalent | A stronger | A narrower | incomparable | n |
|---|---|---|---|---|---|
| same | 7 | 1 | 1 | 9 | 18 |
| explicit | 10 | 3 | 2 | 20 | 35 |
| restated | 20 | 22 | 11 | 75 | 128 |
| stronger | 9 | 16 | 3 | 38 | 66 |
| narrower | 12 | 5 | 10 | 70 | 97 |
| sign | 0 | 0 | 1 | 3 | 4 |

Against the label's expected relation: 66 match, 108 partial (incomparable where the label says
stronger or narrower), 174 mismatch — most of the mismatches are the abstract-vs-embedded setting of
§§8–19, where the embedded special case is the informative comparison: 

| chapter | n | equivalent | A stronger | A narrower | incomparable | B false | embedded proved / one way / failed / n.a. |
|---|---|---|---|---|---|---|---|
| V1 | 13 | 1 | 6 | 3 | 3 | 1 | 0 / 0 / 0 / 13 |
| V2 | 15 | 3 | 1 | 2 | 9 | 0 | 0 / 0 / 0 / 15 |
| V3 | 33 | 14 | 13 | 0 | 6 | 1 | 0 / 0 / 0 / 33 |
| V4 | 21 | 13 | 4 | 1 | 3 | 0 | 0 / 0 / 0 / 21 |
| V5 | 13 | 3 | 2 | 0 | 8 | 0 | 0 / 0 / 0 / 13 |
| V6 | 19 | 1 | 0 | 1 | 17 | 0 | 12 / 2 / 2 / 3 |
| V7 | 31 | 0 | 1 | 5 | 25 | 0 | 20 / 8 / 0 / 3 |
| V8 | 16 | 1 | 0 | 0 | 15 | 0 | 8 / 5 / 0 / 3 |
| V9 | 26 | 1 | 0 | 0 | 25 | 1 | 15 / 2 / 8 / 1 |
| V10 | 26 | 0 | 0 | 2 | 24 | 1 | 1 / 6 / 18 / 1 |
| V11 | 21 | 0 | 0 | 2 | 19 | 5 | 10 / 7 / 4 / 0 |
| V12 | 17 | 0 | 0 | 0 | 17 | 0 | 0 / 4 / 1 / 12 |
| V13 | 14 | 0 | 2 | 0 | 12 | 0 | 2 / 2 / 8 / 2 |
| V14 | 28 | 8 | 8 | 3 | 9 | 0 | 0 / 5 / 1 / 22 |
| V15 | 40 | 5 | 9 | 8 | 18 | 0 | 0 / 0 / 0 / 40 |
| VA | 15 | 8 | 1 | 1 | 5 | 2 | 0 / 0 / 0 / 15 |

**Embedded special case** (items of §§8–19 and the Lie-group items of §§20–23 whose B is about
abstract Riemannian manifolds or Lie groups): 68 proved both ways (Milnor's statement on embedded
manifolds ⇔ the formal one, or the part of it B covers), 33 A ⇒ B_emb only, 5 B_emb ⇒ A only, 3
partial, 42 failed (each with the named obstacle in its note; most are the cell-complex model,
Hanner's theorem, the subdivision hypotheses, fineness, or B_emb itself false). 

**B false** (`not_B` proved, or A ⇒ B refuted). B is a blind formalizer's reading of Milnor's
statement, so a false B refutes that reading, not the book; most of these are edge cases (n = 0 or
1, a closedness hypothesis) that the text presupposes:
- V10_23: As formalized, B is false: it quantifies over n ≥ 1 and requires IsConj (a non-zero Jacobi field) at each interior passage through ±p 'with multiplicity n − 1';
- V11_11: As formalized B is false for n = 1 (flagged by the formalizer): Milnor's 'negative ... hence E**(W_i,W_i) < 0 for some i' needs n ≥ 2. Counter-model S¹ in Items
- V11_12: As formalized B is false for n = 1 (flagged by the formalizer): Myers' theorem needs n ≥ 2. Counter-model S¹ in Items/V11_12.lean (not_B).
- V11_14: As formalized B is false for n = 1 (flagged by the formalizer): on the circle clauses (c) and (d) fail. Counter-model S¹ in Items/V11_14.lean (not_B). Clauses (
- V11_15: False for n = 1 (and B quantifies over all n): with K ≥ (n−1)/r² = 0 a flat circle or line has geodesics of arbitrary length but E_** ≥ 0. Milnor's proof of 19.
- V11_16: False for n = 0: the clause 'with equality for some unit U₀' (Milnor's 'takes on a minimum') needs a unit tangent vector, which a 0-dimensional M lacks, while t
- V1_12: Clause (d) takes Milnor's 'x axis' literally: the critical set of x² is the y-axis {x = 0}. As written B is false (not_B), whereas Milnor clearly means the line
- V3_8: B includes the case n = 0, where S(X₀,X₀) ≤ 0 is not implied by subadditivity (which only gives S(X,X) ≥ 0); Milnor's chain implicitly has n ≥ 1. With 0 < n add
- V9_13: Clause (2) (finite index attained) is stated for every set A ⊆ V and is false when 0 ∉ A (e.g. A = ∅). Milnor's A = TΩ_γ is a vector space; with A a subspace (i
- VA_11: B (Case2 / its clause (a)) has no closedness hypothesis on the Y_i (T), so Milnor's G need not be continuous; proved false (not_B) with Y_0 = (0,∞) ⊂ Y_1 = ℝ an
- VA_9: Not a formalization bug: B faithfully states Milnor's claim without a closedness hypothesis (Milnor never states one), and without that hypothesis the claim does not hold (not_B). The proj

Verdicts revised by the second pass through the Bridge: V6.16 (now equivalent), V7.2, V7.5, V7.7,
V7.17 (B ⇒ A now proved). 

Directions proved without using the hypothesis (vacuous) occur in 73 items; they are flagged in
the JSON (`uses_hypothesis`) and in layer 3 (`vacuous`).


### Reading the labels

* **One label claims too much.** V15.14 (*m_k divides the dimension, and is the least one*) is
  labelled *stronger*, but the formal result covers k ≤ 8 only (m_{k+8} = 16 m_k is a definition,
  not a theorem), while Milnor's claim is for every k: the label should be *narrower* (range).
  (Corrected in the comparison on 2026-11-04, after checking pp. 143–144: for k > 8 Milnor states
  m_k = 16 m_{k−8}, and his Remark takes a space of dimension r·m_k for any k. The tables of this
  report keep the labels as they were when the audit ran.) The
  other items labelled *same* or *stronger* that came out *A narrower* (V7.17, V7.28, V11.9) are
  so only because of the abstract-vs-embedded setting; on embedded manifolds V7.17 and V7.28 are
  proved both ways and V11.9 one way (A ⇒ B_emb).
* **Most mismatches are the setting.** For Milnor §§8–19 the formal statements are about
  submanifolds of a Euclidean space and Milnor's about abstract Riemannian manifolds, so A and B are
  logically incomparable almost always. The embedded special case is the informative test there:
  on embedded manifolds Milnor's statement and the formal one coincide (both directions proved) for
  most items, and A implies Milnor's statement for most of the rest (table above).
* **restated / explicit** are logical equivalences only when the formal statement is not more
  general; Part IV's *restated* items are often *A stronger* (stated for any field 𝕜, any index
  type, any family) or *A narrower* (sets instead of groups, k ≤ 8).
* **narrower** remains the least informative label: the formal results assume more *and* state
  the steps of Milnor's proof as theorems, so neither side implies the other.

### What blocks an equivalence (taxonomy, for layer 3)

1. **Setting gap: abstract vs embedded (§§8–19).** Closed by the embedded special case except
   where a further item below applies; the Bridge has only the induced connection (uniqueness of
   the Levi-Civita connection is not formalized) and model ℝⁿ.
2. **Extra content in A.** The formal side states the steps of Milnor's proof (a.e. lemmas,
   explicit deformations, principal-curvature counts, bookkeeping lemmas) as theorems.
3. **Generality of A.** Abstract algebra of which Milnor's statement is an instance (exact
   sequences, any field 𝕜, any finite index type, arbitrary families, C² instead of C^∞).
4. **Compactness / regular values / closedness.** Theorem 3.1, 3.2 and the cell results for compact
   manifolds or regular end values; the project's `BrokenSetup` (normal radii, `IsShortJoin` on an
   open set) is stronger than Milnor's subdivision hypotheses in §16 (V10.5–V10.11), and its fine
   subdivisions are analytic (mesh h₀) where Milnor's are geometric (minimal pieces in good
   neighbourhoods; V9.16–V9.19).
5. **Cell-complex model.** The project's homotopy type of a cell complex is an iterated adjunction
   space (or a telescope of them); a Mathlib `CWComplex` needs cellular approximation, which
   neither the project nor Mathlib has (V2.11–V2.15, V3.43, V5.11, V5.15, V10.12, V10.13, V10.22,
   V10.24, V10.29, V10.30, V11.22, V11.24, VA.16–VA.19). On embedded manifolds, with the project's
   cell type in place of `CWComplex`, A gives Milnor's conclusion (V10.29, V10.30, V11.24).
6. **"Diffeomorphic" read two ways** (V2.2–V2.4).
7. **Finiteness hidden by `finrank`** (V3.12, V3.35, V3.39).
8. **Choice of structure** (V4.2, V4.4, V4.7, V4.9, V4.11, V4.23).
9. **Coefficients.** The project's homology is over a field; Milnor's 7.1, 7.3 and the homology of
   Ω(Sⁿ) are over ℤ. No universal coefficient theorem in Mathlib (V3.43, V5.16, V5.18, V10.25,
   V10.26). Over any field, A gives Milnor's statements.
10. **Hypotheses taken as given.** Hanner's theorem (Ω^d a manifold ⇒ a neighbourhood retract) is
    an assumption of the project's §22 (V13.2–V13.5, V13.14–V13.16): with it supplied, A gives
    Milnor's conclusions on embedded manifolds. Hypothesis (N) of §7 (V5.18, V5.19): with it,
    A gives Milnor's Theorem 7.4 for algebraic varieties. Connectedness of SU(n) (needed by the
    blind `[ConnectedSpace M]`) is formalized nowhere (V14.14–V14.20).
11. **The algebraic step only.** §21: the project formalizes the algebra of a Lie algebra with an
    ad-invariant form (V12.1–V12.13) and matrix groups (V12.14–V12.18), not the passage from a
    Lie group; the bridges prove "A + three named geometric facts ⇒ B". §§23–24: spectral index
    formulas are arithmetic, never tied to an actual geodesic (V15.3, V15.19).
12. **Range of the formal results.** §24's Clifford-module facts and the index bound only for
    k ≤ 8 (m_{k+8} = 16 m_k is a definition; V15.14, V15.17, V15.29–V15.31); §24 only for the
    explicit structures `bott16`, not every family (V15.41–V15.43); real and unitary periodicity as
    bijections of sets (V14.28–V14.30, V15.45, V15.46) — the group isomorphisms follow from the
    project's per-step lemmas in about 100 lines (`Items/V15_45.lean`, `stratumM`, `linkM`,
    `chainM`); Theorem 23.3 gives *some* isomorphism π_i G_m ≅ π_{i+1} SU(2m), not that the
    inclusion Ω^d → Ω induces it (V14.22).

### What the audit found

* **In Milnor, as the blind formalizers read him** (statements that do not hold in that reading,
  each with a counter-model in Lean; all but one
  already in `Exposition/Findings.md`, which the blind formalizers had not seen):
  - §2 example (d): "x axis" for the critical set of x² (V1.12).
  - §19 at n = 1: 19.4–19.5 and Myers' theorem (V11.11, V11.12, V11.14, V11.15; counter-model the
    embedded circle or line); 19.5's minimum at n = 0 (V11.16, not in Findings: the clause needs a
    unit tangent vector); §17's conjugate points along great circles at n = 1 (V10.23).
  - Appendix: Case 1 and Case 2 as written need the X_n / Y_i closed (VA.9, VA.11: Milnor's g and
    G are discontinuous without it); with closedness both directions are proved, and Theorem A and
    Case 1's conclusion hold without it (VA.10, VA.12), as Findings records.
  - §17, Theorem 17.1: "clearly h is continuous" — believed not to hold by the prover (V10.18, V10.19),
    and already settled by a counterexample in the project (`Morse.milnor_h_not_continuous`).
  - The Appendix's possible misprint (4 − 3t)u for (4t − 3)u: the blind statement used the corrected form, so
    it did not arise (VA.10).
* **In the blind statements** (caught by the provers): the two prelude bugs above (re-blinded);
  V3.8 allowed n = 0; V9.13 quantified over sets instead of subspaces (`not_B`); minor readings
  recorded in `B_issue` (V8.3, V10.6, V11.6).
* **In the formal statements:** no formal theorem says something false or unintended. Scope
  findings are listed under 10–12 above; layer 2 found the definitions faithful (below).

### Harness limits found and fixed

* A definition in A whose proof fields were proved with an item theorem (`Morse.riemMetricSpace`,
  `Morse.energyHessian`, `Morse.eigenJ`, `mulLeftIso`) made every proof mentioning A fail
  `#rt_check`: `#rt_check_soft` (V6.9, V12.12, V12.14 use it).
* A statement containing an item theorem as a proof term (V8.14, V11.15, V13.6, V14.13, V15.23,
  V15.26) cannot be checked at all; the provers check A′ (those proofs generalized to hypotheses,
  `A → A′` by proof irrelevance) instead.
* Items cannot import each other, so dictionaries are copied (≈ 400–800 lines in some files: the
  Ω/PathSp dictionary, the Hessian dictionary, `LamPf`). A shared module of these (on top of
  Bridge.lean and EnergyC2.lean) is the obvious next step.

### Models and cost

`p4a`'s last five items were proved independently by Opus 5.5 (267k tokens) and Fable 5.1 (332k):
the same relation on four, Opus one direction more on the fifth; at list prices Fable cost ≈ 3×
for no gain, so all provers ran on Opus 5.5, Fable only for `EnergyC2.lean` (214k tokens, 14
minutes). Typical costs: a blind statement 20–30k tokens per item; a prover 50–90k per item
(§§16–24 items with dictionaries up to 120k); a layer-2 blind group of 10–15 notions 100–200k, its
prover 130–380k. Layers 1–3 of this session (about 90 agents) used about 24 % of a weekly Max
allowance (7 % → 31 %); the binding limit was the 5-hour window, which ran at 6–9 parallel agents.

## Layer 2: the definitions

The definitions on which the statements of Milnor's numbered theorems rest were collected with
`#rt_defs` (`Check.lean`) over the declarations of the 94 items whose title is a numbered theorem or
corollary: 389 project definitions, triaged (`harness/l2_triage.json`, Sonnet 5.5) into 116 textbook
notions, 117 constructions inside proofs, 112 bookkeeping definitions and 11 structure fields. For
each notion a blind formalizer, shown only a neutral textbook description and the definition's
*signature*, wrote the textbook definition `RoundTrip.L2.<id>.T` (`L2/Blind/`, prompt
`harness/L2_BLIND_PROMPT.md`); a prover compared it with the project's definition
(`L2/Items/<id>.{lean,json}`, prompt `harness/L2_PROVER_PROMPT.md`), outright or under the
textbook's own hypotheses, with a counterexample where they differ.

116 notions

| group | n | equal | equal under hypotheses | differ | harmless | proved partially |
|---|---|---|---|---|---|---|
| g1 | 15 | 10 | 5 | 0 | 15 | 0 |
| g2 | 14 | 13 | 0 | 1 | 14 | 0 |
| g3 | 12 | 7 | 3 | 2 | 12 | 1 |
| g4 | 9 | 9 | 0 | 0 | 9 | 0 |
| g5 | 10 | 7 | 3 | 0 | 10 | 0 |
| g6 | 14 | 9 | 4 | 1 | 14 | 0 |
| g7 | 16 | 13 | 3 | 0 | 16 | 0 |
| g8 | 14 | 7 | 6 | 1 | 14 | 0 |
| g9 | 12 | 10 | 2 | 0 | 12 | 2 |
| all | 116 | 85 | 26 | 5 | 116 | 3 |

Not harmless: none

Differ / partial / T_issue:
- Milnor_SliceChart (differ, proved full): The project's SliceChart carries extra data: a base point x0 in S n source (documented in its docstring). So it is the type of pointed slice charts: Milnor.SliceChart I Z W S ≃ Σ φ : T, ↥(φ.source ∩ S) (proved, `equiv`); the forgetful map to T has range the ch
- Morse_IsCountableCellComplexType (equal_under_hypotheses, proved partial): The model of the union ⋃ Kₙ: the project uses the mapping telescope of the tower, the blind definition uses the colimit. Everything else agrees: proved P ⟺ (T with colimit replaced by the mapping telescope), P_iff_Ttele.
- Morse_IsFiniteCellComplexType (differ, proved full): Order of the cells: the project attaches them in the listed order, the blind T in some permutation (multiset reading). Exactly: T X cells ⟺ ∃ cells' ~ cells, P X cells' (T_iff). Proved example: P X [1,0] is false for every X, since the first cell attached to ∅
- Morse_IsMatrixGroup (equal, proved partial): Different packaging: the project lists consequences (closed under ·, ᴴ; 𝔤 skew, Ad-invariant, exp 𝔤 ⊆ G, dim Z = dim 𝔤) and omits closedness and the characterisation 𝔤 = {X : exp(tX) ∈ G ∀t}; the blind states closed subgroup + that characterisation and omits d
- Morse_IsRelCellAttachment (differ, proved full): The project's predicate is literal: K must be the iterated pushout and j the composite of the cellInl's. The blind one is only up to a homeomorphism of K compatible with the map. Example with no cells: not : Bool → Bool satisfies the blind notion (it is a home
- Morse_NormalCoord (differ, proved full): As types they are not equivalent: the project's structure carries non-canonical witness data (open sets O, U, ambient smooth extensions F, G) and has many elements, the blind NormalChart is a subsingleton (its only data, the chart exp_q⁻¹, is determined); diff
- Morse_Subdivision (equal, proved full, T_issue: not blind: the formalizer saw the project's Subdivision fields through the permitted #print Morse.BrokenSetup and chose k = m + 1 after seeing the project's indexing): Project: a structure with t : Fin (m+2) -> R, strictly increasing, t 0 = 0, t (last) = 1; blind: the subtype of such t. They are equivalent types (Morse.Subdivision m equiv T m) by repackaging the fields, both directions rfl. The indexing m = number of interio
- Morse_hessNullSpace (differ, proved full): Junk values off [0,1] (an encoding convention): the project takes the image of ker E_** under X ↦ X ∘ projIcc (fields constant off [0,1]); the blind takes ker E_** itself inside ℝ → V, which also contains every field of TΩ_γ vanishing on [0,1] with arbitrary v
- Morse_milnorM (equal, proved partial): Definitions differ in form (project: Milnor's table for k ≤ 7 plus the recursion m_{k+8} = 16 m_k; blind: least n > 0 with k anticommuting complex structures on ℝⁿ). Proved equal for k ≤ 8 and T k ≤ milnorM k for all k; the reverse inequality for k > 8 is Clif

**Every project definition agrees with the textbook notion it formalizes**, outright (85) or under
the textbook's own hypotheses (26); the 5 that differ do so by a documented convention (a carried
base point, cells attached in the listed order, literal pushouts, extra witness data, junk values
off [0,1]). The differences "under hypotheses" are of three kinds: junk values outside the
textbook's domain (non-differentiable f, negative radii, paths outside Ω, points off N);
finite dimension (`Morse.index` is Mathlib's `sigNeg`, 0 on infinite-dimensional spaces, and is
used only in finite dimension; Part III uses the ℕ∞-valued `formIndex`); and open vs closed
intervals for geodesics. Three comparisons stop at theorems Mathlib lacks: telescope ≃ₕ colimit
(`IsCountableCellComplexType`), the closed-subgroup theorem (`IsMatrixGroup`), Clifford periodicity
for k > 8 (`milnorM`). One blind definition (`Morse_Subdivision`) is not blind: its formalizer saw
the project's fields through a permitted `#print` of an argument type.

## Layer 3: failure labels

`harness/taxonomy.md` turns the taxonomy above into 19 codes; every layer-1 record carries a list of
codes and a primary one (`RoundTrip/layer3_labels.json`, summary and per-chapter table in
`RoundTrip/layer3_summary.md`; labelled by Sonnet 5.5 from the records' text). Primary codes over the
348 records: `setting` 118, `general_A` 48, `extra_A` 24, `range` 21, `cw_model` 21,
`algebraic_only` 18, `vacuous` 17, `hyp_A` 13, `B_false_milnor` 12, `structure_choice` 11,
`missing_math` 9, `taken_as_hyp` 9, `match` 8, `effort` 7, `reading` 6, `coefficients` 3,
`finrank` 2, `B_false_blind` 1.

## Per-item results (layer 1)

`relation` is the prover's judgement of content; `embedded` is the embedded special case (§§8–19).
The full diagnosis of each item is in `Items/<id>.json`.

| item | title | label | A→B | B→A | relation | embedded | note |
|---|---|---|---|---|---|---|---|
| V1.1 | The torus of §1 | narrower | failed | failed | incomparable | — | A is about the embedded torus Morse.torus R r ⊆ ℝ³ (modelled on ℝ²). It gives the four critical points, their non-degeneracy and indices 0,1,1,2, M^a = ∅ for a < 0 and M^a = M for a ≥ 2R+2r, and Theor… |
| V1.10 | Corollary 2.3: non-degenerate critical points are isolated | stronger | proved | failed | A_stronger | — | A = Euclidean version plus manifold version, each assuming only that f is C² at p (not smooth everywhere), with no Hausdorff hypothesis, any universe, and an iff conclusion. B assumes f is C^∞ on all … |
| V1.12 | Examples of degenerate critical points | sign | false | proved | incomparable **B false** | — | B is false: clause (d) states, following Milnor's words literally, that the critical set of (x,y) ↦ x² is the x-axis {y = 0}; it is {x = 0}, and (1,0) is not critical (not_B). Hence A ⇒ B is false and… |
| V1.13 | One-parameter groups of diffeomorphisms | narrower | failed | proved | A_narrower | — | A works only in a normed space E: φ₀ = id for a 1-parameter group, and orbits of a group generated by X (in the HasDerivAt sense) are integral curves. Both are elementary and are re-proved directly in… |
| V1.14 | Global flows, and smooth dependence on the initial point | restated | failed | failed | incomparable | — | A builds the global flow Morse.flow of a bounded Lipschitz field on a Banach space E directly: integral curves, uniqueness, the group law, and C^n dependence on (t, x) for C^n compactly supported fiel… |
| V1.15 | Lemma 2.4: compactly supported fields generate flows | narrower | failed | proved | A_narrower | — | A proves Lemma 2.4 only for M = E, a complete normed space (any dimension, where the infinite-dimensional case is degenerate: X = 0). B states it for an abstract finite-dimensional Hausdorff manifold.… |
| V1.2 | Attaching a cell | same | proved | proved | equivalent | — | The listed declarations (Morse.AttachCell, Morse.cellDesc) are both definitions, so A is the empty conjunction True; B is then provable outright (identification by Quot.sound, S^{-1} empty, e^0 a poin… |
| V1.3 | Critical points, the Hessian, index and nullity in coordinates | restated | proved | failed | A_stronger | — | A ⇒ B: 'fderiv = 0 ⟺ all partials vanish' is linear algebra on the coordinate basis. For the second clause, the blind nested-partials matrix hmat equals the matrix of Morse.hessian = fderiv (fderiv f)… |
| V1.4 | The same notions on a manifold; Morse functions | restated | failed | proved | A_narrower | — | A's only theorem is isCriticalPointM_iff_milnor (f_* = 0 ⟺ the companion project's 'df_p not surjective'). It is elementary and is re-proved directly in B_to_A without using B; B itself says nothing a… |
| V1.5 | Independence of the coordinate system | stronger | proved | failed | A_stronger | — | A ⇒ B: (1) the blind hmat is the matrix of Morse.hessian. hessian_comp (from A) gives H_{f∘φ}(v,w) = H_f(Dφ v, Dφ w), and with Dφ bijective non-degeneracy transfers; det ≠ 0 ⟺ non-degenerate comes fro… |
| V1.7 | Lemma 2.1 (Hadamard) | stronger | proved | failed | A_stronger | — | B is literally A's first conjunct exists_hadamard_coord (open convex V ⊆ ℝⁿ, f C^∞ on V with f(0) = 0, f = Σ xᵢ gᵢ, gᵢ(0) = ∂f/∂xᵢ(0)). A ⇒ B is immediate. A additionally proves the coordinate-free Ha… |
| V1.8 | Lemma 2.2 (the lemma of Morse) | stronger | proved | failed | A_stronger | — | A ⇒ B: morse_lemmaM with U = univ gives a project smooth coordinate y : M → (Fin (finrank E) → ℝ) with y p = 0 and the normal form. Transporting along finrank (EuclideanSpace ℝ (Fin n)) = n and the li… |
| V1.9 | The index is forced by the normal form | stronger | proved | failed | A_stronger | — | A ⇒ B: isNondegenerateCriticalPointM_of_morse_chart applied to z read in Fin n → ℝ (z composed with EuclideanSpace.equiv is a project IsSmoothCoord). Note that A needs no smoothness of f and no coordi… |
| V2.1 | Sublevel sets and strong deformation retracts | stronger | proved | proved | equivalent | — | Milnor's r_t (the blind DefRetract: a continuous family r_t with r₀ = id, r₁ into A, each r_t fixing A) is exactly the project's IsStrongDeformationRetract (a retraction r with a HomotopyRel from id t… |
| V2.10 | Remark 3.4: the critical level | narrower | failed | failed | A_narrower | — | A = remark_3_4 for f : E → ℝ (E a finite-dimensional inner-product space): M^c is an SDR of M^{c+ε}, and M^{c-ε} ∪ χ(e^λ) is an SDR of M^c for an embedded cell χ. Plus of_retract (A ⊆ B ⊆ C with A, B … |
| V2.11 | Iterated adjunction spaces in place of CW-complexes | narrower | failed | proved | A_narrower | — | The listed declarations (IsCellAttachment, IsFiniteCellComplexType) are definitions, so A = True and B ⇒ A is trivial. B is cellular approximation for an attaching map into a Mathlib CWComplex, plus '… |
| V2.12 | Theorem 3.5 for a compact submanifold of Euclidean space | narrower | failed | failed | incomparable | — | A proves Theorem 3.5 for compact slice submanifolds N of a finite-dimensional V. It concludes IsFiniteCellComplexType: homotopy equivalent to an iterated adjunction space with arbitrary attaching maps… |
| V2.13 | Lemma 3.6 (Whitehead) | same | proved | proved | equivalent | — | Both say: homotopic attaching maps give a homotopy equivalence X∪_{φ0}e^λ ≃ X∪_{φ1}e^λ extending id_X. The only difference is the model of the adjunction space (B: Quot of Y ⊕ closed ball; A: TopCat p… |
| V2.14 | Lemma 3.7, and the Assertion of p. 22 | stronger | proved | proved | equivalent | — | Lemma 3.7: same content (F is f on X and the identity on the cell, and F is a homotopy equivalence), transported along the same Quot ≃ₜ pushout homeomorphism as V2_13. Assertion: A only states RF ≃ id… |
| V2.15 | The Remark of p. 24: sublevel sets at regular values | narrower | failed | failed | incomparable | — | A: for compact slice submanifolds N and regular values a only (no critical point on the level a), N^a is homotopy equivalent to an iterated adjunction space with cells for the critical points below a,… |
| V2.2 | Theorem 3.1 on a Euclidean space | narrower | failed | failed | incomparable | — | A proves Theorem 3.1 only for M = E, a finite-dimensional inner-product space with f : E → ℝ. It also has the cut-off lemma and abstract IsSlabFlow lemmas. B states Theorem 3.1 for an arbitrary smooth… |
| V2.3 | Theorem 3.1 on a submanifold of Euclidean space | narrower | failed | failed | incomparable | — | A proves Theorem 3.1 for f = F/N, with N a slice submanifold of a finite-dimensional V and F smooth on V, concluding an ambient diffeomorphism Φ : N ≃ N with Φ '' N^a = N^b plus SDR and homotopy equiv… |
| V2.4 | Theorem 3.1 on a compact manifold | narrower | failed | failed | incomparable | — | A proves Theorem 3.1 for a compact manifold (CompactSpace M), concluding a global diffeomorphism Ψ : M ≃ M with Ψ '' M^a = M^b, SDR and homotopy equivalence. It also contains the embedding of a compac… |
| V2.5 | Compactness cannot be omitted | restated | proved | failed | A_stronger | — | A ⇒ B: take M = ℝ² minus a point as an open subset (Mathlib's Opens charted space, modelled on EuclideanSpace ℝ (Fin 2)) with f = ‖x‖², a = 1/4, b = 4. Non-compactness and the failure of the deformati… |
| V2.6 | Theorem 3.2 on a Euclidean space | narrower | failed | failed | incomparable | — | A proves Theorem 3.2 only for f : E → ℝ, E a finite-dimensional inner-product space: an embedded cell χ, an SDR onto M^{c-ε} ∪ χ(e^λ), the homotopy equivalence, and the pushout form. B is Theorem 3.2 … |
| V2.7 | A cell meeting a closed set in its boundary is attached to it | explicit | proved | failed | incomparable | — | The two sides formalise disjoint halves of Milnor's remark. B is the coordinate fact: in a Morse chart, for small ε, e^λ ∩ M^{c-ε} = ė^λ (on e^λ, η = 0, so f = c - ξ), and e^λ is a closed λ-cell with … |
| V2.8 | Theorem 3.2 in a Morse patch, and on a submanifold | narrower | failed | failed | incomparable | — | A: Theorem 3.2 for F/N with N a slice submanifold of a finite-dimensional V (cell + SDR, and the pushout form), the extension lemma exists_contDiff_comp_val_eq_of_chart, and patch_theorem_3_2. The lat… |
| V2.9 | Remark 3.3: several critical points on one level | narrower | failed | failed | incomparable | — | A's first conjunct proves Remark 3.3 only for f = F/N with N a slice submanifold of a finite-dimensional normed space V. It concludes a strong deformation retraction of N^{c+ε} onto the explicit subsp… |
| V3.10 | The Betti numbers are subadditive, and the Euler characteristic additive | restated | proved | failed | A_stronger | — | A is linear algebra: for an abstract Morse.LongExactSeq / FiltrationHomology of finite-dimensional spaces, rank–nullity gives dim B_i ≤ dim A_i + dim C_i, finiteness of the middle term, vanishing of t… |
| V3.11 | Theorem 5.2 (weak Morse inequalities), abstractly | narrower | proved | failed | A_stronger | — | A is Theorem 5.2 for an abstract Morse.FiltrationHomology: R_λ(X_n,X_0) ≤ Σ slab dims, the χ equality when slabs vanish in degree N+1, and the identification of the Morse numbers with critical-point c… |
| V3.12 | Lemma 5.3 | restated | proved | failed | A_stronger | — | A is pure linear algebra: rank of the last map of a finite exact sequence equals the alternating sum, and subadditivity of S_λ for any abstract LongExactSeq / FiltrationHomology of finite-dimensional … |
| V3.13 | The strong Morse inequalities, abstractly | narrower | proved | failed | A_stronger | — | A is (4_λ) for an abstract Morse.FiltrationHomology: altSum R ≤ altSum of the Morse numbers, and ≤ altSum of the critical-point counts under a cell hypothesis on the slabs. B is (4_λ) for singular hom… |
| V3.14 | Consequences of the strong inequalities | explicit | proved | failed | A_stronger | — | B is purely arithmetic: for ℕ-sequences R, C vanishing above n and satisfying all (4_λ), it asserts (2_λ) R_λ ≤ C_λ, the equality (3) Σ_{i≤n}(-1)^i R_i = Σ(-1)^i C_i, and that C_{λ+1} = 0 forces R_{λ+… |
| V3.15 | Corollary 5.4, and the lacunary principle | stronger | proved | failed | A_stronger | — | A is Corollary 5.4 abstractly: integer sequences b ≥ 0, c satisfying all (4_λ) (λ ≥ 1 and λ = 0 cases), the same for any Morse.FiltrationHomology with its Morse numbers, and the lacunary principle (b_… |
| V3.16 | The numbers $C_\lambda$ of a function | restated | proved | failed | incomparable | — | The vocabulary agrees: B's Cnum is the project's critCount by rfl (ncard of {critical, index = λ}). A (finsum_neg_one_pow_indexM_eq_sum_critCount) is the regrouping identity Σ_{p critical} (-1)^{ind p… |
| V3.17 | The Poincaré–Hopf integer | restated | proved | proved | equivalent | — | A (exists_isEulerNumber) says that a compact nonempty slice submanifold N ⊆ ℝ^{K+1} (dim d+1, K > 0) has an integer χN equal to the index sum of every smooth tangent field with finitely many zeros (ze… |
| V3.19 | The index of the gradient field is $(-1)^\lambda$ | narrower | proved | failed | A_stronger | — | Same setting and vocabulary: both use the project's tangentialGradient and the companion project's indexN on a compact slice submanifold N ⊆ ℝ^{K+1}. B is exactly the conclusion of indexN_tangentialGr… |
| V3.2 | Small sublevel sets at the extrema are closed cells | restated | proved | failed | A_stronger | — | A ⇒ B: p and q are the strict minimum and maximum, since another extremum would be a third critical point (A's isCriticalPointM_of_isLocalMin, applied to f and to -f). A's Morse charts at a local min/… |
| V3.20 | Formula (3) without homology | restated | proved | proved | equivalent | — | A is formula (3) 'without homology': for a Poincaré–Hopf integer χN (Morse.IsEulerNumber) of a compact slice submanifold N ⊆ ℝ^{K+1} (K > 0), Σ(-1)^{ind} over the critical points of any Morse function… |
| V3.22 | The torus of Diagram 1 is a compact surface | restated | proved | failed | A_stronger | — | Both use the same torus of revolution: B's torus R r is Morse.torus R r by rfl. A ⇒ B: compactness and the slice-submanifold structure (modelled on ℝ², complement ℝ¹) are A's isCompact_torus and isSli… |
| V3.23 | The height function: four critical points, of indices 0, 1, 1, 2 | restated | proved | proved | equivalent | — | Same torus, height function and four points (B's torus/hgt are Morse.torus/height by rfl; pP..pS = pointP..pointS by ext). A lists: critical points ⟺ {p,q,r,s}; critical values {0,2r,2R,2R+2r}; non-de… |
| V3.24 | Milnor's cases (1) and (5), and Theorem 3.1 on the torus | narrower | failed | failed | incomparable | — | Same torus and height (B's M^a is the image in ℝ³ of the project's sublevel set, sub_eq). Shared content: (1) M^a = ∅ for a < 0 and (5) M^a = M for a > f(s); A has (5) for a ≥ 2R+2r, slightly more. B … |
| V3.3 | The two critical points are the minimum and the maximum | explicit | proved | failed | A_stronger | — | A (dim ≥ 1, exactly two critical points, both non-degenerate, M compact, no T2) gives p, q with f p < f q, strict min/max elsewhere, and indices 0 and n. B only says the two given critical points are … |
| V3.31 | Attaching cells to a closed set: the step “by excision” | stronger | failed | failed | incomparable | — | A's cells are embedded. X = Y ∪ χ(D^k) ⊆ E with Y closed, χ continuous and injective on the closed ball, and χ(z) ∈ Y ⟺ ‖z‖ = 1. For such a pair, H_*(χD, χS) → H_*(X,Y) and H_*(D,S) → H_*(X,Y) are iso… |
| V3.32 | The Morse inequalities for any filtration of a space | restated | proved | failed | A_stronger | — | A is Theorem 5.2 and (4_λ) in singular homology for any monotone ℕ-filtration X_0 ⊆ X_1 ⊆ … of subsets whose steps k < n have finite-dimensional homology (arbitrary dimensions). C_λ is Σ_k dim H_λ(X_{… |
| V3.33 | Betti numbers, and the homology of a slab | restated | failed | failed | incomparable | — | Shared: R_λ = rank H_λ (B's first clause holds outright by Module.finrank_eq_rank; the project's bettiNumber is finrank of spaceHomology). A gives homeomorphism invariance of Betti numbers, H_*(E,∅) =… |
| V3.34 | The Morse filtration of a compact submanifold | narrower | failed | failed | incomparable | — | A (submanifold N ⊆ V, f = F/N, read in any T ≃ₜ N) computes H_*(N^a, N^{a'}) for a slab whose ends a' < a are REGULAR values, with any number of critical points on the one critical level inside (dimen… |
| V3.35 | Theorem 5.2 in singular homology | narrower | proved | proved | equivalent | — | A: for a compact slice submanifold N ⊆ V and f = F/N with non-degenerate critical points (homology read in any T ≃ₜ N), b_λ ≤ C_λ, Σ_{λ≤dim}(-1)^λ b_λ = Σ(-1)^λ C_λ, b_i = 0 and H_i = 0 (Subsingleton)… |
| V3.36 | The strong Morse inequalities in singular homology | narrower | proved | proved | equivalent | — | A: the inequalities (4_λ) b_λ - b_{λ-1} + … ± b_0 ≤ C_λ - … ± C_0 for f = F/N on a compact slice submanifold N (homology in any T ≃ₜ N; primed: T = N). B: (4_λ) for every smooth f with non-degenerate … |
| V3.37 | Corollary 5.4 and the lacunary principle in singular homology | narrower | proved | proved | equivalent | — | A: Corollary 5.4 for f = F/N on a compact slice submanifold (λ = l+1 and λ = 0 versions, homology in any T ≃ₜ N) and the lacunary principle (b_i = C_i for all i if no two consecutive C_i are nonzero).… |
| V3.38 | The Euler characteristic, three ways | restated | proved | proved | equivalent | — | A: (i) a Poincaré–Hopf integer χN (Morse.IsEulerNumber) of a compact N ⊆ ℝ^{K+1}, K > 0, dim d+1, equals Σ_{i≤d+1}(-1)^i b_i(T;𝕜) for any T ≃ₜ N; (ii) eulerNumberM E M (Σ(-1)^λ C_λ of a chosen Morse f… |
| V3.39 | The Morse inequalities on a compact manifold | explicit | proved | proved | equivalent | — | Same setting on both sides: abstract compact Hausdorff manifold M (Type), smooth f with non-degenerate critical points, any field. A: finiteness of H_i for compact submanifolds (and spaces homeomorphi… |
| V3.4 | Theorem 3.1 also carries the boundary level | stronger | proved | failed | A_stronger | — | A is Theorem 3.1 with the level set carried along: a diffeomorphism Φ of a slice submanifold N with Φ(N^a) = N^b and Φ(F⁻¹a) = F⁻¹b, for any smooth F on the ambient space with compact critical-point-f… |
| V3.41 | $\mathbb CP^n$ and Milnor's coordinates | restated | proved | failed | A_stronger | not_applicable | A (no universe parameters) is about the matrix model ℂPⁿ = grassmannian (Fin (n+1)) 1 ⊆ Mₙ₊₁(ℂ): points are projections f fᴴ, coord k / param k invert each other between U_k = {Re P_kk > 0} and the op… |
| V3.42 | Milnor's function on $\mathbb CP^n$: critical points and indices | same | proved | proved | equivalent | not_applicable | Same mathematics in two models. A: on the matrix model with its slice structure, height_param (f∘param k = c_k + Σ(c_j−c_k)(x_j²+y_j²) on the closed ball), critical points = param k 0, non-degenerate … |
| V3.43 | The cells and the homology of $\mathbb CP^n$ | narrower | failed | proved | incomparable | not_applicable | A (matrix model): ℂPⁿ is of the project's IsFiniteCellComplexType (homotopy equivalent to an iterated adjunction space with arbitrary attaching maps) with one cell in each even dimension ≤ 2n, and dim… |
| V3.5 | Two closed balls glued along their boundary form a sphere | explicit | proved | proved | equivalent | — | Same theorem, two presentations. A (Hausdorff X) takes two maps h₁, h₂ : ℝⁿ → X, continuous and injective on the closed ball, whose images cover X, meet exactly in h₁(Sⁿ⁻¹), and have the same boundary… |
| V3.6 | Theorem 4.1 (Reeb) | narrower | proved | proved | equivalent | — | A states Reeb's theorem only for compact slice submanifolds N ⊆ V (modelled on some Z: for f = F/N with F smooth on V, the dim-0 case, and f smooth on N ⊆ ℝᴷ⁺¹). B states it for an abstract compact sm… |
| V3.7 | Subadditive and additive functions | restated | proved | proved | equivalent | — | The listed declarations (IsSubadditive, IsAdditive) are definitions, so A = True. B (additive ⇒ subadditive) holds outright, so the equivalence is vacuous. Vocabulary check: on ι = Set α ordered by ⊆,… |
| V3.8 | Lemma 5.1 | explicit | false | proved | equivalent **B false** | — | B as written is false: it allows n = 0, where its first conjunct says S(X₀,X₀) ≤ 0 (empty sum) for every subadditive S, refuted by S ≡ 1 (not_B). So A ⇒ B is false and B ⇒ A holds only vacuously. The … |
| V3.9 | The homology of a filtration, and its Morse numbers | restated | proved | proved | equivalent | — | All listed declarations (LongExactSeq, FiltrationHomology, morseNumber, altSum, FiltrationHomology.ofSteps) are definitions, so A = True. B holds outright: the rank clause is Module.finrank_eq_rank, a… |
| V4.1 | The normal bundle and the endpoint map | stronger | proved | failed | A_stronger | — | B's NSet is the project's normalBundleSet by rfl (tanN is the range of mfd val). A: the normal bundle of ANY slice submanifold M ⊆ ℝᵏ of dimension m (complement w, m + w = k) is a slice submanifold of… |
| V4.10 | The critical points and the Hessian of $L_p$ | stronger | proved | proved | equivalent | — | Clause 1 (q critical for L_p/M ⟺ q − p ⊥ T_qM) is the same on both sides and transfers both ways: A states it for every slice M (k = 0 included) as (q, p − q) ∈ N, B for dim ≥ 1 with tanN; B ⇒ A handl… |
| V4.11 | Lemma 6.5 | explicit | proved | proved | equivalent | — | Both are Lemma 6.5: q is a degenerate critical point of L_p iff p is focal for (M,q), and the nullity of L_p at q is the focal multiplicity. A: any slice M ⊆ ℝⁿ (k + w = n, k = 0 allowed), nullity of … |
| V4.12 | Theorem 6.6 | stronger | proved | proved | equivalent | — | Both are Theorem 6.6: for a.e. p, L_p/M has only non-degenerate critical points. A ⇒ B is A's volume clause. B ⇒ A: B (dim M ≥ 1, volume) extends to all slice M ⊆ ℝⁿ (dim 0 and empty M trivially) and … |
| V4.13 | Corollary 6.7 for closed submanifolds of $\mathbb R^n$ | narrower | proved | proved | equivalent | — | B (Corollary 6.7 for a closed slice M ⊆ ℝ^{K+1}, dim ≥ 1): some smooth f on M has no degenerate critical point and compact sublevel sets. A ⇒ B is A's exists_isMorseFunction_isCompact_sublevel. B ⇒ A … |
| V4.16 | Whitney's embedding, for compact manifolds | narrower | failed | proved | A_narrower | — | A (universes at 0) is Whitney for COMPACT Hausdorff manifolds (any finite-dimensional model E) into SOME ℝᴺ: a smooth closed embedding with injective differential whose image is a slice submanifold; a… |
| V4.17 | Corollary 6.7 for a compact manifold | narrower | proved | proved | equivalent | — | Both are Corollary 6.7 for a compact manifold (universes of A at 0). A: every compact Hausdorff smooth manifold with any finite-dimensional model E (no second countability assumed) has a Morse functio… |
| V4.18 | The Euler number of an abstract manifold | restated | proved | proved | equivalent | — | The item lists only the definition Morse.eulerNumberM, so A = True and both directions are vacuous (B_to_A trivial; A_to_B by proving B outright). B (formula (3) with homology: Σ(-1)^λ dim H_λ(M;ℚ) = … |
| V4.19 | Formula (3) and Application 2 on a compact manifold | restated | proved | proved | equivalent | — | A (universes at 0) is formula (3) 'without homology' for abstract compact manifolds: Σ(-1)^λ C_λ(f) is the same for all Morse f and equals eulerNumberM (defined from one Morse function), = #M in dim 0… |
| V4.2 | Focal points and their multiplicity | explicit | proved | proved | equivalent | — | Both sides are the rank–nullity unpacking of 'focal point = critical value of E': for a square Jacobian, nullity > 0 ⟺ not surjective, and e = q + (e − q). A states it (endpointNullity_pos_iff, isFoca… |
| V4.21 | Corollary 6.8 on a submanifold of $\mathbb R^n$ | stronger | proved | failed | A_stronger | — | B is Corollary 6.8 for a slice submanifold M ⊆ ℝ^{K+1} (dim ≥ 1, not necessarily closed or compact): a BOUNDED smooth f is a uniform ε-limit of smooth g without degenerate critical points, with deriva… |
| V4.22 | Corollary 6.8 on a compact manifold | narrower | proved | failed | A_stronger | — | B is Corollary 6.8 on a compact (Hausdorff, second countable) manifold modelled on ℝⁿ: a bounded smooth f is approximated uniformly within ε by smooth g without degenerate critical points whose deriva… |
| V4.23 | Lemma 6.9: the index of $L_p$ | restated | proved | failed | A_stronger | — | B is Lemma 6.9 as stated: at a non-degenerate critical point of L_p (dim M ≥ 1), index = Σ_{s∈[0,1]} nullity of dE at (q, s(p−q)), with the nullity computed in an ARBITRARY slice structure hNN on N, p… |
| V4.24 | Reeb's theorem on a compact manifold | explicit | proved | proved | equivalent | — | Both are Reeb's theorem for a compact Hausdorff smooth manifold (universes of A at 0): a smooth f with exactly two critical points (ncard = 2), both non-degenerate, forces M ≃ₜ S^n ⊆ ℝ^{n+1}. A allows… |
| V4.3 | Theorem 6.1 (Sard) | narrower | failed | failed | incomparable | — | A is Sard's theorem for SMOOTH maps f : M → F into a finite-dimensional vector space, on an open U ⊆ M or all of M, M second countable, any dimensions, any Haar measure. B is Milnor's Theorem 6.1: f o… |
| V4.4 | Corollary 6.2: almost no point is focal | explicit | proved | proved | equivalent | — | Both are Corollary 6.2: the focal set is Lebesgue/Haar null. A: for the canonical slice structure on N (isSliceSubmanifold_normalBundle hM hkw), any M ⊆ ℝⁿ with k + w = n, any Haar measure. B: ∀ᵐ e (v… |
| V4.5 | The first and second fundamental forms | restated | proved | proved | equivalent | — | All listed declarations (xParam, uParam, dParam, d2Param, firstFF, secondFF, normalForm) are definitions, so A = True. B (for any C² immersion x on an open U: (g_ij) symmetric positive definite, ℓ_ij … |
| V4.6 | Principal curvatures | restated | proved | proved | equivalent | — | A: the shape operator S_v on T_qM = range dx (⟪S_v a, b⟫ = ℓ_v(dx⁻¹a, dx⁻¹b)) is self-adjoint, and the multiplicity of K among principalCurvatures (Mathlib's sorted eigenvalues of S_v) is dim eigenspa… |
| V4.7 | Lemma 6.3: focal points along a normal line | stronger | failed | failed | incomparable | — | Same lemma, different objects. A (in the project's parametrization xParam, no normalization, any v ⊥ T_qM, nullity of dE in the canonical structure on N): focalMult(q + t v) is 0 for t = 0 and dim eig… |
| V4.8 | The Jacobian of the endpoint map | restated | failed | failed | incomparable | — | A is frame-free and works on the manifold N: T_{(q,v)}N = {(dx ξ, h) : ⟪h, ∂x/∂η⟫ + ⟪v, ∂²x/∂ξ∂η⟫ = 0}, the mfderiv of (q,v) ↦ Γq + v on N, and dim ker dE = nullity(g − v·ℓ) in the project's parametri… |
| V4.9 | Assertion 6.4 | stronger | proved | proved | equivalent | — | Both are Assertion 6.4: q + tv is focal of multiplicity μ iff (g_ij − t v·ℓ_ij) has nullity μ > 0. A: in the project's parametrization xParam, any v ⊥ T_qM (not necessarily unit), canonical structure … |
| V5.10 | The index bound for forms of Milnor's shape | stronger | proved | proved | incomparable | — | Both directions are vacuous: each conclusion is proved outright. A (universe 0) is pure linear algebra: on a finite-dimensional complex vector space a real form H with H(v,v) = G(v,v) − Re B(v,v) (G ≥… |
| V5.11 | The index of $L_p$ is at most $k$, in a holomorphic chart | stronger | failed | proved | incomparable | — | A (universes 0) is only the chart-level index bound: for w : V → F complex-C² at q, index of the Hessian of z ↦ ‖w z − p‖² at q is ≤ dim_ℂ V. B is Milnor's proof of Theorem 7.2: for a closed slice sub… |
| V5.13 | The index of $L_p$ on a complex submanifold | stronger | proved | proved | A_stronger | not_applicable | A (universes 0): two_mul_indexM_normSq_sub_le (any finite-dim inner product space V, any slice submanifold N with J-invariant tangent spaces, every critical point of L_p, degenerate or not: 2·index ≤ … |
| V5.15 | Theorem 7.2 | restated | failed | proved | incomparable | not_applicable | A (Theorem 7.2, project form): a closed slice submanifold M ⊆ 𝔼 n of dimension 2k with J-invariant tangent spaces satisfies IsCountableCellComplexType M cells (homotopy equivalent to a mapping telesco… |
| V5.16 | Theorem 7.1 (Andreotti and Frankel), over a field | narrower | failed | failed | incomparable | not_applicable | A (Morse.theorem_7_1, no universe parameters, 𝕜 : Type): for a closed slice submanifold M ⊆ 𝔼 n of real dimension 2k with J-invariant tangent spaces (J orthogonal, J² = −1), H_i(M; 𝕜) = 0 for i > k, e… |
| V5.17 | Hyperplane sections, for an abstract pair | restated | proved | failed | A_stronger | not_applicable | A (no universe parameters; HypothesisN is vocabulary): (i) le_indexM_neg_normSq_sub: at a non-degenerate critical point of L_p on a complex submanifold of real dimension 2k, index(−L_p) ≥ k; (ii) for … |
| V5.18 | Corollary 7.3 (Lefschetz), over a field | narrower | failed | failed | incomparable | not_applicable | A (no universe parameters; CP.affinePart, CP.hyperplaneSection, CP.affineHomeomorph are vocabulary): ‖affine coordinates‖ → ∞ at V ∩ P, and Corollary 7.3 over a field for closed V ⊆ ℂPⁿ (trace-one Her… |
| V5.19 | Theorem 7.4 (Lefschetz) | restated | failed | failed | incomparable | not_applicable | A (universes 0): theorem_7_4_of_section — for compact X, closed A, X − A ≅ M a closed complex submanifold with ‖e⁻¹y‖ → ∞ at A, and Hypothesis (N), every map from a compact P embedded in a space of di… |
| V5.2 | Milnor's form $Q'$, and multiplication by $i$ | stronger | proved | proved | equivalent | — | A (universes at 0): for any complex normed space V and complex bilinear B, Re B(iv, iw) = −Re B(v, w) (the polarized form of Milnor's Q(iz) = −Q(z) for Q' = Re Q), Re⟨iv, iw⟩ = Re⟨v, w⟩ (i is orthogon… |
| V5.3 | Assertion 1 | restated | proved | proved | equivalent | — | A (universes at 0), for any complex inner product space V and complex bilinear B: Re B − e⟨·,·⟩_ℝ and Re B + e⟨·,·⟩_ℝ have equal nullity; the eigenspace of an operator A with Re⟨Au, w⟩ = L(u, w) is th… |
| V5.5 | Real orthogonality to a complex subspace | explicit | proved | proved | equivalent | — | A (universe 0): in any complex inner product space, if Re⟨a, v⟩ = 0 for all a in a complex subspace T, then ⟨a, v⟩ = 0 on T. B: for holomorphic w : ℂᵏ → ℂⁿ with injective dw(0) and v real-orthogonal t… |
| V5.6 | The Hessian of $L_p$ in holomorphic coordinates | restated | failed | proved | incomparable | — | A (universes 0): for w : V → F complex-C² at q (V, F arbitrary complex normed/inner product spaces) and any p, the real Hessian of z ↦ ‖w z − p‖² at q is 2(Re⟨dw v, dw v'⟩ + Re⟨w q − p, d²w(v, v')⟩) —… |
| V5.7 | Assertion 2, in a holomorphic chart | restated | proved | proved | incomparable | — | Both directions are vacuous (each conclusion proved outright). A (universes 0): for any w : V → F complex-C² at q, any n and t, the real Hessians at q of ‖w(·) − (w q + t n)‖² and ‖w(·) − (w q − t n)‖… |
| V6.1 | Tangent spaces, the projection $P_q$, and vector fields | narrower | failed | failed | incomparable | not_applicable | A (universes 0; tangentSubspace, tanProj, dN, IsTangentField, projField are definitions): for a slice submanifold N ⊆ V, dN F q v = fderiv G q v for any local extension G and tangent v (chain rule for… |
| V6.10 | Lemma 8.3 | narrower | failed | proved | incomparable | proved | A (universes 0): for N a slice submanifold of a Euclidean V with the induced Levi-Civita connection, DX/dt := P_{c(t)} X'(t), any curve c and fields X, Y along c (tangent at every t) differentiable at… |
| V6.11 | Corollary 8.4 | restated | failed | proved | incomparable | proved | A (universes 0; IsCompatible is a definition = the Corollary 8.4 formula itself): (a) Cor. 8.4 for the induced connection P(dY(v)) of a slice submanifold N ⊆ V, for fields differentiable at q; (b) for… |
| V6.13 | Definition 8.5: symmetric connections | explicit | failed | proved | incomparable | proved | A (universes 0; IsSymmetric, bracket are definitions): abstract Mathlib connections (any model): Milnor-symmetric (X⊢Y − Y⊢X = mlieBracket X Y, for fields differentiable at the point) ↔ torsion = 0; e… |
| V6.14 | Lemma 8.6: the fundamental lemma of Riemannian geometry | narrower | failed | failed | incomparable | failed | A (universes 0): embedded N ⊆ V — existence (the induced P(dY(X)) is symmetric and compatible), Koszul formula and uniqueness among operations on maps N → V; abstract Mathlib connections — Koszul form… |
| V6.15 | Lemma 8.7 | narrower | failed | failed | incomparable | proved | A (universes 0; velX, velY, covDerivX, covDerivY definitions): for a slice submanifold N ⊆ V and a smooth surface s : ℝ² → N, D/∂x := P ∘ ∂/∂x (computed in V), D/∂x W = P(∂W/∂x) for differentiable W, … |
| V6.16 | The curvature tensor and its sign | same | proved | proved | equivalent | proved | A (universes 0; milnorCurvature, nomizuCurvature (abstract Mathlib CovariantDerivative, any model), curvature (embedded) are definitions; B's curv/nomizuCurv are definitionally A's): Nomizu's R = −Mil… |
| V6.17 | Lemma 9.1: the curvature is a tensor | narrower | failed | failed | incomparable | proved | A (universes 0; curvOp, curvTensor definitions): for the induced metric of a slice submanifold N ⊆ V and smooth tangent fields, R(X,Y)Z = II(Y,II(X,Z)) − II(X,II(Y,Z)) at q, equal to the trilinear map… |
| V6.19 | Lemma 9.2 | narrower | failed | failed | incomparable | proved | A (universes 0): Lemma 9.2 for a smooth surface s : ℝ² → N in a slice submanifold N ⊆ V and a smooth tangent field W along s: D/∂y D/∂x W − D/∂x D/∂y W = curvOp(∂s/∂x, ∂s/∂y) W, with D/∂x = P∘∂/∂x and… |
| V6.20 | Lemma 9.3, symmetries (1)–(3) | narrower | failed | failed | incomparable | proved | A (universes 0; IsCurvatureTensor is a definition): the algebraic equivalence (∀Z W, ⟨TZ,W⟩+⟨TW,Z⟩=0) ↔ ∀Z, ⟨TZ,Z⟩=0 on any real inner product space, and Lemma 9.3 (1)–(3) for the induced metric of a … |
| V6.21 | Lemma 9.3, symmetry (4): the octahedron | stronger | failed | failed | incomparable | proved | A (universes 0): the octahedron as pure algebra for any T : α⁴ → ℝ satisfying (1),(2),(3) (any index type α); (4) for trilinear maps satisfying (1)–(3); (4) for the curvature of smooth tangent fields … |
| V6.22 | Sectional curvature | stronger | failed | failed | incomparable | A_to_Bemb_only | A (universes 0; sectionalCurvature is a definition): pure algebra for any trilinear R on a real inner product space satisfying (1)–(3): sectional curvature ⟨R(X,Y)X,Y⟩/(‖X‖²‖Y‖²−⟨X,Y⟩²) is invariant u… |
| V6.3 | Affine connections on an abstract manifold | restated | failed | proved | A_narrower | failed | A (universes 0): for any Mathlib CovariantDerivative on the tangent bundle of any manifold (any model I), Milnor's rules (3) (cov Y x (f x • X x) = f x • cov Y x (X x)), additivity in Y and the Leibni… |
| V6.4 | The connection of the induced metric, and rules (1)–(4) | narrower | failed | proved | incomparable | Bemb_to_A_only | A (universes 0): for a slice submanifold N ⊆ V and the induced connection (X ⊢ Y)_q = P_q(dY_q(X_q)) (project-defined covAt/leviCivita on maps N → V), Milnor's rules: (1) smooth for smooth tangent X a… |
| V6.5 | Covariant derivative along a curve | narrower | failed | failed | incomparable | not_applicable | A (universes 0; velocity, IsFieldAlong, covDeriv are definitions): for a smooth curve c in a slice submanifold N ⊆ V, the velocity c'(t) ∈ T_{c(t)}N, and the project's DX/dt := P_{c(t)} X'(t) satisfie… |
| V6.6 | Lemma 8.1 | narrower | failed | failed | incomparable | proved | A (universes 0): Lemma 8.1 for the induced connection of a slice submanifold N ⊆ V: covDeriv (P_{c(t)} X') satisfies the project's IsCovDerivAlong (axioms (a)-(c) on smooth tangent fields ℝ → V), and … |
| V6.7 | Global solutions of linear equations | narrower | failed | failed | incomparable | not_applicable | A (universe 0): for continuous A : ℝ → (E →L E), E any real normed space, two solutions of x' = A(t)x agreeing at one time agree on an open interval / on ℝ; and if ⟨A(t)x, x⟩ = 0 (E a complete inner p… |
| V6.8 | Lemma 8.2: parallel fields | narrower | failed | failed | incomparable | proved | A (universes 0; IsParallel is a definition): Lemma 8.2 for the induced connection of a slice submanifold N ⊆ V: along a smooth curve, every v ∈ T_{c(t₀)}N (any t₀) extends to exactly one parallel fiel… |
| V6.9 | Parallel translation is a linear isometry | stronger | failed | failed | incomparable | proved | A (universes 0): for a slice submanifold N of a Euclidean V with the induced connection (DX/dt = P X'), two parallel fields along any curve have constant inner product (i.e. the induced connection IS … |
| V7.1 | Geodesics | narrower | proved | proved | incomparable | proved | Both directions are vacuous. B (definition item, abstract ℝⁿ-manifold): with B's own definitions IsGeodesic ↔ 'acceleration field D/dt(dc/dt) exists and vanishes' ↔ 'velocity parallel' — a tautology, … |
| V7.10 | Lemma 10.3: uniformly normal neighbourhoods | restated | failed | failed | incomparable | proved | B: Lemma 10.3 (1)–(3) for every abstract connected Hausdorff ℝⁿ-manifold with a smooth Mathlib Riemannian metric and any Levi-Civita CovariantDerivative. The lengths and the ε-balls of T_qM are now Ri… |
| V7.10′ | The remark after Lemma 10.3: convex neighbourhoods | restated | failed | failed | incomparable | A_to_Bemb_only | B: on every abstract connected ℝⁿ-manifold with a smooth Mathlib Riemannian metric and any Levi-Civita connection, each p has an open W and ε > 0 such that W, ε satisfy Lemma 10.3 (1)–(3) (Riemannian … |
| V7.11 | Piecewise smooth paths and their lengths | explicit | proved | proved | incomparable | proved | Both directions are vacuous: each conclusion is proved outright, without the hypothesis. B (what Milnor's use of lengths presupposes) holds on every abstract Riemannian manifold. Part (i), B_part_i: t… |
| V7.12 | Lemma 10.5: the Gauss lemma | stronger | failed | failed | incomparable | proved | B is the Gauss lemma for every abstract connected ℝⁿ-manifold with a smooth Mathlib Riemannian metric and any Levi-Civita connection, for any normal ball (Riemannian ε-ball). It is stated in Milnor's … |
| V7.13 | Lemma 10.6: length and radius in a normal ball | narrower | failed | failed | incomparable | proved | B (Lemma 10.6, Riemannian norms): for every abstract connected Hausdorff ℝⁿ-manifold with any smooth Mathlib RiemannianBundle metric and any Levi-Civita CovariantDerivative (Milnor's axioms), any blin… |
| V7.14 | Paths leaving a normal ball: the shell crossing | restated | failed | failed | incomparable | proved | B (p. 61, proof of Thm 10.4): for any blind normal ball (Riemannian radius ε) at q of an abstract connected Riemannian ℝⁿ-manifold with any Levi-Civita connection, 0 < r < ε, and any piecewise smooth … |
| V7.15 | Theorem 10.4: short geodesics are shortest | stronger | failed | failed | incomparable | proved | B (Thm 10.4): for W, ε as in Lemma 10.3 (blind IsUniformNormal: unique short geodesics, smooth dependence into TM, Riemannian normal balls of radius ε containing W) on an abstract connected Riemannian… |
| V7.16 | The equality case of Theorem 10.4, sharp form | stronger | failed | failed | incomparable | A_to_Bemb_only | B (p. 61 remark): for W, ε as in Lemma 10.3 (blind IsUniformNormal) on an abstract connected Riemannian ℝⁿ-manifold with any Levi-Civita connection, if a piecewise smooth ω : [0,1] → M from q₁ to q₂ h… |
| V7.17 | Corollary 10.7: shortest paths are geodesics | stronger | failed | proved | A_narrower | proved | A (universes 0): being a geodesic on an open set is local; a minimizing unit-speed piecewise smooth path c on [0,ℓ] in N agrees on each subinterval inside a uniformly normal O with a geodesic; Corolla… |
| V7.18 | The distance $\rho$ | restated | failed | failed | incomparable | proved | A (riemDist: ℝ≥0∞-valued infimum of pathLength over piecewise smooth paths in N; riemDist_le_pathLength and riemDist_triangle at universe 0 for ANY subset N ⊆ V): riemDist ≤ pathLength, triangle inequ… |
| V7.19 | Metric balls and the topology | restated | failed | failed | incomparable | proved | A (universes 0): for a slice submanifold N ⊆ V with the induced metric (ρ = Morse.riemDist, ℝ≥0∞-valued, N not assumed connected): ρ(p, exp_p v) = ‖v‖ inside a normal ball, metric balls of radius r ≤ … |
| V7.2 | Constant speed and homogeneity | stronger | failed | failed | incomparable | proved | A (universes 0): for a geodesic of a slice submanifold N ⊆ V on an OPEN set s: d/dt‖γ'‖² = 0, constant speed on preconnected s, length of γ on [a,b] ⊆ s is ‖γ'(t₀)‖(b − a), and t ↦ γ(at + b) is a geod… |
| V7.20 | Corollary 10.8: short joins on a compact set | restated | failed | failed | incomparable | A_to_Bemb_only | A (universes 0; IsShortJoin a definition): for a slice submanifold N ⊆ V with the induced metric, the local form (around each p ∈ N an open Ω and s > 0 such that IsShortJoin δ y z for y ∈ N ∩ Ω, ρ(y,z… |
| V7.21 | Continuity and finiteness of $\rho$; the metric space $(N, \rho)$ | restated | failed | failed | incomparable | proved | A (universes 0; riemEMetricSpace, riemMetricSpace definitions): ‖q − p‖ ≤ ρ(p, q) for ANY subset N ⊆ V (chord bound, ambient); ρ = riemDist continuous on N × N (ℝ≥0∞-valued, N possibly disconnected); … |
| V7.22 | Metric and geodesic completeness | restated | failed | failed | incomparable | proved | A (universes 0; IsRiemComplete, IsRiemBounded, IsGeodesicallyComplete are definitions): for a slice submanifold N ⊆ V with the induced metric, (i) if exp_q is defined on all of T_qN at ONE point q, th… |
| V7.23 | The geodesic flow, and the continuity of $\exp$ | explicit | failed | failed | incomparable | A_to_Bemb_only | A (universes 0), for a slice submanifold N ⊆ V with the induced metric: a geodesic on an open preconnected s ∋ 0 is t ↦ exp_{γ(0)}(tγ'(0)); the uniform local geodesic flow near each x₀ (speeds < R, un… |
| V7.24 | Minimal geodesics | restated | proved | proved | incomparable | not_attempted | Both directions are vacuous. B (abstract Riemannian manifold, any Levi-Civita cov; IsMinimal = geodesic on [a,b] whose arcLen is ≤ that of every piecewise smooth path with the same end points) says, f… |
| V7.25 | The two steps of the proof of Theorem 10.9 | explicit | failed | failed | incomparable | proved_partial | A (universes 0; slice submanifold N ⊆ V): (1) for normal coordinates of ANY radius ε at p and EVERY δ ∈ (0, ε), δ < ρ(p,q) < ∞ ⇒ ∃ w ∈ T_pN, ‖w‖ = δ, ρ(p,q) = δ + ρ(exp_p w, q); (2) broken_geodesic_eq… |
| V7.26 | Theorem 10.9: the Hopf–Rinow theorem | stronger | failed | failed | incomparable | proved_partial | A (universes 0; slice submanifold N ⊆ V, induced metric): theorem_10_9 (exp_p defined on all of T_pN for ONE p and ρ(p,q) < ∞, N not assumed connected ⇒ q = exp_p v, ‖v‖ = ρ(p,q), t ↦ exp_p(tv) minima… |
| V7.27 | Corollary 10.10: bounded sets and metric completeness | stronger | failed | failed | incomparable | proved_partial | A (universes 0; slice submanifold N ⊆ V): (1) N preconnected and exp_p defined on T_pN for ONE p ⇒ ρ-bounded sets have compact closure ⊆ N; (2) bounded sets have compact closure in N ⇒ (N, ρ) complete… |
| V7.28 | The converse of Corollary 10.10 | stronger | failed | proved | A_narrower | proved | A (universes 0): for ANY slice submanifold N ⊆ V (model Z arbitrary, N not assumed connected), IsRiemComplete N ⇒ IsGeodesicallyComplete hN (exp_q v defined by a geodesic on an open interval ⊇ [0,1]).… |
| V7.29 | The Hopf–Rinow equivalence | stronger | failed | failed | incomparable | proved | B: for every abstract connected Hausdorff ℝⁿ-manifold with ANY smooth Mathlib RiemannianBundle metric and ANY Levi-Civita CovariantDerivative (Milnor's sense), geodesic completeness (exp_q defined on … |
| V7.3 | The geodesic equation | restated | failed | failed | incomparable | A_to_Bemb_only | A (universes 0; geodesicSpray, chartSpray definitions): for a slice submanifold N ⊆ V, the geodesic equation γ'' = II(γ',γ') (both directions), its first-order form as integral curves of the spray (x,… |
| V7.30′ | Familiar examples of geodesics: $\mathbb R^n$ and $S^n$ | narrower | failed | failed | incomparable | not_attempted | B: for abstract connected Riemannian n-manifolds M with any Levi-Civita CovariantDerivative and a smooth injective isometric immersion f onto ℝⁿ / Sⁿ / the cylinder x²+y²=1 / a rotation-invariant surf… |
| V7.4 | Theorem 10.1: existence, uniqueness and smooth dependence for ODEs | stronger | proved | failed | A_stronger | not_applicable | A (universes 0): local flows of C^∞ first-order systems x' = G(x) on finite-dimensional E with smooth dependence on the initial point; Theorem 10.1 for u'' = F(u,u') on finite-dimensional E (neighbour… |
| V7.5 | Uniqueness of geodesics in the large | explicit | failed | proved | A_narrower | proved | A (universes 0; projRep a definition): for a slice submanifold N ⊆ V, two geodesics (on open sets) with the same position and velocity at t₀ agree near t₀, and on all of an open preconnected s. B: uni… |
| V7.6 | Lemma 10.2: geodesics for small initial velocities | stronger | failed | failed | incomparable | proved | A (universes 0): for a slice submanifold N ⊆ V with the induced connection, local sprays exist in slice charts, their curves are geodesics on the OPEN interval (-2,2) depending smoothly on (u,w,t), an… |
| V7.7 | The exponential map | restated | failed | proved | A_narrower | proved | A (universes 0; IsGeodesicFrom/expDom/exp definitions: exp_q v = γ(1) for a chosen geodesic γ on an open (-δ,1+δ) with γ0=q, γ'0=v, junk q): exp_q v = γ(1) for every such γ, exp_q 0 = q (q ∈ N), exp_q… |
| V7.8 | The tangent manifold, $\exp$ near the zero section, and $d(\exp_q)_0$ | stronger | failed | failed | incomparable | proved | A (universes 0): TN = {(q,v) / v ∈ T_qN} ⊆ V×V is a slice submanifold; exp agrees locally on TN with smooth maps on U × ball 0 ε; there is an open O ⊇ N×{0} with O∩TN ⊆ expDom on which exp is C^∞ (Con… |
| V7.9 | Normal radius | restated | failed | proved | A_narrower | proved | The listed declarations (Morse.NormalCoord, Morse.IsNormalRadius, Morse.expToN, Morse.NormalCoord.expDiffeo) are all definitions, so A = True and B ⇒ A is trivial (vacuous). B is Lemma 10.3 (3) withou… |
| V8.1 | The path space and its “tangent spaces” | restated | failed | proved | incomparable | not_attempted | A (universes 0) is only the unfolding of the project's DEFINITION pathTangent hN c (a Submodule of ℝ → V: piecewise smooth X, tangent to N along c on [0,1], X 0 = X 1 = 0) — mem_pathTangent is Iff.rfl… |
| V8.10 | Geodesics of $\Omega$, and criticality through the first variation | restated | failed | failed | incomparable | proved | A (universes 0), for slice submanifolds N ⊆ V with the induced metric only: (i) c ∈ Ω(N;p,q) is a critical path of E (all variations IsVariation, any open U ⊆ ℝ, any break set) iff the first-variation… |
| V8.11 | Corollary 12.3: the critical paths of $E$ are the geodesics | explicit | failed | failed | incomparable | proved | A (universes 0), for slice submanifolds N ⊆ V with the induced metric: Corollary 12.3 (c ∈ Ω(N;p,q) is a critical path of E iff it is an unbroken geodesic) plus the three steps of its proof — accel_eq… |
| V8.12 | The curvature identity (13.3), and jumps under differentiation | restated | failed | failed | incomparable | A_to_Bemb_only | A (universes 0), for slice submanifolds N ⊆ V: curvR_of_mem (unfolding of the definition curvR); curvature_identity, (13.3) for ANY smooth surface F in N on an open O ⊆ ℝ² (P ∂_u(P ∂²_tF) = P ∂_t(P ∂_… |
| V8.13 | Theorem 13.1: the second variation formula | restated | failed | failed | incomparable | proved | A (universes 0), for slice submanifolds N ⊆ V: Theorem 13.1 for every 2-parameter variation (IsVariation, U ⊆ ℝ² open, any break set) of an unbroken geodesic — the iterated LINE derivative ∂/∂u₁(∂E(α(… |
| V8.14 | The Hessian $E_{**}$ | restated | failed | failed | incomparable | A_to_Bemb_only | A (universes 0), for slice submanifolds N ⊆ V: energyHessian is a DEFINITION (the bilinear form 2·secondVariation γ on TΩ_γ = pathTangent, Milnor's formula); A = energyHessian_apply (rfl unfolding), I… |
| V8.16 | Corollary 13.4: $E_{**}$ is symmetric and bilinear | restated | failed | failed | incomparable | A_to_Bemb_only | A (universes 0), for slice submanifolds N ⊆ V only: ⟨R(v,w₁)v,w₂⟩ = ⟨R(v,w₂)v,w₁⟩ for tangent vectors; symmetry of the integral form hessForm on pathTangent for every γ ∈ Ω (geodesic or not); symmetry… |
| V8.17 | Remark 13.5: the second derivative along a 1-parameter variation | explicit | failed | proved | incomparable | proved | A (universes 0), for slice submanifolds N ⊆ V only: for a 1-parameter variation α (U ⊆ ℝ) of an unbroken geodesic γ, HasDerivAt (deriv (u ↦ E(α u))) (2·secondVariation γ W W) 0, and the same value wri… |
| V8.18 | Lemma 13.6: the Hessian at a minimal geodesic | narrower | failed | proved | incomparable | A_to_Bemb_only | A (universes 0), for slice submanifolds N ⊆ V only: if γ is a minimal path of Ω(N;p,q) and an unbroken geodesic, then 0 ≤ energyHessian(X, X) for every X ∈ TΩ_γ (formula-defined E_**; 'index 0' not st… |
| V8.2 | Variations and variation fields | stronger | failed | proved | incomparable | not_attempted | A (universes 0): for slice submanifolds N ⊆ V, variations IsVariation N U α B with parameters in an open U ∋ 0 of any normed space P (fixed end points, smooth on strips avoiding a finite break set): e… |
| V8.3 | Lemma 11.A: every family of tangent fields comes from one variation | stronger | failed | failed | incomparable | not_attempted | A (universes 0): Lemma 11.A for slice submanifolds N ⊆ V (completeness not assumed): for ω ∈ Ω(N;p,q) and any piecewise smooth family Λ(t) : P →L V of tangent maps vanishing at 0, 1, the formula exp_{… |
| V8.4 | Critical paths of the energy | narrower | proved | proved | equivalent | proved | The only listed declaration, Morse.IsCriticalPath, is a definition, so A = True and both directions are vacuous: B is proved outright (B_holds), since it only says that the blind definition (Fréchet d… |
| V8.5 | Energy and length | stronger | failed | failed | incomparable | proved | A (universe 0): for any path c : ℝ → E into a real normed space (any norm, not only Euclidean), piecewise smooth on [a, b] with a ≤ b arbitrary: L² ≤ (b−a)E; L² = (b−a)E iff ‖c'‖ is constant at the po… |
| V8.6 | Lemma 12.1: the energy at a minimal geodesic | narrower | failed | failed | incomparable | proved | A (universes 0): for a slice submanifold N ⊆ V (completeness NOT assumed), a path γ ∈ Ω(N;p,q) of length ≤ every path of Ω(N;p,q) that is an unbroken geodesic satisfies E(γ) ≤ E(ω) for all ω ∈ Ω(N;p,q… |
| V8.7 | Velocity jumps, acceleration and the first variation | restated | failed | failed | incomparable | A_to_Bemb_only | A (universe 0) is the only listed theorem, Morse.finsum_jump_eq_sum: for c, X : ℝ → V (inner product space) and a finite B such that c is differentiable on (0,1) off B, Σᶠ_{t∈(0,1)} ⟨X t, Δ_t c'⟩ = Σ_… |
| V8.9 | Theorem 12.2: the first variation formula | stronger | failed | failed | incomparable | proved | A (universes 0): for slice submanifolds N ⊆ V with the induced metric and project variations IsVariation N U α B (U ⊆ ℝ, finite break set B): formula (12.2′) at every u₀ ∈ U, and Theorem 12.2 at u = 0… |
| V9.1 | Linear equations have global solutions (Lemma 14.A) | stronger | failed | proved | incomparable | failed | A (universes 0) is pure ODE theory on a Banach space E for x' = A(t)x: global existence on ℝ for continuous A (Grönwall + truncated Picard–Lindelöf), uniqueness on a closed [a,b] by the value at any p… |
| V9.10 | A Jacobi field is determined by its values at two non-conjugate points | stronger | failed | failed | incomparable | proved | B: on every abstract connected Hausdorff ℝⁿ-manifold with any smooth Mathlib RiemannianBundle metric and any Levi-Civita connection (Milnor's axioms), along a geodesic γ on [0,1], if a ≠ b in [0,1] ar… |
| V9.11 | Remark 14.5: Jacobi fields along short geodesics | restated | failed | failed | incomparable | failed | B: on every abstract connected Riemannian ℝⁿ-manifold with a Levi-Civita connection, for EVERY open U with unique minimal geodesics depending smoothly on the end points (GoodNbhd) and EVERY geodesic s… |
| V9.12 | Remark 14.6: no conjugate points near the start | narrower | failed | failed | incomparable | proved | B: on every abstract connected Riemannian ℝⁿ-manifold with a Levi-Civita connection, along a geodesic γ on [0,1]: (i) some δ > 0 with no t ∈ (0,δ) ∩ [0,1] conjugate to 0; (ii) the parameters conjugate… |
| V9.13 | The index and the nullity of a bilinear form | restated | false | proved | incomparable **B false** | not_applicable | B is false (not_B): its clause (2) 'if the index is finite it is attained' quantifies over arbitrary SETS A ⊆ V; for A = ∅ the index (empty supremum) is 0 but no subspace lies in ∅. Hence A ⇒ B is fal… |
| V9.15 | The second variation formula for piecewise Jacobi fields | explicit | failed | failed | incomparable | A_to_Bemb_only | B (abstract connected Riemannian ℝⁿ-manifolds, γ a geodesic): for a broken Jacobi field W₁ (pieces' DW₁/dt = D1 i) and W₂ ∈ TΩ_γ, the variational E_** IsHessT 1 γ W₁ W₂ has the value −2 Σ ⟨W₂(t_i), Δ_… |
| V9.16 | Positivity near zeros, and fine subdivisions | restated | failed | failed | incomparable | failed | A (universes 0; slice submanifolds N ⊆ V, ANY smooth curve γ, no geodesic hypothesis) is the project's ANALYTIC substitute for fine subdivisions: a mesh h₀ = fineMesh built from curvature bounds; hess… |
| V9.17 | Broken Jacobi fields and $T'$ | restated | failed | failed | incomparable | failed | A (universes 0; slice submanifolds, ANY smooth curve γ, 0 < τ ≤ 1, division points B with IsFine = pieces of parameter length ≤ h₀ = fineMesh): exists_isBrokenJacobi (a broken Jacobi field takes any p… |
| V9.18 | Lemma 15.3: the splitting of $T\Omega_\gamma$ | restated | failed | failed | incomparable | failed | A (universes 0; slice submanifolds, ANY smooth curve γ, any 0 < τ ≤ 1, IsFine subdivision = pieces ≤ h₀): Lemma 15.3 for the formula-defined bilinear form energyHessian on fields along γ/[0,τ] — the e… |
| V9.19 | Lemma 15.4: the index on the broken Jacobi fields | restated | failed | failed | incomparable | failed | A (universes 0; slice submanifolds, ANY smooth curve γ, any 0 < τ ≤ 1, IsFine subdivision = pieces ≤ h₀): Lemma 15.4 for the formula-defined energyHessian — equal index on fieldsUpTo τ and on brokenSp… |
| V9.2 | Jacobi fields and the Jacobi system | restated | failed | failed | incomparable | failed | A (universes 0): for slice submanifolds N ⊆ V with the induced metric and ANY smooth curve γ in N on [0,1] (not only geodesics), the Jacobi equation is encoded WITHOUT a frame as the first-order linea… |
| V9.20 | $\lambda(\tau)$, and Assertions (1) and (2) | restated | failed | failed | incomparable | A_to_Bemb_only | A (universes 0; slice submanifolds, ANY smooth curve γ): with λ(τ) = indexUpTo τ = formIndex of the formula-defined energyHessian (of E_0^1) on fields of TΩ_γ vanishing outside [0,τ]: λ(1) = formIndex… |
| V9.21 | The forms $H_\tau$ and their continuity (Lemma 15.C) | explicit | failed | failed | incomparable | failed | A (universes 0; slice submanifolds, ANY smooth curve γ, finite division set B, validFor = {τ ∈ (0,1] / B is IsFine for [0,τ]}): Hform τ = energyHessian (formula-defined) on brokenSpace B τ transported… |
| V9.22 | Assertion (3): $\lambda$ is continuous from the left | same | failed | failed | incomparable | proved | A (universes 0; slice submanifolds, ANY smooth curve γ): Assertion (3) as ∀ τ ∈ (0,1], ∀ᶠ τ' in 𝓝[<] τ, indexUpTo τ' = indexUpTo τ, with λ = index of the formula-defined energyHessian on fields suppor… |
| V9.23 | Assertion (4): the jump of $\lambda$ | stronger | failed | failed | incomparable | proved | B: on every abstract connected Riemannian ℝⁿ-manifold with any Levi-Civita connection, for a geodesic γ and 0<τ<1, λ(τ+ε) = λ(τ) + ν for small ε>0, λ(τ) the index of Milnor's VARIATIONAL (E_0^τ)_** on… |
| V9.24 | Theorem 15.1: the Morse index theorem | stronger | failed | failed | incomparable | proved | B: on every abstract connected Hausdorff ℝⁿ-manifold with any smooth metric and any Levi-Civita connection, for a geodesic γ on [0,1], λ = Σ'_{t∈(0,1)} conjMult(0,t) in ℕ∞ and λ ≠ ⊤, with λ the index … |
| V9.25 | Corollary 15.2: finitely many conjugate points | restated | failed | failed | incomparable | proved | B: on every abstract connected Hausdorff ℝⁿ-manifold with any smooth metric and any Levi-Civita connection (Milnor's axioms), for a geodesic γ on [0,1], {t ∈ (0,1] / IsConj γ 0 t} is finite. A (univer… |
| V9.3 | The space of Jacobi fields (Corollary 14.B) | stronger | failed | failed | incomparable | proved | A (universes 0): for slice submanifolds N ⊆ V (model Z) and ANY smooth curve γ in N on [0,1], J ↦ (J(s), DJ/dt(s)) is a bijection from the space jacobiSpace of Jacobi fields (normalized constant off [… |
| V9.4 | Conjugate points and their multiplicity | restated | proved | proved | equivalent | proved | Vacuous equivalence: both sides are consistency statements between a definition of conjugate points and a definition of multiplicity, and both are provable outright. A (universes 0, isConjugate_iff): … |
| V9.5 | Theorem 14.1: the null vectors of $E_{**}$ are the Jacobi fields | restated | failed | failed | incomparable | proved | A (universes 0): for slice submanifolds N ⊆ V and γ ∈ Ω(N;p,q) an unbroken geodesic: Theorem 14.1 for energyHessian := 2·secondVariation (bilinear form on TΩ_γ DEFINED by the second variation formula)… |
| V9.6 | Theorem 14.1: the null space and the nullity | restated | failed | proved | incomparable | proved | A (universes 0): for slice submanifolds N ⊆ V and γ ∈ Ω(N;p,q) an unbroken geodesic: hessNullSpace (image under X ↦ X∘projIcc of the kernel of the formula-defined energyHessian on TΩ_γ) = conjSpace 0 … |
| V9.7 | Remark 14.2: the nullity is less than $n$ | stronger | failed | failed | incomparable | proved | B (Remark 14.2): for every abstract connected Hausdorff ℝⁿ-manifold with any smooth metric and any Levi-Civita connection and every geodesic γ : [0,1] → M with γ'(0) ≠ 0: the nullity of the blind E_**… |
| V9.7′ | Example 1: no conjugate points in a flat space | narrower | failed | failed | incomparable | proved | B (Example 1): for every abstract connected Hausdorff ℝⁿ-manifold with a Levi-Civita connection whose curvature vanishes identically (flat) and every geodesic γ on [0,1]: Jacobi ⇔ D²J/dt² = 0, a non-z… |
| V9.7″ | Example 2: antipodal points of $S^n$ | stronger | failed | failed | incomparable | proved | B (Example 2): for n ≥ 2, every abstract connected Hausdorff ℝⁿ-manifold M with any smooth metric, any Levi-Civita connection, and a diffeomorphism φ onto Mathlib's sphere S^n ⊆ ℝⁿ⁺¹ that is an isomet… |
| V9.8 | Lemma 14.3: variations through geodesics give Jacobi fields | explicit | failed | failed | incomparable | proved | B (Lemma 14.3): for every abstract connected Hausdorff ℝⁿ-manifold with any smooth RiemannianBundle metric and any Levi-Civita CovariantDerivative (Milnor's axioms), if α : ℝ¹ × ℝ → M is C^∞ on ball(0… |
| V9.9 | Lemma 14.4: every Jacobi field comes from a variation through geodesics | same | failed | failed | incomparable | proved | B (Lemma 14.4): for every abstract connected Hausdorff ℝⁿ-manifold with any smooth metric and any Levi-Civita connection, every Jacobi field J along a geodesic γ : [0,1] → M (Jacobi equation on [0,1])… |
| V10.1 | Milnor's metric on $\Omega$ | restated | failed | proved | A_narrower | A_to_Bemb_only | A (universe 0) is the item's only theorem, PathSp.edist_eq_zero_of_eqOn: for ANY set N in an inner product space, two paths of Ω(N;p,q) agreeing on [0,1] are at distance 0 for the project's Milnor pse… |
| V10.10 | Lemma 15.4 for the subdivision of §16 | explicit | failed | failed | incomparable | failed | A (universes 0; slice N ⊆ V, induced metric, Morse.BrokenSetup = §16 data with the project's δ: IsShortJoin (unique join vector, ρ = ‖v‖, smooth dependence) AND normal radii ≥ δ on S, c·len < δ²): for… |
| V10.11 | Theorem 16.2: the index and nullity of $E'$ | explicit | failed | failed | incomparable | failed | A (universes 0; chartBrokenEquiv is vocabulary): hasDerivAt_deriv_line (second derivative along a line = hessian z z), hessian_eq_energyHessian (for a BrokenSetup, open O ⊆ V^m with N^m ∩ O ⊆ nodes, F… |
| V10.12 | Theorem 16.3 in the finite-dimensional model | narrower | failed | failed | incomparable | not_applicable | A (universes 0): exists_contDiff_eq_of_locally (smooth extension from a compact set), isFiniteCellComplexType_sublevel_of_isCompact (Theorem 3.5 for a sublevel {F ≤ a₀} of an ambient smooth F on a sli… |
| V10.13 | Theorem 16.3: the homotopy type of $\Omega^a$ | narrower | failed | failed | incomparable | failed | A (universes 0; BrokenSetup on a slice N ⊆ V, a < c): theorem_16_3_Omega/_count — if NO geodesic of Ω(N;p,q) has energy exactly a and every geodesic with E ≤ a has hessNullity 0, then {γ : PathSp N p … |
| V10.14 | The Remark on p. 92: a minimum of $E'$ | narrower | failed | failed | incomparable | failed | A (universes 0; BrokenSetup on a slice N ⊆ V): nodeVal_mem_nodes_of_energy_lt (a path with E < c has its break points in U = B.nodes with E' ≤ E) and exists_energy_minimizing (given some path with E <… |
| V10.15 | The full path space $\Omega^*$ and the inclusion $i$ | restated | failed | proved | A_narrower | A_to_Bemb_only | A (universe 0) is the item's only theorem PathSp.edist_toPathC_le: for ANY set N ⊆ V, the uniform distance in C([0,1],V) for the NORM of V between toPathC γ, toPathC γ' is ≤ Milnor's d (pathCSet, Path… |
| V10.18 | Dyadic broken geodesics as homotopy inverses (Lemma 17.C) | restated | failed | failed | incomparable | failed | B (Milnor's Lemma 17.C literally): for every abstract Riemannian M with Levi-Civita connection, a continuous A : Ω* → (0,1] and a CONTINUOUS h : Ω* → Ω (d-topology) with h(ω) the broken minimal geodes… |
| V10.19 | Theorem 17.1: $\Omega$ and $\Omega^*$ are homotopy equivalent | same | failed | failed | incomparable | Bemb_to_A_only | B = (Lemma 17.C as in V10_18: continuous A and continuous broken-geodesic h with h∘i ≃ id, i∘h ≃ id) ∧ (Theorem 17.1: every natural i : Ω → Ω* is a homotopy equivalence), on abstract Riemannian M (not… |
| V10.2 | The energy is continuous for $d$ (Lemmas 16.A and 16.B) | stronger | failed | failed | incomparable | proved | B: on every abstract connected Hausdorff ℝⁿ-manifold with a smooth metric, E = E_0^1 is ε-δ continuous for Milnor's d (blind dOm: real ⨆_t ρ + L² distance of ds/dt, ds/dt the derivative of the arc len… |
| V10.20 | Relative cell complexes and the tower | restated | failed | failed | incomparable | failed | B: for abstract complete M, p, q non-conjugate, levels a_0 < a_1 < … → ∞ (none critical, Ω^{a_0} = ∅, exactly one critical value in each (a_i, a_{i+1})), there are Mathlib CW complexes K_0 = ∅ ⊆ K_1 ⊆… |
| V10.21 | The step from $\Omega^a$ to $\Omega^b$ | restated | failed | failed | incomparable | failed | B: for abstract complete M, p, q non-conjugate, a < b non-critical: a space Y with a Mathlib relative CW structure rel D, φ : Ω^a → Y a homotopy equivalence onto D, f : Ω^b → Y one onto Y, f/Ω^a = φ S… |
| V10.22 | Theorem 17.3: the fundamental theorem of Morse theory | narrower | failed | failed | incomparable | failed | B (abstract connected Hausdorff Riemannian ℝⁿ-manifolds, any Levi-Civita connection, metric-complete, p, q not conjugate along any geodesic): Ω (blind Om) and Ω* are each homotopy equivalent to a coun… |
| V10.23 | The geodesics from $p$ to $q$ on $S^n$, and their indices | restated | false | proved | incomparable **B false** | A_to_Bemb_only | B is false (not_B): it allows n = 1 and claims that every interior passage of γ_k through p or p' is CONJUGATE to p (blind IsConj: a non-zero Jacobi field vanishing at 0 and t) with multiplicity n−1; … |
| V10.24 | Corollary 17.4: the cells of the path space of $S^n$ | narrower | failed | failed | incomparable | failed | B: for every abstract Riemannian ℝⁿ-manifold M with ψ : M → ℝⁿ⁺¹ a smooth injective isometric map onto the unit sphere (n ≥ 1), any Levi-Civita connection, and q ≠ p, p' (via ψ): both Ω(M; p, q) (blin… |
| V10.25 | The homology of a path space read off from its geodesics | restated | failed | failed | incomparable | failed | B: for every abstract Riemannian ℝⁿ-manifold M isometric to Sⁿ via ψ (n > 2), q ≠ p, p': the INTEGRAL singular homology of Ω(M; p, q) (blind Om) and of Ω* is ℤ in degrees k(n−1), zero otherwise. A (un… |
| V10.26 | The homology of the path space of $S^n$ | narrower | failed | failed | incomparable | failed | B: for every abstract Riemannian ℝⁿ-manifold M isometric to Sⁿ via ψ (n > 2), q ≠ p, p': INTEGRAL singular homology of Ω(M; p, q) (blind Om) and of Ω* is ℤ in degrees k(n−1) and zero otherwise, and bo… |
| V10.29 | Corollary 17.2 | restated | failed | failed | incomparable | failed | B: for EVERY abstract connected Hausdorff ℝⁿ-manifold with a smooth Riemannian metric (no completeness) and all p, q, both Ω* (continuous paths, compact-open) and Ω (blind Om, d-topology) are homotopy… |
| V10.3 | The ball $S$, subdivisions, and Milnor’s choices | restated | failed | failed | incomparable | A_to_Bemb_only | B: on every abstract connected Hausdorff ℝⁿ-manifold with a smooth metric and a Levi-Civita connection, for c > 0 with Ω^c ≠ ∅: (a) paths of Ω^c stay in S = {ρ(p,·) ≤ √c}; (b) MetricComplete ⇒ S compa… |
| V10.30 | Corollary 17.4 for the loop space | narrower | failed | failed | incomparable | failed | B: for every abstract Riemannian n-manifold M isometric to the round Sⁿ (IsRoundSphere ψ), n ≥ 1, and p ∈ M, both the loop space Ω(M;p,p) (blind Om, d-topology) and Ω* are homotopy equivalent to a Mat… |
| V10.4 | Lemma 16.1: the manifold of broken geodesics | stronger | failed | failed | incomparable | A_to_Bemb_only | B (re-blinded, Ω = maps constant outside [0,1], d a genuine metric): on every abstract connected complete Riemannian ℝⁿ-manifold (any smooth metric, any Levi-Civita connection), for c > 0 with Ω^c ≠ ∅… |
| V10.5 | Broken geodesics and their break points: a homeomorphism up to distance $0$ | restated | failed | failed | incomparable | failed | B (re-blinded, normalized Ω): on every abstract connected complete Riemannian ℝⁿ-manifold, for Milnor's data Setup16 (ε with the conclusion ShortGood of Lemma 10.8 on S, t_{i+1} − t_i < ε²/c) and Ω^c … |
| V10.6 | Theorem 16.2: $E'$ is smooth and $B^a$ is compact | restated | failed | failed | incomparable | failed | B (re-blinded, normalized Ω): on every abstract connected complete Riemannian ℝⁿ-manifold, for Setup16 data and Ω^c ≠ ∅: (a) some F : M^{k−1} → ℝ, C^∞ for the product model on V = ev(B), with F∘ev = E… |
| V10.7 | Milnor’s deformation $r_u$ (Lemma 16.C) | restated | failed | failed | incomparable | failed | B: on every abstract connected complete Riemannian ℝⁿ-manifold (any smooth metric, any Levi-Civita connection), for Milnor's data (Setup16: ε as in Lemma 10.8 on S, tᵢ₊₁−tᵢ < ε²/c), there EXIST r and … |
| V10.8 | Theorem 16.2: $B^a$ is a deformation retract of $\Omega^a$ | restated | failed | failed | incomparable | failed | B: on every abstract connected complete Riemannian ℝⁿ-manifold, for Milnor's data (Setup16), B^a is a strong deformation retract of Ω^a for every a < c and B of Int Ω^c (IsDefRetract: some homotopy H … |
| V10.9 | Theorem 16.2: the critical points of $E'$ | restated | failed | failed | incomparable | failed | B: on every abstract connected complete Riemannian ℝⁿ-manifold, for Milnor's data (Setup16): (1) the critical paths of E (blind IsCriticalPath via variations) in Int Ω^c are exactly the geodesics on [… |
| V11.1 | $\exp$ is smooth on its whole domain | stronger | failed | failed | incomparable | A_to_Bemb_only | B: on every abstract connected Hausdorff ℝⁿ-manifold with any smooth Mathlib RiemannianBundle metric and any Levi-Civita connection, Milnor-complete (ρ-Cauchy sequences converge): for every p, exp_p(v… |
| V11.10 | A geodesic as a smooth curve with a parallel frame | explicit | failed | failed | incomparable | A_to_Bemb_only | B (abstract M, any Levi-Civita cov, n ≥ 1, blind geodesic γ on [0,1]): (a) parallel fields orthonormal at one t₀ ∈ [0,1] are orthonormal on [0,1]; (b) there are parallel P₁..Pₙ along γ on [0,1], ortho… |
| V11.11 | The test fields $\sin(\pi t)P_i(t)$ | restated | false | proved | incomparable **B false** | failed | B is false (not_B): it allows n = 1, where clause (d) claims ∫₀¹ sin²(πt)((n−1)π² − L²K(Pₙ,Pₙ)) < 0 and E**(W_i,W_i) < 0 for some i ≠ n; for n = 1 the integrand vanishes and Fin 1 has no i ≠ n. Counte… |
| V11.12 | Theorem 19.4 (Myers) | explicit | false | proved | incomparable **B false** | A_to_Bemb_only | B is false (not_B): it allows n = 1; on S¹ the Ricci tensor is 0 ≥ (n−1)/r² = 0, the great circle of speed 4 is a geodesic of length 4 > π·1, but S¹ has no conjugate points at all (curvature 0), contr… |
| V11.13 | Corollary 19.5: compactness and diameter | explicit | failed | failed | A_narrower | proved | B (abstract connected Hausdorff ℝⁿ-manifold, any Levi-Civita cov): (M, ρ) Cauchy-complete, r > 0, (n−1)/r² > 0 and K(U,U) ≥ (n−1)/r² ⇒ M compact, ρ(p,q) ≤ πr, and any p, q are joined by a minimal geod… |
| V11.14 | Example: the sphere | narrower | false | proved | incomparable **B false** | failed | B is false (not_B): it allows n = 1 (the circle), where clause (d) ('best possible': a geodesic of length πR whose end points are conjugate) fails — S¹ has no conjugate points. Counter-model: S¹ ⊆ ℝ²,… |
| V11.15 | Test fields on disjoint pieces | explicit | false | proved | incomparable **B false** | A_to_Bemb_only | B is false (not_B, #rt_check OK), as the blind formalizer flagged: B is stated for all n, and for n = 1 the hypothesis K(U,U) ≥ (n−1)/r² = 0 holds on the flat line ℝ¹ (open slice submanifold univ ⊆ ℝ¹… |
| V11.16 | Theorem 19.6: the index estimate | explicit | false | proved | incomparable **B false** | A_to_Bemb_only | B is false (not_B, #rt_check OK) at n = 0: M = ℝ⁰ (the open slice submanifold univ ⊆ ℝ⁰ via RoundTrip.Bridge) is compact and connected, the positivity hypothesis K(U,U) > 0 for U ≠ 0 is vacuous, but B… |
| V11.17 | Theorem 19.2 (Cartan–Hadamard) | same | failed | failed | incomparable | proved | B (Cartan–Hadamard): on every abstract connected Hausdorff ℝⁿ-manifold with any smooth Mathlib RiemannianBundle metric and any Levi-Civita connection, Milnor-complete, simply connected (Mathlib Simply… |
| V11.18 | The path space in non-positive curvature | stronger | failed | failed | incomparable | proved | B: on every abstract connected Hausdorff ℝⁿ-manifold with any smooth Mathlib RiemannianBundle metric and any Levi-Civita connection, Milnor-complete, simply connected, ⟨R(A,B)A,B⟩ ≤ 0, for all p, q: t… |
| V11.2 | $\exp_q$, its derivative, and critical points of $\exp_q$ | restated | failed | failed | incomparable | proved | B (definitions-only item; IsCritMap is defined but B only asserts the properties of γ_v): on every abstract connected Hausdorff ℝⁿ-manifold with any smooth Mathlib RiemannianBundle metric and any Levi… |
| V11.20 | Each homotopy class of paths contains exactly one geodesic | same | failed | failed | incomparable | proved | B: on every abstract connected Hausdorff Riemannian ℝⁿ-manifold with any Levi-Civita connection, Milnor-complete, ⟨R(A,B)A,B⟩ ≤ 0 and NOT simply connected, every Path p q is homotopic rel end points t… |
| V11.21 | Corollary 19.3: the homotopy groups in non-positive curvature | narrower | failed | failed | incomparable | Bemb_to_A_only | B (Corollary 19.3, both halves): on every abstract connected Hausdorff Riemannian ℝⁿ-manifold with any Levi-Civita connection, Milnor-complete, ⟨R(A,B)A,B⟩ ≤ 0: πᵢ(M,x) = 0 for i ≥ 2 (Mathlib Homotopy… |
| V11.22 | Theorem 19.6: positive Ricci curvature and the path space | narrower | failed | failed | incomparable | failed | B (Theorem 19.6): for every compact abstract connected Riemannian ℝⁿ-manifold with any Levi-Civita connection and positive definite (blind) Ricci tensor, and ALL p, q, the blind Ω(M;p,q) (d-topology) … |
| V11.24 | Theorem 19.6 for all end points | explicit | failed | failed | incomparable | failed | B: every compact abstract connected Riemannian ℝⁿ-manifold with any Levi-Civita connection and positive definite (blind) Ricci tensor has, for ALL p, q, Ω(M;p,q) (blind Om, d-topology) homotopy equiva… |
| V11.3 | Theorem 18.1: conjugate points are critical values of $\exp$ | stronger | failed | failed | incomparable | proved | B: on every abstract connected Hausdorff ℝⁿ-manifold with any smooth Mathlib RiemannianBundle metric and any Levi-Civita connection, Milnor-complete (ρ-Cauchy sequences converge), for every p and v ∈ … |
| V11.5 | Corollary 18.2: almost every point is non-conjugate | restated | failed | failed | incomparable | proved | B: on every abstract connected Hausdorff ℝⁿ-manifold with any smooth Mathlib RiemannianBundle metric and any Levi-Civita connection, Milnor-complete: for every p, the set of q joined to p by a geodesi… |
| V11.6 | Non-conjugate points exist, are dense, and are non-degenerate | stronger | failed | failed | incomparable | proved | B: on every abstract connected Hausdorff ℝⁿ-manifold with any smooth Mathlib RiemannianBundle metric and any Levi-Civita connection, Milnor-complete: for every p there is q with p, q not conjugate alo… |
| V11.7 | Lemma 19.1: no conjugate points in non-positive curvature | restated | failed | failed | incomparable | proved | B: on every abstract connected Hausdorff ℝⁿ-manifold with any smooth Mathlib RiemannianBundle metric and any Levi-Civita connection (Milnor's axioms), if ⟨R(A,B)A,B⟩ ≤ 0 for all A, B (Milnor's sign, I… |
| V11.8 | Non-positive curvature: index $0$, and $\exp_p$ nowhere critical | stronger | failed | failed | incomparable | proved | B: on every abstract connected Hausdorff ℝⁿ-manifold with any smooth Mathlib RiemannianBundle metric and any Levi-Civita connection, under ⟨R(A,B)A,B⟩ ≤ 0: every geodesic [0,1] → M from p to q has ind… |
| V11.9 | The Ricci tensor and Milnor’s Assertion | same | failed | proved | A_narrower | A_to_Bemb_only | B: for every abstract connected Hausdorff ℝⁿ-manifold, any Levi-Civita connection and every p: (a) W ↦ R(U₁,W)U₂ is linear (R = choice function over IsCurvVal), (b) the blind Ricci tensor (trace of th… |
| V12.1 | The algebraic model of a bi-invariant metric | restated | failed | proved | incomparable | not_applicable | A (universe 0) is Morse.isAdInvariant_iff_lieInvariant: for ANY real Lie algebra L and bilinear form B, the project's IsAdInvariant B (⟨[X,Y],Z⟩ = ⟨X,[Y,Z]⟩) ↔ Mathlib's B.lieInvariant; IsAdInvariant … |
| V12.10 | Corollary 21.6, the algebraic step: splitting off the centre | narrower | failed | proved | incomparable | not_applicable | A (universe 0) = mem_centerCompl ∧ isCompl_center_centerCompl ∧ eq_zero_of_mem_centerCompl: for ANY finite-dim real Lie algebra with ad-invariant symmetric positive definite B, centerCompl hB (Mathlib… |
| V12.11 | The operator $K_V$ in the proof of Theorem 21.7 | stronger | failed | proved | incomparable | not_applicable | A (universe 0) = jacobiOp_apply ∧ ad_skew ∧ jacobiOp_symm ∧ jacobiOp_self ∧ jacobiOp_self_nonneg ∧ jacobiOp_eq_zero_iff ∧ eigenvalue_nonneg ∧ ad_eigenvalue_eq_zero: for ANY real Lie algebra with ad-in… |
| V12.12 | The non-zero eigenvalues of $K_V$ occur in pairs | restated | failed | proved | incomparable | not_applicable | A (universe 0) = jacobiOp_of_lie_lie ∧ lie_lie_of_jacobiOp ∧ lie_mem_eigenspace ∧ eigenJ_comp_self ∧ eigenJ_isometry ∧ even_finrank_of_comp_self_eq_neg_id ∧ even_finrank_eigenspace: for ANY finite-dim… |
| V12.13 | Even index from paired eigenvalues | restated | failed | proved | incomparable | not_applicable | A (universe 0) = Morse.even_spectralIndex: for any finite family e : κ → ℝ whose positive values have even multiplicity, spectralIndex e (vocabulary: Σᶠ_t #{i / t ∈ conjParams (e i)}, conjParams = the… |
| V12.14 | Matrix groups and their bi-invariant metric | narrower | failed | failed | incomparable | A_to_Bemb_only | A (universes 0) is the project's Euclidean model of matrix groups: ⟪A,B⟫ = Re tr(AᴴB) on Mₙ(𝕜), its invariance under unitary left/right multiplication, exp of skew-Hermitian is unitary, T_gG = g·𝔤 for… |
| V12.15 | Lemma 21.2: the geodesics are the one-parameter subgroups | narrower | failed | failed | incomparable | A_to_Bemb_only | A (universes 0): for a matrix group G ⊆ U(n) as a slice submanifold of Mₙ(𝕜) with the induced metric: g·exp(tX) are geodesics on ℝ; every geodesic on an open preconnected s is γ(t₀)exp((t−t₀)X); lemma… |
| V12.16 | Lemma 21.1: the reflection $\sigma \mapsto \tau\sigma^{-1}\tau$ | narrower | failed | failed | incomparable | A_to_Bemb_only | A (universes 0): for a matrix group G (slice submanifold of Mₙ(𝕜), induced metric) and τ ∈ G, the ambient linear isometry symmIso τ : A ↦ τAᴴτ (vocabulary) maps G into G, fixes τ, and maps τexp(tX) to… |
| V12.17 | Theorem 21.3 and Corollary 21.4 for matrix groups | narrower | failed | failed | incomparable | A_to_Bemb_only | A (universes 0): the matrix-group version of 21.3/21.4 computed in the embedding G ⊆ Mₙ(𝕜) (induced metric): inner_lie_left (21.3(a) for skew-Hermitian matrices), the Gauss trace identity, P_g = g P_𝔤… |
| V12.18 | Theorem 20.5 for matrix groups: the Jacobi equation along $\exp(tA)$ | narrower | failed | failed | incomparable | failed | A (universes 0): for a matrix group G (slice submanifold of Mₙ(𝕜), induced metric), A ∈ 𝔤, γ(t) = exp(tA), h(t) = exp(tA/2), K_A(U) = ¼[[A,U],A]: D/dt(hUh) = hU'h, R(γ',hMh)γ' = hK_A(M)h, hUh is a Jac… |
| V12.2 | Theorem 21.3 (d): $X \vdash Y = \frac12[X, Y]$ | restated | failed | proved | incomparable | not_applicable | A (universe 0) is Morse.IsLeviCivita.conn_eq: for ANY real Lie algebra L, form B and bilinear D with IsLeviCivita B D, (∀X, D X X = 0) ⇒ D X Y = ½⁅X,Y⁆ — pure algebra; 'X ⊢ X = 0' is a hypothesis. B: … |
| V12.3 | Theorem 21.3 (a): the metric is ad-invariant | restated | failed | proved | incomparable | not_applicable | A (universe 0) is Morse.IsLeviCivita.isAdInvariant: for ANY real Lie algebra L, form B and bilinear D with IsLeviCivita B D and D X X = 0: B ⁅X,Y⁆ Z = B X ⁅Y,Z⁆ — pure algebra. B: on a Lie group with … |
| V12.5 | Theorem 21.3 (b): $R(X, Y)Z = \frac14[[X, Y], Z]$ | restated | failed | proved | incomparable | not_applicable | A (universe 0) is Morse.curv_halfLie: for ANY real Lie algebra L, curv (halfLie L) X Y Z = ¼⁅⁅X,Y⁆,Z⁆ with curv D X Y Z = −D X (D Y Z) + D Y (D X Z) + D ⁅X,Y⁆ Z — the Jacobi-identity computation with … |
| V12.6 | Theorem 21.3 (c) | restated | failed | proved | incomparable | not_applicable | A (universe 0) is Morse.curv_inner: for ANY real Lie algebra L and ad-invariant bilinear B, B (curv (halfLie L) X Y Z) W = ¼ B ⁅X,Y⁆ ⁅Z,W⁆ — pure algebra. B: on a Lie group with a bi-invariant metric … |
| V12.7 | Cartan's 3-form | narrower | failed | proved | incomparable | not_applicable | A (universe 0) is cartan_form_swap₁₂ ∧ cartan_form_swap₂₃: for ANY real Lie algebra L and bilinear B, B ⁅Y,X⁆ Z = −B ⁅X,Y⁆ Z, and for ad-invariant B, B ⁅X,Z⁆ Y = −B ⁅X,Y⁆ Z. B: (A) for a bi-invariant … |
| V12.8 | Corollary 21.4: the sectional curvature | stronger | failed | proved | incomparable | not_applicable | A (universe 0) = Morse.sectional ∧ sectional_nonneg ∧ sectional_eq_zero_iff ∧ sectional_std: for ANY real Lie algebra L and ad-invariant bilinear B (positive definite for the middle two), B (curv (hal… |
| V12.9 | Corollary 21.5, the algebraic step: positive Ricci curvature | narrower | failed | proved | incomparable | not_applicable | A (universe 0) = curv_halfLie_eq_jacobiOp ∧ trace_jacobiOp ∧ trace_eq_sum_of_isOrtho ∧ trace_jacobiOp_pos ∧ killingForm_neg: for ANY finite-dim real Lie algebra with ad-invariant symmetric positive de… |
| V13.1 | The space $\Omega^d$ of minimal geodesics | restated | failed | failed | incomparable | proved | B: on every abstract connected complete Riemannian ℝⁿ-manifold (any smooth metric, any Levi-Civita connection), for all p, q, a path w ∈ Ω (blind Om) lies in Ω^d = E⁻¹[0, ρ(p,q)²] iff w is a minimal g… |
| V13.10 | Lemma 22.4 | stronger | proved | failed | A_stronger | not_applicable | A ⇒ B: Morse.lemma_22_4 at E = ℝⁿ with ε_B = ε_A/(n²+n+1). Dictionary in the file: blind bIndex univ of a continuous bilinear form = Morse.index (finrank_le_index_of_negDef / exists_negDef_finrank_eq_… |
| V13.11 | Lemma 22.4 on a submanifold, for linear perturbations | narrower | failed | failed | incomparable | Bemb_to_A_only | A (universes 0): for a slice submanifold N ⊆ V (any normed V, any finite-dimensional model Z) and F smooth on V, only LINEAR perturbations are controlled: ∃ δ, every critical point in K of (F + a)/N w… |
| V13.13 | Lemma D: passing critical levels of high index | explicit | failed | failed | incomparable | failed | Different conclusions. B (Milnor's sentence): on an abstract smooth manifold with g⁻¹[a,b] compact and all critical points there non-degenerate of index ≥ λ₀, there is a relative CW complex (Y, D) wit… |
| V13.14 | Lemma 22.5 | narrower | failed | failed | incomparable | failed | B: abstract smooth ℝᵐ-manifold M, f ≥ 0 smooth with min 0 attained, all {f ≤ c} compact, M⁰ = f⁻¹(0) a topological manifold, critical points off M⁰ of (blind, possibly degenerate) index ≥ λ₀ ⇒ π_r(M, … |
| V13.15 | Deforming a neighbourhood of the minimal geodesics | explicit | failed | failed | incomparable | failed | B (Milnor p. 121, for any Riemannian metric on M and f with min 0, compact sublevels, M⁰ a topological manifold): ∃ open U ⊇ M⁰ and a retraction r : U → M⁰ such that each x ∈ U is joined to r(x) by a … |
| V13.16 | Theorem 22.1 for an open and closed set of paths | narrower | failed | failed | incomparable | failed | Same situation as Theorem 22.1 (V13_2), relativized to a clopen Ω'. B: abstract connected complete Riemannian ℝⁿ-manifold, any Levi-Civita connection, Ω' clopen in the blind Ω; if (i) Ω' ∩ Ω^d (Ω^d = … |
| V13.2 | Theorem 22.1 | narrower | failed | failed | incomparable | failed | B: on every abstract connected complete Riemannian ℝⁿ-manifold with any Levi-Civita connection, if (i) Ω^d = E⁻¹[0, ρ(p,q)²] (its SeparationQuotient, i.e. paths on [0,1]) is a topological manifold and… |
| V13.3 | The inclusion $\Omega^d \to \Omega$ on homotopy groups | narrower | failed | failed | incomparable | failed | A (universes 0, K : Type) is the project's corollary of Theorem 22.1 for slice submanifolds N ⊆ V (any model Z): if closed ρ-balls about p are compact, every unbroken geodesic p → q NOT OF LEAST ENERG… |
| V13.4 | Corollary 22.2 | narrower | failed | failed | incomparable | failed | A (universes 0; pathCHomeomorph, contractLoop, contractPath are vocabulary): under the project's Theorem 22.1 hypotheses (compact balls, formIndex ≥ λ₀ for geodesics not of least energy, Ω^d = minPath… |
| V13.5 | Corollary 22.2 as groups; change of basepoint is a homomorphism | narrower | failed | failed | incomparable | failed | A (universes 0; evalZeroHomotopyEquiv, changeBaseMulEquiv are vocabulary): (1) change of basepoint along any path is multiplicative (any space, any finite index type); (2) unconditionally, π_{j+1}(Ω(N… |
| V13.6 | Lemma A: the minimal geodesics between antipodes are the equator | restated | failed | failed | incomparable | proved | A (no universe parameters; the defs sphMinPathsHomotopyEquiv / sphMinPathsHomeomorph read as Nonempty of their types; equator, semicircle, minPaths are vocabulary) lives on the project's embedded roun… |
| V13.7 | Lemma B: the index of a geodesic between antipodes | same | failed | failed | incomparable | A_to_Bemb_only | A (no universe parameters) lives on the project's embedded sphere Sph (n+1) with the induced metric: the great circle with L = (2m+1)π from p to -p has formIndex (energyHessian) exactly 2mn, and every… |
| V13.9 | Corollary 22.3 (Freudenthal) | stronger | proved | failed | A_stronger | not_applicable | Same objects: the project's sphere Milnor.Sphere.Sph n = sphG⁻¹{0} is the blind Metric.sphere 0 1 (equal sets via preimage_eq_sphere, not definitionally; rewriting under the binders suffices), and bot… |
| V14.1 | $\exp A = -I$ for diagonal $A$ | narrower | proved | proved | equivalent | not_applicable | A (exp_diagonal_eq_neg_one_iff at universe 0, plus the scalar exp_ofReal_mul_I_eq_neg_one_iff) is exactly B's diagonal claim (ii), for any Fintype index type: exp diag(ia_j) = −I iff each a_j = k_jπ w… |
| V14.10 | Elementary properties of the index formula | same | proved | proved | equivalent | not_applicable | Vocabulary: blind bottFormula k (sum over the filtered ordered pairs of Fin n) = project bottIndex k (double sum with if). A (universes 0, arbitrary finite types): bottIndex ≥ 0 for odd k, invariant u… |
| V14.11 | Lemma 23.2, combinatorially | restated | proved | proved | equivalent | not_applicable | A (ι : Type): Lemma 23.2 for bottIndex (any finite type of cardinality 2m, odd k, Σk = 0, not all ±1 ⇒ ≥ 2m+2), plus two bookkeeping lemmas for ARBITRARY odd k (no Σk = 0): the (positive, negative)-pa… |
| V14.13 | $U(n)$ and $SU(n)$ as compact matrix groups | restated | failed | failed | incomparable | not_applicable | A (universes 0, any RCLike 𝕜 incl. ℝ, any finite ι; SU parts need n ≥ 1): U(n) (and O(n)) is a Milnor.IsSliceSubmanifold as a regular level set of A ↦ AᴴA − I (with the regular-value statement), an Is… |
| V14.14 | The geodesics from $I$ to $-I$ in $SU(n)$ | same | failed | failed | incomparable | A_to_Bemb_only | A (universes 0) lives on the project's embedded SU(n) ⊆ Mₙ(ℂ) (slice submanifold modelled on 𝔰𝔲(n), induced metric; geodesics = IsUnbrokenGeodesic) for any nonempty finite index type: every unbroken g… |
| V14.15 | The distance from $I$ to $-I$, and the minimal geodesics | narrower | failed | proved | A_narrower | not_applicable | A (universes 0) is the SU(2m) half of B on the project's embedded SU(n) ⊆ Mₙ(ℂ) (Frobenius norm): length of exp tA = ‖A‖ (any skew-Hermitian A), ‖T suDiag(k) Tᴴ‖² = π²Σk², π√n ≤ ‖A‖ for exp A = −I in … |
| V14.16 | Lemma 23.1: the velocities of the minimal geodesics form $G_m(\mathbb C^{2m})$ | restated | proved | proved | A_stronger | not_applicable | A (universes 0; minVel = {A ∈ 𝔰𝔲 / A² = −π²I}, grassmannian = Hermitian idempotents of trace m, vocabulary; the def lemma_23_1 read as Nonempty of its type): A² = −π²I ⇒ exp A = −I for skew-Hermitian … |
| V14.17 | Lemma 23.1 in the path space | restated | failed | failed | incomparable | A_to_Bemb_only | A (universes 0; the defs minPathsHomotopyEquiv / minVelHomeomorph read as Nonempty of their types) lives on the project's embedded SU(2m) ⊆ M_{2m}(ℂ) with Ω = PathSp (Milnor's metric d) and Ω^d = minP… |
| V14.18 | Theorem 20.5 for $SU(n)$ | narrower | failed | failed | incomparable | failed | A (universes 0; jacSin/hadSin/suSol/suJac/hadKer vocabulary) lives on the project's embedded SU(n) ⊆ Mₙ(ℂ): for A = T·diag(ia)·Tᴴ it gives the explicit solutions U_C of U'' + K_A U = 0 and Jacobi fiel… |
| V14.19 | The index of a geodesic from $I$ to $-I$ in $SU(n)$ | same | failed | failed | incomparable | A_to_Bemb_only | A (universes 0) lives on the project's embedded SU(n) ⊆ Mₙ(ℂ) (induced metric) with the index = formIndex of the project's energyHessian, computed through the project's Index Theorem theorem_15_1 and … |
| V14.2 | Length and trace of the velocity | restated | proved | proved | incomparable | not_applicable | A (universes 0; suDiag is vocabulary, = blind milnorA): for A = diag(iπk_j), any finite index type and ANY integers k_j, tr AA* = π²Σk_j² and tr A = iπΣk_j — only the diagonal trace computations. B: f… |
| V14.20 | Lemma 23.2 for geodesics | same | failed | failed | incomparable | A_to_Bemb_only | A (universes 0) lives on the project's embedded SU(2m) ⊆ M_{2m}(ℂ) (induced metric) with the index = formIndex of the project's energyHessian: for A ∈ 𝔰𝔲(2m) with exp A = −I there are odd k_j, Σk_j = … |
| V14.22 | Theorem 23.3 (Bott) | restated | failed | proved | A_narrower | Bemb_to_A_only | A (theorem_23_3, theorem_23_3_mulEquiv; universes 0) only asserts, for /ι/ = 2m with ι nonempty and every P ∈ G_m(ℂ^ι) (Hermitian projections of trace m), SOME bijection π_i(G_m, P) ≃ π_{i+1}(SU(ι), I… |
| V14.23 | Coset bundles: local sections, Stiefel manifolds, $U(m + 1) \to S^{2m+1}$ | restated | proved | failed | A_stronger | — | A (universes 0; Stiefel vocabulary, the def stiefelSphere read as Nonempty of its type) is the general machinery: (1) Steenrod's argument for ANY equivariant p : E → B of G-spaces with a local section… |
| V14.24 | The Grassmannian bundle $U(m) \to V_m \to G_m$ | restated | proved | failed | A_stronger | — | A (universes 0; Grassmannian = Hermitian projections of trace m, frameSpan F ↦ FFᴴ, vocabulary): (1) Hermitian projections with PQ = Q and equal traces are equal; (2) every projection of trace m is FF… |
| V14.25 | Lemma 23.4: stability, and the connectivity of Stiefel manifolds | stronger | proved | failed | A_stronger | — | A (universes 0; SphereConnected, unitaryInclC vocabulary): (1) for any RCLike 𝕜 with SphereConnected 𝕜 d, π_i V_k(𝕜ⁿ) = 0 for i + 1 ≤ d(n−k) + d − 1; (2) stability of U(m) → U(m+k) (S ↦ diag(S, I_k), … |
| V14.26 | Lemma 23.4: $\pi_iG_m(\mathbb C^{2m}) \cong \pi_{i-1}U(m)$ | restated | proved | failed | A_stronger | — | A (universes 0; the defs grassmannianEquiv, grassmannianEquiv_complex, grassmannianPiEquiv, minVelPiEquiv read as Nonempty of their types): (1) for ANY RCLike 𝕜 with SphereConnected 𝕜 d and any m', π_… |
| V14.27 | Lemma 23.4: $\pi_jSU(m) \cong \pi_jU(m)$ | narrower | proved | proved | A_stronger | not_applicable | A (universes 0; suInclC vocabulary; the def unitaryProd read as ∃ U(ι) ≃ₜ S¹ × SU(ι) with first component det): for every nonempty finite ι, U(ι) ≅ S¹ × SU(ι) over det, det is locally trivial with fib… |
| V14.28 | The periodicity theorem | restated | proved | proved | equivalent | not_applicable | A (no universes): at base point 1, π_j U(m) ≃ π_{j+2} U(Fin m ⊕ Fin m) for j+1 ≤ 2m and ≃* for degrees ≥ 1 (j+2 ≤ 2m) — the end-to-end composite of Milnor's chain — and periodicity π_{i−1} U(m) ≃ π_{i… |
| V14.29 | Theorem 23.5 (Bott), as sets | restated | proved | proved | equivalent | not_applicable | A (no universes; the def unitaryOneHomeomorph read as ∃ U(1) ≃ₜ S¹ with g ↦ det g): π_1(S¹, 1) ≃ ℤ; U(1) ≃ₜ S¹ by det; π_i(U(m), 1) ≃ π_i(S¹, 1) for i < 2, m ≥ 1; Theorem 23.5 at base point 1 for j+1 … |
| V14.3 | Minimal geodesics, arithmetically | restated | failed | proved | A_narrower | not_applicable | A (universes 0) is only the arithmetic step of Milnor's argument: for odd integers k_j on any finite index type, card ≤ Σk_j², with equality iff every k_j = ±1, and if all k_j = ±1, card = 2m and Σk_j… |
| V14.30 | Theorem 23.5 as groups | restated | proved | proved | A_stronger | not_applicable | A (no universes; the def piOneCircleMulEquiv read as Nonempty of its type): at base point 1, π_1(S¹) ≃* Multiplicative ℤ; π_1 U(m) ≃* π_1 S¹ (m ≥ 1); π_{2k+1} U(m) ≃* Multiplicative ℤ for 2k+2 ≤ 2m; π… |
| V14.4 | Lemma 23.1 as a statement about projections | narrower | failed | proved | incomparable | not_applicable | A (universes 0) is matrix algebra: a skew-Hermitian A (any finite index type) has A² = −π²I iff A = iπ(2P − I) for a Hermitian idempotent P, and tr(iπ(2P − I)) = iπ(2 tr P − n). B is Lemma 23.1 as Mil… |
| V14.5 | The operator $K_A$ for diagonal $A$ | restated | proved | proved | A_stronger | not_applicable | Same computation. A (universes 0; jacobiMat = ¼[[A,W],A] with scalar (1/4 : ℂ), suDiag = diag(iπk_j), both vocabulary and equal to the blind Kop / milnorA): for any finite index type, ANY integers k_j… |
| V14.6 | Milnor's eigenvectors, and that they span | narrower | proved | proved | incomparable | not_applicable | A (universes 0; eReal/eImag/suDiag/jacobiMat are vocabulary, definitionally the blind eReal/eImag/milnorA and Kop up to the scalar ¼ ∈ ℝ vs ℂ): for any finite index type and ANY integers k_j and any j… |
| V14.7 | Conjugate parameters of an eigenvalue: Theorem 20.5 as a definition | restated | proved | proved | equivalent | not_applicable | Vocabulary: the project's Morse.conjParams e = {t ∈ (0,1) / e > 0, t = πs/√e} is the blind conjParams e (all positive parameters t = s·π/√e) intersected with (0,1) (conjParams_inter). A (no universes)… |
| V14.8 | The index of a spectrum: Theorems 20.5 and 15.1 as a definition | restated | proved | proved | equivalent | not_applicable | Vocabulary: blind specMult/specIndex (finsum over t ∈ (0,1) of #{i / t ∈ conjParams(e i)}) equal the project's conjMult/spectralIndex (finsum over all t, with conjParams already restricted to (0,1)) (… |
| V14.9 | The index formula from Milnor's spectrum | restated | proved | proved | equivalent | not_applicable | A (ι : Type): for odd b < a, 2·#conjParams(π²(a−b)²/4) = a − b − 2; for any finite ι and odd k (no Σk = 0 needed), spectralIndex(suSpectrum k) = bottIndex k, where suSpectrum lists π²(k_i − k_j)²/4 tw… |
| V15.1 | Complex structures | stronger | proved | proved | equivalent | not_applicable | Vocabulary: B's IsCplxStr is literally the project's IsComplexStructure (J ∈ O(n) ∧ J² = −1), and B's OmegaK = the project's Omega (anticommutation written in the other order; omegaK_eq_omega). A (uni… |
| V15.10 | Products of anticommuting complex structures | stronger | proved | proved | A_stronger | not_applicable | A (universes 0; Morse.IsClifford is vocabulary): matrix anticommuting families satisfy the Clifford relations, and in an ARBITRARY ring with Clifford relations, the commute/anticommute tables of θ₃, θ… |
| V15.11 | Lemma 24.6, the odd steps (3), (5), (6), (7) | narrower | failed | proved | incomparable | not_applicable | A (universes 0, any n, any k, any 1 ≤ a < b ≤ k) is the algebraic bijection J ↦ θ = J_aJ_bJ from Ω_{k+1}(n) onto the symmetric orthogonal involutions commuting with J_a, J_b and anticommuting with the… |
| V15.12 | Lemma 24.6, the dimensions | stronger | proved | proved | incomparable | not_applicable | A (universes 0; eigV₁/eigW/eigX/jointEigen are vocabulary, shown equal to B's V1/Wsp/Xsp/X1 under toLinAlgEquiv') states only DIMENSIONS: the halving lemma for an abstract finite-dimensional real spac… |
| V15.13 | Minimal spaces and the numbers $m_k$ | restated | failed | proved | A_narrower | not_applicable | The listed declarations (Morse.IsMinimalCliffordModule, Morse.milnorM) are definitions, so A = True and B ⇒ A is trivial (vacuous). A ⇒ B means proving B outright; B is true but its k > 8 part (minima… |
| V15.14 | $m_k$ divides the dimension, and is the least one | stronger | failed | proved | A_narrower | not_applicable | A (universes 0) covers only k <= 8: 2 / dim, 4 / dim, 8 / dim, milnorM k / dim for an ABSTRACT space with anticommuting square roots of -1 (no inner product), milnorM k / n for orthogonal families on … |
| V15.16 | Lemma 24.8: minimal spaces have dimension $m_k$ | narrower | proved | proved | equivalent | not_applicable | A (universes 0): for an ABSTRACT real vector space with anticommuting square roots of -1 (IsClifford, no inner product) and k <= 8: minimal => dim = milnorM k; dim = milnorM k => minimal; minimal => m… |
| V15.17 | Lemma 24.8 (Bott and Shapiro): uniqueness | narrower | failed | proved | A_narrower | not_applicable | A (universes 0; cyclicMap is vocabulary): Lemma 24.8 only for k <= 8, k mod 4 != 3, for ABSTRACT spaces with anticommuting square roots of -1 (no inner product), with a LINEAR isomorphism commuting wi… |
| V15.18 | Vector fields on spheres | narrower | proved | proved | equivalent | not_applicable | Vocabulary: B's IsACFam is the project's IsAnticommFamily (isACFam_iff). A (universes 0, any finite index type, any vector u): <J_a u, J_b u> = delta_ab /u/^2 for an anticommuting family, Ju perp u fo… |
| V15.19 | The index count for $k \not\equiv 2 \pmod 4$, from the spectrum | restated | failed | proved | incomparable | not_applicable | A (universe 0 for the first theorem) is arithmetic on lists of reals: #{i / pi^2 < e_i} <= spectralIndex e, where spectralIndex counts the parameters pi*s/sqrt(e_i) in (0,1) (Theorem 20.5 by definitio… |
| V15.2 | $\exp(\theta J) = \cos\theta\,I + \sin\theta\,J$ | narrower | failed | proved | A_narrower | not_applicable | A (universes 0): for EVERY J with J² = −1 (not necessarily orthogonal, any finite index type) exp(θJ) = cos θ·I + sin θ·J and exp(πJ) = −I. B: (1) the real normal form of a skew A on ℝ^{2m} (orthogona… |
| V15.20 | The index count for $k \equiv 2 \pmod 4$, from the spectrum | sign | proved | proved | incomparable | not_applicable | Both sides are integer arithmetic (vocabulary: B's gapSum = the project's bottIndex, gapSum_eq_bottIndex). A (universes 0, any finite index type): odd a with some /a_i/ >= 3 gives r - /c/ <= 2 bottInd… |
| V15.21 | Totally geodesic sets of orthogonal matrices | restated | proved | proved | A_stronger | not_applicable | A (universes 0) is a generic theory and never mentions Ω_k(n): the slice-submanifold criterion isSliceSubmanifold_of_param (local parametrizations ⇒ slice submanifold, any normed spaces) and, for any … |
| V15.22 | Assertions 1 and 2 in both directions; $\Omega_k(n)$ near a point | explicit | proved | proved | A_stronger | not_applicable | A (universes 0, any finite index type, arbitrary sequence J; tanAlg J k x = Milnor's 𝒯_x = {A skew / Ax = −xA if k ≠ 0, AJ_α = J_αA for α < k}): membership; 𝒯 at k = 0 does not depend on x; Assertions… |
| V15.23 | Lemma 24.4, first half: a smooth, totally geodesic submanifold | restated | proved | proved | A_stronger | not_applicable | A (universes 0, any finite index type, arbitrary sequence J; omegaStratum J k p = points of Ω_k(n) where dim 𝒯 = dim 𝒯_p): dim 𝒯 is constant along x exp(tA); for J_1..J_k anticommuting the stratum is … |
| V15.24 | Lemma 24.1: the length of a geodesic from $I$ to $-I$ | restated | proved | proved | A_stronger | not_applicable | A (universes 0, any finite index type, no normal form): for skew V with exp V = −I every eigenvalue λ of −V² is ≥ π², hence ‖V‖² ≥ π²n (Frobenius; ‖V‖ = length of t ↦ x exp(tV)), with equality only if… |
| V15.25 | The distance from $J_k$ to $-J_k$, and the minimal geodesics | restated | proved | proved | A_stronger | not_applicable | A (universes 0, any p ∈ Ω_k(n), J_1..J_k anticommuting, ASSUMING minVelO J k p = {A ∈ 𝒯_p / A² = −I} non-empty; project's stratum, path space, energy, riemDist): −p ∈ stratum; dist(p, −p) = π√n in the… |
| V15.26 | Lemma 24.1, and Lemma 24.4, second half: minimal geodesics and $\Omega_{k+1}(n)$ | restated | failed | proved | A_narrower | not_applicable | A (universes 0) = the theorems only: A ∈ minVelO J k J_k ↔ J_kA ∈ Ω_{k+1}(n) (J_1..J_k anticommuting); the geodesic J_k exp(πt J_kᴴJ') is the semicircle cos(πt)J_k + sin(πt)J'; omegaPhi J' is that sem… |
| V15.28 | Killing fields are Jacobi fields; a lower bound for the index | restated | failed | failed | A_stronger | not_applicable | A (universes 0; any k ≥ 0, any V ∈ tanAlg, any Killing space 𝒳 ⊆ isoAlg) is in the project's slice-submanifold vocabulary: the Killing field t ↦ Xγ − γX of X ∈ isoAlg is an IsJacobiField of omegaStrat… |
| V15.29 | The splitting into minimal pieces; Lemma 24.8 between two pieces | restated | failed | failed | incomparable | not_applicable | A (universes 0) is abstract operator theory on a finite-dimensional inner product space: splitting into orthogonal minimal invariant pieces for ANY star-signed family, Schur's lemma for self-adjoint c… |
| V15.3 | Lemma 24.2, from Milnor's spectrum | restated | failed | proved | incomparable | not_applicable | A (no universes) is pure arithmetic on integers a_1..a_m: (i) for odd positive a, spectralIndex(oSpectrum a) = bottIndexO a, where oSpectrum a is a list of reals (π²(a_i+a_j)²/4 for i<j, π²(a_i−a_j)²/… |
| V15.30 | Lemma 24.2, and the index of a non-minimal geodesic for $k \not\equiv 2 \pmod 4$ | narrower | failed | failed | incomparable | not_applicable | A (universes 0): algebraic lemmas (IsInterRel.commute_exp; exists_killing_spaces, exists_killing_spaces_omega producing Killing spaces of total dimension r₀s, (s+1)m_{k+1} = n) and the index bound: fo… |
| V15.31 | Theorem 24.5 for each $n$, $k \not\equiv 2 \pmod 4$ | restated | failed | failed | incomparable | not_applicable | A (universes 0, k + 1 ≤ 8, k ≢ 2 mod 4, r₀ = 1 or (2, k = 0), i + 2 ≤ r₀(n/m_{k+1} − 1)): φ_r : Ω_{k+1}(n) → PathSp(omegaStratum J k J_k) (project path space, Milnor's d as pseudo-emetric) is bijectiv… |
| V15.32 | Theorem 24.3 (Bott) | restated | failed | failed | equivalent | not_applicable | A (universe 0, any finite ι, J_1 a complex structure, i + 4 ≤ n): φ_r : Ω_1 → PathSp(O(ι); I, −I) (project path space, J' ↦ cos(πt)I + sin(πt)J') is bijective on π_i at every J', and π_i(Ω_1, J') ≃ π_… |
| V15.34 | The complex determinant of a real matrix | restated | proved | proved | incomparable | not_applicable | Vocabulary: B's cdet i U = det(U_ℂQ + I − Q) with Q = ½(I − √−1·i) is literally the project's cdet = det(U_ℂP₊ + P₋) (Q = P₊, I − Q = P₋; cdet_eq), and B's tr_ℂ A = tr(A_ℂQ) = −√−1·tr(A·i)/2 for tr A … |
| V15.35 | Milnor's $i$ and $f$, and the classes $\Omega^{(c)}$ | restated | proved | proved | incomparable | not_applicable | A (universes 0, any finite index type): IsCentralI for i = J_1 (k = 2) and i = J_1⋯J_5 (k = 6) only; for an ABSTRACT ii with IsCentralI J k ii (any k ≠ 0): /f/ = 1 on Ω_k(n), f(p) = 1, f(p exp tV) = e… |
| V15.37 | The pieces for $k \equiv 2 \pmod 4$ | restated | proved | proved | incomparable | not_applicable | A (universes 0) is operator algebra on an abstract inner product space E (IsOmegaOps, abstract IsIOps for i = iWord): A = c·i on every minimal (A, J, J_α)-invariant subspace (no exp(πA) = −I needed); … |
| V15.38 | The index bound on $\Omega^{(c)}$ | sign | failed | proved | incomparable | not_applicable | A (universes 0): the intertwiner algebra (IsInterRelI.commute_exp; exists_killing_spaces_two: from intertwiners D_i between ONE piece with a₀ and pieces with b_i < a₀, Killing fields in isoAlg at para… |
| V15.39 | Theorem 24.5 for each $n$, $k = 2, 6$ | restated | failed | proved | A_stronger | not_applicable | A (universes 0; IsAnticommFamily J (k+1), i.e. J_1, …, J_{k+1}): for k = 2, 6 (or k ≠ 0, k+1 ≤ 8, k ≢ 3 mod 4 with IsCentralI) φ : Ω_{k+1}(n) → Ω(stratum of J_k; J_k, −J_k) is bijective on π_{j+1} at … |
| V15.4 | The spaces $\Omega_k(n)$ | stronger | proved | proved | equivalent | not_applicable | Vocabulary: B's OmegaK = the project's Omega (anticommutation order flipped; omegaK_eq_omega). A (universes 0, any finite index type, ARBITRARY sequence J, no anticommutation hypothesis): Ω_{k+1} ⊆ Ω_… |
| V15.40 | Theorem 24.5 for each $n$, $k = 2, 6$: path components | narrower | failed | proved | incomparable | not_applicable | A (universe 0; IsAnticommFamily J (k+1), k = 2, 6, and 2 ≤ (n/m_{k+1} − /c/)/4): the finite-stage π_0 correspondence on one class: every path in Ω^{(c)} (project path space of the stratum of J_k) is j… |
| V15.41 | The structures on $\mathbb R^{16r}$, and stabilization | narrower | failed | proved | incomparable | not_applicable | A (no universes; the proof terms isAnticommFamily_bottJ / stab_mem_omega occurring inside the types of omegaPhi_stab and omegaPhi_bottJ_mem_omegaComp replaced by definitionally equal non-item proofs, … |
| V15.42 | Lemma 24.6 (8): $\Omega_8(16r) \cong O(r)$ | restated | failed | proved | incomparable | not_applicable | A (no universes; the def omegaEightHomeomorph read, with omegaEightHomeomorph_basePt, as ∃ h : Ω_8(16r) ≃ₜ O(r) with h J_8 = I — a literal type_of% would drag the def's body, which uses eq_qOf_of_comm… |
| V15.43 | Bott's chain at $n = 16r$ | restated | failed | failed | incomparable | not_applicable | A (no universes): for Milnor's EXPLICIT structures bottJ r, the eight-fold COMPOSITE chain as bijections of SETS at the base points: π_{j+1}Ω_8(16r) ≃ π_{j+9}O(16r) (2j+12 ≤ r), π_iΩ_8(16r) ≃ π_{i+8}O… |
| V15.45 | Theorem 24.7 (Bott), in the stable range | narrower | proved | proved | A_narrower | not_applicable | A (theorem_24_7, no universes): for i ≥ 0, n ≥ i + 2, n' ≥ i + 10, π_i(O(n), I) ≃ π_{i+8}(O(n'), I) as SETS at the base point I. B: the same at all base points (same ranges), GROUP isomorphisms π_{i+1… |
| V15.46 | The periodicity theorem for $U$ in the stable range | restated | proved | proved | A_narrower | not_applicable | A (periodicity_theorem_stable, no universes): for i < 2n and i + 2 < 2n', π_i(U(n), I) ≃ π_{i+2}(U(n'), I) as SETS at the base point I. B (= the first two conjuncts of V14_28's B): the same for every … |
| V15.5 | Lemma 24.4: the reflection preserves $\Omega_k(n)$ | narrower | failed | proved | A_narrower | not_applicable | A (universe 0, arbitrary sequence J, k+1 ≥ 1): P, J' ∈ Ω_{k+1} ⇒ −(PJ'P) ∈ Ω_{k+1}. B: (1) for p, X ∈ Ω_k (any k ≥ 0) Milnor's reflection pX⁻¹p ∈ Ω_k; (2) every component of Ω_k is a symmetric space f… |
| V15.6 | Assertions 1 and 2, the "if" halves | stronger | proved | proved | A_stronger | not_applicable | A (universes 0): Assertion 1 'if' for EVERY skew A (J a complex structure, AJ = −JA ⇒ J exp A a complex structure); Assertion 2 'if' for arbitrary matrices J, J_α, A with J_αJ = −JJ_α and [A, J_α] = 0… |
| V15.7 | From $\Omega_k(n)$ to $\Omega_{k+1}(n)$, algebraically; the Remark | narrower | proved | proved | incomparable | not_applicable | A (universes 0, arbitrary finite index types) is purely algebraic: for J' ∈ Ω_{k+1}, A = -J_kJ' is a complex structure anticommuting with J_k and commuting with J_1…J_{k-1}, and J_kA = J'; the convers… |
| V15.8 | Milnor's imbedding $\Omega_k(n) \to \Omega_k(n + n')$ | narrower | proved | proved | incomparable | not_applicable | A (universes 0, arbitrary finite index types): J_α ⊕ J'_α of two anticommuting families of length k is anticommuting; and for ANY sequences J, J' (no family hypothesis) and any k including k = 0, P ∈ … |
| VA.10 | Theorem A, Case 1, and a possible misprint $(4 - 3t)u$ | sign | proved | proved | A_narrower | not_applicable | A = case1Map_zero ∧ case1Map_one ∧ theoremA_case1 (universes 0), all with every X_n CLOSED; B (blind) uses the CORRECTED last piece h^{n+1}_{(4t−3)u} (so the misprint (4−3t)u is not copied; no not_B) … |
| VA.11 | Theorem A, Case 2: $f_\Sigma$ is a homotopy equivalence | narrower | false | proved | equivalent **B false** | not_applicable | B is false (not_B, #rt_check OK): it asserts that Milnor's G (Gmap, defined strip by strip with n = ⌊τ⌋) is continuous Y_Σ → X_Σ for arbitrary increasing Y_i, but pasting needs the Y_i closed. Counter… |
| VA.12 | Theorem A, by Milnor’s proof | narrower | proved | proved | equivalent | not_applicable | A = type of Morse.theoremA (universes 0,0): Theorem A with the extra hypothesis that the Y_i are closed (needed by Milnor's proof to paste G strip by strip). B = Theorem A as Milnor states it, no clos… |
| VA.15 | Theorem A, exactly as Milnor states it | same | proved | proved | equivalent | not_applicable | A = mapsTo_mappingTelescopeMap ∧ theoremA_general (universes 0,0; mappingTelescopeMap is vocabulary). B = Theorem A as Milnor states it (no closedness), with hypothesis ∃ e : X_i ≃ₕ Y_i whose underlyi… |
| VA.16 | Monotone unions, and the final step of Theorem 17.3 | restated | failed | proved | incomparable | not_applicable | A (universes 0) = nonempty_homotopyEquiv_telescope ∧ isHomotopyEquiv_compareMap ∧ nonempty_homotopyEquiv_mappingTelescope (compareMap is vocabulary): for ANY X = hdl{X_i}, homotopy equivalences X_i → … |
| VA.17 | The Corollary: homotopy direct limits of CW-complexes | narrower | failed | proved | incomparable | not_applicable | A = corollary_appendix (universes 0,0) ∧ corollary_cellComplex (universe 0): for X the homotopy direct limit of {X_n} with X_n ≃ₕ K_n, X ≃ₕ the mapping telescope of a sequence K₀ → K₁ → ⋯ with the giv… |
| VA.18 | Countable cell complexes | narrower | failed | proved | incomparable | not_applicable | A = IsCountableCellComplexType.of_homotopyEquiv (universe 0): the project's notion (X ≃ₕ mapping telescope of a tower of iterated adjunction spaces, cells attached along arbitrary maps; IsRelCellAttac… |
| VA.19 | The topological part of Theorem 17.3 | stronger | failed | proved | incomparable | not_applicable | A (universe 0) = isCountableCellComplexType_of_tower ∧ _of_sublevel ∧ _of_sublevel': for ANY space X with X = hdl{X_n} (resp. sublevels {E ≤ a_n} of a continuous E, a_n ↗ ∞), GIVEN homotopy equivalenc… |
| VA.2 | The telescope and homotopy direct limits | explicit | proved | proved | equivalent | not_applicable | Vacuous round trip: A is the single listed theorem Morse.mem_telescope_iff (property (T1): for monotone A, (x,τ) ∈ X_Σ ↔ ∃ n ≤ τ, x ∈ X_n; universe 0), the rest of the item being definitions; B (tel S… |
| VA.4 | The map of telescopes, and “clearly sufficient” | same | proved | proved | A_stronger | not_applicable | A = telescopeProj_comp_telescopeMap ∧ IsHomotopyEquiv.of_telescopeMap (universes 0). A ⇒ B uses A's second clause after transporting along the identity homeomorphism tel S ≃ₜ telescope S (Homeomorph.s… |
| VA.5 | Truncations of the telescope (T2) | restated | proved | proved | equivalent | not_applicable | A = isClosed_truncation ∧ isHomotopyEquiv_truncIncl ∧ isHomotopyEquiv_truncProj ∧ level_le_of_stripMap (universes 0; level_le_of_stripMap at .{0,0}). B = (a) X_Σ^n = X₀×[0,1] ∪ … ∪ X_{n-1}×[n-1,n] ∪ X… |
| VA.6 | A level function makes a homotopy direct limit (Lemmas 2.1, 2.2) | explicit | proved | proved | equivalent | not_applicable | A = isHomotopyDirectLimit_of_level ∧ isHomotopyDirectLimit_truncation (universes 0): Lemma 2.1 (a level function f ≥ 0, f ≥ i+1 off X_i, makes the increasing sequence a homotopy direct limit) and Lemm… |
| VA.7 | Example 1, and sublevel sets | stronger | proved | proved | equivalent | not_applicable | A = example1 ∧ isHomotopyDirectLimit_sublevel (universes 0). example1 has exactly B's hypotheses (Monotone, interiors cover, ParacompactSpace + T2Space: both sides read Milnor's 'paracompact' with Hau… |
| VA.8 | Example 3 | same | proved | proved | equivalent | not_applicable | A = isClosed_example3Set ∧ iUnion_example3Set ∧ example3 (no universe parameters: the space is unitInterval). The blind Xi i = {x / x = 0 ∨ 1/(i+1) ≤ x} equals Morse.example3Set i (x = 0 in unitInterv… |
| VA.9 | Milnor’s maps $h_1$ and their homotopy inverse $g$ | explicit | false | proved | incomparable **B false** | not_applicable | A = reparam_homotopic ∧ isHomotopyEquiv_of_milnorMap (universes 0), both for CLOSED X_n. B, faithful to Milnor, assumes only S increasing and asks for a CONTINUOUS g given by Milnor's formulas (g(x,n+… |

