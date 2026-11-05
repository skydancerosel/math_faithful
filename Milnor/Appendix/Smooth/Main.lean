import Milnor.Appendix.Smooth.NonCompact
import Milnor.Appendix.HalfSpace

/-!
# Milnor's Appendix, smooth version: the classification theorem

Milnor, *Topology from the Differentiable Viewpoint*, Appendix (book p. 54): *every smooth connected
one-manifold is diffeomorphic either to the circle or to some interval of real numbers.*  This file
is **Stage 9**, the last, of the plan `Exposition/PlanOneManifold.md`: it assembles the four cases
proved in Stages 6, 7 and 8 into the theorem, in the two forms fixed by §6 of that plan.

## The abstract form

`nonempty_diffeomorph_cases` and `nonempty_diffeomorph_or`: a **connected, Hausdorff, σ-compact,
nonempty `C^∞` one-manifold** `M` -- charted on a model with corners `I : ModelWithCorners ℝ E H`
over a real normed space `E` with `Module.finrank ℝ E = 1` -- is `C^∞`-diffeomorphic to exactly one
of

| | boundary empty | boundary nonempty |
| --- | --- | --- |
| compact | `Circle` (Stage 7) | `Icc (0 : ℝ) 1` (Stage 6) |
| not compact | `ℝ` (Stage 8) | `Ici (0 : ℝ)` (Stage 8) |

each model carrying its own model with corners: `𝓡 1` on the circle, `𝓡∂ 1` on the two half-line
type intervals, `𝓘(ℝ, ℝ)` on the line.  The boundary is Mathlib's `I.boundary M`; no compatibility
hypothesis is assumed, Stage 0 having proved chart-independence.

**Exclusivity** is stated separately, as `models_pairwise_not_diffeomorph` and its six constituent
lemmas, because it is a statement about the four models alone.  Two invariants separate them:

* *compactness* separates `{Circle, Icc 0 1}` from `{Ici 0, ℝ}` -- four of the six exclusions.  A
  `Diffeomorph` is in particular a homeomorphism, so `Homeomorph.compactSpace` transports
  `CompactSpace`; `Circle` and `Icc (0 : ℝ) 1` are compact, while `not_compactSpace_Ici` and
  `not_compactSpace_real` say the other two are not (`Ici 0` is not bounded above).
* *the number of boundary points* separates within each pair -- the remaining two exclusions.
  `Diffeomorph.image_boundary` says a diffeomorphism carries `I.boundary M` onto `I'.boundary N`, so
  `ncard_boundary_eq_of_diffeomorph` makes `(I.boundary M).ncard` a diffeomorphism invariant.  Its
  values on the four models are `0`, `2`, `1`, `0`: `Circle` and `ℝ` are boundaryless because their
  models are; `boundary_Icc` is Mathlib's; `boundary_Ici` is proved here.

## The slice form

`Milnor.IsHalfSliceSubmanifold.component_diffeomorph` and its companions: for a **compact half-slice
submanifold `X` of an ambient manifold, with boundary `B`, modelled on the half-space over a `Z`
with one point** -- a compact one-manifold with boundary in the sense of `Milnor/Chapter2/`
`Boundary.lean` -- every connected component of `X` is diffeomorphic to `Circle` or to
`Icc (0 : ℝ) 1`; the components carrying a boundary point are exactly those of the second kind; each
of those meets `B` in exactly two points; and `B` is finite of even cardinality.

The last conclusion is the existing `Milnor.IsHalfSliceSubmanifold.even_ncard_boundary`, which is
left untouched in `Milnor/Appendix/HalfSpace.lean` and is *not* cited here: the point of Stage 9 is
that it now **follows from the classification**, the pairing being realised by the two ends of a
single arc-length parametrization of a component rather than by an abstract parity argument.  What is
reused from the topological file is only the bookkeeping lemma
`Milnor.OneManifold.even_ncard_of_involution` (a fixed-point-free involution of a finite set has
even cardinality), which is pure combinatorics.

## What had to be built

Three bridges, each of which the rest of the project will want:

1. **Connected components of a one-manifold are open** (`isOpen_connectedComponent_of_oneManifold`),
   hence are manifolds in their own right (`componentOpens`, an element of
   `TopologicalSpace.Opens M`, with Mathlib's charted-space and `IsManifold` instances for open
   subsets).  This is what lets the classification -- which needs connectedness -- be applied to a
   *disconnected* manifold.  It needs nothing but `Module.finrank ℝ E = 1` and `IsManifold I ∞ M`:
   Stage 1's `exists_smoothArc_of_mem_boundary` and `exists_smoothArc_of_notMem_boundary` give every
   point an open neighbourhood which is the source of an arc, and the source of an arc is
   preconnected.  No compactness, no Hausdorffness, no length element.
2. **The boundary of the model half-line** (`boundary_Ici`): `(𝓡∂ 1).boundary (Ici (0 : ℝ)) = {0}`
   for the one-chart structure Stage 8 put on `Ici (0 : ℝ)`.  Mathlib computes the boundary of
   `Icc x y` but not of a half-line, there being no half-line manifold instance in Mathlib.
3. **The boundary count for a possibly disconnected compact one-manifold**
   (`finite_boundary_of_compact`, `even_ncard_boundary_of_compact`), from which the slice form is
   pure transport.

No bridge between the project's half-slice charts and `I.boundary` had to be built: Chapter 2
already proves it, as `Milnor.IsHalfSliceSubmanifold.boundary_eq`.  Nor did the ambient/intrinsic
translation: `Milnor.IsHalfSliceSubmanifold.chartedSpace` and `.isManifold` present `X` as a
manifold over `Milnor.halfSpaceModel Z`, and `finrank_prod_eq_one` says that model is
one-dimensional when `Z` is a subsingleton.  The transport of the counting statement follows
`Milnor/Appendix/HalfSpace.lean` line for line: pass to `X` as a manifold, apply the abstract
theorem, and push the boundary set forward along the injection `Subtype.val : X → M`.

## σ-compactness is necessary

**The classification is false without a countability hypothesis.**  The long line -- two copies of
the closed long ray `ω₁ × [0, 1)`, with the lexicographic order topology, glued along their least
elements -- is a connected Hausdorff smooth one-manifold without boundary which is neither compact
nor σ-compact, and it is diffeomorphic to none of the four models: it is not second countable,
whereas all four models are.
So the two non-compact cases (Stage 8) must assume σ-compactness, and they do.  In the *compact*
cases (Stages 6 and 7) nothing extra is needed: compact plus Hausdorff plus a finite-dimensional
model gives second countability by Mathlib's own
`ChartedSpace.secondCountable_of_sigmaCompact`.  Milnor's manifolds sit in `ℝ^k` and are second
countable for free, and his proof uses this silently -- the Euclidean metric he restricts to `M` is a
Riemannian metric, and a manifold admitting one is metrizable.  See
`Exposition/PlanOneManifold.md` §7.1.

## References

* Milnor, *Topology from the Differentiable Viewpoint*, Appendix, p. 54.
* `Exposition/PlanOneManifold.md`, Stage 9 and §6.
* Stage 6 `Milnor/Appendix/Smooth/Compact.lean`, Stage 7 `Milnor/Appendix/Smooth/Circle.lean`,
  Stage 8 `Milnor/Appendix/Smooth/NonCompact.lean`.
-/

open Set Filter Topology

open scoped ContDiff Manifold

noncomputable section

namespace Milnor

namespace OneManifold.Smooth

/-! ## The four models: compactness -/

section Models

/-- **The closed half-line is not compact**: a compact subset of `ℝ` is bounded above, and `Ici 0`
is not.  Together with `not_compactSpace_real` this is what separates the two non-compact models
from the two compact ones. -/
theorem not_compactSpace_Ici : ¬ CompactSpace (Ici (0 : ℝ)) := fun h =>
  not_bddAbove_Ici (a := (0 : ℝ)) (isCompact_iff_compactSpace.2 h).bddAbove

/-- **The line is not compact.**  Mathlib's `NoncompactSpace ℝ`, read as the negation of
`CompactSpace ℝ`. -/
theorem not_compactSpace_real : ¬ CompactSpace ℝ := fun h =>
  NoncompactSpace.noncompact_univ (X := ℝ) h.isCompact_univ

/-- **The circle has no boundary**, its model `𝓡 1` being boundaryless. -/
theorem boundary_circle_eq_empty : (𝓡 1).boundary Circle = ∅ :=
  ModelWithCorners.Boundaryless.boundary_eq_empty

/-- **The line has no boundary**, its model `𝓘(ℝ, ℝ)` being boundaryless. -/
theorem boundary_real_eq_empty : 𝓘(ℝ, ℝ).boundary ℝ = ∅ :=
  ModelWithCorners.Boundaryless.boundary_eq_empty

/-- The circle has `0` boundary points. -/
theorem ncard_boundary_circle : ((𝓡 1).boundary Circle).ncard = 0 := by
  rw [boundary_circle_eq_empty, Set.ncard_empty]

/-- The line has `0` boundary points. -/
theorem ncard_boundary_real : (𝓘(ℝ, ℝ).boundary ℝ).ncard = 0 := by
  rw [boundary_real_eq_empty, Set.ncard_empty]

/-- **The unit interval has `2` boundary points**, namely its two endpoints.  This is Mathlib's
`boundary_Icc`, counted. -/
theorem ncard_boundary_Icc : ((𝓡∂ 1).boundary (Icc (0 : ℝ) 1)).ncard = 2 := by
  rw [boundary_Icc]
  refine Set.ncard_pair ?_
  intro h
  have h' := congrArg Subtype.val h
  norm_num at h'

/-- **The boundary of the closed half-line is its endpoint.**  For the one-chart manifold structure
Stage 8 puts on `Ici (0 : ℝ)` (`Milnor.OneManifold.Smooth.instIciChartedSpace`, the single chart
being `iciHomeomorph` onto the whole model half-space), the extended chart at `u` sends `u` to the
one-entry vector with entry `(u : ℝ)`, and `Mathlib`'s
`frontier_range_modelWithCornersEuclideanHalfSpace` says the frontier of the model range is the set
where that entry vanishes.  So `u` is a boundary point exactly when `(u : ℝ) = 0`.

Mathlib computes the boundary of `Icc x y` (`boundary_Icc`) but has no half-line manifold, so this
had to be proved here. -/
theorem boundary_Ici : (𝓡∂ 1).boundary (Ici (0 : ℝ)) = {⟨0, le_refl (0 : ℝ)⟩} := by
  ext u
  have hchart : extChartAt (𝓡∂ 1) u u = ((iciHomeomorph u).val : EuclideanSpace ℝ (Fin 1)) := rfl
  show (𝓡∂ 1).IsBoundaryPoint u ↔ _
  rw [ModelWithCorners.isBoundaryPoint_iff, frontier_range_modelWithCornersEuclideanHalfSpace,
    hchart]
  rw [Set.mem_singleton_iff, Subtype.ext_iff]
  show (0 : ℝ) = ((iciHomeomorph u).val : EuclideanSpace ℝ (Fin 1)) 0 ↔ (u : ℝ) = (0 : ℝ)
  simp only [iciHomeomorph, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk]
  constructor
  · intro h; simpa using h.symm
  · intro h; simpa using h.symm

/-- **The closed half-line has `1` boundary point.**  This is the invariant that separates it from
the line, the remaining exclusion among the two non-compact models. -/
theorem ncard_boundary_Ici : ((𝓡∂ 1).boundary (Ici (0 : ℝ))).ncard = 1 := by
  rw [boundary_Ici, Set.ncard_singleton]

end Models

/-! ## Two invariants of a diffeomorphism -/

section Invariants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- **Compactness is a diffeomorphism invariant**, being a homeomorphism invariant. -/
theorem compactSpace_of_diffeomorph [CompactSpace M] (Φ : Diffeomorph I I' M N ∞) :
    CompactSpace N :=
  Φ.toHomeomorph.compactSpace

/-- **The number of boundary points is a diffeomorphism invariant.**  `Diffeomorph.image_boundary`
says a `C^n` diffeomorphism with `n ≠ 0` maps `I.boundary M` bijectively onto `I'.boundary N`, and
the cardinality of a set is unchanged by an injective image. -/
theorem ncard_boundary_eq_of_diffeomorph [IsManifold I ∞ M] [IsManifold I' ∞ N]
    (Φ : Diffeomorph I I' M N ∞) : (I.boundary M).ncard = (I'.boundary N).ncard := by
  have h : Φ '' I.boundary M = I'.boundary N := Φ.image_boundary (by simp)
  rw [← h]
  exact (Set.ncard_image_of_injective _ Φ.injective).symm

/-- **Non-diffeomorphy is symmetric**: if there is no diffeomorphism `M → N` there is none
`N → M`, by `Diffeomorph.symm`.  Each of the six exclusions below is therefore stated in one
direction only. -/
theorem isEmpty_diffeomorph_comm (h : IsEmpty (Diffeomorph I I' M N ∞)) :
    IsEmpty (Diffeomorph I' I N M ∞) :=
  ⟨fun Φ => h.elim Φ.symm⟩

end Invariants

/-! ## Exclusivity: the four models are pairwise non-diffeomorphic -/

section Exclusivity

/-- **The circle is not diffeomorphic to the unit interval.**  Both are compact, so compactness does
not separate them; the circle has `0` boundary points and the interval has `2`. -/
theorem isEmpty_diffeomorph_circle_Icc :
    IsEmpty (Diffeomorph (𝓡 1) (𝓡∂ 1) Circle (Icc (0 : ℝ) 1) ∞) := by
  refine ⟨fun Φ => ?_⟩
  have h := ncard_boundary_eq_of_diffeomorph Φ
  rw [ncard_boundary_circle, ncard_boundary_Icc] at h
  exact absurd h (by norm_num)

/-- **The circle is not diffeomorphic to the closed half-line**: the circle is compact and the
half-line is not. -/
theorem isEmpty_diffeomorph_circle_Ici :
    IsEmpty (Diffeomorph (𝓡 1) (𝓡∂ 1) Circle (Ici (0 : ℝ)) ∞) :=
  ⟨fun Φ => not_compactSpace_Ici (compactSpace_of_diffeomorph Φ)⟩

/-- **The circle is not diffeomorphic to the line**: the circle is compact and the line is not. -/
theorem isEmpty_diffeomorph_circle_real :
    IsEmpty (Diffeomorph (𝓡 1) 𝓘(ℝ, ℝ) Circle ℝ ∞) :=
  ⟨fun Φ => not_compactSpace_real (compactSpace_of_diffeomorph Φ)⟩

/-- **The unit interval is not diffeomorphic to the closed half-line**: the interval is compact and
the half-line is not. -/
theorem isEmpty_diffeomorph_Icc_Ici :
    IsEmpty (Diffeomorph (𝓡∂ 1) (𝓡∂ 1) (Icc (0 : ℝ) 1) (Ici (0 : ℝ)) ∞) :=
  ⟨fun Φ => not_compactSpace_Ici (compactSpace_of_diffeomorph Φ)⟩

/-- **The unit interval is not diffeomorphic to the line**: the interval is compact and the line is
not. -/
theorem isEmpty_diffeomorph_Icc_real :
    IsEmpty (Diffeomorph (𝓡∂ 1) 𝓘(ℝ, ℝ) (Icc (0 : ℝ) 1) ℝ ∞) :=
  ⟨fun Φ => not_compactSpace_real (compactSpace_of_diffeomorph Φ)⟩

/-- **The closed half-line is not diffeomorphic to the line.**  Neither is compact, so compactness
does not separate them; the half-line has `1` boundary point (`boundary_Ici`) and the line has
`0`. -/
theorem isEmpty_diffeomorph_Ici_real :
    IsEmpty (Diffeomorph (𝓡∂ 1) 𝓘(ℝ, ℝ) (Ici (0 : ℝ)) ℝ ∞) := by
  refine ⟨fun Φ => ?_⟩
  have h := ncard_boundary_eq_of_diffeomorph Φ
  rw [ncard_boundary_Ici, ncard_boundary_real] at h
  exact absurd h (by norm_num)

/-- **The exclusivity half of Milnor's Appendix theorem: no two of the four models `Circle`,
`Icc (0 : ℝ) 1`, `Ici (0 : ℝ)` and `ℝ` are diffeomorphic.**

All six unordered pairs are listed; the reversed direction of each follows from
`isEmpty_diffeomorph_comm`.  Four of the six are settled by compactness (`Circle` and
`Icc (0 : ℝ) 1` are compact, `Ici (0 : ℝ)` and `ℝ` are not) and the remaining two, one inside each
compactness class, by the number of boundary points (`0`, `2`, `1`, `0` respectively).

Together with `nonempty_diffeomorph_or` this is the "**exactly** one of the four" of the book's
statement. -/
theorem models_pairwise_not_diffeomorph :
    IsEmpty (Diffeomorph (𝓡 1) (𝓡∂ 1) Circle (Icc (0 : ℝ) 1) ∞) ∧
      IsEmpty (Diffeomorph (𝓡 1) (𝓡∂ 1) Circle (Ici (0 : ℝ)) ∞) ∧
      IsEmpty (Diffeomorph (𝓡 1) 𝓘(ℝ, ℝ) Circle ℝ ∞) ∧
      IsEmpty (Diffeomorph (𝓡∂ 1) (𝓡∂ 1) (Icc (0 : ℝ) 1) (Ici (0 : ℝ)) ∞) ∧
      IsEmpty (Diffeomorph (𝓡∂ 1) 𝓘(ℝ, ℝ) (Icc (0 : ℝ) 1) ℝ ∞) ∧
      IsEmpty (Diffeomorph (𝓡∂ 1) 𝓘(ℝ, ℝ) (Ici (0 : ℝ)) ℝ ∞) :=
  ⟨isEmpty_diffeomorph_circle_Icc, isEmpty_diffeomorph_circle_Ici,
    isEmpty_diffeomorph_circle_real, isEmpty_diffeomorph_Icc_Ici, isEmpty_diffeomorph_Icc_real,
    isEmpty_diffeomorph_Ici_real⟩

end Exclusivity

/-! ## The abstract classification -/

section Classification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [IsManifold I ∞ M]

include hE

/-- **Milnor's Appendix theorem (book p. 54), the existence part with the case distinction.**

Let `E` be a real normed space with `Module.finrank ℝ E = 1`, let `I : ModelWithCorners ℝ E H`, and
let `M` be a connected (hence nonempty), Hausdorff, σ-compact `C^∞` manifold charted on `H`.  Then
`M` is `C^∞`-diffeomorphic to

* `Circle` (with `𝓡 1`) if `M` is compact and `I.boundary M = ∅` -- Stage 7;
* `Icc (0 : ℝ) 1` (with `𝓡∂ 1`) if `M` is compact and `I.boundary M ≠ ∅` -- Stage 6;
* `Ici (0 : ℝ)` (with `𝓡∂ 1`) if `M` is not compact and `I.boundary M ≠ ∅` -- Stage 8;
* `ℝ` (with `𝓘(ℝ, ℝ)`) if `M` is not compact and `I.boundary M = ∅` -- Stage 8.

The four clauses are stated as implications rather than as instance hypotheses so that a single
theorem can carry the whole case distinction; `models_pairwise_not_diffeomorph` says the four
conclusions are mutually exclusive, so exactly one clause applies.

σ-compactness is used only in the two non-compact clauses, where it is *necessary* -- see the
module docstring on the long line.  In the two compact clauses it is implied by `CompactSpace M`. -/
theorem nonempty_diffeomorph_cases :
    (CompactSpace M → I.boundary M = ∅ → Nonempty (Diffeomorph I (𝓡 1) M Circle ∞)) ∧
      (CompactSpace M → (I.boundary M).Nonempty →
        Nonempty (Diffeomorph I (𝓡∂ 1) M (Icc (0 : ℝ) 1) ∞)) ∧
      (¬ CompactSpace M → (I.boundary M).Nonempty →
        Nonempty (Diffeomorph I (𝓡∂ 1) M (Ici (0 : ℝ)) ∞)) ∧
      (¬ CompactSpace M → I.boundary M = ∅ → Nonempty (Diffeomorph I 𝓘(ℝ, ℝ) M ℝ ∞)) := by
  refine ⟨fun hc hb => ?_, fun hc hb => ?_, fun hc hb => ?_, fun hc hb => ?_⟩
  · have := hc
    exact nonempty_diffeomorphCircle I hE hb
  · have := hc
    obtain ⟨p, hp⟩ := hb
    exact nonempty_diffeomorphIcc I hE hp
  · obtain ⟨p, hp⟩ := hb
    exact nonempty_diffeomorphIci' I hE hp hc
  · exact nonempty_diffeomorphReal' I hE hb hc

/-- **Milnor's Appendix theorem (book p. 54): a connected, Hausdorff, σ-compact, nonempty `C^∞`
one-manifold is diffeomorphic to one of `Circle`, `Icc (0 : ℝ) 1`, `Ici (0 : ℝ)` and `ℝ`.**

The four-fold disjunction, obtained from `nonempty_diffeomorph_cases` by splitting on whether `M` is
compact and whether its boundary is empty.  By `models_pairwise_not_diffeomorph` the four
alternatives are mutually exclusive, so "one of" is "exactly one of", which is Milnor's own
formulation.

Hypotheses in full: `E` a real normed space with `Module.finrank ℝ E = 1`;
`I : ModelWithCorners ℝ E H`; `M` a topological space charted on `H`, Hausdorff (`T2Space M`),
σ-compact (`SigmaCompactSpace M`), connected (`ConnectedSpace M`, which also supplies nonemptiness)
and a `C^∞` manifold (`IsManifold I ∞ M`).  Nothing is assumed about the boundary, about
orientability, or about second countability. -/
theorem nonempty_diffeomorph_or :
    Nonempty (Diffeomorph I (𝓡 1) M Circle ∞) ∨
      Nonempty (Diffeomorph I (𝓡∂ 1) M (Icc (0 : ℝ) 1) ∞) ∨
      Nonempty (Diffeomorph I (𝓡∂ 1) M (Ici (0 : ℝ)) ∞) ∨
      Nonempty (Diffeomorph I 𝓘(ℝ, ℝ) M ℝ ∞) := by
  obtain ⟨h1, h2, h3, h4⟩ := nonempty_diffeomorph_cases (M := M) I hE
  by_cases hc : CompactSpace M
  · rcases eq_empty_or_nonempty (I.boundary M) with hb | hb
    · exact Or.inl (h1 hc hb)
    · exact Or.inr (Or.inl (h2 hc hb))
  · rcases eq_empty_or_nonempty (I.boundary M) with hb | hb
    · exact Or.inr (Or.inr (Or.inr (h4 hc hb)))
    · exact Or.inr (Or.inr (Or.inl (h3 hc hb)))

end Classification

/-! ## Connected components of a one-manifold -/

section Components

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

include I hE

/-- **Connected components of a smooth one-manifold are open.**

Every point `y` of `M` lies in the source of a smooth arc -- Stage 1's
`exists_smoothArc_of_mem_boundary` at a boundary point and `exists_smoothArc_of_notMem_boundary`
elsewhere -- and the source of an arc is open (`Arc.open_source`) and preconnected
(`Arc.isPreconnected_source`, because it is the continuous image of an order-connected set of
reals).  So every point of `connectedComponent x` has an open neighbourhood inside
`connectedComponent x`.

Hypotheses: `Module.finrank ℝ E = 1` and `IsManifold I ∞ M`.  **No Hausdorffness, no compactness, no
σ-compactness, no length element** -- which is why this can be used to cut a disconnected manifold
into pieces before any of the classification hypotheses are in play. -/
theorem isOpen_connectedComponent_of_oneManifold (x : M) : IsOpen (connectedComponent x) := by
  refine isOpen_iff_forall_mem_open.2 fun y hy => ?_
  have hsub : ∀ A : SmoothArc I ∞ M, y ∈ A.source →
      ∃ U ⊆ connectedComponent x, IsOpen U ∧ y ∈ U := fun A hyA =>
    ⟨A.source, (A.toArc.isPreconnected_source.subset_connectedComponent hyA).trans
      (by rw [connectedComponent_eq hy]), A.toArc.open_source, hyA⟩
  by_cases hyb : y ∈ I.boundary M
  · obtain ⟨A, -, -, hyA, -, -⟩ :=
      exists_smoothArc_of_mem_boundary (n := ∞) I hE (by simp) hyb
    exact hsub A hyA
  · obtain ⟨A, -, -, hyA, -, -, -, -⟩ :=
      exists_smoothArc_of_notMem_boundary (n := ∞) I hE (by simp) hyb
    exact hsub A hyA

/-- **The connected component of a point of a smooth one-manifold, as an open subset.**  Because
`isOpen_connectedComponent_of_oneManifold` makes it open, it inherits from `Mathlib` both a
charted-space structure (`TopologicalSpace.Opens.instChartedSpace`) and a `C^∞` manifold structure
over the *same* model `I`, so the classification can be applied to it.  Its carrier is
`connectedComponent x` on the nose. -/
def componentOpens (x : M) : TopologicalSpace.Opens M :=
  ⟨connectedComponent x, isOpen_connectedComponent_of_oneManifold I hE x⟩

/-- The carrier of `componentOpens I hE x` is the connected component of `x`. -/
@[simp] theorem coe_componentOpens (x : M) :
    ((componentOpens I hE x : TopologicalSpace.Opens M) : Set M) = connectedComponent x := rfl

/-- **The boundary of a component is the boundary of the manifold, restricted.**  This is Mathlib's
`ModelWithCorners.boundary_open` for open subsets; combined with `coe_componentOpens` it says that a
point of `connectedComponent x` is a boundary point of the component exactly when it is a boundary
point of `M`. -/
theorem boundary_componentOpens (x : M) :
    I.boundary (componentOpens I hE x) = Subtype.val ⁻¹' I.boundary M :=
  ModelWithCorners.boundary_open

end Components

/-! ## The compact case, component by component -/

section CompactComponents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [CompactSpace M] [IsManifold I ∞ M]

include I hE

/-- **The two ends of a component: a boundary point of a compact smooth one-manifold has exactly one
partner in its own component.**

For a compact Hausdorff `C^∞` one-manifold -- **not assumed connected** -- and a boundary point `p`,
there is a boundary point `q ≠ p` with `I.boundary M ∩ connectedComponent p = {p, q}`.  This is
Stage 6's `exists_unitSpeedArc_component` read off: the exhausting unit-speed arc from `p` has
source the whole component of `p` and target `Icc 0 ℓ`, and `q` is the far end `A.invFun ℓ`, which
is different from `p` because the arc's coordinate takes the value `0` at `p` and `ℓ > 0` at `q`.

This is the pairing that makes the boundary count even, and it is *geometric*: the two elements of
the pair are the two ends of one arc-length parametrization. -/
theorem boundary_inter_component_eq_pair {p : M} (hp : p ∈ I.boundary M) :
    ∃ q, q ∈ I.boundary M ∧ q ≠ p ∧ I.boundary M ∩ connectedComponent p = {p, q} := by
  obtain ⟨L⟩ := nonempty_lengthElement I hE M
  obtain ⟨A, ℓ, hℓ, -, -, hp0, htgt, -, hbdry⟩ := exists_unitSpeedArc_component I hE L hp
  refine ⟨A.invFun ℓ, ?_, ?_, hbdry⟩
  · have hmem : A.invFun ℓ ∈ I.boundary M ∩ connectedComponent p := by rw [hbdry]; simp
    exact hmem.1
  · intro h
    have hℓt : ℓ ∈ A.target := by rw [htgt]; exact ⟨hℓ.le, le_rfl⟩
    have hv := congrArg A.toFun h
    rw [A.right_inv hℓt, hp0] at hv
    exact hℓ.ne' hv

/-- **A component of a compact smooth one-manifold which meets the boundary meets it in exactly two
points.**  The numerical form of `boundary_inter_component_eq_pair`; no connectedness of `M` is
assumed. -/
theorem ncard_boundary_inter_component {p : M} (hp : p ∈ I.boundary M) :
    (I.boundary M ∩ connectedComponent p).ncard = 2 := by
  obtain ⟨q, -, hqp, heq⟩ := boundary_inter_component_eq_pair I hE hp
  rw [heq]
  exact Set.ncard_pair (Ne.symm hqp)

/-- **The boundary of a compact Hausdorff smooth one-manifold is finite**, with no connectedness
assumed.

Proof from the classification, not from the topological Appendix: the boundary is closed
(`ModelWithCorners.isClosed_boundary`, valid for `C^1` manifolds) hence compact; its points are
covered by the components through them, which are open by
`isOpen_connectedComponent_of_oneManifold`; a finite subcover leaves finitely many components, and
each meets the boundary in a two-element set by `boundary_inter_component_eq_pair`. -/
theorem finite_boundary_of_compact : (I.boundary M).Finite := by
  have hcl : IsClosed (I.boundary M) :=
    ModelWithCorners.isClosed_boundary (I := I) (n := (∞ : WithTop ℕ∞)) (by simp)
  obtain ⟨s, hs⟩ := hcl.isCompact.elim_finite_subcover
    (fun p : I.boundary M => connectedComponent (p : M))
    (fun p => isOpen_connectedComponent_of_oneManifold I hE _)
    (fun p hp => mem_iUnion.2 ⟨⟨p, hp⟩, mem_connectedComponent⟩)
  have hfin : (⋃ p ∈ s, (I.boundary M ∩ connectedComponent (p : M))).Finite := by
    refine Set.Finite.biUnion s.finite_toSet fun p _ => ?_
    obtain ⟨q, -, -, heq⟩ := boundary_inter_component_eq_pair I hE p.2
    rw [heq]
    exact (Set.finite_singleton q).insert (p : M)
  refine hfin.subset fun x hx => ?_
  obtain ⟨p, hps, hxp⟩ := mem_iUnion₂.1 (hs hx)
  exact mem_iUnion₂.2 ⟨p, hps, ⟨hx, hxp⟩⟩

/-- **The boundary of a compact Hausdorff smooth one-manifold has an even number of points**, with
no connectedness assumed.  This is Milnor's corollary of the Appendix, the statement the book
actually uses (through `Milnor/Chapter2/Brouwer.lean` and `Milnor/Chapter4/Homotopy.lean`), now
**derived from the classification**.

The pairing is `boundary_inter_component_eq_pair`: each boundary point is matched with the other end
of its own component.  That matching is an involution of `I.boundary M` without fixed points -- the
partner of the partner of `p` lies in `{p, partner p}` and is not `partner p` -- so the existing
combinatorial lemma `Milnor.OneManifold.even_ncard_of_involution` finishes.  Nothing else is taken
from the topological Appendix: in particular `Milnor.OneManifold.even_ncard_boundary` is *not* used,
and neither is its hypothesis `BoundaryCompatible`. -/
theorem even_ncard_boundary_of_compact : Even (I.boundary M).ncard := by
  classical
  rcases (I.boundary M).eq_empty_or_nonempty with hBe | ⟨p₀, -⟩
  · rw [hBe]; simp
  have : Nonempty M := ⟨p₀⟩
  have hpart := fun p (hp : p ∈ I.boundary M) => boundary_inter_component_eq_pair I hE hp
  choose! ι hιB hιne hιeq using hpart
  refine even_ncard_of_involution (finite_boundary_of_compact I hE) ι hιB ?_ hιne
  intro p hp
  have hq := hιB p hp
  have hK : connectedComponent (ι p) = connectedComponent p := by
    have hmem : ι p ∈ I.boundary M ∩ connectedComponent p := by rw [hιeq p hp]; simp
    exact (connectedComponent_eq hmem.2).symm
  have h1 := hιeq (ι p) hq
  rw [hK, hιeq p hp] at h1
  have h2 : ι (ι p) ∈ ({p, ι p} : Set M) := by rw [h1]; simp
  rcases h2 with h | h
  · exact h
  · rw [Set.mem_singleton_iff] at h
    exact absurd h (hιne (ι p) hq)

/-- **Milnor's Appendix for a possibly disconnected compact one-manifold: every connected component
is diffeomorphic to the circle or to `Icc (0 : ℝ) 1`.**

`M` is a compact Hausdorff `C^∞` one-manifold, *not* assumed connected, and `x` is any point.  The
component of `x`, presented as the open submanifold `componentOpens I hE x`, is compact (a component
is closed, and a closed subset of a compact space is compact), connected and nonempty, so the
abstract classification applies to it; and it is compact, so only the two compact models occur.
Which one is decided by the boundary: `boundary_componentOpens` identifies the boundary of the
component with `I.boundary M ∩ connectedComponent x`. -/
theorem component_diffeomorph (x : M) :
    Nonempty (Diffeomorph I (𝓡 1) (componentOpens I hE x) Circle ∞) ∨
      Nonempty (Diffeomorph I (𝓡∂ 1) (componentOpens I hE x) (Icc (0 : ℝ) 1) ∞) := by
  have : CompactSpace (componentOpens I hE x) :=
    isCompact_iff_compactSpace.1 isClosed_connectedComponent.isCompact
  have : ConnectedSpace (componentOpens I hE x) :=
    isConnected_iff_connectedSpace.1 isConnected_connectedComponent
  rcases eq_empty_or_nonempty (I.boundary M ∩ connectedComponent x) with hb | ⟨p, hpB, hpc⟩
  · refine Or.inl (nonempty_diffeomorphCircle I hE ?_)
    rw [boundary_componentOpens]
    refine eq_empty_iff_forall_notMem.2 fun y hy => ?_
    exact (eq_empty_iff_forall_notMem.1 hb (y : M)) ⟨hy, y.2⟩
  · refine Or.inr (nonempty_diffeomorphIcc I hE (p := ⟨p, hpc⟩) ?_)
    rw [boundary_componentOpens]
    exact hpB

/-- **The components with a boundary point are exactly the ones diffeomorphic to `Icc (0 : ℝ) 1`.**

Forwards: a diffeomorphism of the component with `Icc (0 : ℝ) 1` carries the boundary of the
component onto `(𝓡∂ 1).boundary (Icc (0 : ℝ) 1) = {⊥, ⊤}`, which is nonempty, so the component has a
boundary point.  Backwards: Stage 6 applied to the component, exactly as in
`component_diffeomorph`. -/
theorem nonempty_diffeomorphIcc_component_iff (x : M) :
    Nonempty (Diffeomorph I (𝓡∂ 1) (componentOpens I hE x) (Icc (0 : ℝ) 1) ∞) ↔
      (I.boundary M ∩ connectedComponent x).Nonempty := by
  have : CompactSpace (componentOpens I hE x) :=
    isCompact_iff_compactSpace.1 isClosed_connectedComponent.isCompact
  have : ConnectedSpace (componentOpens I hE x) :=
    isConnected_iff_connectedSpace.1 isConnected_connectedComponent
  constructor
  · rintro ⟨Φ⟩
    have himg := Φ.image_boundary (by simp)
    have hne : (I.boundary (componentOpens I hE x)).Nonempty := by
      rw [← Set.image_nonempty (f := (Φ : (componentOpens I hE x) → Icc (0 : ℝ) 1)), himg,
        boundary_Icc]
      exact ⟨⊥, mem_insert _ _⟩
    obtain ⟨y, hy⟩ := hne
    rw [boundary_componentOpens] at hy
    exact ⟨(y : M), hy, y.2⟩
  · rintro ⟨p, hpB, hpc⟩
    refine nonempty_diffeomorphIcc I hE (p := ⟨p, hpc⟩) ?_
    rw [boundary_componentOpens]
    exact hpB

/-- **The components without a boundary point are exactly the ones diffeomorphic to the circle.**
The complementary half of `nonempty_diffeomorphIcc_component_iff`: forwards because the circle's
model is boundaryless, backwards by Stage 7 applied to the component. -/
theorem nonempty_diffeomorphCircle_component_iff (x : M) :
    Nonempty (Diffeomorph I (𝓡 1) (componentOpens I hE x) Circle ∞) ↔
      I.boundary M ∩ connectedComponent x = ∅ := by
  have : CompactSpace (componentOpens I hE x) :=
    isCompact_iff_compactSpace.1 isClosed_connectedComponent.isCompact
  have : ConnectedSpace (componentOpens I hE x) :=
    isConnected_iff_connectedSpace.1 isConnected_connectedComponent
  constructor
  · rintro ⟨Φ⟩
    have himg := Φ.image_boundary (by simp)
    rw [boundary_circle_eq_empty, Set.image_eq_empty] at himg
    refine eq_empty_iff_forall_notMem.2 fun y hy => ?_
    have hy' : (⟨y, hy.2⟩ : (componentOpens I hE x)) ∈ I.boundary (componentOpens I hE x) := by
      rw [boundary_componentOpens]; exact hy.1
    rw [himg] at hy'
    exact hy'
  · intro hb
    refine nonempty_diffeomorphCircle I hE ?_
    rw [boundary_componentOpens]
    refine eq_empty_iff_forall_notMem.2 fun y hy => ?_
    exact (eq_empty_iff_forall_notMem.1 hb (y : M)) ⟨hy, y.2⟩

end CompactComponents

end OneManifold.Smooth

/-! ## The slice form: compact one-manifolds with boundary in the sense of Chapter 2 -/

section Slice

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The model space of the half-space over a one-point `Z` is one-dimensional.**  `Milnor.HalfSpace
Z` is charted on `ℝ × Z`, and `Module.finrank ℝ (ℝ × Z) = 1 + 0 = 1` when `Z` is a subsingleton.
This is the hypothesis `Module.finrank ℝ E = 1` of the abstract classification, discharged for the
slice setting. -/
theorem finrank_prod_eq_one [Subsingleton Z] : Module.finrank ℝ (ℝ × Z) = 1 := by
  have h0 : Module.finrank ℝ Z = 0 := by
    simpa using Module.finrank_zero_of_subsingleton (R := ℝ) (M := Z)
  simp [Module.finrank_prod, h0]

/-- **A connected component of a half-slice submanifold, as an open subset of it.**  Openness is
`Milnor.OneManifold.Smooth.isOpen_connectedComponent_of_oneManifold` applied to `X` with its
Chapter 2 charted-space and manifold structure over `Milnor.halfSpaceModel Z`, whose model space
`ℝ × Z` is one-dimensional by `finrank_prod_eq_one`.  The carrier is `connectedComponent q` on the
nose, so this is a component of `X` and nothing else. -/
def IsHalfSliceSubmanifold.component [Subsingleton Z] {X B : Set M}
    (hX : IsHalfSliceSubmanifold I Z X B) (q : X) : TopologicalSpace.Opens X :=
  ⟨connectedComponent q, by
    let := hX.chartedSpace
    have := hX.isManifold
    exact OneManifold.Smooth.isOpen_connectedComponent_of_oneManifold
      (halfSpaceModel Z) finrank_prod_eq_one q⟩

/-- The carrier of `Milnor.IsHalfSliceSubmanifold.component` is the connected component. -/
@[simp] theorem IsHalfSliceSubmanifold.coe_component [Subsingleton Z] {X B : Set M}
    (hX : IsHalfSliceSubmanifold I Z X B) (q : X) :
    ((hX.component q : TopologicalSpace.Opens X) : Set X) = connectedComponent q := rfl

/-- **The boundary points of a component, seen in the ambient manifold.**  Chapter 2's
`Milnor.IsHalfSliceSubmanifold.boundary_eq` identifies the intrinsic boundary of `X` with
`{q : X | q.1 ∈ B}`; pushing forward along the injection `Subtype.val : X → M` turns the boundary of
a component into `B ∩ (Subtype.val '' connectedComponent q)`, which is how the rest of the project
speaks of boundary points.  `B ⊆ X` is not needed: a point of `B` that is the value of a point of
the component is automatically a point of `X`. -/
theorem IsHalfSliceSubmanifold.image_boundary_inter_component [Subsingleton Z] {X B : Set M}
    (hX : IsHalfSliceSubmanifold I Z X B) (q : X) :
    letI := hX.chartedSpace
    Subtype.val '' ((halfSpaceModel Z).boundary X ∩ connectedComponent q)
      = B ∩ Subtype.val '' connectedComponent q := by
  let := hX.chartedSpace
  rw [hX.boundary_eq]
  refine Subset.antisymm ?_ ?_
  · rintro y ⟨r, ⟨hrB, hrc⟩, rfl⟩
    exact ⟨hrB, ⟨r, hrc, rfl⟩⟩
  · rintro y ⟨hyB, ⟨r, hrc, rfl⟩⟩
    exact ⟨r, ⟨hyB, hrc⟩, rfl⟩

/-- **Milnor's Appendix in the slice form (book p. 54): every connected component of a compact
one-manifold with boundary is diffeomorphic to the circle or to `Icc (0 : ℝ) 1`.**

Precisely: let `M` be a Hausdorff `C^∞` manifold charted on `H`, let `Z` be a normed space with one
point, and let `X ⊆ M` be a compact half-slice submanifold with boundary `B ⊆ M` in the sense of
`Milnor.IsHalfSliceSubmanifold` -- that is, a compact one-manifold with boundary in the sense of the
book's Chapter 2.  Then for every `q ∈ X` the connected component of `q` in `X`, as a manifold over
`Milnor.halfSpaceModel Z`, is `C^∞`-diffeomorphic either to `Circle` or to `Icc (0 : ℝ) 1`.

The transport follows `Milnor/Appendix/HalfSpace.lean`: `hX.chartedSpace` and `hX.isManifold`
present `X` as a `C^∞` manifold over `halfSpaceModel Z`, `finrank_prod_eq_one` says that model is
one-dimensional, compactness of `X` becomes `CompactSpace X`, Hausdorffness is inherited by a
subtype, and then `Milnor.OneManifold.Smooth.component_diffeomorph` is the abstract theorem. -/
theorem IsHalfSliceSubmanifold.component_diffeomorph [T2Space M] [Subsingleton Z] {X B : Set M}
    (hX : IsHalfSliceSubmanifold I Z X B) (hXc : IsCompact X) (q : X) :
    letI := hX.chartedSpace
    Nonempty (Diffeomorph (halfSpaceModel Z) (𝓡 1) (hX.component q) Circle ∞) ∨
      Nonempty (Diffeomorph (halfSpaceModel Z) (𝓡∂ 1) (hX.component q) (Icc (0 : ℝ) 1) ∞) := by
  let := hX.chartedSpace
  have := hX.isManifold
  have : CompactSpace X := isCompact_iff_compactSpace.1 hXc
  exact OneManifold.Smooth.component_diffeomorph (halfSpaceModel Z) finrank_prod_eq_one q

/-- **The components carrying a boundary point are exactly the ones diffeomorphic to
`Icc (0 : ℝ) 1`.**  The slice form of
`Milnor.OneManifold.Smooth.nonempty_diffeomorphIcc_component_iff`, with the boundary of the
component expressed in the ambient manifold as `B ∩ (Subtype.val '' connectedComponent q)`. -/
theorem IsHalfSliceSubmanifold.nonempty_diffeomorphIcc_component_iff [T2Space M] [Subsingleton Z]
    {X B : Set M} (hX : IsHalfSliceSubmanifold I Z X B) (hXc : IsCompact X) (q : X) :
    letI := hX.chartedSpace
    Nonempty (Diffeomorph (halfSpaceModel Z) (𝓡∂ 1) (hX.component q) (Icc (0 : ℝ) 1) ∞) ↔
      (B ∩ Subtype.val '' connectedComponent q).Nonempty := by
  let := hX.chartedSpace
  have := hX.isManifold
  have : CompactSpace X := isCompact_iff_compactSpace.1 hXc
  have himg : Subtype.val '' ((halfSpaceModel Z).boundary X ∩ connectedComponent q)
      = B ∩ Subtype.val '' connectedComponent q := hX.image_boundary_inter_component q
  rw [← himg, Set.image_nonempty]
  exact OneManifold.Smooth.nonempty_diffeomorphIcc_component_iff (halfSpaceModel Z)
    finrank_prod_eq_one q

/-- **The components carrying no boundary point are exactly the ones diffeomorphic to the circle.**
The slice form of `Milnor.OneManifold.Smooth.nonempty_diffeomorphCircle_component_iff`. -/
theorem IsHalfSliceSubmanifold.nonempty_diffeomorphCircle_component_iff [T2Space M]
    [Subsingleton Z] {X B : Set M} (hX : IsHalfSliceSubmanifold I Z X B) (hXc : IsCompact X)
    (q : X) :
    letI := hX.chartedSpace
    Nonempty (Diffeomorph (halfSpaceModel Z) (𝓡 1) (hX.component q) Circle ∞) ↔
      B ∩ Subtype.val '' connectedComponent q = ∅ := by
  let := hX.chartedSpace
  have := hX.isManifold
  have : CompactSpace X := isCompact_iff_compactSpace.1 hXc
  have himg : Subtype.val '' ((halfSpaceModel Z).boundary X ∩ connectedComponent q)
      = B ∩ Subtype.val '' connectedComponent q := hX.image_boundary_inter_component q
  rw [← himg, Set.image_eq_empty]
  exact OneManifold.Smooth.nonempty_diffeomorphCircle_component_iff (halfSpaceModel Z)
    finrank_prod_eq_one q

/-- **Each component of the second kind contributes exactly two boundary points.**  If the component
of `q` in `X` meets `B` at all, then it meets it in exactly two points -- the two ends of the single
arc-length parametrization of that component, by
`Milnor.OneManifold.Smooth.boundary_inter_component_eq_pair`. -/
theorem IsHalfSliceSubmanifold.ncard_boundary_inter_component [T2Space M] [Subsingleton Z]
    {X B : Set M} (hX : IsHalfSliceSubmanifold I Z X B) (hXc : IsCompact X) (q : X)
    (hne : (B ∩ Subtype.val '' connectedComponent q).Nonempty) :
    (B ∩ Subtype.val '' connectedComponent q).ncard = 2 := by
  let := hX.chartedSpace
  have := hX.isManifold
  have : CompactSpace X := isCompact_iff_compactSpace.1 hXc
  have himg : Subtype.val '' ((halfSpaceModel Z).boundary X ∩ connectedComponent q)
      = B ∩ Subtype.val '' connectedComponent q := hX.image_boundary_inter_component q
  rw [← himg] at hne
  obtain ⟨y, r, hr, -⟩ := hne
  have hcc : connectedComponent q = connectedComponent r := connectedComponent_eq hr.2
  rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective, hcc]
  exact OneManifold.Smooth.ncard_boundary_inter_component (halfSpaceModel Z)
    finrank_prod_eq_one hr.1

/-- **The pairing of the boundary points, realised by the two ends of a component.**  Every boundary
point `p` of a compact one-manifold with boundary has exactly one partner: a boundary point `p' ≠ p`
such that the component of `p` in `X` meets `B` precisely in `{p, p'}`.  This is the geometric
content behind the even count, and the reason it is even. -/
theorem IsHalfSliceSubmanifold.exists_boundary_partner [T2Space M] [Subsingleton Z] {X B : Set M}
    (hX : IsHalfSliceSubmanifold I Z X B) (hXc : IsCompact X) {p : M} (hpB : p ∈ B)
    (hpX : p ∈ X) :
    ∃ p', p' ∈ B ∧ p' ≠ p ∧
      B ∩ Subtype.val '' connectedComponent (⟨p, hpX⟩ : X) = {p, p'} := by
  let := hX.chartedSpace
  have := hX.isManifold
  have : CompactSpace X := isCompact_iff_compactSpace.1 hXc
  have hp : (⟨p, hpX⟩ : X) ∈ (halfSpaceModel Z).boundary X := by rw [hX.boundary_eq]; exact hpB
  obtain ⟨r, hrB, hrp, heq⟩ := OneManifold.Smooth.boundary_inter_component_eq_pair
    (halfSpaceModel Z) finrank_prod_eq_one hp
  refine ⟨(r : M), ?_, ?_, ?_⟩
  · rw [hX.boundary_eq] at hrB; exact hrB
  · exact fun h => hrp (Subtype.ext h)
  · rw [← hX.image_boundary_inter_component, heq, Set.image_insert_eq, Set.image_singleton]

/-- **Milnor's Appendix, as the book uses it, derived from the classification: the boundary of a
compact one-manifold with boundary is finite of even cardinality.**

Same hypotheses as `Milnor.IsHalfSliceSubmanifold.even_ncard_boundary` in
`Milnor/Appendix/HalfSpace.lean`, namely a Hausdorff ambient `C^∞` manifold `M`, a normed space `Z`
with one point, a compact half-slice submanifold `X ⊆ M` with boundary `B ⊆ X`.  The conclusion is
the same statement; the *proof* is different, and that is the point of Stage 9.  The old proof
counts a fixed-point-free involution built from the topological Appendix's arc extension; this one
runs the classification on each component, uses
`Milnor.OneManifold.Smooth.even_ncard_boundary_of_compact` -- whose pairing is the two ends of one
arc-length parametrization -- and transports along `Subtype.val`.  The original theorem is left in
place, is cited by Chapters 2 and 4, and is not used here. -/
theorem IsHalfSliceSubmanifold.even_ncard_boundary_of_classification [T2Space M] [Subsingleton Z]
    {X B : Set M} (hX : IsHalfSliceSubmanifold I Z X B) (hXc : IsCompact X) (hBX : B ⊆ X) :
    B.Finite ∧ Even B.ncard := by
  let := hX.chartedSpace
  have := hX.isManifold
  have : CompactSpace X := isCompact_iff_compactSpace.1 hXc
  have himg : Subtype.val '' ((halfSpaceModel Z).boundary X) = B := by
    rw [hX.boundary_eq]
    refine Subset.antisymm ?_ fun y hy => ⟨⟨y, hBX hy⟩, hy, rfl⟩
    rintro y ⟨r, hrB, rfl⟩
    exact hrB
  rw [← himg]
  refine ⟨(OneManifold.Smooth.finite_boundary_of_compact (halfSpaceModel Z)
    finrank_prod_eq_one).image _, ?_⟩
  rw [Set.ncard_image_of_injective _ Subtype.val_injective]
  exact OneManifold.Smooth.even_ncard_boundary_of_compact (halfSpaceModel Z) finrank_prod_eq_one

end Slice

end Milnor
