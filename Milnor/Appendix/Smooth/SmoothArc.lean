import Milnor.Appendix.Smooth.Setup

/-!
# Milnor's Appendix, smooth version: smooth arcs

Milnor, *Topology from the Differentiable Viewpoint*, Appendix (book p. 54), classifies the
connected one-manifolds.  This file is **Stage 1** of the plan `Exposition/PlanOneManifold.md`,
which builds that classification on top of the topological Appendix of
`Milnor/Appendix/OneManifold.lean` and the one-dimensional model of
`Milnor/Appendix/Smooth/Setup.lean` (Stage 0).

The topological Appendix parametrizes a one-manifold by *arcs*: a `Milnor.OneManifold.Arc M B` is a
homeomorphism from an open subset of `M` onto a bounded order-connected set of reals with at least
two points, under which the "boundary set" `B` corresponds exactly to the non-interior points of
the target.  This file adds smoothness to that notion, taking `B` to be Mathlib's boundary
`I.boundary M` -- which, by Stage 0, is chart-independent for a `C¹` manifold and needs no
compatibility hypothesis.

## What is proved

* `Milnor.OneManifold.Smooth.SmoothArc`: an arc whose coordinate is `Cⁿ` on its source, as a map of
  manifolds into `ℝ`, and whose parametrization is `Cⁿ` on its target, as a map from `ℝ` into the
  manifold.  The target may be half-open -- at a boundary point it is `[0, ε)` -- so the second
  condition is smoothness on a set that is **not open**, i.e. Whitney-style one-sided smoothness at
  the endpoint.  Stage 0's `uniqueDiffOn_modelRange` is the reason this is not pathological; the
  companion fact needed here is `uniqueDiffOn_target` below, which says the same for the target of
  an arc.
* `uniqueDiffOn_target`: the target of *any* arc is convex with nonempty interior, so derivatives
  along it are unique and `derivWithin` is unambiguous at an endpoint.
* `transSource A A'`: the set of `A`-parameters whose point also lies in `A'`, on which the
  transition `s ↦ A'.toFun (A.invFun s)` is defined.  It coincides with the topological Appendix's
  `Milnor.OneManifold.overlap` (`transSource_eq_overlap`, the only statement here that needs
  `T2Space M`, and only because `overlap` is declared under that hypothesis).
* `SmoothArc.contDiffOn_trans`: **the transition between two smooth arcs is `Cⁿ`** on that set --
  applied to `A, A'` and to `A', A` it gives the transition and its inverse.
* `derivWithin_mul_eq_one_of_leftInverse`: the chain rule on a possibly half-open target, isolated
  once and used twice.
* `SmoothArc.derivWithin_trans_mul_derivWithin_trans`, `SmoothArc.derivWithin_trans_ne_zero`: the
  two transition derivatives are reciprocal, so **neither vanishes**.
* `SmoothArc.derivWithin_ne_zero`: **a smooth arc is an immersion** -- read in any chart of the
  maximal atlas, the derivative of the parametrization is nowhere zero on the target, endpoints
  included.
* `SmoothArc.neg`: negating the coordinate of a smooth arc.
* `exists_smoothArc_of_mem_boundary`, `exists_smoothArc_of_notMem_boundary`: **smooth arcs exist
  around every point**, with target `[0, ε)` at a boundary point and `(-ε, ε)` at an interior point.
  These mirror `Milnor.OneManifold.exists_arc_of_mem_boundary` and
  `exists_arc_of_notMem_boundary`, and are built from Stage 0's two normalised local models
  through `smoothArcOfModel`.  Both local models have **bounded** targets, which is what the `Arc`
  structure demands.

## Hypotheses

Throughout, `M` is a manifold charted on a model with corners `I : ModelWithCorners ℝ E H`.
Nothing here assumes that `I` is boundaryless, that `M` is Hausdorff, or that `M` is compact, and
all three shapes of the model range allowed by Stage 0 (`ℝ`, a closed half-line, a nondegenerate
compact interval) stay alive.  The extra hypotheses, where they occur, are:

* `Module.finrank ℝ E = 1` (through `chartCoord` and `modelCoord`): only in the chart statements
  `ofChartCoord`, `contMDiffOn_ofChartCoord`, `SmoothArc.derivWithin_ne_zero` and the two existence
  theorems.  The structure `SmoothArc` itself, `contDiffOn_trans`, the two transition-derivative
  statements and `SmoothArc.neg` never mention the dimension.
* `n ≠ 0`, i.e. `C¹` at least: only where a derivative is taken or where Stage 0's local models are
  invoked -- the transition and immersion statements and the two existence theorems.
* `IsManifold I n M`: only in the two existence theorems, which go through Stage 0.
* `T2Space M`: only in `transSource_eq_overlap`, and only to be able to mention `overlap`.

## The half-open target

Smoothness of the parametrization on a half-open interval is the technical point of the stage, and
it is handled without ever weakening the definition.  Two ingredients do the work.  First,
`ContMDiffOn` is already a Whitney-style notion: `ContMDiffOn 𝓘(ℝ, ℝ) I n A.invFun A.target`
unfolds to a `ContDiffWithinAt` condition relative to `A.target`, which at an endpoint is a
one-sided condition; nothing has to be done to state it.  Second, when a derivative has to be
*computed* there -- in the chain rule of `derivWithin_mul_eq_one_of_leftInverse` -- the set
`A.target` is convex with nonempty interior, hence has unique derivatives by `uniqueDiffOn_convex`,
so `derivWithin` is well defined and two derivatives of the same function agree.  The chain rule
`HasDerivWithinAt.comp` itself needs no unique differentiability, only a `MapsTo`; uniqueness is
needed exactly once, to read off `1` as the derivative of the identity.  No quotient rule is used
anywhere, and no lemma had to be proved by hand about one-sided derivatives.

## References

* Milnor, *Topology from the Differentiable Viewpoint*, Appendix, p. 54.
* `Exposition/PlanOneManifold.md`, Stage 1.
-/

open Set Filter Topology

open scoped ContDiff Manifold

noncomputable section

namespace Milnor.OneManifold.Smooth

/-! ## Derivatives along the target of an arc -/

section ArcTarget

variable {M : Type*} [TopologicalSpace M] {B : Set M}

/-- The target of an arc is convex: it is an order-connected set of reals. -/
theorem convex_target (A : Arc M B) : Convex ℝ A.target :=
  convex_iff_ordConnected.2 A.ordConnected_target

/-- The target of an arc has nonempty interior: the interior is the open interval
`Ioo (sInf) (sSup)`, and the two ends are distinct because the target has at least two points. -/
theorem nonempty_interior_target (A : Arc M B) : (interior A.target).Nonempty := by
  rw [A.interior_target]
  exact nonempty_Ioo.2 A.sInf_lt_sSup

/-- **Derivatives along the target of an arc are unique.** The target is convex with nonempty
interior, so `uniqueDiffOn_convex` applies.  This is the companion, for the target of an arc, of
Stage 0's `uniqueDiffOn_modelRange`, and it is what makes `derivWithin` unambiguous at an *endpoint*
of the target -- the case that actually occurs, since the target of an arc starting at a boundary
point is the half-open interval `Ico 0 ε`. -/
theorem uniqueDiffOn_target (A : Arc M B) : UniqueDiffOn ℝ A.target :=
  uniqueDiffOn_convex (convex_target A) (nonempty_interior_target A)

/-- At every point of the target of an arc, including an endpoint, the derivative within the target
is unique. -/
theorem uniqueDiffWithinAt_target (A : Arc M B) {t : ℝ} (ht : t ∈ A.target) :
    UniqueDiffWithinAt ℝ A.target t := uniqueDiffOn_target A t ht

/-! ## The domain of a transition map -/

/-- **The domain of the transition from `A` to `A'`**: the set of `A`-parameters whose point of `M`
also lies in the source of `A'`.  Equal to the topological Appendix's
`Milnor.OneManifold.overlap A A'` (see `transSource_eq_overlap`), but defined here without the
`T2Space` hypothesis under which `overlap` is declared. -/
def transSource (A A' : Arc M B) : Set ℝ := A.target ∩ A.invFun ⁻¹' A'.source

/-- `transSource` unfolded. -/
theorem transSource_def (A A' : Arc M B) :
    transSource A A' = A.target ∩ A.invFun ⁻¹' A'.source := rfl

/-- The domain of a transition map is contained in the target of the first arc. -/
theorem transSource_subset (A A' : Arc M B) : transSource A A' ⊆ A.target := inter_subset_left

/-- The domain of a transition map is contained in the preimage of the second arc's source. -/
theorem transSource_subset_preimage (A A' : Arc M B) :
    transSource A A' ⊆ A.invFun ⁻¹' A'.source := inter_subset_right

/-- Membership in the domain of a transition map. -/
theorem mem_transSource {A A' : Arc M B} {t : ℝ} (ht : t ∈ A.target)
    (htx : A.invFun t ∈ A'.source) : t ∈ transSource A A' := ⟨ht, htx⟩

/-- A parameter in the domain of the transition names a point of the common source. -/
theorem invFun_mem_of_mem_transSource {A A' : Arc M B} {t : ℝ} (ht : t ∈ transSource A A') :
    A.invFun t ∈ A.source ∩ A'.source := ⟨A.map_target ht.1, ht.2⟩

/-- The transition map carries the domain of the transition from `A` to `A'` into the domain of the
transition back from `A'` to `A`. -/
theorem mapsTo_transSource (A A' : Arc M B) :
    MapsTo (fun s => A'.toFun (A.invFun s)) (transSource A A') (transSource A' A) := by
  intro s hs
  have hx := invFun_mem_of_mem_transSource hs
  refine mem_transSource (A'.map_source hx.2) ?_
  rw [A'.left_inv hx.2]
  exact hx.1

/-- Going from `A` to `A'` and back returns the original parameter. -/
theorem toFun_invFun_trans {A A' : Arc M B} {t : ℝ} (ht : t ∈ transSource A A') :
    A.toFun (A'.invFun (A'.toFun (A.invFun t))) = t := by
  rw [A'.left_inv (invFun_mem_of_mem_transSource ht).2, A.right_inv ht.1]

/-- **The domain of a transition map is the topological Appendix's `overlap`.** This is the only
statement in this file that mentions `T2Space M`, and it does so only because
`Milnor.OneManifold.overlap` is declared under that hypothesis; the two sets are equal for purely
formal reasons. -/
theorem transSource_eq_overlap [T2Space M] (A A' : Arc M B) :
    transSource A A' = overlap A A' := by
  ext t
  refine ⟨fun ht => ⟨A.invFun t, invFun_mem_of_mem_transSource ht, A.right_inv ht.1⟩, fun ht => ?_⟩
  exact mem_transSource (overlap_subset A A' ht) (invFun_mem_of_mem_overlap A A' ht).2

/-! ## The parameters lying over an open set -/

/-- **The parameters of `A` lying over an open set form a relatively open subset of the target.**
The set `A.target ∩ A.invFun ⁻¹' U` is `A.target ∩ W` for some open `W ⊆ ℝ`, by continuity of the
parametrization. -/
theorem exists_isOpen_inter_preimage_invFun (A : Arc M B) {U : Set M} (hU : IsOpen U) :
    ∃ W : Set ℝ, IsOpen W ∧ A.target ∩ A.invFun ⁻¹' U = A.target ∩ W := by
  obtain ⟨W, hW, hWeq⟩ := (continuousOn_iff'.1 A.continuousOn_invFun) U hU
  exact ⟨W, hW, by rw [inter_comm A.target, hWeq, inter_comm]⟩

/-- The parameters of `A` lying over an open set form a neighbourhood, *within the target*, of each
of its points.  This is what lets a derivative computed there be read as a derivative within the
whole target. -/
theorem inter_preimage_invFun_mem_nhdsWithin (A : Arc M B) {U : Set M} (hU : IsOpen U) {t : ℝ}
    (ht : t ∈ A.target) (htU : A.invFun t ∈ U) :
    A.target ∩ A.invFun ⁻¹' U ∈ 𝓝[A.target] t := by
  obtain ⟨W, hW, hWeq⟩ := exists_isOpen_inter_preimage_invFun A hU
  have htW : t ∈ W := by
    have h : t ∈ A.target ∩ W := by rw [← hWeq]; exact ⟨ht, htU⟩
    exact h.2
  rw [hWeq]
  exact inter_mem_nhdsWithin _ (hW.mem_nhds htW)

/-- Derivatives along the parameters of `A` lying over an open set are unique: intersecting the
target with an open set does not spoil unique differentiability. -/
theorem uniqueDiffWithinAt_inter_preimage_invFun (A : Arc M B) {U : Set M} (hU : IsOpen U) {t : ℝ}
    (ht : t ∈ A.target) (htU : A.invFun t ∈ U) :
    UniqueDiffWithinAt ℝ (A.target ∩ A.invFun ⁻¹' U) t := by
  obtain ⟨W, hW, hWeq⟩ := exists_isOpen_inter_preimage_invFun A hU
  have htW : t ∈ W := by
    have h : t ∈ A.target ∩ W := by rw [← hWeq]; exact ⟨ht, htU⟩
    exact h.2
  rw [hWeq]
  exact (uniqueDiffWithinAt_target A ht).inter (hW.mem_nhds htW)

/-! ## The chain rule on a possibly half-open target -/

/-- **The chain rule on the target of an arc, which may be half-open.** Let `A` be an arc, let
`t ∈ A.target` and put `x = A.invFun t`.  Suppose

* `U` is an open set containing `x`;
* `g : M → ℝ` is a real coordinate and `k : ℝ → M` inverts it on `U ∩ A.source`;
* `T ⊆ ℝ` contains the `g`-image of `U ∩ A.source`;
* the composite `s ↦ g (A.invFun s)` has derivative `c` within `A.target ∩ A.invFun ⁻¹' U` at `t`;
* the composite `y ↦ A.toFun (k y)` is differentiable within `T` at `g x`.

Then `c` is also the derivative of `s ↦ g (A.invFun s)` within the whole of `A.target`, and the two
derivatives multiply to `1`; in particular `c ≠ 0`.

Nothing is assumed open about `A.target`: the derivative at an endpoint is a one-sided derivative.
Two facts make the argument go through there.  `HasDerivWithinAt.comp` needs no unique
differentiability, only that `s ↦ g (A.invFun s)` maps `A.target ∩ A.invFun ⁻¹' U` into `T`; and
the one place where uniqueness *is* needed -- identifying the derivative of the identity
`y ↦ A.toFun (k (g (A.invFun y)))` as `1` -- is supplied by
`uniqueDiffWithinAt_inter_preimage_invFun`, i.e. ultimately by the convexity of `A.target`. -/
theorem derivWithin_mul_eq_one_of_leftInverse (A : Arc M B) {U : Set M} (hU : IsOpen U)
    {g : M → ℝ} {k : ℝ → M} {T : Set ℝ} {t c : ℝ} (ht : t ∈ A.target) (htU : A.invFun t ∈ U)
    (hkg : ∀ y ∈ U ∩ A.source, k (g y) = y) (hgT : ∀ y ∈ U ∩ A.source, g y ∈ T)
    (hu : HasDerivWithinAt (fun s => g (A.invFun s)) c (A.target ∩ A.invFun ⁻¹' U) t)
    (hv : DifferentiableWithinAt ℝ (fun y => A.toFun (k y)) T (g (A.invFun t))) :
    HasDerivWithinAt (fun s => g (A.invFun s)) c A.target t ∧
      derivWithin (fun y => A.toFun (k y)) T (g (A.invFun t)) * c = 1 := by
  have hmem : ∀ s ∈ A.target ∩ A.invFun ⁻¹' U, A.invFun s ∈ U ∩ A.source := fun s hs =>
    ⟨hs.2, A.map_target hs.1⟩
  have htS : t ∈ A.target ∩ A.invFun ⁻¹' U := ⟨ht, htU⟩
  have hmaps : MapsTo (fun s => g (A.invFun s)) (A.target ∩ A.invFun ⁻¹' U) T := fun s hs =>
    hgT _ (hmem s hs)
  have hinv : ∀ s ∈ A.target ∩ A.invFun ⁻¹' U, A.toFun (k (g (A.invFun s))) = s := by
    intro s hs
    rw [hkg _ (hmem s hs), A.right_inv hs.1]
  have hchain : HasDerivWithinAt ((fun y => A.toFun (k y)) ∘ fun s => g (A.invFun s))
      (derivWithin (fun y => A.toFun (k y)) T (g (A.invFun t)) * c)
      (A.target ∩ A.invFun ⁻¹' U) t :=
    HasDerivWithinAt.comp t hv.hasDerivWithinAt hu hmaps
  have hid : HasDerivWithinAt (id : ℝ → ℝ)
      (derivWithin (fun y => A.toFun (k y)) T (g (A.invFun t)) * c)
      (A.target ∩ A.invFun ⁻¹' U) t :=
    hchain.congr (fun s hs => (hinv s hs).symm) (hinv t htS).symm
  have huniq : UniqueDiffWithinAt ℝ (A.target ∩ A.invFun ⁻¹' U) t :=
    uniqueDiffWithinAt_inter_preimage_invFun A hU ht htU
  refine ⟨hu.mono_of_mem_nhdsWithin (inter_preimage_invFun_mem_nhdsWithin A hU ht htU), ?_⟩
  exact (huniq.eq_deriv _ (hasDerivWithinAt_id t _) hid).symm

end ArcTarget

/-! ## Smooth arcs -/

section Definition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]

/-- **A smooth arc** of a manifold `M` charted on a model with corners `I`: an arc of `M` relative
to Mathlib's boundary `I.boundary M` -- a homeomorphism from an open subset of `M` onto a bounded
order-connected set of reals with at least two points, carrying boundary points to non-interior
points of the target and nothing else -- both of whose maps are `Cⁿ`.

The forward map is smooth on the source as a map of manifolds into `ℝ`.  The inverse is smooth on
the target as a map from `ℝ` into `M`; since the target need not be open -- at a boundary point it
is `[0, ε)` -- this is smoothness on a non-open set, which is exactly what `ContMDiffOn` means, and
which is unambiguous because the target has unique derivatives (`uniqueDiffOn_target`). -/
structure SmoothArc (I : ModelWithCorners ℝ E H) (n : WithTop ℕ∞) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] extends Arc M (I.boundary M) where
  /-- The coordinate of the arc is `Cⁿ` on the source, as a map of manifolds into `ℝ`. -/
  contMDiffOn_toFun : ContMDiffOn I 𝓘(ℝ, ℝ) n toFun source
  /-- The parametrization is `Cⁿ` on the target, as a map from `ℝ` into the manifold.  The target
  may be half-open, so this is one-sided smoothness at an endpoint. -/
  contMDiffOn_invFun : ContMDiffOn 𝓘(ℝ, ℝ) I n invFun target

end Definition

namespace SmoothArc

section Transition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- **The transition between two smooth arcs is `Cⁿ`.** The transition from `A` to `A'` is the real
function `s ↦ A'.toFun (A.invFun s)`, defined on `transSource A.toArc A'.toArc`; applying the lemma
to `A', A` instead gives the smoothness of the inverse transition.  The domain need not be open, so
this is again smoothness in the Whitney sense; it is proved by composing the two `ContMDiffOn`
fields and reading the result in the trivial model on `ℝ`. -/
theorem contDiffOn_trans (A A' : SmoothArc I n M) :
    ContDiffOn ℝ n (fun s => A'.toFun (A.invFun s)) (transSource A.toArc A'.toArc) :=
  contMDiffOn_iff_contDiffOn.1
    (A'.contMDiffOn_toFun.comp
      (A.contMDiffOn_invFun.mono (transSource_subset A.toArc A'.toArc))
      (transSource_subset_preimage A.toArc A'.toArc))

/-- The transition between two smooth arcs is differentiable within its domain, `derivWithin` being
unambiguous there. -/
theorem differentiableWithinAt_trans (hn : n ≠ 0) (A A' : SmoothArc I n M) {t : ℝ}
    (ht : t ∈ transSource A.toArc A'.toArc) :
    DifferentiableWithinAt ℝ (fun s => A'.toFun (A.invFun s)) (transSource A.toArc A'.toArc) t :=
  (A.contDiffOn_trans A').differentiableOn hn t ht

/-- **The two transition derivatives of a pair of smooth arcs are reciprocal.** At a parameter `t`
of `A` whose point also lies in `A'`, the derivative of the transition `A → A'` within `A.target`
and the derivative of the transition `A' → A` within `A'.target` multiply to `1`.  Both derivatives
are taken within a possibly half-open set, and are unambiguous by `uniqueDiffOn_target`.

Hypotheses: a `Cⁿ` structure with `n ≠ 0`.  No dimension hypothesis, no Hausdorffness, no
compactness. -/
theorem derivWithin_trans_mul_derivWithin_trans (hn : n ≠ 0) (A A' : SmoothArc I n M) {t : ℝ}
    (ht : t ∈ transSource A.toArc A'.toArc) :
    derivWithin (fun s => A.toFun (A'.invFun s)) A'.target (A'.toFun (A.invFun t)) *
      derivWithin (fun s => A'.toFun (A.invFun s)) A.target t = 1 := by
  have hy : A'.toFun (A.invFun t) ∈ transSource A'.toArc A.toArc :=
    mapsTo_transSource A.toArc A'.toArc ht
  have hkg : ∀ y ∈ A'.source ∩ A.source, A'.invFun (A'.toFun y) = y := fun _ hy => A'.left_inv hy.1
  have hgT : ∀ y ∈ A'.source ∩ A.source, A'.toFun y ∈ transSource A'.toArc A.toArc := by
    intro y hy
    refine mem_transSource (A'.map_source hy.1) ?_
    rw [A'.left_inv hy.1]
    exact hy.2
  obtain ⟨hmain, hprod⟩ :=
    derivWithin_mul_eq_one_of_leftInverse A.toArc A'.open_source ht.1 ht.2 hkg hgT
      (A.differentiableWithinAt_trans hn A' ht).hasDerivWithinAt
      (A'.differentiableWithinAt_trans hn A hy)
  -- the backward transition's derivative within `transSource A' A` is its derivative within
  -- `A'.target`, because the former is a neighbourhood of the point within the latter
  have hback : HasDerivWithinAt (fun s => A.toFun (A'.invFun s))
      (derivWithin (fun s => A.toFun (A'.invFun s)) (transSource A'.toArc A.toArc)
        (A'.toFun (A.invFun t))) A'.target (A'.toFun (A.invFun t)) :=
    (A'.differentiableWithinAt_trans hn A hy).hasDerivWithinAt.mono_of_mem_nhdsWithin
      (inter_preimage_invFun_mem_nhdsWithin A'.toArc A.open_source hy.1 hy.2)
  rw [hmain.derivWithin (uniqueDiffWithinAt_target A.toArc ht.1),
    hback.derivWithin (uniqueDiffWithinAt_target A'.toArc hy.1)]
  exact hprod

/-- **The derivative of the transition between two smooth arcs never vanishes.** Immediate from
`derivWithin_trans_mul_derivWithin_trans`: a factor of a product equal to `1` is nonzero.  Together
with `contDiffOn_trans` this says the transition is a `Cⁿ` diffeomorphism onto its image, endpoints
of the (possibly half-open) domain included. -/
theorem derivWithin_trans_ne_zero (hn : n ≠ 0) (A A' : SmoothArc I n M) {t : ℝ}
    (ht : t ∈ transSource A.toArc A'.toArc) :
    derivWithin (fun s => A'.toFun (A.invFun s)) A.target t ≠ 0 :=
  right_ne_zero_of_mul_eq_one (A.derivWithin_trans_mul_derivWithin_trans hn A' ht)

/-! ### Negating the coordinate -/

/-- **Negating the coordinate of a smooth arc.** The underlying arc is
`Milnor.OneManifold.Arc.neg`; smoothness in both directions is preserved because negation of `ℝ` is
smooth with smooth inverse.  This is the smooth counterpart of `Arc.neg`, and it is what lets later
stages normalise the direction in which an arc is traversed. -/
def neg (A : SmoothArc I n M) : SmoothArc I n M where
  toArc := A.toArc.neg
  contMDiffOn_toFun := (contDiff_neg (𝕜 := ℝ) (F := ℝ)).contMDiff.comp_contMDiffOn
    A.contMDiffOn_toFun
  contMDiffOn_invFun :=
    A.contMDiffOn_invFun.comp
      ((contDiff_neg (𝕜 := ℝ) (F := ℝ)).contMDiff.contMDiffOn (s := -A.target))
      fun _ ht => Set.mem_neg.1 ht

/-- The arc underlying `SmoothArc.neg` is `Arc.neg` of the arc underlying the original. -/
@[simp] theorem neg_toArc (A : SmoothArc I n M) : A.neg.toArc = A.toArc.neg := rfl

/-- The coordinate of the negated smooth arc is the negated coordinate. -/
@[simp] theorem neg_toFun (A : SmoothArc I n M) (x : M) : A.neg.toFun x = -A.toFun x := rfl

/-- The parametrization of the negated smooth arc runs the original one backwards. -/
@[simp] theorem neg_invFun (A : SmoothArc I n M) (t : ℝ) : A.neg.invFun t = A.invFun (-t) := rfl

/-- Negating the coordinate does not change the source. -/
@[simp] theorem neg_source (A : SmoothArc I n M) : A.neg.source = A.source := rfl

/-- Negating the coordinate negates the target. -/
@[simp] theorem neg_target (A : SmoothArc I n M) : A.neg.target = -A.target := rfl

end Transition

end SmoothArc

/-! ## A smooth arc is an immersion -/

section Immersion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M]

/-- **The point of `M` with a given chart coordinate**, the local inverse of Stage 0's
`chartCoord`: read the real number in the normalised linear coordinate of `E` and apply the inverse
of the extended chart. -/
def ofChartCoord (e : OpenPartialHomeomorph M H) (t : ℝ) : M :=
  (e.extend I).symm ((modelCoord I hE).symm t)

/-- `ofChartCoord` inverts `chartCoord` on the source of the chart. -/
theorem ofChartCoord_chartCoord {e : OpenPartialHomeomorph M H} {y : M} (hy : y ∈ e.source) :
    ofChartCoord I hE e (chartCoord I hE e y) = y := by
  show (e.extend I).symm ((modelCoord I hE).symm (modelCoord I hE ((e.extend I) y))) = y
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact e.extend_left_inv hy

/-- The coordinate image of a chart is the normalised linear image of the extended chart's target.
-/
theorem chartCoord_image_source (e : OpenPartialHomeomorph M H) :
    chartCoord I hE e '' e.source = modelCoord I hE '' (e.extend I).target := by
  rw [e.extend_target_eq_image_source, ← Set.image_comp]; rfl

/-- A point of the coordinate image of a chart names, in the normalised linear coordinate, a point
of the extended chart's target -- so `ofChartCoord` is defined there by the extended chart's
inverse. -/
theorem symm_modelCoord_mem_extend_target {e : OpenPartialHomeomorph M H} {t : ℝ}
    (ht : t ∈ chartCoord I hE e '' e.source) : (modelCoord I hE).symm t ∈ (e.extend I).target := by
  rw [chartCoord_image_source] at ht
  obtain ⟨v, hv, rfl⟩ := ht
  rwa [ContinuousLinearEquiv.symm_apply_apply]

/-- The coordinate of a point of a chart lies in the chart's coordinate image. -/
theorem chartCoord_mem_image {e : OpenPartialHomeomorph M H} {y : M} (hy : y ∈ e.source) :
    chartCoord I hE e y ∈ chartCoord I hE e '' e.source := ⟨y, hy, rfl⟩

variable [ChartedSpace H M]

/-- **The inverse chart coordinate is `Cⁿ`** on the chart's coordinate image, as a map from `ℝ`
into the manifold.  That image is only *relatively* open in the model range -- Stage 0's
`exists_isOpen_chartCoord_image` -- so this too is smoothness on a possibly non-open set.  It is
Mathlib's `contMDiffOn_extend_symm` composed with the normalised linear coordinate. -/
theorem contMDiffOn_ofChartCoord {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M) :
    ContMDiffOn 𝓘(ℝ, ℝ) I n (ofChartCoord I hE e) (chartCoord I hE e '' e.source) := by
  have h1 : ContMDiffOn 𝓘(ℝ, E) I n (e.extend I).symm (e.extend I).target := by
    rw [e.extend_target']
    exact contMDiffOn_extend_symm he
  have h2 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) n (fun t : ℝ => (modelCoord I hE).symm t)
      (chartCoord I hE e '' e.source) :=
    ((modelCoord I hE).symm.contDiff.contMDiff).contMDiffOn
  exact h1.comp h2 fun _ ht => symm_modelCoord_mem_extend_target I hE ht

/-- **A smooth arc is an immersion.** Read in any chart `e` of the maximal `Cⁿ` atlas, the velocity
of the parametrization of a smooth arc is nowhere zero: for every parameter `t` of the arc whose
point lies in the source of `e`, the derivative of `s ↦ chartCoord e (A.invFun s)` within
`A.target` is nonzero.

The derivative is taken within `A.target`, which may be half-open, and `t` may be an endpoint; it is
unambiguous by `uniqueDiffOn_target`.  The proof is the chain rule of
`derivWithin_mul_eq_one_of_leftInverse` with `g = chartCoord e` and `k = ofChartCoord e`, together
with the `Cⁿ` smoothness of both.

Hypotheses: `Module.finrank ℝ E = 1` (to have `chartCoord` at all), `n ≠ 0`, and `e` in the maximal
`Cⁿ` atlas.  No Hausdorffness, no compactness, and all three shapes of the model range. -/
theorem SmoothArc.derivWithin_ne_zero (hn : n ≠ 0) (A : SmoothArc I n M)
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I n M) {t : ℝ}
    (ht : t ∈ A.target) (hx : A.invFun t ∈ e.source) :
    derivWithin (fun s => chartCoord I hE e (A.invFun s)) A.target t ≠ 0 := by
  have hkg : ∀ y ∈ e.source ∩ A.source, ofChartCoord I hE e (chartCoord I hE e y) = y :=
    fun _ hy => ofChartCoord_chartCoord I hE hy.1
  have hgT : ∀ y ∈ e.source ∩ A.source, chartCoord I hE e y ∈
      chartCoord I hE e '' e.source ∩ ofChartCoord I hE e ⁻¹' A.source := by
    intro y hy
    refine ⟨chartCoord_mem_image I hE hy.1, ?_⟩
    show ofChartCoord I hE e (chartCoord I hE e y) ∈ A.source
    rw [ofChartCoord_chartCoord I hE hy.1]
    exact hy.2
  have hu : ContDiffOn ℝ n (fun s => chartCoord I hE e (A.invFun s))
      (A.target ∩ A.invFun ⁻¹' e.source) :=
    contMDiffOn_iff_contDiffOn.1 ((contMDiffOn_chartCoord I hE he).comp
      (A.contMDiffOn_invFun.mono inter_subset_left) inter_subset_right)
  have hv : ContDiffOn ℝ n (fun y => A.toFun (ofChartCoord I hE e y))
      (chartCoord I hE e '' e.source ∩ ofChartCoord I hE e ⁻¹' A.source) :=
    contMDiffOn_iff_contDiffOn.1 (A.contMDiffOn_toFun.comp
      ((contMDiffOn_ofChartCoord I hE he).mono inter_subset_left) inter_subset_right)
  obtain ⟨hmain, hprod⟩ :=
    derivWithin_mul_eq_one_of_leftInverse A.toArc e.open_source ht hx hkg hgT
      ((hu.differentiableOn hn t ⟨ht, hx⟩).hasDerivWithinAt)
      (hv.differentiableOn hn _ (hgT _ ⟨hx, A.map_target ht⟩))
  rw [hmain.derivWithin (uniqueDiffWithinAt_target A.toArc ht)]
  exact right_ne_zero_of_mul_eq_one hprod

end Immersion

/-! ## Smooth arcs from the two normalised local models -/

section Existence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **A smooth arc from a local model.** A partial homeomorphism `f` from `M` to `ℝ` with open
source, bounded order-connected target with at least two points, the boundary law, and `Cⁿ`
smoothness in both directions, *is* a smooth arc.  This is the shape in which Stage 0's
`exists_boundaryModel` and `exists_interiorModel` deliver their local models; boundedness of the
target -- which the `Arc` structure demands and which both local models supply, their targets being
`[0, ε)` and `(-ε, ε)` -- is an explicit hypothesis here. -/
def smoothArcOfModel (f : PartialHomeomorph M ℝ) (hopen : IsOpen f.source)
    (hoc : f.target.OrdConnected) (hnt : f.target.Nontrivial) (hba : BddAbove f.target)
    (hbb : BddBelow f.target)
    (hbdry : ∀ y ∈ f.source, y ∈ I.boundary M ↔ f y ∉ interior f.target)
    (hfwd : ContMDiffOn I 𝓘(ℝ, ℝ) n f f.source)
    (hinv : ContMDiffOn 𝓘(ℝ, ℝ) I n f.symm f.target) : SmoothArc I n M where
  toFun x := f x
  invFun t := f.symm t
  source := f.source
  target := f.target
  map_source' _ hx := f.map_source hx
  map_target' _ ht := f.map_target ht
  left_inv' _ hx := f.left_inv hx
  right_inv' _ ht := f.right_inv ht
  open_source := hopen
  ordConnected_target := hoc
  nontrivial_target := hnt
  bddAbove_target := hba
  bddBelow_target := hbb
  continuousOn_toFun := f.continuousOn
  continuousOn_invFun := f.continuousOn_symm
  bdry := hbdry
  contMDiffOn_toFun := hfwd
  contMDiffOn_invFun := hinv

/-- The source of a smooth arc built from a local model is the model's source. -/
@[simp] theorem smoothArcOfModel_source (f : PartialHomeomorph M ℝ) (hopen hoc hnt hba hbb hbdry)
    (hfwd : ContMDiffOn I 𝓘(ℝ, ℝ) n f f.source)
    (hinv : ContMDiffOn 𝓘(ℝ, ℝ) I n f.symm f.target) :
    (smoothArcOfModel I f hopen hoc hnt hba hbb hbdry hfwd hinv).source = f.source := rfl

/-- The target of a smooth arc built from a local model is the model's target. -/
@[simp] theorem smoothArcOfModel_target (f : PartialHomeomorph M ℝ) (hopen hoc hnt hba hbb hbdry)
    (hfwd : ContMDiffOn I 𝓘(ℝ, ℝ) n f f.source)
    (hinv : ContMDiffOn 𝓘(ℝ, ℝ) I n f.symm f.target) :
    (smoothArcOfModel I f hopen hoc hnt hba hbb hbdry hfwd hinv).target = f.target := rfl

/-- The coordinate of a smooth arc built from a local model is the model map. -/
@[simp] theorem smoothArcOfModel_toFun (f : PartialHomeomorph M ℝ) (hopen hoc hnt hba hbb hbdry)
    (hfwd : ContMDiffOn I 𝓘(ℝ, ℝ) n f f.source)
    (hinv : ContMDiffOn 𝓘(ℝ, ℝ) I n f.symm f.target) (x : M) :
    (smoothArcOfModel I f hopen hoc hnt hba hbb hbdry hfwd hinv).toFun x = f x := rfl

/-- The parametrization of a smooth arc built from a local model is the model's inverse. -/
@[simp] theorem smoothArcOfModel_invFun (f : PartialHomeomorph M ℝ) (hopen hoc hnt hba hbb hbdry)
    (hfwd : ContMDiffOn I 𝓘(ℝ, ℝ) n f f.source)
    (hinv : ContMDiffOn 𝓘(ℝ, ℝ) I n f.symm f.target) (t : ℝ) :
    (smoothArcOfModel I f hopen hoc hnt hba hbb hbdry hfwd hinv).invFun t = f.symm t := rfl

variable [IsManifold I n M]

/-- **A smooth arc starting at a boundary point.** Every boundary point `p` of a `Cⁿ` one-manifold
(`n ≠ 0`) lies in the source of a smooth arc whose target is the half-open interval `Ico 0 ε` and
which sends `p` to `0`.  This is the smooth counterpart of
`Milnor.OneManifold.exists_arc_of_mem_boundary`, built from Stage 0's `exists_boundaryModel`.

The target `Ico 0 ε` is bounded, as the `Arc` structure demands, and half-open, which is why the
smoothness of the parametrization is one-sided at `0`.

Hypotheses: `Module.finrank ℝ E = 1`, `IsManifold I n M` with `n ≠ 0`.  No Hausdorffness, no
compactness; all three shapes of the model range are covered (in the line case the statement is
vacuous, there being no boundary point, and in the compact-interval case Stage 0's normalisation
reflects the coordinate when `p` is the upper endpoint of the model). -/
theorem exists_smoothArc_of_mem_boundary (hE : Module.finrank ℝ E = 1) (hn : n ≠ 0) {p : M}
    (hp : p ∈ I.boundary M) :
    ∃ (A : SmoothArc I n M) (ε : ℝ), 0 < ε ∧ p ∈ A.source ∧ A.toFun p = 0 ∧
      A.target = Ico 0 ε := by
  obtain ⟨ε, f, σ, hε, -, hopen, hpf, -, -, hf0, htgt, hbd, hfwd, hinv⟩ :=
    exists_boundaryModel I hE hn hp
  have hoc : f.target.OrdConnected := by rw [htgt]; exact ordConnected_Ico
  have hnt : f.target.Nontrivial := by
    rw [htgt]
    exact ⟨0, ⟨le_rfl, hε⟩, ε / 2, ⟨by positivity, by linarith⟩, by intro h; linarith⟩
  have hba : BddAbove f.target := by rw [htgt]; exact bddAbove_Ico
  have hbb : BddBelow f.target := by rw [htgt]; exact bddBelow_Ico
  have hbdry : ∀ y ∈ f.source, y ∈ I.boundary M ↔ f y ∉ interior f.target := by
    intro y hy
    have hyt : f y ∈ Ico 0 ε := by rw [← htgt]; exact f.map_source hy
    rw [hbd y hy, htgt, interior_Ico]
    refine ⟨fun h0 => by rw [h0]; simp, fun h => ?_⟩
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at h
    rcases h with h | h
    · exact le_antisymm h hyt.1
    · exact absurd hyt.2 (not_lt.2 h)
  exact ⟨smoothArcOfModel I f hopen hoc hnt hba hbb hbdry hfwd hinv, ε, hε, hpf, hf0, htgt⟩

/-- **A smooth arc around an interior point.** Every point `y` of a `Cⁿ` one-manifold (`n ≠ 0`) that
is *not* a boundary point lies in the source of a smooth arc whose target is the **open** interval
`Ioo (-ε) ε`, which sends `y` to `0`, and whose source consists of interior points only.  This is
the smooth counterpart of `Milnor.OneManifold.exists_arc_of_notMem_boundary`, built from Stage 0's
`exists_interiorModel`; as there, the conclusion `interior A.target = A.target` is recorded, since
that is the form in which the topological Appendix consumes it.

The target `Ioo (-ε) ε` is bounded, as the `Arc` structure demands.  The `ε` comes from shrinking
the chart away from the endpoints of the model range, which is what Stage 0's local model does.

Hypotheses: `Module.finrank ℝ E = 1`, `IsManifold I n M` with `n ≠ 0`.  No Hausdorffness, no
compactness, all three shapes of the model range. -/
theorem exists_smoothArc_of_notMem_boundary (hE : Module.finrank ℝ E = 1) (hn : n ≠ 0) {y : M}
    (hy : y ∉ I.boundary M) :
    ∃ (A : SmoothArc I n M) (ε : ℝ), 0 < ε ∧ y ∈ A.source ∧ A.toFun y = 0 ∧
      A.target = Ioo (-ε) ε ∧ interior A.target = A.target ∧ A.source ⊆ I.interior M := by
  have hyint : y ∈ I.interior M := by
    rw [← I.compl_interior, mem_compl_iff] at hy
    exact not_not.1 hy
  obtain ⟨ε, f, hε, hopen, hyf, -, -, hf0, htgt, hint, hfwd, hinv⟩ :=
    exists_interiorModel I hE hn hyint
  have hoc : f.target.OrdConnected := by rw [htgt]; exact ordConnected_Ioo
  have hnt : f.target.Nontrivial := by
    rw [htgt]
    exact ⟨0, ⟨by linarith, hε⟩, ε / 2, ⟨by linarith, by linarith⟩, by intro h; linarith⟩
  have hba : BddAbove f.target := by rw [htgt]; exact bddAbove_Ioo
  have hbb : BddBelow f.target := by rw [htgt]; exact bddBelow_Ioo
  have hbdry : ∀ z ∈ f.source, z ∈ I.boundary M ↔ f z ∉ interior f.target := by
    intro z hz
    have hzt : f z ∈ Ioo (-ε) ε := by rw [← htgt]; exact f.map_source hz
    rw [htgt, interior_Ioo]
    refine ⟨fun hzb => absurd (hint hz) ?_, fun hcon => absurd hzt hcon⟩
    rw [← I.compl_interior, mem_compl_iff] at hzb
    exact hzb
  refine ⟨smoothArcOfModel I f hopen hoc hnt hba hbb hbdry hfwd hinv, ε, hε, hyf, hf0, htgt, ?_,
    hint⟩
  show interior f.target = f.target
  rw [htgt, interior_Ioo]

end Existence

end Milnor.OneManifold.Smooth
