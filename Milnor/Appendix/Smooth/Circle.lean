import Milnor.Appendix.Smooth.Compact
import Milnor.Chapter1.InverseFunction
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Milnor's Appendix, smooth version: the compact boundaryless case is the circle

Milnor, *Topology from the Differentiable Viewpoint*, Appendix (book p. 54), classifies the connected
one-manifolds into four cases.  This file is **Stage 7** of the plan
`Exposition/PlanOneManifold.md`, and it settles Milnor's first case: **a compact, Hausdorff,
connected, boundaryless smooth one-manifold is diffeomorphic to `Circle`**
(`nonempty_diffeomorphCircle`).

## The headline theorems

* `exists_periodic_parametrisation` -- **Milnor's periodic parametrisation, Step 5.**  On a nonempty
  compact Hausdorff preconnected `C^∞` one-manifold `M` with `I.boundary M = ∅` there are a length
  element `L`, a period `T > 0` and a map `γ : ℝ → M` which is an arc-length parametrization near
  every time, is `T`-periodic and onto, is injective on `[0, T)`, has `T` as its *least* period, and
  satisfies `γ s = γ t ↔ ∃ n : ℤ, s - t = n * T`.  In words: a compact connected boundaryless
  one-manifold *is* a closed geodesic of length `T`.
* `nonempty_diffeomorphCircle` -- **the classification**: such an `M` is `C^∞`-diffeomorphic to
  `Circle` with `Mathlib`'s model `𝓡 1`.  `nonempty_diffeomorphCircle'` is the same statement in the
  direction `Circle → M`.

## The three intermediate results, each usable on its own

**(1) The two-component geometry, as rigidity of unit-speed curves.**  A *unit-speed curve*
(`IsUnitSpeedCurveOn`) is a map `γ : ℝ → M` which, near every time of a set `U`, coincides with the
arc-length parametrization `s ↦ A.invFun (s - k)` of a unit-speed smooth arc.  Unlike an `Arc` it is
not injective -- which is the whole point, since the curve that wraps around a circle is not.  The
key rigidity statements are:

* `trans_eq_add_of_two_points`: a transition of unit-speed arcs that is `v ↦ v + m` at two parameters
  of one component of the overlap is `v ↦ v + m` on the whole component.  This is Stage 5's affine
  half of Milnor's Lemma 1 (`exists_affine_trans`), sharpened by two coincidences.
* `eqOn_of_eventuallyEq` -- **the propagation lemma**: two unit-speed curves on the same interval of
  times which agree near one time agree at every time.  This replaces the uniqueness theorem for
  integral curves that Mathlib proves only for manifolds without boundary and only for genuine
  flows, and it needs nothing but `T2Space M`.
* `periodic_of_eq`: if `γ t₁ = γ t₂` then `t₂ - t₁` is a period.  Read in an arc `B` centred at the
  common value, the curve has slope `σ₁ = ±1` near `t₁` and `σ₂ = ±1` near `t₂`; if the signs agree
  the period follows, and if they disagree the curve would reflect about the midpoint, contradicting
  its local injectivity.  **That the two slopes must agree is exactly the fact the plan singles out
  as the one part of Milnor's Step 5 with no counterpart in the existing topological file.**

**(2) The periodic parametrisation.**  `Reach`, `Dom` and `globalCurve` build the maximal unit-speed
curve issuing from a fixed arc: `Reach` is single-valued by propagation (`Reach.unique`), so a
function can be extracted from it, and `Dom` -- the set of times it reaches -- is an open interval
containing `0` (`ordConnected_dom`, `isOpen_dom`).  `not_bddAbove_dom` shows `Dom` is unbounded above
(and, applied to the reversed arc, below), so `dom_eq_univ`: the curve is defined on the whole line.
`exists_period` then produces a positive period from compactness, and `exists_minimal_period` the
least one.

**(3) The minimal period.**  The set of periods is a closed subgroup of the line -- closed because
the curve is continuous -- and *discrete*, because a unit-speed curve is injective near every time,
so no period is smaller than the radius of an interval of injectivity.  The positive periods are
therefore the elements of a closed set bounded below, whose infimum belongs to it; and every period
is an integer multiple of that least one.  `surjective_of_periodic` finishes the geometry: the image
of the curve is the image of `[0, T]`, hence closed, and open because the curve is a local
parametrization, so it is all of a preconnected `M`.

## How the descent goes, and why it cannot go through a quotient

Mathlib has no quotient-manifold theory, so `ℝ / T ℤ` is not available as a smooth manifold and the
descent must go through *local inverses of the exponential*.  Concretely:

* `circleParam T t = Circle.exp (2π t / T)` is smooth (`contMDiff_circleParam`), onto
  (`circleParam_surjective`, by the explicit section `circleSection` built from the principal
  argument), and identifies exactly the times differing by a multiple of `T`
  (`circleParam_eq_iff`).
* `isLocalDiffeomorph_circleParam`: `circleParam T` is a local diffeomorphism.  The project's
  manifold inverse function theorem `Milnor.ContMDiff.isLocalDiffeomorphAt_of_isInvertible_mfderiv`
  reduces this to invertibility of the derivative, and that is obtained **without computing a chart
  of the circle**: the coordinate functions `z ↦ (z : ℂ).im` and `z ↦ (z : ℂ).re` are smooth
  (`contMDiff_coe_sphere`) and pull back to `sin (2π t/T)` and `cos (2π t/T)`, whose derivatives
  cannot both vanish; rescaling whichever is nonzero gives a smooth `ψ : Circle → ℝ` with
  `(ψ ∘ circleParam T)' (t) = 1`, so `mfderiv ψ` is a continuous linear *left* inverse of
  `mfderiv (circleParam T)`, and on a one-dimensional tangent space a left inverse is two-sided
  (`isInvertible_of_finrank_one`).
* The descended map is `z ↦ γ (circleSection T z)`.  It is bijective because `γ` and `circleParam T`
  identify *the same* pairs of times, and it is a local diffeomorphism because it agrees, near each
  point, with `γ` composed with a local inverse of `circleParam T`
  (`IsLocalDiffeomorphAt.congr_eventuallyEq`, `IsUnitSpeedCurveOn.isLocalDiffeomorphAt`).  Mathlib's
  `IsLocalDiffeomorph.diffeomorphOfBijective` then gives the diffeomorphism, with no
  finite-dimensionality and no boundarylessness hypothesis of its own.

## Hypotheses, and which step uses what

`E` is a real normed space with `Module.finrank ℝ E = 1`, `I : ModelWithCorners ℝ E H`, and `M` is a
`C^∞` manifold charted on `H` (`IsManifold I ∞ M`).  Beyond that:

* `I.boundary M = ∅` is the boundarylessness hypothesis, and it is about `M`, not about the model:
  the model range may still be a half-line or a compact interval.  It is used through
  `Arc.isOpen_target_of_boundary_eq_empty` -- on a boundaryless manifold every arc has an *open*
  target, which is what lets an arc be read as a unit-speed curve on an open interval of times -- and
  through `exists_unitSpeed_centred`, which needs a point that is not a boundary point.  Note that
  the propagation lemma itself needs no boundarylessness.
* `T2Space M` is used three times: by Stage 3 to build a length element, by Stage 5's `overlap`/
  `trans` API, and -- essentially -- in the propagation lemma, for uniqueness of limits.
* `CompactSpace M` is used twice, and **σ-compactness would not do for either**: to make the curve
  accumulate as its time approaches the end of its interval, which is what lets it be continued
  (`not_bddAbove_dom`), and to make it accumulate at `+∞`, which is what forces it to return and
  produces the period (`exists_period`).  Compactness also feeds Stage 3 through
  `CompactSpace.sigmaCompact`, and that use alone could be relaxed.
* `PreconnectedSpace M` is used only for surjectivity, and `Nonempty M` only to choose a base point.
* No second countability (compact plus Hausdorff plus a finite-dimensional model gives it), no
  orientability, and no `BoundarylessManifold` instance.

## What had to be restated, and what the plan got wrong

**Nothing in `Milnor/Appendix/OneManifold.lean` or in Stages 0--6 is edited.**  What is *restated*
here is the exhaustion: Stage 6's `exists_closed_unitSpeedArc`, and with it
`Milnor.OneManifold.exists_closed_arc`, cannot be reused, and neither can Stage 5's extension
theorem.  **The reason is a genuine gap in the plan.**  The plan's Stage 7 says to "run the
exhaustion" and reach a stage where the overlap has two components.  But on a boundaryless manifold
every arc has an open target (see above), whereas `exists_extension_unitSpeed` -- and the topological
`exists_extension` it refines -- require the first arc to have target `Ico 0 c`, i.e. to *start at a
boundary point*.  So the with-boundary exhaustion is not merely inconvenient here, it is inapplicable,
and the finite-cover induction of Stage 6 has no boundaryless analogue in the form the plan assumes.

The route taken instead replaces arcs by *curves*: a unit-speed curve is not required to be
injective, so continuing it past the end of its interval needs no gluing of arcs and no
two-component bookkeeping at all.  The propagation lemma does all the work, the continuation step is
five lines of gluing, and the two-component geometry appears where it belongs -- as the statement
that two times with the same value have matching directions (`periodic_of_eq`).  This is a shorter
honest route than the plan's, and it dispenses with one of the plan's three named sub-problems
(the exhaustion) while keeping the other two.

## References

* Milnor, *Topology from the Differentiable Viewpoint*, Appendix, p. 54 (Step 5 and the circle case).
* `Exposition/PlanOneManifold.md`, Stage 7 and §3(a).
-/

open Set Filter Topology

open scoped ContDiff Manifold

noncomputable section

namespace Milnor.OneManifold.Smooth

/-! ## Arcs of a boundaryless manifold -/

section Boundaryless

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **On a boundaryless manifold every arc has an open target.**  The boundary law of an `Arc` says
that a point of the source lies in the boundary exactly when its coordinate is *not* an interior
point of the target; if the boundary is empty, every coordinate is an interior point, so the target
is its own interior. -/
theorem Arc.isOpen_target_of_boundary_eq_empty (hb : I.boundary M = ∅)
    (A : Arc M (I.boundary M)) : IsOpen A.target := by
  have h : A.target ⊆ interior A.target := by
    intro t ht
    have hx : A.invFun t ∈ A.source := A.map_target ht
    have hiff := A.bdry _ hx
    rw [A.right_inv ht] at hiff
    exact not_not.1 fun hc => absurd (hb.subset (hiff.2 hc)) (Set.notMem_empty _)
  exact interior_eq_iff_isOpen.1 (Subset.antisymm interior_subset h)

/-- The target of a smooth arc of a boundaryless manifold is open. -/
theorem SmoothArc.isOpen_target {n : WithTop ℕ∞} (hb : I.boundary M = ∅) (A : SmoothArc I n M) :
    IsOpen A.target :=
  Arc.isOpen_target_of_boundary_eq_empty hb A.toArc

/-- **A smooth arc of a boundaryless manifold is a partial diffeomorphism** from `ℝ` to `M`: its
target is open, its source is open, and the two smoothness fields of a `SmoothArc` are exactly the
two smoothness fields of a `Mathlib` `PartialDiffeomorph`, read in the trivial model on `ℝ`. -/
def SmoothArc.partialDiffeomorph {n : WithTop ℕ∞} (hb : I.boundary M = ∅) (A : SmoothArc I n M) :
    PartialDiffeomorph 𝓘(ℝ, ℝ) I ℝ M n where
  toFun := A.invFun
  invFun := A.toFun
  source := A.target
  target := A.source
  map_source' := A.map_target'
  map_target' := A.map_source'
  left_inv' := A.right_inv'
  right_inv' := A.left_inv'
  open_source := A.isOpen_target hb
  open_target := A.open_source
  contMDiffOn_toFun := A.contMDiffOn_invFun
  contMDiffOn_invFun := A.contMDiffOn_toFun

/-- **A smooth arc carries open sets of parameters to open sets of points.**  The image of
`V ∩ A.target` under the parametrization is `A.source ∩ A.toFun ⁻¹' V`, which is open because the
source is open and the coordinate is continuous on it. -/
theorem SmoothArc.isOpen_image {n : WithTop ℕ∞} (A : SmoothArc I n M) {V : Set ℝ} (hV : IsOpen V) :
    IsOpen (A.invFun '' (V ∩ A.target)) := by
  have heq : A.invFun '' (V ∩ A.target) = A.source ∩ A.toFun ⁻¹' V := by
    ext x
    constructor
    · rintro ⟨t, ⟨htV, htT⟩, rfl⟩
      exact ⟨A.map_target htT, by rw [Set.mem_preimage, A.right_inv htT]; exact htV⟩
    · rintro ⟨hx, hxV⟩
      exact ⟨A.toFun x, ⟨hxV, A.map_source hx⟩, A.left_inv hx⟩
  rw [heq]
  exact A.continuousOn_toFun.isOpen_inter_preimage A.open_source hV

end Boundaryless

/-! ## Unit-speed curves -/

section Curves

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **A unit-speed curve on a set of times.**  `γ : ℝ → M` is a unit-speed curve on `U` when every
`t ∈ U` has an interval `Ioo (t - η) (t + η) ⊆ U` on which `γ` is a *shifted parametrization by a
unit-speed smooth arc*: there are a unit-speed smooth arc `A` and a shift `k` with
`γ s = A.invFun (s - k)` and `s - k ∈ A.target` throughout that interval.

This is Milnor's "parametrization by arc length", localized.  Unlike an `Arc` it is *not* assumed
injective -- which is the whole point, since the curve that wraps around a circle is not -- and
unlike a `SmoothArc` it is a genuine function on `ℝ`, so two of them can be compared time by time.
Requiring the interval to lie inside `U` makes `U` open. -/
def IsUnitSpeedCurveOn (L : LengthElement I ∞ M) (γ : ℝ → M) (U : Set ℝ) : Prop :=
  ∀ t ∈ U, ∃ (A : SmoothArc I ∞ M) (k η : ℝ), UnitSpeed L A ∧ 0 < η ∧
    Ioo (t - η) (t + η) ⊆ U ∧
      ∀ s ∈ Ioo (t - η) (t + η), s - k ∈ A.target ∧ γ s = A.invFun (s - k)

namespace IsUnitSpeedCurveOn

variable {L : LengthElement I ∞ M} {γ : ℝ → M} {U : Set ℝ}

/-- The set of times of a unit-speed curve is open. -/
theorem isOpen (h : IsUnitSpeedCurveOn L γ U) : IsOpen U := by
  rw [Metric.isOpen_iff]
  intro t ht
  obtain ⟨A, k, η, -, hη, hsub, -⟩ := h t ht
  refine ⟨η, hη, fun s hs => hsub ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- A unit-speed curve restricts to any open subset of its times. -/
theorem mono (h : IsUnitSpeedCurveOn L γ U) {V : Set ℝ} (hV : IsOpen V) (hVU : V ⊆ U) :
    IsUnitSpeedCurveOn L γ V := by
  intro t ht
  obtain ⟨A, k, η, hA, hη, -, hdesc⟩ := h t (hVU ht)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hV t ht
  refine ⟨A, k, min η δ, hA, lt_min hη hδ, ?_, fun s hs => hdesc s ?_⟩
  · intro s hs
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hs.1, min_le_right η δ], by linarith [hs.2, min_le_right η δ]⟩
  · exact ⟨by linarith [hs.1, min_le_left η δ], by linarith [hs.2, min_le_left η δ]⟩

/-- Being a unit-speed curve depends only on the values of the map on the given times. -/
theorem congr (h : IsUnitSpeedCurveOn L γ U) {γ' : ℝ → M} (hγ : ∀ t ∈ U, γ' t = γ t) :
    IsUnitSpeedCurveOn L γ' U := by
  intro t ht
  obtain ⟨A, k, η, hA, hη, hsub, hdesc⟩ := h t ht
  exact ⟨A, k, η, hA, hη, hsub, fun s hs => ⟨(hdesc s hs).1,
    by rw [hγ s (hsub hs)]; exact (hdesc s hs).2⟩⟩

/-- **A unit-speed curve is continuous at each of its times**, the arc's parametrization being
continuous on its target. -/
theorem continuousAt (h : IsUnitSpeedCurveOn L γ U) {t : ℝ} (ht : t ∈ U) : ContinuousAt γ t := by
  obtain ⟨A, k, η, -, hη, -, hdesc⟩ := h t ht
  have hmem : Ioo (t - η) (t + η) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hcont : ContinuousAt (fun s => A.invFun (s - k)) t := by
    have h1 : ContinuousWithinAt A.invFun A.target (t - k) :=
      A.continuousOn_invFun _ (hdesc t ⟨by linarith, by linarith⟩).1
    have h2 : Tendsto (fun s : ℝ => s - k) (𝓝 t) (𝓝[A.target] (t - k)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨(continuous_id.sub continuous_const).continuousAt, ?_⟩
      filter_upwards [hmem] with s hs using (hdesc s hs).1
    exact h1.tendsto.comp h2
  refine hcont.congr ?_
  filter_upwards [hmem] with s hs using (hdesc s hs).2.symm

/-- **A unit-speed curve is injective near each of its times**: on the interval supplied by the
definition it is the injective parametrization of an arc, shifted. -/
theorem exists_injOn (h : IsUnitSpeedCurveOn L γ U) {t : ℝ} (ht : t ∈ U) :
    ∃ η > 0, Ioo (t - η) (t + η) ⊆ U ∧ InjOn γ (Ioo (t - η) (t + η)) := by
  obtain ⟨A, k, η, -, hη, hsub, hdesc⟩ := h t ht
  refine ⟨η, hη, hsub, fun s hs s' hs' hss => ?_⟩
  have h1 := (hdesc s hs).2
  have h2 := (hdesc s' hs').2
  have := A.injOn_invFun (hdesc s hs).1 (hdesc s' hs').1 (by rw [← h1, ← h2, hss])
  linarith [this]

end IsUnitSpeedCurveOn

/-! ### The basic examples: an arc, a translate, a reversal -/

variable {L : LengthElement I ∞ M}

/-- **A unit-speed arc, shifted, is a unit-speed curve** on the shifted target.  This is the local
model that the definition of `IsUnitSpeedCurveOn` refers to, packaged as an instance of it; the
target has to be open, which on a boundaryless manifold it is. -/
theorem isUnitSpeedCurveOn_arc (hb : I.boundary M = ∅) {A : SmoothArc I ∞ M}
    (hA : UnitSpeed L A) (k : ℝ) :
    IsUnitSpeedCurveOn L (fun s => A.invFun (s - k)) {s | s - k ∈ A.target} := by
  have hopen : IsOpen {s : ℝ | s - k ∈ A.target} :=
    (A.isOpen_target hb).preimage (continuous_id.sub continuous_const)
  intro t ht
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hopen t ht
  have hIoo : Ioo (t - η) (t + η) ⊆ {s : ℝ | s - k ∈ A.target} := by
    intro s hs
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  exact ⟨A, k, η, hA, hη, hIoo, fun s hs => ⟨hIoo hs, rfl⟩⟩

/-- **A unit-speed curve translated in time is a unit-speed curve.** -/
theorem IsUnitSpeedCurveOn.comp_add {γ : ℝ → M} {U : Set ℝ} (h : IsUnitSpeedCurveOn L γ U)
    (c : ℝ) : IsUnitSpeedCurveOn L (fun s => γ (s + c)) {s | s + c ∈ U} := by
  intro t ht
  obtain ⟨A, k, η, hA, hη, hsub, hdesc⟩ := h (t + c) ht
  refine ⟨A, k - c, η, hA, hη,
    fun s hs => hsub ⟨by linarith [hs.1], by linarith [hs.2]⟩, fun s hs => ?_⟩
  have hmem : s + c ∈ Ioo (t + c - η) (t + c + η) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have heq : s - (k - c) = s + c - k := by ring
  rw [heq]
  exact hdesc _ hmem

/-- **A unit-speed curve run backwards is a unit-speed curve.**  The arc's coordinate is negated
(`SmoothArc.neg`), and unit speed survives that by Stage 5's `UnitSpeed.neg`. -/
theorem IsUnitSpeedCurveOn.comp_neg {γ : ℝ → M} {U : Set ℝ} (h : IsUnitSpeedCurveOn L γ U) :
    IsUnitSpeedCurveOn L (fun s => γ (-s)) {s | -s ∈ U} := by
  intro t ht
  obtain ⟨A, k, η, hA, hη, hsub, hdesc⟩ := h (-t) ht
  refine ⟨A.neg, -k, η, hA.neg, hη,
    fun s hs => hsub ⟨by linarith [hs.2], by linarith [hs.1]⟩, fun s hs => ?_⟩
  have hmem : -s ∈ Ioo (-t - η) (-t + η) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  obtain ⟨h1, h2⟩ := hdesc _ hmem
  have heq : -(s - -k) = -s - k := by ring
  refine ⟨?_, ?_⟩
  · show s - -k ∈ -A.target
    rw [Set.mem_neg, heq]
    exact h1
  · show γ (-s) = A.invFun (-(s - -k))
    rw [heq]
    exact h2

/-- A unit-speed curve on the whole line, translated in time, is again one. -/
theorem IsUnitSpeedCurveOn.comp_add_univ {γ : ℝ → M} (h : IsUnitSpeedCurveOn L γ univ) (c : ℝ) :
    IsUnitSpeedCurveOn L (fun s => γ (s + c)) univ := by
  have h' := h.comp_add c
  simpa using h'

/-- A unit-speed curve on the whole line, reversed, is again one. -/
theorem IsUnitSpeedCurveOn.comp_neg_univ {γ : ℝ → M} (h : IsUnitSpeedCurveOn L γ univ) :
    IsUnitSpeedCurveOn L (fun s => γ (-s)) univ := by
  have h' := h.comp_neg
  simpa using h'

/-- A unit-speed curve is continuous. -/
theorem IsUnitSpeedCurveOn.continuous {γ : ℝ → M} (h : IsUnitSpeedCurveOn L γ univ) :
    Continuous γ :=
  continuous_iff_continuousAt.2 fun t => h.continuousAt (mem_univ t)

/-- Two sets of times both serve the same curve; used to glue a curve to an arc beyond the end of
its interval. -/
theorem IsUnitSpeedCurveOn.union {γ : ℝ → M} {U₁ U₂ : Set ℝ} (h₁ : IsUnitSpeedCurveOn L γ U₁)
    (h₂ : IsUnitSpeedCurveOn L γ U₂) : IsUnitSpeedCurveOn L γ (U₁ ∪ U₂) := by
  intro t ht
  rcases ht with ht | ht
  · obtain ⟨A, k, η, hA, hη, hsub, hdesc⟩ := h₁ t ht
    exact ⟨A, k, η, hA, hη, hsub.trans subset_union_left, hdesc⟩
  · obtain ⟨A, k, η, hA, hη, hsub, hdesc⟩ := h₂ t ht
    exact ⟨A, k, η, hA, hη, hsub.trans subset_union_right, hdesc⟩

/-- The times at which a shifted arc parametrization is defined form an interval. -/
theorem ordConnected_shift (A : SmoothArc I ∞ M) (u : ℝ) :
    {s : ℝ | s - u ∈ A.target}.OrdConnected := by
  constructor
  intro a ha b hb c hc
  exact A.ordConnected_target.out ha hb ⟨by linarith [hc.1], by linarith [hc.2]⟩

/-- The times at which a shifted arc parametrization is defined, when the arc's target is
`Ioo (-ε) ε`. -/
theorem shift_eq_Ioo {A : SmoothArc I ∞ M} {ε : ℝ} (hA : A.target = Ioo (-ε) ε) (u : ℝ) :
    {s : ℝ | s - u ∈ A.target} = Ioo (u - ε) (u + ε) := by
  ext s
  simp only [hA, mem_Ioo, Set.mem_ofPred_eq]
  constructor
  · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩

end Curves

/-! ## The propagation lemma -/

section Rigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {L : LengthElement I ∞ M}

/-- **A transition of unit-speed arcs that is `v ↦ v + m` at two parameters of a connected piece of
the overlap is `v ↦ v + m` on the whole piece.**

By the affine half of Milnor's Lemma 1 (Stage 5's `exists_affine_trans`) the transition is
`v ↦ ε v + k` there with `ε = ±1`; two coincidences with `v ↦ v + m` force `ε = 1` and `k = m`.
This is the rigidity that makes a local agreement of two unit-speed curves spread out. -/
theorem trans_eq_add_of_two_points {A A' : SmoothArc I ∞ M} (hA : UnitSpeed L A)
    (hA' : UnitSpeed L A') {C : Set ℝ} (hCsub : C ⊆ A.target ∩ A.invFun ⁻¹' A'.source)
    (hCoc : C.OrdConnected) {m v₁ v₂ : ℝ} (hv₁ : v₁ ∈ C) (hv₂ : v₂ ∈ C) (hne : v₁ ≠ v₂)
    (he₁ : A'.toFun (A.invFun v₁) = v₁ + m) (he₂ : A'.toFun (A.invFun v₂) = v₂ + m) :
    ∀ v ∈ C, A'.toFun (A.invFun v) = v + m := by
  obtain ⟨ε, k, hε, haff⟩ := exists_affine_trans hA hA' hCsub hCoc
  have h1 : v₁ + m = ε * v₁ + k := by rw [← he₁]; exact haff v₁ hv₁
  have h2 : v₂ + m = ε * v₂ + k := by rw [← he₂]; exact haff v₂ hv₂
  have hzero : (ε - 1) * (v₁ - v₂) = 0 := by linear_combination h2 - h1
  have hεone : ε = 1 := by
    rcases mul_eq_zero.1 hzero with h | h
    · linarith
    · exact absurd (by linarith : v₁ = v₂) hne
  have hkm : k = m := by rw [hεone] at h1; linarith
  intro v hv
  rw [haff v hv, hεone, hkm, one_mul]

end Rigidity

/-! ## The propagation lemma -/

section Propagation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {L : LengthElement I ∞ M}

/-- **The propagation lemma: two unit-speed curves that agree near one time agree at every time.**

Let `γ₁` and `γ₂` be unit-speed curves on the same *interval* `U` of times (order-connectedness is
what makes the argument possible; `U` is automatically open).  If they agree on a neighbourhood of
one time of `U`, they agree on all of `U`.

This is the engine of Stage 7 and replaces the uniqueness theorem for integral curves that Mathlib
proves only for manifolds without boundary and only for genuine flows.  The proof is a connectedness
argument run in the *parameter* of one arc rather than in the time, because the set of times where
the two curves agree *on a neighbourhood* is not obviously closed: the difficulty is exactly that
the overlap of two arcs can have two components, and it is resolved by pushing the argument into a
single component -- a `hull` -- where `trans_eq_add_of_two_points` applies.  In detail: with `A₁, k₁`
and `A₂, k₂` the local descriptions at a limit time `t*`, the set

  `D = {u | A₁.invFun u ∈ A₂.source ∧ A₂.toFun (A₁.invFun u) = u + k₁ - k₂}`

is *closed* in the parameter interval, by continuity of the two parametrizations and uniqueness of
limits in a Hausdorff space; and the set of points having a whole neighbourhood in `D` is closed
there too, because at a limit point the hull of the overlap is a relative neighbourhood on which the
transition is affine and pinned down by two coincidences.  Being open, nonempty and closed in an
interval, it is everything.

Hypotheses: `T2Space M`, for uniqueness of limits, and nothing else -- no compactness, no dimension
hypothesis, no boundarylessness and no connectedness of `M`.  (Boundarylessness is needed to *supply*
unit-speed curves, since it is what makes an arc's target open, but not to propagate them.) -/
theorem eqOn_of_eventuallyEq {γ₁ γ₂ : ℝ → M} {U : Set ℝ}
    (hU : U.OrdConnected) (h₁ : IsUnitSpeedCurveOn L γ₁ U) (h₂ : IsUnitSpeedCurveOn L γ₂ U)
    {t₀ : ℝ} (ht₀ : t₀ ∈ U) (hloc : γ₁ =ᶠ[𝓝 t₀] γ₂) : EqOn γ₁ γ₂ U := by
  set V := {t : ℝ | γ₁ =ᶠ[𝓝 t] γ₂} with hVdef
  have hVopen : IsOpen V := isOpen_setOfPred_eventually_nhds
  have key : closure V ∩ U ⊆ V := by
    rintro ts ⟨htcl, htU⟩
    obtain ⟨A₁, k₁, η₁, hA₁, hη₁, -, hdesc₁⟩ := h₁ ts htU
    obtain ⟨A₂, k₂, η₂, hA₂, hη₂, -, hdesc₂⟩ := h₂ ts htU
    set η := min η₁ η₂ with hηdef
    have hη : 0 < η := lt_min hη₁ hη₂
    have hIoo₁ : Ioo (ts - η) (ts + η) ⊆ Ioo (ts - η₁) (ts + η₁) := fun s hs =>
      ⟨by linarith [hs.1, min_le_left η₁ η₂], by linarith [hs.2, min_le_left η₁ η₂]⟩
    have hIoo₂ : Ioo (ts - η) (ts + η) ⊆ Ioo (ts - η₂) (ts + η₂) := fun s hs =>
      ⟨by linarith [hs.1, min_le_right η₁ η₂], by linarith [hs.2, min_le_right η₁ η₂]⟩
    -- the parameter interval of the first arc
    set P := Ioo (ts - η - k₁) (ts + η - k₁) with hPdef
    have hPmem : ∀ {u : ℝ}, u ∈ P → u + k₁ ∈ Ioo (ts - η) (ts + η) := fun {u} hu =>
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hPtgt : ∀ {u : ℝ}, u ∈ P → u ∈ A₁.target := fun {u} hu => by
      have := (hdesc₁ _ (hIoo₁ (hPmem hu))).1
      simpa using this
    have hPtgt₂ : ∀ {u : ℝ}, u ∈ P → u + k₁ - k₂ ∈ A₂.target := fun {u} hu => by
      have := (hdesc₂ _ (hIoo₂ (hPmem hu))).1
      simpa using this
    -- `D`: the parameters at which the first arc's point lies on the second, with matching shift
    set D : Set ℝ :=
      {u | u ∈ P ∧ A₁.invFun u ∈ A₂.source ∧ A₂.toFun (A₁.invFun u) = u + k₁ - k₂} with hDdef
    have hDP : D ⊆ P := fun u hu => hu.1
    -- `D` is closed in `P`
    have hDclosed : P ∩ closure D ⊆ D := by
      rintro us ⟨hus, hcl⟩
      have : (𝓝[D] us).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
      have hf : Tendsto A₁.invFun (𝓝[D] us) (𝓝 (A₁.invFun us)) :=
        (A₁.continuousOn_invFun us (hPtgt hus)).tendsto.mono_left
          (nhdsWithin_mono _ fun v hv => hPtgt (hDP hv))
      have hshift : Tendsto (fun v : ℝ => v + k₁ - k₂) (𝓝[D] us)
          (𝓝[A₂.target] (us + k₁ - k₂)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨Tendsto.mono_left
          ((continuous_id.add continuous_const).sub continuous_const).continuousAt
          nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with v hv using hPtgt₂ (hDP hv)
      have hg : Tendsto (fun v : ℝ => A₂.invFun (v + k₁ - k₂)) (𝓝[D] us)
          (𝓝 (A₂.invFun (us + k₁ - k₂))) :=
        (A₂.continuousOn_invFun _ (hPtgt₂ hus)).tendsto.comp hshift
      have heq : ∀ v ∈ D, A₁.invFun v = A₂.invFun (v + k₁ - k₂) := fun v hv => by
        conv_lhs => rw [← A₂.left_inv hv.2.1, hv.2.2]
      have hg' : Tendsto A₁.invFun (𝓝[D] us) (𝓝 (A₂.invFun (us + k₁ - k₂))) :=
        hg.congr' (by filter_upwards [self_mem_nhdsWithin] with v hv using (heq v hv).symm)
      have hkey : A₁.invFun us = A₂.invFun (us + k₁ - k₂) := tendsto_nhds_unique hf hg'
      refine ⟨hus, ?_, ?_⟩
      · rw [hkey]; exact A₂.map_target (hPtgt₂ hus)
      · rw [hkey, A₂.right_inv (hPtgt₂ hus)]
    -- `D'`: the parameters with a whole neighbourhood inside `D`
    set D' : Set ℝ := {u | ∃ δ > 0, Ioo (u - δ) (u + δ) ⊆ D} with hD'def
    have hD'D : D' ⊆ D := by
      rintro u ⟨δ, hδ, hsub⟩
      exact hsub ⟨by linarith, by linarith⟩
    have hD'open : IsOpen D' := by
      rw [Metric.isOpen_iff]
      rintro u ⟨δ, hδ, hsub⟩
      refine ⟨δ / 2, by linarith, fun v hv => ⟨δ / 2, by linarith, fun w hw => hsub ?_⟩⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hv
      exact ⟨by linarith [hw.1, hv.1], by linarith [hw.2, hv.2]⟩
    -- `D'` is nonempty: near a time where the two curves already agree
    have hD'ne : (P ∩ D').Nonempty := by
      obtain ⟨s, hsV, hsdist⟩ := Metric.mem_closure_iff.1 htcl η hη
      rw [Real.dist_eq, abs_lt] at hsdist
      obtain ⟨δ₀, hδ₀, hδ₀eq⟩ := Metric.eventually_nhds_iff.1 hsV
      set δ := min δ₀ (min (η - (s - ts)) (η - (ts - s))) with hδdef
      have hδ : 0 < δ := lt_min hδ₀ (lt_min (by linarith [hsdist.2]) (by linarith [hsdist.1]))
      have hmain : ∀ v ∈ Ioo (s - k₁ - δ) (s - k₁ + δ), v ∈ D := by
        intro v hv
        have hvP : v ∈ P := by
          have h1 : δ ≤ η - (s - ts) := le_trans (min_le_right _ _) (min_le_left _ _)
          have h2 : δ ≤ η - (ts - s) := le_trans (min_le_right _ _) (min_le_right _ _)
          exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
        have hx : γ₁ (v + k₁) = γ₂ (v + k₁) := by
          refine hδ₀eq ?_
          rw [Real.dist_eq, abs_lt]
          have h1 : δ ≤ δ₀ := min_le_left _ _
          exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
        have e₁ := (hdesc₁ _ (hIoo₁ (hPmem hvP))).2
        have e₂ := (hdesc₂ _ (hIoo₂ (hPmem hvP))).2
        have hvv : A₁.invFun v = A₂.invFun (v + k₁ - k₂) := by
          have : A₁.invFun (v + k₁ - k₁) = A₂.invFun (v + k₁ - k₂) := by rw [← e₁, ← e₂, hx]
          simpa using this
        refine ⟨hvP, ?_, ?_⟩
        · rw [hvv]; exact A₂.map_target (hPtgt₂ hvP)
        · rw [hvv, A₂.right_inv (hPtgt₂ hvP)]
      exact ⟨s - k₁, hmain _ ⟨by linarith, by linarith⟩ |>.1, δ, hδ, hmain⟩
    -- `D'` is closed in `P`
    have hD'cl : closure D' ∩ P ⊆ D' := by
      rintro us ⟨hcl, hus⟩
      have husD : us ∈ D := hDclosed ⟨hus, closure_mono hD'D hcl⟩
      have husS : us ∈ overlap A₁.toArc A₂.toArc :=
        ⟨A₁.invFun us, ⟨A₁.map_target (hPtgt hus), husD.2.1⟩, A₁.right_inv (hPtgt hus)⟩
      obtain ⟨W, hW, hSW⟩ := overlap_relOpen A₁.toArc A₂.toArc
      obtain ⟨ε, hε, hballC⟩ :=
        hull_relOpen hW hSW A₁.ordConnected_target (mem_hull_self husS)
      set C := hull (overlap A₁.toArc A₂.toArc) us with hCdef
      have hCsub : C ⊆ A₁.target ∩ A₁.invFun ⁻¹' A₂.source := by
        rw [← overlap_eq_inter_preimage]; exact hull_subset _ _
      have hCmem : ∀ v ∈ A₁.target, |v - us| < ε → v ∈ C := hballC
      -- a point of `D'` within `ε` of `us`
      obtain ⟨u, huD', hudist⟩ := Metric.mem_closure_iff.1 hcl ε hε
      rw [Real.dist_eq] at hudist
      have hudist' : |u - us| < ε := by rwa [abs_sub_comm] at hudist
      obtain ⟨δ, hδ, hδsub⟩ := huD'
      set δ' := min δ (ε - |u - us|) with hδ'def
      have hδ'pos : 0 < δ' := lt_min hδ (by linarith)
      have hδ'C : ∀ v ∈ Ioo (u - δ') (u + δ'), v ∈ C := by
        intro v hv
        have hvD : v ∈ D := hδsub ⟨by linarith [hv.1, min_le_left δ (ε - |u - us|)],
          by linarith [hv.2, min_le_left δ (ε - |u - us|)]⟩
        refine hCmem v (hPtgt (hDP hvD)) ?_
        have h2 : δ' ≤ ε - |u - us| := min_le_right _ _
        have hvu : |v - u| < δ' := by
          rw [abs_lt]; exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
        calc |v - us| ≤ |v - u| + |u - us| := abs_sub_le v u us
          _ < ε := by linarith
      -- pin the transition down on `C` using two points of `D`
      have hv₁D : u ∈ D := hδsub ⟨by linarith, by linarith⟩
      have hv₂D : u + δ' / 2 ∈ D := hδsub ⟨by linarith [min_le_left δ (ε - |u - us|)],
        by linarith [min_le_left δ (ε - |u - us|)]⟩
      have haffC := trans_eq_add_of_two_points hA₁ hA₂ hCsub
        (hull_ordConnected _ _) (m := k₁ - k₂)
        (hδ'C u ⟨by linarith, by linarith⟩)
        (hδ'C (u + δ' / 2) ⟨by linarith, by linarith⟩)
        (by intro h; linarith [h ▸ (rfl : u + δ' / 2 = u + δ' / 2)])
        (by rw [hv₁D.2.2]; ring) (by rw [hv₂D.2.2]; ring)
      -- hence a whole neighbourhood of `us` lies in `D`
      obtain ⟨δ'', hδ'', hδ''P⟩ := Metric.isOpen_iff.1 isOpen_Ioo us hus
      refine ⟨min δ'' ε, lt_min hδ'' hε, fun v hv => ?_⟩
      have hvP : v ∈ P := by
        refine hδ''P ?_
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [hv.1, min_le_left δ'' ε], by linarith [hv.2, min_le_left δ'' ε]⟩
      have hvC : v ∈ C := by
        refine hCmem v (hPtgt hvP) ?_
        rw [abs_lt]
        exact ⟨by linarith [hv.1, min_le_right δ'' ε], by linarith [hv.2, min_le_right δ'' ε]⟩
      exact ⟨hvP, (hCsub hvC).2, by rw [haffC v hvC]; ring⟩
    -- an interval is connected, so `D'` is everything
    have hPD' : P ⊆ D' :=
      isPreconnected_Ioo.subset_of_closure_inter_subset hD'open hD'ne hD'cl
    obtain ⟨δ, hδ, hδsub⟩ := hPD' (show ts - k₁ ∈ P from ⟨by linarith, by linarith⟩)
    have hmin : 0 < min δ η := lt_min hδ hη
    filter_upwards [Ioo_mem_nhds (show ts - min δ η < ts by linarith)
      (show ts < ts + min δ η by linarith)] with s hs
    have hsP : s - k₁ ∈ Ioo (ts - k₁ - δ) (ts - k₁ + δ) :=
      ⟨by linarith [hs.1, min_le_left δ η], by linarith [hs.2, min_le_left δ η]⟩
    have hsD := hδsub hsP
    have hsη : s ∈ Ioo (ts - η) (ts + η) :=
      ⟨by linarith [hs.1, min_le_right δ η], by linarith [hs.2, min_le_right δ η]⟩
    have e₁ := (hdesc₁ _ (hIoo₁ hsη)).2
    have e₂ := (hdesc₂ _ (hIoo₂ hsη)).2
    have hvv : A₁.invFun (s - k₁) = A₂.invFun (s - k₁ + k₁ - k₂) := by
      conv_lhs => rw [← A₂.left_inv hsD.2.1, hsD.2.2]
    rw [e₁, e₂, hvv]
    congr 1
    ring
  have ht₀V : t₀ ∈ V := hloc
  have hUV : U ⊆ V :=
    hU.isPreconnected.subset_of_closure_inter_subset hVopen ⟨t₀, ht₀, ht₀V⟩ key
  exact fun t ht => (hUV ht).self_of_nhds

end Propagation

/-! ## Local structure of a unit-speed curve -/

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {L : LengthElement I ∞ M}

/-- **A unit-speed curve read in a given arc has slope `±1`.**  If the point `γ t` lies in the
source of a unit-speed arc `B`, then near `t` the curve stays in that source and its `B`-coordinate
is the affine function `s ↦ σ (s - t) + B.toFun (γ t)` with `σ = ±1`.

This is the affine half of Milnor's Lemma 1 transported from arcs to curves: the local description of
`γ` by an arc `A` is compared with `B` on the component -- the `hull` -- of the overlap that contains
the parameter of `γ t`, which by `Milnor.OneManifold.hull_relOpen` is a relative neighbourhood of
that parameter, so the affine formula is available on a whole interval of times. -/
theorem IsUnitSpeedCurveOn.exists_sign {γ : ℝ → M} {U : Set ℝ} (h : IsUnitSpeedCurveOn L γ U)
    {t : ℝ} (ht : t ∈ U) {B : SmoothArc I ∞ M} (hB : UnitSpeed L B) (hmem : γ t ∈ B.source) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ δ > 0, ∀ s ∈ Ioo (t - δ) (t + δ),
      γ s ∈ B.source ∧ B.toFun (γ s) = σ * (s - t) + B.toFun (γ t) := by
  obtain ⟨A, k, η, hA, hη, -, hdesc⟩ := h t ht
  have htmem : t ∈ Ioo (t - η) (t + η) := ⟨by linarith, by linarith⟩
  have htk : t - k ∈ overlap A.toArc B.toArc := by
    refine ⟨A.invFun (t - k), ⟨A.map_target (hdesc t htmem).1, ?_⟩,
      A.right_inv (hdesc t htmem).1⟩
    rw [← (hdesc t htmem).2]; exact hmem
  obtain ⟨W, hW, hSW⟩ := overlap_relOpen A.toArc B.toArc
  obtain ⟨ε, hε, hballC⟩ := hull_relOpen hW hSW A.ordConnected_target (mem_hull_self htk)
  have hCsub : hull (overlap A.toArc B.toArc) (t - k) ⊆ A.target ∩ A.invFun ⁻¹' B.source := by
    rw [← overlap_eq_inter_preimage]; exact hull_subset _ _
  obtain ⟨σ, m, hσ, haff⟩ := exists_affine_trans hA hB hCsub (hull_ordConnected _ _)
  refine ⟨σ, hσ, min η ε, lt_min hη hε, fun s hs => ?_⟩
  have hsη : s ∈ Ioo (t - η) (t + η) :=
    ⟨by linarith [hs.1, min_le_left η ε], by linarith [hs.2, min_le_left η ε]⟩
  have hsC : s - k ∈ hull (overlap A.toArc B.toArc) (t - k) := by
    refine hballC _ (hdesc s hsη).1 ?_
    rw [abs_lt]
    exact ⟨by linarith [hs.1, min_le_right η ε], by linarith [hs.2, min_le_right η ε]⟩
  have hval : B.toFun (γ s) = σ * (s - k) + m := by
    rw [(hdesc s hsη).2]; exact haff _ hsC
  have hvalt : B.toFun (γ t) = σ * (t - k) + m := by
    rw [(hdesc t htmem).2]; exact haff _ (mem_hull_self htk)
  exact ⟨by rw [(hdesc s hsη).2]; exact (hCsub hsC).2, by rw [hval, hvalt]; ring⟩

/-- A unit-speed curve that agrees with a shifted arc parametrization near one time agrees with it
at *every* time where both are defined.  This is the propagation lemma, specialized. -/
theorem eqOn_shift_of_eventuallyEq (hb : I.boundary M = ∅) {γ : ℝ → M} {U : Set ℝ}
    (hU : U.OrdConnected) (h : IsUnitSpeedCurveOn L γ U) {B : SmoothArc I ∞ M}
    (hB : UnitSpeed L B) {u t : ℝ} (ht : t ∈ U) (htB : t - u ∈ B.target)
    (hloc : ∀ᶠ s in 𝓝 t, γ s = B.invFun (s - u)) :
    EqOn γ (fun s => B.invFun (s - u)) (U ∩ {s | s - u ∈ B.target}) := by
  have hWopen : IsOpen {s : ℝ | s - u ∈ B.target} :=
    (B.isOpen_target hb).preimage (continuous_id.sub continuous_const)
  have hUopen : IsOpen U := h.isOpen
  refine eqOn_of_eventuallyEq (hU.inter (ordConnected_shift B u))
    (h.mono (hUopen.inter hWopen) inter_subset_left)
    ((isUnitSpeedCurveOn_arc hb hB u).mono (hUopen.inter hWopen) inter_subset_right)
    (show t ∈ U ∩ {s : ℝ | s - u ∈ B.target} from ⟨ht, htB⟩) hloc

/-- **A unit-speed curve is, wherever it is defined, the parametrization of one whole arc.**

Let `γ` be a unit-speed curve on an interval `U` of times and let `B` be a unit-speed arc with
target `Ioo (-ε) ε` whose source contains `γ t`.  Then, after possibly reversing `B`'s coordinate,
`γ` agrees with the shifted parametrization `s ↦ B'.invFun (s - u)` at every time of `U` in the
interval `Ioo (u - ε) (u + ε)`, where the shift is `u = t - σ B.toFun (γ t)` -- so `|t - u| < ε`, and
`γ u` is the centre `B.invFun 0` of the arc.

The two conclusions are what Stage 7 uses twice over: the shifted parametrization is a unit-speed
curve on a *whole* interval of length `2ε`, which is how a curve is continued beyond the end of its
interval; and `γ u = B.invFun 0`, which is how one finds two times with the same value, hence a
period.  The upgrade from "near `t`" to "on the whole interval" is the propagation lemma; without it
one could only continue the curve by an unknown, possibly shrinking amount. -/
theorem IsUnitSpeedCurveOn.exists_shift (hb : I.boundary M = ∅) {γ : ℝ → M} {U : Set ℝ}
    (hU : U.OrdConnected) (h : IsUnitSpeedCurveOn L γ U) {t : ℝ} (ht : t ∈ U)
    {B : SmoothArc I ∞ M} {ε : ℝ} (hB : UnitSpeed L B) (hBt : B.target = Ioo (-ε) ε)
    (hmem : γ t ∈ B.source) :
    ∃ (B' : SmoothArc I ∞ M) (u : ℝ), UnitSpeed L B' ∧ B'.target = Ioo (-ε) ε ∧
      |t - u| = |B.toFun (γ t)| ∧ B'.invFun 0 = B.invFun 0 ∧
      IsUnitSpeedCurveOn L (fun s => B'.invFun (s - u)) (Ioo (u - ε) (u + ε)) ∧
      EqOn γ (fun s => B'.invFun (s - u)) (U ∩ Ioo (u - ε) (u + ε)) := by
  obtain ⟨σ, hσ, δ, hδ, hloc⟩ := h.exists_sign ht hB hmem
  have hctgt : B.toFun (γ t) ∈ Ioo (-ε) ε := by rw [← hBt]; exact B.map_source hmem
  set c := B.toFun (γ t) with hc
  have hnegt : B.neg.target = Ioo (-ε) ε := by
    rw [SmoothArc.neg_target, hBt]
    ext v
    simp only [Set.mem_neg, mem_Ioo]
    constructor
    · intro hv; exact ⟨by linarith [hv.2], by linarith [hv.1]⟩
    · intro hv; exact ⟨by linarith [hv.2], by linarith [hv.1]⟩
  -- the same bookkeeping serves both signs, so it is done once
  have main : ∀ (B' : SmoothArc I ∞ M) (u : ℝ), UnitSpeed L B' → B'.target = Ioo (-ε) ε →
      |t - u| = |c| → B'.invFun 0 = B.invFun 0 →
      (∀ s ∈ Ioo (t - δ) (t + δ), γ s = B'.invFun (s - u)) →
      ∃ (B'' : SmoothArc I ∞ M) (u' : ℝ), UnitSpeed L B'' ∧ B''.target = Ioo (-ε) ε ∧
        |t - u'| = |c| ∧ B''.invFun 0 = B.invFun 0 ∧
        IsUnitSpeedCurveOn L (fun s => B''.invFun (s - u')) (Ioo (u' - ε) (u' + ε)) ∧
        EqOn γ (fun s => B''.invFun (s - u')) (U ∩ Ioo (u' - ε) (u' + ε)) := by
    intro B' u hB' hB't habs hcent hdesc
    have hWeq : {s : ℝ | s - u ∈ B'.target} = Ioo (u - ε) (u + ε) := shift_eq_Ioo hB't u
    have hcurve : IsUnitSpeedCurveOn L (fun s => B'.invFun (s - u)) (Ioo (u - ε) (u + ε)) := by
      rw [← hWeq]; exact isUnitSpeedCurveOn_arc hb hB' u
    have habs' : |t - u| < ε := by
      rw [habs, abs_lt]
      exact ⟨by linarith [hctgt.1], by linarith [hctgt.2]⟩
    have htB : t - u ∈ B'.target := by
      rw [hB't, mem_Ioo]
      rw [abs_lt] at habs'
      exact ⟨by linarith [habs'.2], by linarith [habs'.1]⟩
    have heq := eqOn_shift_of_eventuallyEq hb hU h hB' ht htB
      (Filter.eventually_iff_exists_mem.2 ⟨Ioo (t - δ) (t + δ),
        Ioo_mem_nhds (by linarith) (by linarith), hdesc⟩)
    refine ⟨B', u, hB', hB't, habs, hcent, hcurve, ?_⟩
    rw [← hWeq]; exact heq
  rcases hσ with h1 | h1
  · refine main B (t - c) hB hBt ?_ rfl fun s hs => ?_
    · rw [show t - (t - c) = c by ring]
    · obtain ⟨hsrc, hval⟩ := hloc s hs
      rw [h1, one_mul] at hval
      conv_lhs => rw [← B.left_inv hsrc]
      rw [hval]
      congr 1
      ring
  · refine main B.neg (t + c) hB.neg hnegt ?_ (by simp) fun s hs => ?_
    · rw [show t - (t + c) = -c by ring, abs_neg]
    · obtain ⟨hsrc, hval⟩ := hloc s hs
      show γ s = B.invFun (-(s - (t + c)))
      conv_lhs => rw [← B.left_inv hsrc]
      congr 1
      rw [hval, h1]
      ring

end Local


/-! ## The global unit-speed curve -/

section Global

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

/-- The union of two open intervals meeting in a point is the open interval spanning them. -/
theorem Ioo_union_Ioo_of_mem {a b c d x : ℝ} (h1 : x ∈ Ioo a b) (h2 : x ∈ Ioo c d) :
    Ioo a b ∪ Ioo c d = Ioo (min a c) (max b d) := by
  refine Subset.antisymm (union_subset (Ioo_subset_Ioo (min_le_left _ _) (le_max_left _ _))
    (Ioo_subset_Ioo (min_le_right _ _) (le_max_right _ _))) fun y hy => ?_
  by_contra hcon
  rw [mem_union, not_or] at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at hn1 hn2
  have hmin := hy.1
  have hmax := hy.2
  rcases hn1 with h | h <;> rcases hn2 with h' | h'
  · rcases le_total a c with hac | hac
    · rw [min_eq_left hac] at hmin; linarith
    · rw [min_eq_right hac] at hmin; linarith
  · linarith [h1.1, h2.2]
  · linarith [h1.2, h2.1]
  · rcases le_total b d with hbd | hbd
    · rw [max_eq_right hbd] at hmax; linarith
    · rw [max_eq_left hbd] at hmax; linarith

variable {L : LengthElement I ∞ M} {A₀ : SmoothArc I ∞ M}

/-- **`Reach A₀ t x` says that the unit-speed curve issuing from the arc `A₀` reaches `x` at
time `t`.**  Formally: some unit-speed curve, defined on an open interval of times containing `0`
and `t` and agreeing with `A₀.invFun` near `0`, takes the value `x` at `t`.

This is a relation rather than a function because there is no *a priori* curve on all of `ℝ`; the
point of `Reach` is that it is single-valued (`Reach.unique`, from the propagation lemma), so a
function can be extracted from it.  The germ condition pins down the starting point *and the
direction*, which is what makes the value unique: without it the reversed curve would compete. -/
def Reach (L : LengthElement I ∞ M) (A₀ : SmoothArc I ∞ M) (t : ℝ) (x : M) : Prop :=
  ∃ (γ : ℝ → M) (α β : ℝ), α < 0 ∧ 0 < β ∧ IsUnitSpeedCurveOn L γ (Ioo α β) ∧ t ∈ Ioo α β ∧
    γ =ᶠ[𝓝 (0 : ℝ)] A₀.invFun ∧ γ t = x

/-- **A unit-speed curve is determined by its germ at one time**: the relation `Reach` is
single-valued.  Two competing curves are compared on the intersection of their intervals of times,
which is again an interval containing `0`; they agree near `0` because both agree with `A₀.invFun`
there, hence everywhere by the propagation lemma. -/
theorem Reach.unique {t : ℝ} {x y : M} (hx : Reach I L A₀ t x) (hy : Reach I L A₀ t y) : x = y := by
  obtain ⟨γ₁, α₁, β₁, hα₁, hβ₁, hc₁, ht₁, hg₁, hv₁⟩ := hx
  obtain ⟨γ₂, α₂, β₂, hα₂, hβ₂, hc₂, ht₂, hg₂, hv₂⟩ := hy
  have hopen : IsOpen (Ioo α₁ β₁ ∩ Ioo α₂ β₂) := isOpen_Ioo.inter isOpen_Ioo
  have h0 : (0 : ℝ) ∈ Ioo α₁ β₁ ∩ Ioo α₂ β₂ := ⟨⟨hα₁, hβ₁⟩, ⟨hα₂, hβ₂⟩⟩
  have heq := eqOn_of_eventuallyEq (ordConnected_Ioo.inter ordConnected_Ioo)
    (hc₁.mono hopen inter_subset_left) (hc₂.mono hopen inter_subset_right) h0
    (hg₁.trans hg₂.symm)
  rw [← hv₁, ← hv₂]
  exact heq ⟨ht₁, ht₂⟩

/-- **The set of times the curve from `A₀` reaches.** -/
def Dom (L : LengthElement I ∞ M) (A₀ : SmoothArc I ∞ M) : Set ℝ := {t | ∃ x, Reach I L A₀ t x}

/-- **The maximal unit-speed curve issuing from `A₀`**, defined by choosing the unique value that
`Reach` allows, and by an irrelevant default outside `Dom`. -/
def globalCurve (L : LengthElement I ∞ M) (A₀ : SmoothArc I ∞ M) : ℝ → M := fun t =>
  @dite M (∃ x, Reach I L A₀ t x) (Classical.dec _) (fun h => h.choose) fun _ => A₀.invFun 0

omit [T2Space M] in
/-- At a time it reaches, the global curve takes a value that `Reach` allows. -/
theorem reach_globalCurve {t : ℝ} (ht : t ∈ Dom I L A₀) :
    Reach I L A₀ t (globalCurve I L A₀ t) := by
  have hval : globalCurve I L A₀ t = (show ∃ x, Reach I L A₀ t x from ht).choose :=
    dif_pos (show ∃ x, Reach I L A₀ t x from ht)
  rw [hval]
  exact (show ∃ x, Reach I L A₀ t x from ht).choose_spec

/-- **Every unit-speed curve with the right germ is a restriction of the global one.**  Its interval
of times is contained in `Dom`, and it agrees with `globalCurve` there. -/
theorem subset_dom_and_eqOn {γ : ℝ → M} {α β : ℝ} (hα : α < 0) (hβ : 0 < β)
    (hγ : IsUnitSpeedCurveOn L γ (Ioo α β)) (hg : γ =ᶠ[𝓝 (0 : ℝ)] A₀.invFun) :
    Ioo α β ⊆ Dom I L A₀ ∧ EqOn γ (globalCurve I L A₀) (Ioo α β) := by
  have hreach : ∀ t ∈ Ioo α β, Reach I L A₀ t (γ t) := fun t ht =>
    show ∃ (g : ℝ → M) (a b : ℝ), a < 0 ∧ 0 < b ∧ IsUnitSpeedCurveOn L g (Ioo a b) ∧ t ∈ Ioo a b ∧
        g =ᶠ[𝓝 (0 : ℝ)] A₀.invFun ∧ g t = γ t from
      ⟨γ, α, β, hα, hβ, hγ, ht, hg, rfl⟩
  refine ⟨fun t ht => ⟨γ t, hreach t ht⟩, fun t ht => ?_⟩
  exact Reach.unique I (hreach t ht) (reach_globalCurve I ⟨γ t, hreach t ht⟩)

/-- **The global curve is a unit-speed curve on `Dom`.** -/
theorem isUnitSpeedCurveOn_globalCurve :
    IsUnitSpeedCurveOn L (globalCurve I L A₀) (Dom I L A₀) := by
  intro t ht
  obtain ⟨x, γ, α, β, hα, hβ, hγ, htβ, hg, -⟩ := ht
  obtain ⟨hsub, heq⟩ := subset_dom_and_eqOn (A₀ := A₀) I hα hβ hγ hg
  obtain ⟨A, k, η, hA, hη, hIoo, hdesc⟩ :=
    (hγ.congr fun s hs => (heq hs).symm) t htβ
  exact ⟨A, k, η, hA, hη, hIoo.trans hsub, hdesc⟩

/-- `Dom` is open. -/
theorem isOpen_dom : IsOpen (Dom I L A₀) := (isUnitSpeedCurveOn_globalCurve I).isOpen

omit [T2Space M] in
/-- **`Dom` is an interval.**  Every witnessing interval contains `0`, so a time between two reached
times lies in the witnessing interval of whichever of the two is on the same side of `0`. -/
theorem ordConnected_dom : (Dom I L A₀).OrdConnected := by
  constructor
  intro a ha b hb t ht
  obtain ⟨x, γ₁, α₁, β₁, hα₁, hβ₁, hc₁, ha₁, hg₁, -⟩ := ha
  obtain ⟨y, γ₂, α₂, β₂, hα₂, hβ₂, hc₂, hb₂, hg₂, -⟩ := hb
  by_cases h0 : (0 : ℝ) ≤ t
  · exact ⟨γ₂ t, γ₂, α₂, β₂, hα₂, hβ₂, hc₂,
      ⟨by linarith [hα₂], by linarith [ht.2, hb₂.2]⟩, hg₂, rfl⟩
  · push Not at h0
    exact ⟨γ₁ t, γ₁, α₁, β₁, hα₁, hβ₁, hc₁,
      ⟨by linarith [ht.1, ha₁.1], by linarith [hβ₁]⟩, hg₁, rfl⟩

/-- `0` is reached, and the global curve starts along `A₀`. -/
theorem zero_mem_dom (hb : I.boundary M = ∅) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hA₀ : UnitSpeed L A₀)
    (hA₀t : A₀.target = Ioo (-ε₀) ε₀) :
    (0 : ℝ) ∈ Dom I L A₀ ∧ globalCurve I L A₀ =ᶠ[𝓝 (0 : ℝ)] A₀.invFun := by
  have hcurve : IsUnitSpeedCurveOn L A₀.invFun (Ioo (-ε₀) ε₀) := by
    have h := isUnitSpeedCurveOn_arc hb hA₀ 0
    rw [shift_eq_Ioo hA₀t 0] at h
    simpa using h
  obtain ⟨hsub, heq⟩ :=
    subset_dom_and_eqOn I (show -ε₀ < 0 by linarith) hε₀ hcurve EventuallyEq.rfl
  refine ⟨hsub ⟨by linarith, hε₀⟩, ?_⟩
  filter_upwards [Ioo_mem_nhds (show -ε₀ < (0 : ℝ) by linarith) hε₀] with s hs
  exact (heq hs).symm

end Global


/-! ## Global existence: the curve is defined on the whole line -/

section Cluster

variable {M : Type*} [TopologicalSpace M] [CompactSpace M]

/-- **A curve into a compact space accumulates along any filter of times.**  There is a point `q`
such that every neighbourhood of `q` is met by the curve at times in every member of the filter.
Applied to the filter of times approaching the end of the curve's interval, this is what lets the
curve be continued; applied to `Filter.atTop`, it is what forces the curve to return. -/
theorem exists_cluster (γ : ℝ → M) (F : Filter ℝ) [F.NeBot] :
    ∃ q : M, ∀ N ∈ 𝓝 q, ∀ S ∈ F, ∃ t ∈ S, γ t ∈ N := by
  obtain ⟨q, hq⟩ := exists_clusterPt_of_compactSpace (Filter.map γ F)
  refine ⟨q, fun N hN S hS => ?_⟩
  have hnb : (𝓝 q ⊓ Filter.map γ F).NeBot := hq
  obtain ⟨x, hxN, t, htS, rfl⟩ : (N ∩ γ '' S).Nonempty :=
    Filter.nonempty_of_mem (Filter.inter_mem_inf hN (Filter.image_mem_map hS))
  exact ⟨t, htS, hxN⟩

end Cluster

section Existence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

include hE

omit [T2Space M] in
/-- **A unit-speed arc centred at any point of a boundaryless one-manifold**, with symmetric open
target.  This is Stage 4's `exists_unitSpeed_of_notMem_boundary`, with the boundary hypothesis
discharged from `I.boundary M = ∅`. -/
theorem exists_unitSpeed_centred (hb : I.boundary M = ∅) (L : LengthElement I ∞ M) (q : M) :
    ∃ (B : SmoothArc I ∞ M) (ε : ℝ), 0 < ε ∧ UnitSpeed L B ∧ q ∈ B.source ∧ B.toFun q = 0 ∧
      B.target = Ioo (-ε) ε := by
  obtain ⟨B, ε, hε, h1, h2, h3, h4⟩ :=
    exists_unitSpeed_of_notMem_boundary I hE L fun h => Set.notMem_empty q (hb.subset h)
  exact ⟨B, ε, hε, h4, h1, h2, h3⟩

variable [CompactSpace M]

/-- **The maximal unit-speed curve runs forever.**  Its set of reached times is not bounded above.

This is the step at which compactness enters.  If the times were bounded above by `βs`, the curve
would accumulate somewhere, at a point `q`; a unit-speed arc `B` of radius `ε` centred at `q` is met
by the curve at a time `t₁` within `ε/4` of `βs` and with `B`-coordinate within `ε/4` of `0`; and
then `IsUnitSpeedCurveOn.exists_shift` identifies the curve, on a *whole* interval of radius `ε`
about a time `u` within `ε/4` of `t₁`, with the parametrization of `B`.  That interval reaches past
`βs`, so gluing produces a curve defined beyond `βs` -- contradicting the definition of `βs`.

The gluing is legitimate precisely because the two descriptions agree on the whole overlap, which is
the propagation lemma; with only a germ one could continue by an unknown, possibly shrinking amount
and never reach past `βs`. -/
theorem not_bddAbove_dom (hb : I.boundary M = ∅) (L : LengthElement I ∞ M)
    {A₀ : SmoothArc I ∞ M} {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hA₀ : UnitSpeed L A₀)
    (hA₀t : A₀.target = Ioo (-ε₀) ε₀) : ¬ BddAbove (Dom I L A₀) := by
  intro hbdd
  obtain ⟨h0, -⟩ := zero_mem_dom I hb hε₀ hA₀ hA₀t
  have hcurve : IsUnitSpeedCurveOn L (globalCurve I L A₀) (Dom I L A₀) :=
    isUnitSpeedCurveOn_globalCurve I
  have hoc : (Dom I L A₀).OrdConnected := ordConnected_dom I
  have hopen : IsOpen (Dom I L A₀) := isOpen_dom I
  have hDne : (Dom I L A₀).Nonempty := ⟨0, h0⟩
  -- the supremum of the reached times is positive, and every earlier positive time is reached
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen 0 h0
  have hrD : r / 2 ∈ Dom I L A₀ := by
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  have hβpos : 0 < sSup (Dom I L A₀) := lt_of_lt_of_le (by linarith) (le_csSup hbdd hrD)
  have hIoo : Ioo 0 (sSup (Dom I L A₀)) ⊆ Dom I L A₀ := by
    intro t ht
    obtain ⟨t', ht'D, htt'⟩ := exists_lt_of_lt_csSup hDne ht.2
    exact hoc.out h0 ht'D ⟨ht.1.le, htt'.le⟩
  -- the curve accumulates as the time approaches the supremum
  have hnb : (𝓝[Ioo 0 (sSup (Dom I L A₀))] sSup (Dom I L A₀)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.1 ?_
    rw [closure_Ioo (ne_of_lt hβpos)]
    exact ⟨hβpos.le, le_refl _⟩
  obtain ⟨q, hq⟩ :=
    exists_cluster (globalCurve I L A₀) (𝓝[Ioo 0 (sSup (Dom I L A₀))] sSup (Dom I L A₀))
  obtain ⟨B, ε, hε, hB, hqB, hq0, hBt⟩ := exists_unitSpeed_centred I hE hb L q
  have hNopen : IsOpen (B.source ∩ B.toFun ⁻¹' Ioo (-(ε / 4)) (ε / 4)) :=
    B.continuousOn_toFun.isOpen_inter_preimage B.open_source isOpen_Ioo
  have hqN : q ∈ B.source ∩ B.toFun ⁻¹' Ioo (-(ε / 4)) (ε / 4) :=
    ⟨hqB, by rw [Set.mem_preimage, hq0]; exact ⟨by linarith, by linarith⟩⟩
  obtain ⟨t₁, ht₁S, ht₁N⟩ := hq _ (hNopen.mem_nhds hqN) _
    (inter_mem_nhdsWithin (Ioo 0 (sSup (Dom I L A₀)))
      (Ioo_mem_nhds (show sSup (Dom I L A₀) - ε / 4 < sSup (Dom I L A₀) by linarith)
        (show sSup (Dom I L A₀) < sSup (Dom I L A₀) + 1 by linarith)))
  -- the curve, near `t₁`, is the parametrization of `B` on a whole interval of radius `ε`
  obtain ⟨γ₁, α₁, β₁, hα₁, hβ₁, hc₁, ht₁β, hg₁, hv₁⟩ := reach_globalCurve I (hIoo ht₁S.1)
  have hmemB : γ₁ t₁ ∈ B.source := by rw [hv₁]; exact ht₁N.1
  obtain ⟨B', u, hB', hB't, habs, -, hcurve', heq'⟩ :=
    IsUnitSpeedCurveOn.exists_shift hb ordConnected_Ioo hc₁ ht₁β hB hBt hmemB
  have habs' : |t₁ - u| < ε / 4 := by
    rw [habs, hv₁, abs_lt]
    exact ⟨by linarith [ht₁N.2.1], by linarith [ht₁N.2.2]⟩
  rw [abs_lt] at habs'
  have ht₁u : t₁ ∈ Ioo (u - ε) (u + ε) := ⟨by linarith [habs'.2], by linarith [habs'.1]⟩
  -- glue, and reach past the supremum
  have h2₁ : IsUnitSpeedCurveOn L
      (fun s => if s ∈ Ioo α₁ β₁ then γ₁ s else B'.invFun (s - u)) (Ioo α₁ β₁) :=
    hc₁.congr fun s hs => if_pos hs
  have h2₂ : IsUnitSpeedCurveOn L
      (fun s => if s ∈ Ioo α₁ β₁ then γ₁ s else B'.invFun (s - u)) (Ioo (u - ε) (u + ε)) := by
    refine hcurve'.congr fun s hs => ?_
    by_cases hmem : s ∈ Ioo α₁ β₁
    · rw [if_pos hmem]; exact heq' ⟨hmem, hs⟩
    · rw [if_neg hmem]
  have hunion := h2₁.union h2₂
  rw [Ioo_union_Ioo_of_mem ht₁β ht₁u] at hunion
  have hgerm₂ : (fun s => if s ∈ Ioo α₁ β₁ then γ₁ s else B'.invFun (s - u)) =ᶠ[𝓝 (0 : ℝ)]
      A₀.invFun := by
    refine Filter.EventuallyEq.trans ?_ hg₁
    filter_upwards [Ioo_mem_nhds hα₁ hβ₁] with s hs using if_pos hs
  obtain ⟨hsub, -⟩ := subset_dom_and_eqOn (A₀ := A₀) I
    (lt_of_le_of_lt (min_le_left α₁ (u - ε)) hα₁)
    (lt_of_lt_of_le hβ₁ (le_max_left β₁ (u + ε))) hunion hgerm₂
  have hub : sSup (Dom I L A₀) < u + ε := by linarith [ht₁S.1.2, ht₁S.2.1]
  have hmax : sSup (Dom I L A₀) < max β₁ (u + ε) := lt_of_lt_of_le hub (le_max_right _ _)
  have hmem₂ : (sSup (Dom I L A₀) + max β₁ (u + ε)) / 2 ∈
      Ioo (min α₁ (u - ε)) (max β₁ (u + ε)) := by
    refine ⟨?_, by linarith⟩
    have : min α₁ (u - ε) < 0 := lt_of_le_of_lt (min_le_left α₁ (u - ε)) hα₁
    linarith
  have := le_csSup hbdd (hsub hmem₂)
  linarith

/-- **The maximal unit-speed curve is defined at every time.**  Combining `not_bddAbove_dom` with
its mirror image -- obtained by applying the same theorem to the reversed arc `A₀.neg`, whose reached
times are the negatives of `A₀`'s -- the interval of reached times is unbounded in both directions,
hence all of `ℝ`. -/
theorem dom_eq_univ (hb : I.boundary M = ∅) (L : LengthElement I ∞ M)
    {A₀ : SmoothArc I ∞ M} {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hA₀ : UnitSpeed L A₀)
    (hA₀t : A₀.target = Ioo (-ε₀) ε₀) : Dom I L A₀ = univ := by
  obtain ⟨h0, -⟩ := zero_mem_dom I hb hε₀ hA₀ hA₀t
  have hoc : (Dom I L A₀).OrdConnected := ordConnected_dom I
  have hup : ¬ BddAbove (Dom I L A₀) := not_bddAbove_dom I hE hb L hε₀ hA₀ hA₀t
  -- the reversed arc reaches the negatives of the times `A₀` reaches
  have hnegt : A₀.neg.target = Ioo (-ε₀) ε₀ := by
    rw [SmoothArc.neg_target, hA₀t]
    ext v
    simp only [Set.mem_neg, mem_Ioo]
    exact ⟨fun hv => ⟨by linarith [hv.2], by linarith [hv.1]⟩,
      fun hv => ⟨by linarith [hv.2], by linarith [hv.1]⟩⟩
  have hrev : Dom I L A₀.neg ⊆ -Dom I L A₀ := by
    rintro t ⟨x, γ, α, β, hα, hβ, hc, htβ, hg, hv⟩
    rw [Set.mem_neg]
    have hset : {s : ℝ | -s ∈ Ioo α β} = Ioo (-β) (-α) := by
      ext s
      simp only [mem_Ioo, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨by linarith [h.2], by linarith [h.1]⟩,
        fun h => ⟨by linarith [h.2], by linarith [h.1]⟩⟩
    have hcneg : IsUnitSpeedCurveOn L (fun s => γ (-s)) (Ioo (-β) (-α)) := by
      have h := hc.comp_neg
      rwa [hset] at h
    refine ⟨x, fun s => γ (-s), -β, -α, by linarith, by linarith, hcneg,
      ⟨by linarith [htβ.2], by linarith [htβ.1]⟩, ?_, by simpa using hv⟩
    have hcont : Filter.Tendsto (fun s : ℝ => -s) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using continuous_neg.tendsto (0 : ℝ)
    have h2 : ∀ᶠ s in 𝓝 (0 : ℝ), γ (-s) = A₀.neg.invFun (-s) := hcont.eventually hg
    filter_upwards [h2] with s hs
    rw [hs]
    show A₀.invFun (-(-s)) = A₀.invFun s
    rw [neg_neg]
  have hdown : ¬ BddBelow (Dom I L A₀) := by
    intro hbdd
    exact not_bddAbove_dom I hE hb L hε₀ hA₀.neg hnegt
      ((bddAbove_neg.2 hbdd).mono hrev)
  refine eq_univ_of_forall fun t => ?_
  obtain ⟨a, haD, hat⟩ : ∃ a ∈ Dom I L A₀, t < a := by
    by_contra hcon
    push Not at hcon
    exact hup ⟨t, fun a ha => hcon a ha⟩
  obtain ⟨b, hbD, hbt⟩ : ∃ b ∈ Dom I L A₀, b < t := by
    by_contra hcon
    push Not at hcon
    exact hdown ⟨t, fun b hb => hcon b hb⟩
  exact hoc.out hbD haD ⟨hbt.le, hat.le⟩

end Existence


/-! ## The period -/

section Period

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {L : LengthElement I ∞ M}

include hE

/-- **Two times with the same value produce a period.**  This is Milnor's Step 5 in its sharpest
form.  Let `γ` be a unit-speed curve on the whole line and suppose `γ t₁ = γ t₂`.  Read in a
unit-speed arc `B` centred at that common value, the curve has slope `σ₁ = ±1` near `t₁` and
`σ₂ = ±1` near `t₂`.

* If `σ₁ = σ₂` then `γ (t₁ + w) = γ (t₂ + w)` for small `w`, so `γ` and `γ (· + (t₂ - t₁))` agree
  near `t₁`, hence everywhere by the propagation lemma: `t₂ - t₁` is a period.
* If `σ₁ = -σ₂` the curve would have to *reflect*: `γ` and `γ (t₁ + t₂ - ·)` would agree near `t₁`,
  hence everywhere, giving `γ (m + w) = γ (m - w)` about the midpoint `m`, which contradicts the
  local injectivity of a unit-speed curve.

So **the two slopes must agree** -- the geometric fact that the plan singles out as the one part of
Milnor's Step 5 with no counterpart in the existing topological file -- and the period follows. -/
theorem periodic_of_eq (hb : I.boundary M = ∅) {γ : ℝ → M} (hγ : IsUnitSpeedCurveOn L γ univ)
    {t₁ t₂ : ℝ} (heq : γ t₁ = γ t₂) : Function.Periodic γ (t₂ - t₁) := by
  obtain ⟨B, ε, hε, hB, hqB, hq0, hBt⟩ := exists_unitSpeed_centred I hE hb L (γ t₁)
  obtain ⟨σ₁, hσ₁, δ₁, hδ₁, hloc₁⟩ := hγ.exists_sign (mem_univ t₁) hB hqB
  obtain ⟨σ₂, hσ₂, δ₂, hδ₂, hloc₂⟩ := hγ.exists_sign (mem_univ t₂) hB (by rw [← heq]; exact hqB)
  have hq0' : B.toFun (γ t₂) = 0 := by rw [← heq]; exact hq0
  set δ := min δ₁ δ₂ with hδdef
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  by_cases hsign : σ₁ = σ₂
  · -- the slopes agree: the difference of the two times is a period
    have hagree : ∀ w, |w| < δ → γ (t₁ + w) = γ (t₂ + w) := by
      intro w hw
      rw [abs_lt] at hw
      have h1 := hloc₁ (t₁ + w) ⟨by linarith [hw.1, min_le_left δ₁ δ₂],
        by linarith [hw.2, min_le_left δ₁ δ₂]⟩
      have h2 := hloc₂ (t₂ + w) ⟨by linarith [hw.1, min_le_right δ₁ δ₂],
        by linarith [hw.2, min_le_right δ₁ δ₂]⟩
      refine B.injOn h1.1 h2.1 ?_
      rw [h1.2, h2.2, hq0, hq0', hsign]
      ring
    have hcurve₂ : IsUnitSpeedCurveOn L (fun s => γ (s + (t₂ - t₁))) univ :=
      hγ.comp_add_univ (t₂ - t₁)
    have hlocal : γ =ᶠ[𝓝 t₁] fun s => γ (s + (t₂ - t₁)) := by
      filter_upwards [Ioo_mem_nhds (show t₁ - δ < t₁ by linarith)
        (show t₁ < t₁ + δ by linarith)] with s hs
      have hw : |s - t₁| < δ := by rw [abs_lt]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have h := hagree (s - t₁) hw
      have e1 : t₁ + (s - t₁) = s := by ring
      have e2 : t₂ + (s - t₁) = s + (t₂ - t₁) := by ring
      rw [e1, e2] at h
      exact h
    intro x
    have := eqOn_of_eventuallyEq ordConnected_univ hγ hcurve₂ (mem_univ t₁) hlocal (mem_univ x)
    exact this.symm
  · -- the slopes disagree: the curve would reflect, contradicting local injectivity
    exfalso
    have hopp : σ₂ = -σ₁ := by
      rcases hσ₁ with h | h <;> rcases hσ₂ with h' | h'
      · exact absurd (h.trans h'.symm) hsign
      · rw [h', h]
      · rw [h', h]; norm_num
      · exact absurd (h.trans h'.symm) hsign
    have hagree : ∀ w, |w| < δ → γ (t₁ + w) = γ (t₂ - w) := by
      intro w hw
      rw [abs_lt] at hw
      have h1 := hloc₁ (t₁ + w) ⟨by linarith [hw.1, min_le_left δ₁ δ₂],
        by linarith [hw.2, min_le_left δ₁ δ₂]⟩
      have h2 := hloc₂ (t₂ - w) ⟨by linarith [hw.2, min_le_right δ₁ δ₂],
        by linarith [hw.1, min_le_right δ₁ δ₂]⟩
      refine B.injOn h1.1 h2.1 ?_
      rw [h1.2, h2.2, hq0, hq0', hopp]
      ring
    have hcurve₂ : IsUnitSpeedCurveOn L (fun s => γ (-s + (t₁ + t₂))) univ := by
      have h := (hγ.comp_neg_univ).comp_add_univ (-(t₁ + t₂))
      refine h.congr fun s _ => ?_
      show γ (-s + (t₁ + t₂)) = γ (-(s + -(t₁ + t₂)))
      rw [show -(s + -(t₁ + t₂)) = -s + (t₁ + t₂) from by ring]
    have hlocal : γ =ᶠ[𝓝 t₁] fun s => γ (-s + (t₁ + t₂)) := by
      filter_upwards [Ioo_mem_nhds (show t₁ - δ < t₁ by linarith)
        (show t₁ < t₁ + δ by linarith)] with s hs
      have hw : |s - t₁| < δ := by rw [abs_lt]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have h := hagree (s - t₁) hw
      have hs1 : t₁ + (s - t₁) = s := by ring
      have hs2 : t₂ - (s - t₁) = -s + (t₁ + t₂) := by ring
      rw [hs1, hs2] at h
      exact h
    have hrefl := eqOn_of_eventuallyEq ordConnected_univ hγ hcurve₂ (mem_univ t₁) hlocal
    obtain ⟨η, hη, -, hinj⟩ := hγ.exists_injOn (mem_univ ((t₁ + t₂) / 2))
    have hval := hrefl (mem_univ ((t₁ + t₂) / 2 + η / 2))
    have hval' : γ ((t₁ + t₂) / 2 + η / 2) = γ ((t₁ + t₂) / 2 - η / 2) := by
      rw [hval]
      show γ (-((t₁ + t₂) / 2 + η / 2) + (t₁ + t₂)) = γ ((t₁ + t₂) / 2 - η / 2)
      rw [show -((t₁ + t₂) / 2 + η / 2) + (t₁ + t₂) = (t₁ + t₂) / 2 - η / 2 from by ring]
    have h1 : (t₁ + t₂) / 2 + η / 2 ∈ Ioo ((t₁ + t₂) / 2 - η) ((t₁ + t₂) / 2 + η) :=
      ⟨by linarith, by linarith⟩
    have h2 : (t₁ + t₂) / 2 - η / 2 ∈ Ioo ((t₁ + t₂) / 2 - η) ((t₁ + t₂) / 2 + η) :=
      ⟨by linarith, by linarith⟩
    have := hinj h1 h2 hval'
    linarith

variable [CompactSpace M]

/-- **A unit-speed curve on a compact manifold has a positive period.**

Compactness makes the curve accumulate at some point `q` as the time tends to `+∞`
(`exists_cluster`).  Take a unit-speed arc `B` of radius `ε` centred at `q`, and two times `t₁` and
`t₂`, at least `ε` apart, at which the curve lies in `B.source` with `B`-coordinate less than `ε/4`
in absolute value.  By `IsUnitSpeedCurveOn.exists_shift` the curve *passes exactly through* `q`, at
times `u₁` and `u₂` within `ε/4` of `t₁` and `t₂`; those two times are distinct, so `periodic_of_eq`
turns them into a period.  Note that it is the propagation lemma, not a germ argument, that produces
the exact hits `γ u_i = q`. -/
theorem exists_period (hb : I.boundary M = ∅) {γ : ℝ → M} (hγ : IsUnitSpeedCurveOn L γ univ) :
    ∃ T, 0 < T ∧ Function.Periodic γ T := by
  obtain ⟨q, hq⟩ := exists_cluster γ Filter.atTop
  obtain ⟨B, ε, hε, hB, hqB, hq0, hBt⟩ := exists_unitSpeed_centred I hE hb L q
  have hNopen : IsOpen (B.source ∩ B.toFun ⁻¹' Ioo (-(ε / 4)) (ε / 4)) :=
    B.continuousOn_toFun.isOpen_inter_preimage B.open_source isOpen_Ioo
  have hqN : q ∈ B.source ∩ B.toFun ⁻¹' Ioo (-(ε / 4)) (ε / 4) :=
    ⟨hqB, by rw [Set.mem_preimage, hq0]; exact ⟨by linarith, by linarith⟩⟩
  obtain ⟨t₁, -, ht₁N⟩ := hq _ (hNopen.mem_nhds hqN) _ (Filter.Ici_mem_atTop (0 : ℝ))
  obtain ⟨t₂, ht₂ge, ht₂N⟩ := hq _ (hNopen.mem_nhds hqN) _ (Filter.Ici_mem_atTop (t₁ + ε))
  -- the curve passes exactly through `q`, at two distinct times
  have hhit : ∀ t : ℝ, γ t ∈ B.source ∩ B.toFun ⁻¹' Ioo (-(ε / 4)) (ε / 4) →
      ∃ u, |t - u| < ε / 4 ∧ γ u = B.invFun 0 := by
    intro t htN
    obtain ⟨B', u, hB', hB't, habs, hcent, hcurve', heq'⟩ :=
      IsUnitSpeedCurveOn.exists_shift hb ordConnected_univ hγ (mem_univ t) hB hBt htN.1
    refine ⟨u, ?_, ?_⟩
    · rw [habs, abs_lt]
      exact ⟨by linarith [htN.2.1], by linarith [htN.2.2]⟩
    · have := heq' ⟨mem_univ u, ⟨by linarith, by linarith⟩⟩
      rw [this]
      simpa using hcent
  have ht₂ge' : t₁ + ε ≤ t₂ := ht₂ge
  obtain ⟨u₁, hu₁, hv₁⟩ := hhit t₁ ht₁N
  obtain ⟨u₂, hu₂, hv₂⟩ := hhit t₂ ht₂N
  rw [abs_lt] at hu₁ hu₂
  refine ⟨u₂ - u₁, by linarith, periodic_of_eq I hE hb hγ ?_⟩
  rw [hv₁, hv₂]

/-- **The minimal period.**  A unit-speed curve on a compact one-manifold has a least positive
period `T`; every period is an integer multiple of `T`; and the curve is injective on `[0, T)`.

The set of periods is a closed subgroup of the line -- closed because the curve is continuous -- and
it is *discrete*, because a unit-speed curve is injective near every time, so no period can be
smaller than the radius `η` of an interval of injectivity.  Hence the positive periods are exactly
the elements of the closed set `Per ∩ [η, ∞)`, whose infimum therefore belongs to it. -/
theorem exists_minimal_period (hb : I.boundary M = ∅) {γ : ℝ → M}
    (hγ : IsUnitSpeedCurveOn L γ univ) :
    ∃ T, 0 < T ∧ Function.Periodic γ T ∧ (∀ S, Function.Periodic γ S → ∃ n : ℤ, S = n * T) ∧
      InjOn γ (Ico 0 T) := by
  classical
  have hcont : Continuous γ := hγ.continuous
  -- the period set is closed
  have hclosed : IsClosed {T : ℝ | Function.Periodic γ T} := by
    have hset : {T : ℝ | Function.Periodic γ T} = ⋂ x : ℝ, {T : ℝ | γ (x + T) = γ x} := by
      ext T
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      exact ⟨fun h x => h x, fun h x => h x⟩
    rw [hset]
    exact isClosed_iInter fun x =>
      isClosed_eq (hcont.comp (continuous_const.add continuous_id)) continuous_const
  -- no period is smaller than the radius of injectivity at `0`
  obtain ⟨η, hη, -, hinj⟩ := hγ.exists_injOn (mem_univ (0 : ℝ))
  have hlarge : ∀ S, Function.Periodic γ S → 0 < S → η ≤ S := by
    intro S hS hSpos
    by_contra hcon
    push Not at hcon
    have h1 : S ∈ Ioo ((0 : ℝ) - η) (0 + η) := ⟨by linarith, by linarith⟩
    have h2 : (0 : ℝ) ∈ Ioo ((0 : ℝ) - η) (0 + η) := ⟨by linarith, by linarith⟩
    have := hinj h1 h2 (by simpa using hS 0)
    linarith
  -- the positive periods form a closed set bounded below, so they have a least element
  obtain ⟨T₀, hT₀pos, hT₀⟩ := exists_period I hE hb hγ
  have hne : ({T : ℝ | Function.Periodic γ T} ∩ Ici η).Nonempty :=
    ⟨T₀, hT₀, hlarge T₀ hT₀ hT₀pos⟩
  have hbdd : BddBelow ({T : ℝ | Function.Periodic γ T} ∩ Ici η) :=
    ⟨η, fun x hx => hx.2⟩
  obtain ⟨hTper, hTge⟩ : sInf ({T : ℝ | Function.Periodic γ T} ∩ Ici η) ∈
      {T : ℝ | Function.Periodic γ T} ∩ Ici η :=
    (hclosed.inter isClosed_Ici).csInf_mem hne hbdd
  set T := sInf ({T : ℝ | Function.Periodic γ T} ∩ Ici η) with hTdef
  have hTpos : 0 < T := lt_of_lt_of_le hη hTge
  have hmin : ∀ S, Function.Periodic γ S → 0 < S → T ≤ S := fun S hS hSpos =>
    csInf_le hbdd ⟨hS, hlarge S hS hSpos⟩
  refine ⟨T, hTpos, hTper, fun S hS => ?_, fun s hs t ht hst => ?_⟩
  · -- every period is an integer multiple of the least one
    refine ⟨⌊S / T⌋, ?_⟩
    have hr : Function.Periodic γ (S - (⌊S / T⌋ : ℝ) * T) := by
      have h := hS.add_period ((hTper.int_mul (-⌊S / T⌋)))
      have heq : S + ((-⌊S / T⌋ : ℤ) : ℝ) * T = S - (⌊S / T⌋ : ℝ) * T := by push_cast; ring
      rwa [heq] at h
    have h0 : 0 ≤ S - (⌊S / T⌋ : ℝ) * T := Int.sub_floor_div_mul_nonneg S hTpos
    have h1 : S - (⌊S / T⌋ : ℝ) * T < T := Int.sub_floor_div_mul_lt S hTpos
    rcases eq_or_lt_of_le h0 with h | h
    · linarith [h]
    · linarith [hmin _ hr h]
  · -- injectivity on a half-open period
    by_contra hst'
    rcases lt_or_gt_of_ne hst' with hlt | hlt
    · have := hmin _ (periodic_of_eq I hE hb hγ hst) (by linarith)
      linarith [hs.1, ht.2]
    · have := hmin _ (periodic_of_eq I hE hb hγ hst.symm) (by linarith)
      linarith [ht.1, hs.2]

end Period


/-! ## Surjectivity, and the periodic parametrisation -/

section Surjective

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {L : LengthElement I ∞ M}

omit hE [T2Space M] [IsManifold I ∞ M] in
/-- **The image of a unit-speed curve is open**, because the curve is locally the parametrization of
an arc and an arc carries open sets of parameters to open sets of points. -/
theorem IsUnitSpeedCurveOn.isOpen_range (_hb : I.boundary M = ∅) {γ : ℝ → M}
    (h : IsUnitSpeedCurveOn L γ univ) : IsOpen (range γ) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨t, rfl⟩
  obtain ⟨A, k, η, hA, hη, -, hdesc⟩ := h t (mem_univ t)
  have htmem : t ∈ Ioo (t - η) (t + η) := ⟨by linarith, by linarith⟩
  refine ⟨A.invFun '' (Ioo (t - η - k) (t + η - k) ∩ A.target), ?_,
    A.isOpen_image isOpen_Ioo, ?_⟩
  · rintro y ⟨v, ⟨hvV, hvT⟩, rfl⟩
    refine ⟨v + k, ?_⟩
    have hmem : v + k ∈ Ioo (t - η) (t + η) := ⟨by linarith [hvV.1], by linarith [hvV.2]⟩
    rw [(hdesc _ hmem).2]
    congr 1
    ring
  · exact ⟨t - k, ⟨⟨by linarith, by linarith⟩, (hdesc t htmem).1⟩, ((hdesc t htmem).2).symm⟩

omit hE [IsManifold I ∞ M] in
/-- **A periodic unit-speed curve on a connected compact one-manifold is onto.**  Its image is the
image of `[0, T]`, hence compact, hence closed; it is open because the curve is a local
parametrization; so it is a nonempty clopen subset of a preconnected space. -/
theorem surjective_of_periodic [PreconnectedSpace M] [CompactSpace M] (hb : I.boundary M = ∅)
    {γ : ℝ → M} (h : IsUnitSpeedCurveOn L γ univ) {T : ℝ} (hT : 0 < T)
    (hper : Function.Periodic γ T) : Function.Surjective γ := by
  have hrange : range γ = γ '' Icc 0 T := by
    refine Subset.antisymm ?_ (image_subset_range _ _)
    rintro x ⟨s, rfl⟩
    refine ⟨s - (⌊s / T⌋ : ℝ) * T, ⟨Int.sub_floor_div_mul_nonneg s hT,
      (Int.sub_floor_div_mul_lt s hT).le⟩, ?_⟩
    have hp := hper.int_mul ⌊s / T⌋ (s - (⌊s / T⌋ : ℝ) * T)
    rw [show s - (⌊s / T⌋ : ℝ) * T + ((⌊s / T⌋ : ℤ) : ℝ) * T = s by ring] at hp
    exact hp.symm
  have hclosed : IsClosed (range γ) := by
    rw [hrange]; exact (isCompact_Icc.image h.continuous).isClosed
  rcases isClopen_iff.1 ⟨hclosed, h.isOpen_range I hb⟩ with hemp | huniv
  · exact absurd hemp (Set.nonempty_iff_ne_empty.1 ⟨γ 0, mem_range_self 0⟩)
  · intro x
    have hx : x ∈ range γ := by rw [huniv]; exact mem_univ x
    exact hx

include hE

variable [CompactSpace M] [PreconnectedSpace M] [Nonempty M]

/-- **Milnor's periodic parametrisation of a compact boundaryless one-manifold (Appendix, p. 54).**

Let `M` be a compact, Hausdorff, connected, nonempty `C^∞` one-manifold with `I.boundary M = ∅`.
Then there are a length element `L`, a period `T > 0` and a map `γ : ℝ → M` such that

* `γ` is a **unit-speed curve** in the sense of `IsUnitSpeedCurveOn`: near every time it is the
  arc-length parametrization of a smooth arc, so it is smooth and a local diffeomorphism;
* `γ` is **`T`-periodic** and **onto**;
* `γ` is **injective on `[0, T)`**, and `T` is the **least** period: every period is an integer
  multiple of `T`;
* and, sharpest of all, `γ s = γ t` **exactly when** `s - t` is an integer multiple of `T`.

This is the content of Milnor's Step 5, and the statement from which the diffeomorphism with the
circle is read off by descending through the exponential.  It is stated separately because it is the
geometric heart of the argument and is usable on its own: it says that a compact connected
boundaryless one-manifold *is* a closed geodesic of length `T`. -/
theorem exists_periodic_parametrisation (hb : I.boundary M = ∅) :
    ∃ (L : LengthElement I ∞ M) (γ : ℝ → M) (T : ℝ), 0 < T ∧
      IsUnitSpeedCurveOn L γ univ ∧ Function.Periodic γ T ∧ Function.Surjective γ ∧
      InjOn γ (Ico 0 T) ∧ (∀ S, Function.Periodic γ S → ∃ n : ℤ, S = n * T) ∧
      ∀ s t : ℝ, γ s = γ t ↔ ∃ n : ℤ, s - t = n * T := by
  obtain ⟨L⟩ := nonempty_lengthElement I hE M
  obtain ⟨A₀, ε₀, hε₀, hA₀, -, -, hA₀t⟩ :=
    exists_unitSpeed_centred I hE hb L (Classical.arbitrary M)
  have hdom : Dom I L A₀ = univ := dom_eq_univ I hE hb L hε₀ hA₀ hA₀t
  have hγ : IsUnitSpeedCurveOn L (globalCurve I L A₀) univ := by
    have h := isUnitSpeedCurveOn_globalCurve (L := L) (A₀ := A₀) I
    rwa [hdom] at h
  obtain ⟨T, hTpos, hTper, hTmul, hTinj⟩ := exists_minimal_period I hE hb hγ
  refine ⟨L, globalCurve I L A₀, T, hTpos, hγ, hTper,
    surjective_of_periodic I hb hγ hTpos hTper, hTinj, hTmul, fun s t => ⟨fun heq => ?_, ?_⟩⟩
  · obtain ⟨n, hn⟩ := hTmul _ (periodic_of_eq I hE hb hγ heq)
    exact ⟨-n, by push_cast; linarith [hn]⟩
  · rintro ⟨n, hn⟩
    have hp := hTper.int_mul n t
    rw [show t + (n : ℝ) * T = s by linarith [hn]] at hp
    exact hp

end Surjective


/-! ## Descending through the exponential -/

section Descent

/-- **A continuous linear map between one-dimensional modules with a continuous linear left inverse
along one vector is invertible.**  If `v₁` spans the source, `f v₁ ≠ 0` spans the target, and
`g (f v₁) = v₁`, then `g` is a two-sided inverse of `f`, so `f` is a continuous linear equivalence.

The statement is for topological modules rather than normed spaces because the tangent spaces of a
manifold carry no norm in `Mathlib`: `TangentSpace` is a deliberately irreducible type synonym with
only its module and topology. -/
theorem isInvertible_of_finrank_one {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    (hV : Module.finrank ℝ V = 1) (hW : Module.finrank ℝ W = 1) (f : V →L[ℝ] W) (g : W →L[ℝ] V)
    {v₁ : V} (hv₁ : f v₁ ≠ 0) (hgf : g (f v₁) = v₁) :
    (f : V →L[ℝ] W).IsInvertible := by
  have hv₁0 : v₁ ≠ 0 := fun h => hv₁ (by rw [h, map_zero])
  have hVspan := (finrank_eq_one_iff_of_nonzero' v₁ hv₁0).1 hV
  have hWspan := (finrank_eq_one_iff_of_nonzero' (f v₁) hv₁).1 hW
  refine ⟨ContinuousLinearEquiv.equivOfInverse f g ?_ ?_, by ext v; rfl⟩
  · intro v
    obtain ⟨d, hd⟩ := hVspan v
    rw [← hd, map_smul, map_smul, hgf]
  · intro w
    obtain ⟨d, hd⟩ := hWspan w
    rw [← hd, map_smul, map_smul, hgf, hd]

/-- **The circle, run at period `T`**: `t ↦ exp (2π t / T)`, a `T`-periodic parametrization of
`Circle` by the line. -/
def circleParam (T : ℝ) : ℝ → Circle := fun t => Circle.exp (2 * Real.pi / T * t)

/-- **The canonical section of `circleParam`**, built from the principal argument. -/
def circleSection (T : ℝ) : Circle → ℝ := fun z => Complex.arg z * T / (2 * Real.pi)

/-- `circleParam` is `C^∞`: `Mathlib`'s `contMDiff_circleExp` composed with a linear rescaling. -/
theorem contMDiff_circleParam (T : ℝ) : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ (circleParam T) :=
  contMDiff_circleExp.comp ((contDiff_const.mul contDiff_id).contMDiff)

/-- **`circleParam T` identifies exactly the times that differ by a multiple of `T`.**  This is
`Circle.exp_eq_exp` after cancelling the nonzero factor `2π/T`. -/
theorem circleParam_eq_iff {T : ℝ} (hT : 0 < T) {s t : ℝ} :
    circleParam T s = circleParam T t ↔ ∃ n : ℤ, s - t = n * T := by
  have hTne : T ≠ 0 := ne_of_gt hT
  have hc : 2 * Real.pi / T ≠ 0 := by
    refine div_ne_zero ?_ hTne
    positivity
  have hcT : 2 * Real.pi / T * T = 2 * Real.pi := by field_simp
  rw [circleParam, circleParam, Circle.exp_eq_exp]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have e : 2 * Real.pi / T * (t + (m : ℝ) * T) =
        2 * Real.pi / T * t + (m : ℝ) * (2 * Real.pi / T * T) := by ring
    have key : 2 * Real.pi / T * s = 2 * Real.pi / T * (t + (m : ℝ) * T) := by
      rw [e, hcT, hm]
    have := mul_left_cancel₀ hc key
    linarith
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hs : s = t + (n : ℝ) * T := by linarith
    have e : 2 * Real.pi / T * (t + (n : ℝ) * T) =
        2 * Real.pi / T * t + (n : ℝ) * (2 * Real.pi / T * T) := by ring
    rw [hs, e, hcT]

/-- `circleSection` really is a section of `circleParam`. -/
theorem circleParam_circleSection {T : ℝ} (hT : 0 < T) (z : Circle) :
    circleParam T (circleSection T z) = z := by
  have hTne : T ≠ 0 := ne_of_gt hT
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have key : 2 * Real.pi / T * (Complex.arg z * T / (2 * Real.pi)) = Complex.arg z := by
    field_simp
  rw [circleParam, circleSection, key]
  exact Circle.exp_arg z

/-- `circleParam T` is onto, by `circleSection`. -/
theorem circleParam_surjective {T : ℝ} (hT : 0 < T) : Function.Surjective (circleParam T) :=
  fun z => ⟨circleSection T z, circleParam_circleSection hT z⟩

/-- **`circleParam T` is a local diffeomorphism.**

The manifold inverse function theorem -- the project's own
`Milnor.ContMDiff.isLocalDiffeomorphAt_of_isInvertible_mfderiv`, both models here being boundaryless
-- reduces this to invertibility of the derivative.  That is obtained without ever computing a chart
of the circle: the two real coordinate functions `z ↦ (z : ℂ).im` and `z ↦ (z : ℂ).re` are smooth
(`contMDiff_coe_sphere`) and pull back along `circleParam T` to `sin (2π t/T)` and `cos (2π t/T)`,
whose derivatives cannot both vanish since `sin² + cos² = 1`.  Rescaling whichever one is nonzero
produces a smooth `ψ : Circle → ℝ` with `(ψ ∘ circleParam T)' (t) = 1`, and then the chain rule
exhibits `mfderiv ψ` as a continuous linear left inverse of `mfderiv (circleParam T)`; since the
tangent space of the circle is one-dimensional, a left inverse is a two-sided one. -/
theorem isLocalDiffeomorph_circleParam {T : ℝ} (hT : 0 < T) :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞ (circleParam T) := by
  have hfact : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp [Complex.finrank_real_complex]⟩
  intro t
  refine ContMDiff.isLocalDiffeomorphAt_of_isInvertible_mfderiv (contMDiff_circleParam T)
    (by simp) ?_
  set c := 2 * Real.pi / T with hc
  have hcne : c ≠ 0 := by
    refine div_ne_zero ?_ (ne_of_gt hT)
    positivity
  have hmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) (circleParam T) t :=
    (contMDiff_circleParam T).mdifferentiableAt (by simp)
  -- a smooth real function on the circle whose pullback has nonzero derivative at `t`
  have hsin : ∀ s : ℝ, ((circleParam T s : Circle) : ℂ).im = Real.sin (c * s) := fun s => by
    rw [circleParam, Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
  have hcos : ∀ s : ℝ, ((circleParam T s : Circle) : ℂ).re = Real.cos (c * s) := fun s => by
    rw [circleParam, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  have hexists : ∃ (F : Circle → ℝ) (d : ℝ), ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ F ∧
      HasDerivAt (F ∘ circleParam T) d t ∧ d ≠ 0 := by
    by_cases hc0 : Real.cos (c * t) = 0
    · have hs0 : Real.sin (c * t) ≠ 0 := by
        intro h
        have := Real.sin_sq_add_cos_sq (c * t)
        rw [h, hc0] at this
        norm_num at this
      refine ⟨fun z : Circle => (z : ℂ).re, -Real.sin (c * t) * c,
        Complex.reCLM.contDiff.contMDiff.comp contMDiff_coe_sphere, ?_, ?_⟩
      · have hlin : HasDerivAt (fun s : ℝ => c * s) c t := by
          simpa using (hasDerivAt_id t).const_mul c
        refine ((Real.hasDerivAt_cos (c * t)).comp t hlin).congr_of_eventuallyEq ?_
        filter_upwards with s using hcos s
      · simp only [ne_eq, mul_eq_zero, neg_eq_zero]
        exact fun h => h.elim hs0 hcne
    · refine ⟨fun z : Circle => (z : ℂ).im, Real.cos (c * t) * c,
        Complex.imCLM.contDiff.contMDiff.comp contMDiff_coe_sphere, ?_, ?_⟩
      · have hlin : HasDerivAt (fun s : ℝ => c * s) c t := by
          simpa using (hasDerivAt_id t).const_mul c
        refine ((Real.hasDerivAt_sin (c * t)).comp t hlin).congr_of_eventuallyEq ?_
        filter_upwards with s using hsin s
      · simp only [ne_eq, mul_eq_zero]
        exact fun h => h.elim hc0 hcne
  obtain ⟨F, d, hF, hd, hdne⟩ := hexists
  -- rescale so that the pullback has derivative exactly `1`
  set ψ : Circle → ℝ := fun z => (F z - F (circleParam T t)) / d + t with hψ
  have hψsmooth : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ ψ := by
    have h1 : ContDiff ℝ ∞ fun u : ℝ => (u - F (circleParam T t)) / d + t := by
      fun_prop
    exact h1.contMDiff.comp hF
  have hψd : HasDerivAt (ψ ∘ circleParam T) 1 t := by
    have h : HasDerivAt (fun s => ((F ∘ circleParam T) s - F (circleParam T t)) / d + t)
        (d / d) t := by
      simpa using ((hd.sub_const (F (circleParam T t))).div_const d).add_const t
    rw [div_self hdne] at h
    exact h
  have hψdiff : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) ψ (circleParam T t) :=
    hψsmooth.mdifferentiableAt (by simp)
  -- the chain rule turns that into a left inverse of the derivative
  have hchain : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (ψ ∘ circleParam T) t 1 =
      mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ψ (circleParam T t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (circleParam T) t 1) :=
    mfderiv_comp_apply t hψdiff hmdiff 1
  have hone : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (ψ ∘ circleParam T) t 1 = 1 := by
    have hmf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (ψ ∘ circleParam T) t
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (1 : ℝ)) := by
      rw [hasMFDerivAt_iff_hasFDerivAt]; exact hψd
    have hval : (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (1 : ℝ)) (1 : ℝ) = 1 := by simp
    rw [hmf.mfderiv]
    exact hval
  have hgf : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ψ (circleParam T t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (circleParam T) t 1) = 1 := by rw [← hchain, hone]
  have hv1 : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (circleParam T) t 1 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hgf
    have h01 : (0 : ℝ) = (1 : ℝ) := hgf
    exact zero_ne_one h01
  have hVone : Module.finrank ℝ (TangentSpace 𝓘(ℝ, ℝ) t) = 1 := by
    show Module.finrank ℝ ℝ = 1
    exact Module.finrank_self ℝ
  have hWone : Module.finrank ℝ (TangentSpace (𝓡 1) (circleParam T t)) = 1 := by
    show Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1
    rw [finrank_euclideanSpace_fin]
  exact isInvertible_of_finrank_one hVone hWone _
    (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ψ (circleParam T t)) hv1 hgf

end Descent


/-! ## The classification in the compact boundaryless case -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {L : LengthElement I ∞ M}

omit hE [T2Space M] [IsManifold I ∞ M] in
/-- **A local diffeomorphism is recognized from a germ**: a map agreeing near `x` with a local
diffeomorphism at `x` is one.  The partial diffeomorphism is simply cut down to the open set where
the two maps agree. -/
theorem IsLocalDiffeomorphAt.congr_eventuallyEq {E₂ : Type*} [NormedAddCommGroup E₂]
    [NormedSpace ℝ E₂] {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H₂ N] {n : WithTop ℕ∞} {f g : N → M} {x : N}
    (h : IsLocalDiffeomorphAt I₂ I n g x) (heq : f =ᶠ[𝓝 x] g) :
    IsLocalDiffeomorphAt I₂ I n f x := by
  obtain ⟨Φ, hx, hΦ⟩ := h
  obtain ⟨U, hUmem, hUeq⟩ := heq.exists_mem
  obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.1 hUmem
  refine ⟨{ toFun := Φ.toFun
            invFun := Φ.invFun
            source := Φ.source ∩ V
            target := Φ.target ∩ Φ.invFun ⁻¹' V
            map_source' := fun y hy =>
              ⟨Φ.map_source hy.1, show Φ.invFun (Φ.toFun y) ∈ V by
                rw [Φ.left_inv' hy.1]; exact hy.2⟩
            map_target' := fun z hz => ⟨Φ.map_target hz.1, hz.2⟩
            left_inv' := fun y hy => Φ.left_inv hy.1
            right_inv' := fun z hz => Φ.right_inv hz.1
            open_source := Φ.open_source.inter hVopen
            open_target := Φ.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage
              Φ.open_target hVopen
            contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono inter_subset_left
            contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono inter_subset_left },
    ⟨hx, hxV⟩, fun y hy => ?_⟩
  rw [hUeq (hVU hy.2)]
  exact hΦ hy.1

omit hE [T2Space M] [IsManifold I ∞ M] in
/-- **A unit-speed curve is a local diffeomorphism at each of its times.**  On the interval supplied
by the definition it *is* the parametrization of a smooth arc, shifted, whose inverse is the arc's
coordinate shifted back; both are smooth and the source and target are open. -/
theorem IsUnitSpeedCurveOn.isLocalDiffeomorphAt {γ : ℝ → M} {U : Set ℝ}
    (h : IsUnitSpeedCurveOn L γ U) {t : ℝ} (ht : t ∈ U) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) I ∞ γ t := by
  obtain ⟨A, k, η, hA, hη, -, hdesc⟩ := h t ht
  have htmem : t ∈ Ioo (t - η) (t + η) := ⟨by linarith, by linarith⟩
  have hsub : A.invFun '' (Ioo (t - η - k) (t + η - k) ∩ A.target) ⊆ A.source := by
    rintro x ⟨v, ⟨-, hvT⟩, rfl⟩
    exact A.map_target hvT
  refine ⟨{ toFun := γ
            invFun := fun x => A.toFun x + k
            source := Ioo (t - η) (t + η)
            target := A.invFun '' (Ioo (t - η - k) (t + η - k) ∩ A.target)
            map_source' := fun s hs =>
              ⟨s - k, ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, (hdesc s hs).1⟩,
                ((hdesc s hs).2).symm⟩
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            open_source := isOpen_Ioo
            open_target := A.isOpen_image isOpen_Ioo
            contMDiffOn_toFun := ?_
            contMDiffOn_invFun := ?_ }, htmem, fun y _ => rfl⟩
  · rintro x ⟨v, ⟨hvV, hvT⟩, rfl⟩
    rw [A.right_inv hvT]
    exact ⟨by linarith [hvV.1], by linarith [hvV.2]⟩
  · intro s hs
    rw [(hdesc s hs).2, A.right_inv (hdesc s hs).1]
    ring
  · rintro x ⟨v, ⟨hvV, hvT⟩, rfl⟩
    rw [A.right_inv hvT]
    have hmem : v + k ∈ Ioo (t - η) (t + η) := ⟨by linarith [hvV.1], by linarith [hvV.2]⟩
    rw [(hdesc _ hmem).2]
    congr 1
    ring
  · have hshift : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => s - k) (Ioo (t - η) (t + η)) :=
      (contDiff_id.sub contDiff_const).contMDiff.contMDiffOn
    have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun s => A.invFun (s - k)) (Ioo (t - η) (t + η)) :=
      A.contMDiffOn_invFun.comp hshift fun s hs => (hdesc s hs).1
    exact hcomp.congr fun s hs => (hdesc s hs).2
  · exact ((contDiff_id.add contDiff_const).contMDiff).comp_contMDiffOn
      (A.contMDiffOn_toFun.mono hsub)

variable [CompactSpace M] [PreconnectedSpace M] [Nonempty M]

include hE

/-- **Milnor's Appendix, the first case (book p. 54): a compact connected smooth one-manifold
without boundary is diffeomorphic to the circle.**

Precisely: let `E` be a real normed space with `Module.finrank ℝ E = 1`, let
`I : ModelWithCorners ℝ E H`, and let `M` be a nonempty compact Hausdorff preconnected `C^∞`
manifold charted on `H` with `I.boundary M = ∅`.  Then `M` is `C^∞`-diffeomorphic to `Circle` with
`Mathlib`'s model `𝓡 1`.

The diffeomorphism is exhibited: it is the inverse of `z ↦ γ (arg z · T / 2π)`, where `γ` is the
arc-length parametrization of `M` by the line from `exists_periodic_parametrisation` and `T` is its
minimal period.  Bijectivity is the sharp form of the period statement -- `γ s = γ t` exactly when
`s - t ∈ T ℤ`, and `circleParam T s = circleParam T t` under exactly the same condition -- and
smoothness in both directions comes from composing `γ` with a *local inverse* of `circleParam T`,
which exists because `circleParam T` is a local diffeomorphism.  Mathlib has no quotient-manifold
theory, so the descent has to go through local inverses of the exponential like this rather than
through `ℝ / T ℤ`.

Hypotheses: `Module.finrank ℝ E = 1`, `IsManifold I ∞ M`, `T2Space M`, `CompactSpace M`,
`PreconnectedSpace M`, `Nonempty M`, and `I.boundary M = ∅`.  No second countability (compact plus
Hausdorff gives it), no orientability, and no boundarylessness of the *model* -- only of `M`. -/
theorem nonempty_diffeomorphCircle (hb : I.boundary M = ∅) :
    Nonempty (Diffeomorph I (𝓡 1) M Circle ∞) := by
  obtain ⟨L, γ, T, hT, hγ, hper, hsurj, -, -, hiff⟩ := exists_periodic_parametrisation I hE hb
  -- the descended map, and the fact that it inverts the parametrization
  have hΦθ : ∀ t : ℝ, γ (circleSection T (circleParam T t)) = γ t := by
    intro t
    exact (hiff _ _).2 ((circleParam_eq_iff hT).1 (circleParam_circleSection hT (circleParam T t)))
  have hbij : Function.Bijective (fun z : Circle => γ (circleSection T z)) := by
    constructor
    · intro z₁ z₂ hz
      obtain ⟨t₁, rfl⟩ := circleParam_surjective hT z₁
      obtain ⟨t₂, rfl⟩ := circleParam_surjective hT z₂
      simp only [hΦθ] at hz
      exact (circleParam_eq_iff hT).2 ((hiff _ _).1 hz)
    · intro x
      obtain ⟨t, rfl⟩ := hsurj x
      exact ⟨circleParam T t, hΦθ t⟩
  -- the descended map is a local diffeomorphism, through a local inverse of `circleParam T`
  have hloc : IsLocalDiffeomorph (𝓡 1) I ∞ fun z : Circle => γ (circleSection T z) := by
    intro z
    obtain ⟨t, rfl⟩ := circleParam_surjective hT z
    have hθ : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ (circleParam T) t :=
      isLocalDiffeomorph_circleParam hT t
    have hψt : hθ.localInverse (circleParam T t) = t :=
      hθ.localInverse_left_inv hθ.localInverse_mem_target
    have hγloc : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) I ∞ γ (hθ.localInverse (circleParam T t)) := by
      rw [hψt]; exact hγ.isLocalDiffeomorphAt I (mem_univ t)
    refine IsLocalDiffeomorphAt.congr_eventuallyEq I
      (IsLocalDiffeomorphAt.comp I M hθ.localInverse_isLocalDiffeomorphAt hγloc) ?_
    filter_upwards [hθ.localInverse.open_source.mem_nhds hθ.localInverse_mem_source] with w hw
    have hu : circleParam T (hθ.localInverse w) = w := hθ.localInverse_right_inv hw
    show γ (circleSection T w) = γ (hθ.localInverse w)
    conv_lhs => rw [← hu]
    exact hΦθ _
  exact ⟨(hloc.diffeomorphOfBijective hbij).symm⟩

/-- **The boundaryless compact case, as a statement about the circle**: a nonempty compact Hausdorff
preconnected `C^∞` one-manifold with empty boundary is diffeomorphic to `Circle`, in the direction
`Circle → M`.  Same hypotheses as `nonempty_diffeomorphCircle`. -/
theorem nonempty_diffeomorphCircle' (hb : I.boundary M = ∅) :
    Nonempty (Diffeomorph (𝓡 1) I Circle M ∞) :=
  (nonempty_diffeomorphCircle I hE hb).map Diffeomorph.symm

end Main

end Milnor.OneManifold.Smooth
