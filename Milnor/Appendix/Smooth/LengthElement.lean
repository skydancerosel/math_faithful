import Milnor.Appendix.Smooth.SmoothArc
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Milnor's Appendix, smooth version: the length element

Milnor, *Topology from the Differentiable Viewpoint*, Appendix (book p. 54), classifies the
connected one-manifolds.  This file is **Stage 3** of the plan `Exposition/PlanOneManifold.md`,
which builds that classification on top of the topological Appendix of
`Milnor/Appendix/OneManifold.lean`, the one-dimensional model of `Milnor/Appendix/Smooth/Setup.lean`
(Stage 0) and the smooth arcs of `Milnor/Appendix/Smooth/SmoothArc.lean` (Stage 1).

Milnor's proof reparametrizes a one-manifold by *arc length*, which presupposes a Riemannian
metric; his manifolds sit in `ℝᵏ`, so he may use the Euclidean one without comment.  In dimension
one a Riemannian metric is the same thing as a **length element**: a positive smooth density, read
in each local real coordinate, transforming by the absolute value of the derivative of the
transition.  That is what this file builds, and it is the only piece of general theory the
classification needs which Mathlib does not have.

## The formulation

The awkwardness of a density is that it is not a function on the manifold: it is a function of a
point *and* a local coordinate.  Rather than build the bundle of bilinear forms on the tangent
bundle, this file indexes the density by a **local real parameter**:

* `Milnor.OneManifold.Smooth.RealChart I n M`: a partial homeomorphism from an open subset of `M`
  onto a subset of `ℝ` with unique derivatives, `Cⁿ` in both directions.  Both of the things one
  wants to read a density in are real charts: an honest chart of `M`, through Stage 0's real
  coordinate (`RealChart.ofChart`), and a smooth arc (`SmoothArc.toRealChart`).  Using one notion
  for both is what makes Stage 4 short: the length element can be evaluated along an arc with no
  intermediate layer.
* `Milnor.OneManifold.Smooth.transDeriv c c' u`: the derivative of the transition `c → c'` at the
  `c`-parameter `u`, taken *within* `c.target`, which may be half-open.
* `Milnor.OneManifold.Smooth.LengthElement I n M`: a function `ρ` assigning to every real chart `c`
  a real function `ρ c` which is positive and `Cⁿ` on `c.target` and satisfies the **cocycle rule**
  `ρ c u = ρ c' (c' (c⁻¹ u)) * |transDeriv c c' u|`.

## What is proved

* `transDeriv_self`, `transDeriv_comp`, `transDeriv_ne_zero`: the transition derivatives of real
  charts form a cocycle -- `transDeriv c c u = 1` and
  `transDeriv c c'' u = transDeriv c' c'' (c' (c⁻¹ u)) * transDeriv c c' u` -- and therefore never
  vanish.  This is the chain rule on a possibly half-open set, and it is the engine of the whole
  file: the cocycle rule for the length element is `transDeriv_comp` summed against a partition of
  unity, and positivity is `transDeriv_ne_zero`.
* `contDiffOn_transDeriv`: a transition derivative is itself `Cᵐ` where the charts are `Cᵐ⁺¹`.
* `nonempty_lengthElement`: **a `C^∞` one-manifold which is Hausdorff and σ-compact carries a
  `C^∞` length element.**  Constructed exactly as the plan prescribes: with `λ` a smooth partition
  of unity subordinate to the sources of the preferred charts (Mathlib's
  `SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source`) and `κ i` the real coordinate of
  the chart at `i`,
  `ρ c u = ∑ᶠ i, λ i (c⁻¹ u) * |transDeriv c (κ i) u|`.
  Each summand is `C^∞` where it matters because the transition derivative never vanishes there,
  so its absolute value is smooth; and the sum is positive because the `λ i` add up to `1`, so one
  of them is positive, and at such an `i` the point lies in the chart at `i` and the transition
  derivative is nonzero.

## Hypotheses

The structures `RealChart` and `LengthElement` and the `transDeriv` calculus are stated for a
manifold `M` charted on an arbitrary model with corners `I : ModelWithCorners ℝ E H` and an
arbitrary smoothness `n`; no dimension hypothesis, no Hausdorffness, no compactness, no
boundarylessness.  The derivative statements need `n ≠ 0`.

The **existence** theorem `nonempty_lengthElement` needs, on top of that:

* `Module.finrank ℝ E = 1`, to have Stage 0's real coordinate on a chart at all.  Finite
  dimensionality of `E`, which Mathlib's partition of unity demands, is a consequence and is
  supplied internally by Stage 0's `finiteDimensional_of_finrank_eq_one`.
* `n = ∞`, because Mathlib's smooth partitions of unity are built from `C^∞` bump functions, and
  because a transition derivative loses one degree of smoothness -- for finite `n` the construction
  would give a `Cⁿ⁻¹` length element from a `Cⁿ` manifold.
* `T2Space M` and `SigmaCompactSpace M`, exactly the hypotheses of
  `SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source`.  Both are automatic for a compact
  Hausdorff manifold, so the compact case of the plan needs nothing extra; the **full σ-compact
  generality is achieved**, and the plan's fallback to a finite cover was not needed.  No
  boundarylessness: Mathlib's partitions of unity work for a manifold with boundary, and all three
  shapes of the model range allowed by Stage 0 stay alive.

## References

* Milnor, *Topology from the Differentiable Viewpoint*, Appendix, p. 54.
* `Exposition/PlanOneManifold.md`, Stage 3.
-/

open Set Filter Topology

open scoped ContDiff Manifold

noncomputable section

namespace Milnor.OneManifold.Smooth

/-! ## Local real parameters -/

section RealChartDef

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]

/-- **A local real parameter on `M`**: a partial homeomorphism from an *open* subset of `M` onto a
subset of `ℝ` on which derivatives are unique, `Cⁿ` in both directions.

This is the common generalization of the two things a density has to be read in: a chart of `M`,
expressed in Stage 0's real coordinate (`RealChart.ofChart`), and a smooth arc
(`SmoothArc.toRealChart`).  The target is *not* assumed open -- for an arc starting at a boundary
point it is `[0, ε)` -- which is why unique differentiability of the target is a field rather than a
consequence; it is what makes `derivWithin` unambiguous at an endpoint.  Continuity in both
directions is not a field, being a consequence of the two smoothness fields. -/
structure RealChart (I : ModelWithCorners ℝ E H) (n : WithTop ℕ∞) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] where
  /-- The real coordinate. -/
  toFun : M → ℝ
  /-- The parametrization, inverse to the coordinate. -/
  invFun : ℝ → M
  /-- The open subset of `M` on which the coordinate is defined. -/
  source : Set M
  /-- The subset of `ℝ` which the coordinate covers. -/
  target : Set ℝ
  /-- The coordinate maps the source into the target. -/
  map_source' : ∀ x ∈ source, toFun x ∈ target
  /-- The parametrization maps the target into the source. -/
  map_target' : ∀ t ∈ target, invFun t ∈ source
  /-- The parametrization undoes the coordinate on the source. -/
  left_inv' : ∀ x ∈ source, invFun (toFun x) = x
  /-- The coordinate undoes the parametrization on the target. -/
  right_inv' : ∀ t ∈ target, toFun (invFun t) = t
  /-- The source is open. -/
  open_source : IsOpen source
  /-- Derivatives along the target are unique, so `derivWithin` is unambiguous even at an endpoint
  of a half-open target. -/
  uniqueDiffOn_target : UniqueDiffOn ℝ target
  /-- The coordinate is `Cⁿ` on the source, as a map of manifolds into `ℝ`. -/
  contMDiffOn_toFun : ContMDiffOn I 𝓘(ℝ, ℝ) n toFun source
  /-- The parametrization is `Cⁿ` on the target, as a map from `ℝ` into the manifold.  The target
  may be half-open, so this is one-sided smoothness at an endpoint. -/
  contMDiffOn_invFun : ContMDiffOn 𝓘(ℝ, ℝ) I n invFun target

namespace RealChart

variable {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- The coordinate of a point of the source lies in the target. -/
theorem map_source (c : RealChart I n M) {x : M} (hx : x ∈ c.source) : c.toFun x ∈ c.target :=
  c.map_source' x hx

/-- The point named by a parameter of the target lies in the source. -/
theorem map_target (c : RealChart I n M) {t : ℝ} (ht : t ∈ c.target) : c.invFun t ∈ c.source :=
  c.map_target' t ht

/-- The parametrization undoes the coordinate. -/
theorem left_inv (c : RealChart I n M) {x : M} (hx : x ∈ c.source) : c.invFun (c.toFun x) = x :=
  c.left_inv' x hx

/-- The coordinate undoes the parametrization. -/
theorem right_inv (c : RealChart I n M) {t : ℝ} (ht : t ∈ c.target) : c.toFun (c.invFun t) = t :=
  c.right_inv' t ht

/-- The parametrization is continuous on the target. -/
theorem continuousOn_invFun (c : RealChart I n M) : ContinuousOn c.invFun c.target :=
  c.contMDiffOn_invFun.continuousOn

/-- The coordinate is continuous on the source. -/
theorem continuousOn_toFun (c : RealChart I n M) : ContinuousOn c.toFun c.source :=
  c.contMDiffOn_toFun.continuousOn

/-- At every parameter of the target, including an endpoint, the derivative within the target is
unique. -/
theorem uniqueDiffWithinAt_target (c : RealChart I n M) {t : ℝ} (ht : t ∈ c.target) :
    UniqueDiffWithinAt ℝ c.target t := c.uniqueDiffOn_target t ht

/-- **The parameters lying over an open set are cut out of the target by an open set.**  By
continuity of the parametrization, `c.target ∩ c.invFun ⁻¹' U` is `c.target ∩ W` for some open
`W ⊆ ℝ`. -/
theorem exists_isOpen_inter_preimage_invFun (c : RealChart I n M) {U : Set M} (hU : IsOpen U) :
    ∃ W : Set ℝ, IsOpen W ∧ c.target ∩ c.invFun ⁻¹' U = c.target ∩ W := by
  obtain ⟨W, hW, hWeq⟩ := (continuousOn_iff'.1 c.continuousOn_invFun) U hU
  exact ⟨W, hW, by rw [inter_comm c.target, hWeq, inter_comm]⟩

/-- The parameters lying over an open set form a neighbourhood, *within the target*, of each of
their members.  This is what lets a derivative computed there be read as a derivative within the
whole target. -/
theorem inter_preimage_invFun_mem_nhdsWithin (c : RealChart I n M) {U : Set M} (hU : IsOpen U)
    {t : ℝ} (ht : t ∈ c.target) (htU : c.invFun t ∈ U) :
    c.target ∩ c.invFun ⁻¹' U ∈ 𝓝[c.target] t := by
  obtain ⟨W, hW, hWeq⟩ := c.exists_isOpen_inter_preimage_invFun hU
  have htW : t ∈ W := by
    have h : t ∈ c.target ∩ W := by rw [← hWeq]; exact ⟨ht, htU⟩
    exact h.2
  rw [hWeq]
  exact inter_mem_nhdsWithin _ (hW.mem_nhds htW)

/-- Derivatives along the parameters lying over an open set are unique: intersecting the target
with the preimage of an open set does not spoil unique differentiability. -/
theorem uniqueDiffOn_inter_preimage_invFun (c : RealChart I n M) {U : Set M} (hU : IsOpen U) :
    UniqueDiffOn ℝ (c.target ∩ c.invFun ⁻¹' U) := by
  obtain ⟨W, hW, hWeq⟩ := c.exists_isOpen_inter_preimage_invFun hU
  rw [hWeq]
  intro t ht
  exact (c.uniqueDiffWithinAt_target ht.1).inter (hW.mem_nhds ht.2)

/-- **The transition between two local real parameters is `Cⁿ`** on the set of `c`-parameters whose
point also lies in the source of `c'`.  That set need not be open, so this is smoothness in the
Whitney sense; it is proved by composing the two smoothness fields and reading the result in the
trivial model on `ℝ`. -/
theorem contDiffOn_trans (c c' : RealChart I n M) :
    ContDiffOn ℝ n (fun s => c'.toFun (c.invFun s)) (c.target ∩ c.invFun ⁻¹' c'.source) :=
  contMDiffOn_iff_contDiffOn.1
    (c'.contMDiffOn_toFun.comp (c.contMDiffOn_invFun.mono inter_subset_left) inter_subset_right)

/-- The transition between two local real parameters is differentiable at each parameter whose
point lies in the source of the second one. -/
theorem differentiableWithinAt_trans (hn : n ≠ 0) (c c' : RealChart I n M) {u : ℝ}
    (hu : u ∈ c.target) (hx : c.invFun u ∈ c'.source) :
    DifferentiableWithinAt ℝ (fun s => c'.toFun (c.invFun s))
      (c.target ∩ c.invFun ⁻¹' c'.source) u :=
  (c.contDiffOn_trans c').differentiableOn hn u ⟨hu, hx⟩

end RealChart

/-! ## The transition derivative -/

variable {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- **The derivative of the transition from `c` to `c'`**, at the `c`-parameter `u`, taken *within*
`c.target`.  The target may be half-open and `u` may be an endpoint of it, in which case this is a
one-sided derivative; it is unambiguous because `c.target` has unique derivatives. -/
def transDeriv (c c' : RealChart I n M) (u : ℝ) : ℝ :=
  derivWithin (fun s => c'.toFun (c.invFun s)) c.target u

/-- The transition derivative may equally be computed within the smaller set of parameters whose
point lies in the source of `c'`, on which the transition is actually defined. -/
theorem transDeriv_eq_derivWithin_inter (hn : n ≠ 0) (c c' : RealChart I n M) {u : ℝ}
    (hu : u ∈ c.target) (hx : c.invFun u ∈ c'.source) :
    transDeriv c c' u = derivWithin (fun s => c'.toFun (c.invFun s))
      (c.target ∩ c.invFun ⁻¹' c'.source) u :=
  derivWithin_of_mem_nhdsWithin
    (c.inter_preimage_invFun_mem_nhdsWithin c'.open_source hu hx)
    (c.uniqueDiffWithinAt_target hu)
    (RealChart.differentiableWithinAt_trans hn c c' hu hx)

/-- **The transition has the transition derivative as its derivative within the whole target.**
This is the form in which the chain rule is applied below; the point of it is that the derivative
is taken within `c.target`, not within the smaller set on which the transition is defined. -/
theorem hasDerivWithinAt_trans (hn : n ≠ 0) (c c' : RealChart I n M) {u : ℝ} (hu : u ∈ c.target)
    (hx : c.invFun u ∈ c'.source) :
    HasDerivWithinAt (fun s => c'.toFun (c.invFun s)) (transDeriv c c' u) c.target u := by
  rw [transDeriv_eq_derivWithin_inter hn c c' hu hx]
  exact (RealChart.differentiableWithinAt_trans hn c c' hu hx).hasDerivWithinAt
    |>.mono_of_mem_nhdsWithin (c.inter_preimage_invFun_mem_nhdsWithin c'.open_source hu hx)

/-- **The transition from a local real parameter to itself has derivative `1`.**  The transition is
the identity on the target, and the target has unique derivatives. -/
theorem transDeriv_self (c : RealChart I n M) {u : ℝ} (hu : u ∈ c.target) :
    transDeriv c c u = 1 := by
  have h : HasDerivWithinAt (fun s => c.toFun (c.invFun s)) 1 c.target u :=
    (hasDerivWithinAt_id u c.target).congr (fun s hs => c.right_inv hs) (c.right_inv hu)
  exact h.derivWithin (c.uniqueDiffWithinAt_target hu)

/-- **The cocycle rule for transition derivatives**, i.e. the chain rule on a possibly half-open
set: going from `c` to `c''` directly has the same derivative as going through `c'`.

All three derivatives are taken within the respective targets, which need not be open, and `u` may
be an endpoint of `c.target`.  Two things make the argument work there.  `HasDerivWithinAt.comp`
needs no unique differentiability, only that the transition maps the set of parameters lying over
`c'.source ∩ c''.source` into `c'.target`; and the set of such parameters is a neighbourhood of `u`
*within* `c.target`, so the composite derivative computed there is the derivative within
`c.target`, which is where unique differentiability is used.

Hypotheses: `n ≠ 0`.  No dimension hypothesis, no Hausdorffness, no compactness. -/
theorem transDeriv_comp (hn : n ≠ 0) (c c' c'' : RealChart I n M) {u : ℝ} (hu : u ∈ c.target)
    (h' : c.invFun u ∈ c'.source) (h'' : c.invFun u ∈ c''.source) :
    transDeriv c c'' u = transDeriv c' c'' (c'.toFun (c.invFun u)) * transDeriv c c' u := by
  set x : M := c.invFun u with hxdef
  set v : ℝ := c'.toFun x with hvdef
  have hvt : v ∈ c'.target := c'.map_source h'
  have hvx : c'.invFun v = x := c'.left_inv h'
  set S : Set ℝ := c.target ∩ c.invFun ⁻¹' (c'.source ∩ c''.source) with hSdef
  have hSsub : S ⊆ c.target := inter_subset_left
  have hSnhds : S ∈ 𝓝[c.target] u :=
    c.inter_preimage_invFun_mem_nhdsWithin (c'.open_source.inter c''.open_source) hu ⟨h', h''⟩
  have huS : u ∈ S := ⟨hu, h', h''⟩
  -- the inner map, differentiated within `c.target` and then restricted to `S`
  have hd : HasDerivWithinAt (fun s => c'.toFun (c.invFun s)) (transDeriv c c' u) S u :=
    (hasDerivWithinAt_trans hn c c' hu h').mono hSsub
  -- the outer map, differentiated within `c'.target`
  have hd' : HasDerivWithinAt (fun w => c''.toFun (c'.invFun w)) (transDeriv c' c'' v)
      c'.target v := hasDerivWithinAt_trans hn c' c'' hvt (by rw [hvx]; exact h'')
  have hmaps : MapsTo (fun s => c'.toFun (c.invFun s)) S c'.target :=
    fun s hs => c'.map_source hs.2.1
  have hcomp : HasDerivWithinAt ((fun w => c''.toFun (c'.invFun w)) ∘
      fun s => c'.toFun (c.invFun s)) (transDeriv c' c'' v * transDeriv c c' u) S u :=
    HasDerivWithinAt.comp u hd' hd hmaps
  have heq : ∀ s ∈ S, c''.toFun (c.invFun s) =
      ((fun w => c''.toFun (c'.invFun w)) ∘ fun s => c'.toFun (c.invFun s)) s :=
    fun s hs => by simp only [Function.comp_apply, c'.left_inv hs.2.1]
  have hfin : HasDerivWithinAt (fun s => c''.toFun (c.invFun s))
      (transDeriv c' c'' v * transDeriv c c' u) S u := hcomp.congr heq (heq u huS)
  exact (hfin.mono_of_mem_nhdsWithin hSnhds).derivWithin (c.uniqueDiffWithinAt_target hu)

/-- **A transition derivative never vanishes.**  Take `c'' = c` in `transDeriv_comp`: the product of
the two transition derivatives is `transDeriv c c u = 1`.  Geometrically this says a local real
parameter is an immersion when read in any other one, endpoints of a half-open target included.

Hypotheses: `n ≠ 0`.  No dimension hypothesis, no Hausdorffness, no compactness. -/
theorem transDeriv_ne_zero (hn : n ≠ 0) (c c' : RealChart I n M) {u : ℝ} (hu : u ∈ c.target)
    (hx : c.invFun u ∈ c'.source) : transDeriv c c' u ≠ 0 := by
  have h := transDeriv_comp hn c c' c hu hx (c.map_target hu)
  rw [transDeriv_self c hu] at h
  exact right_ne_zero_of_mul_eq_one h.symm

/-- **A transition derivative is one degree less smooth than the charts.**  On the set of
`c`-parameters lying over `c'.source`, `transDeriv c c'` is `Cᵐ` whenever the charts are `Cⁿ` with
`m + 1 ≤ n`; for `n = m = ∞` there is no loss.  The proof is Mathlib's `ContDiffOn.derivWithin`
applied on that set, together with `transDeriv_eq_derivWithin_inter` to identify the two
`derivWithin`s. -/
theorem contDiffOn_transDeriv (hn : n ≠ 0) {m : WithTop ℕ∞} (hmn : m + 1 ≤ n)
    (c c' : RealChart I n M) :
    ContDiffOn ℝ m (transDeriv c c') (c.target ∩ c.invFun ⁻¹' c'.source) := by
  have hS : UniqueDiffOn ℝ (c.target ∩ c.invFun ⁻¹' c'.source) :=
    c.uniqueDiffOn_inter_preimage_invFun c'.open_source
  have h := ((c.contDiffOn_trans c').derivWithin hS hmn)
  exact h.congr fun u hu => transDeriv_eq_derivWithin_inter hn c c' hu.1 hu.2

end RealChartDef

/-! ## Local real parameters from arcs and from charts -/

section Sources

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {n : WithTop ℕ∞} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **A smooth arc is a local real parameter.**  Everything is inherited: the source of an arc is
open and its target is convex with nonempty interior, hence has unique derivatives by Stage 1's
`uniqueDiffOn_target`. -/
def SmoothArc.toRealChart {I : ModelWithCorners ℝ E H} (A : SmoothArc I n M) : RealChart I n M where
  toFun := A.toFun
  invFun := A.invFun
  source := A.source
  target := A.target
  map_source' := A.map_source'
  map_target' := A.map_target'
  left_inv' := A.left_inv'
  right_inv' := A.right_inv'
  open_source := A.open_source
  uniqueDiffOn_target := uniqueDiffOn_target A.toArc
  contMDiffOn_toFun := A.contMDiffOn_toFun
  contMDiffOn_invFun := A.contMDiffOn_invFun

/-- The coordinate of the local real parameter of a smooth arc is the arc's coordinate. -/
@[simp] theorem SmoothArc.toRealChart_toFun {I : ModelWithCorners ℝ E H} (A : SmoothArc I n M) :
    A.toRealChart.toFun = A.toFun := rfl

/-- The parametrization of the local real parameter of a smooth arc is the arc's
parametrization. -/
@[simp] theorem SmoothArc.toRealChart_invFun {I : ModelWithCorners ℝ E H} (A : SmoothArc I n M) :
    A.toRealChart.invFun = A.invFun := rfl

/-- The source of the local real parameter of a smooth arc is the arc's source. -/
@[simp] theorem SmoothArc.toRealChart_source {I : ModelWithCorners ℝ E H} (A : SmoothArc I n M) :
    A.toRealChart.source = A.source := rfl

/-- The target of the local real parameter of a smooth arc is the arc's target. -/
@[simp] theorem SmoothArc.toRealChart_target {I : ModelWithCorners ℝ E H} (A : SmoothArc I n M) :
    A.toRealChart.target = A.target := rfl

variable (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1)

/-- **A chart of `M` is a local real parameter**, through Stage 0's real coordinate `chartCoord`.
The target is the coordinate image of the chart, which by Stage 0 is the model range cut by an open
set; that is why it has unique derivatives even though it need not be open, and it is where the
boundary of the model shows up.

Hypotheses: `Module.finrank ℝ E = 1` and membership of `e` in the maximal `Cⁿ` atlas. -/
def RealChart.ofChart (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I n M) : RealChart I n M where
  toFun := chartCoord I hE e
  invFun := ofChartCoord I hE e
  source := e.source
  target := chartCoord I hE e '' e.source
  map_source' x hx := ⟨x, hx, rfl⟩
  map_target' t ht := by
    obtain ⟨y, hy, rfl⟩ := ht
    rw [ofChartCoord_chartCoord I hE hy]
    exact hy
  left_inv' _ hx := ofChartCoord_chartCoord I hE hx
  right_inv' t ht := by
    obtain ⟨y, hy, rfl⟩ := ht
    rw [ofChartCoord_chartCoord I hE hy]
  open_source := e.open_source
  uniqueDiffOn_target := by
    obtain ⟨W, hW, hWeq⟩ := exists_isOpen_chartCoord_image I hE e
    rw [hWeq, inter_comm]
    intro t ht
    exact (uniqueDiffOn_modelRange I hE t ht.1).inter (hW.mem_nhds ht.2)
  contMDiffOn_toFun := contMDiffOn_chartCoord I hE he
  contMDiffOn_invFun := contMDiffOn_ofChartCoord I hE he

/-- The source of the local real parameter attached to a chart is the source of the chart. -/
@[simp] theorem RealChart.ofChart_source (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I n M) : (RealChart.ofChart I hE e he).source = e.source :=
  rfl

/-- The coordinate of the local real parameter attached to a chart is Stage 0's `chartCoord`. -/
@[simp] theorem RealChart.ofChart_toFun (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I n M) :
    (RealChart.ofChart I hE e he).toFun = chartCoord I hE e := rfl

end Sources

/-! ## The length element -/

section LengthElementDef

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]

/-- **A length element on `M`**: a Riemannian metric in dimension one, written as a density.

To every local real parameter `c` it assigns a real function `fn c`, positive and `Cⁿ` on
`c.target`, and these are related by the **cocycle rule**
`fn c u = fn c' (c' (c⁻¹ u)) * |transDeriv c c' u|`
whenever the point named by the `c`-parameter `u` also lies in the source of `c'`.  The cocycle rule
is exactly the transformation law of a density `ρ |du|` under a change of parameter, and it is what
makes "the integral of the length element along an arc" independent of the parametrization -- which
is what Stage 4 uses to build unit-speed arcs.

Nothing here assumes a dimension, Hausdorffness, compactness or boundarylessness; existence is
`nonempty_lengthElement` below, and that does need hypotheses. -/
structure LengthElement (I : ModelWithCorners ℝ E H) (n : WithTop ℕ∞) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] where
  /-- The density, read in a local real parameter. -/
  fn : RealChart I n M → ℝ → ℝ
  /-- The density is positive on the target of every local real parameter. -/
  pos : ∀ c : RealChart I n M, ∀ u ∈ c.target, 0 < fn c u
  /-- The density is `Cⁿ` on the target of every local real parameter -- one-sidedly at an endpoint
  of a half-open target. -/
  contDiffOn : ∀ c : RealChart I n M, ContDiffOn ℝ n (fn c) c.target
  /-- **The cocycle rule**: the density transforms by the absolute value of the derivative of the
  transition. -/
  cocycle : ∀ c c' : RealChart I n M, ∀ u ∈ c.target, c.invFun u ∈ c'.source →
    fn c u = fn c' (c'.toFun (c.invFun u)) * |transDeriv c c' u|

variable {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- The density of a length element is nowhere zero on the target of a local real parameter. -/
theorem LengthElement.ne_zero (L : LengthElement I n M) (c : RealChart I n M) {u : ℝ}
    (hu : u ∈ c.target) : L.fn c u ≠ 0 := (L.pos c u hu).ne'

end LengthElementDef

/-! ## Existence of a length element -/

section Existence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) (M : Type*) [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

include hE in
/-- **Every `C^∞` one-manifold which is Hausdorff and σ-compact carries a `C^∞` length element.**

This is Stage 3 of the plan, and the existence theorem the classification needs: Milnor's proof
reparametrizes by arc length, which presupposes a Riemannian metric, and in dimension one a
Riemannian metric is a length element.  Milnor's manifolds are embedded in `ℝᵏ`, so he restricts the
Euclidean metric without comment; intrinsically there is something to prove, and Mathlib has no
existence theorem for a Riemannian metric.

**The construction.**  Let `λ` be a `C^∞` partition of unity subordinate to the sources of the
preferred charts (Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source`), and for
`i : M` let `κ i` be the local real parameter of the chart at `i` (`RealChart.ofChart`).  Set
`fn c u = ∑ᶠ i, λ i (c⁻¹ u) * |transDeriv c (κ i) u|`.

* *The cocycle rule* is `transDeriv_comp` applied term by term: for the terms that matter,
  `λ i (c⁻¹ u) ≠ 0` forces the point into the source of `κ i`, where the chain rule applies, and
  taking absolute values turns the chain rule into the cocycle rule.  The terms that do not matter
  vanish on both sides.
* *Positivity* is `transDeriv_ne_zero`: the `λ i` sum to `1`, so some `λ i (c⁻¹ u)` is positive, and
  at such an `i` the point lies in the chart at `i`, so the transition derivative is nonzero.
* *Smoothness* is local: near a given parameter the locally finite sum is a finite sum over the
  `tsupport`s meeting the point, and each of its terms is `C^∞` because `transDeriv` is
  (`contDiffOn_transDeriv`) and because the absolute value is smooth away from zero.

**Hypotheses.**  `Module.finrank ℝ E = 1` (through Stage 0's real coordinate on a chart);
`IsManifold I ∞ M`; `T2Space M` and `SigmaCompactSpace M`, which are what Mathlib's partition of
unity needs.  Finite dimensionality of `E` is automatic from `finrank = 1`.  Nothing is assumed
about the boundary: all three shapes of the model range allowed by Stage 0 are covered, and the
manifold may well have boundary points. -/
theorem nonempty_lengthElement : Nonempty (LengthElement I ∞ M) := by
  have : FiniteDimensional ℝ E := finiteDimensional_of_finrank_eq_one hE
  obtain ⟨lam, hsub⟩ := SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M
  -- the local real parameter of the preferred chart at `i`
  set κ : M → RealChart I ∞ M := fun i =>
    RealChart.ofChart I hE (chartAt H i) (IsManifold.chart_mem_maximalAtlas i) with hκdef
  have hκsource : ∀ i : M, (κ i).source = (chartAt H i).source := fun i => rfl
  -- the density
  set ρ : RealChart I ∞ M → ℝ → ℝ := fun c u => ∑ᶠ i : M, lam i (c.invFun u) *
    |transDeriv c (κ i) u| with hρdef
  -- a summand can only be nonzero at an `i` whose chart contains the point
  have hmem : ∀ (x : M) (i : M), lam i x ≠ 0 → x ∈ (κ i).source := by
    intro x i hx
    rw [hκsource]
    exact hsub i (subset_tsupport _ hx)
  -- the locally finite sum is the finite sum over the parameters of the point
  have hfinsum : ∀ (c : RealChart I ∞ M) (u : ℝ), ρ c u =
      ∑ i ∈ lam.finsupport (c.invFun u), lam i (c.invFun u) * |transDeriv c (κ i) u| := by
    intro c u
    rw [hρdef]
    refine finsum_eq_finsetSum_of_support_subset _ ?_
    intro i hi
    have hi' : lam i (c.invFun u) ≠ 0 := by
      intro h
      rw [Function.mem_support, h, zero_mul] at hi
      exact hi rfl
    exact (lam.mem_finsupport _).2 hi'
  refine ⟨{ fn := ρ, pos := ?_, contDiffOn := ?_, cocycle := ?_ }⟩
  · -- positivity
    intro c u hu
    rw [hfinsum c u]
    obtain ⟨i, hi⟩ := lam.exists_pos_of_mem (mem_univ (c.invFun u))
    refine Finset.sum_pos' (fun j _ => mul_nonneg (lam.nonneg j _) (abs_nonneg _)) ⟨i, ?_, ?_⟩
    · exact (lam.mem_finsupport _).2 hi.ne'
    · exact mul_pos hi (abs_pos.2
        (transDeriv_ne_zero (by simp) c (κ i) hu (hmem _ i hi.ne')))
  · -- smoothness
    intro c u₀ hu₀
    set x₀ : M := c.invFun u₀ with hx₀def
    -- a finite set of indices controlling the sum near `x₀`
    set F : Finset M := lam.fintsupport x₀ with hFdef
    obtain ⟨N, hNsub, hNopen, hNmem⟩ := mem_nhds_iff.1 (lam.eventually_finsupport_subset x₀)
    set N' : Set M := N ∩ ⋂ i ∈ F, (κ i).source with hN'def
    have hN'open : IsOpen N' := hNopen.inter (isOpen_biInter_finset fun i _ => (κ i).open_source)
    have hN'mem : x₀ ∈ N' := by
      refine ⟨hNmem, ?_⟩
      simp only [mem_iInter]
      intro i hi
      rw [hκsource]
      exact hsub i ((lam.mem_fintsupport_iff x₀ i).1 hi)
    set V : Set ℝ := c.target ∩ c.invFun ⁻¹' N' with hVdef
    have hVnhds : V ∈ 𝓝[c.target] u₀ :=
      c.inter_preimage_invFun_mem_nhdsWithin hN'open hu₀ hN'mem
    have hVu₀ : u₀ ∈ V := ⟨hu₀, hN'mem⟩
    -- on `V` the sum is the finite sum over `F`
    have hVeq : ∀ u ∈ V, ρ c u = ∑ i ∈ F, lam i (c.invFun u) * |transDeriv c (κ i) u| := by
      intro u hu
      rw [hfinsum c u]
      refine Finset.sum_subset (hNsub hu.2.1) ?_
      intro i _ hi
      have : lam i (c.invFun u) = 0 := by
        by_contra h
        exact hi ((lam.mem_finsupport _).2 h)
      rw [this, zero_mul]
    -- each term of the finite sum is `C^∞` on `V`
    have hterm : ∀ i ∈ F, ContDiffOn ℝ ∞
        (fun u => lam i (c.invFun u) * |transDeriv c (κ i) u|) V := by
      intro i hi
      have hxi : x₀ ∈ (κ i).source := by
        rw [hκsource]
        exact hsub i ((lam.mem_fintsupport_iff x₀ i).1 hi)
      have hVsub : V ⊆ c.target ∩ c.invFun ⁻¹' (κ i).source := by
        intro u hu
        refine ⟨hu.1, ?_⟩
        have := hu.2.2
        simp only [mem_iInter] at this
        exact this i hi
      have h1 : ContDiffOn ℝ ∞ (fun u => lam i (c.invFun u)) V := by
        have : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun u => lam i (c.invFun u)) c.target :=
          (lam i).contMDiff.comp_contMDiffOn c.contMDiffOn_invFun
        exact (contMDiffOn_iff_contDiffOn.1 this).mono inter_subset_left
      have h2 : ContDiffOn ℝ ∞ (fun u => |transDeriv c (κ i) u|) V := by
        refine (((contDiffOn_transDeriv (by simp) (m := ∞) (by simp) c (κ i)).abs
          ?_).mono hVsub)
        intro u hu
        exact transDeriv_ne_zero (by simp) c (κ i) hu.1 hu.2
      exact h1.mul h2
    have hsum : ContDiffOn ℝ ∞ (fun u => ∑ i ∈ F, lam i (c.invFun u) *
        |transDeriv c (κ i) u|) V := ContDiffOn.sum hterm
    refine ((hsum u₀ hVu₀).mono_of_mem_nhdsWithin hVnhds).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem hVnhds hVeq) (hVeq u₀ hVu₀)
  · -- the cocycle rule
    intro c c' u hu hx
    have hv : c'.invFun (c'.toFun (c.invFun u)) = c.invFun u := c'.left_inv hx
    rw [hfinsum c u, hfinsum c' (c'.toFun (c.invFun u)), hv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : lam i (c.invFun u) ≠ 0 := (lam.mem_finsupport _).1 hi
    have hxi : c.invFun u ∈ (κ i).source := hmem _ i hi'
    rw [transDeriv_comp (by simp) c c' (κ i) hu hx hxi, abs_mul]
    ring

end Existence

end Milnor.OneManifold.Smooth
