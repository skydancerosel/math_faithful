import Milnor.Appendix.Smooth.Main
import Milnor.Chapter7.Orientable
import Milnor.Chapter8.OrientFrame

/-!
# Connected one-manifolds are orientable

**What this file is for.**  Milnor's theorem at the end of §7 (book p. 50) — two smooth maps of a
closed connected *non-orientable* `m`-manifold to `Sᵐ` are smoothly homotopic exactly when their
degrees agree modulo `2` — used to be stated in `Milnor/Chapter7/HopfMod2.lean` with the extra
hypothesis `2 ≤ m`, which Stage 5 of the mod `2` plan needs in order to keep the complement of a
finite set connected.  That hypothesis is empty mathematics: a connected `1`-manifold is
diffeomorphic to the circle or to an interval and all of those are orientable, so a connected
non-orientable manifold has dimension at least two.  It was carried only because the classification
of one-manifolds was not formalized.  It now is (`Milnor/Appendix/Smooth/Main.lean`), and this file
draws the conclusion (`Milnor.two_le_of_not_isOrientable`,
`Milnor.two_le_of_not_isOrientable_slice`), which lets `HopfMod2.lean` drop the hypothesis.

Orientability is `Milnor.IsOrientable I M m` of `Chapter7/Orientable.lean`: the existence of a
`Milnor.Orient I M m`, i.e. of a choice `or x` of orientation of each tangent space `T_xM = E` such
that for every `x` and every `y` near `x` the derivative at `y` of the chart centred at `x` carries
`or y` to `or x`.

## What is proved

* **The pullback of an orientation along an invertible linear map.**  `Milnor.orPull hE b T` is the
  orientation of `E` which an invertible `T : E →L[ℝ] F` carries to the orientation `b` of `F`
  (`Milnor.orSign_orPull`); it is the only one (`Milnor.eq_orPull`), a space of dimension `n` having
  exactly two orientations.

* **Two cheap orientations.**  `Milnor.Orient.ofConst`: if all the charts of `M` are the *same*
  partial homeomorphism then every transition map is the identity and a constant family of
  orientations is an orientation.  `Milnor.Orient.ofZero`: a `0`-dimensional manifold is orientable
  whatever its charts, because in dimension `0` every linear map preserves every orientation
  (`Milnor.orSign_self_eq_one_of_zero`: the only tuple to test is the empty one).

* **Transport along a map with invertible derivative**
  (`Milnor.eventually_orSign_eq_one_of_pullback`, `Milnor.Orient.comap`,
  `Milnor.IsOrientable.comap`).  Let `Φ : M → N` be smooth between manifolds of the same dimension
  `n`, let `N` be oriented by `oN`, and let each `dΦ_x` be invertible.  Then `M` is oriented by
  `or x := orPull (oN.or (Φ x)) (dΦ_x)`.  `Φ` need be neither injective nor surjective nor a local
  diffeomorphism.  The proof is the chain rule of `Milnor.eventually_signAt_eq_of_contMDiffOn`
  (`Chapter5/Orient.lean`) read backwards: writing `Φ` in the charts at `x₀` and `Φ x₀` as `g`, the
  transition of `N` at `Φ x` composed with `dΦ_x` equals `dg` composed with the transition of `M` at
  `x`; the left-hand side has sign `1` by the definition of `or` and the compatibility of `oN`, and
  the right-hand side splits as the sign of `dg` — locally constant, and `1` at `x₀` because there
  `dg = dΦ_{x₀}` — times the sign of the transition of `M`, which is therefore `1`.
  `Milnor.IsOrientable.of_diffeomorph` is the case of a diffeomorphism, whose derivative is
  invertible by Mathlib's `Diffeomorph.mfderivToContinuousLinearEquiv`.

* **The four models of the classification are orientable.**  `Milnor.orientReal` (the line) and
  `Milnor.orientIci` (the closed half-line, with the one-chart structure Stage 8 puts on it) are
  constant families, by `Milnor.Orient.ofConst`.  `Milnor.orientIcc` (the unit interval) is *not*:
  Mathlib's manifold structure on `Icc (0 : ℝ) 1` has two charts, `z ↦ z` on `[0, 1)` and `z ↦ 1 - z`
  on `(0, 1]`, and the transition between them reverses orientation, so the orientation has to flip
  at the right endpoint; the one derivative that has to be computed is that transition, and
  `Milnor.mfd_extChartAt_Icc_top` computes it by factoring the chart at `1` through the chart at `z`
  and the reflection `t ↦ 1 - t` of the model space, which is affine.  `Milnor.isOrientable_circle`
  goes through the unit sphere `S¹ ⊆ ℝ²` of Chapter 5, which Chapter 8 orients as the boundary of the
  disk (`Milnor.Sphere.sphOrStd`): `S¹` is itself a nonempty compact Hausdorff connected boundaryless
  smooth one-manifold, so Stage 7 of the Appendix gives a diffeomorphism `S¹ → Circle`, and
  orientability travels along it.  That is shorter than the two direct routes — the derivative of the
  transition between the two stereographic charts of `Circle`, or a descent of the orientation of the
  line along the periodic parametrisation of `Milnor/Appendix/Smooth/Circle.lean` — because the sphere
  is oriented already.

* **Connected one-manifolds** (`Milnor.isOrientable_of_finrank_eq_one`): a connected, Hausdorff,
  `σ`-compact smooth manifold modelled on a *boundaryless* `I` with `finrank ℝ E = 1` is orientable.
  The classification (`Milnor.OneManifold.Smooth.nonempty_diffeomorph_cases`) makes it diffeomorphic
  to `Circle` if it is compact and to `ℝ` if it is not — the two interval models are excluded because
  the boundary of `M` is empty — and orientability travels back.

* **Hence the dimension of a connected non-orientable manifold**
  (`Milnor.two_le_of_not_isOrientable`): with the same hypotheses on `M` and `I` and
  `finrank ℝ E = m`, if `M` is not orientable then `2 ≤ m`.  Dimension `0` is excluded by
  `Milnor.Orient.ofZero` and dimension `1` by the previous item.
  `Milnor.two_le_of_not_isOrientable_slice` is the same statement for the objects of Chapters 7 and
  8, a compact slice submanifold `M` of a Euclidean space charted on `ℝᵐ`; there every hypothesis is
  free — `M` is Hausdorff as a subspace of a metric space, `σ`-compact because compact, and its model
  `𝓘(ℝ, ℝᵐ)` is boundaryless, so its boundary is empty.

## The one restriction, and why it costs nothing here

`Milnor.eventually_orSign_eq_one_of_pullback`, and so every transport statement, assumes
`[I.Boundaryless]` **for the source**; the target may have boundary.  Boundarylessness of the source
is used in exactly one way: the target of a chart of `M` must be open in the model space `E`, so that
the map `g` of `Φ` in charts is defined on an open set, has a genuine `fderiv` there and that
`fderiv` is continuous.  For a model with boundary the same argument would have to be run with
`fderivWithin ℝ g (range I)` and unique differentiability throughout; that is not done here.

The consequence is that `Milnor.isOrientable_of_finrank_eq_one` is proved for boundaryless models
only, so "every connected `σ`-compact one-manifold is orientable" is available here in that generality
and not for manifolds with boundary — even though all four models of the classification, the two with
boundary included, are oriented above.  Nothing in the project needs more: the manifolds of Chapter 7
are compact slice submanifolds of a Euclidean space, whose model `𝓘(ℝ, ℝᵐ)` is boundaryless.

## References

* Milnor, *Topology from the Differentiable Viewpoint*, §7 p. 50 and the Appendix p. 54.
* The classification of one-manifolds: `Milnor/Appendix/Smooth/Main.lean` (Stage 9) and the stages
  beneath it.
* The orientation machinery: `Milnor/Chapter5/OrSign.lean`, `Milnor/Chapter5/Orient.lean`,
  `Milnor/Chapter7/OrientTransport.lean`, `Milnor/Chapter7/Orientable.lean`.
* The use made of this file: `Milnor/Chapter7/HopfMod2.lean`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold

set_option linter.unusedSectionVars false

noncomputable section

namespace Milnor

/-! ### Pulling an orientation back along an invertible linear map -/

section Pull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {n : ℕ}

/-- The sign of a linear map between oriented spaces of possibly different model spaces is `1`,
`-1` or `0`.  (`Milnor.orSign_mem` is the case `F = E`.) -/
theorem orSign_trichotomy (a : Orientation ℝ E (Fin n)) (b : Orientation ℝ F (Fin n))
    (T : E →L[ℝ] F) : orSign a b T = 1 ∨ orSign a b T = -1 ∨ orSign a b T = 0 := sgn_mem

/-- A reference orientation of a space of dimension `n`, that of `Module.finBasisOfFinrankEq`. -/
def refOr (hE : finrank ℝ E = n) : Orientation ℝ E (Fin n) :=
  (finBasisOfFinrankEq ℝ E hE).orientation

/-- **The orientation pulled back along an invertible linear map**: the orientation of `E` which
`T : E →L[ℝ] F` carries to the orientation `b` of `F`.  It is the reference orientation or its
reverse, according to the sign of `T`; for singular `T` the value is junk. -/
def orPull (hE : finrank ℝ E = n) (b : Orientation ℝ F (Fin n)) (T : E →L[ℝ] F) :
    Orientation ℝ E (Fin n) :=
  if orSign (refOr hE) b T = 1 then refOr hE else -refOr hE

/-- **The characterising property of `Milnor.orPull`**: an invertible `T` carries `orPull hE b T`
to `b`. -/
theorem orSign_orPull (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (b : Orientation ℝ F (Fin n))
    {T : E →L[ℝ] F} (hT : Function.Bijective T) : orSign (orPull hE b T) b T = 1 := by
  by_cases h : orSign (refOr hE) b T = 1
  · rw [orPull, if_pos h]; exact h
  · rw [orPull, if_neg h, orSign_neg_left hE]
    rcases orSign_trichotomy (refOr hE) b T with h1 | h1 | h1
    · exact absurd h1 h
    · rw [h1]; norm_num
    · exact absurd h1 ((orSign_ne_zero_iff hE hF _ _ _).2 hT)

/-- **Uniqueness of the pullback**: `orPull hE b T` is the only orientation of `E` that the
invertible map `T` carries to `b`, because a space has only two orientations. -/
theorem eq_orPull (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) {a : Orientation ℝ E (Fin n)}
    {b : Orientation ℝ F (Fin n)} {T : E →L[ℝ] F} (hT : Function.Bijective T)
    (h : orSign a b T = 1) : a = orPull hE b T := by
  rcases eq_or_eq_neg hE a (orPull hE b T) with h1 | h1
  · exact h1
  · rw [h1, orSign_neg_left hE, orSign_orPull hE hF b hT] at h
    norm_num at h

/-- In dimension `0` every linear map preserves every orientation: the only tuple to test is the
empty one. -/
theorem orSign_self_eq_one_of_zero (a : Orientation ℝ E (Fin 0)) (T : E →L[ℝ] E) :
    orSign a a T = 1 := by
  have h : (fun i => T (orTuple a i)) = orTuple a := funext fun i => i.elim0
  rw [orSign]
  simp only [AlternatingMap.compLinearMap_apply, ContinuousLinearMap.coe_coe, h]
  exact sgn_mul_self (someVector_orTuple_ne_zero a)

end Pull

/-! ### Two easy orientations -/

section Easy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ}

/-- **A manifold covered by a single chart is orientable**, by a constant family of orientations:
all the transition maps are the identity, and the identity preserves every orientation. -/
def Orient.ofConst (hch : ∀ x y : M, (chartAt H x : M → H) = (chartAt H y : M → H))
    (a : Orientation ℝ E (Fin n)) : Orient I M n where
  or _ := a
  cont x := by
    refine Filter.Eventually.of_forall fun y => ?_
    have h : (extChartAt I x : M → E) = (extChartAt I y : M → E) :=
      congrArg (fun g : M → H => (I ∘ g : M → E)) (hch x y)
    rw [h, mfd_extChartAt_self]
    exact orSign_id a

/-- **A `0`-dimensional manifold is orientable**, whatever its charts. -/
def Orient.ofZero (hE : finrank ℝ E = 0) : Orient I M 0 where
  or _ := refOr hE
  cont _ := Filter.Eventually.of_forall fun _ => orSign_self_eq_one_of_zero _ _

end Easy

/-! ### Pulling an orientation back along a map with invertible derivative -/

section Comap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] {n : ℕ}

/-- **A family of orientations carried by `dΦ` to an orientation of the target is compatible with
the charts of the source.**  Let `Φ : M → N` be smooth between manifolds of the same dimension `n`,
let `oN` be an orientation of `N`, and let `or` assign to each `x : M` the orientation of `T_xM`
which `dΦ_x` carries to `oN` at `Φ x` (in particular `dΦ_x` is then invertible).  Then `or`
satisfies the compatibility condition of `Milnor.Orient`.

The proof is the chain-rule computation of `Milnor.eventually_signAt_eq_of_contMDiffOn` read
backwards.  Write `Φ` in the charts at `x₀` and `Φ x₀` as `g : E → F`.  The chain rule says that
for `x` near `x₀` the transition of `N` at `Φ x` composed with `dΦ_x` equals `dg` composed with
the transition of `M` at `x`.  Taking signs, the left-hand side has sign `1` -- one factor is the
hypothesis on `or`, the other is the compatibility of `oN` -- while the right-hand side splits as
the sign of `dg`, which is locally constant (`Milnor.eventually_orSign_eq_of_continuousAt`) and
equals `1` at `x₀` because there `dg = dΦ_{x₀}`, times the sign of the transition of `M`.  So the
latter is `1`, which is what was wanted. -/
theorem eventually_orSign_eq_one_of_pullback (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (oN : Orient J N n) {Φ : M → N} (hΦ : ContMDiff I J ∞ Φ)
    {or : M → Orientation ℝ E (Fin n)}
    (hor : ∀ x : M, orSign (or x) (oN.or (Φ x)) (mfd I J Φ x) = 1) (x₀ : M) :
    ∀ᶠ y in 𝓝 x₀, orSign (or y) (or x₀) (mfd I 𝓘(ℝ, E) (extChartAt I x₀) y) = 1 := by
  have hfc : ContinuousAt Φ x₀ := hΦ.continuous.continuousAt
  -- `Φ` read in the charts at `x₀` and `Φ x₀`
  let g : E → F := fun u => extChartAt J (Φ x₀) (Φ ((extChartAt I x₀).symm u))
  let U : Set E := (extChartAt I x₀).target ∩
    (extChartAt I x₀).symm ⁻¹' (Φ ⁻¹' (extChartAt J (Φ x₀)).source)
  have hWf : IsOpen (Φ ⁻¹' (extChartAt J (Φ x₀)).source) :=
    (isOpen_extChartAt_source (Φ x₀)).preimage hΦ.continuous
  have hU : IsOpen U := (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage
    (isOpen_extChartAt_target x₀) hWf
  have hg : ContDiffOn ℝ ∞ g U := by
    rw [← contMDiffOn_iff_contDiffOn]
    have h1 : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm U :=
      (contMDiffOn_extChartAt_symm x₀).mono inter_subset_left
    have h3 : ContMDiffOn J 𝓘(ℝ, F) ∞ (extChartAt J (Φ x₀)) (extChartAt J (Φ x₀)).source := by
      rw [extChartAt_source]; exact contMDiffOn_extChartAt
    exact h3.comp (hΦ.comp_contMDiffOn h1) (fun u hu => hu.2)
  have hfd : ContinuousOn (fderiv ℝ g) U := hg.continuousOn_fderiv_of_isOpen hU (by simp)
  have hx₀U : extChartAt I x₀ x₀ ∈ U := by
    refine ⟨(extChartAt I x₀).map_source (mem_extChartAt_source x₀), ?_⟩
    simp only [mem_preimage]
    rw [(extChartAt I x₀).left_inv (mem_extChartAt_source x₀)]
    exact mem_extChartAt_source (Φ x₀)
  have hV : (extChartAt I x₀).source ∩ Φ ⁻¹' (extChartAt J (Φ x₀)).source ∈ 𝓝 x₀ :=
    inter_mem (extChartAt_source_mem_nhds x₀) (hWf.mem_nhds (mem_extChartAt_source (Φ x₀)))
  -- the chain rule in the charts
  have key : ∀ x ∈ (extChartAt I x₀).source ∩ Φ ⁻¹' (extChartAt J (Φ x₀)).source,
      (mfd J 𝓘(ℝ, F) (extChartAt J (Φ x₀)) (Φ x)).comp (mfd I J Φ x) =
        (fderiv ℝ g (extChartAt I x₀ x)).comp (mfd I 𝓘(ℝ, E) (extChartAt I x₀) x) := by
    rintro x ⟨hxe, hxe'⟩
    have hxU : extChartAt I x₀ x ∈ U := by
      refine ⟨(extChartAt I x₀).map_source hxe, ?_⟩
      simp only [mem_preimage]; rw [(extChartAt I x₀).left_inv hxe]; exact hxe'
    have hD' := hasMFDerivAt_mfd (I := J) (J := 𝓘(ℝ, F)) ((contMDiffAt_extChartAt' (I := J)
      (n := ∞) (x := Φ x₀)
      (by rwa [← extChartAt_source J] : Φ x ∈ (chartAt G (Φ x₀)).source)).mdifferentiableAt
        (by simp))
    have hdf := hasMFDerivAt_mfd (I := I) (J := J) ((hΦ x).mdifferentiableAt (by simp))
    have hDe := hasMFDerivAt_mfd (I := I) (J := 𝓘(ℝ, E)) ((contMDiffAt_extChartAt' (I := I)
      (n := ∞) (x := x₀)
      (by rwa [← extChartAt_source I] : x ∈ (chartAt H x₀).source)).mdifferentiableAt (by simp))
    have hdg : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, F) g (extChartAt I x₀ x)
        (fderiv ℝ g (extChartAt I x₀ x)) :=
      ((hg.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)).hasFDerivAt.hasMFDerivAt
    have h1 := hD'.comp x hdf
    have h2 := hdg.comp x hDe
    have h3 : (extChartAt J (Φ x₀) ∘ Φ) =ᶠ[𝓝 x] (g ∘ extChartAt I x₀) := by
      filter_upwards [(isOpen_extChartAt_source x₀).mem_nhds hxe] with z hz
      simp only [Function.comp, g]
      rw [(extChartAt I x₀).left_inv hz]
    exact hasMFDerivAt_unique h1 (h2.congr_of_eventuallyEq h3)
  -- at `x₀` the derivative in the charts is the derivative of `Φ`
  have hGx₀ : fderiv ℝ g (extChartAt I x₀ x₀) = mfd I J Φ x₀ := by
    have hk := key x₀ ⟨mem_extChartAt_source x₀, mem_extChartAt_source (Φ x₀)⟩
    rw [mfd_extChartAt_self, mfd_extChartAt_self, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_id] at hk
    exact hk.symm
  have hmid0 : orSign (or x₀) (oN.or (Φ x₀)) (fderiv ℝ g (extChartAt I x₀ x₀)) = 1 := by
    rw [hGx₀]; exact hor x₀
  have hloc := eventually_orSign_eq_of_continuousAt hE hF (or x₀) (oN.or (Φ x₀))
    (hfd.continuousAt (hU.mem_nhds hx₀U)) (by rw [hmid0]; norm_num)
  have hloc' := (continuousAt_extChartAt x₀).eventually hloc
  have hcontN : ∀ᶠ x in 𝓝 x₀, orSign (oN.or (Φ x)) (oN.or (Φ x₀))
      (mfd J 𝓘(ℝ, F) (extChartAt J (Φ x₀)) (Φ x)) = 1 := hfc.eventually (oN.cont (Φ x₀))
  filter_upwards [hV, hloc', hcontN] with x hxV hmid hN
  have hk := key x hxV
  have h1 := orSign_comp hE hF (or x) (oN.or (Φ x)) (oN.or (Φ x₀)) (mfd I J Φ x)
    (mfd J 𝓘(ℝ, F) (extChartAt J (Φ x₀)) (Φ x))
  have h2 := orSign_comp hE hE (or x) (or x₀) (oN.or (Φ x₀))
    (mfd I 𝓘(ℝ, E) (extChartAt I x₀) x) (fderiv ℝ g (extChartAt I x₀ x))
  rw [hN, one_mul, hor x] at h1
  rw [← hk, h1, hmid, hmid0, one_mul] at h2
  exact h2.symm

/-- **The orientation pulled back along a map with invertible derivative.**  If `Φ : M → N` is
smooth, `M` and `N` have the same dimension `n`, `N` is oriented by `oN`, and the derivative of `Φ`
is invertible at every point, then `M` is oriented by declaring positive at `x` the orientation
which `dΦ_x` carries to the orientation of `N` at `Φ x`.

`Φ` need be neither injective nor surjective nor a local diffeomorphism: only the invertibility of
each `dΦ_x` matters. -/
def Orient.comap (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oN : Orient J N n) {Φ : M → N}
    (hΦ : ContMDiff I J ∞ Φ) (hbij : ∀ x : M, Function.Bijective (mfd I J Φ x)) :
    Orient I M n where
  or x := orPull hE (oN.or (Φ x)) (mfd I J Φ x)
  cont := eventually_orSign_eq_one_of_pullback hE hF oN hΦ
    (fun x => orSign_orPull hE hF _ (hbij x))

/-- **Orientability is inherited along a map with invertible derivative**, in particular along a
diffeomorphism. -/
theorem IsOrientable.comap (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (hN : IsOrientable J N n) {Φ : M → N} (hΦ : ContMDiff I J ∞ Φ)
    (hbij : ∀ x : M, Function.Bijective (mfd I J Φ x)) : IsOrientable I M n :=
  ⟨Orient.comap hE hF hN.orient hΦ hbij⟩

/-- **The derivative of a diffeomorphism is a linear isomorphism**, Mathlib's
`Diffeomorph.mfderivToContinuousLinearEquiv` read as a statement about `Milnor.mfd`. -/
theorem bijective_mfd_diffeomorph (Φ : Diffeomorph I J M N ∞) (x : M) :
    Function.Bijective (mfd I J Φ x) :=
  (Φ.mfderivToContinuousLinearEquiv (by simp) x).bijective

/-- **Orientability travels along a diffeomorphism.**  If `M` and `N` are diffeomorphic manifolds
of the same dimension `n` and `N` is orientable, so is `M`: push the orientation of `N` back by the
derivative of the diffeomorphism. -/
theorem IsOrientable.of_diffeomorph (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (hN : IsOrientable J N n) (Φ : Diffeomorph I J M N ∞) : IsOrientable I M n :=
  hN.comap hE hF Φ.contMDiff (bijective_mfd_diffeomorph Φ)

end Comap

/-! ### The four models of the classification are orientable -/

section Models

open OneManifold.Smooth

/-- **The line is orientable**: it is covered by the single chart `id`, so a constant family of
orientations will do. -/
def orientReal : Orient 𝓘(ℝ, ℝ) ℝ 1 := Orient.ofConst (fun _ _ => rfl) (refOr (by simp))

/-- **The closed half-line is orientable**: the manifold structure Stage 8 puts on `Ici (0 : ℝ)`
(`Milnor.OneManifold.Smooth.instIciChartedSpace`) has the single chart `iciHomeomorph`, so a
constant family of orientations will do.  Note that the model `𝓡∂ 1` has a boundary; nothing in
`Milnor.Orient.ofConst` minds. -/
def orientIci : Orient (𝓡∂ 1) (Ici (0 : ℝ)) 1 :=
  Orient.ofConst (fun _ _ => rfl) (refOr finrank_euclideanSpace_fin)

/-! #### The unit interval

Mathlib's manifold structure on `Icc (0 : ℝ) 1` has **two** charts, `IccLeftChart`, defined on
`[0, 1)` by `z ↦ z`, and `IccRightChart`, defined on `(0, 1]` by `z ↦ 1 - z`; the chart at `z` is the
first if `z < 1` and the second if `z = 1`.  The transition between them reverses orientation, so no
constant family of orientations works, and the orientation below is the one that flips at the right
endpoint.  The single computation needed is the derivative of that transition, and it is done by
factoring the chart at `1` through the chart at `z` and the reflection `t ↦ 1 - t` of the model
space, which is affine, so its derivative is `-1` everywhere. -/

section Icc

local notation "E1" => EuclideanSpace ℝ (Fin 1)

/-- **The sign of `-1` in dimension one is `-1`.**  With `e` the reference basis of the line, the
form representing an orientation takes the value `±1` on `e` and `∓1` on `-e`. -/
theorem orSign_neg_id_of_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : finrank ℝ E = 1) (a : Orientation ℝ E (Fin 1)) :
    orSign a a (-ContinuousLinearMap.id ℝ E) = -1 := by
  set e := finBasisOfFinrankEq ℝ E hE with he
  have hωe : (orEpsB e a • e.det) e ≠ 0 := by rw [orEpsB_apply_self]; exact orEpsB_ne_zero e a
  rw [orSign_eq_sgn_mul hE _ _ (rayOfNeZero_orEpsB_det e a) (rayOfNeZero_orEpsB_det e a)
    (-ContinuousLinearMap.id ℝ E) hωe]
  have hdet : e.det (fun i => -(e i)) = -1 := by
    rw [Basis.det_apply, Matrix.det_fin_one]
    simp [Basis.toMatrix_apply]
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.coe_coe, neg_apply, ContinuousLinearMap.id_apply, Basis.det_self, mul_one,
    hdet]
  rw [show orEpsB e a * (-1) * orEpsB e a = -(orEpsB e a * orEpsB e a) by ring, sgn_neg',
    sgn_mul_self (orEpsB_ne_zero e a)]

/-- **The extended chart of `[0,1]` at the right endpoint**, as a formula valid at every point of
`[0,1]`, not merely on the chart's source: it is `z ↦ 1 - z`. -/
theorem extChartAt_Icc_top (w : Icc (0 : ℝ) 1) :
    extChartAt (𝓡∂ 1) (⊤ : Icc (0 : ℝ) 1) w = WithLp.toLp 2 (fun _ : Fin 1 => 1 - (w : ℝ)) := by
  rw [extChartAt, OpenPartialHomeomorph.extend_coe]
  simp [Icc_chartedSpaceChartAt_of_top_le (z := (⊤ : Icc (0 : ℝ) 1)) (by simp), IccRightChart_apply]

/-- **The extended chart of `[0,1]` at a point of `[0,1)`**, as a formula valid at every point of
`[0,1]`: it is `z ↦ z`. -/
theorem extChartAt_Icc_lt {y : Icc (0 : ℝ) 1} (hy : (y : ℝ) < 1) (w : Icc (0 : ℝ) 1) :
    extChartAt (𝓡∂ 1) y w = WithLp.toLp 2 (fun _ : Fin 1 => (w : ℝ)) := by
  rw [extChartAt, OpenPartialHomeomorph.extend_coe]
  simp [Icc_chartedSpaceChartAt_of_le_top hy, IccLeftChart_apply]

/-- **The transition of `[0,1]` from a point of `[0,1)` to the right endpoint reverses
orientation**: read in the two charts it is the reflection `t ↦ 1 - t` of the model space, whose
derivative is `-1` at every point.  Both charts are given by formulas valid on the whole of `[0,1]`
(`Milnor.extChartAt_Icc_top`, `Milnor.extChartAt_Icc_lt`), so the factorisation of one through the
other holds everywhere and no neighbourhood has to be produced. -/
theorem mfd_extChartAt_Icc_top {y : Icc (0 : ℝ) 1} (hy : (y : ℝ) < 1) :
    mfd (𝓡∂ 1) 𝓘(ℝ, E1) (extChartAt (𝓡∂ 1) (⊤ : Icc (0 : ℝ) 1)) y
      = -ContinuousLinearMap.id ℝ E1 := by
  have hfd : HasFDerivAt (fun t : E1 => (WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ))) - t)
      (-ContinuousLinearMap.id ℝ E1) (extChartAt (𝓡∂ 1) y y) :=
    (hasFDerivAt_id (extChartAt (𝓡∂ 1) y y)).const_sub _
  have h2 := hfd.hasMFDerivAt.comp y (hasMFDerivAt_extChartAt_self y)
  have h3 : HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ, E1) (extChartAt (𝓡∂ 1) (⊤ : Icc (0 : ℝ) 1)) y
      ((-ContinuousLinearMap.id ℝ E1).comp (ContinuousLinearMap.id ℝ E1)) := by
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    show extChartAt (𝓡∂ 1) (⊤ : Icc (0 : ℝ) 1) z = _ - extChartAt (𝓡∂ 1) y z
    rw [extChartAt_Icc_top, extChartAt_Icc_lt hy]
    ext i
    simp
  rw [HasMFDerivAt.mfd_eq h3]
  exact ContinuousLinearMap.comp_id _

/-- A point of `[0,1]` which is not below `1` is the right endpoint. -/
theorem Icc_eq_top_of_not_lt {x : Icc (0 : ℝ) 1} (hx : ¬ (x : ℝ) < 1) : x = (⊤ : Icc (0 : ℝ) 1) := by
  refine Subtype.ext ?_
  have h1 : ((⊤ : Icc (0 : ℝ) 1) : ℝ) = 1 := by simp
  rw [h1]
  exact le_antisymm x.2.2 (not_lt.1 hx)

/-- **The orientation of the unit interval**: the reference orientation of the model space in the
left chart, its reverse at the right endpoint, where the chart is the reflected one. -/
def orIcc (z : Icc (0 : ℝ) 1) : Orientation ℝ E1 (Fin 1) :=
  if (z : ℝ) < 1 then refOr finrank_euclideanSpace_fin else -refOr finrank_euclideanSpace_fin

/-- **`Milnor.orIcc` is compatible with the charts.**  At a point of `[0,1)` the chart is the left
one at every nearby point too, so the transition is the identity and the two orientations are equal;
at the right endpoint the transition from the left chart is `-1` (`Milnor.mfd_extChartAt_Icc_top`)
and the two orientations are opposite, so the sign is again `1`. -/
theorem cont_orIcc (x : Icc (0 : ℝ) 1) : ∀ᶠ z in 𝓝 x,
    orSign (orIcc z) (orIcc x) (mfd (𝓡∂ 1) 𝓘(ℝ, E1) (extChartAt (𝓡∂ 1) x) z) = 1 := by
  by_cases hx : (x : ℝ) < 1
  · filter_upwards [(isOpen_lt continuous_subtype_val continuous_const).mem_nhds hx] with z hz
    have hch : (extChartAt (𝓡∂ 1) x : Icc (0 : ℝ) 1 → E1) = extChartAt (𝓡∂ 1) z :=
      congrArg (fun g : Icc (0 : ℝ) 1 → EuclideanHalfSpace 1 =>
          ((𝓡∂ 1) ∘ g : Icc (0 : ℝ) 1 → E1))
        (by rw [Icc_chartedSpaceChartAt_of_le_top hx, Icc_chartedSpaceChartAt_of_le_top hz])
    rw [orIcc, orIcc, if_pos hz, if_pos hx, hch, mfd_extChartAt_self]
    exact orSign_id _
  · have hxt : x = (⊤ : Icc (0 : ℝ) 1) := Icc_eq_top_of_not_lt hx
    subst hxt
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : (z : ℝ) < 1
    · rw [orIcc, orIcc, if_pos hz, if_neg hx, mfd_extChartAt_Icc_top hz,
        orSign_neg_right finrank_euclideanSpace_fin,
        orSign_neg_id_of_one finrank_euclideanSpace_fin]
      norm_num
    · have hzt : z = (⊤ : Icc (0 : ℝ) 1) := Icc_eq_top_of_not_lt hz
      subst hzt
      rw [mfd_extChartAt_self]
      exact orSign_id _

/-- **The unit interval is orientable.** -/
def orientIcc : Orient (𝓡∂ 1) (Icc (0 : ℝ) 1) 1 where
  or := orIcc
  cont := cont_orIcc

end Icc

/-- **The circle is orientable.**  The route is not through the stereographic charts of `Circle`
but through the unit sphere `S¹ ⊆ ℝ²` of Chapter 5, which Chapter 8 orients as the boundary of the
disk (`Milnor.Sphere.sphOrStd`).  `S¹` is itself a nonempty compact Hausdorff connected smooth
one-manifold with empty boundary, so Stage 7 of the Appendix
(`Milnor.OneManifold.Smooth.nonempty_diffeomorphCircle`) provides a diffeomorphism `S¹ → Circle`,
and orientability travels along it.

This is cheaper than either of the two direct routes -- computing the derivative of the transition
between the two stereographic charts of `Circle`, or descending the orientation of the line along
the periodic parametrisation of `Milnor/Appendix/Smooth/Circle.lean` -- because the sphere is
already oriented and the classification is already proved. -/
theorem isOrientable_circle : IsOrientable (𝓡 1) Circle 1 := by
  have : PreconnectedSpace (Sphere.Sph 1) := Sphere.preconnectedSpace one_pos
  obtain ⟨Φ⟩ := nonempty_diffeomorphCircle (M := Sphere.Sph 1)
    𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) finrank_euclideanSpace_fin
    ModelWithCorners.Boundaryless.boundary_eq_empty
  exact IsOrientable.of_diffeomorph finrank_euclideanSpace_fin finrank_euclideanSpace_fin
    (Sphere.sphOrStd 1).isOrientable Φ.symm

/-- **All four models of the classification of one-manifolds are orientable**: the circle
(`Milnor.isOrientable_circle`), the unit interval (`Milnor.orientIcc`), the closed half-line
(`Milnor.orientIci`) and the line (`Milnor.orientReal`).  This is the counterpart of
`Milnor.OneManifold.Smooth.models_pairwise_not_diffeomorph`, and it is what makes the classification
say that every connected one-manifold is orientable. -/
theorem isOrientable_models :
    IsOrientable (𝓡 1) Circle 1 ∧ IsOrientable (𝓡∂ 1) (Icc (0 : ℝ) 1) 1 ∧
      IsOrientable (𝓡∂ 1) (Ici (0 : ℝ)) 1 ∧ IsOrientable 𝓘(ℝ, ℝ) ℝ 1 :=
  ⟨isOrientable_circle, orientIcc.isOrientable, orientIci.isOrientable, orientReal.isOrientable⟩

end Models

/-! ### Connected one-manifolds are orientable -/

section OneManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] {m : ℕ}

/-- **Every connected `σ`-compact Hausdorff smooth one-manifold without boundary is orientable.**

By Milnor's Appendix (`Milnor.OneManifold.Smooth.nonempty_diffeomorph_cases`) such a manifold is
diffeomorphic to `Circle` if it is compact and to `ℝ` if it is not -- the two other models,
`Icc (0 : ℝ) 1` and `Ici (0 : ℝ)`, are excluded because the boundary of `M` is empty, the model `I`
being boundaryless.  Both `Circle` (`Milnor.isOrientable_circle`) and `ℝ` (`Milnor.orientReal`) are
orientable, and orientability travels back along the diffeomorphism. -/
theorem isOrientable_of_finrank_eq_one (hE : finrank ℝ E = 1) : IsOrientable I M 1 := by
  have hb : I.boundary M = ∅ := ModelWithCorners.Boundaryless.boundary_eq_empty
  obtain ⟨h1, -, -, h4⟩ := OneManifold.Smooth.nonempty_diffeomorph_cases (M := M) I hE
  by_cases hc : CompactSpace M
  · exact IsOrientable.of_diffeomorph hE finrank_euclideanSpace_fin isOrientable_circle
      (h1 hc hb).some
  · exact IsOrientable.of_diffeomorph hE (by simp) orientReal.isOrientable (h4 hc hb).some

/-- **A connected non-orientable manifold has dimension at least two.**  This is the statement
Milnor's mod `2` theorem needs: the hypothesis `2 ≤ m` of `Milnor.Framed.hopf_homotopic_mod2` and
its companions follows from the non-orientability of a connected `M`, so it need not be assumed.

Dimension `0` is orientable for trivial reasons (`Milnor.Orient.ofZero`: in dimension `0` every
linear map preserves every orientation), and dimension `1` by
`Milnor.isOrientable_of_finrank_eq_one`. -/
theorem two_le_of_not_isOrientable (hE : finrank ℝ E = m) (h : ¬ IsOrientable I M m) : 2 ≤ m := by
  by_contra hm
  rw [not_le] at hm
  interval_cases m
  · exact h (Orient.ofZero hE).isOrientable
  · exact h (isOrientable_of_finrank_eq_one hE)

end OneManifold

/-! ### The form Chapter 7 uses -/

section Slice

/-- **A compact connected non-orientable submanifold of a Euclidean space has dimension at least
two.**  This is `Milnor.two_le_of_not_isOrientable` in the vocabulary of Chapters 7 and 8, where a
manifold is a compact slice submanifold `M` of some `ℝᴷ⁺¹` charted on `ℝᵐ`.  All the hypotheses the
classification of one-manifolds needs are free there: `M` is Hausdorff because it is a subspace of a
metric space, `σ`-compact because it is compact, and its boundary is empty because its model
`𝓘(ℝ, ℝᵐ)` is boundaryless. -/
theorem two_le_of_not_isOrientable_slice {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
    (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin w)) M) (hMc : IsCompact M)
    (hconn : letI := hM.chartedSpace; ConnectedSpace M)
    (hnor : letI := hM.chartedSpace; ¬ IsOrientable 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m) :
    2 ≤ m := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI := hconn
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  exact two_le_of_not_isOrientable finrank_euclideanSpace_fin hnor

end Slice

end Milnor
