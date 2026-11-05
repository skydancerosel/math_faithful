import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §1.

# The inverse function theorem on manifolds

Milnor states (p. 4): *If the derivative `dfₓ : ℝᵏ → ℝᵏ` is nonsingular, then `f` maps any
sufficiently small open set `U'` about `x` diffeomorphically onto an open set `f(U')`.*
He cites Apostol/Dieudonné for the Euclidean case and then uses the manifold case freely
(p. 7: "it follows from the inverse function theorem that `f` maps a neighborhood of `x` in `M`
diffeomorphically onto an open set in `N`").

Mathlib has the Euclidean case (`ContDiffAt.toOpenPartialHomeomorph`) but, as of v4.33.1,
lists the manifold case as a TODO in `Mathlib.Geometry.Manifold.LocalDiffeomorph`.
This file proves it.

## Statement

For `f : M → N` between `C^n` manifolds without boundary (`n ≠ 0`), if `f` is `C^n` on a
neighbourhood of `x` and `mfderiv I J f x` is invertible, then `f` is a `C^n` local
diffeomorphism at `x`.

## A subtlety worth recording for the prose version

We assume `f` is `C^n` *on a neighbourhood* of `x`, not merely *at* `x`. For finite `n` and
for `n = ω` the two are equivalent (`ContMDiffAt.eventually`), but for `n = ∞` Mathlib's
`ContMDiffAt ∞ f x` means "for every `k`, `C^k` on some neighbourhood depending on `k`", and
that does *not* give `C^∞` on any single neighbourhood. Since a local diffeomorphism is
`C^∞` on a whole open set, the neighbourhood hypothesis is genuinely needed in that case.
For Milnor, whose maps are smooth everywhere, this costs nothing (see
`ContMDiff.isLocalDiffeomorphAt_of_isInvertible_mfderiv`).
-/

open Set Filter Topology Manifold ContDiff

noncomputable section

namespace Milnor

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞}

/-! ### Step 1: reading `f` in the preferred charts around `x` and `f x`. -/

section charts

variable [I.Boundaryless] [J.Boundaryless] [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {x : M}

omit [CompleteSpace E] [J.Boundaryless] in
/-- If `f` is `C^n` at every point near `x`, then `f` written in the extended charts at `x`
and `f x` is `C^n` at every point near `extChartAt I x x`. -/
theorem eventually_contDiffAt_writtenInExtChartAt
    (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt I J n f y) :
    ∀ᶠ u in 𝓝 (extChartAt I x x), ContDiffAt 𝕜 n (writtenInExtChartAt I J x f) u := by
  rw [← map_extChartAt_nhds_of_boundaryless x, eventually_map]
  have h1 : (extChartAt I x).source ∈ 𝓝 x := extChartAt_source_mem_nhds x
  have h2 : f ⁻¹' (extChartAt J (f x)).source ∈ 𝓝 x := by
    have hc : ContinuousAt f x := hf.self_of_nhds.continuousAt
    exact hc.preimage_mem_nhds (extChartAt_source_mem_nhds (f x))
  filter_upwards [hf, h1, h2] with y hy hy1 hy2
  rw [extChartAt_source] at hy1
  rw [mem_preimage, extChartAt_source] at hy2
  have := (contMDiffAt_iff_of_mem_source (I := I) (I' := J) (n := n) hy1 hy2).1 hy
  rw [I.range_eq_univ, contDiffWithinAt_univ] at this
  exact this.2

omit [CompleteSpace E] [J.Boundaryless] in
/-- The derivative of `f` written in charts at `extChartAt I x x` is `mfderiv I J f x`. -/
theorem hasFDerivAt_writtenInExtChartAt (hf : MDifferentiableAt I J f x) :
    HasFDerivAt (writtenInExtChartAt I J x f) (mfderiv I J f x) (extChartAt I x x) := by
  have hd := hf.differentiableWithinAt_writtenInExtChartAt
  rw [I.range_eq_univ, differentiableWithinAt_univ] at hd
  have := hd.hasFDerivAt
  rwa [hf.mfderiv, I.range_eq_univ, fderivWithin_univ]

end charts

/-! ### Step 2: a Euclidean lemma. -/

/-- If `g : E → F` is `C^n` (`n ≠ 0`) near `a` and `fderiv 𝕜 g a` is invertible, then
`fderiv 𝕜 g u` is invertible for all `u` near `a`. -/
theorem eventually_isInvertible_fderiv {g : E → F} {a : E}
    (hg : ContDiffAt 𝕜 n g a) (hn : n ≠ 0) (h : (fderiv 𝕜 g a).IsInvertible) :
    ∀ᶠ u in 𝓝 a, (fderiv 𝕜 g u).IsInvertible := by
  obtain ⟨u, hu, hgu⟩ := hg.contDiffOn (m := 1) (ENat.one_le_iff_ne_zero_withTop.mpr hn) (by simp)
  obtain ⟨v, hvu, hv, hav⟩ := mem_nhds_iff.1 hu
  have hcont : ContinuousAt (fderiv 𝕜 g) a :=
    ((hgu.mono hvu).continuousOn_fderiv_of_isOpen hv le_rfl).continuousAt (hv.mem_nhds hav)
  obtain ⟨e, he⟩ := h
  have hmem : range ((↑) : (E ≃L[𝕜] F) → E →L[𝕜] F) ∈ 𝓝 (fderiv 𝕜 g a) := by
    rw [← he]; exact ContinuousLinearEquiv.nhds e
  filter_upwards [hcont.preimage_mem_nhds hmem] with u hu
  obtain ⟨e', he'⟩ := hu
  exact ⟨e', he'⟩

/-! ### Step 3: the theorem. -/

section main

variable [I.Boundaryless] [J.Boundaryless] [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {x : M}

/-- **Inverse function theorem on manifolds.** If `f : M → N` is `C^n` (`n ≠ 0`) on a
neighbourhood of `x` and `mfderiv I J f x` is invertible, then `f` is a `C^n` local
diffeomorphism at `x`. -/
theorem isLocalDiffeomorphAt_of_isInvertible_mfderiv
    (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt I J n f y) (hn : n ≠ 0)
    (h : (mfderiv I J f x).IsInvertible) :
    IsLocalDiffeomorphAt I J n f x := by
  -- Notation for the charts and for `f` in charts.
  set φ := extChartAt I x with hφ
  set ψ := extChartAt J (f x) with hψ
  set g := writtenInExtChartAt I J x f with hg_def
  have hg_apply : ∀ u, g u = ψ (f (φ.symm u)) := fun u => rfl
  -- `g` is `C^n` near `φ x` with invertible derivative there.
  have hgnhds : ∀ᶠ u in 𝓝 (φ x), ContDiffAt 𝕜 n g u :=
    eventually_contDiffAt_writtenInExtChartAt hf
  have hgx : ContDiffAt 𝕜 n g (φ x) := hgnhds.self_of_nhds
  have hmd : MDifferentiableAt I J f x := hf.self_of_nhds.mdifferentiableAt hn
  have hderiv : HasFDerivAt g (mfderiv I J f x) (φ x) := hasFDerivAt_writtenInExtChartAt hmd
  obtain ⟨e₀, he₀⟩ := h
  let e : E ≃L[𝕜] F := e₀
  have he : (e : E →L[𝕜] F) = mfderiv I J f x := he₀
  have hderiv' : HasFDerivAt g (e : E →L[𝕜] F) (φ x) := he ▸ hderiv
  have hinv : (fderiv 𝕜 g (φ x)).IsInvertible := ⟨e, by rw [hderiv'.fderiv]⟩
  -- The Euclidean inverse function theorem.
  let Φ : OpenPartialHomeomorph E F := hgx.toOpenPartialHomeomorph g hderiv' hn
  have hΦ : (Φ : E → F) = g := rfl
  have hxΦ : φ x ∈ Φ.source := hgx.mem_toOpenPartialHomeomorph_source hderiv' hn
  -- The set `T ⊆ M` of good points near `x`, and its image `V ⊆ E`.
  let T : Set M := interior {y | ContMDiffAt I J n f y ∧ f y ∈ ψ.source} ∩ φ.source
  have hT_open : IsOpen T := isOpen_interior.inter (isOpen_extChartAt_source x)
  have hxT : x ∈ T := by
    refine ⟨mem_interior_iff_mem_nhds.2 ?_, mem_extChartAt_source x⟩
    have hc : ContinuousAt f x := hf.self_of_nhds.continuousAt
    exact hf.and (hc.preimage_mem_nhds (extChartAt_source_mem_nhds (f x)))
  have hT_good : ∀ y ∈ T, ContMDiffAt I J n f y ∧ f y ∈ ψ.source := fun y hy => by
    have h := interior_subset hy.1
    exact h
  have hT_src : T ⊆ φ.source := fun _ hy => hy.2
  -- `U ⊆ E`: an open neighbourhood of `φ x` where everything is fine.
  have hU : ∀ᶠ u in 𝓝 (φ x), ContDiffAt 𝕜 n g u ∧ (fderiv 𝕜 g u).IsInvertible ∧
      u ∈ Φ.source ∧ u ∈ φ.target ∧ φ.symm u ∈ T := by
    have h1 : ∀ᶠ u in 𝓝 (φ x), (fderiv 𝕜 g u).IsInvertible :=
      eventually_isInvertible_fderiv hgx hn hinv
    have h2 : ∀ᶠ u in 𝓝 (φ x), u ∈ Φ.source := Φ.open_source.mem_nhds hxΦ
    have h3 : ∀ᶠ u in 𝓝 (φ x), u ∈ φ.target := extChartAt_target_mem_nhds x
    have h4 : ∀ᶠ u in 𝓝 (φ x), φ.symm u ∈ T := by
      have hT' : T ∈ 𝓝 (φ.symm (φ x)) := by
        rw [hφ, extChartAt_to_inv]; exact hT_open.mem_nhds hxT
      exact (continuousAt_extChartAt_symm (I := I) x).preimage_mem_nhds hT'
    filter_upwards [hgnhds, h1, h2, h3, h4] with u hu1 hu2 hu3 hu4 hu5
    exact ⟨hu1, hu2, hu3, hu4, hu5⟩
  obtain ⟨V, hVsub, hV_open, hxV⟩ := mem_nhds_iff.1 hU
  have hV : ∀ u ∈ V, ContDiffAt 𝕜 n g u ∧ (fderiv 𝕜 g u).IsInvertible ∧
      u ∈ Φ.source ∧ u ∈ φ.target ∧ φ.symm u ∈ T := fun u hu => hVsub hu
  have hVΦ : V ⊆ Φ.source := fun u hu => (hV u hu).2.2.1
  have hVφ : V ⊆ φ.target := fun u hu => (hV u hu).2.2.2.1
  -- The source `S ⊆ M` and target `S' ⊆ N` of our partial diffeomorphism.
  let S : Set M := φ.source ∩ φ ⁻¹' V
  let S' : Set N := ψ.source ∩ ψ ⁻¹' (Φ '' V)
  have hS_open : IsOpen S :=
    (continuousOn_extChartAt x).isOpen_inter_preimage (isOpen_extChartAt_source x) hV_open
  have hΦV_open : IsOpen (Φ '' V) := (Φ.isOpen_image_iff_of_subset_source hVΦ).2 hV_open
  have hS'_open : IsOpen S' :=
    (continuousOn_extChartAt (f x)).isOpen_inter_preimage
      (isOpen_extChartAt_source (f x)) hΦV_open
  -- Key identities.
  have key1 : ∀ y ∈ S, φ.symm (φ y) = y := fun y hy => φ.left_inv hy.1
  have key2 : ∀ y ∈ S, ψ (f y) = Φ (φ y) := fun y hy => by
    rw [hΦ, hg_apply, key1 y hy]
  have key3 : ∀ y ∈ S, f y ∈ ψ.source := fun y hy => by
    have := (hV _ hy.2).2.2.2.2
    rw [key1 y hy] at this
    exact (hT_good y this).2
  have key4 : ∀ u ∈ V, f (φ.symm u) = ψ.symm (Φ u) := fun u hu => by
    rw [hΦ, hg_apply, ψ.left_inv (hT_good _ (hV u hu).2.2.2.2).2]
  have key5 : ∀ u ∈ V, φ.symm u ∈ S := fun u hu =>
    ⟨φ.map_target (hVφ hu), by simpa [S, φ.right_inv (hVφ hu)] using hu⟩
  -- Build the partial diffeomorphism.
  let Ψ : PartialDiffeomorph I J M N n :=
    { toFun := f
      invFun := φ.symm ∘ Φ.symm ∘ ψ
      source := S
      target := S'
      map_source' := fun y hy => by
        refine ⟨key3 y hy, ?_⟩
        rw [mem_preimage, key2 y hy]
        exact mem_image_of_mem _ hy.2
      map_target' := fun z hz => by
        obtain ⟨u, hu, hzu⟩ := hz.2
        simp only [Function.comp_apply]
        rw [← hzu, Φ.left_inv (hVΦ hu)]
        exact key5 u hu
      left_inv' := fun y hy => by
        simp only [Function.comp_apply]
        rw [key2 y hy, Φ.left_inv (hVΦ hy.2), key1 y hy]
      right_inv' := fun z hz => by
        have hz1 : z ∈ ψ.source := mem_of_mem_inter_left hz
        obtain ⟨u, hu, hzu⟩ := hz.2
        simp only [Function.comp_apply]
        rw [← hzu, Φ.left_inv (hVΦ hu), key4 u hu, hzu, ψ.left_inv hz1]
      open_source := hS_open
      open_target := hS'_open
      contMDiffOn_toFun := fun y hy => by
        have := (hV _ hy.2).2.2.2.2
        rw [key1 y hy] at this
        exact (hT_good y this).1.contMDiffWithinAt
      contMDiffOn_invFun := by
        -- `ψ` is `C^n` on `S' ⊆ ψ.source`.
        have h1 : ContMDiffOn J 𝓘(𝕜, F) n ψ S' :=
          (contMDiffOn_extChartAt (n := n)).mono fun z hz => by
            have h : z ∈ ψ.source := mem_of_mem_inter_left hz
            rw [hψ, extChartAt_source] at h
            exact h
        -- `Φ.symm` is `C^n` on `Φ '' V`.
        have h2 : ContMDiffOn 𝓘(𝕜, F) 𝓘(𝕜, E) n Φ.symm (Φ '' V) := by
          rw [contMDiffOn_iff_contDiffOn]
          intro w hw
          obtain ⟨u, hu, rfl⟩ := hw
          obtain ⟨hgu, ⟨e', he'⟩, huΦ, -, -⟩ := hV u hu
          have hdu : HasFDerivAt g (e' : E →L[𝕜] F) u := by
            rw [he']; exact (hgu.differentiableAt hn).hasFDerivAt
          have hsymm : Φ.symm (Φ u) = u := Φ.left_inv huΦ
          have hd' : HasFDerivAt Φ (e' : E →L[𝕜] F) (Φ.symm (Φ u)) := by rw [hsymm]; exact hdu
          have hg' : ContDiffAt 𝕜 n Φ (Φ.symm (Φ u)) := by rw [hsymm]; exact hgu
          exact (Φ.contDiffAt_symm (Φ.map_source huΦ) hd' hg').contDiffWithinAt
        -- `φ.symm` is `C^n` on `V ⊆ φ.target`.
        have h3 : ContMDiffOn 𝓘(𝕜, E) I n φ.symm V :=
          (contMDiffOn_extChartAt_symm x).mono hVφ
        have m1 : MapsTo ψ S' (Φ '' V) := fun z hz => hz.2
        have m2 : MapsTo Φ.symm (Φ '' V) V := fun w hw => by
          obtain ⟨u, hu, rfl⟩ := hw
          rw [Φ.left_inv (hVΦ hu)]; exact hu
        exact (h3.comp h2 m2).comp h1 m1 }
  have hxS : x ∈ S := ⟨mem_extChartAt_source x, hxV⟩
  exact ⟨Ψ, hxS, fun y _ => rfl⟩

/-- Milnor's form of the statement: a smooth map with invertible derivative at `x` is a local
diffeomorphism at `x`. -/
theorem ContMDiff.isLocalDiffeomorphAt_of_isInvertible_mfderiv
    (hf : ContMDiff I J n f) (hn : n ≠ 0) (h : (mfderiv I J f x).IsInvertible) :
    IsLocalDiffeomorphAt I J n f x :=
  Milnor.isLocalDiffeomorphAt_of_isInvertible_mfderiv (Eventually.of_forall fun y => hf y) hn h

/-- Pointwise version, valid for `n ≠ ∞` (finite regularity or analytic). -/
theorem ContMDiffAt.isLocalDiffeomorphAt_of_isInvertible_mfderiv
    (hf : ContMDiffAt I J n f x) (hn : n ≠ 0) (hn' : n ≠ ∞)
    (h : (mfderiv I J f x).IsInvertible) :
    IsLocalDiffeomorphAt I J n f x :=
  Milnor.isLocalDiffeomorphAt_of_isInvertible_mfderiv
    ((contMDiffAt_iff_contMDiffAt_nhds hn').1 hf) hn h

end main

end Milnor
