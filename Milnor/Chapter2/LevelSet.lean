import Milnor.Chapter2.Submanifold
import Milnor.Chapter2.Brown
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §2, Lemmas 1 and 2 (pp. 11–12).

# The preimage of a regular value is a submanifold

> **Lemma 1.** If `f : M → N` is a smooth map between manifolds of dimension `m ≥ n`, and if
> `y ∈ N` is a regular value, then the set `f⁻¹(y) ⊆ M` is a smooth manifold of dimension `m - n`.
>
> *Proof.* Let `x ∈ f⁻¹(y)`. Since `y` is a regular value, the derivative `dfₓ` must map `TMₓ`
> onto `TN_y`. The null space `𝒩 ⊆ TMₓ` of `dfₓ` will therefore be an `(m-n)`-dimensional vector
> space. If `M ⊆ ℝᵏ`, choose a linear map `L : ℝᵏ → ℝᵐ⁻ⁿ` that is nonsingular on this subspace
> `𝒩 ⊆ TMₓ ⊆ ℝᵏ`. Now define `F : M → N × ℝᵐ⁻ⁿ` by `F(ξ) = (f(ξ), L(ξ))`. The derivative `dFₓ` is
> clearly given by the formula `dFₓ(v) = (dfₓ(v), L(v))`. Thus `dFₓ` is nonsingular. Hence `F`
> maps some neighborhood `U` of `x` diffeomorphically onto a neighborhood `V` of `(y, L(x))`. Note
> that `f⁻¹(y)` corresponds, under `F`, to the hyperplane `y × ℝᵐ⁻ⁿ ∩ V`. This proves that
> `f⁻¹(y)` is a smooth manifold of dimension `m - n`.
>
> **Lemma 2.** The null space of `dfₓ : TMₓ → TN_y` is precisely equal to the tangent space
> `TM'ₓ ⊆ TMₓ` of the submanifold `M' = f⁻¹(y)`.

For abstract manifolds we read `f` in charts `φ` at `x` and `ψ` at `y`: `F̃ = ψ ∘ f ∘ φ⁻¹` has
surjective derivative `D` at `φ x`, with kernel `𝒩` of dimension `m - n`. We fix a model space
`Z` of dimension `m - n`, an isomorphism `ι : 𝒩 ≅ Z`, a projection `E → 𝒩`, and put
`L = ι ∘ proj`. Milnor's `F` becomes `Φ(p) = (L(φ p), ψ(f p) - ψ(y)) : M → Z × F`, whose
derivative at `x` is `(L, D) ∘ dφₓ`, invertible. The inverse function theorem of chapter 1 makes
`Φ` a slice chart in the sense of `Milnor.SliceChart`, with `f⁻¹(y)` corresponding to
`Z × {0}`. The general construction of `Milnor.Chapter2.Submanifold` then gives the manifold
structure (`Lemma 1`), and Lemma 2 follows from the chain rule applied to `f ∘ incl = const` and
`(fst ∘ Φ) ∘ incl = chart`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [I.Boundaryless] [J.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {f : M → N}

/-! ### Derivatives of charts are invertible -/

/-- The derivative of an extended chart, at a point of its source, is invertible (its inverse is
the derivative of the inverse chart). -/
theorem isInvertible_mfderiv_extChartAt {x p : M} (hp : p ∈ (extChartAt I x).source) :
    (mfderiv I 𝓘(ℝ, E) (extChartAt I x) p).IsInvertible := by
  set φ := extChartAt I x with hφ
  have hφ' : MDifferentiableAt I 𝓘(ℝ, E) φ p :=
    mdifferentiableAt_extChartAt (by rwa [extChartAt_source] at hp)
  have hφs : MDifferentiableAt 𝓘(ℝ, E) I φ.symm (φ p) :=
    mdifferentiableOn_extChartAt_symm.mdifferentiableAt
      ((isOpen_extChartAt_target x).mem_nhds (φ.map_source hp))
  have hL : mfderiv I I (φ.symm ∘ φ) p =
      (mfderiv 𝓘(ℝ, E) I φ.symm (φ p)).comp (mfderiv I 𝓘(ℝ, E) φ p) := mfderiv_comp p hφs hφ'
  have hLid : mfderiv I I (φ.symm ∘ φ) p = mfderiv I I id p := by
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards [(isOpen_extChartAt_source x).mem_nhds hp] with z hz
    exact φ.left_inv hz
  rw [mfderiv_id] at hLid
  have hφ'' : MDifferentiableAt I 𝓘(ℝ, E) φ (φ.symm (φ p)) := by
    rw [φ.left_inv hp]; exact hφ'
  have hR : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ ∘ φ.symm) (φ p) =
      (mfderiv I 𝓘(ℝ, E) φ p).comp (mfderiv 𝓘(ℝ, E) I φ.symm (φ p)) := by
    have := mfderiv_comp (φ p) hφ'' hφs
    rwa [φ.left_inv hp] at this
  have hRid : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ ∘ φ.symm) (φ p) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id (φ p) := by
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds (φ.map_source hp)] with z hz
    exact φ.right_inv hz
  rw [mfderiv_id] at hRid
  refine ⟨ContinuousLinearEquiv.equivOfInverse (mfderiv I 𝓘(ℝ, E) φ p)
    (mfderiv 𝓘(ℝ, E) I φ.symm (φ p) : TangentSpace 𝓘(ℝ, E) (φ p) →L[ℝ] TangentSpace I p)
    (fun v => DFunLike.congr_fun (hL.symm.trans hLid) v)
    (fun w => DFunLike.congr_fun (hR.symm.trans hRid) w), rfl⟩

/-- The derivative of the inverse of an extended chart is surjective. -/
theorem surjective_mfderiv_extChartAt_symm {x p : M} (hp : p ∈ (extChartAt I x).source) :
    Surjective (mfderiv 𝓘(ℝ, E) I (extChartAt I x).symm (extChartAt I x p)) := by
  set φ := extChartAt I x with hφ
  have hφ' : MDifferentiableAt I 𝓘(ℝ, E) φ p :=
    mdifferentiableAt_extChartAt (by rwa [extChartAt_source] at hp)
  have hφs : MDifferentiableAt 𝓘(ℝ, E) I φ.symm (φ p) :=
    mdifferentiableOn_extChartAt_symm.mdifferentiableAt
      ((isOpen_extChartAt_target x).mem_nhds (φ.map_source hp))
  have hL : mfderiv I I (φ.symm ∘ φ) p =
      (mfderiv 𝓘(ℝ, E) I φ.symm (φ p)).comp (mfderiv I 𝓘(ℝ, E) φ p) := mfderiv_comp p hφs hφ'
  have hLid : mfderiv I I (φ.symm ∘ φ) p = mfderiv I I id p := by
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards [(isOpen_extChartAt_source x).mem_nhds hp] with z hz
    exact φ.left_inv hz
  rw [mfderiv_id] at hLid
  intro v
  exact ⟨mfderiv I 𝓘(ℝ, E) φ p v, DFunLike.congr_fun (hL.symm.trans hLid) v⟩

/-! ### Lemma 1 -/

/-- The construction in **Milnor's Lemma 1** (p. 11): around each point `x` of `f⁻¹(y)`, `y` a
regular value, there is a slice chart `Φ` whose second component is `ψ ∘ f - ψ y` for the chart
`ψ` of `N` at `y`. -/
theorem exists_sliceChart_preimage {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (hZ : finrank ℝ Z + finrank ℝ F = finrank ℝ E)
    (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y) {x : M} (hx : x ∈ f ⁻¹' {y}) :
    ∃ σ : SliceChart I Z F (f ⁻¹' {y}), x ∈ σ.φ.source ∧
      ∀ p ∈ σ.φ.source, (σ.φ p).2 = extChartAt J y (f p) - extChartAt J y y := by
  have hfx : f x = y := hx
  have := FiniteDimensional.complete ℝ E
  set φ := extChartAt I x with hφ
  set ψ := extChartAt J y with hψ
  have hxφ : x ∈ φ.source := mem_extChartAt_source x
  have hyψ : y ∈ ψ.source := mem_extChartAt_source y
  have hxx : φ.symm (φ x) = x := φ.left_inv hxφ
  -- `f` in charts, and its derivative `D` at `φ x`.
  set Ft : E → F := ψ ∘ f ∘ φ.symm with hFt_def
  set U₀ : Set E := φ.target ∩ φ.symm ⁻¹' (f ⁻¹' ψ.source) with hU₀_def
  have hU₀ : IsOpen U₀ :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x)
      (hf.continuous.isOpen_preimage _ (isOpen_extChartAt_source y))
  have hFt : ContDiffOn ℝ ∞ Ft U₀ := by
    have := (contMDiffOn_iff.1 (hf.contMDiffOn (s := univ))).2 x y
    rwa [univ_inter] at this
  have hxU₀ : φ x ∈ U₀ := by
    refine ⟨φ.map_source hxφ, ?_⟩
    show f (φ.symm (φ x)) ∈ ψ.source
    rw [hxx, hfx]
    exact hyψ
  set D := fderiv ℝ Ft (φ x) with hD_def
  have hFt_at : HasFDerivAt Ft D (φ x) :=
    ((hFt.contDiffAt (hU₀.mem_nhds hxU₀)).differentiableAt (by simp)).hasFDerivAt
  -- `D` is surjective: chain rule `dF̃ = dψ ∘ df ∘ d(φ⁻¹)` with `dψ`, `df`, `d(φ⁻¹)` surjective.
  have hD : Surjective D := by
    have hφ' : MDifferentiableAt 𝓘(ℝ, E) I φ.symm (φ x) :=
      mdifferentiableOn_extChartAt_symm.mdifferentiableAt
        ((isOpen_extChartAt_target x).mem_nhds (φ.map_source hxφ))
    have hf' : MDifferentiableAt I J f (φ.symm (φ x)) := by
      rw [hxx]; exact hf.mdifferentiableAt (by simp)
    have hψ' : MDifferentiableAt J 𝓘(ℝ, F) ψ (f (φ.symm (φ x))) := by
      rw [hxx, hfx]; exact mdifferentiableAt_extChartAt (by rwa [extChartAt_source] at hyψ)
    have hchain : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) Ft (φ x) =
        (mfderiv J 𝓘(ℝ, F) ψ (f (φ.symm (φ x)))).comp
          ((mfderiv I J f (φ.symm (φ x))).comp (mfderiv 𝓘(ℝ, E) I φ.symm (φ x))) := by
      rw [mfderiv_comp (φ x) hψ' (hf'.comp (φ x) hφ'), mfderiv_comp (φ x) hf' hφ']
      rfl
    have hD_eq : D = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) Ft (φ x) := mfderiv_eq_fderiv.symm
    rw [hD_eq, hchain]
    have h1 : Surjective (mfderiv J 𝓘(ℝ, F) ψ (f (φ.symm (φ x)))) := by
      rw [hxx, hfx]
      obtain ⟨e, he⟩ := isInvertible_mfderiv_extChartAt (I := J) (x := y) hyψ
      rw [← he]
      exact e.surjective
    have h2 : Surjective (mfderiv I J f (φ.symm (φ x))) := by
      rw [hxx]; exact hy x hfx
    have h3 : Surjective (mfderiv 𝓘(ℝ, E) I φ.symm (φ x)) :=
      surjective_mfderiv_extChartAt_symm hxφ
    exact h1.comp (h2.comp h3)
  -- The kernel `𝒩` of `D`, an isomorphism `𝒩 ≅ Z`, and the map `L = ι ∘ proj`.
  set Nk : Submodule ℝ E := LinearMap.ker (D : E →ₗ[ℝ] F) with hNk_def
  have hNk : finrank ℝ Nk = finrank ℝ Z := by
    have h := LinearMap.finrank_range_add_finrank_ker (D : E →ₗ[ℝ] F)
    rw [LinearMap.range_eq_top.2 hD, finrank_top, ← hNk_def] at h
    omega
  let ι : Nk ≃L[ℝ] Z := ContinuousLinearEquiv.ofFinrankEq hNk
  obtain ⟨C, hC⟩ := Nk.exists_isCompl
  let proj : E →ₗ[ℝ] Nk := Nk.projectionOnto C hC
  let L : E →L[ℝ] Z := (ι : Nk →L[ℝ] Z).comp (LinearMap.toContinuousLinearMap proj)
  have hL_ker : ∀ v (hv : v ∈ Nk), L v = ι ⟨v, hv⟩ := fun v hv => by
    simp only [L, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
      ContinuousLinearEquiv.coe_coe]
    congr 1
    exact Submodule.projectionOnto_apply_left hC ⟨v, hv⟩
  -- `(L, D) : E → Z × F` is an isomorphism.
  have hinj : Injective (L.prod D) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hDv : D v = 0 := congrArg Prod.snd hv
    have hvN : v ∈ Nk := by simpa [hNk_def, LinearMap.mem_ker] using hDv
    have hLv : L v = 0 := congrArg Prod.fst hv
    rw [hL_ker v hvN] at hLv
    have : (⟨v, hvN⟩ : Nk) = 0 := ι.injective (by simpa using hLv)
    simpa using congrArg Subtype.val this
  have hsurj : Surjective (L.prod D) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (L.prod D : E →ₗ[ℝ] Z × F)) (by rw [Module.finrank_prod, hZ])).1 hinj
  let e : E ≃L[ℝ] Z × F :=
    (LinearEquiv.ofBijective (L.prod D : E →ₗ[ℝ] Z × F) ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] Z × F) = L.prod D := by ext v <;> rfl
  -- Milnor's map `F`, here `Φ p = (L (φ p), ψ (f p) - ψ y)`.
  set Φ : M → Z × F := fun p => (L (φ p), ψ (f p) - ψ y) with hΦ_def
  set U₁ : Set M := φ.source ∩ f ⁻¹' ψ.source with hU₁_def
  have hU₁ : IsOpen U₁ :=
    (isOpen_extChartAt_source x).inter (hf.continuous.isOpen_preimage _ (isOpen_extChartAt_source y))
  have hxU₁ : x ∈ U₁ := ⟨hxφ, by show f x ∈ ψ.source; rw [hfx]; exact hyψ⟩
  have hΦ_smooth : ContMDiffOn I 𝓘(ℝ, Z × F) ∞ Φ U₁ := by
    refine ContMDiffOn.prodMk_space ?_ ?_
    · refine L.contDiff.contMDiff.comp_contMDiffOn ?_
      refine (contMDiffOn_extChartAt (n := ∞)).mono ?_
      rw [← extChartAt_source (I := I)]
      exact inter_subset_left
    · refine ((contDiff_id.sub contDiff_const).contMDiff (n := ∞)).comp_contMDiffOn ?_
      refine (contMDiffOn_extChartAt (n := ∞)).comp hf.contMDiffOn ?_
      intro p hp
      rw [← extChartAt_source (I := J)]
      exact hp.2
  -- Its derivative at `x` is `(L, D) ∘ dφₓ`, which is invertible.
  have hΦ_deriv : mfderiv I 𝓘(ℝ, Z × F) Φ x = (L.prod D).comp (mfderiv I 𝓘(ℝ, E) φ x) := by
    set Φ₀ : E → Z × F := fun u => (L u, Ft u - ψ y) with hΦ₀_def
    have hΦ₀ : HasFDerivAt Φ₀ (L.prod D) (φ x) := L.hasFDerivAt.prodMk (hFt_at.sub_const _)
    have heq : Φ =ᶠ[𝓝 x] Φ₀ ∘ φ := by
      filter_upwards [(isOpen_extChartAt_source x).mem_nhds hxφ] with p hp
      simp only [hΦ_def, hΦ₀_def, Function.comp_apply, hFt_def, φ.left_inv hp]
    rw [heq.mfderiv_eq, mfderiv_comp x hΦ₀.differentiableAt.mdifferentiableAt
      (mdifferentiableAt_extChartAt (mem_chart_source H x)), mfderiv_eq_fderiv, hΦ₀.fderiv]
    rfl
  have hΦ_inv : (mfderiv I 𝓘(ℝ, Z × F) Φ x).IsInvertible := by
    rw [hΦ_deriv]
    obtain ⟨eφ, heφ⟩ := isInvertible_mfderiv_extChartAt (I := I) (x := x) hxφ
    refine ⟨eφ.trans e, ?_⟩
    rw [← heφ, ← he]
    rfl
  -- The inverse function theorem makes `Φ` a local diffeomorphism at `x`.
  have hloc : IsLocalDiffeomorphAt I 𝓘(ℝ, Z × F) ∞ Φ x := by
    refine Milnor.isLocalDiffeomorphAt_of_isInvertible_mfderiv ?_ (by simp) hΦ_inv
    filter_upwards [hU₁.mem_nhds hxU₁] with p hp
    exact hΦ_smooth.contMDiffAt (hU₁.mem_nhds hp)
  obtain ⟨Ψ, hxΨ, hΨ⟩ := hloc
  -- Restricted to `U₁`, it is a slice chart for `f⁻¹(y)`.
  have hslice : ∀ p ∈ (Ψ.restrOpen U₁ hU₁).source, p ∈ f ⁻¹' {y} ↔ ((Ψ.restrOpen U₁ hU₁) p).2 = 0 := by
    intro p hp
    rw [PartialDiffeomorph.restrOpen_apply, ← hΨ hp.1]
    show p ∈ f ⁻¹' {y} ↔ ψ (f p) - ψ y = 0
    rw [mem_preimage, mem_singleton_iff, sub_eq_zero]
    constructor
    · intro h; rw [h]
    · intro h; exact ψ.injOn hp.2.2 hyψ h
  refine ⟨⟨Ψ.restrOpen U₁ hU₁, x, hx, ⟨hxΨ, hxU₁⟩, hslice⟩, ⟨hxΨ, hxU₁⟩, ?_⟩
  intro p hp
  rw [PartialDiffeomorph.restrOpen_apply, ← hΨ hp.1]

/-- **Milnor's Lemma 1** (p. 11): if `y` is a regular value of the smooth map `f : M → N`, then
`f⁻¹(y)` is a slice submanifold of `M`, modelled on any space `Z` of dimension
`dim M - dim N`. -/
theorem isSliceSubmanifold_preimage {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (hZ : finrank ℝ Z + finrank ℝ F = finrank ℝ E)
    (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y) :
    IsSliceSubmanifold I Z F (f ⁻¹' {y}) := fun x hx =>
  let ⟨σ, hσ, _⟩ := exists_sliceChart_preimage hZ hf hy hx
  ⟨σ, hσ⟩

/-! ### Lemma 2 -/

/-- **Milnor's Lemma 2** (p. 12), first half: `df` vanishes on the tangent space of `f⁻¹(y)`,
i.e. `dfₓ ∘ d(incl)ₓ = 0`. -/
theorem mfderiv_comp_val_eq_zero {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (hf : ContMDiff I J ∞ f) {y : N} (hS : IsSliceSubmanifold I Z F (f ⁻¹' {y}))
    (p : f ⁻¹' {y}) :
    letI := hS.chartedSpace
    (mfderiv I J f p.1).comp (mfderiv 𝓘(ℝ, Z) I (Subtype.val : f ⁻¹' {y} → M) p) = 0 := by
  letI := hS.chartedSpace
  haveI := hS.isManifold
  have hval : MDifferentiableAt 𝓘(ℝ, Z) I (Subtype.val : f ⁻¹' {y} → M) p :=
    hS.contMDiff_val.mdifferentiableAt (by simp)
  have hf' : MDifferentiableAt I J f p.1 := hf.mdifferentiableAt (by simp)
  have hcomp : mfderiv 𝓘(ℝ, Z) J (f ∘ Subtype.val) p =
      (mfderiv I J f p.1).comp (mfderiv 𝓘(ℝ, Z) I Subtype.val p) := mfderiv_comp p hf' hval
  have hconst : f ∘ (Subtype.val : f ⁻¹' {y} → M) = fun _ => y := by
    funext q
    exact q.2
  rw [← hcomp, hconst, mfderiv_const]
  rfl

/-- **Milnor's Lemma 2**, second half: the inclusion of a slice submanifold has injective
derivative (so the tangent space of `S` sits inside `TMₓ`). -/
theorem injective_mfderiv_val {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {S : Set M} (hS : IsSliceSubmanifold I Z W S) (p : S) :
    letI := hS.chartedSpace
    Injective (mfderiv 𝓘(ℝ, Z) I (Subtype.val : S → M) p) := by
  letI := hS.chartedSpace
  haveI := hS.isManifold
  set σ := (hS p.1 p.2).choose with hσ
  have hpσ : p.1 ∈ σ.φ.source := (hS p.1 p.2).choose_spec
  -- `g := fst ∘ φ` satisfies `g ∘ val = chartAt p`, whose derivative at `p` is the identity.
  set g : M → Z := fun m => (σ.φ m).1 with hg_def
  have hg : MDifferentiableAt I 𝓘(ℝ, Z) g p.1 := by
    have h1 : ContMDiffAt I 𝓘(ℝ, Z × W) ∞ σ.φ p.1 :=
      σ.φ.contMDiffOn.contMDiffAt (σ.φ.open_source.mem_nhds hpσ)
    exact ((contDiff_fst.contMDiff (n := ∞)).contMDiffAt.comp p.1 h1).mdifferentiableAt (by simp)
  have hval : MDifferentiableAt 𝓘(ℝ, Z) I (Subtype.val : S → M) p :=
    hS.contMDiff_val.mdifferentiableAt (by simp)
  have hcomp : mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, Z) (g ∘ Subtype.val) p =
      (mfderiv I 𝓘(ℝ, Z) g p.1).comp (mfderiv 𝓘(ℝ, Z) I Subtype.val p) := mfderiv_comp p hg hval
  have hchart : g ∘ (Subtype.val : S → M) = chartAt Z p := by
    rw [hS.chartAt_eq, ← hσ]
    funext q
    rfl
  have hid : ∀ v, mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, Z) (g ∘ Subtype.val) p v = v := by
    intro v
    have h : mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, Z) (g ∘ Subtype.val) p =
        mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, Z) (chartAt Z p) p :=
      Filter.EventuallyEq.mfderiv_eq (Filter.Eventually.of_forall fun q => congrFun hchart q)
    rw [mfderiv_chartAt_eq_tangentCoordChange (mem_chart_source Z p)] at h
    have h2 : tangentCoordChange 𝓘(ℝ, Z) p p p v = v :=
      tangentCoordChange_self (mem_extChartAt_source p)
    have h3 : mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, Z) (g ∘ Subtype.val) p v = tangentCoordChange 𝓘(ℝ, Z) p p p v :=
      DFunLike.congr_fun h v
    exact h3.trans h2
  intro v w hvw
  have h1 := hid v
  have h2 := hid w
  rw [hcomp] at h1 h2
  simp only [ContinuousLinearMap.comp_apply] at h1 h2
  rw [← h1, ← h2, hvw]

/-- **Milnor's Lemma 2** (p. 12), in full: a vector `v ∈ TMₚ` is tangent to `f⁻¹(y)` (i.e. is the
image of some vector under the derivative of the inclusion) if and only if `df_p v = 0`. -/
theorem mem_range_mfderiv_val_iff {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (hZ : finrank ℝ Z + finrank ℝ F = finrank ℝ E)
    (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y) (p : f ⁻¹' {y}) (v : E) :
    letI := (isSliceSubmanifold_preimage hZ hf hy).chartedSpace
    (∃ w : Z, mfderiv 𝓘(ℝ, Z) I (Subtype.val : f ⁻¹' {y} → M) p w = v) ↔
      mfderiv I J f p.1 v = 0 := by
  set hS := isSliceSubmanifold_preimage hZ hf hy
  letI := hS.chartedSpace
  haveI := hS.isManifold
  let Lι : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) I (Subtype.val : f ⁻¹' {y} → M) p
  let Lf : E →L[ℝ] F := mfderiv I J f p.1
  have hcomp : ∀ w : Z, Lf (Lι w) = 0 := fun w =>
    DFunLike.congr_fun (mfderiv_comp_val_eq_zero hf hS p) w
  have hle : LinearMap.range (Lι : Z →ₗ[ℝ] E) ≤ LinearMap.ker (Lf : E →ₗ[ℝ] F) := by
    rintro _ ⟨w, rfl⟩
    exact hcomp w
  have hinj : Injective Lι := injective_mfderiv_val hS p
  have h1 : finrank ℝ (LinearMap.range (Lι : Z →ₗ[ℝ] E)) = finrank ℝ Z :=
    LinearMap.finrank_range_of_inj hinj
  have h2 : finrank ℝ (LinearMap.range (Lf : E →ₗ[ℝ] F)) +
      finrank ℝ (LinearMap.ker (Lf : E →ₗ[ℝ] F)) = finrank ℝ E :=
    LinearMap.finrank_range_add_finrank_ker (Lf : E →ₗ[ℝ] F)
  have hsurj : Surjective Lf := hy p.1 p.2
  have h3 : LinearMap.range (Lf : E →ₗ[ℝ] F) = ⊤ := LinearMap.range_eq_top.2 hsurj
  rw [h3, finrank_top] at h2
  have heq : LinearMap.range (Lι : Z →ₗ[ℝ] E) = LinearMap.ker (Lf : E →ₗ[ℝ] F) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [h1]; omega)
  constructor
  · rintro ⟨w, rfl⟩
    exact hcomp w
  · intro hv
    have : v ∈ LinearMap.range (Lι : Z →ₗ[ℝ] E) := by
      rw [heq, LinearMap.mem_ker]
      exact hv
    obtain ⟨w, hw⟩ := this
    exact ⟨w, hw⟩

end Milnor
