import Milnor.Chapter2.Corestrict

/-!
Milnor, *Morse Theory*, §6, p. 36 (the proof of Corollary 6.7), and the use of Whitney's theorem
throughout Part I.

# The image of an embedding is a submanifold, and the embedding is a diffeomorphism onto it

## Milnor's text, paraphrased

In the proof of Corollary 6.7 (p. 36) Milnor writes that "an `n`-dimensional manifold can be
embedded differentiably as a closed subset of `ℝ²ⁿ⁺¹`" (Whitney, *Geometric Integration Theory*,
p. 113), and from then on treats the manifold as the image of the embedding: Theorem 6.6, proved
for manifolds in Euclidean space, is applied to it.  That the image of a differentiable embedding
is a manifold in Euclidean space, and that the embedding identifies the two (so that critical
points, indices and sublevel sets correspond), is taken for granted.

## What is proved here

Let `M` be a smooth manifold without boundary modelled on a finite-dimensional real normed space
`E` (`[ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]`, the convention of
`Morse/Chapter1/Manifold.lean`), `F` a finite-dimensional real normed space (Milnor's `ℝᴷ`), and
`e : M → F` smooth, a topological embedding (`Topology.IsEmbedding e`: a homeomorphism onto its
image with the subspace topology) with injective derivative at every point.  Let `Z`, `W` be
finite-dimensional real normed spaces with `dim Z = dim E` and `dim Z + dim W = dim F`.

* `Morse.exists_continuousLinearEquiv_coprod` (linear algebra): for an injective
  `A : E →L[ℝ] F` and `T : Z ≃L[ℝ] E` there is `L : W →L[ℝ] F` such that
  `(z, w) ↦ A (T z) + L w` is an isomorphism `Z × W ≃ F` (`L` maps `W` onto a complement of the
  range of `A`).
* `Morse.exists_sliceChart_range` (**the local immersion theorem**): around `e x` there is a slice
  chart for `e(M)` in the sense of the companion project (`Milnor.SliceChart`), namely the
  inverse of `Ψ(z, w) = e(φ⁻¹(T z)) + L w`, `φ` the chart of `M` at `x` and `L` as above with
  `A = de_x`.  `Ψ` has invertible derivative at `(T⁻¹ φ x, 0)`, so the inverse function theorem
  (`Milnor.isLocalDiffeomorphAt_of_isInvertible_mfderiv`) makes it a diffeomorphism near that
  point.  The chart also satisfies `e(φ⁻¹(T (σ p).1)) = p` for every `p ∈ e(M)` in its domain.
* `Morse.isSliceSubmanifold_range`: **`e(M)` is a slice submanifold of `F` modelled on `Z`**
  (`Milnor.IsSliceSubmanifold 𝓘(ℝ, F) Z W (range e)`), hence a smooth manifold
  (`hN.chartedSpace`, `hN.isManifold`).
* `Morse.contMDiff_ofInjective_symm` and `Morse.diffeomorphRange`: **`e : M → e(M)` is a
  diffeomorphism** (Mathlib's `Diffeomorph`, for the manifold structure `hN.chartedSpace` of
  `e(M)`); its inverse reads `p ↦ φ⁻¹(T (σ p).1)` in the slice chart `σ` built at `x`.
  `Morse.exists_diffeomorph_range` packages the two statements.

## What Milnor leaves implicit

* **An injective immersion need not have a submanifold as image**: the figure eight (an injective
  immersion of an open interval) is not a submanifold at the crossing point.  What is needed is
  that `e` be a homeomorphism onto its image.  In the proof it enters exactly once: the open set
  `U ∋ x` on which `Ψ` is a diffeomorphism must satisfy `e(M) ∩ O = e(U)` for some open `O ⊆ F`,
  which is the definition of the subspace topology (`Topology.IsInducing.isOpen_iff`).  For
  compact `M` (the case of `Morse/Chapter4/Whitney.lean`) every continuous injection into `F` is
  a closed embedding, so the hypothesis is automatic there.
* **The local immersion theorem** (that an immersion looks like `u ↦ (u, 0)` in suitable charts)
  is the inverse function theorem applied to `Ψ`; Mathlib (v4.33.1) lists it as a TODO in
  `Mathlib/Geometry/Manifold/Immersion.lean`.  The complement of `de_x(TM_x)` varies with `x`, so
  a fixed space `W` of the right dimension is identified with it at each point.
* **The model space of `e(M)`** is any `Z` of the dimension of `E`; it need not be `E` itself.
  This is used to read `e(M)` on `ℝᵈ⁺¹ = EuclideanSpace ℝ (Fin (d + 1))`, the model of the
  results of `Morse/Chapter3/EulerChar.lean`.
* **The inverse of `e` is smooth** on the manifold `e(M)`: this is not a consequence of `e` being
  smooth and bijective onto `e(M)` alone (`x ↦ x³` on `ℝ`); it is read off from the slice chart.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

namespace Morse

/-! ### Linear algebra: completing an injective map to an isomorphism -/

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- **Completing an injective linear map to an isomorphism.**  If `A : E → F` is injective,
`T : Z ≃ E` and `dim Z + dim W = dim F`, there is a linear map `L : W → F` such that
`(z, w) ↦ A (T z) + L w` is a linear isomorphism `Z × W ≃ F` (`L` maps `W` isomorphically onto a
complement of the range of `A`). -/
theorem exists_continuousLinearEquiv_coprod (A : E →L[ℝ] F) (hA : Injective A) (T : Z ≃L[ℝ] E)
    (hW : finrank ℝ Z + finrank ℝ W = finrank ℝ F) :
    ∃ L : W →L[ℝ] F, ∃ D : (Z × W) ≃L[ℝ] F, ∀ p : Z × W, D p = A (T p.1) + L p.2 := by
  obtain ⟨C, hC⟩ := (LinearMap.range (A : E →ₗ[ℝ] F)).exists_isCompl
  have h1 : finrank ℝ (LinearMap.range (A : E →ₗ[ℝ] F)) = finrank ℝ Z := by
    rw [LinearMap.finrank_range_of_inj hA, T.toLinearEquiv.finrank_eq]
  have h2 := Submodule.finrank_add_eq_of_isCompl hC
  have hWC : finrank ℝ W = finrank ℝ C := by omega
  let J : W ≃ₗ[ℝ] C := LinearEquiv.ofFinrankEq W C hWC
  let L : W →L[ℝ] F := LinearMap.toContinuousLinearMap (C.subtype ∘ₗ J.toLinearMap)
  have hLC : ∀ w, L w ∈ C := fun w => (J w).2
  let D₀ : (Z × W) →ₗ[ℝ] F := ((A.comp (T : Z →L[ℝ] E)).coprod L : Z × W →L[ℝ] F)
  have hD₀ : ∀ p : Z × W, D₀ p = A (T p.1) + L p.2 := fun p => rfl
  have hinj : Injective D₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hD₀] at hp
    have hmem : A (T p.1) ∈ LinearMap.range (A : E →ₗ[ℝ] F) ⊓ C := by
      refine ⟨⟨T p.1, rfl⟩, ?_⟩
      have : A (T p.1) = -L p.2 := eq_neg_of_add_eq_zero_left hp
      rw [this]
      exact C.neg_mem (hLC _)
    rw [hC.inf_eq_bot, Submodule.mem_bot] at hmem
    have h1 : p.1 = 0 := T.injective (hA (by rw [hmem, map_zero, map_zero]))
    have h2 : L p.2 = 0 := by rw [hmem, zero_add] at hp; exact hp
    have h3 : p.2 = 0 := by
      have : J p.2 = 0 := Subtype.ext h2
      exact J.injective (by rw [this, map_zero])
    exact Prod.ext h1 h3
  have hdim : finrank ℝ (Z × W) = finrank ℝ F := by rw [Module.finrank_prod, hW]
  exact ⟨L, (LinearMap.linearEquivOfInjective D₀ hinj hdim).toContinuousLinearEquiv,
    fun p => rfl⟩

end Linear

/-! ### The local immersion theorem and the slice charts of `e(M)` -/

section Slice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {e : M → F}

omit [FiniteDimensional ℝ E] in
/-- **The local immersion theorem, as a slice chart.**  Let `e : M → F` be smooth, a topological
embedding, with injective derivative at `x`, and let `T : Z ≃ E`, `dim Z + dim W = dim F`.  Then
there is a slice chart `σ` of `e(M) ⊆ F` (in the sense of `Milnor.SliceChart`) whose domain
contains `e x`, such that for every `p` in its domain `T (σ p).1` lies in the target of the chart
`φ` of `M` at `x`, and `e (φ⁻¹ (T (σ p).1)) = p` when `p ∈ e(M)`.

The chart is the inverse of `Ψ(z, w) = e(φ⁻¹(T z)) + L w`, `L` completing `de_x` to an
isomorphism (`Morse.exists_continuousLinearEquiv_coprod`), restricted to an open set `O` with
`e(M) ∩ O = e(U)`, `U` the set of points whose image `(T⁻¹ φ y, 0)` lies in the domain of `Ψ`. -/
theorem exists_sliceChart_range (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (hemb : IsEmbedding e)
    {x : M} (hinj : Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x)) (T : Z ≃L[ℝ] E)
    (hW : finrank ℝ Z + finrank ℝ W = finrank ℝ F) :
    ∃ σ : Milnor.SliceChart 𝓘(ℝ, F) Z W (range e), e x ∈ σ.φ.source ∧
      ∀ p ∈ σ.φ.source, T (σ.φ p).1 ∈ (extChartAt 𝓘(ℝ, E) x).target ∧
        (p ∈ range e → e ((extChartAt 𝓘(ℝ, E) x).symm (T (σ.φ p).1)) = p) := by
  set φ := extChartAt 𝓘(ℝ, E) x with hφ
  obtain ⟨L, D, hD⟩ :=
    exists_continuousLinearEquiv_coprod (E := E) (F := F) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x) hinj T hW
  -- Milnor's map `Ψ(z, w) = e(φ⁻¹(T z)) + L w`, near `x₀ = (T⁻¹ (φ x), 0)`
  set Ψ : Z × W → F := fun p => e (φ.symm (T p.1)) + L p.2 with hΨ
  set x₀ : Z × W := (T.symm (φ x), 0) with hx₀
  set S₀ : Set (Z × W) := {p | T p.1 ∈ φ.target} with hS₀
  have hS₀o : IsOpen S₀ :=
    (isOpen_extChartAt_target x).preimage (T.continuous.comp continuous_fst)
  have hx₀S : x₀ ∈ S₀ := by
    change T (T.symm (φ x)) ∈ φ.target
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact mem_extChartAt_target x
  have hg : ContDiffOn ℝ ∞ (e ∘ φ.symm) φ.target :=
    contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn (contMDiffOn_extChartAt_symm x))
  have hΨs : ∀ p ∈ S₀, ContDiffAt ℝ ∞ Ψ p := by
    intro p hp
    have h1 : ContDiffAt ℝ ∞ (e ∘ φ.symm) (T p.1) :=
      hg.contDiffAt ((isOpen_extChartAt_target x).mem_nhds hp)
    have h2 : ContDiffAt ℝ ∞ (fun p : Z × W => T p.1) p :=
      (T.contDiff.comp contDiff_fst).contDiffAt
    exact (h1.comp p h2).add (L.contDiff.comp contDiff_snd).contDiffAt
  -- the derivative of `Ψ` at `x₀` is the isomorphism `D`
  have hderiv : HasFDerivAt Ψ (D : Z × W →L[ℝ] F) x₀ := by
    have h1 : HasFDerivAt (e ∘ φ.symm) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x : E →L[ℝ] F) (φ x) := by
      have := Milnor.hasFDerivAt_writtenInExtChartAt
        (he.mdifferentiableAt (by simp) : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) e x)
      have hw : writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, F) x e = e ∘ φ.symm := by
        funext u
        simp [writtenInExtChartAt, chartAt_self_eq, hφ]
      rwa [hw] at this
    have h1' : HasFDerivAt (e ∘ φ.symm) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x : E →L[ℝ] F) (T x₀.1) := by
      simpa [hx₀] using h1
    have h2 : HasFDerivAt (fun p : Z × W => T p.1)
        ((T : Z →L[ℝ] E).comp (ContinuousLinearMap.fst ℝ Z W)) x₀ :=
      ((T : Z →L[ℝ] E).comp (ContinuousLinearMap.fst ℝ Z W)).hasFDerivAt
    have h3 : HasFDerivAt (fun p : Z × W => L p.2) (L.comp (ContinuousLinearMap.snd ℝ Z W)) x₀ :=
      (L.comp (ContinuousLinearMap.snd ℝ Z W)).hasFDerivAt
    have h4 := (h1'.comp x₀ h2).add h3
    refine h4.congr_fderiv (ContinuousLinearMap.ext fun p => ?_)
    rw [ContinuousLinearEquiv.coe_coe, hD]
    rfl
  -- the inverse function theorem
  have hloc : IsLocalDiffeomorphAt 𝓘(ℝ, Z × W) 𝓘(ℝ, F) ∞ Ψ x₀ := by
    refine Milnor.isLocalDiffeomorphAt_of_isInvertible_mfderiv ?_ (by simp) ?_
    · filter_upwards [hS₀o.mem_nhds hx₀S] with p hp
      exact (hΨs p hp).contMDiffAt
    · rw [mfderiv_eq_fderiv, hderiv.fderiv]
      exact ⟨D, rfl⟩
  obtain ⟨Φ, hx₀Φ, hΦeq⟩ := hloc
  have hΨΦ : ∀ q ∈ Φ.source, Φ q = Ψ q := fun q hq => (hΦeq hq).symm
  -- restrict `Φ` to `S₀`
  set Φ₁ := Φ.restrOpen S₀ hS₀o with hΦ₁
  have hx₀Φ₁ : x₀ ∈ Φ₁.source := ⟨hx₀Φ, hx₀S⟩
  -- the open set `U ∋ x` of points `y` with `(T⁻¹ (φ y), 0)` in the source of `Φ₁`
  set U : Set M := φ.source ∩ (fun y => ((T.symm (φ y), (0 : W)) : Z × W)) ⁻¹' Φ₁.source
    with hU
  have hUo : IsOpen U := by
    refine ContinuousOn.isOpen_inter_preimage ?_ (isOpen_extChartAt_source x) Φ₁.open_source
    exact (T.symm.continuous.comp_continuousOn (continuousOn_extChartAt x)).prodMk
      continuousOn_const
  have hxU : x ∈ U := ⟨mem_extChartAt_source x, hx₀Φ₁⟩
  -- `e` is an embedding: `U = e⁻¹(O)` for an open `O ⊆ F`
  obtain ⟨O, hOo, hOU⟩ := hemb.isInducing.isOpen_iff.1 hUo
  -- the slice chart: `Φ₁⁻¹` restricted to `O`
  set Φ₂ := Φ₁.symm.restrOpen O hOo with hΦ₂
  have hΦ₂_apply : ∀ p, Φ₂ p = Φ.invFun p := fun p => rfl
  have hsrc : ∀ p ∈ Φ₂.source, Φ.invFun p ∈ Φ.source ∧ Φ.invFun p ∈ S₀ ∧
      Φ (Φ.invFun p) = p := by
    rintro p ⟨⟨q, hq, rfl⟩, -⟩
    rw [Φ.invFun_apply hq.1]
    exact ⟨hq.1, hq.2, rfl⟩
  have hΨ_param : ∀ y ∈ φ.source, Ψ (T.symm (φ y), 0) = e y := by
    intro y hy
    simp only [hΨ, ContinuousLinearEquiv.apply_symm_apply, map_zero, add_zero]
    rw [φ.left_inv hy]
  have hslice : ∀ p ∈ Φ₂.source, p ∈ range e ↔ (Φ₂ p).2 = 0 := by
    intro p hp
    constructor
    · rintro ⟨y, rfl⟩
      have hyU : y ∈ U := by rw [← hOU]; exact hp.2
      have h1 : Φ (T.symm (φ y), 0) = e y := by rw [hΨΦ _ hyU.2.1, hΨ_param y hyU.1]
      rw [hΦ₂_apply, ← h1, Φ.invFun_apply hyU.2.1]
    · intro h
      obtain ⟨hq, -, hqp⟩ := hsrc p hp
      rw [hΦ₂_apply] at h
      refine ⟨φ.symm (T (Φ.invFun p).1), ?_⟩
      have h1 : Ψ (Φ.invFun p) = p := by rw [← hΨΦ _ hq, hqp]
      have h2 : Ψ (Φ.invFun p) = e (φ.symm (T (Φ.invFun p).1)) := by
        simp only [hΨ, h, map_zero, add_zero]
      exact h2.symm.trans h1
  have hex : e x ∈ Φ₂.source := by
    refine ⟨⟨x₀, ⟨hx₀Φ, hx₀S⟩, ?_⟩, ?_⟩
    · show Φ x₀ = e x
      rw [hΨΦ _ hx₀Φ, hΨ_param x (mem_extChartAt_source x)]
    · show e x ∈ O
      rw [← mem_preimage, hOU]
      exact hxU
  refine ⟨⟨Φ₂, e x, mem_range_self x, hex, hslice⟩, hex, fun p hp => ⟨(hsrc p hp).2.1, ?_⟩⟩
  intro hpe
  have h := (hslice p hp).1 hpe
  obtain ⟨hq, -, hqp⟩ := hsrc p hp
  rw [hΦ₂_apply] at h
  change e (φ.symm (T (Φ.invFun p).1)) = p
  have h1 : Ψ (Φ.invFun p) = p := by rw [← hΨΦ _ hq, hqp]
  have h2 : Ψ (Φ.invFun p) = e (φ.symm (T (Φ.invFun p).1)) := by
    simp only [hΨ, h, map_zero, add_zero]
  exact h2.symm.trans h1

/-- **The image of an embedding is a submanifold.**  If `e : M → F` is smooth, a topological
embedding, and has injective derivative everywhere, then `e(M)` is a slice submanifold of `F`
modelled on any `Z` with `dim Z = dim M`, with normal model `W`, `dim Z + dim W = dim F`. -/
theorem isSliceSubmanifold_range (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (hemb : IsEmbedding e)
    (hinj : ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x))
    (hZ : finrank ℝ Z = finrank ℝ E) (hW : finrank ℝ Z + finrank ℝ W = finrank ℝ F) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, F) Z W (range e) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨σ, hσ, -⟩ :=
    exists_sliceChart_range he hemb (hinj x) (ContinuousLinearEquiv.ofFinrankEq hZ) hW
  exact ⟨σ, hσ⟩

/-- **The inverse of `e : M → e(M)` is smooth** for the manifold structure of the slice
submanifold `e(M)`: near `e x` it is `p ↦ φ⁻¹(T (σ p).1)`, `σ` the slice chart of
`Morse.exists_sliceChart_range` built at `x`. -/
theorem contMDiff_ofInjective_symm (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, F) Z W (range e))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (hemb : IsEmbedding e)
    (hinj : ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x))
    (hZ : finrank ℝ Z = finrank ℝ E) (hW : finrank ℝ Z + finrank ℝ W = finrank ℝ F) :
    letI := hN.chartedSpace
    ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ (Equiv.ofInjective e hemb.injective).symm := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  intro q
  set x := (Equiv.ofInjective e hemb.injective).symm q with hx
  have hqx : e x = q.1 := Equiv.apply_ofInjective_symm hemb.injective q
  set T : Z ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq hZ
  obtain ⟨σ, hσx, hσ⟩ := exists_sliceChart_range he hemb (hinj x) T hW
  set φ := extChartAt 𝓘(ℝ, E) x with hφ
  -- the inverse near `q`, read in the slice chart
  have hloc : ∀ q' : range e, q'.1 ∈ σ.φ.source →
      (Equiv.ofInjective e hemb.injective).symm q' = φ.symm (T (σ.φ q'.1).1) := by
    intro q' hq'
    apply hemb.injective
    rw [(hσ q'.1 hq').2 q'.2]
    exact Equiv.apply_ofInjective_symm hemb.injective q'
  have hq_src : q.1 ∈ σ.φ.source := hqx ▸ hσx
  have hev : (Equiv.ofInjective e hemb.injective).symm =ᶠ[𝓝 q]
      fun q' : range e => φ.symm (T (σ.φ q'.1).1) := by
    have : {q' : range e | q'.1 ∈ σ.φ.source} ∈ 𝓝 q :=
      (σ.φ.open_source.preimage continuous_subtype_val).mem_nhds hq_src
    filter_upwards [this] with q' hq' using hloc q' hq'
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
  have h1 : ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, F) ∞ (Subtype.val : range e → F) q := hN.contMDiff_val q
  have h2 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, Z × W) ∞ σ.φ q.1 :=
    (σ.φ.contMDiffOn _ hq_src).contMDiffAt (σ.φ.open_source.mem_nhds hq_src)
  have h3 : ContMDiffAt 𝓘(ℝ, Z × W) 𝓘(ℝ, E) ∞ (fun p : Z × W => T p.1) (σ.φ q.1) :=
    (T.contDiff.comp contDiff_fst).contMDiff.contMDiffAt
  have h4 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φ.symm (T (σ.φ q.1).1) :=
    (contMDiffOn_extChartAt_symm x _ (hσ _ hq_src).1).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (hσ _ hq_src).1)
  have h5 : ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞
      ((fun p : Z × W => T p.1) ∘ (σ.φ ∘ (Subtype.val : range e → F))) q :=
    h3.comp q (h2.comp q h1)
  exact h4.comp q h5

/-- **`e : M → e(M)` is a diffeomorphism** onto the slice submanifold `e(M)` (with its manifold
structure `hN.chartedSpace`, modelled on `Z`). -/
def diffeomorphRange (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, F) Z W (range e))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (hemb : IsEmbedding e)
    (hinj : ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x))
    (hZ : finrank ℝ Z = finrank ℝ E) (hW : finrank ℝ Z + finrank ℝ W = finrank ℝ F) :
    letI := hN.chartedSpace
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) M (range e) ∞ :=
  letI := hN.chartedSpace
  { toEquiv := Equiv.ofInjective e hemb.injective
    contMDiff_toFun := hN.contMDiff_codRestrict he (fun x => mem_range_self x)
    contMDiff_invFun := contMDiff_ofInjective_symm hN he hemb hinj hZ hW }

@[simp] theorem diffeomorphRange_apply_coe
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, F) Z W (range e))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (hemb : IsEmbedding e)
    (hinj : ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x))
    (hZ : finrank ℝ Z = finrank ℝ E) (hW : finrank ℝ Z + finrank ℝ W = finrank ℝ F) (x : M) :
    letI := hN.chartedSpace
    ((diffeomorphRange hN he hemb hinj hZ hW x : range e) : F) = e x := rfl

/-- **`e : M → e(M)` is a diffeomorphism** (existence form): if `e` is a smooth embedding with
injective derivative, `e(M)` is a slice submanifold of `F` modelled on `Z` and there is a
diffeomorphism `Φ : M ≃ e(M)` with `Φ x = e x`. -/
theorem exists_diffeomorph_range (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (hemb : IsEmbedding e)
    (hinj : ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x))
    (hZ : finrank ℝ Z = finrank ℝ E) (hW : finrank ℝ Z + finrank ℝ W = finrank ℝ F) :
    ∃ hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, F) Z W (range e),
      letI := hN.chartedSpace
      ∃ Φ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) M (range e) ∞, ∀ x, (Φ x : F) = e x :=
  ⟨isSliceSubmanifold_range he hemb hinj hZ hW,
    diffeomorphRange (isSliceSubmanifold_range he hemb hinj hZ hW) he hemb hinj hZ hW,
    fun _ => rfl⟩

end Slice

end Morse
