import Milnor.Chapter8.LocalSlice

/-!
# Problems 8 and 9: tangent spaces of products and of graphs

Let `M ⊆ E₁` and `N ⊆ E₂` be slice submanifolds of finite-dimensional real vector spaces, modelled
on `Z₁` and `Z₂` (slice charts `φ` map open subsets of `Eᵢ` onto open subsets of `Zᵢ × Wᵢ`).
Tangent spaces are the ranges of the derivatives of the inclusions (written with `mfd`).

* **Problem 8.** `M × N ⊆ E₁ × E₂` is a slice submanifold modelled on `Z₁ × Z₂`
  (`isSliceSubmanifold_prod`), and `T(M × N)_(x,y) = TMₓ × TN_y` (`range_mfd_val_prod`).
  Near `(x, y)`, `M × N` is the zero set of the submersion `(a, b) ↦ ((φ₁ a).2, (φ₂ b).2)` built
  from slice charts `φ₁` at `x` and `φ₂` at `y`. Its derivative is `D₁ × D₂` with `Dᵢ = (dφᵢ)₂`,
  whose kernel is `ker D₁ × ker D₂`, and `ker Dᵢ` is the tangent space of the factor.
* **Problem 9.** The graph `Γ ⊆ E₁ × E₂` of a smooth map `f : M → N` is a slice submanifold
  modelled on `Z₁` (`isSliceSubmanifold_graph`), and `TΓ_(x, f x)` is the graph of `dfₓ`, i.e. the
  image of `u ↦ (dιₓ u, dι_{f x} (dfₓ u))` (`range_mfd_val_graph`). For a slice chart `φ` of `M`
  at `x`, `f` extends to the smooth map `f̃ a = f (φ⁻¹ ((φ a).1, 0))` on an open subset of `E₁`,
  and near `(x, f x)` the graph is the zero set of the submersion `(a, b) ↦ ((φ a).2, b - f̃ a)`.
  The kernel of its derivative is `{(v, w) | v ∈ TMₓ, w = df̃ v}`, and `df̃ = dι_N ∘ df` on `TMₓ`
  by the chain rule for `f̃ ∘ ι_M = ι_N ∘ f`.

Both parts rest on `IsSliceSubmanifold.of_locally_preimage` (local zero sets of submersions are
slice submanifolds) and `IsSliceSubmanifold.range_mfderiv_val_eq_ker` (their tangent spaces are
kernels).
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

namespace Problems

/-! ### Slice charts in a vector space -/

section chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {S : Set E}

/-- The second component `a ↦ (φ a).2` of a slice chart: a local defining function for `S`. -/
def sliceDef (σ : SliceChart 𝓘(ℝ, E) Z W S) (a : E) : W := (σ.φ a).2

theorem contDiffOn_sliceChart (σ : SliceChart 𝓘(ℝ, E) Z W S) :
    ContDiffOn ℝ ∞ σ.φ σ.φ.source :=
  contMDiffOn_iff_contDiffOn.1 σ.φ.contMDiffOn

theorem contDiffOn_sliceDef (σ : SliceChart 𝓘(ℝ, E) Z W S) :
    ContDiffOn ℝ ∞ (sliceDef σ) σ.φ.source :=
  contDiff_snd.comp_contDiffOn (contDiffOn_sliceChart σ)

/-- The derivative of a slice chart at a point of its domain is bijective (an isomorphism
`E ≃ Z × W`). -/
theorem bijective_fderiv_sliceChart (σ : SliceChart 𝓘(ℝ, E) Z W S) {a : E}
    (ha : a ∈ σ.φ.source) :
    DifferentiableAt ℝ σ.φ a ∧ Bijective (fderiv ℝ σ.φ a) := by
  have hloc := σ.φ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, Z × W) ∞ ha
  refine ⟨mdifferentiableAt_iff_differentiableAt.1 (σ.φ.mdifferentiableAt (by simp) ha), ?_⟩
  have h := (hloc.mfderivToContinuousLinearEquiv (by simp)).bijective
  rw [← mfderiv_eq_fderiv]
  exact h

/-- The derivative of the local defining function `sliceDef σ` is `(dφ)₂`. -/
theorem hasFDerivAt_sliceDef (σ : SliceChart 𝓘(ℝ, E) Z W S) {a : E} (ha : a ∈ σ.φ.source) :
    HasFDerivAt (sliceDef σ) ((ContinuousLinearMap.snd ℝ Z W).comp (fderiv ℝ σ.φ a)) a :=
  (bijective_fderiv_sliceChart σ ha).1.hasFDerivAt.snd

/-- The derivative `(dφ)₂` of `sliceDef σ` is surjective. -/
theorem surjective_fderiv_sliceDef (σ : SliceChart 𝓘(ℝ, E) Z W S) {a : E}
    (ha : a ∈ σ.φ.source) :
    Surjective ((ContinuousLinearMap.snd ℝ Z W).comp (fderiv ℝ σ.φ a)) := by
  intro w
  obtain ⟨v, hv⟩ := (bijective_fderiv_sliceChart σ ha).2.2 (0, w)
  refine ⟨v, ?_⟩
  rw [ContinuousLinearMap.comp_apply, hv]
  rfl

theorem mfd_sliceDef (σ : SliceChart 𝓘(ℝ, E) Z W S) {a : E} (ha : a ∈ σ.φ.source) :
    mfd 𝓘(ℝ, E) 𝓘(ℝ, W) (sliceDef σ) a =
      (ContinuousLinearMap.snd ℝ Z W).comp (fderiv ℝ σ.φ a) :=
  mfderiv_eq_fderiv.trans (hasFDerivAt_sliceDef σ ha).fderiv

end chart

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  {Z₁ : Type*} [NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁]
  {Z₂ : Type*} [NormedAddCommGroup Z₂] [NormedSpace ℝ Z₂]
  {W₁ : Type*} [NormedAddCommGroup W₁] [NormedSpace ℝ W₁]
  {W₂ : Type*} [NormedAddCommGroup W₂] [NormedSpace ℝ W₂]
  {M : Set E₁} {N : Set E₂}

/-! ### Dimension and tangent space of a slice submanifold -/

section dim

variable [FiniteDimensional ℝ Z₁] [FiniteDimensional ℝ W₁]

/-- A slice chart gives `finrank Z + finrank W = finrank E`. -/
theorem IsSliceSubmanifold.finrank_add (hM : IsSliceSubmanifold 𝓘(ℝ, E₁) Z₁ W₁ M)
    (hne : M.Nonempty) : finrank ℝ Z₁ + finrank ℝ W₁ = finrank ℝ E₁ := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨σ, hσ⟩ := hM x hx
  have hbij := (bijective_fderiv_sliceChart σ hσ).2
  rw [← finrank_prod]
  exact (LinearEquiv.ofBijective (fderiv ℝ σ.φ x : E₁ →ₗ[ℝ] Z₁ × W₁) hbij).finrank_eq.symm

variable [FiniteDimensional ℝ E₁]

/-- The tangent space of a slice submanifold at `x` is the kernel of `(dφₓ)₂` for any slice chart
`φ` at `x`. -/
theorem range_mfd_val_eq_ker_sliceChart (hM : IsSliceSubmanifold 𝓘(ℝ, E₁) Z₁ W₁ M) (x : M)
    (σ : SliceChart 𝓘(ℝ, E₁) Z₁ W₁ M) (hx : x.1 ∈ σ.φ.source) :
    letI := hM.chartedSpace
    LinearMap.range (mfd 𝓘(ℝ, Z₁) 𝓘(ℝ, E₁) (Subtype.val : M → E₁) x : Z₁ →ₗ[ℝ] E₁) =
      LinearMap.ker ((ContinuousLinearMap.snd ℝ Z₁ W₁).comp (fderiv ℝ σ.φ x.1) :
        E₁ →ₗ[ℝ] W₁) := by
  have hsurj : Surjective (mfderiv 𝓘(ℝ, E₁) 𝓘(ℝ, W₁) (sliceDef σ) x.1) := by
    change Surjective (mfd 𝓘(ℝ, E₁) 𝓘(ℝ, W₁) (sliceDef σ) x.1)
    rw [mfd_sliceDef σ hx]
    exact surjective_fderiv_sliceDef σ hx
  rw [IsSliceSubmanifold.range_mfderiv_val_eq_ker hM
    (IsSliceSubmanifold.finrank_add hM ⟨x.1, x.2⟩) x σ.φ.open_source hx
    (contDiffOn_sliceDef σ).contMDiffOn (fun y hy hyS => (σ.slice y hy).1 hyS) hsurj,
    mfd_sliceDef σ hx]

end dim

/-! ### Problem 8: the product -/

section prod

/-- The local defining function `(a, b) ↦ ((φ₁ a).2, (φ₂ b).2)` of `M × N` is smooth. -/
theorem contMDiffOn_prodDef (σ₁ : SliceChart 𝓘(ℝ, E₁) Z₁ W₁ M)
    (σ₂ : SliceChart 𝓘(ℝ, E₂) Z₂ W₂ N) :
    ContMDiffOn 𝓘(ℝ, E₁ × E₂) 𝓘(ℝ, W₁ × W₂) ∞ (Prod.map (sliceDef σ₁) (sliceDef σ₂))
      (σ₁.φ.source ×ˢ σ₂.φ.source) :=
  ((contDiffOn_sliceDef σ₁).prodMap (contDiffOn_sliceDef σ₂)).contMDiffOn

/-- On the product of the chart domains, `M × N` is the zero set of the local defining
function. -/
theorem prodDef_eq_zero_iff (σ₁ : SliceChart 𝓘(ℝ, E₁) Z₁ W₁ M)
    (σ₂ : SliceChart 𝓘(ℝ, E₂) Z₂ W₂ N) {p : E₁ × E₂} (hp : p ∈ σ₁.φ.source ×ˢ σ₂.φ.source) :
    p ∈ M ×ˢ N ↔ Prod.map (sliceDef σ₁) (sliceDef σ₂) p = 0 := by
  rw [mem_prod, σ₁.slice p.1 hp.1, σ₂.slice p.2 hp.2, Prod.map_apply, Prod.mk_eq_zero]
  rfl

theorem mfd_prodDef (σ₁ : SliceChart 𝓘(ℝ, E₁) Z₁ W₁ M)
    (σ₂ : SliceChart 𝓘(ℝ, E₂) Z₂ W₂ N) {p : E₁ × E₂} (hp : p ∈ σ₁.φ.source ×ˢ σ₂.φ.source) :
    mfd 𝓘(ℝ, E₁ × E₂) 𝓘(ℝ, W₁ × W₂) (Prod.map (sliceDef σ₁) (sliceDef σ₂)) p =
      ((ContinuousLinearMap.snd ℝ Z₁ W₁).comp (fderiv ℝ σ₁.φ p.1)).prodMap
        ((ContinuousLinearMap.snd ℝ Z₂ W₂).comp (fderiv ℝ σ₂.φ p.2)) :=
  mfderiv_eq_fderiv.trans
    ((hasFDerivAt_sliceDef σ₁ hp.1).prodMap p (hasFDerivAt_sliceDef σ₂ hp.2)).fderiv

/-- The local defining function of `M × N` is a submersion. -/
theorem surjective_mfderiv_prodDef (σ₁ : SliceChart 𝓘(ℝ, E₁) Z₁ W₁ M)
    (σ₂ : SliceChart 𝓘(ℝ, E₂) Z₂ W₂ N) {p : E₁ × E₂} (hp : p ∈ σ₁.φ.source ×ˢ σ₂.φ.source) :
    Surjective (mfderiv 𝓘(ℝ, E₁ × E₂) 𝓘(ℝ, W₁ × W₂) (Prod.map (sliceDef σ₁) (sliceDef σ₂)) p) := by
  change Surjective (mfd 𝓘(ℝ, E₁ × E₂) 𝓘(ℝ, W₁ × W₂) (Prod.map (sliceDef σ₁) (sliceDef σ₂)) p)
  rw [mfd_prodDef σ₁ σ₂ hp]
  rintro ⟨w₁, w₂⟩
  obtain ⟨v₁, hv₁⟩ := surjective_fderiv_sliceDef σ₁ hp.1 w₁
  obtain ⟨v₂, hv₂⟩ := surjective_fderiv_sliceDef σ₂ hp.2 w₂
  exact ⟨(v₁, v₂), Prod.ext hv₁ hv₂⟩

variable [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [FiniteDimensional ℝ Z₁]
  [FiniteDimensional ℝ Z₂] [FiniteDimensional ℝ W₁] [FiniteDimensional ℝ W₂]

/-- **Problem 8, the product is a manifold.** -/
theorem isSliceSubmanifold_prod (hM : IsSliceSubmanifold 𝓘(ℝ, E₁) Z₁ W₁ M)
    (hN : IsSliceSubmanifold 𝓘(ℝ, E₂) Z₂ W₂ N) :
    IsSliceSubmanifold 𝓘(ℝ, E₁ × E₂) (Z₁ × Z₂) (W₁ × W₂) (M ×ˢ N) := by
  intro p hp
  have h1 := IsSliceSubmanifold.finrank_add hM ⟨p.1, hp.1⟩
  have h2 := IsSliceSubmanifold.finrank_add hN ⟨p.2, hp.2⟩
  refine IsSliceSubmanifold.of_locally_preimage (F := W₁ × W₂)
    (by simp only [finrank_prod]; omega) ?_ p hp
  intro q hq
  obtain ⟨σ₁, hσ₁⟩ := hM q.1 hq.1
  obtain ⟨σ₂, hσ₂⟩ := hN q.2 hq.2
  exact ⟨σ₁.φ.source ×ˢ σ₂.φ.source, σ₁.φ.open_source.prod σ₂.φ.open_source, ⟨hσ₁, hσ₂⟩,
    Prod.map (sliceDef σ₁) (sliceDef σ₂), contMDiffOn_prodDef σ₁ σ₂,
    fun y hy => prodDef_eq_zero_iff σ₁ σ₂ hy, fun y hy _ => surjective_mfderiv_prodDef σ₁ σ₂ hy⟩

/-- **Problem 8.** `T(M × N)_(x,y) = TMₓ × TN_y` (tangent spaces as ranges of the derivatives of
the inclusions). -/
theorem range_mfd_val_prod (hM : IsSliceSubmanifold 𝓘(ℝ, E₁) Z₁ W₁ M)
    (hN : IsSliceSubmanifold 𝓘(ℝ, E₂) Z₂ W₂ N) (q : M ×ˢ N) :
    letI := (isSliceSubmanifold_prod hM hN).chartedSpace; letI := hM.chartedSpace
    letI := hN.chartedSpace
    LinearMap.range (mfd 𝓘(ℝ, Z₁ × Z₂) 𝓘(ℝ, E₁ × E₂) (Subtype.val : M ×ˢ N → E₁ × E₂) q :
        Z₁ × Z₂ →ₗ[ℝ] E₁ × E₂) =
      (LinearMap.range (mfd 𝓘(ℝ, Z₁) 𝓘(ℝ, E₁) (Subtype.val : M → E₁) ⟨q.1.1, q.2.1⟩ :
          Z₁ →ₗ[ℝ] E₁)).prod
        (LinearMap.range (mfd 𝓘(ℝ, Z₂) 𝓘(ℝ, E₂) (Subtype.val : N → E₂) ⟨q.1.2, q.2.2⟩ :
          Z₂ →ₗ[ℝ] E₂)) := by
  obtain ⟨σ₁, hσ₁⟩ := hM q.1.1 q.2.1
  obtain ⟨σ₂, hσ₂⟩ := hN q.1.2 q.2.2
  have h1 := IsSliceSubmanifold.finrank_add hM ⟨q.1.1, q.2.1⟩
  have h2 := IsSliceSubmanifold.finrank_add hN ⟨q.1.2, q.2.2⟩
  have hq : q.1 ∈ σ₁.φ.source ×ˢ σ₂.φ.source := ⟨hσ₁, hσ₂⟩
  -- The tangent spaces of `M × N`, `M` and `N` are the kernels of the local defining functions.
  rw [IsSliceSubmanifold.range_mfderiv_val_eq_ker (isSliceSubmanifold_prod hM hN) (F := W₁ × W₂)
      (by simp only [finrank_prod]; omega) q (σ₁.φ.open_source.prod σ₂.φ.open_source) hq
      (contMDiffOn_prodDef σ₁ σ₂) (fun y hy hyS => (prodDef_eq_zero_iff σ₁ σ₂ hy).1 hyS)
      (surjective_mfderiv_prodDef σ₁ σ₂ hq),
    range_mfd_val_eq_ker_sliceChart hM ⟨q.1.1, q.2.1⟩ σ₁ hσ₁,
    range_mfd_val_eq_ker_sliceChart hN ⟨q.1.2, q.2.2⟩ σ₂ hσ₂, mfd_prodDef σ₁ σ₂ hq,
    ContinuousLinearMap.coe_prodMap, LinearMap.ker_prodMap]

end prod

/-! ### Problem 9: the graph -/

/-- The graph of `f : M → N`. -/
def graph (f : M → N) : Set (E₁ × E₂) := {q | ∃ x : M, q = (x.1, (f x).1)}

section graph

section ext

variable (σ : SliceChart 𝓘(ℝ, E₁) Z₁ W₁ M) (f : M → N)

/-- The open set `{a ∈ dom φ | ((φ a).1, 0) ∈ im φ}` on which `graphExt σ f` is smooth. -/
def graphDom : Set E₁ := σ.φ.source ∩ (fun a => (σ.φ a).1) ⁻¹' σ.toChart.target

/-- The extension `a ↦ f (φ⁻¹ ((φ a).1, 0))` of `f` to a neighbourhood in `E₁`. -/
def graphExt (a : E₁) : E₂ := (f (σ.invChart (σ.φ a).1)).1

/-- The local defining function of the graph: `(a, b) ↦ ((φ a).2, b - f̃ a)`. -/
def graphDef (p : E₁ × E₂) : W₁ × E₂ := (sliceDef σ p.1, p.2 - graphExt σ f p.1)

theorem isOpen_graphDom : IsOpen (graphDom σ) :=
  (continuous_fst.comp_continuousOn (contDiffOn_sliceChart σ).continuousOn).isOpen_inter_preimage
    σ.φ.open_source σ.toChart.open_target

theorem mem_graphDom (x : M) (hx : x.1 ∈ σ.φ.source) : x.1 ∈ graphDom σ :=
  ⟨hx, σ.mk_zero_mem_target hx x.2⟩

omit [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] in
/-- `f̃` extends `f`. -/
theorem graphExt_val (x : M) (hx : x.1 ∈ σ.φ.source) : graphExt σ f x.1 = (f x).1 := by
  have h : σ.invChart (σ.φ x.1).1 = x := σ.toChart.left_inv hx
  rw [graphExt, h]

/-- `f̃` is smooth: it is `ι_N ∘ f ∘ ψ⁻¹ ∘ fst ∘ φ`, where `ψ` is the chart of `M` induced by
`φ`. -/
theorem contDiffOn_graphExt (hM : IsSliceSubmanifold 𝓘(ℝ, E₁) Z₁ W₁ M)
    (hN : IsSliceSubmanifold 𝓘(ℝ, E₂) Z₂ W₂ N)
    (hf : letI := hM.chartedSpace; letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z₁) 𝓘(ℝ, Z₂) ∞ f) :
    ContDiffOn ℝ ∞ (graphExt σ f) (graphDom σ) := by
  let := hM.chartedSpace
  let := hN.chartedSpace
  have := hM.isManifold
  have hchart : σ.toChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, Z₁) ∞ M :=
    IsManifold.subset_maximalAtlas ((hM.mem_atlas_iff _).2 ⟨σ, rfl⟩)
  have h1 : ContMDiffOn 𝓘(ℝ, Z₁) 𝓘(ℝ, Z₁) ∞ σ.toChart.symm σ.toChart.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hchart
  have h2 : ContMDiffOn 𝓘(ℝ, E₁) 𝓘(ℝ, Z₁) ∞ (fun a => (σ.φ a).1) (graphDom σ) :=
    (contDiff_fst.comp_contDiffOn ((contDiffOn_sliceChart σ).mono inter_subset_left)).contMDiffOn
  have h3 := (hN.contMDiff_val.comp hf).comp_contMDiffOn (h1.comp h2 fun a ha => ha.2)
  exact contMDiffOn_iff_contDiffOn.1 h3

theorem contMDiffOn_graphDef (hM : IsSliceSubmanifold 𝓘(ℝ, E₁) Z₁ W₁ M)
    (hN : IsSliceSubmanifold 𝓘(ℝ, E₂) Z₂ W₂ N)
    (hf : letI := hM.chartedSpace; letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z₁) 𝓘(ℝ, Z₂) ∞ f) :
    ContMDiffOn 𝓘(ℝ, E₁ × E₂) 𝓘(ℝ, W₁ × E₂) ∞ (graphDef σ f) (graphDom σ ×ˢ univ) := by
  have h1 : ContDiffOn ℝ ∞ (fun p : E₁ × E₂ => sliceDef σ p.1) (graphDom σ ×ˢ univ) :=
    ((contDiffOn_sliceDef σ).mono inter_subset_left).comp contDiff_fst.contDiffOn
      (fun p hp => hp.1)
  have h2 : ContDiffOn ℝ ∞ (fun p : E₁ × E₂ => graphExt σ f p.1) (graphDom σ ×ˢ univ) :=
    (contDiffOn_graphExt σ f hM hN hf).comp contDiff_fst.contDiffOn (fun p hp => hp.1)
  exact (h1.prodMk (contDiff_snd.contDiffOn.sub h2)).contMDiffOn

omit [NormedSpace ℝ E₂] in
/-- Over the chart domain, the graph is the zero set of the local defining function. -/
theorem graphDef_eq_zero_iff {p : E₁ × E₂} (hp : p.1 ∈ σ.φ.source) :
    p ∈ graph f ↔ graphDef σ f p = 0 := by
  obtain ⟨a, b⟩ := p
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
    refine Prod.ext ((σ.slice x.1 hp).1 x.2) ?_
    change (f x).1 - graphExt σ f x.1 = 0
    rw [graphExt_val σ f x hp, sub_self]
  · intro h
    have h1 : sliceDef σ a = 0 := congrArg Prod.fst h
    have h2 : b - graphExt σ f a = 0 := congrArg Prod.snd h
    have haM : a ∈ M := (σ.slice a hp).2 h1
    exact ⟨⟨a, haM⟩, Prod.ext rfl ((sub_eq_zero.1 h2).trans (graphExt_val σ f ⟨a, haM⟩ hp))⟩

theorem hasFDerivAt_graphDef (hM : IsSliceSubmanifold 𝓘(ℝ, E₁) Z₁ W₁ M)
    (hN : IsSliceSubmanifold 𝓘(ℝ, E₂) Z₂ W₂ N)
    (hf : letI := hM.chartedSpace; letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z₁) 𝓘(ℝ, Z₂) ∞ f)
    {p : E₁ × E₂} (hp : p.1 ∈ graphDom σ) :
    HasFDerivAt (graphDef σ f)
      ((((ContinuousLinearMap.snd ℝ Z₁ W₁).comp (fderiv ℝ σ.φ p.1)).comp
          (ContinuousLinearMap.fst ℝ E₁ E₂)).prod
        (ContinuousLinearMap.snd ℝ E₁ E₂ -
          (fderiv ℝ (graphExt σ f) p.1).comp (ContinuousLinearMap.fst ℝ E₁ E₂))) p := by
  have hd1 := (hasFDerivAt_sliceDef σ hp.1).comp p (hasFDerivAt_fst (p := p))
  have hd2 : HasFDerivAt (graphExt σ f) (fderiv ℝ (graphExt σ f) p.1) p.1 :=
    (((contDiffOn_graphExt σ f hM hN hf).contDiffAt
      ((isOpen_graphDom σ).mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  exact hd1.prodMk (hasFDerivAt_snd.sub (hd2.comp p hasFDerivAt_fst))

theorem mfd_graphDef (hM : IsSliceSubmanifold 𝓘(ℝ, E₁) Z₁ W₁ M)
    (hN : IsSliceSubmanifold 𝓘(ℝ, E₂) Z₂ W₂ N)
    (hf : letI := hM.chartedSpace; letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z₁) 𝓘(ℝ, Z₂) ∞ f)
    {p : E₁ × E₂} (hp : p.1 ∈ graphDom σ) :
    mfd 𝓘(ℝ, E₁ × E₂) 𝓘(ℝ, W₁ × E₂) (graphDef σ f) p =
      (((ContinuousLinearMap.snd ℝ Z₁ W₁).comp (fderiv ℝ σ.φ p.1)).comp
          (ContinuousLinearMap.fst ℝ E₁ E₂)).prod
        (ContinuousLinearMap.snd ℝ E₁ E₂ -
          (fderiv ℝ (graphExt σ f) p.1).comp (ContinuousLinearMap.fst ℝ E₁ E₂)) :=
  mfderiv_eq_fderiv.trans (hasFDerivAt_graphDef σ f hM hN hf hp).fderiv

/-- The local defining function of the graph is a submersion: `(v, w) ↦ (D v, w - df̃ v)` with
`D` surjective. -/
theorem surjective_mfderiv_graphDef (hM : IsSliceSubmanifold 𝓘(ℝ, E₁) Z₁ W₁ M)
    (hN : IsSliceSubmanifold 𝓘(ℝ, E₂) Z₂ W₂ N)
    (hf : letI := hM.chartedSpace; letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z₁) 𝓘(ℝ, Z₂) ∞ f)
    {p : E₁ × E₂} (hp : p.1 ∈ graphDom σ) :
    Surjective (mfderiv 𝓘(ℝ, E₁ × E₂) 𝓘(ℝ, W₁ × E₂) (graphDef σ f) p) := by
  change Surjective (mfd 𝓘(ℝ, E₁ × E₂) 𝓘(ℝ, W₁ × E₂) (graphDef σ f) p)
  rw [mfd_graphDef σ f hM hN hf hp]
  rintro ⟨z, w⟩
  obtain ⟨v, hv⟩ := surjective_fderiv_sliceDef σ hp.1 z
  refine ⟨(v, w + fderiv ℝ (graphExt σ f) p.1 v), Prod.ext hv ?_⟩
  change w + fderiv ℝ (graphExt σ f) p.1 v - fderiv ℝ (graphExt σ f) p.1 v = w
  rw [add_sub_cancel_right]

end ext

variable [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [FiniteDimensional ℝ Z₁]
  [FiniteDimensional ℝ W₁]

/-- **Problem 9, the graph is a manifold.** -/
theorem isSliceSubmanifold_graph (hM : IsSliceSubmanifold 𝓘(ℝ, E₁) Z₁ W₁ M)
    (hN : IsSliceSubmanifold 𝓘(ℝ, E₂) Z₂ W₂ N) {f : M → N}
    (hf : letI := hM.chartedSpace; letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z₁) 𝓘(ℝ, Z₂) ∞ f) :
    IsSliceSubmanifold 𝓘(ℝ, E₁ × E₂) Z₁ (W₁ × E₂) (graph f) := by
  rintro _ ⟨x, rfl⟩
  have h1 := IsSliceSubmanifold.finrank_add hM ⟨x.1, x.2⟩
  refine IsSliceSubmanifold.of_locally_preimage (F := W₁ × E₂)
    (by simp only [finrank_prod]; omega) ?_ _ ⟨x, rfl⟩
  rintro _ ⟨y, rfl⟩
  obtain ⟨σ, hσ⟩ := hM y.1 y.2
  exact ⟨graphDom σ ×ˢ univ, (isOpen_graphDom σ).prod isOpen_univ,
    ⟨mem_graphDom σ y hσ, trivial⟩, graphDef σ f, contMDiffOn_graphDef σ f hM hN hf,
    fun p hp => graphDef_eq_zero_iff σ f hp.1.1,
    fun p hp _ => surjective_mfderiv_graphDef σ f hM hN hf hp.1⟩

/-- **Problem 9.** `TΓ_(x, f x)` is the graph of `dfₓ`: the image of
`u ↦ (dιₓ u, dι_{f x} (dfₓ u))`. -/
theorem range_mfd_val_graph (hM : IsSliceSubmanifold 𝓘(ℝ, E₁) Z₁ W₁ M)
    (hN : IsSliceSubmanifold 𝓘(ℝ, E₂) Z₂ W₂ N) {f : M → N}
    (hf : letI := hM.chartedSpace; letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z₁) 𝓘(ℝ, Z₂) ∞ f)
    (x : M) :
    letI := (isSliceSubmanifold_graph hM hN hf).chartedSpace; letI := hM.chartedSpace
    letI := hN.chartedSpace
    LinearMap.range (mfd 𝓘(ℝ, Z₁) 𝓘(ℝ, E₁ × E₂) (Subtype.val : graph f → E₁ × E₂)
        ⟨(x.1, (f x).1), x, rfl⟩ : Z₁ →ₗ[ℝ] E₁ × E₂) =
      LinearMap.range (((mfd 𝓘(ℝ, Z₁) 𝓘(ℝ, E₁) (Subtype.val : M → E₁) x).prod
        ((mfd 𝓘(ℝ, Z₂) 𝓘(ℝ, E₂) (Subtype.val : N → E₂) (f x)).comp
          (mfd 𝓘(ℝ, Z₁) 𝓘(ℝ, Z₂) f x)) : Z₁ →L[ℝ] E₁ × E₂) : Z₁ →ₗ[ℝ] E₁ × E₂) := by
  let := hM.chartedSpace
  let := hN.chartedSpace
  have := hM.isManifold
  have := hN.isManifold
  obtain ⟨σ, hσ⟩ := hM x.1 x.2
  have h1 := IsSliceSubmanifold.finrank_add hM ⟨x.1, x.2⟩
  have hx : (x.1, (f x).1).1 ∈ graphDom σ := mem_graphDom σ x hσ
  -- The tangent space of the graph is the kernel of the derivative of `graphDef σ f`.
  rw [IsSliceSubmanifold.range_mfderiv_val_eq_ker (isSliceSubmanifold_graph hM hN hf)
      (F := W₁ × E₂) (by simp only [finrank_prod]; omega) ⟨(x.1, (f x).1), x, rfl⟩
      ((isOpen_graphDom σ).prod isOpen_univ) ⟨hx, trivial⟩ (contMDiffOn_graphDef σ f hM hN hf)
      (fun p hp hpS => (graphDef_eq_zero_iff σ f hp.1.1).1 hpS)
      (surjective_mfderiv_graphDef σ f hM hN hf hx),
    mfd_graphDef σ f hM hN hf hx]
  have hker := range_mfd_val_eq_ker_sliceChart hM x σ hσ
  -- The chain rule for `f̃ ∘ ι_M = ι_N ∘ f` near `x`.
  have hchain : ∀ u : Z₁, fderiv ℝ (graphExt σ f) x.1
      (mfd 𝓘(ℝ, Z₁) 𝓘(ℝ, E₁) (Subtype.val : M → E₁) x u) =
      mfd 𝓘(ℝ, Z₂) 𝓘(ℝ, E₂) (Subtype.val : N → E₂) (f x) (mfd 𝓘(ℝ, Z₁) 𝓘(ℝ, Z₂) f x u) := by
    intro u
    have hvalM : MDifferentiableAt 𝓘(ℝ, Z₁) 𝓘(ℝ, E₁) (Subtype.val : M → E₁) x :=
      hM.contMDiff_val.mdifferentiableAt (by simp)
    have hvalN : MDifferentiableAt 𝓘(ℝ, Z₂) 𝓘(ℝ, E₂) (Subtype.val : N → E₂) (f x) :=
      hN.contMDiff_val.mdifferentiableAt (by simp)
    have hfx : MDifferentiableAt 𝓘(ℝ, Z₁) 𝓘(ℝ, Z₂) f x := hf.mdifferentiableAt (by simp)
    have hext : MDifferentiableAt 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) (graphExt σ f) x.1 :=
      (((contDiffOn_graphExt σ f hM hN hf).contDiffAt
        ((isOpen_graphDom σ).mem_nhds hx)).differentiableAt (by simp)).mdifferentiableAt
    have heq : graphExt σ f ∘ (Subtype.val : M → E₁) =ᶠ[𝓝 x] Subtype.val ∘ f := by
      filter_upwards [(σ.φ.open_source.preimage continuous_subtype_val).mem_nhds hσ] with y hy
      exact graphExt_val σ f y hy
    have h3 : mfderiv 𝓘(ℝ, Z₁) 𝓘(ℝ, E₂) (graphExt σ f ∘ (Subtype.val : M → E₁)) x =
        mfderiv 𝓘(ℝ, Z₁) 𝓘(ℝ, E₂) (Subtype.val ∘ f) x := heq.mfderiv_eq
    rw [mfderiv_comp x hext hvalM, mfderiv_comp x hvalN hfx, mfderiv_eq_fderiv] at h3
    exact DFunLike.congr_fun h3 u
  -- `ker (v, w) ↦ (D v, w - df̃ v) = {(v, w) | v ∈ TMₓ, w = df̃ v}` is the graph of `dι_N ∘ df`.
  ext ⟨v, w⟩
  simp only [LinearMap.mem_ker, LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  constructor
  · intro h
    have hv : v ∈ LinearMap.ker ((ContinuousLinearMap.snd ℝ Z₁ W₁).comp (fderiv ℝ σ.φ x.1) :
        E₁ →ₗ[ℝ] W₁) :=
      LinearMap.mem_ker.2 (congrArg Prod.fst h)
    rw [← hker] at hv
    obtain ⟨u, hu⟩ := LinearMap.mem_range.1 hv
    have hu' : mfd 𝓘(ℝ, Z₁) 𝓘(ℝ, E₁) (Subtype.val : M → E₁) x u = v := hu
    subst hu'
    have h2 : w - fderiv ℝ (graphExt σ f) x.1
        (mfd 𝓘(ℝ, Z₁) 𝓘(ℝ, E₁) (Subtype.val : M → E₁) x u) = 0 :=
      congrArg Prod.snd h
    refine ⟨u, Prod.ext rfl ?_⟩
    change mfd 𝓘(ℝ, Z₂) 𝓘(ℝ, E₂) (Subtype.val : N → E₂) (f x) (mfd 𝓘(ℝ, Z₁) 𝓘(ℝ, Z₂) f x u) = w
    rw [← hchain]
    exact (sub_eq_zero.1 h2).symm
  · rintro ⟨u, hu⟩
    have hv : mfd 𝓘(ℝ, Z₁) 𝓘(ℝ, E₁) (Subtype.val : M → E₁) x u = v := congrArg Prod.fst hu
    have hw : mfd 𝓘(ℝ, Z₂) 𝓘(ℝ, E₂) (Subtype.val : N → E₂) (f x)
        (mfd 𝓘(ℝ, Z₁) 𝓘(ℝ, Z₂) f x u) = w := congrArg Prod.snd hu
    subst hv hw
    have hk : mfd 𝓘(ℝ, Z₁) 𝓘(ℝ, E₁) (Subtype.val : M → E₁) x u ∈
        LinearMap.ker ((ContinuousLinearMap.snd ℝ Z₁ W₁).comp (fderiv ℝ σ.φ x.1) :
          E₁ →ₗ[ℝ] W₁) := by
      rw [← hker]
      exact ⟨u, rfl⟩
    refine Prod.ext (LinearMap.mem_ker.1 hk) ?_
    change mfd 𝓘(ℝ, Z₂) 𝓘(ℝ, E₂) (Subtype.val : N → E₂) (f x) (mfd 𝓘(ℝ, Z₁) 𝓘(ℝ, Z₂) f x u) -
      fderiv ℝ (graphExt σ f) x.1 (mfd 𝓘(ℝ, Z₁) 𝓘(ℝ, E₁) (Subtype.val : M → E₁) x u) = 0
    rw [hchain, sub_self]

end graph

end Problems

end Milnor
