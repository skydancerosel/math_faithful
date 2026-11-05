import Milnor.Chapter8.LocalSlice
import Milnor.Chapter2.Corestrict

/-!
# Problem 10: the tangent bundle

Milnor, *Topology from the Differentiable Viewpoint*, §8, Problem 10:

> Given `M ⊂ ℝᵏ`, show that the tangent bundle space
> `TM = {(x, v) ∈ M × ℝᵏ | v ∈ TMₓ}` is also a smooth manifold. Show that any smooth map
> `f : M → N` gives rise to a smooth map `df : TM → TN` where `d(identity) = identity`,
> `d(g ∘ f) = (dg) ∘ (df)`.

Here `M ⊆ E` is a slice submanifold of a finite-dimensional real normed space `E`, modelled on `Z`
(`Milnor.IsSliceSubmanifold 𝓘(ℝ, E) Z W M`). Its tangent space at `x` is the range of the
derivative of the inclusion (`tangentSpace`), and

* `tangentBundleSet hM ⊆ E × E` is Milnor's `TM`;
* `isSliceSubmanifold_tangentBundle`: `TM` is a slice submanifold of `E × E` modelled on `Z × Z`,
  i.e. a smooth manifold of dimension `2 dim M`;
* `tangentMap hM hN f : TM → TN` is `df (x, v) = (f x, dfₓ v)`, where the tangent vector
  `v ∈ TMₓ ⊆ E` is read in the chart coordinates of `M` (`tangentCoord`);
* `contMDiff_tangentMap`: `df` is smooth when `f` is;
* `tangentMap_id`, `tangentMap_comp`: `d(id) = id` and `d(g ∘ f) = dg ∘ df`.

*Proof that `TM` is a manifold.* Let `φ` be a slice chart of `M` around `x` (a diffeomorphism
from an open set of `E` onto an open set of `Z × W` carrying `M` to `Z × {0}`). On
`U = dom φ × E` consider `g (a, v) = ((φ a)₂, (dφₐ v)₂) ∈ W × W`. For `a ∈ M ∩ dom φ` the tangent
space `TMₐ` is the kernel of `d(pr₂ ∘ φ)ₐ = pr₂ ∘ dφₐ` (Milnor's Lemma 2,
`IsSliceSubmanifold.range_mfderiv_val_eq_ker`), so `TM ∩ U = g⁻¹(0)`. The derivative of `g` at
`(a, v)` is `(u, w) ↦ ((dφₐ u)₂, (dφₐ w)₂ + (d²φₐ(u, v))₂)`, which is onto since `pr₂ ∘ dφₐ` is
onto (`dφₐ` is an isomorphism `E ≅ Z × W`). Hence `TM` is locally the zero set of a submersion,
so a slice submanifold (`IsSliceSubmanifold.of_locally_preimage`).

*Proof that `df` is smooth.* Near `(x, v)`, with the chart `ψ` of `M` at `x` induced by the
slice chart `φ`, the map `ρ(a) = f(ψ⁻¹((φ a)₁))` is a smooth extension of `f` to an open set of
`E`. For `(a, w) ∈ TM` near `(x, v)`, differentiating `ρ ∘ incl = incl ∘ f` gives
`dfₐ w = dρₐ w`, so `df` is the restriction to `TM` of the smooth map `(a, w) ↦ (ρ a, dρₐ w)`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

namespace Problems

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {M : Set E} (hM : IsSliceSubmanifold 𝓘(ℝ, E) Z W M)
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {Z' : Type*} [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] [FiniteDimensional ℝ Z']
  {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
  {N : Set E'} (hN : IsSliceSubmanifold 𝓘(ℝ, E') Z' W' N)
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  {Z'' : Type*} [NormedAddCommGroup Z''] [NormedSpace ℝ Z''] [FiniteDimensional ℝ Z'']
  {W'' : Type*} [NormedAddCommGroup W''] [NormedSpace ℝ W''] [FiniteDimensional ℝ W'']
  {P : Set E''} (hP : IsSliceSubmanifold 𝓘(ℝ, E'') Z'' W'' P)

/-! ### Slice charts of subsets of a vector space -/

section SliceChart

variable (σ : SliceChart 𝓘(ℝ, E) Z W M)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem sliceChart_contDiffOn : ContDiffOn ℝ ∞ σ.φ σ.φ.source :=
  contMDiffOn_iff_contDiffOn.1 σ.φ.contMDiffOn

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem sliceChart_contDiffOn_invFun : ContDiffOn ℝ ∞ σ.φ.invFun σ.φ.target :=
  contMDiffOn_iff_contDiffOn.1 σ.φ.contMDiffOn_invFun

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem sliceChart_differentiableAt {a : E} (ha : a ∈ σ.φ.source) : DifferentiableAt ℝ σ.φ a :=
  ((sliceChart_contDiffOn σ).contDiffAt (σ.φ.open_source.mem_nhds ha)).differentiableAt (by simp)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The derivative of a slice chart is a linear isomorphism `E ≃ Z × W`. -/
theorem sliceChart_exists_equiv {a : E} (ha : a ∈ σ.φ.source) :
    ∃ e : E ≃L[ℝ] Z × W, (e : E →L[ℝ] Z × W) = fderiv ℝ σ.φ a := by
  have hb : σ.φ a ∈ σ.φ.target := σ.φ.apply_mem ha
  have hψa : σ.φ.invFun (σ.φ a) = a := σ.φ.invFun_apply ha
  have hφd := sliceChart_differentiableAt σ ha
  have hψd : DifferentiableAt ℝ σ.φ.invFun (σ.φ a) :=
    ((sliceChart_contDiffOn_invFun σ).contDiffAt (σ.φ.open_target.mem_nhds hb)).differentiableAt
      (by simp)
  have hφd' : DifferentiableAt ℝ σ.φ (σ.φ.invFun (σ.φ a)) := by rw [hψa]; exact hφd
  have h1 : fderiv ℝ (σ.φ.invFun ∘ σ.φ) a = fderiv ℝ id a := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [σ.φ.open_source.mem_nhds ha] with b hb
    exact σ.φ.invFun_apply hb
  rw [fderiv_comp a hψd hφd, fderiv_id] at h1
  have h2 : fderiv ℝ (σ.φ ∘ σ.φ.invFun) (σ.φ a) = fderiv ℝ id (σ.φ a) := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [σ.φ.open_target.mem_nhds hb] with y hy
    exact σ.φ.apply_invFun hy
  rw [fderiv_comp (σ.φ a) hφd' hψd, fderiv_id, hψa] at h2
  exact ⟨ContinuousLinearEquiv.equivOfInverse (fderiv ℝ σ.φ a) (fderiv ℝ σ.φ.invFun (σ.φ a))
    (fun v => DFunLike.congr_fun h1 v) (fun w => DFunLike.congr_fun h2 w), rfl⟩

omit [FiniteDimensional ℝ E] in
include σ in
/-- The dimension count `dim Z + dim W = dim E` forced by a slice chart. -/
theorem sliceChart_finrank : finrank ℝ Z + finrank ℝ W = finrank ℝ E := by
  obtain ⟨e, -⟩ := sliceChart_exists_equiv σ σ.x₀_source
  rw [← Module.finrank_prod]
  exact e.toLinearEquiv.finrank_eq.symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem sliceChart_surjective_snd {a : E} (ha : a ∈ σ.φ.source) :
    Surjective fun v => (fderiv ℝ σ.φ a v).2 := by
  obtain ⟨e, he⟩ := sliceChart_exists_equiv σ ha
  intro w
  refine ⟨e.symm (0, w), ?_⟩
  show (fderiv ℝ σ.φ a (e.symm (0, w))).2 = w
  rw [← he]
  simp

end SliceChart

/-! ### The tangent bundle space -/

/-- The tangent space `TMₓ ⊆ E` of `M` at `x`: the range of the derivative of the inclusion. -/
def tangentSpace (x : M) : Submodule ℝ E :=
  letI := hM.chartedSpace
  LinearMap.range (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : M → E) x : Z →ₗ[ℝ] E)

/-- The tangent bundle space `TM = {(x, v) ∈ M × E | v ∈ TMₓ}`. -/
def tangentBundleSet : Set (E × E) :=
  {q | ∃ hx : q.1 ∈ M, q.2 ∈ tangentSpace hM ⟨q.1, hx⟩}

/-- In the domain of a slice chart `φ`, the tangent space of `M` is the kernel of
`pr₂ ∘ dφ` (Milnor's Lemma 2). -/
theorem sliceChart_mem_tangentSpace_iff (σ : SliceChart 𝓘(ℝ, E) Z W M) {a : M}
    (ha : a.1 ∈ σ.φ.source) (v : E) :
    v ∈ tangentSpace hM a ↔ (fderiv ℝ σ.φ a v).2 = 0 := by
  let _ := hM.chartedSpace
  have hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, W) ∞ (fun b => (σ.φ b).2) σ.φ.source :=
    contMDiffOn_iff_contDiffOn.2 (contDiff_snd.comp_contDiffOn (sliceChart_contDiffOn σ))
  have hgS : ∀ y ∈ σ.φ.source, y ∈ M → (σ.φ y).2 = 0 := fun y hy hyM => (σ.slice y hy).1 hyM
  have hD : HasFDerivAt (fun b => (σ.φ b).2)
      ((ContinuousLinearMap.snd ℝ Z W).comp (fderiv ℝ σ.φ a)) a :=
    (sliceChart_differentiableAt σ ha).hasFDerivAt.snd
  have hsurj : Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, W) (fun b => (σ.φ b).2) a.1) := by
    rw [mfderiv_eq_fderiv, hD.fderiv]
    exact sliceChart_surjective_snd σ ha
  have hker := hM.range_mfderiv_val_eq_ker (sliceChart_finrank σ) a σ.φ.open_source ha hg hgS hsurj
  have hmfd : mfd 𝓘(ℝ, E) 𝓘(ℝ, W) (fun b => (σ.φ b).2) a.1 =
      (ContinuousLinearMap.snd ℝ Z W).comp (fderiv ℝ σ.φ a) :=
    HasMFDerivAt.mfd_eq hD.hasMFDerivAt
  unfold tangentSpace
  rw [hker, LinearMap.mem_ker, hmfd]
  rfl

/-- **Problem 10, first part.** The tangent bundle space `TM ⊆ E × E` is a smooth manifold of
dimension `2 dim M`: a slice submanifold modelled on `Z × Z`. -/
theorem isSliceSubmanifold_tangentBundle :
    IsSliceSubmanifold 𝓘(ℝ, E × E) (Z × Z) (W × W) (tangentBundleSet hM) := by
  intro p hp
  obtain ⟨σ₀, -⟩ := hM p.1 hp.fst
  have hZ : finrank ℝ (Z × Z) + finrank ℝ (W × W) = finrank ℝ (E × E) := by
    have := sliceChart_finrank σ₀
    simp only [Module.finrank_prod]
    omega
  refine IsSliceSubmanifold.of_locally_preimage hZ ?_ p hp
  intro q hq
  obtain ⟨σ, hσ⟩ := hM q.1 hq.fst
  refine ⟨σ.φ.source ×ˢ univ, σ.φ.open_source.prod isOpen_univ, ⟨hσ, trivial⟩,
    fun r => ((σ.φ r.1).2, (fderiv ℝ σ.φ r.1 r.2).2), ?_, ?_, ?_⟩
  · -- smoothness of the local defining function
    rw [contMDiffOn_iff_contDiffOn]
    have h1 : ContDiffOn ℝ ∞ (fun r : E × E => σ.φ r.1) (σ.φ.source ×ˢ univ) :=
      (sliceChart_contDiffOn σ).comp contDiff_fst.contDiffOn fun r hr => hr.1
    have h2 : ContDiffOn ℝ ∞ (fun r : E × E => fderiv ℝ σ.φ r.1) (σ.φ.source ×ˢ univ) :=
      ((sliceChart_contDiffOn σ).fderiv_of_isOpen σ.φ.open_source (by simp)).comp
        contDiff_fst.contDiffOn fun r hr => hr.1
    exact (contDiff_snd.comp_contDiffOn h1).prodMk
      (contDiff_snd.comp_contDiffOn (h2.clm_apply contDiff_snd.contDiffOn))
  · -- `TM` is its zero set
    rintro ⟨a, v⟩ ⟨ha, -⟩
    simp only [Prod.mk_eq_zero]
    constructor
    · rintro ⟨haM, hv⟩
      exact ⟨(σ.slice a ha).1 haM,
        (sliceChart_mem_tangentSpace_iff hM σ (a := ⟨a, haM⟩) ha v).1 hv⟩
    · rintro ⟨h1, h2⟩
      have haM : a ∈ M := (σ.slice a ha).2 h1
      exact ⟨haM, (sliceChart_mem_tangentSpace_iff hM σ (a := ⟨a, haM⟩) ha v).2 h2⟩
  · -- its derivative is onto along `TM`
    rintro ⟨a, v⟩ ⟨ha, -⟩ -
    have ha' : a ∈ σ.φ.source := ha
    have hφa : HasFDerivAt σ.φ (fderiv ℝ σ.φ a) a :=
      (sliceChart_differentiableAt σ ha').hasFDerivAt
    have hφ2 : HasFDerivAt (fderiv ℝ σ.φ) (fderiv ℝ (fderiv ℝ σ.φ) a) a :=
      ((((sliceChart_contDiffOn σ).contDiffAt (σ.φ.open_source.mem_nhds ha')).fderiv_right
        (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
    have hA : HasFDerivAt (fun r : E × E => σ.φ r.1)
        ((fderiv ℝ σ.φ a).comp (ContinuousLinearMap.fst ℝ E E)) (a, v) :=
      hφa.comp (a, v) hasFDerivAt_fst
    have hB : HasFDerivAt (fun r : E × E => fderiv ℝ σ.φ r.1)
        ((fderiv ℝ (fderiv ℝ σ.φ) a).comp (ContinuousLinearMap.fst ℝ E E)) (a, v) :=
      hφ2.comp (a, v) hasFDerivAt_fst
    have hC := hB.clm_apply hasFDerivAt_snd
    have hg := hA.snd.prodMk hC.snd
    rw [mfderiv_eq_fderiv, hg.fderiv]
    rintro ⟨y₁, y₂⟩
    obtain ⟨u, hu⟩ := sliceChart_surjective_snd σ ha' y₁
    obtain ⟨w, hw⟩ := sliceChart_surjective_snd σ ha' (y₂ - (fderiv ℝ (fderiv ℝ σ.φ) a u v).2)
    have hu' : (fderiv ℝ σ.φ a u).2 = y₁ := hu
    have hw' : (fderiv ℝ σ.φ a w).2 = y₂ - (fderiv ℝ (fderiv ℝ σ.φ) a u v).2 := hw
    refine ⟨(u, w), Prod.ext ?_ ?_⟩
    · exact hu'
    · show (fderiv ℝ σ.φ a w).2 + (fderiv ℝ (fderiv ℝ σ.φ) a u v).2 = y₂
      rw [hw', sub_add_cancel]

/-! ### The tangent map -/

/-- The chart coordinates of an ambient vector tangent to `M` at `x`: the (unique) `w ∈ Z` with
`d(incl)ₓ w = v`. -/
def tangentCoord (x : M) (v : E) : Z :=
  letI := hM.chartedSpace
  Function.invFun (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : M → E) x) v

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem mfd_val_tangentCoord {x : M} {v : E} (hv : v ∈ tangentSpace hM x) :
    letI := hM.chartedSpace
    mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : M → E) x (tangentCoord hM x v) = v := by
  let _ := hM.chartedSpace
  obtain ⟨a, ha⟩ := (LinearMap.mem_range).1 hv
  exact Function.invFun_eq ⟨a, ha⟩

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem tangentCoord_mfd_val (x : M) (u : Z) :
    letI := hM.chartedSpace
    tangentCoord hM x (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : M → E) x u) = u := by
  let _ := hM.chartedSpace
  exact Function.leftInverse_invFun (injective_mfderiv_val hM x) u

/-- The differential `df : TM → TN`, `(x, v) ↦ (f x, dfₓ v)`, where `dfₓ` is read on ambient
tangent vectors: `v ∈ TMₓ ⊆ E` is written in chart coordinates, pushed forward by `dfₓ`, and
included into `E'`. -/
def tangentMap (f : M → N) : tangentBundleSet hM → tangentBundleSet hN := fun q =>
  letI := hM.chartedSpace
  letI := hN.chartedSpace
  ⟨((f ⟨q.1.1, q.2.fst⟩).1, mfd 𝓘(ℝ, Z') 𝓘(ℝ, E') (Subtype.val : N → E') (f ⟨q.1.1, q.2.fst⟩)
      (mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z') f ⟨q.1.1, q.2.fst⟩ (tangentCoord hM ⟨q.1.1, q.2.fst⟩ q.1.2))),
    (f ⟨q.1.1, q.2.fst⟩).2, LinearMap.mem_range_self _ _⟩

/-- **Problem 10.** The differential `df : TM → TN` of a smooth map is smooth. -/
theorem contMDiff_tangentMap {f : M → N}
    (hf : letI := hM.chartedSpace; letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, Z') ∞ f) :
    letI := (isSliceSubmanifold_tangentBundle hM).chartedSpace
    letI := (isSliceSubmanifold_tangentBundle hN).chartedSpace
    ContMDiff 𝓘(ℝ, Z × Z) 𝓘(ℝ, Z' × Z') ∞ (tangentMap hM hN f) := by
  let _ := hM.chartedSpace
  have _ := hM.isManifold
  let _ := hN.chartedSpace
  have _ := hN.isManifold
  let _ := (isSliceSubmanifold_tangentBundle hM).chartedSpace
  have _ := (isSliceSubmanifold_tangentBundle hM).isManifold
  let _ := (isSliceSubmanifold_tangentBundle hN).chartedSpace
  refine (isSliceSubmanifold_tangentBundle hN).contMDiff_codRestrict
    (F := fun q => (tangentMap hM hN f q).1) ?_ (fun q => (tangentMap hM hN f q).2)
  intro q₀
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : M, x₀ = ⟨q₀.1.1, q₀.2.fst⟩ := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ, (hM x₀.1 x₀.2).choose = σ := ⟨_, rfl⟩
  have hx₀σ : x₀.1 ∈ σ.φ.source := hσ ▸ (hM x₀.1 x₀.2).choose_spec
  have hchart : chartAt Z x₀ = σ.toChart := by rw [hM.chartAt_eq, hσ]
  -- A smooth extension `ρ` of `f` to an open set `V ⊆ E`.
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : E → E',
      ρ = fun a => ((f ((chartAt Z x₀).symm (σ.φ a).1) : N) : E') := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V : Set E,
      V = σ.φ.source ∩ (fun a => (σ.φ a).1) ⁻¹' (chartAt Z x₀).target := ⟨_, rfl⟩
  have hV : IsOpen V := by
    rw [hVdef]
    exact (continuous_fst.comp_continuousOn σ.φ.contMDiffOn.continuousOn).isOpen_inter_preimage
      σ.φ.open_source (chartAt Z x₀).open_target
  have hsymm : ∀ b : M, b.1 ∈ σ.φ.source →
      (σ.φ b.1).1 = chartAt Z x₀ b ∧ b ∈ (chartAt Z x₀).source := by
    intro b hb
    rw [hchart]
    exact ⟨rfl, hb⟩
  have hVM : ∀ b : M, b.1 ∈ σ.φ.source → b.1 ∈ V := by
    intro b hb
    rw [hVdef]
    refine ⟨hb, ?_⟩
    show (σ.φ b.1).1 ∈ (chartAt Z x₀).target
    rw [(hsymm b hb).1]
    exact (chartAt Z x₀).map_source (hsymm b hb).2
  have hρM : ∀ b : M, b.1 ∈ σ.φ.source → ρ b.1 = (f b).1 := by
    intro b hb
    rw [hρdef]
    show ((f ((chartAt Z x₀).symm (σ.φ b.1).1) : N) : E') = (f b).1
    rw [(hsymm b hb).1, (chartAt Z x₀).left_inv (hsymm b hb).2]
  have hρ : ContDiffOn ℝ ∞ ρ V := by
    have h1 : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, Z) ∞ (chartAt Z x₀).symm (chartAt Z x₀).target :=
      contMDiffOn_chart_symm
    have h2 : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E') ∞
        (fun z => ((f ((chartAt Z x₀).symm z) : N) : E')) (chartAt Z x₀).target :=
      (hN.contMDiff_val.comp hf).comp_contMDiffOn h1
    have h3 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Z) ∞ (fun a => (σ.φ a).1) σ.φ.source :=
      (contDiff_fst.contMDiff).comp_contMDiffOn σ.φ.contMDiffOn
    have h4 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ ρ V := by
      rw [hρdef, hVdef]
      exact h2.comp (h3.mono inter_subset_left) fun a ha => ha.2
    exact contMDiffOn_iff_contDiffOn.1 h4
  -- On `TM`, the second component of `df` is `dρ`.
  have key : ∀ b : M, b.1 ∈ σ.φ.source → ∀ w ∈ tangentSpace hM b,
      fderiv ℝ ρ b.1 w = mfd 𝓘(ℝ, Z') 𝓘(ℝ, E') (Subtype.val : N → E') (f b)
        (mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z') f b (tangentCoord hM b w)) := by
    intro b hb w hw
    have hρd : DifferentiableAt ℝ ρ b.1 :=
      (hρ.contDiffAt (hV.mem_nhds (hVM b hb))).differentiableAt (by simp)
    have hloc : (Subtype.val ∘ f) =ᶠ[𝓝 b] (ρ ∘ (Subtype.val : M → E)) := by
      filter_upwards [(σ.φ.open_source.preimage continuous_subtype_val).mem_nhds hb] with c hc
      exact (hρM c hc).symm
    have hval : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : M → E) b :=
      hM.contMDiff_val.mdifferentiableAt (by simp)
    have hfb : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, Z') f b := hf.mdifferentiableAt (by simp)
    have hvalN : MDifferentiableAt 𝓘(ℝ, Z') 𝓘(ℝ, E') (Subtype.val : N → E') (f b) :=
      hN.contMDiff_val.mdifferentiableAt (by simp)
    have h1 : HasMFDerivAt 𝓘(ℝ, Z) 𝓘(ℝ, E') (ρ ∘ Subtype.val) b
        ((fderiv ℝ ρ b.1).comp (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : M → E) b) : Z →L[ℝ] E') :=
      hρd.hasFDerivAt.hasMFDerivAt.comp b (hasMFDerivAt_mfd hval)
    have h2 : HasMFDerivAt 𝓘(ℝ, Z) 𝓘(ℝ, E') (Subtype.val ∘ f) b
        ((mfd 𝓘(ℝ, Z') 𝓘(ℝ, E') (Subtype.val : N → E') (f b)).comp
          (mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z') f b) : Z →L[ℝ] E') :=
      (hasMFDerivAt_mfd hvalN).comp b (hasMFDerivAt_mfd hfb)
    have h3 := (HasMFDerivAt.mfd_eq (h1.congr_of_eventuallyEq hloc)).symm.trans
      (HasMFDerivAt.mfd_eq h2)
    have h4 := DFunLike.congr_fun h3 (tangentCoord hM b w)
    simp only [ContinuousLinearMap.comp_apply] at h4
    rw [mfd_val_tangentCoord hM hw] at h4
    exact h4
  -- Hence, near `q₀`, `df` is the restriction of the smooth map `(a, w) ↦ (ρ a, dρₐ w)`.
  have hG : ContDiffOn ℝ ∞ (fun r : E × E => (ρ r.1, fderiv ℝ ρ r.1 r.2)) (V ×ˢ univ) := by
    have hρ' : ContDiffOn ℝ ∞ (fderiv ℝ ρ) V := hρ.fderiv_of_isOpen hV (by simp)
    exact (hρ.comp contDiff_fst.contDiffOn fun r hr => hr.1).prodMk
      ((hρ'.comp contDiff_fst.contDiffOn fun r hr => hr.1).clm_apply contDiff_snd.contDiffOn)
  have hq₀V : q₀.1 ∈ V ×ˢ univ := by
    refine ⟨?_, trivial⟩
    have := hVM x₀ hx₀σ
    rw [hx₀] at this
    exact this
  have hGat : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E' × E') ∞
      (fun r : E × E => (ρ r.1, fderiv ℝ ρ r.1 r.2)) q₀.1 :=
    (hG.contDiffAt ((hV.prod isOpen_univ).mem_nhds hq₀V)).contMDiffAt
  have hcomp := hGat.comp q₀ (isSliceSubmanifold_tangentBundle hM).contMDiff_val.contMDiffAt
  refine hcomp.congr_of_eventuallyEq ?_
  have hx₀σ' : q₀.1.1 ∈ σ.φ.source := by rw [hx₀] at hx₀σ; exact hx₀σ
  filter_upwards [(σ.φ.open_source.preimage (continuous_fst.comp continuous_subtype_val)).mem_nhds
    hx₀σ'] with q hq
  refine Prod.ext ?_ ?_
  · exact (hρM ⟨q.1.1, q.2.fst⟩ hq).symm
  · exact (key ⟨q.1.1, q.2.fst⟩ hq q.1.2 q.2.snd).symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Problem 10.** `d(identity) = identity`. -/
theorem tangentMap_id : tangentMap hM hM id = id := by
  let _ := hM.chartedSpace
  funext q
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · show mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : M → E) ⟨q.1.1, q.2.fst⟩
      (mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z) (id : M → M) ⟨q.1.1, q.2.fst⟩
        (tangentCoord hM ⟨q.1.1, q.2.fst⟩ q.1.2)) = q.1.2
    have hid : mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z) (id : M → M) ⟨q.1.1, q.2.fst⟩ = ContinuousLinearMap.id ℝ Z :=
      mfderiv_id
    rw [hid, ContinuousLinearMap.id_apply]
    exact mfd_val_tangentCoord hM q.2.snd

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ W] [FiniteDimensional ℝ W']
  [FiniteDimensional ℝ E''] [FiniteDimensional ℝ W''] in
/-- **Problem 10.** The chain rule `d(g ∘ f) = (dg) ∘ (df)`. -/
theorem tangentMap_comp {f : M → N} {g : N → P}
    (hf : letI := hM.chartedSpace; letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, Z') ∞ f)
    (hg : letI := hN.chartedSpace; letI := hP.chartedSpace; ContMDiff 𝓘(ℝ, Z') 𝓘(ℝ, Z'') ∞ g) :
    tangentMap hM hP (g ∘ f) = tangentMap hN hP g ∘ tangentMap hM hN f := by
  let _ := hM.chartedSpace
  let _ := hN.chartedSpace
  let _ := hP.chartedSpace
  funext q
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · obtain ⟨x, hx⟩ : ∃ x : M, x = ⟨q.1.1, q.2.fst⟩ := ⟨_, rfl⟩
    show mfd 𝓘(ℝ, Z'') 𝓘(ℝ, E'') (Subtype.val : P → E'') (g (f ⟨q.1.1, q.2.fst⟩))
        (mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z'') (g ∘ f) ⟨q.1.1, q.2.fst⟩
          (tangentCoord hM ⟨q.1.1, q.2.fst⟩ q.1.2)) =
      mfd 𝓘(ℝ, Z'') 𝓘(ℝ, E'') (Subtype.val : P → E'') (g (f ⟨q.1.1, q.2.fst⟩))
        (mfd 𝓘(ℝ, Z') 𝓘(ℝ, Z'') g (f ⟨q.1.1, q.2.fst⟩)
          (tangentCoord hN (f ⟨q.1.1, q.2.fst⟩)
            (mfd 𝓘(ℝ, Z') 𝓘(ℝ, E') (Subtype.val : N → E') (f ⟨q.1.1, q.2.fst⟩)
              (mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z') f ⟨q.1.1, q.2.fst⟩
                (tangentCoord hM ⟨q.1.1, q.2.fst⟩ q.1.2)))))
    rw [← hx, tangentCoord_mfd_val hN]
    have hfx : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, Z') f x := hf.mdifferentiableAt (by simp)
    have hgx : MDifferentiableAt 𝓘(ℝ, Z') 𝓘(ℝ, Z'') g (f x) := hg.mdifferentiableAt (by simp)
    have hchain : mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z'') (g ∘ f) x =
        (mfd 𝓘(ℝ, Z') 𝓘(ℝ, Z'') g (f x)).comp (mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z') f x) :=
      HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd hgx).comp x (hasMFDerivAt_mfd hfx))
    rw [hchain]
    rfl

end Problems

end Milnor
