import Morse.Chapter1.Manifold
import Milnor.Chapter2.Submanifold
import Milnor.Chapter6.ChartIndex

/-!
Milnor, *Morse Theory*, §2 (pp. 4–5) for submanifolds of Euclidean space, as used in §6 (pp. 32–36)
and in Application 2 of §6 (p. 36).

# Critical points of a function restricted to a submanifold of `ℝᴷ`

Milnor's §6 studies functions `f = F|N` on a manifold `N` embedded in Euclidean space (his `ℝⁿ`,
with `N` of dimension `k`), mainly `L_p(x) = ‖x − p‖²`, by computing in coordinates
`(u¹, …, uᵏ)` on a region of `N`: the inclusion becomes a parametrization `u ↦ x(u)`, and

* (p. 35) `∂f/∂uⁱ = 2 (∂x/∂uⁱ) · (x − p)`, so *`f` has a critical point at `q` iff `q − p` is normal
  to `N` at `q`*;
* (p. 36) at a critical point, `∂²f/∂uⁱ∂uʲ = 2 ((∂x/∂uⁱ) · (∂x/∂uʲ) + (∂²x/∂uⁱ∂uʲ) · (x − p))`, and
  the index and nullity of `f` at `q` are those of this matrix.

This file supplies the bridge between such computations and the manifold-level notions of
`Morse/Chapter1/Manifold.lean`, for the submanifolds of the companion project.

## Setting

`V` is a real normed space (Milnor's `ℝⁿ`; an inner product space from the section on gradients
on),
and `N ⊆ V` is a `Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N`: around each of its points there is a
diffeomorphism `σ.φ` of open subsets of `V` and `Z × W` under which `N` corresponds to `Z × {0}`.
The companion project makes `N` a smooth manifold modelled on `Z` (`hN.chartedSpace`,
`hN.isManifold`), whose charts are the maps `σ.toChart : q ↦ (σ.φ q).1`.  Statements about `N` are
written `letI := hN.chartedSpace; …`, as in the companion project.

* `Morse.sliceParam σ : Z → V`, `z ↦ σ.φ⁻¹(z, 0)`: Milnor's local parametrization `u ↦ x(u)`, the
  inverse of the chart `σ.toChart`, defined on the open set `σ.toChart.target` (for the slice chart
  chosen at `q` by the companion project this is `Milnor.Tub.φ hN q`).
* `Morse.tangentSubspace hN q`: the tangent space `T_qN ⊆ V`, the range of the derivative of the
  inclusion (the companion project's `Milnor.Tub.tanN` in the Euclidean case,
  `Morse.tangentSubspace_eq_tanN`); it is the range of `d(sliceParam σ)` at `(σ.φ q).1`
  (`Morse.tangentSubspace_eq_range_fderiv_sliceParam`).

## Main results

For `F : V → ℝ` and `q ∈ N` in the domain of a slice chart `σ`:

* `Morse.isCriticalPointM_comp_val_iff_sliceParam`: `q` is a critical point of `F|N` iff
  `(σ.φ q).1` is a critical point of `F ∘ sliceParam σ`;
* `Morse.hessian_comp_sliceParam`, `Morse.isNondegenerate_hessian_comp_sliceParam_iff`,
  `Morse.index_hessian_comp_sliceParam`, `Morse.nullity_hessian_comp_sliceParam`,
  `Morse.isNondegenerateCriticalPointM_comp_val_iff_sliceParam`: at a critical point, the Hessian,
  non-degeneracy, index and nullity of `F|N` are computed by `F ∘ sliceParam σ`;
* `Morse.isCriticalPointM_comp_val_iff_forall_tangent`: `q` is critical for `F|N` iff `dF_q`
  vanishes on `T_qN`; `Morse.isCriticalPointM_comp_val_iff_gradient_mem_orthogonal`: iff the
  ambient gradient `∇F(q)` is orthogonal to `T_qN`;
  `Morse.isCriticalPointM_comp_val_iff_starProjection_gradient_eq_zero`: iff the tangential part
  of `∇F(q)` vanishes;
* `Morse.isCriticalPointM_normSq_sub_iff` (Milnor, p. 35): `q` is a critical point of
  `L_p = ‖· − p‖²` on `N` iff `q − p ⊥ T_qN`;
* `Morse.hessian_normSq_sub_comp` (Milnor, p. 36): the Hessian of `u ↦ ‖x(u) − p‖²` is
  `2 (⟪∂x/∂v, ∂x/∂w⟫ + ⟪∂²x/∂v∂w, x − p⟫)`; `Morse.indexM_normSq_sub_eq`,
  `Morse.nullityM_normSq_sub_eq`, `Morse.isNondegenerate_hessianM_normSq_sub_iff`: the index,
  nullity and non-degeneracy of `L_p` at a critical point are those of this form;
* in the notation of the companion project's tubular neighbourhood files (`Milnor.Tub.φ`,
  `Milnor.Tub.z₀`, `Milnor.Tub.tanN`), used by its Poincaré–Hopf theorem:
  `Morse.sliceParam_tub`, `Morse.tangentSubspace_eq_tanN`, `Morse.indexM_comp_val_eq_tub`,
  `Morse.isNondegenerateCriticalPointM_comp_val_iff_tub`.

## What Milnor leaves implicit

* That critical points, non-degeneracy and the index of `f = F|N` may be computed in *any* local
  parametrization of `N` (he works in one fixed local coordinate system).  This is the chart
  independence of `Morse/Chapter1/Manifold.lean`, applied to the slice charts, which belong to the
  atlas of `N`.
* The Hessian of `F ∘ x` is *not* the restriction of the ambient Hessian of `F`: the second-order
  chain rule (`Morse.hessian_comp_apply`) has the extra term `dF(∂²x/∂uⁱ∂uʲ)`, which does not vanish
  at a critical point of `F|N` (only the tangential part of `dF` does).  For `L_p` this is the
  second fundamental form term of Milnor's formula.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

/-! ### The parametrization of a slice chart -/

section Param

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V}

/-- **The local parametrization of `N` given by a slice chart** `σ`: `z ↦ σ.φ⁻¹(z, 0)`, Milnor's
`u ↦ x(u)`.  It is meaningful on the open set `σ.toChart.target = {z | (z, 0) ∈ σ.φ.target}`,
where it is the inverse of the chart `σ.toChart` of `N`. -/
def sliceParam (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) (z : Z) : V :=
  σ.φ.invFun (z, 0)

variable (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N)

theorem isOpen_toChart_target : IsOpen σ.toChart.target :=
  σ.toChart.open_target

theorem sliceParam_mem {z : Z} (hz : z ∈ σ.toChart.target) : sliceParam σ z ∈ N :=
  σ.symm_mem z hz

theorem val_toChart_symm {z : Z} (hz : z ∈ σ.toChart.target) :
    ((σ.toChart.symm z : N) : V) = sliceParam σ z :=
  σ.toChart_symm_apply hz

theorem toChart_apply_mem_target {q : N} (hq : q.1 ∈ σ.φ.source) :
    σ.toChart q ∈ σ.toChart.target :=
  σ.toChart.map_source hq

/-- The parametrization inverts the chart: `x((σ.φ q).1) = q` for `q ∈ N` in the chart domain. -/
theorem sliceParam_toChart {q : N} (hq : q.1 ∈ σ.φ.source) : sliceParam σ (σ.toChart q) = q := by
  rw [← val_toChart_symm σ (toChart_apply_mem_target σ hq), σ.toChart.left_inv hq]

/-- The parametrization is smooth on its domain. -/
theorem contDiffOn_sliceParam : ContDiffOn ℝ ∞ (sliceParam σ) σ.toChart.target := by
  have h1 : ContMDiffOn 𝓘(ℝ, Z × W) 𝓘(ℝ, V) ∞ σ.φ.invFun σ.φ.target := σ.φ.contMDiffOn_invFun
  have h2 : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, Z × W) ∞ (fun z : Z => (z, (0 : W))) :=
    contMDiff_iff_contDiff.2 (contDiff_id.prodMk contDiff_const)
  rw [← contMDiffOn_iff_contDiffOn]
  exact h1.comp h2.contMDiffOn fun z hz => hz

theorem contDiffAt_sliceParam {z : Z} (hz : z ∈ σ.toChart.target) :
    ContDiffAt ℝ ∞ (sliceParam σ) z :=
  (contDiffOn_sliceParam σ).contDiffAt ((isOpen_toChart_target σ).mem_nhds hz)

/-- Near a point of its domain, a function on `N` read in the chart `σ.toChart` is the ambient
function composed with the parametrization. -/
theorem comp_val_comp_toChart_symm_eventuallyEq (F : V → ℝ) {z : Z}
    (hz : z ∈ σ.toChart.target) :
    (F ∘ Subtype.val) ∘ σ.toChart.symm =ᶠ[𝓝 z] F ∘ sliceParam σ := by
  filter_upwards [(isOpen_toChart_target σ).mem_nhds hz] with z' hz'
  simp only [comp_apply]
  rw [val_toChart_symm σ hz']

end Param

/-! ### Slice charts are smooth coordinate systems of `N` -/

section Chart

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-- The chart induced by a slice chart belongs to the maximal atlas of `N`. -/
theorem toChart_mem_maximalAtlas (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) :
    letI := hN.chartedSpace
    σ.toChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, Z) ∞ N := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  exact IsManifold.subset_maximalAtlas ((hN.mem_atlas_iff _).2 ⟨σ, rfl⟩)

/-- The chart induced by a slice chart is a smooth coordinate system of `N`. -/
theorem isSmoothCoord_toChart (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) :
    letI := hN.chartedSpace
    IsSmoothCoord Z σ.toChart := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  exact isSmoothCoord_of_mem_maximalAtlas (toChart_mem_maximalAtlas hN σ)

/-- An ambient `Cⁿ` function restricts to a `Cⁿ` function on `N`. -/
theorem contMDiffAt_comp_val {F : V → ℝ} {q : N} {n : WithTop ℕ∞} (hn : n ≤ ∞)
    (hF : ContDiffAt ℝ n F q) :
    letI := hN.chartedSpace
    ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) n (F ∘ Subtype.val) q := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  exact hF.contMDiffAt.comp q ((hN.contMDiff_val q).of_le hn)

/-- An ambient smooth function restricts to a smooth function on `N`. -/
theorem contMDiff_comp_val {F : V → ℝ} (hF : ContDiff ℝ ∞ F) :
    letI := hN.chartedSpace
    ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ (F ∘ (Subtype.val : N → V)) := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  exact hF.contMDiff.comp hN.contMDiff_val

theorem mdifferentiableAt_comp_val {F : V → ℝ} {q : N} (hF : DifferentiableAt ℝ F q) :
    letI := hN.chartedSpace
    MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) (F ∘ Subtype.val) q := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  exact hF.mdifferentiableAt.comp q ((hN.contMDiff_val q).mdifferentiableAt (by simp))

/-! ### Critical points, Hessian, index of `F|N` in a slice parametrization -/

variable (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) {F : V → ℝ} {q : N}

/-- **Critical points of `F|N` in a parametrization**: `q` is a critical point of `F|N` iff
`(σ.φ q).1` is a critical point of `F ∘ x`, `x = sliceParam σ`. -/
theorem isCriticalPointM_comp_val_iff_sliceParam (hq : q.1 ∈ σ.φ.source)
    (hF : DifferentiableAt ℝ F q) :
    letI := hN.chartedSpace
    IsCriticalPointM Z (F ∘ Subtype.val) q ↔ IsCriticalPoint (F ∘ sliceParam σ) (σ.φ q).1 := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have hev := comp_val_comp_toChart_symm_eventuallyEq σ F (toChart_apply_mem_target σ hq)
  rw [(isSmoothCoord_toChart hN σ).isCriticalPointM_iff hq (mdifferentiableAt_comp_val hN hF)]
  exact ⟨fun h => h.congr_of_eventuallyEq hev.symm, fun h => h.congr_of_eventuallyEq hev⟩

/-- **The Hessian of `F|N` in a parametrization**: at a critical point `q` of `F|N`, the Hessian of
`F ∘ x` at `(σ.φ q).1` is `f_**` pulled back by the derivative of the parametrization. -/
theorem hessian_comp_sliceParam (hq : q.1 ∈ σ.φ.source) (hF : ContDiffAt ℝ 2 F q)
    (hcrit : letI := hN.chartedSpace; IsCriticalPointM Z (F ∘ Subtype.val) q) (v w : Z) :
    letI := hN.chartedSpace
    hessian (F ∘ sliceParam σ) (σ.φ q).1 v w =
      hessianM Z (F ∘ Subtype.val) q (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, Z) σ.toChart.symm (σ.toChart q) v)
        (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, Z) σ.toChart.symm (σ.toChart q) w) := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have hev := comp_val_comp_toChart_symm_eventuallyEq σ F (toChart_apply_mem_target σ hq)
  have hF' := contMDiffAt_comp_val hN (by norm_cast) hF
  rw [← (isSmoothCoord_toChart hN σ).hessian_comp_symm hq hF' hcrit,
    hessian_congr hev]
  rfl

/-- **Non-degeneracy of a critical point of `F|N` in a parametrization.** -/
theorem isNondegenerate_hessian_comp_sliceParam_iff (hq : q.1 ∈ σ.φ.source)
    (hF : ContDiffAt ℝ 2 F q)
    (hcrit : letI := hN.chartedSpace; IsCriticalPointM Z (F ∘ Subtype.val) q) :
    letI := hN.chartedSpace
    IsNondegenerate (hessian (F ∘ sliceParam σ) (σ.φ q).1) ↔
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q) := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have hev := comp_val_comp_toChart_symm_eventuallyEq σ F (toChart_apply_mem_target σ hq)
  have hF' := contMDiffAt_comp_val hN (by norm_cast) hF
  rw [← (isSmoothCoord_toChart hN σ).isNondegenerate_iff hq hF' hcrit,
    hessian_congr hev]
  rfl

/-- **The index of a critical point of `F|N` in a parametrization.** -/
theorem index_hessian_comp_sliceParam (hq : q.1 ∈ σ.φ.source) (hF : ContDiffAt ℝ 2 F q)
    (hcrit : letI := hN.chartedSpace; IsCriticalPointM Z (F ∘ Subtype.val) q) :
    letI := hN.chartedSpace
    index (hessian (F ∘ sliceParam σ) (σ.φ q).1) = indexM Z (F ∘ Subtype.val) q := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have hev := comp_val_comp_toChart_symm_eventuallyEq σ F (toChart_apply_mem_target σ hq)
  have hF' := contMDiffAt_comp_val hN (by norm_cast) hF
  rw [← (isSmoothCoord_toChart hN σ).index_eq hq hF' hcrit,
    hessian_congr hev]
  rfl

/-- **The nullity of a critical point of `F|N` in a parametrization.** -/
theorem nullity_hessian_comp_sliceParam (hq : q.1 ∈ σ.φ.source) (hF : ContDiffAt ℝ 2 F q)
    (hcrit : letI := hN.chartedSpace; IsCriticalPointM Z (F ∘ Subtype.val) q) :
    letI := hN.chartedSpace
    nullity (hessian (F ∘ sliceParam σ) (σ.φ q).1) = nullityM Z (F ∘ Subtype.val) q := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have hev := comp_val_comp_toChart_symm_eventuallyEq σ F (toChart_apply_mem_target σ hq)
  have hF' := contMDiffAt_comp_val hN (by norm_cast) hF
  rw [← (isSmoothCoord_toChart hN σ).nullity_eq hq hF' hcrit,
    hessian_congr hev]
  rfl

/-- **Non-degenerate critical points of `F|N` in a parametrization.** -/
theorem isNondegenerateCriticalPointM_comp_val_iff_sliceParam (hq : q.1 ∈ σ.φ.source)
    (hF : ContDiffAt ℝ 2 F q) :
    letI := hN.chartedSpace
    IsNondegenerateCriticalPointM Z (F ∘ Subtype.val) q ↔
      IsNondegenerateCriticalPoint (F ∘ sliceParam σ) (σ.φ q).1 := by
  let _ := hN.chartedSpace
  have hcrit := isCriticalPointM_comp_val_iff_sliceParam hN σ hq (hF.differentiableAt (by simp))
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hcrit.1 h1, (isNondegenerate_hessian_comp_sliceParam_iff hN σ hq hF h1).2 h2⟩
  · rintro ⟨h1, h2⟩
    have h1' := hcrit.2 h1
    exact ⟨h1', (isNondegenerate_hessian_comp_sliceParam_iff hN σ hq hF h1').1 h2⟩

end Chart

/-! ### The tangent space, and critical points via the ambient derivative -/

section Tangent

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-- **The tangent space `T_qN` as a linear subspace of the ambient space** `V`: the range of the
derivative of the inclusion `N → V` at `q`. -/
def tangentSubspace (q : N) : Submodule ℝ V :=
  letI := hN.chartedSpace
  LinearMap.range ((Milnor.mfd 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : N → V) q : Z →L[ℝ] V) :
    Z →ₗ[ℝ] V)

theorem mem_tangentSubspace_iff {q : N} {v : V} :
    letI := hN.chartedSpace
    v ∈ tangentSubspace hN q ↔ ∃ z : Z, mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : N → V) q z = v :=
  Iff.rfl

/-- **The tangent space is spanned by the partial derivatives of a parametrization**:
`T_qN` is the range of `d(sliceParam σ)` at `(σ.φ q).1`, for any slice chart `σ` around `q`. -/
theorem tangentSubspace_eq_range_fderiv_sliceParam (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N)
    {q : N} (hq : q.1 ∈ σ.φ.source) :
    tangentSubspace hN q =
      LinearMap.range ((fderiv ℝ (sliceParam σ) (σ.φ q).1 : Z →L[ℝ] V) : Z →ₗ[ℝ] V) := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have hy := isSmoothCoord_toChart hN σ
  have hz := toChart_apply_mem_target σ hq
  -- `val = x ∘ σ.toChart` near `q`
  have hev : (Subtype.val : N → V) =ᶠ[𝓝 q] sliceParam σ ∘ σ.toChart := by
    filter_upwards [σ.toChart.open_source.mem_nhds hq] with q' hq'
    exact (sliceParam_toChart σ hq').symm
  have hx : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) (sliceParam σ) (σ.toChart q) :=
    ((contDiffAt_sliceParam σ hz).differentiableAt (by simp)).mdifferentiableAt
  have hcomp := mfderiv_comp q hx (hy.mdifferentiableAt hq)
  rw [← hev.mfderiv_eq, mfderiv_eq_fderiv] at hcomp
  obtain ⟨L, hL⟩ := hy.exists_mfderiv_eq hq
  rw [hL] at hcomp
  have hmfd : Milnor.mfd 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : N → V) q =
      (fderiv ℝ (sliceParam σ) (σ.φ q).1).comp (L : Z →L[ℝ] Z) := hcomp
  have hsurj : LinearMap.range ((L : Z →L[ℝ] Z) : Z →ₗ[ℝ] Z) = ⊤ :=
    LinearMap.range_eq_top.2 L.surjective
  rw [tangentSubspace, hmfd]
  exact LinearMap.range_comp_of_range_eq_top _ hsurj

/-- **`q` is a critical point of `F|N` iff `dF_q` vanishes on the tangent space `T_qN`.** -/
theorem isCriticalPointM_comp_val_iff_forall_tangent {F : V → ℝ} {q : N}
    (hF : DifferentiableAt ℝ F q) :
    letI := hN.chartedSpace
    IsCriticalPointM Z (F ∘ Subtype.val) q ↔ ∀ v ∈ tangentSubspace hN q, fderiv ℝ F q v = 0 := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have hval : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : N → V) q :=
    (hN.contMDiff_val q).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp q (I' := 𝓘(ℝ, V)) hF.mdifferentiableAt hval
  rw [mfderiv_eq_fderiv] at hcomp
  rw [IsCriticalPointM, hcomp]
  constructor
  · rintro h v ⟨z, rfl⟩
    have := congrArg (fun T : Z →L[ℝ] ℝ => T z) h
    exact this
  · intro h
    ext z
    exact h _ ⟨z, rfl⟩

end Tangent

/-! ### Gradients; the distance-squared function `L_p` -/

section Gradient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-- **`q` is a critical point of `F|N` iff the ambient gradient `∇F(q)` is normal to `N` at `q`**
(Milnor uses this on p. 35). -/
theorem isCriticalPointM_comp_val_iff_gradient_mem_orthogonal [CompleteSpace V] {F : V → ℝ}
    {q : N} (hF : DifferentiableAt ℝ F q) :
    letI := hN.chartedSpace
    IsCriticalPointM Z (F ∘ Subtype.val) q ↔ gradient F q ∈ (tangentSubspace hN q)ᗮ := by
  rw [isCriticalPointM_comp_val_iff_forall_tangent hN hF, Submodule.mem_orthogonal]
  refine forall₂_congr fun v _ => ?_
  rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply]

/-- **The tangential gradient vanishes exactly at the critical points**: `q` is a critical point
of `F|N` iff the orthogonal projection of `∇F(q)` on `T_qN` is zero (Milnor, §6, Application 2,
p. 36: the zeros of the vector field `grad f` are the critical points of `f`). -/
theorem isCriticalPointM_comp_val_iff_starProjection_gradient_eq_zero [FiniteDimensional ℝ V]
    {F : V → ℝ} {q : N} (hF : DifferentiableAt ℝ F q) :
    letI := hN.chartedSpace
    IsCriticalPointM Z (F ∘ Subtype.val) q ↔
      (tangentSubspace hN q).starProjection (gradient F q) = 0 := by
  rw [isCriticalPointM_comp_val_iff_gradient_mem_orthogonal hN hF,
    Submodule.starProjection_apply_eq_zero_iff]

/-- The derivative of `x ↦ ‖x − p‖²` is `v ↦ 2 ⟪x − p, v⟫`. -/
theorem hasFDerivAt_normSq_sub (p x : V) :
    HasFDerivAt (fun y : V => ‖y - p‖ ^ 2) ((2 : ℝ) • innerSL ℝ (x - p)) x := by
  have h := ((hasFDerivAt_id x).sub_const p).norm_sq
  refine h.congr_fderiv ?_
  ext v
  change (2 : ℕ) • ((innerSL ℝ (x - p)) v) = (2 : ℝ) • ((innerSL ℝ (x - p)) v)
  rw [two_nsmul, two_smul]

theorem fderiv_normSq_sub_apply (p x v : V) :
    fderiv ℝ (fun y : V => ‖y - p‖ ^ 2) x v = 2 * ⟪x - p, v⟫ := by
  rw [(hasFDerivAt_normSq_sub p x).fderiv]
  rfl

/-- The Hessian of `x ↦ ‖x − p‖²` is `2 ⟪·, ·⟫` at every point. -/
theorem hessian_normSq_sub (p x : V) :
    hessian (fun y : V => ‖y - p‖ ^ 2) x = (2 : ℝ) • innerSL ℝ := by
  have h1 : fderiv ℝ (fun y : V => ‖y - p‖ ^ 2) = fun y => (2 : ℝ) • innerSL ℝ (y - p) :=
    funext fun y => (hasFDerivAt_normSq_sub p y).fderiv
  have hfun : (fun y : V => (2 : ℝ) • innerSL ℝ (y - p)) =
      fun y => ((2 : ℝ) • innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ) y -
        ((2 : ℝ) • innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ) p := by
    funext y
    rw [← map_sub]
    rfl
  have h2 : HasFDerivAt (fun y : V => (2 : ℝ) • innerSL ℝ (y - p)) ((2 : ℝ) • innerSL ℝ) x := by
    rw [hfun]
    exact (((2 : ℝ) • innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).hasFDerivAt (x := x)).sub_const _
  rw [hessian, h1, h2.fderiv]

theorem hessian_normSq_sub_apply (p x v w : V) :
    hessian (fun y : V => ‖y - p‖ ^ 2) x v w = 2 * ⟪v, w⟫ := by
  rw [hessian_normSq_sub]
  rfl

theorem contDiff_normSq_sub (p : V) : ContDiff ℝ ∞ (fun y : V => ‖y - p‖ ^ 2) :=
  (contDiff_id.sub contDiff_const).norm_sq ℝ

/-- **Milnor, p. 35**: *`L_p` has a critical point at `q` iff `q − p` is normal to `N` at `q`*,
for `L_p(x) = ‖x − p‖²` restricted to `N`. -/
theorem isCriticalPointM_normSq_sub_iff (p : V) (q : N) :
    letI := hN.chartedSpace
    IsCriticalPointM Z (fun x : N => ‖(x : V) - p‖ ^ 2) q ↔
      (q : V) - p ∈ (tangentSubspace hN q)ᗮ := by
  have h := isCriticalPointM_comp_val_iff_forall_tangent hN
    (hasFDerivAt_normSq_sub p (q : V)).differentiableAt
  rw [Submodule.mem_orthogonal]
  refine h.trans (forall₂_congr fun v _ => ?_)
  rw [fderiv_normSq_sub_apply, real_inner_comm]
  constructor
  · intro h0
    linarith
  · intro h0
    rw [h0, mul_zero]

/-- **Milnor, p. 36**: *the second partial derivatives of `L_p` in a parametrization* `x`:
`∂²‖x − p‖²/∂v∂w = 2 (⟪∂x/∂v, ∂x/∂w⟫ + ⟪∂²x/∂v∂w, x − p⟫)`.  (Milnor states it at a critical
point; it holds everywhere.) -/
theorem hessian_normSq_sub_comp {x : Z → V} {u : Z} (hx : ContDiffAt ℝ 2 x u) (p : V) (v w : Z) :
    hessian (fun z => ‖x z - p‖ ^ 2) u v w =
      2 * (⟪fderiv ℝ x u v, fderiv ℝ x u w⟫ + ⟪fderiv ℝ (fderiv ℝ x) u v w, x u - p⟫) := by
  have h := hessian_comp_apply (f := fun y : V => ‖y - p‖ ^ 2)
    ((contDiff_normSq_sub p).contDiffAt.of_le (by norm_cast)) hx v w
  have hc : ((fun y : V => ‖y - p‖ ^ 2) ∘ x) = fun z => ‖x z - p‖ ^ 2 := rfl
  rw [hc] at h
  rw [h, hessian_normSq_sub_apply, fderiv_normSq_sub_apply,
    real_inner_comm (x u - p) (fderiv ℝ (fderiv ℝ x) u v w)]
  ring

/-- **The index of `L_p` at a critical point, in a parametrization** (Milnor, p. 36): it is the
index of the bilinear form `(v, w) ↦ 2 (⟪∂x/∂v, ∂x/∂w⟫ + ⟪∂²x/∂v∂w, x − p⟫)` at `u = (σ.φ q).1`,
`x = sliceParam σ`. -/
theorem indexM_normSq_sub_eq (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) (p : V) {q : N}
    (hq : q.1 ∈ σ.φ.source)
    (hcrit : letI := hN.chartedSpace; IsCriticalPointM Z (fun x : N => ‖(x : V) - p‖ ^ 2) q) :
    letI := hN.chartedSpace
    indexM Z (fun x : N => ‖(x : V) - p‖ ^ 2) q =
      index (hessian (fun z => ‖sliceParam σ z - p‖ ^ 2) (σ.φ q).1) :=
  (index_hessian_comp_sliceParam hN σ hq ((contDiff_normSq_sub p).contDiffAt.of_le
    (by norm_cast)) hcrit).symm

/-- **The nullity of `L_p` at a critical point, in a parametrization** (Milnor, p. 36, Lemma 6.5:
the nullity of `q` as a critical point is computed by the matrix
`2 (⟪∂x/∂uⁱ, ∂x/∂uʲ⟫ + ⟪∂²x/∂uⁱ∂uʲ, x − p⟫)`). -/
theorem nullityM_normSq_sub_eq (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) (p : V) {q : N}
    (hq : q.1 ∈ σ.φ.source)
    (hcrit : letI := hN.chartedSpace; IsCriticalPointM Z (fun x : N => ‖(x : V) - p‖ ^ 2) q) :
    letI := hN.chartedSpace
    nullityM Z (fun x : N => ‖(x : V) - p‖ ^ 2) q =
      nullity (hessian (fun z => ‖sliceParam σ z - p‖ ^ 2) (σ.φ q).1) :=
  (nullity_hessian_comp_sliceParam hN σ hq ((contDiff_normSq_sub p).contDiffAt.of_le
    (by norm_cast)) hcrit).symm

/-- Non-degeneracy of a critical point of `L_p`, in a parametrization. -/
theorem isNondegenerate_hessianM_normSq_sub_iff (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) (p : V)
    {q : N} (hq : q.1 ∈ σ.φ.source)
    (hcrit : letI := hN.chartedSpace; IsCriticalPointM Z (fun x : N => ‖(x : V) - p‖ ^ 2) q) :
    letI := hN.chartedSpace
    IsNondegenerate (hessianM Z (fun x : N => ‖(x : V) - p‖ ^ 2) q) ↔
      IsNondegenerate (hessian (fun z => ‖sliceParam σ z - p‖ ^ 2) (σ.φ q).1) :=
  (isNondegenerate_hessian_comp_sliceParam_iff hN σ hq ((contDiff_normSq_sub p).contDiffAt.of_le
    (by norm_cast)) hcrit).symm

end Gradient

/-! ### In the notation of the companion project's tubular neighbourhood files

`Milnor.Tub` (used for the Poincaré–Hopf theorem, `Milnor.Tub.poincare_hopf`, and the chart index,
`Milnor.Tub.chartIndexN`) works with `N ⊆ ℝᴷ⁺¹`, its preferred slice chart `Milnor.Tub.σ hN q` at
`q`, the parametrization `Milnor.Tub.φ hN q` and the point `Milnor.Tub.z₀ hN q` over `q`.  These
are `Morse.sliceParam` and `(σ.φ q).1` for that slice chart. -/

section Tub

variable {K d m : ℕ} {N : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
    (EuclideanSpace ℝ (Fin (d + 1))) (EuclideanSpace ℝ (Fin m)) N)

theorem sliceParam_tub (q : N) : sliceParam (Milnor.Tub.σ hN q) = Milnor.Tub.φ hN q := rfl

theorem tangentSubspace_eq_tanN (q : N) : tangentSubspace hN q = Milnor.Tub.tanN hN q := rfl

/-- The index of `F|N` at a critical point `q`, computed in the parametrization `Milnor.Tub.φ hN q`
of the companion project. -/
theorem indexM_comp_val_eq_tub {F : EuclideanSpace ℝ (Fin (K + 1)) → ℝ} {q : N}
    (hF : ContDiffAt ℝ 2 F q)
    (hcrit : letI := hN.chartedSpace;
      IsCriticalPointM (EuclideanSpace ℝ (Fin (d + 1))) (F ∘ Subtype.val) q) :
    letI := hN.chartedSpace
    indexM (EuclideanSpace ℝ (Fin (d + 1))) (F ∘ Subtype.val) q =
      index (hessian (F ∘ Milnor.Tub.φ hN q) (Milnor.Tub.z₀ hN q)) :=
  (index_hessian_comp_sliceParam hN (Milnor.Tub.σ hN q) (Milnor.Tub.mem_source hN q) hF
    hcrit).symm

/-- Non-degenerate critical points of `F|N`, in the parametrization `Milnor.Tub.φ hN q`. -/
theorem isNondegenerateCriticalPointM_comp_val_iff_tub {F : EuclideanSpace ℝ (Fin (K + 1)) → ℝ}
    {q : N} (hF : ContDiffAt ℝ 2 F q) :
    letI := hN.chartedSpace
    IsNondegenerateCriticalPointM (EuclideanSpace ℝ (Fin (d + 1))) (F ∘ Subtype.val) q ↔
      IsNondegenerateCriticalPoint (F ∘ Milnor.Tub.φ hN q) (Milnor.Tub.z₀ hN q) :=
  isNondegenerateCriticalPointM_comp_val_iff_sliceParam hN (Milnor.Tub.σ hN q)
    (Milnor.Tub.mem_source hN q) hF

end Tub

end Morse
