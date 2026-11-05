import Morse.Chapter1.ManifoldSubmanifold
import Milnor.Chapter8.NormalBundle

/-!
Milnor, *Morse Theory*, §6, pp. 32–35.

# The normal bundle and the derivative of the endpoint map

## Setting

`M ⊆ ℝⁿ` (`ℝⁿ = EuclideanSpace ℝ (Fin n)`) is a slice submanifold of dimension `k`,
`Milnor.IsSliceSubmanifold 𝓘(ℝ, ℝⁿ) ℝᵏ ℝʷ M`; when `M` is nonempty, `k + w = n`
(`Morse.slice_dim_add_eq_of_nonempty`, `Morse/Chapter4/Focal.lean`).  This is Milnor's manifold of
dimension `k < n` "differentiably embedded" in `ℝⁿ` (p. 32); `M` need not be closed or compact,
and `k = n` is allowed.  Milnor's objects and their formal counterparts:

* the **normal bundle** `N = {(q, v) ∈ M × ℝⁿ | v ⊥ T_qM}` (p. 32) is the companion project's
  `Milnor.Problems.normalBundleSet hM`, a slice submanifold of `ℝⁿ × ℝⁿ` of dimension `n`
  (`Milnor.Problems.isSliceSubmanifold_normalBundle`; Milnor: "not difficult to show").
  `Morse.mem_normalBundleSet_iff` restates membership with the tangent space `T_qM =
  Morse.tangentSubspace hM q` of `Morse/Chapter1/ManifoldSubmanifold.lean`;
* the **endpoint map** `E(q, v) = q + v` (p. 32) is `Milnor.Problems.normalSum hM`.  We also use
  the generalized endpoint map `Morse.normalEnd hM Γ : (q, v) ↦ Γ(q) + v` for a map
  `Γ : ℝⁿ → ℝⁿ`; `Γ = id` gives `E` (`Morse.normalEnd_id`), and `Γ = −∇F` serves for
  Corollary 6.8 (`Morse/Chapter4/Approximation.lean`);
* Milnor's **coordinates** `u ↦ x(u)` on a region of `M` (p. 33) are `Morse.xParam hM q`, the
  inverse of the slice chart chosen at `q`, with `x(u_q) = q` for `u_q = Morse.uParam hM q`;
  `Morse.dParam hM q` and `Morse.d2Param hM q` are its first and second derivatives at `u_q`
  (Milnor's vectors `∂x/∂uⁱ` and `∂²x/∂uⁱ∂uʲ` at `q`);
* the **first fundamental form** `(g_ij)` and the **second fundamental form in the direction `v`**,
  `(v · ℓ_ij)` (pp. 33–34), are the bilinear forms `Morse.firstFF hM q` and
  `Morse.secondFF hM q v` on `ℝᵏ`.

## Main results

* `Morse.mem_range_mfd_val_normalBundle_iff`, **the tangent space of `N` at `(q, v)`**: a pair
  `(a, b) ∈ ℝⁿ × ℝⁿ` is tangent to `N` iff `a = dx(ξ)` for some `ξ ∈ ℝᵏ` and
  `⟪b, ∂x/∂η⟫ + ⟪v, ∂²x/∂ξ∂η⟫ = 0` for every `η ∈ ℝᵏ`.
* `Morse.finrank_ker_mfd_normalEnd`, **the kernel of the derivative of `(q, v) ↦ Γ(q) + v`**: at
  `(q, v) ∈ N` its dimension is the nullity of the bilinear form
  `(ξ, η) ↦ ⟪dΓ_q(∂x/∂ξ), ∂x/∂η⟫ − ⟪v, ∂²x/∂ξ∂η⟫` on `ℝᵏ` (`Morse.normalForm`).  For `Γ = id`
  this is Milnor's computation of pp. 34–35: the nullity of the Jacobian of `E` at `(q, v)` is the
  nullity of the matrix `(g_ij − v · ℓ_ij)`.

## Milnor's argument, and the one formalized

Milnor (p. 34) chooses `n − k` vector fields `w_α(u)`, orthonormal and normal to `M`, takes
`(u, t) ↦ (x(u), Σ t^α w_α(u))` as coordinates on `N`, computes the partial derivatives of `E` in
them, takes inner products with the basis `∂x/∂uⁱ, w_β` of `ℝⁿ` to obtain a block triangular
`n × n` matrix, and identifies the upper left block with `(g_ij − Σ t^α w_α · ℓ_ij)` by
differentiating `w_α · ∂x/∂uʲ = 0`.

The formalization uses no normal frame.  The companion project builds the manifold structure of
`N` from the local defining function `(a, b) ↦ ((σ a)₂, (dx_{c(a)})† b)` (`σ` the slice chart of
`M` at `q`, `c(a) = (σ a)₁`), so the tangent space of `N` is the kernel of its derivative
(`Milnor.IsSliceSubmanifold.range_mfderiv_val_eq_ker`).  Computing that derivative
(`Morse.hasFDerivAt_B`) gives the description of `T_{(q,v)}N` above; its second condition is the
derivative of Milnor's identity `w_α · ∂x/∂uʲ = 0`.  The kernel of `dE` on `T_{(q,v)}N` is then
`{(dx(ξ), −dx(ξ)) | ξ in the null space of g − v · ℓ}`, and similarly for `Γ`.

## Gaps in Milnor's text

* **Normal frames exist only locally.**  Milnor writes the `w_α` as functions of `u`, i.e. on a
  coordinate patch, and does not say why they exist (Gram–Schmidt applied to a basis completing
  the `∂x/∂uⁱ`); they need not extend along all of `M` (the normal bundle of a Möbius band in `ℝ³`
  is not trivial).  The formalization needs no frame.
* **"The rank is equal to the rank of the upper left hand block"** (p. 35) is a slip: the
  `n × n` matrix has rank `n − k` plus the rank of that `k × k` block.  What the argument needs,
  and what is true, is that the two nullities agree (`Morse.finrank_ker_mfd_normalEnd`).
* That `N` is an `n`-manifold, "not difficult" in Milnor, is Problem 11 of Chapter 8 of the
  companion volume, formalized there.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

namespace Morse

open Milnor.Problems (normalBundleSet normalSum isSliceSubmanifold_normalBundle)

variable {n k w : ℕ} {M : Set (𝔼 n)}
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M)

/-! ### The normal bundle as a set -/

section Set

/-- A point `(q, v)` lies in the normal bundle iff `q ∈ M` and `v ⊥ T_qM`. -/
theorem mem_normalBundleSet_iff {q v : 𝔼 n} :
    (q, v) ∈ normalBundleSet hM ↔ ∃ hq : q ∈ M, v ∈ (tangentSubspace hM ⟨q, hq⟩)ᗮ := by
  refine exists_congr fun hq => ?_
  rw [Submodule.mem_orthogonal']
  rfl

theorem fst_mem_of_mem_normalBundleSet {y : 𝔼 n × 𝔼 n} (hy : y ∈ normalBundleSet hM) : y.1 ∈ M :=
  hy.fst

/-- The foot point `q ∈ M` of a point `(q, v)` of the normal bundle. -/
def footPoint (x : normalBundleSet hM) : M :=
  ⟨x.1.1, fst_mem_of_mem_normalBundleSet hM x.2⟩

@[simp] theorem footPoint_coe (x : normalBundleSet hM) : (footPoint hM x : 𝔼 n) = x.1.1 := rfl

end Set

/-! ### Milnor's parametrization and the fundamental forms -/

section Param

/-- **Milnor's parametrization** `u ↦ x(u)` of `M` near `p` (p. 33): the inverse of the slice chart
of `M` chosen at `p`. -/
abbrev xParam (p : M) : 𝔼 k → 𝔼 n := Milnor.Tub.φ hM p

/-- The coordinates `u_p` of `p` in Milnor's parametrization. -/
abbrev uParam (p : M) : 𝔼 k := Milnor.Tub.z₀ hM p

/-- The derivative `dx` at `u_p`: the vectors `∂x/∂uⁱ` at `p`. -/
def dParam (p : M) : 𝔼 k →L[ℝ] 𝔼 n := fderiv ℝ (xParam hM p) (uParam hM p)

/-- The second derivative `d²x` at `u_p`: the vectors `∂²x/∂uⁱ∂uʲ` at `p`. -/
def d2Param (p : M) : 𝔼 k →L[ℝ] 𝔼 k →L[ℝ] 𝔼 n :=
  fderiv ℝ (fderiv ℝ (xParam hM p)) (uParam hM p)

theorem xParam_uParam (p : M) : xParam hM p (uParam hM p) = p := Milnor.Tub.φ_z₀ hM p

theorem contDiffAt_xParam (p : M) : ContDiffAt ℝ ∞ (xParam hM p) (uParam hM p) :=
  (Milnor.Tub.contDiffOn_φ hM p).contDiffAt
    ((Milnor.Tub.isOpen_Ω hM p).mem_nhds (Milnor.Tub.z₀_mem hM p))

theorem hasFDerivAt_fderiv_xParam (p : M) :
    HasFDerivAt (fderiv ℝ (xParam hM p)) (d2Param hM p) (uParam hM p) :=
  (((contDiffAt_xParam hM p).fderiv_right (m := 1) (by norm_cast)).differentiableAt
    (by norm_num)).hasFDerivAt

theorem injective_dParam (p : M) : Injective (dParam hM p) :=
  Milnor.Tub.injective_fderiv_φ hM p (Milnor.Tub.z₀_mem hM p)

/-- The slice chart composed with the parametrization is `u ↦ (u, 0)`, so
`dσ_p ∘ dx_{u_p} = inl`. -/
theorem fderiv_σφ_comp_dParam (p : M) :
    (fderiv ℝ (Milnor.Tub.σ hM p).φ p.1).comp (dParam hM p) =
      ContinuousLinearMap.inl ℝ (𝔼 k) (𝔼 w) := by
  have hz := Milnor.Tub.z₀_mem hM p
  have hcomp : (fun z' => (Milnor.Tub.σ hM p).φ (Milnor.Tub.φ hM p z')) =ᶠ[𝓝 (uParam hM p)]
      fun z' : 𝔼 k => (z', (0 : 𝔼 w)) := by
    filter_upwards [(Milnor.Tub.isOpen_Ω hM p).mem_nhds hz] with z' hz'
    exact (Milnor.Tub.σ hM p).φ.apply_invFun hz'
  have h1 : HasFDerivAt (fun z' => (Milnor.Tub.σ hM p).φ (Milnor.Tub.φ hM p z'))
      ((fderiv ℝ (Milnor.Tub.σ hM p).φ (Milnor.Tub.φ hM p (uParam hM p))).comp
        (dParam hM p)) (uParam hM p) :=
    (Milnor.Tub.hasFDerivAt_σφ hM p (Milnor.Tub.φ_mem_source hM p hz)).comp _
      (Milnor.Tub.hasFDerivAt_φ hM p hz)
  have h2 : HasFDerivAt (fun z' : 𝔼 k => (z', (0 : 𝔼 w)))
      (ContinuousLinearMap.inl ℝ (𝔼 k) (𝔼 w)) (uParam hM p) :=
    (hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _)
  have h3 := (h1.congr_of_eventuallyEq hcomp.symm).unique h2
  rwa [Milnor.Tub.φ_z₀] at h3

/-- The derivative of the slice chart at `p` is injective. -/
theorem injective_fderiv_σφ (p : M) : Injective (fderiv ℝ (Milnor.Tub.σ hM p).φ p.1) := by
  have hloc := (Milnor.Tub.σ hM p).φ.isLocalDiffeomorphAt 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 k × 𝔼 w) ∞
    (Milnor.Tub.mem_source hM p)
  have h := (hloc.mfderivToContinuousLinearEquiv (by simp)).injective
  rw [← mfderiv_eq_fderiv]
  exact h

/-- **The derivative of the adjoint `B a = (dx_{c(a)})†`** used in the local defining function of
the normal bundle: `dB_p(u) = (d²x(dc_p u, ·))†`, `c(a)` being the first slice coordinate. -/
theorem hasFDerivAt_B (p : M) :
    HasFDerivAt (Milnor.Problems.NormalAux.B hM p)
      ((Milnor.Tub.adjointCLM.comp (d2Param hM p)).comp
        ((ContinuousLinearMap.fst ℝ (𝔼 k) (𝔼 w)).comp
          (fderiv ℝ (Milnor.Tub.σ hM p).φ p.1))) p.1 := by
  have hA : HasFDerivAt (Milnor.Tub.A hM p) (Milnor.Tub.adjointCLM.comp (d2Param hM p))
      (uParam hM p) :=
    Milnor.Tub.adjointCLM.hasFDerivAt.comp _ (hasFDerivAt_fderiv_xParam hM p)
  have hc : HasFDerivAt (fun a => ((Milnor.Tub.σ hM p).φ a).1)
      ((ContinuousLinearMap.fst ℝ (𝔼 k) (𝔼 w)).comp (fderiv ℝ (Milnor.Tub.σ hM p).φ p.1)) p.1 :=
    (Milnor.Tub.hasFDerivAt_σφ hM p (Milnor.Tub.mem_source hM p)).fst
  exact hA.comp p.1 hc

theorem B_self_inner (p : M) (h : 𝔼 n) (η : 𝔼 k) :
    ⟪Milnor.Problems.NormalAux.B hM p p.1 h, η⟫ = ⟪h, dParam hM p η⟫ :=
  Milnor.Tub.A_inner hM p _ h η

end Param

/-! ### The tangent space of the normal bundle -/

section Tangent

variable (hkw : k + w = n)

include hkw in
/-- The dimension count `n + (w + k) = 2n` for the normal bundle. -/
theorem finrank_normalBundle_add :
    finrank ℝ (𝔼 n) + finrank ℝ (𝔼 w × 𝔼 k) = finrank ℝ (𝔼 n × 𝔼 n) := by
  simp only [finrank_prod, finrank_euclideanSpace_fin]
  omega

/-- **The tangent space of the normal bundle** at `x = (q, v)`, as a subspace of `ℝⁿ × ℝⁿ`: a pair
`(u, h)` is tangent to `N` at `(q, v)` iff `u = dx(ξ)` is tangent to `M` and
`⟪h, ∂x/∂η⟫ + ⟪v, ∂²x/∂ξ∂η⟫ = 0` for all `η`.  This is the derivative, in the direction
`(u, h)`, of the equations `⟪v, ∂x/∂η⟫ = 0` defining `N`; Milnor uses it on p. 35 in the form
`0 = ∂/∂uⁱ (w_α · ∂x/∂uʲ)`. -/
theorem mem_range_mfd_val_normalBundle_iff (x : normalBundleSet hM) (t : 𝔼 n × 𝔼 n) :
    letI := (isSliceSubmanifold_normalBundle hM hkw).chartedSpace
    t ∈ LinearMap.range (Milnor.mfd 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n × 𝔼 n)
        (Subtype.val : normalBundleSet hM → 𝔼 n × 𝔼 n) x : 𝔼 n →ₗ[ℝ] 𝔼 n × 𝔼 n) ↔
      ∃ ξ : 𝔼 k, t.1 = dParam hM (footPoint hM x) ξ ∧
        ∀ η, ⟪t.2, dParam hM (footPoint hM x) η⟫ +
          ⟪x.1.2, d2Param hM (footPoint hM x) ξ η⟫ = 0 := by
  have hN := isSliceSubmanifold_normalBundle hM hkw
  let := hN.chartedSpace
  have := hN.isManifold
  set p := footPoint hM x with hp
  have hxV : x.1.1 ∈ Milnor.Problems.NormalAux.V hM p := Milnor.Problems.NormalAux.mem_V hM p
  have hker := hN.range_mfderiv_val_eq_ker (finrank_normalBundle_add hkw)
    x ((Milnor.Problems.NormalAux.isOpen_V hM p).prod isOpen_univ) ⟨hxV, mem_univ _⟩
    (g := Milnor.Problems.NormalAux.g hM p)
    (contMDiffOn_iff_contDiffOn.2 (Milnor.Problems.NormalAux.contDiffOn_g hM p))
    (fun y hy hyS => (Milnor.Problems.NormalAux.mem_normalBundleSet_iff hM p hy.1).1 hyS)
    (by
      rw [mfderiv_eq_fderiv]
      exact Milnor.Problems.NormalAux.surjective_fderiv_g hM p hxV x.1.2)
  have hmfd : Milnor.mfd 𝓘(ℝ, 𝔼 n × 𝔼 n) 𝓘(ℝ, 𝔼 w × 𝔼 k) (Milnor.Problems.NormalAux.g hM p) x.1 =
      fderiv ℝ (Milnor.Problems.NormalAux.g hM p) x.1 := mfderiv_eq_fderiv
  have hg := Milnor.Problems.NormalAux.fderiv_g_apply hM p hxV x.1.2 t.1 t.2
  simp only [Prod.mk.eta] at hg
  rw [hker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hmfd, hg, Prod.mk_eq_zero]
  have hpx : x.1.1 = (p : 𝔼 n) := rfl
  rw [hpx]
  set dσ := fderiv ℝ (Milnor.Tub.σ hM p).φ p.1 with hdσ
  have hσx : ∀ ξ, dσ (dParam hM p ξ) = (ξ, 0) := fun ξ => by
    have := congrArg (fun L : 𝔼 k →L[ℝ] 𝔼 k × 𝔼 w => L ξ) (fderiv_σφ_comp_dParam hM p)
    simpa using this
  have hB : ∀ u η, ⟪fderiv ℝ (Milnor.Problems.NormalAux.B hM p) p.1 u x.1.2, η⟫ =
      ⟪x.1.2, d2Param hM p (dσ u).1 η⟫ := fun u η => by
    rw [(hasFDerivAt_B hM p).fderiv]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _
  have key : ∀ ξ, (∀ η, ⟪t.2, dParam hM p η⟫ + ⟪x.1.2, d2Param hM p ξ η⟫ = 0) ↔
      Milnor.Problems.NormalAux.B hM p p.1 t.2 +
        fderiv ℝ (Milnor.Problems.NormalAux.B hM p) p.1 (dParam hM p ξ) x.1.2 = 0 := by
    intro ξ
    have hinner : ∀ η, ⟪Milnor.Problems.NormalAux.B hM p p.1 t.2 +
        fderiv ℝ (Milnor.Problems.NormalAux.B hM p) p.1 (dParam hM p ξ) x.1.2, η⟫ =
        ⟪t.2, dParam hM p η⟫ + ⟪x.1.2, d2Param hM p ξ η⟫ := fun η => by
      rw [inner_add_left, B_self_inner, hB, hσx]
    constructor
    · intro h
      exact ext_inner_right ℝ fun η => by rw [hinner, h, inner_zero_left]
    · intro h η
      rw [← hinner, h, inner_zero_left]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(dσ t.1).1, ?_, ?_⟩
    · apply injective_fderiv_σφ hM p
      rw [← hdσ, hσx]
      exact Prod.ext rfl h1
    · have ht : dParam hM p (dσ t.1).1 = t.1 := by
        apply injective_fderiv_σφ hM p
        rw [← hdσ, hσx]
        exact Prod.ext rfl h1.symm
      rw [key, ht]
      exact h2
  · rintro ⟨ξ, h1, h2⟩
    refine ⟨by rw [h1, hσx], ?_⟩
    rw [h1]
    exact (key ξ).1 h2

end Tangent

/-! ### The fundamental forms -/

section Forms

variable (n) in
/-- The inner product of `ℝⁿ` as a continuous bilinear form.  (Mathlib's `innerSL ℝ` is typed as
conjugate-linear in its first argument, which over `ℝ` is the same thing.) -/
def innerBilin : 𝔼 n →L[ℝ] 𝔼 n →L[ℝ] ℝ := innerSL ℝ

@[simp] theorem innerBilin_apply (u v : 𝔼 n) : innerBilin n u v = ⟪u, v⟫ := rfl

/-- **The first fundamental form** at `p` (Milnor, p. 33): `g(ξ, η) = ⟪∂x/∂ξ, ∂x/∂η⟫`, in the
parametrization `xParam hM p`. -/
def firstFF (p : M) : 𝔼 k →L[ℝ] 𝔼 k →L[ℝ] ℝ :=
  (innerBilin n).bilinearComp (dParam hM p) (dParam hM p)

/-- **The second fundamental form in the direction `v`** at `p` (Milnor, pp. 33–34):
`ℓ_v(ξ, η) = ⟪v, ∂²x/∂ξ∂η⟫`.  For `v` normal to `M` at `p` this is Milnor's `v · ℓ_ij`, the
tangential part of `∂²x/∂uⁱ∂uʲ` being orthogonal to `v`. -/
def secondFF (p : M) (v : 𝔼 n) : 𝔼 k →L[ℝ] 𝔼 k →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (𝔼 k) (𝔼 n) ℝ (innerSL ℝ v)).comp (d2Param hM p)

/-- The bilinear form `(ξ, η) ↦ ⟪T(∂x/∂ξ), ∂x/∂η⟫ − ⟪v, ∂²x/∂ξ∂η⟫` attached to a linear map
`T : ℝⁿ → ℝⁿ` (the derivative of `Γ` in the generalized endpoint map `(q, v) ↦ Γ q + v`); for
`T = id` it is Milnor's matrix `(g_ij − v · ℓ_ij)` of Assertion 6.4. -/
def normalForm (T : 𝔼 n →L[ℝ] 𝔼 n) (p : M) (v : 𝔼 n) : 𝔼 k →L[ℝ] 𝔼 k →L[ℝ] ℝ :=
  (innerBilin n).bilinearComp (T.comp (dParam hM p)) (dParam hM p) -
    secondFF hM p v

variable {hM}

@[simp] theorem firstFF_apply (p : M) (ξ η : 𝔼 k) :
    firstFF hM p ξ η = ⟪dParam hM p ξ, dParam hM p η⟫ := rfl

@[simp] theorem secondFF_apply (p : M) (v : 𝔼 n) (ξ η : 𝔼 k) :
    secondFF hM p v ξ η = ⟪v, d2Param hM p ξ η⟫ := rfl

@[simp] theorem normalForm_apply (T : 𝔼 n →L[ℝ] 𝔼 n) (p : M) (v : 𝔼 n) (ξ η : 𝔼 k) :
    normalForm hM T p v ξ η = ⟪T (dParam hM p ξ), dParam hM p η⟫ - ⟪v, d2Param hM p ξ η⟫ := rfl

theorem normalForm_id (p : M) (v : 𝔼 n) :
    normalForm hM (ContinuousLinearMap.id ℝ (𝔼 n)) p v = firstFF hM p - secondFF hM p v := rfl

theorem secondFF_smul (p : M) (t : ℝ) (v : 𝔼 n) : secondFF hM p (t • v) = t • secondFF hM p v := by
  ext ξ η
  simp [inner_smul_left]

end Forms

/-! ### The generalized endpoint map and its derivative -/

section Endpoint

/-- **The generalized endpoint map** `(q, v) ↦ Γ(q) + v` on the normal bundle.  For `Γ = id` it is
Milnor's endpoint map `E(q, v) = q + v` (`Milnor.Problems.normalSum`, `Morse.normalEnd_id`); for
`Γ = −∇f` it parametrizes the vectors `a` for which `f + ⟪a, ·⟫` has a critical point
(`Morse/Chapter4/Approximation.lean`). -/
def normalEnd (Γ : 𝔼 n → 𝔼 n) (x : normalBundleSet hM) : 𝔼 n := Γ x.1.1 + x.1.2

theorem normalEnd_id : normalEnd hM id = normalSum hM := rfl

variable (hkw : k + w = n)

/-- The derivative of the generalized endpoint map: `(u, h) ↦ dΓ(u) + h` on the tangent space of
`N`. -/
theorem hasMFDerivAt_normalEnd {Γ : 𝔼 n → 𝔼 n} {x : normalBundleSet hM}
    (hΓ : DifferentiableAt ℝ Γ x.1.1) :
    letI := (isSliceSubmanifold_normalBundle hM hkw).chartedSpace
    HasMFDerivAt 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n) (normalEnd hM Γ) x
      ((((fderiv ℝ Γ x.1.1).comp (ContinuousLinearMap.fst ℝ (𝔼 n) (𝔼 n))) +
          ContinuousLinearMap.snd ℝ (𝔼 n) (𝔼 n)).comp
        (Milnor.mfd 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n × 𝔼 n)
          (Subtype.val : normalBundleSet hM → 𝔼 n × 𝔼 n) x)) := by
  have hN := isSliceSubmanifold_normalBundle hM hkw
  let := hN.chartedSpace
  have := hN.isManifold
  have hval : MDifferentiableAt 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n × 𝔼 n)
      (Subtype.val : normalBundleSet hM → 𝔼 n × 𝔼 n) x :=
    hN.contMDiff_val.mdifferentiableAt (by simp)
  have hG : HasFDerivAt (fun y : 𝔼 n × 𝔼 n => Γ y.1 + y.2)
      (((fderiv ℝ Γ x.1.1).comp (ContinuousLinearMap.fst ℝ (𝔼 n) (𝔼 n))) +
        ContinuousLinearMap.snd ℝ (𝔼 n) (𝔼 n)) x.1 :=
    (hΓ.hasFDerivAt.comp x.1 hasFDerivAt_fst).add hasFDerivAt_snd
  exact hG.hasMFDerivAt.comp x (Milnor.hasMFDerivAt_mfd hval)

/-- The generalized endpoint map is smooth over the open set where `Γ` is smooth. -/
theorem contMDiffOn_normalEnd {Γ : 𝔼 n → 𝔼 n} {U : Set (𝔼 n)} (hΓ : ContDiffOn ℝ ∞ Γ U) :
    letI := (isSliceSubmanifold_normalBundle hM hkw).chartedSpace
    ContMDiffOn 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n) ∞ (normalEnd hM Γ) {x | x.1.1 ∈ U} := by
  have hN := isSliceSubmanifold_normalBundle hM hkw
  let := hN.chartedSpace
  have := hN.isManifold
  have hG : ContDiffOn ℝ ∞ (fun y : 𝔼 n × 𝔼 n => Γ y.1 + y.2) (U ×ˢ univ) :=
    (hΓ.comp contDiff_fst.contDiffOn fun y hy => hy.1).add contDiff_snd.contDiffOn
  exact (contMDiffOn_iff_contDiffOn.2 hG).comp hN.contMDiff_val.contMDiffOn
    fun x hx => ⟨hx, mem_univ _⟩

/-- **The kernel of the derivative of the generalized endpoint map.**  At `x = (q, v) ∈ N`, the
nullity of `d(Γ + ·)` on `T_xN` equals the nullity of the bilinear form
`(ξ, η) ↦ ⟪dΓ_q(∂x/∂ξ), ∂x/∂η⟫ − ⟪v, ∂²x/∂ξ∂η⟫` on `ℝᵏ`: the map `ξ ↦ (∂x/∂ξ, −dΓ_q(∂x/∂ξ))`
is an isomorphism from the null space of this form onto the kernel.  For `Γ = id` this is
Milnor's computation on p. 35 (the "upper left hand block" of the Jacobian of `E`). -/
theorem finrank_ker_mfd_normalEnd {Γ : 𝔼 n → 𝔼 n} (x : normalBundleSet hM)
    (hΓ : DifferentiableAt ℝ Γ x.1.1) :
    letI := (isSliceSubmanifold_normalBundle hM hkw).chartedSpace
    finrank ℝ (LinearMap.ker (Milnor.mfd 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n) (normalEnd hM Γ) x :
        𝔼 n →ₗ[ℝ] 𝔼 n)) =
      nullity (normalForm hM (fderiv ℝ Γ x.1.1) (footPoint hM x) x.1.2) := by
  have hN := isSliceSubmanifold_normalBundle hM hkw
  let := hN.chartedSpace
  have := hN.isManifold
  set p := footPoint hM x with hp
  set L := Milnor.mfd 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n × 𝔼 n)
    (Subtype.val : normalBundleSet hM → 𝔼 n × 𝔼 n) x with hL
  set T := fderiv ℝ Γ x.1.1 with hT
  set S : 𝔼 n × 𝔼 n →L[ℝ] 𝔼 n := T.comp (ContinuousLinearMap.fst ℝ (𝔼 n) (𝔼 n)) +
    ContinuousLinearMap.snd ℝ (𝔼 n) (𝔼 n) with hS
  have hmfd : Milnor.mfd 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n) (normalEnd hM Γ) x = S.comp L :=
    Milnor.HasMFDerivAt.mfd_eq (hasMFDerivAt_normalEnd hM hkw hΓ)
  have hLinj : Injective (L : 𝔼 n →ₗ[ℝ] 𝔼 n × 𝔼 n) := Milnor.injective_mfderiv_val hN x
  set dx := dParam hM p with hdx
  set ι : 𝔼 k →L[ℝ] 𝔼 n × 𝔼 n := dx.prod (-(T.comp dx)) with hι
  have hιinj : Injective (ι : 𝔼 k →ₗ[ℝ] 𝔼 n × 𝔼 n) :=
    fun a b h => injective_dParam hM p (congrArg Prod.fst h)
  have heq : LinearMap.range (L : 𝔼 n →ₗ[ℝ] 𝔼 n × 𝔼 n) ⊓
      LinearMap.ker (S : 𝔼 n × 𝔼 n →ₗ[ℝ] 𝔼 n) =
      (nullSpace (normalForm hM T p x.1.2)).map (ι : 𝔼 k →ₗ[ℝ] 𝔼 n × 𝔼 n) := by
    ext t
    rw [Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_map]
    rw [mem_range_mfd_val_normalBundle_iff hM hkw x t]
    constructor
    · rintro ⟨⟨ξ, h1, h2⟩, h3⟩
      have h3' : T t.1 + t.2 = 0 := h3
      have ht2 : t.2 = -T (dx ξ) := by rw [← h1]; exact eq_neg_of_add_eq_zero_right h3'
      refine ⟨ξ, ?_, ?_⟩
      · rw [mem_nullSpace]
        intro η
        rw [normalForm_apply]
        have := h2 η
        rw [ht2, inner_neg_left] at this
        linarith
      · exact Prod.ext h1.symm ht2.symm
    · rintro ⟨ξ, hξ, rfl⟩
      rw [mem_nullSpace] at hξ
      refine ⟨⟨ξ, rfl, fun η => ?_⟩, ?_⟩
      · have := hξ η
        rw [normalForm_apply] at this
        change ⟪-T (dx ξ), dx η⟫ + ⟪x.1.2, d2Param hM p ξ η⟫ = 0
        rw [inner_neg_left]
        linarith
      · change T (dx ξ) + -T (dx ξ) = 0
        exact add_neg_cancel _
  rw [hmfd, ContinuousLinearMap.toLinearMap_comp, LinearMap.ker_comp,
    (Submodule.equivMapOfInjective _ hLinj (Submodule.comap _ _)).finrank_eq,
    Submodule.map_comap_eq, heq, ← (Submodule.equivMapOfInjective _ hιinj _).finrank_eq]
  rfl

end Endpoint

end Morse
