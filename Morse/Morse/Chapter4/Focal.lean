import Morse.Chapter4.NormalBundle
import Morse.Chapter4.Sard

/-!
Milnor, *Morse Theory*, §6, pp. 32–36.

# Focal points; `L_p` is a Morse function for almost every `p`

Setting and notation as in `Morse/Chapter4/NormalBundle.lean`: `M ⊆ ℝⁿ` is a slice submanifold
of dimension `k`, `N` its normal bundle, `E(q, v) = q + v` the endpoint map, and
`L_p(q) = ‖q − p‖²` for `p ∈ ℝⁿ` (Milnor, p. 32).

## Milnor's definitions and statements (paraphrased)

* (p. 32) `e ∈ ℝⁿ` is a *focal point of `(M, q)` with multiplicity `μ`* if `e = q + v` with
  `(q, v) ∈ N` and the Jacobian of `E` at `(q, v)` has nullity `μ > 0`; a *focal point of `M`* if
  it is a focal point of `(M, q)` for some `q ∈ M`.
* **Corollary 6.2** (p. 33): almost every `x ∈ ℝⁿ` is not a focal point of `M`.  (The focal points
  are the images of the critical points of `E`; Sard's theorem, Theorem 6.1.)
* **Assertion 6.4** (p. 35): for a unit normal `v` at `q`, `q + tv` is a focal point of `(M, q)`
  with multiplicity `μ` iff the matrix `(g_ij − t v · ℓ_ij)` is singular with nullity `μ`.
  (Assertion 6.4 is the core of the proof of Lemma 6.3, which locates the focal points along the
  normal line at the reciprocals of the principal curvatures; Lemma 6.3 proper, and the index
  theorem Lemma 6.9, are in `Morse/Chapter4/Curvature.lean`.)
* (p. 35) `q` is a critical point of `L_p` iff `q − p` is normal to `M` at `q`; (p. 36) at a
  critical point, writing `p = q + tv`, the Hessian of `L_p` in the coordinates `u` is
  `2(g_ij − t v · ℓ_ij)`.
* **Lemma 6.5** (p. 36): `q` is a degenerate critical point of `L_p` iff `p` is a focal point of
  `(M, q)`, and the nullity of `q` as a critical point is the multiplicity of `p` as a focal point.
* **Theorem 6.6** (p. 36): for almost all `p ∈ ℝⁿ`, `L_p` has no degenerate critical points.

## Formal statements

* `Morse.endpointNullity`, `Morse.IsFocalPointMult`, `Morse.IsFocalPoint`, `Morse.focalSet`:
  Milnor's definitions.  The nullity of the Jacobian of `E` at `x ∈ N` is the dimension of the
  kernel of `mfderiv E x`, the tangent space `T_xN` being identified with `ℝⁿ` by the chart of `N`
  at `x` (another chart changes the derivative by an isomorphism, which preserves the nullity).
* `Morse.endpointNullity_pos_iff`, `Morse.isFocalPoint_iff`,
  `Morse.focalSet_eq_image_critPoints`: `e` is a focal point of `(M, q)` iff `(q, e − q) ∈ N` is
  a critical point of `E` (a point where `dE` is not onto, `Milnor.critPoints`), the multiplicity
  being the nullity of `dE` there; so the focal set is the set of critical values of `E`.
* `Morse.measure_focalSet_eq_zero` (**Corollary 6.2**), for every Haar measure on `ℝⁿ`.
* `Morse.endpointNullity_eq_nullity`, `Morse.isFocalPointMult_add_smul_iff` (**Assertion 6.4**,
  for any normal vector `v`, unit or not), `Morse.not_isFocalPoint_self` (`q` is never a focal
  point of `(M, q)`).
* `Morse.isCriticalPointM_normSq_sub_iff_mem_normalBundleSet` (p. 35),
  `Morse.hessian_normSq_sub_xParam` (p. 36).
* `Morse.isFocalPointMult_iff`, `Morse.nullityM_normSq_sub_eq_endpointNullity`,
  `Morse.isDegenerate_normSq_sub_iff_isFocalPoint` (**Lemma 6.5**, with multiplicities).
* `Morse.ae_isMorseFunction_normSq_sub` (**Theorem 6.6**, for every Haar measure on `ℝⁿ`),
  `Morse.ae_volume_isMorseFunction_normSq_sub` (Lebesgue measure); consequences:
  `Morse.exists_mem_isMorseFunction_normSq_sub` (such `p` are dense) and
  `Morse.exists_isMorseFunction_normSq_sub`.

## Gaps in Milnor's text

* **The case `t = 0`.**  Milnor's step "`(g_ij − t v · ℓ_ij)` is singular iff `1/t` is an
  eigenvalue" divides by `t`.  For `t = 0` the matrix is `(g_ij)`, which is non-singular, so `q` is
  never a focal point of `(M, q)` (`Morse.not_isFocalPoint_self`).
* **"Setting `p = x + tv`, as in the proof of Lemma 6.3"** (p. 36) presupposes that `p − q` is
  normal to `M` at `q`, i.e. that `q` is a critical point of `L_p` (p. 35), and that `p ≠ q` if
  `v` is to be a unit vector; for `p = q` the Hessian is `2(g_ij)`, non-degenerate.  Here
  `v = p − q` need not be a unit vector (`secondFF` is linear in `v`), which removes the case
  distinction.
* **Lemma 6.5 for non-critical `q`**: if `q` is not a critical point of `L_p`, then `p − q` is not
  normal at `q` and `p` is not a focal point of `(M, q)`; Milnor leaves this case implicit.
* **Dimensions.**  Milnor's `N` is `n`-dimensional because `k + (n − k) = n`; for a slice
  submanifold this needs `M ≠ ∅` (`Morse.slice_dim_add_eq_of_nonempty`), and for `M = ∅`
  Theorem 6.6 is vacuous.  Theorem 6.1 needs a countable basis for `N`, automatic for a subset of
  `ℝ²ⁿ`.
-/

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

namespace Morse

open Milnor.Problems (normalBundleSet normalSum isSliceSubmanifold_normalBundle)

/-! ### Null spaces of multiples -/

section NullSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem nullSpace_smul_of_ne_zero {c : ℝ} (hc : c ≠ 0) (H : E →L[ℝ] E →L[ℝ] ℝ) :
    nullSpace (c • H) = nullSpace H := by
  ext v
  simp [mem_nullSpace, hc]

theorem nullity_smul_of_ne_zero {c : ℝ} (hc : c ≠ 0) (H : E →L[ℝ] E →L[ℝ] ℝ) :
    nullity (c • H) = nullity H := by
  rw [nullity, nullSpace_smul_of_ne_zero hc, nullity]

end NullSpace

variable {n k w : ℕ} {M : Set (𝔼 n)}
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M)

include hM in
/-- A nonempty slice submanifold of `ℝⁿ` modelled on `ℝᵏ` with complement `ℝʷ` has `k + w = n`
(the derivative of a slice chart is a linear isomorphism `ℝⁿ ≅ ℝᵏ × ℝʷ`). -/
theorem slice_dim_add_eq_of_nonempty (hne : M.Nonempty) : k + w = n := by
  obtain ⟨q, hq⟩ := hne
  obtain ⟨σ, hσ⟩ := hM q hq
  have hloc := σ.φ.isLocalDiffeomorphAt 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 k × 𝔼 w) ∞ hσ
  have h := (hloc.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv.finrank_eq
  have h' : finrank ℝ (𝔼 n) = finrank ℝ (𝔼 k × 𝔼 w) := h
  simp only [finrank_euclideanSpace_fin, finrank_prod] at h'
  omega

/-! ### Focal points -/

section Focal

variable (hkw : k + w = n)

/-- **The nullity of the Jacobian of the endpoint map** `E(q, v) = q + v` at a point `x` of the
normal bundle `N` (Milnor, p. 32): the dimension of the kernel of `dE_x : T_xN → ℝⁿ`, the tangent
space of `N` being identified with `ℝⁿ` by the chart of `N` at `x`.  (The dimension does not
depend on the chart: two charts differ by an isomorphism of `ℝⁿ`.) -/
def endpointNullity (x : normalBundleSet hM) : ℕ :=
  letI := (isSliceSubmanifold_normalBundle hM hkw).chartedSpace
  finrank ℝ (LinearMap.ker (Milnor.mfd 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n) (normalSum hM) x : 𝔼 n →ₗ[ℝ] 𝔼 n))

/-- **Focal point of `(M, q)` with multiplicity `μ`** (Milnor, p. 32): `e = q + v` with
`(q, v) ∈ N` and the Jacobian of `E` at `(q, v)` has nullity `μ > 0`.  (Given `q` and `e`, the
vector `v = e − q` is determined.) -/
def IsFocalPointMult (q : M) (e : 𝔼 n) (μ : ℕ) : Prop :=
  ∃ h : ((q : 𝔼 n), e - q) ∈ normalBundleSet hM, endpointNullity hM hkw ⟨_, h⟩ = μ ∧ 0 < μ

/-- **Focal point of `(M, q)`** (Milnor, p. 32): a focal point of `(M, q)` of some multiplicity. -/
def IsFocalPoint (q : M) (e : 𝔼 n) : Prop :=
  ∃ μ, IsFocalPointMult hM hkw q e μ

/-- **The focal points of `M`** (Milnor, p. 32): the points which are focal points of `(M, q)` for
some `q ∈ M`. -/
def focalSet : Set (𝔼 n) :=
  {e | ∃ q : M, IsFocalPoint hM hkw q e}

/-- The kernel of `dE_x` is nontrivial iff `x` is a critical point of `E` (Milnor, p. 33: a
critical point is a point where the Jacobian is singular); `N` and `ℝⁿ` have the same
dimension, so singular, not injective and not surjective are the same. -/
theorem endpointNullity_pos_iff (x : normalBundleSet hM) :
    letI := (isSliceSubmanifold_normalBundle hM hkw).chartedSpace
    0 < endpointNullity hM hkw x ↔
      x ∈ Milnor.critPoints 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n) (normalSum hM) := by
  let := (isSliceSubmanifold_normalBundle hM hkw).chartedSpace
  set L : 𝔼 n →ₗ[ℝ] 𝔼 n := (Milnor.mfd 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n) (normalSum hM) x : 𝔼 n →ₗ[ℝ] 𝔼 n)
    with hL
  have hcrit : x ∈ Milnor.critPoints 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n) (normalSum hM) ↔ ¬ Surjective L :=
    Iff.rfl
  rw [hcrit, endpointNullity, ← hL, ← LinearMap.injective_iff_surjective, Nat.pos_iff_ne_zero,
    Ne, Submodule.finrank_eq_zero, LinearMap.ker_eq_bot]

/-- **Focal points are the images of the critical points of `E`** (Milnor, p. 32 and the proof of
Corollary 6.2): `e` is a focal point of `(M, q)` iff `(q, e − q) ∈ N` and `(q, e − q)` is a
critical point of `E`; the multiplicity of the focal point is the nullity of `dE` there. -/
theorem isFocalPoint_iff (q : M) (e : 𝔼 n) :
    letI := (isSliceSubmanifold_normalBundle hM hkw).chartedSpace
    IsFocalPoint hM hkw q e ↔ ∃ h : ((q : 𝔼 n), e - q) ∈ normalBundleSet hM,
      (⟨_, h⟩ : normalBundleSet hM) ∈ Milnor.critPoints 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n) (normalSum hM) := by
  constructor
  · rintro ⟨μ, h, hμ, hpos⟩
    exact ⟨h, (endpointNullity_pos_iff hM hkw _).1 (hμ ▸ hpos)⟩
  · rintro ⟨h, hc⟩
    exact ⟨_, h, rfl, (endpointNullity_pos_iff hM hkw _).2 hc⟩

/-- **The focal set is the set of critical values of the endpoint map** `E : N → ℝⁿ`. -/
theorem focalSet_eq_image_critPoints :
    letI := (isSliceSubmanifold_normalBundle hM hkw).chartedSpace
    focalSet hM hkw = normalSum hM '' Milnor.critPoints 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n) (normalSum hM) := by
  let := (isSliceSubmanifold_normalBundle hM hkw).chartedSpace
  ext e
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨h, hc⟩ := (isFocalPoint_iff hM hkw q e).1 hq
    refine ⟨_, hc, ?_⟩
    change (q : 𝔼 n) + (e - q) = e
    abel
  · rintro ⟨x, hx, rfl⟩
    refine ⟨footPoint hM x, (isFocalPoint_iff hM hkw _ _).2 ?_⟩
    have hx' : (((footPoint hM x : M) : 𝔼 n), normalSum hM x - (footPoint hM x : 𝔼 n)) = x.1 := by
      change (x.1.1, x.1.1 + x.1.2 - x.1.1) = x.1
      rw [add_sub_cancel_left]
    have hmem : (((footPoint hM x : M) : 𝔼 n), normalSum hM x - (footPoint hM x : 𝔼 n)) ∈
        normalBundleSet hM := hx' ▸ x.2
    refine ⟨hmem, ?_⟩
    have hxx : (⟨_, hmem⟩ : normalBundleSet hM) = x := Subtype.ext hx'
    rw [hxx]
    exact hx

/-- **Corollary 6.2** (Milnor, p. 33): *for almost all `x ∈ ℝⁿ`, `x` is not a focal point of `M`*;
the focal set is a null set for every Haar measure on `ℝⁿ`.  Proof: it is the set of critical
values of the smooth map `E` from the `n`-manifold `N` (with a countable basis, as a subset of
`ℝ²ⁿ`) to `ℝⁿ`, which is null by Sard's theorem (Theorem 6.1). -/
theorem measure_focalSet_eq_zero (μ : Measure (𝔼 n)) [μ.IsAddHaarMeasure] :
    μ (focalSet hM hkw) = 0 := by
  have hN := isSliceSubmanifold_normalBundle hM hkw
  let := hN.chartedSpace
  have := hN.isManifold
  rw [focalSet_eq_image_critPoints hM hkw]
  exact measure_image_critPoints_eq_zero μ (Milnor.Problems.contMDiff_normalSum hM hkw)

end Focal

/-! ### Assertion 6.4 and Lemma 6.5 -/

section Lemma65

variable (hkw : k + w = n)

/-- The nullity of `dE` at `(q, v) ∈ N` is the nullity of the bilinear form
`g − ℓ_v = (⟪∂x/∂uⁱ, ∂x/∂uʲ⟫ − ⟪v, ∂²x/∂uⁱ∂uʲ⟫)` (Milnor, p. 35), computed in the
parametrization `xParam hM q` of `M` at `q`. -/
theorem endpointNullity_eq_nullity (x : normalBundleSet hM) :
    endpointNullity hM hkw x =
      nullity (firstFF hM (footPoint hM x) - secondFF hM (footPoint hM x) x.1.2) := by
  have h := finrank_ker_mfd_normalEnd hM hkw (Γ := id) x differentiableAt_id
  rw [fderiv_id, normalForm_id] at h
  exact h

/-- **Assertion 6.4** (Milnor, p. 35): *`q + tv` is a focal point of `(M, q)` with multiplicity
`μ` iff the matrix `(g_ij − t v · ℓ_ij)` is singular with nullity `μ`*, for `v` normal to `M` at
`q` (Milnor takes `v` a unit vector) and the fundamental forms computed in the parametrization
`xParam hM q`. -/
theorem isFocalPointMult_add_smul_iff (q : M) {v : 𝔼 n} (hv : v ∈ (tangentSubspace hM q)ᗮ)
    (t : ℝ) (μ : ℕ) :
    IsFocalPointMult hM hkw q ((q : 𝔼 n) + t • v) μ ↔
      nullity (firstFF hM q - t • secondFF hM q v) = μ ∧ 0 < μ := by
  have hmem : ((q : 𝔼 n), ((q : 𝔼 n) + t • v) - q) ∈ normalBundleSet hM := by
    rw [add_sub_cancel_left, mem_normalBundleSet_iff]
    exact ⟨q.2, Submodule.smul_mem _ t hv⟩
  have hnull : endpointNullity hM hkw ⟨_, hmem⟩ = nullity (firstFF hM q - t • secondFF hM q v) := by
    rw [endpointNullity_eq_nullity]
    change nullity (firstFF hM q - secondFF hM q ((q : 𝔼 n) + t • v - q)) = _
    rw [add_sub_cancel_left, secondFF_smul]
  constructor
  · rintro ⟨h, hμ, hpos⟩
    exact ⟨hnull ▸ hμ, hpos⟩
  · rintro ⟨hμ, hpos⟩
    exact ⟨hmem, hnull.trans hμ, hpos⟩

/-- `q` is never a focal point of `(M, q)` (Milnor, implicit in the proof of Lemma 6.3: for
`t = 0` the matrix `(g_ij − t v · ℓ_ij)` is `(g_ij)`, which is non-singular). -/
theorem not_isFocalPoint_self (q : M) : ¬ IsFocalPoint hM hkw q q := by
  rintro ⟨μ, h, hμ, hpos⟩
  rw [endpointNullity_eq_nullity] at hμ
  have h0 : (⟨_, h⟩ : normalBundleSet hM).1.2 = 0 := sub_self _
  have hq : footPoint hM ⟨_, h⟩ = q := rfl
  rw [h0, hq] at hμ
  -- the first fundamental form is non-degenerate: `dx` is injective
  have hnd : nullSpace (firstFF hM q - secondFF hM q 0) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro ξ hξ
    rw [mem_nullSpace] at hξ
    have := hξ ξ
    simp only [FunLike.coe_sub, Pi.sub_apply, firstFF_apply, secondFF_apply, inner_zero_left,
      sub_zero] at this
    rw [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at this
    exact injective_dParam hM q (this.trans (map_zero _).symm)
  rw [nullity, hnd, finrank_bot] at hμ
  omega

variable {hM}

/-- **The critical points of `L_p` and the normal bundle** (Milnor, p. 35): `q` is a critical point
of `L_p = ‖· − p‖²` on `M` iff `p − q ⊥ T_qM`, i.e. `(q, p − q) ∈ N`. -/
theorem isCriticalPointM_normSq_sub_iff_mem_normalBundleSet (p : 𝔼 n) (q : M) :
    letI := hM.chartedSpace
    IsCriticalPointM (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) q ↔
      ((q : 𝔼 n), p - q) ∈ normalBundleSet hM := by
  rw [isCriticalPointM_normSq_sub_iff hM p q, mem_normalBundleSet_iff]
  constructor
  · intro h
    refine ⟨q.2, ?_⟩
    rw [← neg_sub]
    exact Submodule.neg_mem _ h
  · rintro ⟨hq, h⟩
    rw [← neg_sub]
    exact Submodule.neg_mem _ h

/-- The Hessian of `L_p` in the parametrization `xParam hM q` at a critical point `q` is twice the
bilinear form `g − ℓ_{p−q}` (Milnor, p. 36: `∂²f/∂uⁱ∂uʲ = 2(g_ij − t v · ℓ_ij)` with
`p = q + tv`). -/
theorem hessian_normSq_sub_xParam (p : 𝔼 n) (q : M) :
    hessian (fun z => ‖xParam hM q z - p‖ ^ 2) (uParam hM q) =
      (2 : ℝ) • (firstFF hM q - secondFF hM q (p - q)) := by
  ext ξ η
  rw [hessian_normSq_sub_comp ((contDiffAt_xParam hM q).of_le (by norm_cast)) p ξ η,
    xParam_uParam]
  simp only [FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply,
    Pi.sub_apply, firstFF_apply, secondFF_apply, smul_eq_mul]
  rw [show (q : 𝔼 n) - p = -(p - q) by abel, inner_neg_right, real_inner_comm (p - q)]
  simp only [dParam, d2Param]
  ring

/-- **The nullity of `L_p` at a critical point is the multiplicity of the focal point** (Milnor,
Lemma 6.5, second sentence): if `(q, p − q) ∈ N` (i.e. `q` is a critical point of `L_p`), the
nullity of the Hessian of `L_p` at `q` equals the nullity of `dE` at `(q, p − q)`. -/
theorem nullityM_normSq_sub_eq_endpointNullity (p : 𝔼 n) (q : M)
    (h : ((q : 𝔼 n), p - q) ∈ normalBundleSet hM) :
    letI := hM.chartedSpace
    nullityM (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) q = endpointNullity hM hkw ⟨_, h⟩ := by
  let := hM.chartedSpace
  have hcrit := (isCriticalPointM_normSq_sub_iff_mem_normalBundleSet p q).2 h
  rw [nullityM_normSq_sub_eq hM (Milnor.Tub.σ hM q) p (Milnor.Tub.mem_source hM q) hcrit,
    endpointNullity_eq_nullity]
  change nullity (hessian (fun z => ‖xParam hM q z - p‖ ^ 2) (uParam hM q)) = _
  rw [hessian_normSq_sub_xParam, nullity_smul_of_ne_zero two_ne_zero]
  rfl

/-- **Lemma 6.5** (Milnor, p. 36), with multiplicities: *`p` is a focal point of `(M, q)` with
multiplicity `μ` iff `q` is a critical point of `L_p` with nullity `μ > 0`*. -/
theorem isFocalPointMult_iff (p : 𝔼 n) (q : M) (μ : ℕ) :
    letI := hM.chartedSpace
    IsFocalPointMult hM hkw q p μ ↔
      IsCriticalPointM (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) q ∧
        nullityM (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) q = μ ∧ 0 < μ := by
  let := hM.chartedSpace
  constructor
  · rintro ⟨h, hμ, hpos⟩
    exact ⟨(isCriticalPointM_normSq_sub_iff_mem_normalBundleSet p q).2 h,
      (nullityM_normSq_sub_eq_endpointNullity hkw p q h).trans hμ, hpos⟩
  · rintro ⟨hcrit, hμ, hpos⟩
    have h := (isCriticalPointM_normSq_sub_iff_mem_normalBundleSet p q).1 hcrit
    exact ⟨h, (nullityM_normSq_sub_eq_endpointNullity hkw p q h).symm.trans hμ, hpos⟩

/-- **Lemma 6.5** (Milnor, p. 36): *`q ∈ M` is a degenerate critical point of `L_p` iff `p` is a
focal point of `(M, q)`*. -/
theorem isDegenerate_normSq_sub_iff_isFocalPoint (p : 𝔼 n) (q : M) :
    letI := hM.chartedSpace
    (IsCriticalPointM (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) q ∧
      ¬ IsNondegenerate (hessianM (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) q)) ↔
      IsFocalPoint hM hkw q p := by
  let := hM.chartedSpace
  rw [isNondegenerate_hessianM_iff_nullityM_eq_zero]
  constructor
  · rintro ⟨hcrit, hnd⟩
    exact ⟨_, (isFocalPointMult_iff hkw p q _).2 ⟨hcrit, rfl, Nat.pos_of_ne_zero hnd⟩⟩
  · rintro ⟨μ, hμ⟩
    obtain ⟨hcrit, hnull, hpos⟩ := (isFocalPointMult_iff hkw p q μ).1 hμ
    exact ⟨hcrit, by omega⟩

end Lemma65

/-! ### Theorem 6.6 -/

section Theorem66

variable {hM}

/-- If `L_p` is not a Morse function on `M`, then `p` is a focal point of `M`. -/
theorem mem_focalSet_of_not_isMorseFunction (hkw : k + w = n) {p : 𝔼 n}
    (hp : letI := hM.chartedSpace; ¬ IsMorseFunction (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2)) :
    p ∈ focalSet hM hkw := by
  let := hM.chartedSpace
  by_contra hfocal
  apply hp
  refine ⟨contMDiff_comp_val hM (contDiff_normSq_sub p), fun q hcrit => ?_⟩
  by_contra hnd
  exact hfocal ⟨q, (isDegenerate_normSq_sub_iff_isFocalPoint hkw p q).1 ⟨hcrit, hnd⟩⟩

/-- **Theorem 6.6** (Milnor, p. 36): *for almost all `p ∈ ℝⁿ` (all but a set of measure `0`) the
function `L_p : M → ℝ`, `L_p(q) = ‖q − p‖²`, has no degenerate critical points*.  Stated for every
Haar measure `μ` on `ℝⁿ`; `M` is any slice submanifold of `ℝⁿ` (no compactness or closedness is
needed). -/
theorem ae_isMorseFunction_normSq_sub (μ : Measure (𝔼 n)) [μ.IsAddHaarMeasure] :
    letI := hM.chartedSpace
    ∀ᵐ p ∂μ, IsMorseFunction (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) := by
  let := hM.chartedSpace
  rcases M.eq_empty_or_nonempty with hempty | hne
  · subst hempty
    refine Eventually.of_forall fun p => ⟨contMDiff_comp_val hM (contDiff_normSq_sub p), ?_⟩
    rintro ⟨q, hq⟩
    exact absurd hq (notMem_empty q)
  · have hkw := slice_dim_add_eq_of_nonempty hM hne
    rw [ae_iff]
    exact measure_mono_null (fun p hp => mem_focalSet_of_not_isMorseFunction hkw hp)
      (measure_focalSet_eq_zero hM hkw μ)

/-- **Theorem 6.6**, with the Lebesgue measure of `ℝⁿ`. -/
theorem ae_volume_isMorseFunction_normSq_sub :
    letI := hM.chartedSpace
    ∀ᵐ p ∂(volume : Measure (𝔼 n)), IsMorseFunction (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) :=
  ae_isMorseFunction_normSq_sub volume

/-- The points `p` for which `L_p` is a Morse function on `M` are dense in `ℝⁿ`: every nonempty
open set contains one (a null set contains no ball; Milnor uses this in the proof of
Corollary 6.8). -/
theorem exists_mem_isMorseFunction_normSq_sub {U : Set (𝔼 n)} (hU : IsOpen U)
    (hne : U.Nonempty) :
    letI := hM.chartedSpace
    ∃ p ∈ U, IsMorseFunction (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) := by
  let := hM.chartedSpace
  have hpos : (volume : Measure (𝔼 n)) U ≠ 0 := (hU.measure_pos volume hne).ne'
  exact Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (ae_restrict_of_ae (ae_volume_isMorseFunction_normSq_sub (hM := hM)))

/-- In particular some `L_p` is a Morse function on `M`. -/
theorem exists_isMorseFunction_normSq_sub :
    letI := hM.chartedSpace
    ∃ p : 𝔼 n, IsMorseFunction (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) := by
  obtain ⟨p, -, hp⟩ := exists_mem_isMorseFunction_normSq_sub (hM := hM) isOpen_univ univ_nonempty
  exact ⟨p, hp⟩

end Theorem66

end Morse
