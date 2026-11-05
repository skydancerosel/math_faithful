import Morse.Chapter1.ManifoldSubmanifold
import Morse.Chapter3.EulerCharAlgebra

/-!
Milnor, *Morse Theory*, §6, Application 2 (p. 36): the index of `grad f` at a critical point of
index `λ` is `(-1)^λ`; used for §5, p. 29, formula (3).  The gradient field of a function on a
submanifold `N ⊆ ℝᴷ⁺¹`.

# The tangential gradient and its index at a non-degenerate critical point

For `F : ℝᴷ⁺¹ → ℝ` and a submanifold `N ⊆ ℝᴷ⁺¹`, the *tangential gradient* of `F` on `N` is the
vector field `v(q) = P_q ∇F(q)`, `P_q` the orthogonal projection of `ℝᴷ⁺¹` onto the tangent space
`T_qN` (`Morse.tangentialGradient`).  It is the gradient of `f = F|N` for the metric induced from
`ℝᴷ⁺¹`: `⟪v(q), t⟫ = df_q(t)` for `t ∈ T_qN` (`Morse.inner_tangentialGradient`).  This file is
the bridge from Milnor's critical points and indices (§2, `Morse/Chapter1/Manifold.lean`) to the
indices of vector fields of the companion project's Poincaré–Hopf theorem
(`Milnor.Tub.poincare_hopf`), in four steps.

1. **Zeros.**  `v(q) = 0` iff `q` is a critical point of `f`
   (`Morse.tangentialGradient_eq_zero_iff`, from
   `Morse.isCriticalPointM_comp_val_iff_starProjection_gradient_eq_zero`).
2. **Smoothness.**  For compact `N` with its nearest-point retraction `r` on the tubular
   neighbourhood `N_ε` (`Milnor.Tub.tubr`), the derivative `dr_q` at `q ∈ N` is the orthogonal
   projection `P_q` (`Morse.dret_eq_starProjection`, from the companion project's
   `Milnor.Tub.range_dret`, `Milnor.Tub.ker_dret`).  Hence `v(q) = ∇(F ∘ r)(q)` on `N`
   (`Morse.tangentialGradient_eq_gradient`), and `v` is the restriction to `N` of the field
   `∇(F ∘ r)`, smooth on the open set `N_ε` (`Morse.contMDiff_tangentialGradient`).  This is the
   form of smoothness required by `Milnor.Tub.poincare_hopf`.
3. **The derivative at a critical point.**  Milnor's Lemma 5 of *Topology from the Differentiable
   Viewpoint* (`Milnor.Tub.dvr_mem_tanN`) makes the derivative of `v` at a zero `q` an endomorphism
   `dv_q` of `T_qN` (`Milnor.Tub.dvT`).  For `v = ∇(F ∘ r)|N`, `⟪dv_q t, s⟫ = d²(F ∘ r)_q(t, s)`
   for `t, s ∈ T_qN` (`Morse.inner_dvT_tangentialGradient`): `dv_q` is the self-adjoint operator of
   the bilinear form `Morse.hessT`, the second derivative of `F ∘ r` restricted to `T_qN`.
4. **The Hessian.**  At a critical point `q` of `f`, `q` is also a critical point of the ambient
   function `F ∘ r` (`Morse.fderiv_comp_tubRet_eq_zero`), so in the slice parametrization `φ` of
   `N` at `q` the Hessian of `f ∘ φ = (F ∘ r) ∘ φ` is `d²(F ∘ r)_q(dφ ·, dφ ·)` — the second-order
   term of the chain rule vanishes.  As `dφ` is an isomorphism onto `T_qN`, the index and the
   non-degeneracy of Milnor's Hessian `f_**` are those of `Morse.hessT`
   (`Morse.index_hessT`, `Morse.isNondegenerate_hessT_iff`).

With `Morse.sgn_det_eq_neg_one_pow_index` (`Morse/Chapter3/EulerCharAlgebra.lean`) and the
companion project's `Milnor.Tub.indexN_eq_sgn_det` this gives the main result:

* `Morse.bijective_dvT_tangentialGradient`: at a non-degenerate critical point `q` of `f = F|N`
  of index `λ`, `dv_q` is invertible with `sgn det dv_q = (-1)^λ`;
* `Morse.indexN_tangentialGradient`: **at a non-degenerate critical point `q` of `f = F|N`, the
  tangential gradient has index `(-1)^λ`, `λ` the index of `f` at `q`.**

## What Milnor leaves implicit

Milnor asserts the result without proof in Application 2 of §6 (p. 36: the index of `grad f` at
a critical point of index `λ` is `(-1)^λ`), and again in *Topology from the Differentiable
Viewpoint* (§6, p. 40).  Three points are not visible in that sentence, and a fourth is used
silently.

* **Which gradient.**  `grad f` depends on a metric on `N`, which Milnor does not specify; here it
  is the metric induced from `ℝᴷ⁺¹`, and the field is `P_q ∇F(q)`.  The field depends on the
  metric; the value `(-1)^λ` does not, at the level of linear algebra
  (`Morse.sgn_det_eq_neg_one_pow_index` holds for every inner product), but only the induced
  metric is treated here.
* **The Hessian of `F|N` is not the restriction of the Hessian of `F`.**  At a critical point of
  `F|N` the ambient gradient `∇F(q)` is normal to `N`, not zero, and the Hessian of `F|N` carries
  a second fundamental form term (see `Morse/Chapter1/ManifoldSubmanifold.lean`).  The device of
  step 4 is to replace `F` by `F ∘ r`, which agrees with `F` on `N` and is *critical* at `q` as a
  function on `ℝᴷ⁺¹`; the Hessian of `F|N` is then the restriction of that of `F ∘ r`.  The same
  device makes the field smooth (step 2): `P_q` is the derivative of `r` at `q`.
* **Which derivative.**  The derivative of `v` at a zero is an endomorphism of `T_qN` only because
  `v` vanishes there (Milnor's Lemma 5 of the companion book); the index is the sign of its
  determinant on `T_qN`, not on `ℝᴷ⁺¹` (`Milnor.Tub.det_fderiv_w₀`).
* **Linear algebra.**  That `sgn det dv_q = (-1)^λ` for the operator `dv_q` of a non-degenerate
  form of index `λ` is the spectral theorem plus Sylvester's law of inertia
  (`Morse/Chapter3/EulerCharAlgebra.lean`); Milnor uses it silently.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

/-! ### The tangential gradient on a submanifold of an inner product space -/

section General

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-- **The tangential gradient** of `F : V → ℝ` on `N`: the orthogonal projection `P_q ∇F(q)` of
the ambient gradient on the tangent space `T_qN`.  It is the gradient of `F|N` for the metric
induced from `V` (`Morse.inner_tangentialGradient`). -/
def tangentialGradient (F : V → ℝ) (q : N) : V :=
  (tangentSubspace hN q).starProjection (gradient F q)

/-- The tangential gradient is tangent to `N`. -/
theorem tangentialGradient_mem (F : V → ℝ) (q : N) :
    tangentialGradient hN F q ∈ tangentSubspace hN q :=
  Submodule.starProjection_apply_mem _ _

/-- **The tangential gradient is the gradient of `F|N`**: `⟪v(q), t⟫ = dF_q(t)` for every tangent
vector `t ∈ T_qN`. -/
theorem inner_tangentialGradient (F : V → ℝ) (q : N) {t : V} (ht : t ∈ tangentSubspace hN q) :
    ⟪tangentialGradient hN F q, t⟫ = fderiv ℝ F q t := by
  rw [tangentialGradient, Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.2 ht, ← Milnor.fderiv_apply_eq_inner_gradient]

/-- **The zeros of the tangential gradient are the critical points of `F|N`.** -/
theorem tangentialGradient_eq_zero_iff {F : V → ℝ} {q : N} (hF : DifferentiableAt ℝ F q) :
    letI := hN.chartedSpace
    tangentialGradient hN F q = 0 ↔ IsCriticalPointM Z (F ∘ Subtype.val) q :=
  (isCriticalPointM_comp_val_iff_starProjection_gradient_eq_zero hN hF).symm

end General

/-! ### Two lemmas of calculus -/

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The derivative of the gradient is the Hessian**: `⟪d(∇f)_x t, s⟫ = d²f_x(t, s)`. -/
theorem inner_fderiv_gradient {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (t s : E) :
    ⟪fderiv ℝ (gradient f) x t, s⟫ = hessian f x t s := by
  have h1 : HasFDerivAt (fderiv ℝ f) (hessian f x) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h2 : HasFDerivAt (gradient f)
      ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (hessian f x)) x :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.hasFDerivAt.comp x h1
  rw [h2.fderiv]
  exact InnerProductSpace.toDual_symm_apply

/-- The gradient of a function smooth at `x` is smooth at `x`. -/
theorem contDiffAt_gradient {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (gradient f) x :=
  (InnerProductSpace.toDual ℝ E).symm.contDiff.contDiffAt.comp x (hf.fderiv_right (by simp))

end Calculus

/-! ### Compact submanifolds of `ℝᴷ⁺¹`: the retraction -/

section Tub

variable {K d m : ℕ} {N : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
    (EuclideanSpace ℝ (Fin (d + 1))) (EuclideanSpace ℝ (Fin m)) N)
  (hNc : IsCompact N) (hne : N.Nonempty)

local notation "𝔼" => EuclideanSpace ℝ (Fin (K + 1))
local notation "𝔻" => EuclideanSpace ℝ (Fin (d + 1))

/-- The nearest-point retraction `r` of the tubular neighbourhood of `N`
(`Milnor.Tub.tubr`), read as a map of the ambient space. -/
def tubRet (x : 𝔼) : 𝔼 := (Milnor.Tub.tubr hN hNc hne x).1

theorem tubRet_of_mem {x : 𝔼} (hx : x ∈ N) : tubRet hN hNc hne x = x :=
  (Milnor.Tub.tubr_spec hN hNc hne).2.2.1 x hx

theorem tubRet_mem (x : 𝔼) : tubRet hN hNc hne x ∈ N := (Milnor.Tub.tubr hN hNc hne x).2

theorem contDiffAt_tubRet {x : 𝔼} (hx : x ∈ Milnor.Tub.Nε hN hNc hne) :
    ContDiffAt ℝ ∞ (tubRet hN hNc hne) x :=
  Milnor.Tub.contDiffAt_tubr hN hNc hne hx

theorem fderiv_tubRet (q : N) : fderiv ℝ (tubRet hN hNc hne) q.1 = Milnor.Tub.dret hN hNc hne q :=
  rfl

/-- **`dr_q` is the orthogonal projection on the tangent space** `T_qN`. -/
theorem dret_eq_starProjection (q : N) :
    Milnor.Tub.dret hN hNc hne q = (Milnor.Tub.tanN hN q).starProjection := by
  refine ContinuousLinearMap.ext fun x => ?_
  symm
  refine Submodule.eq_starProjection_of_mem_orthogonal (Milnor.Tub.dret_mem_tanN hN hNc hne q x) ?_
  rw [← Milnor.Tub.ker_dret hN hNc hne q, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub,
    Milnor.Tub.dret_dret, sub_self]

/-- The ambient function `F ∘ r`, restricted to `N`, is `F|N`. -/
theorem comp_tubRet_comp_val (F : 𝔼 → ℝ) :
    (F ∘ tubRet hN hNc hne) ∘ (Subtype.val : N → 𝔼) = F ∘ Subtype.val := by
  funext q
  simp only [comp_apply, tubRet_of_mem hN hNc hne q.2]

theorem contDiffAt_comp_tubRet {F : 𝔼 → ℝ} (hF : ContDiff ℝ ∞ F) {x : 𝔼}
    (hx : x ∈ Milnor.Tub.Nε hN hNc hne) : ContDiffAt ℝ ∞ (F ∘ tubRet hN hNc hne) x :=
  hF.contDiffAt.comp x (contDiffAt_tubRet hN hNc hne hx)

/-- The derivative of `F ∘ r` at a point of `N` is `dF_q ∘ P_q`. -/
theorem fderiv_comp_tubRet {F : 𝔼 → ℝ} {q : N} (hF : DifferentiableAt ℝ F q.1) :
    fderiv ℝ (F ∘ tubRet hN hNc hne) q.1 =
      (fderiv ℝ F q.1).comp (Milnor.Tub.dret hN hNc hne q) := by
  have hr : HasFDerivAt (tubRet hN hNc hne) (Milnor.Tub.dret hN hNc hne q) q.1 :=
    Milnor.Tub.hasFDerivAt_tubr hN hNc hne (Milnor.Tub.mem_Nε_of_mem hN hNc hne q.2)
  have hF' : HasFDerivAt F (fderiv ℝ F q.1) (tubRet hN hNc hne q.1) := by
    rw [tubRet_of_mem hN hNc hne q.2]
    exact hF.hasFDerivAt
  exact (hF'.comp q.1 hr).fderiv

/-- **The tangential gradient is the gradient of `F ∘ r`** at the points of `N`. -/
theorem tangentialGradient_eq_gradient {F : 𝔼 → ℝ} {q : N} (hF : DifferentiableAt ℝ F q.1) :
    tangentialGradient hN F q = gradient (F ∘ tubRet hN hNc hne) q.1 := by
  refine ext_inner_right ℝ fun w => ?_
  rw [real_inner_comm, ← Milnor.fderiv_apply_eq_inner_gradient, fderiv_comp_tubRet hN hNc hne hF,
    ContinuousLinearMap.comp_apply, dret_eq_starProjection, Milnor.fderiv_apply_eq_inner_gradient,
    ← Submodule.inner_starProjection_left_eq_right, real_inner_comm]
  rfl

/-- **At a critical point of `F|N`, `q` is a critical point of the ambient function `F ∘ r`.** -/
theorem fderiv_comp_tubRet_eq_zero {F : 𝔼 → ℝ} {q : N} (hF : DifferentiableAt ℝ F q.1)
    (hcrit : letI := hN.chartedSpace; IsCriticalPointM 𝔻 (F ∘ Subtype.val) q) :
    fderiv ℝ (F ∘ tubRet hN hNc hne) q.1 = 0 := by
  rw [fderiv_comp_tubRet hN hNc hne hF]
  ext w
  exact (isCriticalPointM_comp_val_iff_forall_tangent hN hF).1 hcrit _
    (Milnor.Tub.dret_mem_tanN hN hNc hne q w)

/-! ### The tangential gradient as a smooth tangent field -/

include hNc hne in
/-- **The tangential gradient is smooth** on `N`, as a map `N → ℝᴷ⁺¹`: it is the restriction of
the field `∇(F ∘ r)`, smooth on the tubular neighbourhood. -/
theorem contMDiff_tangentialGradient {F : 𝔼 → ℝ} (hF : ContDiff ℝ ∞ F) :
    letI := hN.chartedSpace
    ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ (tangentialGradient hN F) := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have heq : tangentialGradient hN F = gradient (F ∘ tubRet hN hNc hne) ∘ Subtype.val :=
    funext fun q => tangentialGradient_eq_gradient hN hNc hne (hF.differentiable (by simp) _)
  rw [heq]
  intro q
  exact (contDiffAt_gradient (contDiffAt_comp_tubRet hN hNc hne hF
    (Milnor.Tub.mem_Nε_of_mem hN hNc hne q.2))).contMDiffAt.comp q (hN.contMDiff_val q)

/-- The tangential gradient is a tangent field in the sense of the companion project. -/
theorem isTangent_tangentialGradient (F : 𝔼 → ℝ) :
    Milnor.Tub.IsTangent hN (tangentialGradient hN F) :=
  tangentialGradient_mem hN F

/-- The tangential gradient is tangent in the form of the hypothesis `_hvT` of
`Milnor.Tub.poincare_hopf`. -/
theorem tangentialGradient_mem_range (F : 𝔼 → ℝ) (q : N) :
    letI := hN.chartedSpace
    tangentialGradient hN F q ∈ LinearMap.range ((Milnor.mfd 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼)
      (Subtype.val : N → 𝔼) q : 𝔻 →L[ℝ] 𝔼) : 𝔻 →ₗ[ℝ] 𝔼) :=
  tangentialGradient_mem hN F q

/-! ### The derivative of the tangential gradient at a critical point -/

/-- **Milnor's `dv_q` for the tangential gradient**: the derivative at `q` of `x ↦ v(r x)` is
`d(∇(F ∘ r))_q ∘ dr_q`. -/
theorem dvr_tangentialGradient {F : 𝔼 → ℝ} (hF : ContDiff ℝ ∞ F) (q : N) :
    Milnor.Tub.dvr hN hNc hne (tangentialGradient hN F) q =
      (fderiv ℝ (gradient (F ∘ tubRet hN hNc hne)) q.1).comp (Milnor.Tub.dret hN hNc hne q) := by
  have heq : (fun x => tangentialGradient hN F (Milnor.Tub.tubr hN hNc hne x)) =
      gradient (F ∘ tubRet hN hNc hne) ∘ tubRet hN hNc hne :=
    funext fun x => tangentialGradient_eq_gradient hN hNc hne (hF.differentiable (by simp) _)
  have hq := Milnor.Tub.mem_Nε_of_mem hN hNc hne q.2
  have hr : HasFDerivAt (tubRet hN hNc hne) (Milnor.Tub.dret hN hNc hne q) q.1 :=
    Milnor.Tub.hasFDerivAt_tubr hN hNc hne hq
  have hg : HasFDerivAt (gradient (F ∘ tubRet hN hNc hne))
      (fderiv ℝ (gradient (F ∘ tubRet hN hNc hne)) q.1) (tubRet hN hNc hne q.1) := by
    rw [tubRet_of_mem hN hNc hne q.2]
    exact ((contDiffAt_gradient (contDiffAt_comp_tubRet hN hNc hne hF hq)).differentiableAt
      (by simp)).hasFDerivAt
  unfold Milnor.Tub.dvr
  rw [heq]
  exact (hg.comp q.1 hr).fderiv

/-- **The Hessian of `F|N` at `q`, as a bilinear form on the tangent space** `T_qN ⊆ ℝᴷ⁺¹`: the
second derivative of `F ∘ r` at `q`, restricted to `T_qN`.  At a critical point it represents
Milnor's `f_**` (`Morse.index_hessT`, `Morse.isNondegenerate_hessT_iff`). -/
def hessT (F : 𝔼 → ℝ) (q : N) :
    Milnor.Tub.tanN hN q →L[ℝ] Milnor.Tub.tanN hN q →L[ℝ] ℝ :=
  (hessian (F ∘ tubRet hN hNc hne) q.1).bilinearComp (Milnor.Tub.tanN hN q).subtypeL
    (Milnor.Tub.tanN hN q).subtypeL

theorem hessT_apply (F : 𝔼 → ℝ) (q : N) (t s : Milnor.Tub.tanN hN q) :
    hessT hN hNc hne F q t s = hessian (F ∘ tubRet hN hNc hne) q.1 t s :=
  rfl

theorem hessT_symm {F : 𝔼 → ℝ} (hF : ContDiff ℝ ∞ F) (q : N) (t s : Milnor.Tub.tanN hN q) :
    hessT hN hNc hne F q t s = hessT hN hNc hne F q s t :=
  hessian_symm ((contDiffAt_comp_tubRet hN hNc hne hF
    (Milnor.Tub.mem_Nε_of_mem hN hNc hne q.2)).of_le (by norm_cast)) _ _

/-- **The derivative of the tangential gradient represents `hessT`**:
`⟪dv_q t, s⟫ = d²(F ∘ r)_q(t, s)` for `t, s ∈ T_qN`, `dv_q` the derivative at `q` of `x ↦ v(r x)`
(Milnor's `dv_q`, `Milnor.Tub.dvr`). -/
theorem hessT_apply_eq_inner_dvr {F : 𝔼 → ℝ} (hF : ContDiff ℝ ∞ F) (q : N)
    (t s : Milnor.Tub.tanN hN q) :
    hessT hN hNc hne F q t s =
      ⟪Milnor.Tub.dvr hN hNc hne (tangentialGradient hN F) q t, (s : 𝔼)⟫ := by
  rw [dvr_tangentialGradient hN hNc hne hF q, ContinuousLinearMap.comp_apply,
    Milnor.Tub.dret_apply_of_mem_tanN hN hNc hne q t.2, inner_fderiv_gradient, hessT_apply]
  exact (contDiffAt_comp_tubRet hN hNc hne hF (Milnor.Tub.mem_Nε_of_mem hN hNc hne q.2)).of_le
    (by norm_cast)

/-- **At a critical point, the derivative of the tangential gradient is the operator of the
Hessian**: `⟪dv_q t, s⟫ = d²(F ∘ r)_q(t, s)` for `t, s ∈ T_qN`, `dv_q` now the endomorphism of
`T_qN` given by Milnor's Lemma 5 (`Milnor.Tub.dvT`). -/
theorem inner_dvT_tangentialGradient {F : 𝔼 → ℝ} (hF : ContDiff ℝ ∞ F) {q : N}
    (hvq : tangentialGradient hN F q = 0) (t s : Milnor.Tub.tanN hN q) :
    hessT hN hNc hne F q t s = ⟪Milnor.Tub.dvT hN hNc hne (tangentialGradient hN F)
      (contMDiff_tangentialGradient hN hNc hne hF) (isTangent_tangentialGradient hN F) q hvq t,
        s⟫ := by
  rw [Submodule.coe_inner, hessT_apply_eq_inner_dvr hN hNc hne hF q]
  rfl

/-! ### The Hessian in the slice parametrization -/

/-- The tangent space at `q` is the range of the derivative of the slice parametrization. -/
theorem tanN_eq_range (q : N) :
    Milnor.Tub.tanN hN q = LinearMap.range
      ((fderiv ℝ (Milnor.Tub.φ hN q) (Milnor.Tub.z₀ hN q) : 𝔻 →L[ℝ] 𝔼) : 𝔻 →ₗ[ℝ] 𝔼) :=
  Milnor.Tub.range_mfd_val hN q q (Milnor.Tub.mem_source hN q)

/-- The derivative of the slice parametrization at `q`, as an isomorphism `ℝⁿ ≅ T_qN`. -/
def tanEquiv (q : N) : 𝔻 ≃L[ℝ] Milnor.Tub.tanN hN q :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofBijective
      (LinearMap.codRestrict (Milnor.Tub.tanN hN q)
        ((fderiv ℝ (Milnor.Tub.φ hN q) (Milnor.Tub.z₀ hN q) : 𝔻 →L[ℝ] 𝔼) : 𝔻 →ₗ[ℝ] 𝔼)
        fun a => by
          rw [tanN_eq_range]
          exact ⟨a, rfl⟩)
      ⟨fun a b hab => Milnor.Tub.injective_fderiv_φ hN q (Milnor.Tub.z₀_mem hN q)
          (congrArg Subtype.val hab),
        fun t => by
          obtain ⟨a, ha⟩ : (t : 𝔼) ∈ LinearMap.range
              ((fderiv ℝ (Milnor.Tub.φ hN q) (Milnor.Tub.z₀ hN q) : 𝔻 →L[ℝ] 𝔼) : 𝔻 →ₗ[ℝ] 𝔼) := by
            exact (tanN_eq_range hN q).le t.2
          exact ⟨a, Subtype.ext ha⟩⟩)

theorem tanEquiv_apply (q : N) (a : 𝔻) :
    (tanEquiv hN q a : 𝔼) = fderiv ℝ (Milnor.Tub.φ hN q) (Milnor.Tub.z₀ hN q) a :=
  rfl

/-- **At a critical point, the Hessian of `F|N` in the slice parametrization is `hessT` pulled back
by `dφ`**: the second-order term of the chain rule vanishes because `q` is a critical point of the
ambient function `F ∘ r`. -/
theorem hessian_comp_φ_eq {F : 𝔼 → ℝ} (hF : ContDiff ℝ ∞ F) {q : N}
    (hcrit : letI := hN.chartedSpace; IsCriticalPointM 𝔻 (F ∘ Subtype.val) q) :
    hessian (F ∘ Milnor.Tub.φ hN q) (Milnor.Tub.z₀ hN q) =
      (hessT hN hNc hne F q).bilinearComp (tanEquiv hN q : 𝔻 →L[ℝ] Milnor.Tub.tanN hN q)
        (tanEquiv hN q : 𝔻 →L[ℝ] Milnor.Tub.tanN hN q) := by
  have hz := Milnor.Tub.z₀_mem hN q
  have hφz : Milnor.Tub.φ hN q (Milnor.Tub.z₀ hN q) = q.1 := Milnor.Tub.φ_z₀ hN q
  have hev : F ∘ Milnor.Tub.φ hN q =ᶠ[𝓝 (Milnor.Tub.z₀ hN q)]
      (F ∘ tubRet hN hNc hne) ∘ Milnor.Tub.φ hN q := by
    filter_upwards [(Milnor.Tub.isOpen_Ω hN q).mem_nhds hz] with z hz'
    simp only [comp_apply, tubRet_of_mem hN hNc hne (Milnor.Tub.φ_mem hN q hz')]
  have hFr : ContDiffAt ℝ 2 (F ∘ tubRet hN hNc hne) (Milnor.Tub.φ hN q (Milnor.Tub.z₀ hN q)) := by
    rw [hφz]
    exact (contDiffAt_comp_tubRet hN hNc hne hF (Milnor.Tub.mem_Nε_of_mem hN hNc hne q.2)).of_le
      (by norm_cast)
  have hφ : ContDiffAt ℝ 2 (Milnor.Tub.φ hN q) (Milnor.Tub.z₀ hN q) :=
    ((Milnor.Tub.contDiffOn_φ hN q).contDiffAt ((Milnor.Tub.isOpen_Ω hN q).mem_nhds hz)).of_le
      (by norm_cast)
  have hcrit' : fderiv ℝ (F ∘ tubRet hN hNc hne) (Milnor.Tub.φ hN q (Milnor.Tub.z₀ hN q)) = 0 := by
    rw [hφz]
    exact fderiv_comp_tubRet_eq_zero hN hNc hne (hF.differentiable (by simp) _) hcrit
  ext a b
  rw [hessian_congr hev, hessian_comp hFr hφ hcrit', hφz]
  rfl

/-- **The index of `F|N` at a critical point is the index of `hessT`.** -/
theorem index_hessT {F : 𝔼 → ℝ} (hF : ContDiff ℝ ∞ F) {q : N}
    (hcrit : letI := hN.chartedSpace; IsCriticalPointM 𝔻 (F ∘ Subtype.val) q) :
    letI := hN.chartedSpace
    index (hessT hN hNc hne F q) = indexM 𝔻 (F ∘ Subtype.val) q := by
  let _ := hN.chartedSpace
  rw [indexM_comp_val_eq_tub hN (hF.contDiffAt.of_le (by norm_cast)) hcrit,
    hessian_comp_φ_eq hN hNc hne hF hcrit, index_bilinearComp]

/-- **A critical point of `F|N` is non-degenerate iff `hessT` is non-degenerate.** -/
theorem isNondegenerate_hessT_iff {F : 𝔼 → ℝ} (hF : ContDiff ℝ ∞ F) {q : N}
    (hcrit : letI := hN.chartedSpace; IsCriticalPointM 𝔻 (F ∘ Subtype.val) q) :
    letI := hN.chartedSpace
    IsNondegenerate (hessT hN hNc hne F q) ↔ IsNondegenerate (hessianM 𝔻 (F ∘ Subtype.val) q) := by
  let _ := hN.chartedSpace
  rw [← isNondegenerate_hessian_comp_sliceParam_iff hN (Milnor.Tub.σ hN q)
    (Milnor.Tub.mem_source hN q) (hF.contDiffAt.of_le (by norm_cast)) hcrit]
  change _ ↔ IsNondegenerate (hessian (F ∘ Milnor.Tub.φ hN q) (Milnor.Tub.z₀ hN q))
  rw [hessian_comp_φ_eq hN hNc hne hF hcrit, isNondegenerate_bilinearComp_iff]

/-! ### The index of the tangential gradient -/

/-- **At a non-degenerate critical point the derivative of the tangential gradient is invertible,
with `sgn det dv_q = (-1)^λ`**, `λ` the index of `F|N` at `q`: `dv_q` is the self-adjoint operator
of `hessT`, whose index and non-degeneracy are those of Milnor's Hessian `f_**`. -/
theorem bijective_dvT_tangentialGradient {F : 𝔼 → ℝ} (hF : ContDiff ℝ ∞ F) {q : N}
    (hvq : tangentialGradient hN F q = 0)
    (hnd : letI := hN.chartedSpace; IsNondegenerate (hessianM 𝔻 (F ∘ Subtype.val) q)) :
    letI := hN.chartedSpace
    Bijective (Milnor.Tub.dvT hN hNc hne (tangentialGradient hN F)
        (contMDiff_tangentialGradient hN hNc hne hF) (isTangent_tangentialGradient hN F) q hvq) ∧
      Milnor.sgn (LinearMap.det (Milnor.Tub.dvT hN hNc hne (tangentialGradient hN F)
        (contMDiff_tangentialGradient hN hNc hne hF) (isTangent_tangentialGradient hN F) q hvq)) =
        (-1) ^ indexM 𝔻 (F ∘ Subtype.val) q := by
  let _ := hN.chartedSpace
  have hcrit : IsCriticalPointM 𝔻 (F ∘ Subtype.val) q :=
    (tangentialGradient_eq_zero_iff hN (hF.differentiable (by simp) _)).1 hvq
  have hH := inner_dvT_tangentialGradient hN hNc hne hF hvq
  have hnd' : IsNondegenerate (hessT hN hNc hne F q) :=
    (isNondegenerate_hessT_iff hN hNc hne hF hcrit).2 hnd
  refine ⟨(isNondegenerate_iff_bijective hH).1 hnd', ?_⟩
  rw [sgn_det_eq_neg_one_pow_index_of_symm hH (hessT_symm hN hNc hne hF q) hnd',
    index_hessT hN hNc hne hF hcrit]

/-- **The index of the gradient field at a non-degenerate critical point** (Milnor, §6,
Application 2, p. 36; *Topology from the Differentiable Viewpoint*, p. 40): if `q` is a
non-degenerate critical point of index `λ` of `F|N`, then the tangential gradient of `F` has index
`(-1)^λ` at `q`. -/
theorem indexN_tangentialGradient (hK : 0 < K) {F : 𝔼 → ℝ} (hF : ContDiff ℝ ∞ F) {q : N}
    (hq : letI := hN.chartedSpace; IsNondegenerateCriticalPointM 𝔻 (F ∘ Subtype.val) q) :
    letI := hN.chartedSpace
    Milnor.Tub.indexN hN hNc hne (tangentialGradient hN F)
      (contMDiff_tangentialGradient hN hNc hne hF) q = (-1) ^ indexM 𝔻 (F ∘ Subtype.val) q := by
  let _ := hN.chartedSpace
  have hvq : tangentialGradient hN F q = 0 :=
    (tangentialGradient_eq_zero_iff hN (hF.differentiable (by simp) _)).2 hq.1
  obtain ⟨hbij, hsgn⟩ := bijective_dvT_tangentialGradient hN hNc hne hF hvq hq.2
  rw [Milnor.Tub.indexN_eq_sgn_det hN hNc hne hK (contMDiff_tangentialGradient hN hNc hne hF)
    (isTangent_tangentialGradient hN F) hvq hbij, hsgn]

end Tub

end Morse
