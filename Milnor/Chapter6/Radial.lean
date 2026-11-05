import Milnor.Chapter6.Compose
import Milnor.Chapter6.Region

/-!
# The sign of a normalized linear map of the sphere

For an invertible linear map `A` of `ℝⁿ⁺¹`, the map `u ↦ A u / |A u|` of the unit sphere has
sign `sgn (det A)` at every point (for the orientation `sphOr`).  This replaces Milnor's Lemma 2
(the isotopy of `A` to the identity or a reflection through `GL⁺`).

The proof: `u ↦ A u / |A u|` is the restriction to the sphere of the ambient map
`Θ x = (|x| / |A x|) A x`, which preserves `sphG = |·|² - 1`; by `signAt_levelOrientM_map` the
sign on the sphere is `sgn det dΘ`, and `dΘ_u = (λ • id + (dλ_u ∘ A⁻¹) ⊗ (A u)) ∘ A` with
`λ = |·| / |A ·|` homogeneous of degree `0`, so `det dΘ_u = λ(u)ⁿ⁺¹ det A` by the matrix
determinant lemma.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

section det

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The matrix determinant lemma for a rank-one perturbation of the identity. -/
theorem det_id_add_smulRight (μ : E →L[ℝ] ℝ) (p : E) :
    LinearMap.det ((ContinuousLinearMap.id ℝ E + μ.smulRight p : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      1 + μ p := by
  classical
  set b := Module.finBasis ℝ E
  rw [← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b ((ContinuousLinearMap.id ℝ E + μ.smulRight p : E →L[ℝ] E) :
      E →ₗ[ℝ] E) = 1 + Matrix.replicateCol Unit (fun i => b.repr p i) *
        Matrix.replicateRow Unit (fun j => μ (b j)) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.smulRight_apply, map_add, map_smul,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply,
      Basis.repr_self, Finsupp.single_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton]
    by_cases h : i = j
    · subst h; simp [mul_comm]
    · simp [h, Ne.symm h, mul_comm]
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  rw [dotProduct]
  conv_rhs => rw [← b.sum_repr p]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem det_smul_id_add_smulRight {c : ℝ} (hc : c ≠ 0) (μ : E →L[ℝ] ℝ) (p : E) (hp : μ p = 0) :
    LinearMap.det ((c • ContinuousLinearMap.id ℝ E + μ.smulRight p : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      c ^ finrank ℝ E := by
  have h1 : (c • ContinuousLinearMap.id ℝ E + μ.smulRight p : E →L[ℝ] E) =
      c • (ContinuousLinearMap.id ℝ E + (c⁻¹ • μ).smulRight p) := by
    ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.smulRight_apply, smul_add, smul_smul,
      smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have h2 : (((c • (ContinuousLinearMap.id ℝ E + (c⁻¹ • μ).smulRight p)) : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      c • ((ContinuousLinearMap.id ℝ E + (c⁻¹ • μ).smulRight p : E →L[ℝ] E) : E →ₗ[ℝ] E) := rfl
  rw [h1, h2, LinearMap.det_smul, det_id_add_smulRight]
  simp [hp]

end det

namespace Sphere

variable {n : ℕ}

/-- The radial factor `λ x = |x| / |A x|`. -/
def lam (A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ := ‖x‖ / ‖A x‖

/-- The ambient map `Θ x = λ x • A x`, preserving `|·|`. -/
def Θ (A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (x : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 1)) := lam A x • A x

variable {A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
  (hA : Bijective A)

include hA in
theorem A_ne_zero {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ≠ 0) : A x ≠ 0 := fun h =>
  hx (hA.1 (by rw [h, map_zero]))

include hA in
theorem lam_pos {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ≠ 0) : 0 < lam A x :=
  div_pos (norm_pos_iff.2 hx) (norm_pos_iff.2 (A_ne_zero hA hx))

include hA in
theorem norm_Θ (x : EuclideanSpace ℝ (Fin (n + 1))) : ‖Θ A x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [Θ, lam, hx]
  · have hAx : ‖A x‖ ≠ 0 := norm_ne_zero_iff.2 (A_ne_zero hA hx)
    rw [Θ, norm_smul, lam, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)), div_mul_cancel₀ _ hAx]

include hA in
theorem sphG_Θ (x : EuclideanSpace ℝ (Fin (n + 1))) : sphG (Θ A x) = sphG x := by
  simp only [sphG, real_inner_self_eq_norm_sq, norm_Θ hA]

include hA in
theorem contDiffAt_lam {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (lam A) x :=
  (contDiffAt_norm ℝ hx).div ((contDiffAt_norm ℝ (A_ne_zero hA hx)).comp x A.contDiff.contDiffAt)
    (norm_ne_zero_iff.2 (A_ne_zero hA hx))

include hA in
theorem contDiffAt_Θ {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (Θ A) x :=
  (contDiffAt_lam hA hx).smul A.contDiff.contDiffAt

include hA in
/-- Euler's identity for the `0`-homogeneous `λ`: `dλ_x (x) = 0`. -/
theorem fderiv_lam_self {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ≠ 0) :
    fderiv ℝ (lam A) x x = 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t • x) x 1 := by
    have := (hasDerivAt_id (1 : ℝ)).smul_const x
    simpa using this
  have h2 : HasFDerivAt (lam A) (fderiv ℝ (lam A) x) ((1 : ℝ) • x) := by
    rw [one_smul]
    exact ((contDiffAt_lam hA hx).differentiableAt (by simp)).hasFDerivAt
  have h3 : HasDerivAt (fun t : ℝ => lam A (t • x)) (fderiv ℝ (lam A) x x) 1 := by
    have := h2.comp_hasDerivAt (1 : ℝ) h1
    exact this
  have h4 : (fun t : ℝ => lam A (t • x)) =ᶠ[𝓝 (1 : ℝ)] fun _ => lam A x := by
    filter_upwards [lt_mem_nhds (zero_lt_one' ℝ)] with t ht
    simp only [lam, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    rw [mul_div_mul_left _ _ ht.ne']
  have h5 : HasDerivAt (fun t : ℝ => lam A (t • x)) 0 1 :=
    (hasDerivAt_const (1 : ℝ) (lam A x)).congr_of_eventuallyEq h4
  exact h3.unique h5

include hA in
theorem hasFDerivAt_Θ {u : EuclideanSpace ℝ (Fin (n + 1))} (hu : u ≠ 0) :
    HasFDerivAt (Θ A) (lam A u • A + (fderiv ℝ (lam A) u).smulRight (A u)) u :=
  ((contDiffAt_lam hA hu).differentiableAt (by simp)).hasFDerivAt.smul A.hasFDerivAt

include hA in
/-- `det dΘ_u = λ(u)ⁿ⁺¹ det A`. -/
theorem det_fderiv_Θ {u : EuclideanSpace ℝ (Fin (n + 1))} (hu : u ≠ 0) :
    LinearMap.det (fderiv ℝ (Θ A) u : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) =
      lam A u ^ (n + 1) * LinearMap.det (A : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) := by
  rw [(hasFDerivAt_Θ hA hu).fderiv]
  set Ae := ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.2 hA.1)
    (LinearMap.range_eq_top.2 hA.2) with hAe
  have hAec : Ae.toContinuousLinearMap = A := ContinuousLinearEquiv.coe_ofBijective _ _ _
  set μ : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
    (fderiv ℝ (lam A) u).comp Ae.symm.toContinuousLinearMap with hμ
  have hsymm : ∀ v, Ae.symm.toContinuousLinearMap (A v) = v := fun v => by
    have : A v = Ae v := by rw [← hAec]; rfl
    rw [this]
    exact Ae.symm_apply_apply v
  have hfac : (lam A u • A + (fderiv ℝ (lam A) u).smulRight (A u)) =
      (lam A u • ContinuousLinearMap.id ℝ _ + μ.smulRight (A u)).comp A := by
    ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_id', id_eq, hμ, hsymm]
  have hμu : μ (A u) = 0 := by
    simp only [hμ, ContinuousLinearMap.comp_apply, hsymm]
    exact fderiv_lam_self hA hu
  have hcoe : (((lam A u • ContinuousLinearMap.id ℝ _ + μ.smulRight (A u)).comp A :
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
      EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) =
      ((lam A u • ContinuousLinearMap.id ℝ _ + μ.smulRight (A u) :
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
        EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))).comp
        (A : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) := rfl
  rw [hfac, hcoe, LinearMap.det_comp,
    det_smul_id_add_smulRight (lam_pos hA hu).ne' μ (A u) hμu, finrank_euclideanSpace_fin]

include hA in
/-- **The sign of `u ↦ A u / |A u|` on the sphere is `sgn (det A)`.** -/
theorem signAt_nv0_linear (u : Sph n) :
    signAt (sphOr n) (sphOr n) (fun u : Sph n => nv0 (A u.1)) u =
      sgn (LinearMap.det (A : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) := by
  have hne : ∀ q : Sph n, q.1 ≠ 0 := fun q h => by
    have := mem_iff_norm.1 q.2
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set a₀ := (finBasisOfFinrankEq ℝ (EuclideanSpace ℝ (Fin (n + 1))) hE).orientation with ha₀
  set oE : Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) (n + 1) :=
    Orient.const a₀ with hoE
  have hsphOr : sphOr n = levelOrientM hE hZ oE contMDiff_sphG isRegularValue_sphG :=
    levelOrient_eq_levelOrientM hE hZ a₀ contMDiff_sphG isRegularValue_sphG
  have hΘG : ∀ x, sphG x = 0 → sphG (Θ A x) = 0 := fun x hx => by rw [sphG_Θ hA]; exact hx
  have hres : (fun q : Sph n => (⟨Θ A q.1, hΘG q.1 q.2⟩ : Sph n)) =
      fun u : Sph n => nv0 (A u.1) := by
    funext q
    apply Subtype.ext
    rw [nv0_val (A_ne_zero hA (hne q))]
    show lam A q.1 • A q.1 = normalize (A q.1)
    rw [lam, mem_iff_norm.1 q.2, one_div, normalize]
  have hΘs : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      (fun q : Sph n => Θ A q.1) := fun q =>
    (contDiffAt_Θ hA (hne q)).contMDiffAt.comp q contMDiff_val.contMDiffAt
  have hdc : (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) sphG (Θ A u.1)).comp
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (Θ A) u.1) =
      (1 : ℝ) • mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) sphG u.1 := by
    rw [one_smul]
    have h1 := HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
      (J := 𝓘(ℝ, ℝ)) (contMDiff_sphG.mdifferentiableAt (by simp) :
        MDifferentiableAt _ _ sphG (Θ A u.1))).comp u.1
      (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
        (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
        ((contDiffAt_Θ hA (hne u)).contMDiffAt.mdifferentiableAt (by simp))))
    have h2 : sphG ∘ Θ A = sphG := funext (sphG_Θ hA)
    rw [h2] at h1
    exact h1.symm
  have hmap := signAt_levelOrientM_map hE hZ oE oE contMDiff_sphG isRegularValue_sphG contMDiff_sphG
    isRegularValue_sphG (Φ := Θ A) hΘG hΘs u
    ((contDiffAt_Θ hA (hne u)).contMDiffAt.mdifferentiableAt (by simp)) ⟨1, one_pos, hdc⟩
  rw [hres] at hmap
  rw [hsphOr, hmap]
  unfold signAt
  rw [Orient.const_or, Orient.const_or, orSign_self_eq_sgn_det hE]
  have hm : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (Θ A) u.1 =
      fderiv ℝ (Θ A) u.1 := mfderiv_eq_fderiv
  rw [hm, det_fderiv_Θ hA (hne u), sgn_mul, sgn_pos (pow_pos (lam_pos hA (hne u)) _), one_mul]

end Sphere

end Milnor
