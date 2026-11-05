import Milnor.Chapter7.Lemma1
import Milnor.Chapter6.Radial

/-!
# Smooth families of rotations of the sphere

For an orthonormal pair `u, v` in `ℝᵖ⁺¹` and an angle `θ`, `rotCLM u v θ` is the rotation by `θ`
in the plane spanned by `u, v` (the identity on the orthogonal complement):

  `x ↦ x + (cos θ - 1) • (⟪u,x⟫ • u + ⟪v,x⟫ • v) + sin θ • (⟪u,x⟫ • v - ⟪v,x⟫ • u)`.

It is a one-parameter group of isometries with positive determinant, depends smoothly on
`(x, θ)`, and induces an orientation-preserving diffeomorphism `rotS u v θ` of the sphere `Sᵖ`.

The main result `exists_rotation_path`: for `p ≥ 1` and `y, y' ∈ Sᵖ` there are an orthonormal
pair `u, v` and an angle `θ₀ ∈ [0, π]` with `rotCLM u v θ₀ y = y'`, such that along the path
`t ↦ rotCLM u v (t θ₀) y` (`t ∈ [0,1]`) the distance to `y` never exceeds `dist y' y`.
-/

open Set Filter Topology Function Module Metric Real
open scoped ContDiff Manifold RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace Milnor

open Sphere

namespace Sphere

variable {p : ℕ}

/-! ### The planar rotation as a continuous linear map -/

/-- Rotation by the angle `θ` in the plane spanned by the orthonormal pair `u, v`, as a
continuous linear map of `ℝᵖ⁺¹`. -/
def rotCLM (u v : EuclideanSpace ℝ (Fin (p + 1))) (θ : ℝ) :
    EuclideanSpace ℝ (Fin (p + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (p + 1)) :=
  ContinuousLinearMap.id ℝ _ +
    (cos θ - 1) • ((innerSL ℝ u).smulRight u + (innerSL ℝ v).smulRight v) +
    sin θ • ((innerSL ℝ u).smulRight v - (innerSL ℝ v).smulRight u)

theorem rotCLM_apply (u v : EuclideanSpace ℝ (Fin (p + 1))) (θ : ℝ)
    (x : EuclideanSpace ℝ (Fin (p + 1))) :
    rotCLM u v θ x = x + (cos θ - 1) • (⟪u, x⟫ • u + ⟪v, x⟫ • v) +
      sin θ • (⟪u, x⟫ • v - ⟪v, x⟫ • u) := by
  simp only [rotCLM, add_apply, smul_apply, ContinuousLinearMap.coe_id', id_eq, sub_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

/-- The rotation, written as `x + α • u + β • v`. -/
theorem rotCLM_apply' (u v : EuclideanSpace ℝ (Fin (p + 1))) (θ : ℝ)
    (x : EuclideanSpace ℝ (Fin (p + 1))) :
    rotCLM u v θ x = x + (⟪u, x⟫ * (cos θ - 1) - ⟪v, x⟫ * sin θ) • u +
      (⟪u, x⟫ * sin θ + ⟪v, x⟫ * (cos θ - 1)) • v := by
  rw [rotCLM_apply]
  module

/-- `θ ↦ rotCLM u v θ` is smooth as a map into the space of continuous linear maps. -/
theorem contDiff_rotCLM_clm (u v : EuclideanSpace ℝ (Fin (p + 1))) :
    ContDiff ℝ ∞ (fun θ : ℝ => rotCLM u v θ) := by
  unfold rotCLM
  exact (contDiff_const.add ((Real.contDiff_cos.sub contDiff_const).smul contDiff_const)).add
    (Real.contDiff_sin.smul contDiff_const)

/-- Joint smoothness of `(x, θ) ↦ rotCLM u v θ x`. -/
theorem contDiff_rotCLM (u v : EuclideanSpace ℝ (Fin (p + 1))) :
    ContDiff ℝ ∞ (fun q : EuclideanSpace ℝ (Fin (p + 1)) × ℝ => rotCLM u v q.2 q.1) :=
  ((contDiff_rotCLM_clm u v).comp contDiff_snd).clm_apply contDiff_fst

section orthonormal

variable {u v : EuclideanSpace ℝ (Fin (p + 1))} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0)

include hu in
theorem inner_self_of_norm_one : ⟪u, u⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, hu, one_pow]

include hu hv huv in
theorem inner_rotCLM_u (θ : ℝ) (x : EuclideanSpace ℝ (Fin (p + 1))) :
    ⟪u, rotCLM u v θ x⟫ = cos θ * ⟪u, x⟫ - sin θ * ⟪v, x⟫ := by
  rw [rotCLM_apply']
  simp only [inner_add_right, real_inner_smul_right, inner_self_of_norm_one hu, huv]
  ring

include hu hv huv in
theorem inner_rotCLM_v (θ : ℝ) (x : EuclideanSpace ℝ (Fin (p + 1))) :
    ⟪v, rotCLM u v θ x⟫ = sin θ * ⟪u, x⟫ + cos θ * ⟪v, x⟫ := by
  have hvu : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
  rw [rotCLM_apply']
  simp only [inner_add_right, real_inner_smul_right, inner_self_of_norm_one hv, hvu]
  ring

theorem rotCLM_zero (u v : EuclideanSpace ℝ (Fin (p + 1))) :
    rotCLM u v 0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (p + 1))) := by
  ext x
  simp [rotCLM_apply]

include hu hv huv in
/-- The one-parameter group law. -/
theorem rotCLM_add (θ₁ θ₂ : ℝ) :
    rotCLM u v (θ₁ + θ₂) = (rotCLM u v θ₁).comp (rotCLM u v θ₂) := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.comp_apply, rotCLM_apply' u v θ₁ (rotCLM u v θ₂ x),
    inner_rotCLM_u hu hv huv, inner_rotCLM_v hu hv huv, rotCLM_apply' u v θ₂ x,
    rotCLM_apply' u v (θ₁ + θ₂) x, cos_add, sin_add]
  module

include hu hv huv in
theorem rotCLM_neg_comp (θ : ℝ) :
    (rotCLM u v (-θ)).comp (rotCLM u v θ) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (p + 1))) := by
  rw [← rotCLM_add hu hv huv, neg_add_cancel, rotCLM_zero]

include hu hv huv in
theorem rotCLM_comp_neg (θ : ℝ) :
    (rotCLM u v θ).comp (rotCLM u v (-θ)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (p + 1))) := by
  rw [← rotCLM_add hu hv huv, add_neg_cancel, rotCLM_zero]

include hu hv huv in
theorem rotCLM_neg_rotCLM (θ : ℝ) (x : EuclideanSpace ℝ (Fin (p + 1))) :
    rotCLM u v (-θ) (rotCLM u v θ x) = x := by
  rw [← ContinuousLinearMap.comp_apply, rotCLM_neg_comp hu hv huv]; rfl

include hu hv huv in
theorem rotCLM_rotCLM_neg (θ : ℝ) (x : EuclideanSpace ℝ (Fin (p + 1))) :
    rotCLM u v θ (rotCLM u v (-θ) x) = x := by
  rw [← ContinuousLinearMap.comp_apply, rotCLM_comp_neg hu hv huv]; rfl

include hu hv huv in
theorem rotCLM_bijective (θ : ℝ) : Bijective (rotCLM u v θ) :=
  ⟨fun x y h => by
    have := congrArg (rotCLM u v (-θ)) h
    rwa [rotCLM_neg_rotCLM hu hv huv, rotCLM_neg_rotCLM hu hv huv] at this,
  fun y => ⟨rotCLM u v (-θ) y, rotCLM_rotCLM_neg hu hv huv θ y⟩⟩

include hu hv huv in
/-- The rotation is an isometry. -/
theorem norm_rotCLM (θ : ℝ) (x : EuclideanSpace ℝ (Fin (p + 1))) :
    ‖rotCLM u v θ x‖ = ‖x‖ := by
  have hvu : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
  have hxu : ⟪x, u⟫ = ⟪u, x⟫ := real_inner_comm u x
  have hxv : ⟪x, v⟫ = ⟪v, x⟫ := real_inner_comm v x
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, rotCLM_apply']
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_self_of_norm_one hu, inner_self_of_norm_one hv, huv, hvu, hxu, hxv]
  linear_combination (⟪u, x⟫ ^ 2 + ⟪v, x⟫ ^ 2) * (sin_sq_add_cos_sq θ)

include hu hv huv in
theorem rotCLM_mem (θ : ℝ) {x : EuclideanSpace ℝ (Fin (p + 1))} (hx : x ∈ Sph p) :
    rotCLM u v θ x ∈ Sph p := by
  rw [mem_iff_norm] at hx ⊢
  rw [norm_rotCLM hu hv huv, hx]

include hu hv huv in
theorem rotCLM_apply_u (θ : ℝ) : rotCLM u v θ u = cos θ • u + sin θ • v := by
  have hvu : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
  rw [rotCLM_apply', inner_self_of_norm_one hu, hvu]
  module

include hu hv huv in
/-- The chord from `u` to its rotation: `‖R_θ u - u‖² = 2 - 2 cos θ`. -/
theorem dist_rotCLM_u_sq (θ : ℝ) : dist (rotCLM u v θ u) u ^ 2 = 2 - 2 * cos θ := by
  have hvu : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
  rw [dist_eq_norm, rotCLM_apply_u hu hv huv, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, inner_self_of_norm_one hu,
    inner_self_of_norm_one hv, huv, hvu]
  linear_combination (sin_sq_add_cos_sq θ)

include hu hv huv in
/-- On `[0, π]` the chord from `u` grows with the angle. -/
theorem dist_rotCLM_u {θ θ₀ : ℝ} (h0 : 0 ≤ θ) (hθ : θ ≤ θ₀) (hπ : θ₀ ≤ π) :
    dist (rotCLM u v θ u) u ≤ dist (rotCLM u v θ₀ u) u := by
  refine (pow_le_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero).1 ?_
  rw [dist_rotCLM_u_sq hu hv huv, dist_rotCLM_u_sq hu hv huv]
  have := cos_le_cos_of_nonneg_of_le_pi h0 hπ hθ
  linarith

include hu hv huv in
/-- The rotation has positive determinant. -/
theorem det_rotCLM_pos (θ : ℝ) :
    0 < LinearMap.det (rotCLM u v θ : EuclideanSpace ℝ (Fin (p + 1)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (p + 1))) := by
  set D : ℝ → ℝ := fun t => LinearMap.det (rotCLM u v t : EuclideanSpace ℝ (Fin (p + 1)) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin (p + 1))) with hD
  have hcont : Continuous D :=
    ContinuousLinearMap.continuous_det.comp (contDiff_rotCLM_clm u v).continuous
  have hD0 : D 0 = 1 := by
    simp only [hD, rotCLM_zero, ContinuousLinearMap.coe_id, LinearMap.det_id]
  have hne : ∀ t, D t ≠ 0 := fun t h => by
    have h1 : D (-t) * D t = 1 := by
      simp only [hD]
      rw [← LinearMap.det_comp, ← ContinuousLinearMap.toLinearMap_comp, rotCLM_neg_comp hu hv huv,
        ContinuousLinearMap.coe_id, LinearMap.det_id]
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  by_contra hle
  push Not at hle
  have hlt : D θ < 0 := lt_of_le_of_ne hle (hne θ)
  have hIVT := isPreconnected_univ.intermediate_value (mem_univ θ) (mem_univ 0)
    hcont.continuousOn
  obtain ⟨t, -, ht⟩ := hIVT ⟨hlt.le, by rw [hD0]; exact zero_le_one⟩
  exact hne t ht

/-! ### The induced map of the sphere -/

end orthonormal

/-- The rotation of the sphere induced by `rotCLM u v θ` (normalized into the sphere via `nv0`,
so that the definition needs no hypotheses on `u, v`; for orthonormal `u, v` it is
`x ↦ rotCLM u v θ x`, see `rotS_val`). -/
def rotS (u v : EuclideanSpace ℝ (Fin (p + 1))) (θ : ℝ) (x : Sph p) : Sph p :=
  nv0 (rotCLM u v θ x.1)

section orthonormal

variable {u v : EuclideanSpace ℝ (Fin (p + 1))} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0)

include hu hv huv in
theorem rotS_val (θ : ℝ) (x : Sph p) : (rotS u v θ x).1 = rotCLM u v θ x.1 := by
  have h1 : ‖rotCLM u v θ x.1‖ = 1 := by rw [norm_rotCLM hu hv huv]; exact mem_iff_norm.1 x.2
  have hne : rotCLM u v θ x.1 ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact zero_ne_one h1
  rw [rotS, nv0_val hne, normalize, h1, inv_one, one_smul]

include hu hv huv in
theorem rotS_neg_rotS (θ : ℝ) (x : Sph p) : rotS u v (-θ) (rotS u v θ x) = x := by
  apply Subtype.ext
  rw [rotS_val hu hv huv, rotS_val hu hv huv, rotCLM_neg_rotCLM hu hv huv]

include hu hv huv in
theorem rotS_rotS_neg (θ : ℝ) (x : Sph p) : rotS u v θ (rotS u v (-θ) x) = x := by
  apply Subtype.ext
  rw [rotS_val hu hv huv, rotS_val hu hv huv, rotCLM_rotCLM_neg hu hv huv]

include hu hv huv in
theorem rotS_zero (x : Sph p) : rotS u v 0 x = x := by
  apply Subtype.ext
  rw [rotS_val hu hv huv, rotCLM_zero]; rfl

include hu hv huv in
/-- Smoothness of the family `(x, t) ↦ rotS u v (ρ t) x` on `Sᵖ × ℝ`. -/
theorem contMDiff_rotS_family {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun q : Sph p × ℝ => rotS u v (ρ q.2) q.1) := by
  set F : Sph p × ℝ → EuclideanSpace ℝ (Fin (p + 1)) :=
    fun q => rotCLM u v (ρ q.2) q.1.1 with hF
  have hFS : ∀ q, F q ∈ Sph p := fun q => rotCLM_mem hu hv huv _ q.1.2
  have hFsmooth : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) ∞ F :=
    ContMDiff.clm_apply ((contDiff_rotCLM_clm u v).contMDiff.comp (hρ.contMDiff.comp contMDiff_snd))
      (contMDiff_val.comp contMDiff_fst)
  have heq : (fun q : Sph p × ℝ => rotS u v (ρ q.2) q.1) = fun q => ⟨F q, hFS q⟩ := by
    funext q; exact Subtype.ext (rotS_val hu hv huv _ _)
  rw [heq]
  exact (sphS p).contMDiff_codRestrict hFsmooth hFS

include hu hv huv in
theorem contMDiff_rotS (θ : ℝ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (rotS u v θ) := by
  have := contMDiff_rotS_family hu hv huv (ρ := fun _ => θ) contDiff_const
  have h2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, ℝ)) ∞ (fun x : Sph p => (x, (0 : ℝ))) :=
    contMDiff_id.prodMk contMDiff_const
  exact this.comp h2

include hu hv huv in
/-- The rotation of the sphere preserves the orientation `sphOr p`. -/
theorem signAt_rotS (θ : ℝ) (x : Sph p) : signAt (sphOr p) (sphOr p) (rotS u v θ) x = 1 :=
  (signAt_nv0_linear (rotCLM_bijective hu hv huv θ) x).trans
    (sgn_pos (det_rotCLM_pos hu hv huv θ))

include hu hv huv in
theorem mfd_rotS_bijective (θ : ℝ) (x : Sph p) :
    Bijective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (rotS u v θ) x) :=
  (signAt_ne_zero_iff hZ hZ (sphOr p) (sphOr p) (rotS u v θ) x).1
    (by rw [signAt_rotS hu hv huv]; exact one_ne_zero)

end orthonormal

/-! ### Existence of a rotation path between two points of the sphere -/

/-- For `p ≥ 1`, every unit vector has a unit vector orthogonal to it. -/
theorem exists_unit_orthogonal (hp : 1 ≤ p) {u : EuclideanSpace ℝ (Fin (p + 1))}
    (hu : ‖u‖ = 1) : ∃ v : EuclideanSpace ℝ (Fin (p + 1)), ‖v‖ = 1 ∧ ⟪u, v⟫ = 0 := by
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (p + 1))) = p + 1) := ⟨hE⟩
  have hu0 : u ≠ 0 := fun h => by rw [h, norm_zero] at hu; exact zero_ne_one hu
  have hfr : finrank ℝ (ℝ ∙ u)ᗮ = p := Submodule.finrank_orthogonal_span_singleton hu0
  have hbot : (ℝ ∙ u)ᗮ ≠ ⊥ := fun h => by
    have := Submodule.finrank_eq_zero.2 h
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0)]
  · rw [real_inner_smul_right, Submodule.mem_orthogonal_singleton_iff_inner_right.1 hw, mul_zero]

/-- **Rotation paths on the sphere.** For `p ≥ 1` and `y, y' ∈ Sᵖ` there is an orthonormal pair
`u, v` and an angle `θ₀ ∈ [0, π]` with `rotCLM u v θ₀ y = y'`, and along the path
`t ↦ rotCLM u v (t θ₀) y`, `t ∈ [0, 1]`, the distance to `y` is at most `dist y' y`. -/
theorem exists_rotation_path (hp : 1 ≤ p) (y y' : Sph p) :
    ∃ u v : EuclideanSpace ℝ (Fin (p + 1)), ∃ θ₀ : ℝ,
      ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ⟪u, v⟫ = 0 ∧ 0 ≤ θ₀ ∧ θ₀ ≤ π ∧
      rotCLM u v θ₀ y.1 = y'.1 ∧
      ∀ t, 0 ≤ t → t ≤ 1 → dist (rotCLM u v (t * θ₀) y.1) y.1 ≤ dist y'.1 y.1 := by
  have hy : ‖y.1‖ = 1 := mem_iff_norm.1 y.2
  have hy' : ‖y'.1‖ = 1 := mem_iff_norm.1 y'.2
  set a : ℝ := ⟪y.1, y'.1⟫ with ha
  have ha1 : |a| ≤ 1 := by
    have := abs_real_inner_le_norm y.1 y'.1
    rwa [hy, hy', one_mul] at this
  obtain ⟨ha_lo, ha_hi⟩ := abs_le.1 ha1
  set w : EuclideanSpace ℝ (Fin (p + 1)) := y'.1 - a • y.1 with hw
  have hyw : ⟪y.1, w⟫ = 0 := by
    rw [hw, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hy]; ring
  have hwsq : ‖w‖ ^ 2 = 1 - a ^ 2 := by
    rw [hw, norm_sub_sq_real, real_inner_smul_right, real_inner_comm, ← ha, norm_smul, hy, hy',
      Real.norm_eq_abs, mul_one, sq_abs]
    ring
  -- a unit vector `v ⊥ y` with `‖w‖ • v = w`
  obtain ⟨v, hv, hyv, hwv⟩ : ∃ v : EuclideanSpace ℝ (Fin (p + 1)),
      ‖v‖ = 1 ∧ ⟪y.1, v⟫ = 0 ∧ ‖w‖ • v = w := by
    by_cases hw0 : w = 0
    · obtain ⟨v, hv, hyv⟩ := exists_unit_orthogonal hp hy
      exact ⟨v, hv, hyv, by rw [hw0, norm_zero, zero_smul]⟩
    · have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
      refine ⟨‖w‖⁻¹ • w, ?_, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwn]
      · rw [real_inner_smul_right, hyw, mul_zero]
      · rw [smul_smul, mul_inv_cancel₀ hwn, one_smul]
  set θ₀ := arccos a with hθ₀
  have hcos : cos θ₀ = a := cos_arccos ha_lo ha_hi
  have hsin : sin θ₀ = ‖w‖ := by
    rw [hθ₀, sin_arccos, ← hwsq, Real.sqrt_sq (norm_nonneg _)]
  have hrot : rotCLM y.1 v θ₀ y.1 = y'.1 := by
    rw [rotCLM_apply_u hy hv hyv, hcos, hsin, hwv, hw]
    abel
  refine ⟨y.1, v, θ₀, hy, hv, hyv, arccos_nonneg a, arccos_le_pi a, hrot, ?_⟩
  intro t ht0 ht1
  rw [← hrot]
  exact dist_rotCLM_u hy hv hyv (mul_nonneg ht0 (arccos_nonneg a))
    (by nlinarith [arccos_nonneg a]) (arccos_le_pi a)

end Sphere

end Milnor
