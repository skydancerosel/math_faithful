import Milnor.Chapter7.Rotation

/-!
# The standard collapse map `π : ℝᵖ → Sᵖ`

The map `ℝᵖ → Sᵖ` which sends `0` to the north pole `north`, the complement of the ball of
radius `1/2` to the south pole `south`, and which near `0` is the (inverse) stereographic-type
map `t ↦ (t, 1)/|(t, 1)|`.  It is smooth, `north` is a regular value with the single preimage
`0`, and the derivative at `0` is bijective.  This is the map used to define the Pontryagin
manifold of a framed submanifold (Milnor, Chapter 7).

Concretely `stdMap t = nv0 (stdW t)` with
`stdW t = ψ(|t|²) • ι t + (2 ψ(|t|²) - 1) • northV`, where `ι : ℝᵖ → ℝᵖ⁺¹` is the inclusion as
the equator plane, `northV = e_{p}` and `ψ` is a smooth cutoff equal to `1` on `(-∞, 1/16]` and
to `0` on `[1/4, ∞)`.
-/

open Set Filter Topology Function Module Metric Real
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Sphere

variable {p : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (p + 1))
local notation "E'" => EuclideanSpace ℝ (Fin p)

/-! ### The poles and the inclusion of the equator plane -/

/-- The north pole vector `e_p ∈ ℝᵖ⁺¹`. -/
def northV : E := EuclideanSpace.single (Fin.last p) 1

theorem norm_northV : ‖(northV : E)‖ = 1 := by simp [northV]

theorem northV_ne_zero : (northV : E) ≠ 0 := by
  intro h; have := norm_northV (p := p); rw [h, norm_zero] at this; exact zero_ne_one this

/-- The north pole of `Sᵖ`. -/
def north : Sph p := ⟨northV, by rw [mem_iff_norm]; exact norm_northV⟩

/-- The south pole of `Sᵖ`. -/
def south : Sph p := ⟨-northV, by rw [mem_iff_norm, norm_neg]; exact norm_northV⟩

theorem north_val : (north : Sph p).1 = northV := rfl
theorem south_val : (south : Sph p).1 = -northV := rfl

/-- The inclusion `ℝᵖ → ℝᵖ⁺¹`, `t ↦ (t, 0)`, as a linear map. -/
def ιₗ : E' →ₗ[ℝ] E where
  toFun t := WithLp.toLp 2 (Fin.snoc (WithLp.ofLp t) (0 : ℝ))
  map_add' t s := by
    ext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [Fin.snoc_last]
    · simp [Fin.snoc_castSucc]
  map_smul' c t := by
    ext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [Fin.snoc_last]
    · simp [Fin.snoc_castSucc]

/-- The inclusion `ℝᵖ → ℝᵖ⁺¹`, `t ↦ (t, 0)`, as a continuous linear map. -/
def ι : E' →L[ℝ] E := LinearMap.toContinuousLinearMap ιₗ

theorem ι_apply_castSucc (t : E') (i : Fin p) : ι t (Fin.castSucc i) = t i := by
  show (WithLp.toLp 2 (Fin.snoc (WithLp.ofLp t) (0 : ℝ)) : E) (Fin.castSucc i) = t i
  simp [Fin.snoc_castSucc]

theorem ι_apply_last (t : E') : ι t (Fin.last p) = 0 := by
  show (WithLp.toLp 2 (Fin.snoc (WithLp.ofLp t) (0 : ℝ)) : E) (Fin.last p) = 0
  simp [Fin.snoc_last]

theorem inner_ι_northV (t : E') : ⟪ι t, (northV : E)⟫ = 0 := by
  rw [northV, EuclideanSpace.inner_single_right, ι_apply_last]; simp

theorem inner_northV_ι (t : E') : ⟪(northV : E), ι t⟫ = 0 := by
  rw [real_inner_comm, inner_ι_northV]

theorem norm_ι (t : E') : ‖ι t‖ = ‖t‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_castSucc]
  simp only [ι_apply_castSucc, ι_apply_last, norm_zero]
  simp

theorem inner_ι_self (t : E') : ⟪ι t, ι t⟫ = ‖t‖ ^ 2 := by
  rw [real_inner_self_eq_norm_sq, norm_ι]

theorem ι_injective : Injective (ι : E' →L[ℝ] E) := by
  intro a b h
  have := norm_ι (a - b)
  rw [map_sub, h, sub_self, norm_zero] at this
  exact sub_eq_zero.1 (norm_eq_zero.1 this.symm)

/-! ### The cutoff function -/

/-- A smooth cutoff, equal to `1` on `(-∞, 1/16]` and to `0` on `[1/4, ∞)`. -/
def ψ (s : ℝ) : ℝ := 1 - Real.smoothTransition ((16 * s - 1) / 3)

theorem ψ_of_le {s : ℝ} (h : s ≤ 1 / 16) : ψ s = 1 := by
  unfold ψ; rw [Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

theorem ψ_of_ge {s : ℝ} (h : 1 / 4 ≤ s) : ψ s = 0 := by
  unfold ψ; rw [Real.smoothTransition.one_of_one_le (by linarith), sub_self]

theorem ψ_eq_zero_iff {s : ℝ} : ψ s = 0 ↔ 1 / 4 ≤ s := by
  unfold ψ
  rw [sub_eq_zero, eq_comm, Real.smoothTransition.eq_one_iff_one_le]
  constructor <;> intro h <;> linarith

theorem ψ_nonneg (s : ℝ) : 0 ≤ ψ s := by
  unfold ψ; linarith [Real.smoothTransition.le_one ((16 * s - 1) / 3)]

theorem ψ_le_one (s : ℝ) : ψ s ≤ 1 := by
  unfold ψ; linarith [Real.smoothTransition.nonneg ((16 * s - 1) / 3)]

theorem contDiff_ψ : ContDiff ℝ ∞ ψ :=
  contDiff_const.sub ((Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop))

/-! ### The standard map -/

/-- The unnormalized standard map `ℝᵖ → ℝᵖ⁺¹ ∖ {0}`. -/
def stdW (t : E') : E := ψ (‖t‖ ^ 2) • ι t + (2 * ψ (‖t‖ ^ 2) - 1) • northV

/-- The standard collapse map `ℝᵖ → Sᵖ`. -/
def stdMap (t : E') : Sph p := nv0 (stdW t)

theorem inner_stdW_northV (t : E') : ⟪stdW t, (northV : E)⟫ = 2 * ψ (‖t‖ ^ 2) - 1 := by
  rw [stdW, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_ι_northV,
    real_inner_self_eq_norm_sq, norm_northV]
  ring

theorem inner_stdW_ι (t : E') : ⟪stdW t, ι t⟫ = ψ (‖t‖ ^ 2) * ‖t‖ ^ 2 := by
  rw [stdW, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_northV_ι,
    inner_ι_self]
  ring

theorem stdW_ne_zero (t : E') : stdW t ≠ 0 := by
  intro h
  have h1 := inner_stdW_northV t
  have h2 := inner_stdW_ι t
  rw [h, inner_zero_left] at h1 h2
  have hψ : ψ (‖t‖ ^ 2) = 1 / 2 := by linarith
  rw [hψ] at h2
  have ht : ‖t‖ ^ 2 = 0 := by linarith
  have ht0 : t = 0 := norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ht)
  rw [ht0, norm_zero] at hψ
  rw [ψ_of_le (by norm_num)] at hψ
  norm_num at hψ

theorem stdMap_val (t : E') : (stdMap t).1 = ‖stdW t‖⁻¹ • stdW t :=
  nv0_val (stdW_ne_zero t)

theorem contDiff_stdW : ContDiff ℝ ∞ (stdW (p := p)) := by
  have hψ : ContDiff ℝ ∞ (fun t : E' => ψ (‖t‖ ^ 2)) :=
    contDiff_ψ.comp (contDiff_norm_sq ℝ)
  exact (hψ.smul ι.contDiff).add
    (((contDiff_const.mul hψ).sub contDiff_const).smul contDiff_const)

theorem contMDiff_stdMap : ContMDiff 𝓘(ℝ, E') 𝓘(ℝ, E') ∞ (stdMap (p := p)) :=
  contMDiff_nv0_comp (I' := 𝓘(ℝ, E')) (contMDiff_iff_contDiff.2 contDiff_stdW) stdW_ne_zero

theorem stdW_of_small {t : E'} (ht : ‖t‖ ≤ 1 / 4) : stdW t = ι t + northV := by
  have h : ‖t‖ ^ 2 ≤ 1 / 16 := by
    have := norm_nonneg t
    nlinarith
  rw [stdW, ψ_of_le h]; norm_num

theorem stdW_of_half_le {t : E'} (ht : 1 / 2 ≤ ‖t‖) : stdW t = -northV := by
  have h : 1 / 4 ≤ ‖t‖ ^ 2 := by nlinarith
  rw [stdW, ψ_of_ge h]; norm_num

theorem stdMap_zero : stdMap (0 : E') = north := by
  apply Subtype.ext
  rw [stdMap_val, stdW_of_small (by simp), map_zero, zero_add, norm_northV, inv_one, one_smul,
    north_val]

theorem stdMap_of_half_le {t : E'} (ht : 1 / 2 ≤ ‖t‖) : stdMap t = south := by
  apply Subtype.ext
  rw [stdMap_val, stdW_of_half_le ht, norm_neg, norm_northV, inv_one, one_smul, south_val]

theorem stdMap_eq_of_small {t : E'} (ht : ‖t‖ ≤ 1 / 4) :
    (stdMap t).1 = ‖ι t + northV‖⁻¹ • (ι t + northV) := by
  rw [stdMap_val, stdW_of_small ht]

theorem stdMap_eq_north_iff {t : E'} : stdMap t = north ↔ t = 0 := by
  constructor
  · intro h
    have hv : ‖stdW t‖⁻¹ • stdW t = northV := by rw [← stdMap_val, h, north_val]
    have h1 := congrArg (fun y : E => ⟪y, ι t⟫) hv
    simp only [real_inner_smul_left, inner_stdW_ι, inner_northV_ι] at h1
    have hne : ‖stdW t‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.2 (stdW_ne_zero t))
    have h2 : ψ (‖t‖ ^ 2) * ‖t‖ ^ 2 = 0 := (mul_eq_zero.1 h1).resolve_left hne
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exfalso
      have h4 : stdW t = -northV := by rw [stdW, h3]; norm_num
      rw [h4, norm_neg, norm_northV, inv_one, one_smul] at hv
      have h5 := congrArg (fun y : E => ⟪y, northV⟫) hv
      simp only [inner_neg_left, real_inner_self_eq_norm_sq, norm_northV] at h5
      norm_num at h5
    · exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h3)
  · rintro rfl; exact stdMap_zero

theorem stdMap_eq_south_iff {t : E'} : stdMap t = south ↔ 1 / 2 ≤ ‖t‖ := by
  constructor
  · intro h
    have hv : ‖stdW t‖⁻¹ • stdW t = -northV := by rw [← stdMap_val, h, south_val]
    have h1 := congrArg (fun y : E => ⟪y, ι t⟫) hv
    simp only [real_inner_smul_left, inner_stdW_ι, inner_neg_left, inner_northV_ι, neg_zero] at h1
    have hne : ‖stdW t‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.2 (stdW_ne_zero t))
    have h2 : ψ (‖t‖ ^ 2) * ‖t‖ ^ 2 = 0 := (mul_eq_zero.1 h1).resolve_left hne
    rcases mul_eq_zero.1 h2 with h3 | h3
    · have h4 := ψ_eq_zero_iff.1 h3
      have := norm_nonneg t
      nlinarith
    · exfalso
      have ht0 : t = 0 := norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h3)
      rw [ht0, stdW_of_small (by simp), map_zero, zero_add, norm_northV, inv_one, one_smul] at hv
      have h5 := congrArg (fun y : E => ⟪y, northV⟫) hv
      simp only [inner_neg_left, real_inner_self_eq_norm_sq, norm_northV] at h5
      norm_num at h5
  · exact stdMap_of_half_le

/-! ### The derivative at `0` -/

theorem hasFDerivAt_stdMap_val_zero :
    HasFDerivAt (fun t : E' => (stdMap t).1) (ι : E' →L[ℝ] E) 0 := by
  have h1 : HasFDerivAt (fun t : E' => ι t + northV) (ι : E' →L[ℝ] E) 0 :=
    ι.hasFDerivAt.add_const northV
  have h2 := h1.norm_sq
  have hD : (2 • (innerSL ℝ (ι (0 : E') + northV)).comp (ι : E' →L[ℝ] E)) = 0 := by
    ext t
    simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      map_zero, zero_add, zero_apply, inner_northV_ι, smul_zero]
  rw [hD] at h2
  have hne : ‖ι (0 : E') + northV‖ ^ 2 ≠ 0 := by simp [norm_northV]
  have h3 := h2.sqrt hne
  have h4 := (hasDerivAt_inv (show √(‖ι (0 : E') + northV‖ ^ 2) ≠ 0 by
    simp [norm_northV])).comp_hasFDerivAt (0 : E') h3
  have h5 := h4.smul h1
  have hfun : (fun t : E' => ‖ι t + northV‖⁻¹ • (ι t + northV)) =
      fun t => (√(‖ι t + northV‖ ^ 2))⁻¹ • (ι t + northV) := by
    funext t; rw [Real.sqrt_sq (norm_nonneg _)]
  have hev : (fun t : E' => (stdMap t).1) =ᶠ[𝓝 0]
      fun t => ‖ι t + northV‖⁻¹ • (ι t + northV) :=
    Filter.eventually_of_mem (Metric.closedBall_mem_nhds (0 : E') (by norm_num : (0 : ℝ) < 1 / 4))
      (fun t ht => stdMap_eq_of_small (mem_closedBall_zero_iff.1 ht))
  rw [hfun] at hev
  refine (h5.congr_fderiv ?_).congr_of_eventuallyEq hev
  ext t
  simp [norm_northV]

/-- The derivative of the standard map at `0` is bijective. -/
theorem mfd_stdMap_zero_bijective :
    Bijective (mfd 𝓘(ℝ, E') 𝓘(ℝ, E') (stdMap (p := p)) 0) := by
  have hval : HasMFDerivAt 𝓘(ℝ, E') 𝓘(ℝ, E) (Subtype.val : Sph p → E) (stdMap 0)
      (mfd 𝓘(ℝ, E') 𝓘(ℝ, E) (Subtype.val : Sph p → E) (stdMap 0)) :=
    hasMFDerivAt_mfd (contMDiff_val.mdifferentiableAt (by simp))
  have hstd : HasMFDerivAt 𝓘(ℝ, E') 𝓘(ℝ, E') (stdMap (p := p)) 0
      (mfd 𝓘(ℝ, E') 𝓘(ℝ, E') (stdMap (p := p)) 0) :=
    hasMFDerivAt_mfd (contMDiff_stdMap.mdifferentiableAt (by simp))
  have h1 := hval.comp (0 : E') hstd
  have h2 : HasMFDerivAt 𝓘(ℝ, E') 𝓘(ℝ, E) (Subtype.val ∘ stdMap) (0 : E') (ι : E' →L[ℝ] E) :=
    hasFDerivAt_stdMap_val_zero.hasMFDerivAt
  have h3 : (mfd 𝓘(ℝ, E') 𝓘(ℝ, E) (Subtype.val : Sph p → E) (stdMap 0)).comp
      (mfd 𝓘(ℝ, E') 𝓘(ℝ, E') (stdMap (p := p)) 0) = ι := hasMFDerivAt_unique h1 h2
  have hinj_val : Injective (mfd 𝓘(ℝ, E') 𝓘(ℝ, E) (Subtype.val : Sph p → E) (stdMap 0)) :=
    injective_mfderiv_val (sphS p) (stdMap 0)
  have hinj : Injective (mfd 𝓘(ℝ, E') 𝓘(ℝ, E') (stdMap (p := p)) 0) := by
    have hc : Injective ((mfd 𝓘(ℝ, E') 𝓘(ℝ, E) (Subtype.val : Sph p → E) (stdMap 0)).comp
        (mfd 𝓘(ℝ, E') 𝓘(ℝ, E') (stdMap (p := p)) 0)) := by
      rw [h3]; exact ι_injective
    exact Injective.of_comp (f := ⇑(mfd 𝓘(ℝ, E') 𝓘(ℝ, E) (Subtype.val : Sph p → E) (stdMap 0))) hc
  exact ⟨hinj, LinearMap.injective_iff_surjective
    (f := (mfd 𝓘(ℝ, E') 𝓘(ℝ, E') (stdMap (p := p)) 0).toLinearMap) |>.1 hinj⟩

/-- `north` is a regular value of the standard map. -/
theorem isRegularValue_stdMap_north :
    IsRegularValue 𝓘(ℝ, E') 𝓘(ℝ, E') (stdMap (p := p)) north := by
  intro t ht
  rw [stdMap_eq_north_iff] at ht
  subst ht
  exact mfd_stdMap_zero_bijective.2


end Sphere

end Milnor
