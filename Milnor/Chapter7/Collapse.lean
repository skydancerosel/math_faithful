import Milnor.Chapter7.StdMap

/-!
# The collapse map with prescribed derivative

Given a basis `b` of `ℝᵖ` (the model space of `Sᵖ` at the north pole), `collapse b c t =
stdMap (c • A t)` with `A = (d stdMap₀)⁻¹ ∘ B`, `B eᵢ = bᵢ`, is a smooth map `ℝᵖ → Sᵖ` with
`collapse⁻¹(north) = {0}`, equal to the south pole outside a ball (for `c` large), and with
`d(φ ∘ collapse)₀ (eᵢ) = c • bᵢ` in the chart `φ` at the north pole.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Sphere

variable {p : ℕ}

/-- The linear map `eᵢ ↦ bᵢ`. -/
def basisCLM (b : Fin p → EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  ∑ i, (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).smulRight (b i)

theorem basisCLM_apply (b : Fin p → EuclideanSpace ℝ (Fin p)) (s : EuclideanSpace ℝ (Fin p)) :
    basisCLM b s = ∑ i, s i • b i := by
  simp [basisCLM]

theorem basisCLM_single (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    basisCLM b (EuclideanSpace.single i 1) = b i := by
  rw [basisCLM_apply]
  simp [EuclideanSpace.single_apply]

theorem basisCLM_injective {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b) :
    Injective (basisCLM b) := by
  refine (injective_iff_map_eq_zero _).2 fun s hs => ?_
  rw [basisCLM_apply] at hs
  have := (Fintype.linearIndependent_iff.1 hb) s hs
  ext i
  simp [this i]

theorem basisCLM_bijective {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b) :
    Bijective (basisCLM b) :=
  ⟨basisCLM_injective hb, LinearMap.injective_iff_surjective
    (f := (basisCLM b : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))) |>.1
    (basisCLM_injective hb)⟩

/-- The derivative of the standard map at `0`, as an equivalence. -/
def De : EuclideanSpace ℝ (Fin p) ≃L[ℝ] EuclideanSpace ℝ (Fin p) :=
  ContinuousLinearEquiv.ofBijective
    (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (stdMap (p := p)) 0)
    (LinearMap.ker_eq_bot.2 mfd_stdMap_zero_bijective.1)
    (LinearMap.range_eq_top.2 mfd_stdMap_zero_bijective.2)

theorem De_apply (t : EuclideanSpace ℝ (Fin p)) :
    De t = mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (stdMap (p := p)) 0 t :=
  rfl

/-- `eᵢ ↦ bᵢ` as an equivalence. -/
def Be {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b) :
    EuclideanSpace ℝ (Fin p) ≃L[ℝ] EuclideanSpace ℝ (Fin p) :=
  ContinuousLinearEquiv.ofBijective (basisCLM b)
    (LinearMap.ker_eq_bot.2 (basisCLM_bijective hb).1)
    (LinearMap.range_eq_top.2 (basisCLM_bijective hb).2)

theorem Be_apply {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
    (t : EuclideanSpace ℝ (Fin p)) : Be hb t = basisCLM b t :=
  rfl

/-- `A = (d stdMap₀)⁻¹ ∘ B`. -/
def Ae {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b) :
    EuclideanSpace ℝ (Fin p) ≃L[ℝ] EuclideanSpace ℝ (Fin p) :=
  (Be hb).trans De.symm

theorem mfd_stdMap_Ae {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
    (t : EuclideanSpace ℝ (Fin p)) :
    mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (stdMap (p := p)) 0
      (Ae hb t) = basisCLM b t := by
  rw [← De_apply]
  simp only [Ae, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply, Be_apply]

/-- The scaled collapse map. -/
def collapse {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b) (c : ℝ)
    (t : EuclideanSpace ℝ (Fin p)) : Sph p :=
  stdMap (c • Ae hb t)

theorem contMDiff_collapse {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
    (c : ℝ) : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (collapse hb c) := by
  have h : ContDiff ℝ ∞ (fun t : EuclideanSpace ℝ (Fin p) => c • Ae hb t) :=
    (Ae hb : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)).contDiff.const_smul c
  exact contMDiff_stdMap.comp (contMDiff_iff_contDiff.2 h)

theorem collapse_zero {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b) (c : ℝ) :
    collapse hb c 0 = north := by
  simp [collapse, stdMap_zero]

theorem collapse_eq_north_iff {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
    {c : ℝ} (hc : c ≠ 0) {t : EuclideanSpace ℝ (Fin p)} : collapse hb c t = north ↔ t = 0 := by
  rw [collapse, stdMap_eq_north_iff, smul_eq_zero, or_iff_right hc]
  constructor
  · intro h
    exact (Ae hb).injective (by rw [h, map_zero] : Ae hb t = Ae hb 0)
  · intro h; rw [h, map_zero]

/-- For `c` large, the collapse map is the south pole outside the ball of radius `ε / 2`. -/
theorem exists_scale {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b) {ε : ℝ}
    (hε : 0 < ε) : ∃ c : ℝ, 0 < c ∧ ∀ t, ε / 2 ≤ ‖t‖ → collapse hb c t = south := by
  set Kc : NNReal := ‖((Ae hb).symm : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))‖₊
    with hKc
  have hanti : AntilipschitzWith Kc (Ae hb) := (Ae hb).antilipschitz
  refine ⟨2 * (Kc + 1) / ε, by positivity, fun t ht => ?_⟩
  apply stdMap_of_half_le
  have h1 : ‖t‖ ≤ Kc * ‖Ae hb t‖ := by
    have := hanti.le_mul_dist t 0
    simpa [dist_zero_right] using this
  have h2 : 0 ≤ ‖Ae hb t‖ := norm_nonneg _
  have h3 : ε / 2 ≤ (Kc + 1) * ‖Ae hb t‖ := by nlinarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [div_mul_eq_mul_div, le_div_iff₀ hε]
  nlinarith

/-- The derivative of the collapse map, read in the chart at the north pole, along a line. -/
theorem hasDerivAt_chart_collapse {b : Fin p → EuclideanSpace ℝ (Fin p)}
    (hb : LinearIndependent ℝ b) (c : ℝ) (wv : EuclideanSpace ℝ (Fin p)) :
    HasDerivAt (fun s : ℝ => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) north (collapse hb c (s • wv)))
      (c • basisCLM b wv) 0 := by
  -- the chart representative of `stdMap` at `0`
  have h1 := (contMDiff_stdMap (p := p) 0).mdifferentiableAt (by simp) |>.hasMFDerivAt.2
  rw [ModelWithCorners.range_eq_univ] at h1
  have h2 := hasFDerivWithinAt_univ.1 h1
  have h3 : HasFDerivAt (fun t : EuclideanSpace ℝ (Fin p) =>
      extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) north (stdMap t))
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (stdMap (p := p)) 0) 0 := by
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp [writtenInExtChartAt, stdMap_zero, chartAt_self_eq]
  -- compose with the line `s ↦ s • (c • Ae wv)`
  have h4 : HasDerivAt (fun s : ℝ => s • (c • Ae hb wv)) (c • Ae hb wv) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (c • Ae hb wv)
  have h5 : HasFDerivAt (fun t : EuclideanSpace ℝ (Fin p) =>
      extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) north (stdMap t))
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (stdMap (p := p)) 0)
      ((0 : ℝ) • (c • Ae hb wv)) := by rw [zero_smul]; exact h3
  have h6 := h5.comp_hasDerivAt (0 : ℝ) h4
  have hfun : (fun s : ℝ => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) north (collapse hb c (s • wv))) =
      (fun t : EuclideanSpace ℝ (Fin p) => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) north (stdMap t)) ∘
        fun s : ℝ => s • (c • Ae hb wv) := by
    funext s
    simp only [Function.comp, collapse, map_smul, smul_comm s c]
  rw [hfun, ← mfd_stdMap_Ae hb]
  rw [map_smul] at h6
  exact h6

end Sphere

end Milnor
