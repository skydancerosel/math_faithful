import Milnor.Chapter7.Collapse

/-!
# The collapse scale can be taken as large as desired
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {p : ℕ}

/-- `exists_scale` with a prescribed lower bound on the scale. -/
theorem exists_scale_ge {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b) {ε : ℝ}
    (hε : 0 < ε) (c₀ : ℝ) :
    ∃ c : ℝ, c₀ ≤ c ∧ 0 < c ∧ ∀ t, ε / 2 ≤ ‖t‖ → collapse hb c t = south := by
  set Kc : NNReal := ‖((Ae hb).symm : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))‖₊
    with hKc
  have hanti : AntilipschitzWith Kc (Ae hb) := (Ae hb).antilipschitz
  have hc1 : (0 : ℝ) < 2 * (Kc + 1) / ε := by positivity
  refine ⟨max c₀ (2 * (Kc + 1) / ε), le_max_left _ _, lt_max_of_lt_right hc1, fun t ht => ?_⟩
  apply stdMap_of_half_le
  have h1 : ‖t‖ ≤ Kc * ‖Ae hb t‖ := by
    have := hanti.le_mul_dist t 0
    simpa [dist_zero_right] using this
  have h2 : 0 ≤ ‖Ae hb t‖ := norm_nonneg _
  have h3 : ε / 2 ≤ (Kc + 1) * ‖Ae hb t‖ := by nlinarith
  have h4 : 1 / 2 ≤ 2 * (Kc + 1) / ε * ‖Ae hb t‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    nlinarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (lt_max_of_lt_right hc1)]
  calc (1 : ℝ) / 2 ≤ 2 * (Kc + 1) / ε * ‖Ae hb t‖ := h4
    _ ≤ max c₀ (2 * (Kc + 1) / ε) * ‖Ae hb t‖ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) h2

/-- A threshold beyond which every scale works. -/
theorem exists_scale_all {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ c, c₁ ≤ c → ∀ t, ε / 2 ≤ ‖t‖ → collapse hb c t = south := by
  set Kc : NNReal := ‖((Ae hb).symm : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))‖₊
    with hKc
  have hanti : AntilipschitzWith Kc (Ae hb) := (Ae hb).antilipschitz
  have hc1 : (0 : ℝ) < 2 * (Kc + 1) / ε := by positivity
  refine ⟨2 * (Kc + 1) / ε, hc1, fun c hc t ht => ?_⟩
  apply stdMap_of_half_le
  have h1 : ‖t‖ ≤ Kc * ‖Ae hb t‖ := by
    have := hanti.le_mul_dist t 0
    simpa [dist_zero_right] using this
  have h2 : 0 ≤ ‖Ae hb t‖ := norm_nonneg _
  have h3 : ε / 2 ≤ (Kc + 1) * ‖Ae hb t‖ := by nlinarith
  have h4 : 1 / 2 ≤ 2 * (Kc + 1) / ε * ‖Ae hb t‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    nlinarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hc1 hc)]
  calc (1 : ℝ) / 2 ≤ 2 * (Kc + 1) / ε * ‖Ae hb t‖ := h4
    _ ≤ c * ‖Ae hb t‖ := mul_le_mul_of_nonneg_right hc h2

/-- The derivative of the collapse map at `0` is `c • basisCLM b`. -/
theorem hasMFDerivAt_collapse_zero {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
    (c : ℝ) :
    HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (collapse hb c) 0
      (c • basisCLM b) := by
  set L : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
    c • (Ae hb : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) with hL
  have hLdef : collapse hb c = stdMap ∘ L := by
    funext t; simp [collapse, hL]
  have hL0 : L 0 = 0 := by simp
  have h1 : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) L 0 L :=
    (hasMFDerivAt_iff_hasFDerivAt).2 L.hasFDerivAt
  have h2 : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (stdMap (p := p)) (L 0)
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (stdMap (p := p)) 0) := by
    rw [hL0]
    exact ((contMDiff_stdMap (p := p)).mdifferentiableAt (by simp)).hasMFDerivAt
  have heq : (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (stdMap (p := p)) 0).comp L = c • basisCLM b := by
    refine ContinuousLinearMap.ext fun y => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply]
    have := mfd_stdMap_Ae hb (c • y)
    simp only [map_smul] at this
    rw [map_smul]
    exact this
  have h3 : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (collapse hb c) 0 ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (stdMap (p := p)) 0).comp L) := by
    rw [hLdef]; exact h2.comp 0 h1
  exact heq ▸ h3

end Framed

end Milnor
