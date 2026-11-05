import Milnor.Chapter7.BasisPath
import Milnor.Chapter7.Collapse

/-!
# Smooth paths of bases, with the associated linear maps

Two bases `e₀`, `e₁` of `ℝᵖ` with the same orientation are joined by a smooth path `τ` of
linearly independent tuples, constant near the ends of `[0,1]`, such that `t ↦ basisCLM (τ t)`
is smooth and uniformly bounded below (`exists_tuplePath`).
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

namespace Framed

open GLp Sphere

theorem exists_tuplePath {p : ℕ} (e₀ e₁ : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p)))
    (hor : e₀.orientation = e₁.orientation) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ τ : ℝ → Fin p → EuclideanSpace ℝ (Fin p),
      ContDiff ℝ ∞ τ ∧ (∀ t, t ≤ ε → τ t = ⇑e₀) ∧ (∀ t, 1 - ε ≤ t → τ t = ⇑e₁) ∧
      (∀ t, LinearIndependent ℝ (τ t)) ∧
      ContDiff ℝ ∞ (fun t => basisCLM (τ t)) ∧
      ∃ μ : ℝ, 0 < μ ∧ ∀ t z, μ * ‖z‖ ≤ ‖basisCLM (τ t) z‖ := by
  obtain ⟨A, hA, hAe⟩ := exists_det_pos_of_orientation_eq e₁ e₀ hor.symm
  obtain ⟨τ, hτs, hτ0, hτ1, hτli⟩ := exists_basisPath e₁.linearIndependent hA hε hε'
  rw [hAe] at hτ0
  -- smoothness of `t ↦ basisCLM (τ t)`
  have hclm : ContDiff ℝ ∞ (fun t => basisCLM (τ t)) := by
    have : (fun t => basisCLM (τ t)) = fun t => ∑ i : Fin p,
        ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin p)) (EuclideanSpace ℝ (Fin p))
          (EuclideanSpace.proj i) (τ t i) := rfl
    rw [this]
    refine ContDiff.sum fun i _ => ?_
    exact (ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin p)) (EuclideanSpace ℝ (Fin p))
      (EuclideanSpace.proj i)).contDiff.comp (contDiff_pi.1 hτs i)
  refine ⟨τ, hτs, hτ0, hτ1, hτli, hclm, ?_⟩
  rcases Nat.eq_zero_or_pos p with hp | hp
  · -- `p = 0`: every vector is zero
    subst hp
    refine ⟨1, one_pos, fun t z => ?_⟩
    have hz : z = 0 := by ext i; exact i.elim0
    simp [hz]
  · -- `p ≥ 1`: minimise on the compact set `[0,1] × Sᵖ⁻¹`
    set K : Set (ℝ × EuclideanSpace ℝ (Fin p)) :=
      Icc (0 : ℝ) 1 ×ˢ sphere (0 : EuclideanSpace ℝ (Fin p)) 1 with hKdef
    have hK : IsCompact K := isCompact_Icc.prod (isCompact_sphere 0 1)
    have hKne : K.Nonempty :=
      ⟨(0, EuclideanSpace.single ⟨0, hp⟩ (1 : ℝ)),
        ⟨⟨le_rfl, zero_le_one⟩, by simp [PiLp.norm_single]⟩⟩
    have hg : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin p) => ‖basisCLM (τ q.1) q.2‖) :=
      ((hclm.continuous.comp continuous_fst).clm_apply continuous_snd).norm
    obtain ⟨q, hqK, hqmin⟩ := hK.exists_isMinOn hKne hg.continuousOn
    have hμ : 0 < ‖basisCLM (τ q.1) q.2‖ := by
      refine norm_pos_iff.2 fun h => ?_
      have h0 : q.2 = 0 := basisCLM_injective (hτli q.1) (h.trans (map_zero _).symm)
      have h1 := hqK.2
      rw [mem_sphere_zero_iff_norm, h0, norm_zero] at h1
      exact zero_ne_one h1
    refine ⟨‖basisCLM (τ q.1) q.2‖, hμ, ?_⟩
    -- the bound on `[0,1]`
    have hIcc : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z,
        ‖basisCLM (τ q.1) q.2‖ * ‖z‖ ≤ ‖basisCLM (τ t) z‖ := by
      intro t ht z
      by_cases hz : z = 0
      · simp [hz]
      · have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
        have hmem : (t, ‖z‖⁻¹ • z) ∈ K := by
          refine ⟨ht, ?_⟩
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hzn.ne']
        have hle := isMinOn_iff.1 hqmin _ hmem
        simp only [map_smul, norm_smul, norm_inv, norm_norm] at hle
        calc ‖basisCLM (τ q.1) q.2‖ * ‖z‖
            ≤ (‖z‖⁻¹ * ‖basisCLM (τ t) z‖) * ‖z‖ := mul_le_mul_of_nonneg_right hle hzn.le
          _ = ‖basisCLM (τ t) z‖ := by field_simp
    intro t z
    rcases le_or_gt t 0 with ht | ht
    · rw [show τ t = τ 0 from (hτ0 t (ht.trans hε.le)).trans (hτ0 0 hε.le).symm]
      exact hIcc 0 ⟨le_rfl, zero_le_one⟩ z
    rcases le_or_gt t 1 with ht1 | ht1
    · exact hIcc t ⟨ht.le, ht1⟩ z
    · rw [show τ t = τ 1 from (hτ1 t (by linarith)).trans (hτ1 1 (by linarith)).symm]
      exact hIcc 1 ⟨zero_le_one, le_rfl⟩ z

end Framed

end Milnor
