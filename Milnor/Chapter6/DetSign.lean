import Milnor.Chapter6.Compose

/-!
# The sign of the Jacobian is constant on a ball

If `f` is smooth with invertible derivative on an open set containing a closed ball, the sign
of `det df` is constant on the ball (intermediate value theorem along segments).
-/

open Set Filter Topology Function Module
open scoped ContDiff

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- `L ↦ det L` is continuous on `E →L[ℝ] E`. -/
theorem continuous_det_clm : Continuous fun L : E →L[ℝ] E => LinearMap.det (L : E →ₗ[ℝ] E) := by
  classical
  set b := Module.finBasis ℝ E
  have h1 : Continuous fun L : E →L[ℝ] E => LinearMap.toMatrix b b (L : E →ₗ[ℝ] E) :=
    ((LinearMap.toMatrix b b).toLinearMap.comp
      (ContinuousLinearMap.coeLM ℝ : (E →L[ℝ] E) →ₗ[ℝ] (E →ₗ[ℝ] E))).continuous_of_finiteDimensional
  have h2 := h1.matrix_det
  refine h2.congr fun L => ?_
  simp [LinearMap.det_toMatrix]

theorem det_ne_zero_of_bijective {L : E →L[ℝ] E} (h : Bijective L) :
    LinearMap.det (L : E →ₗ[ℝ] E) ≠ 0 := by
  have := (LinearEquiv.ofBijective (L : E →ₗ[ℝ] E) h).isUnit_det'
  exact isUnit_iff_ne_zero.1 this

/-- **Constancy of the sign of the Jacobian on a closed ball.** -/
theorem sgn_det_fderiv_eq {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hinv : ∀ x ∈ U, Bijective (fderiv ℝ f x)) {z : E} {r : ℝ} (hr : Metric.closedBall z r ⊆ U)
    {x : E} (hx : x ∈ Metric.closedBall z r) :
    sgn (LinearMap.det (fderiv ℝ f x : E →ₗ[ℝ] E)) = sgn (LinearMap.det (fderiv ℝ f z : E →ₗ[ℝ] E)) := by
  have hz : z ∈ Metric.closedBall z r := Metric.mem_closedBall_self (by
    by_contra h; push_neg at h
    exact absurd hx (by simp [Metric.closedBall_eq_empty.2 h]))
  set g : ℝ → ℝ := fun t => LinearMap.det (fderiv ℝ f (z + t • (x - z)) : E →ₗ[ℝ] E) with hg
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, z + t • (x - z) ∈ Metric.closedBall z r := by
    intro t ht
    have := (convex_closedBall z r).add_smul_sub_mem hz hx ht
    exact this
  have hgc : ContinuousOn g (Icc 0 1) := by
    have hfd : ContinuousOn (fderiv ℝ f) U := hf.continuousOn_fderiv_of_isOpen hU (by simp)
    refine continuous_det_clm.comp_continuousOn (hfd.comp ?_ fun t ht => hr (hseg t ht))
    exact (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
  have hg0 : ∀ t ∈ Icc (0 : ℝ) 1, g t ≠ 0 := fun t ht =>
    det_ne_zero_of_bijective (hinv _ (hr (hseg t ht)))
  have h0 : g 0 = LinearMap.det (fderiv ℝ f z : E →ₗ[ℝ] E) := by simp [g]
  have h1 : g 1 = LinearMap.det (fderiv ℝ f x : E →ₗ[ℝ] E) := by simp [g]
  rw [← h0, ← h1]
  -- the sign cannot change without a zero
  rcases lt_or_gt_of_ne (hg0 0 ⟨le_rfl, zero_le_one⟩) with hneg | hpos
  · rcases lt_or_gt_of_ne (hg0 1 ⟨zero_le_one, le_rfl⟩) with hneg1 | hpos1
    · rw [sgn_neg hneg1, sgn_neg hneg]
    · exfalso
      obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc zero_le_one hgc ⟨hneg.le, hpos1.le⟩
      exact hg0 t ht ht0
  · rcases lt_or_gt_of_ne (hg0 1 ⟨zero_le_one, le_rfl⟩) with hneg1 | hpos1
    · exfalso
      obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc' zero_le_one hgc ⟨hneg1.le, hpos.le⟩
      exact hg0 t ht ht0
    · rw [sgn_pos hpos1, sgn_pos hpos]

end Milnor
