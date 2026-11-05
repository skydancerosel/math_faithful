import Milnor.Chapter6.PoincareHopf

/-!
# A smooth time reparametrization with positive derivative in the middle

For `0 < ε < 1/2` there is a smooth `ρ : ℝ → [0,1]` with `ρ = 0` on `(-∞, ε]`, `ρ = 1` on
`[1 - ε, ∞)`, and `ρ' > 0` on `(ε, 1 - ε)`.  It is used to make a homotopy constant near the
ends of `[0,1]` without creating new critical points.
-/

open Set Filter Topology Function Real Polynomial
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

theorem hasDerivAt_expNegInvGlue (x : ℝ) :
    HasDerivAt expNegInvGlue (x⁻¹ ^ 2 * expNegInvGlue x) x := by
  have := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) x
  simpa using this

theorem deriv_expNegInvGlue_pos {x : ℝ} (hx : 0 < x) : 0 < x⁻¹ ^ 2 * expNegInvGlue x :=
  mul_pos (pow_pos (inv_pos.2 hx) 2) (expNegInvGlue.pos_of_pos hx)

theorem hasDerivAt_smoothTransition (x : ℝ) :
    HasDerivAt smoothTransition
      ((x⁻¹ ^ 2 * expNegInvGlue x * (expNegInvGlue x + expNegInvGlue (1 - x)) -
        expNegInvGlue x * (x⁻¹ ^ 2 * expNegInvGlue x -
          (1 - x)⁻¹ ^ 2 * expNegInvGlue (1 - x))) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2) x := by
  have h1 := hasDerivAt_expNegInvGlue x
  have h2 : HasDerivAt (fun y => expNegInvGlue (1 - y))
      ((1 - x)⁻¹ ^ 2 * expNegInvGlue (1 - x) * (-1)) x :=
    (hasDerivAt_expNegInvGlue (1 - x)).comp x ((hasDerivAt_id x).const_sub 1)
  have h3 := h1.div (h1.add h2) (smoothTransition.pos_denom x).ne'
  have hfun : smoothTransition = fun y => expNegInvGlue y / (expNegInvGlue y + expNegInvGlue (1 - y)) :=
    rfl
  rw [hfun]
  convert h3 using 1 <;> first | rfl | (simp only [Pi.add_apply, Pi.div_apply]; ring)

theorem deriv_smoothTransition_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    0 < deriv smoothTransition x := by
  rw [(hasDerivAt_smoothTransition x).deriv]
  have ha := deriv_expNegInvGlue_pos h0
  have hb := deriv_expNegInvGlue_pos (sub_pos.2 h1)
  have hc := expNegInvGlue.pos_of_pos h0
  have hd := expNegInvGlue.pos_of_pos (sub_pos.2 h1)
  have hD := smoothTransition.pos_denom x
  apply div_pos _ (pow_pos hD 2)
  nlinarith [mul_pos ha hd, mul_pos hc hb]

/-- **The transition function.** -/
theorem exists_timeTransition {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ t, t ≤ ε → ρ t = 0) ∧ (∀ t, 1 - ε ≤ t → ρ t = 1) ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 1) ∧ (∀ t, ε < t → t < 1 - ε → 0 < deriv ρ t) := by
  have hden : 0 < 1 - 2 * ε := by linarith
  refine ⟨fun t => smoothTransition ((t - ε) / (1 - 2 * ε)), ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  · intro t ht
    exact smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le)
  · intro t ht
    exact smoothTransition.one_of_one_le ((le_div_iff₀ hden).2 (by linarith))
  · intro t
    exact ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  · intro t h1 h2
    have hin : HasDerivAt (fun t : ℝ => (t - ε) / (1 - 2 * ε)) (1 / (1 - 2 * ε)) t := by
      have := ((hasDerivAt_id t).sub_const ε).div_const (1 - 2 * ε)
      simpa using this
    have hd : HasDerivAt (fun t => smoothTransition ((t - ε) / (1 - 2 * ε)))
        (deriv smoothTransition ((t - ε) / (1 - 2 * ε)) * (1 / (1 - 2 * ε))) t := by
      have := ((hasDerivAt_smoothTransition ((t - ε) / (1 - 2 * ε))).comp t hin)
      rw [(hasDerivAt_smoothTransition _).deriv]
      exact this
    rw [hd.deriv]
    have h0 : 0 < (t - ε) / (1 - 2 * ε) := div_pos (by linarith) hden
    have h1' : (t - ε) / (1 - 2 * ε) < 1 := (div_lt_one hden).2 (by linarith)
    have := deriv_smoothTransition_pos h0 h1'
    exact mul_pos this (one_div_pos.2 hden)

end Milnor
