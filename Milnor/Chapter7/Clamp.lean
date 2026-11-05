import Milnor.Chapter7.Transition

/-!
# A smooth radial clamp

For `0 < a` and `2a ≤ b` there is a smooth map `λ : E → E` of a finite-dimensional inner
product space which is the identity on the ball of radius `a`, takes values in the ball of
radius `b`, and is a positive radial rescaling `λ t = c t • t` with `0 < c t ≤ 1`.
-/

open Set Filter Topology Real
open scoped ContDiff

noncomputable section

namespace Milnor

theorem exists_clamp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b : ℝ} (ha : 0 < a) (hab : 2 * a ≤ b) :
    ∃ «λ» : E → E, ContDiff ℝ ∞ «λ» ∧ (∀ t, ‖t‖ ≤ a → «λ» t = t) ∧ (∀ t, ‖«λ» t‖ ≤ b) ∧
      (∀ t, ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ «λ» t = c • t) := by
  have hb : 0 < b := by linarith
  -- the cutoff `ψ`: `0` on `(-∞, a²]`, `1` on `[4a², ∞)`
  set ψ : ℝ → ℝ := fun s => smoothTransition ((s - a ^ 2) / (3 * a ^ 2)) with hψ
  have hψs : ∀ s, ψ s = smoothTransition ((s - a ^ 2) / (3 * a ^ 2)) := fun s => rfl
  have hψ0 : ∀ s, s ≤ a ^ 2 → ψ s = 0 := fun s hs => by
    rw [hψs]
    exact smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
  have hψ1 : ∀ s, 4 * a ^ 2 ≤ s → ψ s = 1 := fun s hs => by
    rw [hψs]
    exact smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by positivity)]; linarith)
  have hψnn : ∀ s, 0 ≤ ψ s := fun s => smoothTransition.nonneg _
  have hψsmooth : ContDiff ℝ ∞ ψ :=
    smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  -- the squared scaling factor `g t = 1 + ψ(‖t‖²) ‖t‖² / b²`
  set g : E → ℝ := fun t => 1 + ψ (‖t‖ ^ 2) * ‖t‖ ^ 2 / b ^ 2 with hg
  have hgt : ∀ t, g t = 1 + ψ (‖t‖ ^ 2) * ‖t‖ ^ 2 / b ^ 2 := fun t => rfl
  have hg1 : ∀ t, 1 ≤ g t := fun t => by
    rw [hgt]
    have := hψnn (‖t‖ ^ 2)
    have : 0 ≤ ψ (‖t‖ ^ 2) * ‖t‖ ^ 2 / b ^ 2 := by positivity
    linarith
  have hgpos : ∀ t, 0 < g t := fun t => lt_of_lt_of_le one_pos (hg1 t)
  have hsqrtpos : ∀ t, 0 < √(g t) := fun t => Real.sqrt_pos.2 (hgpos t)
  have hsqrt1 : ∀ t, 1 ≤ √(g t) := fun t => by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (hg1 t)
  have hgsmooth : ContDiff ℝ ∞ g := by
    have h1 : ContDiff ℝ ∞ fun t : E => ‖t‖ ^ 2 := contDiff_norm_sq ℝ
    exact contDiff_const.add (((hψsmooth.comp h1).mul h1).div_const _)
  refine ⟨fun t => (√(g t))⁻¹ • t, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    exact ((hgsmooth.sqrt fun t => (hgpos t).ne').inv fun t => (hsqrtpos t).ne').smul
      contDiff_id
  · -- identity on the ball of radius `a`
    intro t ht
    have h2 : ‖t‖ ^ 2 ≤ a ^ 2 := by nlinarith [norm_nonneg t]
    have : g t = 1 := by rw [hgt, hψ0 _ h2]; ring
    simp only [this, Real.sqrt_one, inv_one, one_smul]
  · -- bounded by `b`
    intro t
    have hkey : ‖t‖ ^ 2 ≤ b ^ 2 * g t := by
      rcases lt_or_ge (‖t‖ ^ 2) (4 * a ^ 2) with h | h
      · have := hg1 t
        nlinarith
      · rw [hgt, hψ1 _ h]
        have : b ^ 2 * (1 + 1 * ‖t‖ ^ 2 / b ^ 2) = b ^ 2 + ‖t‖ ^ 2 := by
          field_simp
        rw [this]
        nlinarith
    have hsq : ‖t‖ ≤ b * √(g t) := by
      rw [← Real.sqrt_sq (norm_nonneg t), ← Real.sqrt_sq hb.le, ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt hkey
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hsqrtpos t))]
    rw [inv_mul_le_iff₀' (hsqrtpos t)]
    exact hsq
  · -- positive radial rescaling
    intro t
    exact ⟨(√(g t))⁻¹, inv_pos.2 (hsqrtpos t), inv_le_one_of_one_le₀ (hsqrt1 t), rfl⟩

end Milnor

end
