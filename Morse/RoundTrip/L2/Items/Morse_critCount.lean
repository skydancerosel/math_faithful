import Morse
import RoundTrip.L2.Blind.Morse_critCount

/-! Layer-2 check of `Morse.critCount` against the blind textbook definition. Both count, with
`Set.ncard`, the points `p` with `mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p = 0` and index `k`, where the index
is that of the same Hessian (the extended chart of the model `𝓘(ℝ, E)` is the preferred chart). The
only difference is the index of a bilinear form in infinite dimension: the project's (Mathlib's
`sigNeg`) is `0` by convention, the blind `sSup` still counts finite-dimensional negative subspaces.
So the counts agree for finite-dimensional `E` (the textbook's setting) and, more generally,
whenever the two indices agree at every critical point. On `M = E = ℓ²(ℕ)` the function
`f x = ⟪x, x⟫ - 2 x₀²` has the single critical point `0`, of project index `0` and blind index `1`,
so `C₀` is `1` for the project and `0` for the blind definition. -/

namespace RoundTrip.L2.Morse_critCount

open Module
open scoped Manifold RealInnerProductSpace

theorem hessianM_eq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) :
    Morse.hessianM E f p = hess E f p := by
  simp only [Morse.hessianM, Morse.hessian, Morse.localRep, hess, Morse.extChartAt_self_coe,
    Morse.extChartAt_self_coe_symm]

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem index_eq_idx [FiniteDimensional ℝ E] (H : E →L[ℝ] E →L[ℝ] ℝ) : Morse.index H = idx H := by
  have hset : {d : ℕ | ∃ W : Submodule ℝ E, FiniteDimensional ℝ W ∧ finrank ℝ W = d ∧
      NegDefOn H W} =
      {k | ∃ W : Submodule ℝ E, finrank ℝ W = k ∧ ∀ v ∈ W, v ≠ 0 → H v v < 0} := by
    ext d
    constructor
    · rintro ⟨W, -, hW, hneg⟩
      exact ⟨W, hW, hneg⟩
    · rintro ⟨W, hW, hneg⟩
      exact ⟨W, inferInstance, hW, hneg⟩
  unfold idx
  rw [hset, (Morse.index_isGreatest H).csSup_eq]

theorem index_eq_zero_of_not_finite (h : ¬ FiniteDimensional ℝ E) (H : E →L[ℝ] E →L[ℝ] ℝ) :
    Morse.index H = 0 := by
  have := Morse.index_le_finrank H
  rw [Module.finrank_of_not_finite h] at this
  omega

/-- A form negative on `e`, whose quadratic form is negative only off the kernel of a functional
`φ`, has blind index `1`. -/
theorem idx_eq_one (φ : E →L[ℝ] ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ) (e : E) (he : H e e < 0)
    (hH : ∀ v, H v v < 0 → φ v ≠ 0) : idx H = 1 := by
  unfold idx
  apply IsGreatest.csSup_eq
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  refine ⟨⟨ℝ ∙ e, inferInstance, finrank_span_singleton he0, ?_⟩, ?_⟩
  · intro v hv hv0
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    have hc : c ≠ 0 := by
      rintro rfl
      simp at hv0
    simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_self_pos.2 hc]
  · rintro d ⟨W, hW, rfl, hneg⟩
    have hinj : Function.Injective ((φ : E →ₗ[ℝ] ℝ).comp W.subtype) := by
      rw [injective_iff_map_eq_zero]
      intro w hw
      by_contra hw0
      have hw0' : (w : E) ≠ 0 := fun h => hw0 (Subtype.ext h)
      exact hH w (hneg w w.2 hw0') hw
    simpa using LinearMap.finrank_le_finrank_of_injective hinj

end General

/-- Agreement whenever the two indices agree at every critical point. -/
theorem agree_of_index_eq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ)
    (h : ∀ p, IsCrit E f p → Morse.index (hess E f p) = idx (hess E f p)) (k : ℕ) :
    Morse.critCount E f k = T E f k := by
  unfold Morse.critCount T
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Morse.indexM, hessianM_eq]
  constructor
  · rintro ⟨hp, hk⟩
    exact ⟨hp, (h p hp) ▸ hk⟩
  · rintro ⟨hp, hk⟩
    exact ⟨hp, (h p hp).symm ▸ hk⟩

/-- Agreement for finite-dimensional models. -/
theorem agree_of (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (k : ℕ) :
    Morse.critCount E f k = T E f k :=
  agree_of_index_eq E f (fun _ _ => index_eq_idx _) k

section Counterexample

/-- `ℓ²(ℕ)`, an infinite-dimensional real Hilbert space. -/
abbrev Ell2 : Type := lp (fun _ : ℕ => ℝ) 2

noncomputable def unitVec (n : ℕ) : Ell2 := lp.single 2 n (1 : ℝ)

theorem not_finiteDimensional_Ell2 : ¬ FiniteDimensional ℝ Ell2 := by
  intro hfin
  apply Module.Finite.not_linearIndependent_of_infinite (R := ℝ) unitVec
  rw [linearIndependent_iff']
  intro s g hs i hi
  have := congrArg (fun x : Ell2 => lp.evalₗ (𝕜 := ℝ) (fun _ : ℕ => ℝ) 2 i x) hs
  simp only [map_sum, map_smul, lp.evalₗ_apply, unitVec, lp.single_apply, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, if_pos hi] at this
  simpa using this

noncomputable def coord0 : Ell2 →L[ℝ] ℝ := lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 0

theorem coord0_apply (x : Ell2) : coord0 x = x 0 := rfl

theorem inner_unitVec (x : Ell2) : ⟪x, unitVec 0⟫ = x 0 := by
  simp [unitVec, lp.inner_single_right]

theorem inner_unitVec_self : ⟪unitVec 0, unitVec 0⟫ = 1 := by
  simp [unitVec]

theorem unitVec_zero_apply : (unitVec 0 : ℕ → ℝ) 0 = 1 := by simp [unitVec]

/-- The inner product of `ℓ²(ℕ)` as a continuous bilinear form. -/
noncomputable def innerR : Ell2 →L[ℝ] Ell2 →L[ℝ] ℝ := innerSL ℝ

theorem innerR_apply (x y : Ell2) : innerR x y = ⟪x, y⟫ := rfl

/-- The bilinear form `B(x, y) = ⟪x, y⟫ - 2 x₀ y₀`. -/
noncomputable def B : Ell2 →L[ℝ] Ell2 →L[ℝ] ℝ :=
  innerR - (2 : ℝ) • (ContinuousLinearMap.mul ℝ ℝ).bilinearComp coord0 coord0

theorem B_apply (x y : Ell2) : B x y = ⟪x, y⟫ - 2 * (x 0 * y 0) := by
  simp [B, innerR_apply, coord0_apply]

/-- `f x = ⟪x, x⟫ - 2 x₀²`. -/
noncomputable def f₀ : Ell2 → ℝ := fun x => B x x

theorem f₀_eq : f₀ = fun x => B x x := rfl

theorem fderiv_f₀ (x : Ell2) : fderiv ℝ f₀ x = B x + B.flip x := by
  have h := B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
  have heq : B.precompR Ell2 (id x) (ContinuousLinearMap.id ℝ Ell2) +
      B.precompL Ell2 (ContinuousLinearMap.id ℝ Ell2) (id x) = B x + B.flip x := by
    ext v
    simp
  rw [heq] at h
  exact h.fderiv

/-- The only critical point of `f₀` is `0`. -/
theorem isCrit_f₀ (x : Ell2) : IsCrit Ell2 f₀ x ↔ x = 0 := by
  rw [IsCrit, mfderiv_eq_fderiv, fderiv_f₀]
  constructor
  · intro h
    have h' : B x + B.flip x = (0 : Ell2 →L[ℝ] ℝ) := h
    have h1 : (B x + B.flip x) (unitVec 0) = 0 := by rw [h']; rfl
    have h2 : (B x + B.flip x) x = 0 := by rw [h']; rfl
    simp only [add_apply, ContinuousLinearMap.flip_apply, B_apply] at h1 h2
    rw [inner_unitVec, real_inner_comm, inner_unitVec, unitVec_zero_apply] at h1
    have hx0 : x 0 = 0 := by linarith
    rw [hx0] at h2
    have : ⟪x, x⟫ = 0 := by linarith
    exact inner_self_eq_zero.1 this
  · rintro rfl
    ext v
    simp only [map_zero, add_zero]
    rfl

theorem hess_f₀ : hess Ell2 f₀ 0 = Morse.hessian f₀ 0 := by
  simp only [hess, chartAt_self_eq, OpenPartialHomeomorph.refl_symm]
  rfl

theorem idx_hess_f₀ : idx (hess Ell2 f₀ 0) = 1 := by
  rw [hess_f₀]
  refine idx_eq_one coord0 _ (unitVec 0) ?_ ?_
  · rw [f₀_eq, Morse.hessian_bilinear, B_apply, inner_unitVec_self, unitVec_zero_apply]
    norm_num
  · intro v hv h0
    rw [f₀_eq, Morse.hessian_bilinear, B_apply] at hv
    rw [coord0_apply] at h0
    rw [h0] at hv
    nlinarith [real_inner_self_nonneg (x := v)]

/-- `C₀(f₀)` is `1` for the project (`0` has project index `0`) and `0` for the blind definition
(`0` has blind index `1`). -/
theorem differ : Morse.critCount Ell2 f₀ 0 ≠ T Ell2 f₀ 0 := by
  have hP : {p : Ell2 | Morse.IsCriticalPointM Ell2 f₀ p ∧ Morse.indexM Ell2 f₀ p = 0} = {0} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Morse.indexM,
      index_eq_zero_of_not_finite not_finiteDimensional_Ell2, and_true]
    exact isCrit_f₀ p
  have hT : {p : Ell2 | IsCrit Ell2 f₀ p ∧ idx (hess Ell2 f₀ p) = 0} = ∅ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp
    rw [(isCrit_f₀ p).1 hp, idx_hess_f₀]
    decide
  rw [Morse.critCount, T, hP, hT, Set.ncard_singleton, Set.ncard_empty]
  decide

end Counterexample

end RoundTrip.L2.Morse_critCount
