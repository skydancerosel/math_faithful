import Morse
import RoundTrip.L2.Blind.Morse_indexM

/-! Layer-2 check of `Morse.indexM` against the blind textbook definition. Both take the index of
the same Hessian (the extended chart of the model `𝓘(ℝ, E)` is the preferred chart, so
`Morse.hessianM E f p = hess E f p` at every point). The indices of a bilinear form agree for
finite-dimensional `E` (the textbook's setting); in infinite dimension the project's index (Mathlib's
`sigNeg`) is `0` by convention, while the blind `sSup` still counts finite-dimensional negative
subspaces: on `M = E = ℓ²(ℕ)`, `f x = -x₀²` has Hessian `-2 v₀ w₀` at `0`, of project index `0` and
blind index `1`. Non-criticality plays no role (both are defined at every point). -/

namespace RoundTrip.L2.Morse_indexM

open Module

theorem hessianM_eq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) :
    Morse.hessianM E f p = hess E f p := by
  simp only [Morse.hessianM, Morse.hessian, Morse.localRep, hess, Morse.extChartAt_self_coe,
    Morse.extChartAt_self_coe_symm]

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The indices of a bilinear form agree in finite dimension. -/
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

theorem idx_eq_one (φ : E →L[ℝ] ℝ) (e : E) (he : φ e ≠ 0) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : ∀ v, H v v < 0 ↔ φ v ≠ 0) : idx H = 1 := by
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
    rw [hH]
    simp [hc, he]
  · rintro d ⟨W, hW, rfl, hneg⟩
    have hinj : Function.Injective ((φ : E →ₗ[ℝ] ℝ).comp W.subtype) := by
      rw [injective_iff_map_eq_zero]
      intro w hw
      by_contra hw0
      have hw0' : (w : E) ≠ 0 := fun h => hw0 (Subtype.ext h)
      exact ((hH w).1 (hneg w w.2 hw0')) hw
    simpa using LinearMap.finrank_le_finrank_of_injective hinj

end General

/-- Agreement for finite-dimensional models, at every point. -/
theorem agree_of (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) :
    Morse.indexM E f p = T E f p := by
  rw [Morse.indexM, hessianM_eq, index_eq_idx]
  rfl

section Counterexample

/-- `ℓ²(ℕ)`, an infinite-dimensional real normed space. -/
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

/-- The bilinear form `(x, y) ↦ -(x₀ y₀)`. -/
noncomputable def negSq : Ell2 →L[ℝ] Ell2 →L[ℝ] ℝ :=
  -((ContinuousLinearMap.mul ℝ ℝ).bilinearComp coord0 coord0)

theorem negSq_apply (x y : Ell2) : negSq x y = -(x 0 * y 0) := rfl

/-- `f x = -x₀²` on `M = E = ℓ²(ℕ)` (its own chart), at `0`. -/
theorem differ : Morse.indexM Ell2 (fun x : Ell2 => negSq x x) 0 ≠
    T Ell2 (fun x : Ell2 => negSq x x) 0 := by
  have hH : hess Ell2 (fun x : Ell2 => negSq x x) 0 =
      Morse.hessian (fun x : Ell2 => negSq x x) 0 := by
    simp only [hess, chartAt_self_eq, OpenPartialHomeomorph.refl_symm]
    rfl
  rw [Morse.indexM, index_eq_zero_of_not_finite not_finiteDimensional_Ell2, T, hH,
    idx_eq_one coord0 (unitVec 0) (by simp [coord0_apply, unitVec]) _ (fun v => by
      rw [Morse.hessian_bilinear, negSq_apply, coord0_apply]
      constructor
      · intro h h0
        rw [h0] at h
        simp at h
      · intro h
        nlinarith [mul_self_pos.2 h])]
  decide

end Counterexample

end RoundTrip.L2.Morse_indexM
