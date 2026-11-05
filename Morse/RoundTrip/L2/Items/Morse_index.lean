import Morse
import RoundTrip.L2.Blind.Morse_index

/-! Layer-2 check of `Morse.index` (Mathlib's `sigNeg` of `v ↦ H v v`) against the blind textbook
definition (`sSup` of the dimensions of the finite-dimensional subspaces on which `H` is negative
definite). For finite-dimensional `E` (the textbook's setting) they agree: the project proves
`Morse.index_isGreatest`, and every subspace is then finite-dimensional. In infinite dimension
Mathlib's `sigNeg` is `0` by convention (it is bounded by `finrank ℝ E = 0`), while the blind `sSup`
still sees finite-dimensional negative subspaces: on `ℓ²(ℕ)` the form `-(x₀ y₀)` has project index
`0` and blind index `1`. -/

namespace RoundTrip.L2.Morse_index

open Module

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Agreement in finite dimension. -/
theorem agree_of [FiniteDimensional ℝ E] (H : E →L[ℝ] E →L[ℝ] ℝ) : Morse.index H = T H := by
  have hset : {d : ℕ | ∃ W : Submodule ℝ E, FiniteDimensional ℝ W ∧ finrank ℝ W = d ∧
      NegDefOn H W} =
      {k | ∃ W : Submodule ℝ E, finrank ℝ W = k ∧ ∀ v ∈ W, v ≠ 0 → H v v < 0} := by
    ext d
    constructor
    · rintro ⟨W, -, hW, hneg⟩
      exact ⟨W, hW, hneg⟩
    · rintro ⟨W, hW, hneg⟩
      exact ⟨W, inferInstance, hW, hneg⟩
  unfold T
  rw [hset, (Morse.index_isGreatest H).csSup_eq]

/-- In infinite dimension the project's index is `0` (the convention of Mathlib's `sigNeg`). -/
theorem index_eq_zero_of_not_finite (h : ¬ FiniteDimensional ℝ E) (H : E →L[ℝ] E →L[ℝ] ℝ) :
    Morse.index H = 0 := by
  have := Morse.index_le_finrank H
  rw [Module.finrank_of_not_finite h] at this
  omega

/-- The blind index of a form whose quadratic form is negative exactly off the kernel of a
functional `φ ≠ 0` is `1`, in any dimension. -/
theorem T_eq_one (φ : E →L[ℝ] ℝ) (e : E) (he : φ e ≠ 0) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : ∀ v, H v v < 0 ↔ φ v ≠ 0) : T H = 1 := by
  unfold T
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

section Counterexample

/-- `ℓ²(ℕ)`, an infinite-dimensional real normed space. -/
abbrev Ell2 : Type := lp (fun _ : ℕ => ℝ) 2

/-- The standard unit vectors of `ℓ²(ℕ)`. -/
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

/-- The zeroth coordinate. -/
noncomputable def coord0 : Ell2 →L[ℝ] ℝ := lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 0

theorem coord0_apply (x : Ell2) : coord0 x = x 0 := rfl

/-- The bilinear form `(x, y) ↦ -(x₀ y₀)`. -/
noncomputable def negSq : Ell2 →L[ℝ] Ell2 →L[ℝ] ℝ :=
  -((ContinuousLinearMap.mul ℝ ℝ).bilinearComp coord0 coord0)

theorem negSq_apply (x y : Ell2) : negSq x y = -(x 0 * y 0) := rfl

theorem differ : Morse.index negSq ≠ T negSq := by
  rw [index_eq_zero_of_not_finite not_finiteDimensional_Ell2,
    T_eq_one coord0 (unitVec 0) (by simp [coord0_apply, unitVec]) negSq (fun v => by
      rw [negSq_apply, coord0_apply, neg_lt_zero]
      exact mul_self_pos)]
  decide

end Counterexample

end RoundTrip.L2.Morse_index
