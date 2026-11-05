import Morse
import RoundTrip.Check
import RoundTrip.Blind.V1_3

open scoped ContDiff Matrix

namespace RoundTrip.V1_3

/-- The project's statement: the types of the listed theorems (`IsCriticalPoint`, `hessian`,
`nullSpace`, `nullity`, `index`, `IsNondegenerate` are vocabulary), universes instantiated at
`0`. -/
def A : Prop :=
  (type_of% @Morse.hessian_symm.{0}) ∧
  (type_of% @Morse.index_isGreatest.{0}) ∧
  (type_of% @Morse.isNondegenerate_iff_nullity_eq_zero.{0}) ∧
  (type_of% @Morse.isNondegenerate_hessian_iff_det_ne_zero)

theorem A_holds : A :=
  ⟨@Morse.hessian_symm.{0}, @Morse.index_isGreatest.{0},
    @Morse.isNondegenerate_iff_nullity_eq_zero.{0}, @Morse.isNondegenerate_hessian_iff_det_ne_zero⟩

section Glue

variable {n : ℕ}

theorem eq_sum_basis (v : Fin n → ℝ) : v = ∑ i, v i • (Pi.single i 1 : Fin n → ℝ) := by
  conv_lhs => rw [← (Pi.basisFun ℝ (Fin n)).sum_repr v]
  simp

/-- A linear functional on `ℝⁿ` vanishes iff it vanishes on the coordinate vectors. -/
theorem clm_eq_zero_iff (L : (Fin n → ℝ) →L[ℝ] ℝ) : L = 0 ↔ ∀ i, L (Pi.single i 1) = 0 := by
  refine ⟨fun h i => by simp [h], fun h => ContinuousLinearMap.ext fun v => ?_⟩
  rw [eq_sum_basis v]
  simp [map_sum, h]

/-- The bilinear form of the matrix `H(eᵢ, eⱼ)` is `H`. -/
theorem dot_mulVec_eq (H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (v w : Fin n → ℝ) :
    v ⬝ᵥ ((Matrix.of fun i j => H (Pi.single i 1) (Pi.single j 1)).mulVec w) = H v w := by
  conv_rhs => rw [eq_sum_basis v, eq_sum_basis w]
  simp [map_sum, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm]
  exact Finset.sum_comm

/-- The blind Hessian matrix is the matrix of the project's Hessian. -/
theorem hmat_eq {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (p : Fin n → ℝ) :
    hmat f p = Matrix.of fun i j => Morse.hessian f p (Pi.single i 1) (Pi.single j 1) := by
  ext i j
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    ((hf.fderiv_right (m := 1) (by norm_cast)).differentiable (by simp)) p
  simp only [hmat, Matrix.of_apply]
  show fderiv ℝ (fun x => fderiv ℝ f x (Pi.single j 1)) p (Pi.single i 1) = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp [Morse.hessian]

end Glue

theorem A_to_B : A → B := by
  intro hA n f p hf
  refine ⟨clm_eq_zero_iff _, ?_⟩
  have h2 : ContDiffAt ℝ 2 f p := hf.contDiffAt.of_le (by norm_cast)
  rw [hmat_eq hf, ← hA.2.2.2 h2, hA.2.2.1]
  -- `nul` of the matrix form is the project's nullity
  have hset : {v : Fin n → ℝ | ∀ w, v ⬝ᵥ ((Matrix.of fun i j =>
      Morse.hessian f p (Pi.single i 1) (Pi.single j 1)).mulVec w) = 0} =
      (Morse.nullSpace (Morse.hessian f p) : Set (Fin n → ℝ)) := by
    ext v
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Morse.mem_nullSpace, dot_mulVec_eq]
  unfold nul
  rw [hset, Submodule.span_eq]
  rfl

#rt_check RoundTrip.V1_3.A_to_B [Morse.hessian_symm, Morse.index_isGreatest,
  Morse.isNondegenerate_iff_nullity_eq_zero, Morse.isNondegenerate_hessian_iff_det_ne_zero]

end RoundTrip.V1_3
