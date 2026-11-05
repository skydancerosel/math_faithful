import Morse
import RoundTrip.L2.Blind.Morse_nullityM

/-! Layer-2 check of `Morse.nullityM` against the blind textbook definition: the Hessians agree
(the extended chart of the model `𝓘(ℝ, E)` is the preferred chart) and both nullities are the
`Module.finrank` of the same subspace `{v | ∀ w, H v w = 0}`. Equal at every point. -/

namespace RoundTrip.L2.Morse_nullityM

theorem hessianM_eq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) :
    Morse.hessianM E f p = hess E f p := by
  simp only [Morse.hessianM, Morse.hessian, Morse.localRep, hess, Morse.extChartAt_self_coe,
    Morse.extChartAt_self_coe_symm]

theorem nullSpace_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E →L[ℝ] E →L[ℝ] ℝ) : Morse.nullSpace H = nullSpace H := by
  ext v
  rw [Morse.mem_nullSpace]
  rfl

theorem agree (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) :
    Morse.nullityM E f p = T E f p := by
  unfold Morse.nullityM Morse.nullity T
  rw [hessianM_eq, nullSpace_eq]

end RoundTrip.L2.Morse_nullityM
