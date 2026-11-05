import Morse
import RoundTrip.L2.Blind.Morse_IsNondegenerateCriticalPointM

/-! Layer-2 check of `Morse.IsNondegenerateCriticalPointM` against the blind textbook definition:
same criticality (`mfderiv … = 0`), same Hessian (the extended chart of the model `𝓘(ℝ, E)` is the
preferred chart), and `Morse.IsNondegenerate` is the trivial-null-space condition. -/

namespace RoundTrip.L2.Morse_IsNondegenerateCriticalPointM

theorem hessianM_eq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) :
    Morse.hessianM E f p = hess E f p := by
  simp only [Morse.hessianM, Morse.hessian, Morse.localRep, hess, Morse.extChartAt_self_coe,
    Morse.extChartAt_self_coe_symm]

theorem agree (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) :
    Morse.IsNondegenerateCriticalPointM E f p ↔ T E f p := by
  unfold Morse.IsNondegenerateCriticalPointM T
  rw [hessianM_eq, Morse.isNondegenerate_iff]
  rfl

end RoundTrip.L2.Morse_IsNondegenerateCriticalPointM
