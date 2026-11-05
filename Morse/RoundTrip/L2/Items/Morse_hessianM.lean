import Morse
import RoundTrip.L2.Blind.Morse_hessianM

/-! Layer-2 check of `Morse.hessianM` against the blind textbook definition. The project takes the
second derivative of `f ∘ (extChartAt 𝓘(ℝ, E) p).symm` at `extChartAt 𝓘(ℝ, E) p p`; for the
model `𝓘(ℝ, E)` the extended chart is the preferred chart `chartAt E p` itself
(`Morse.extChartAt_self_coe`, `Morse.extChartAt_self_coe_symm`), which is the blind choice. Equal
at every point (critical or not). -/

namespace RoundTrip.L2.Morse_hessianM

theorem agree (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) :
    Morse.hessianM E f p = T E f p := by
  simp only [Morse.hessianM, Morse.hessian, Morse.localRep, T, Morse.extChartAt_self_coe,
    Morse.extChartAt_self_coe_symm]

end RoundTrip.L2.Morse_hessianM
