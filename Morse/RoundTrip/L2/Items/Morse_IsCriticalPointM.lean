import Morse
import RoundTrip.L2.Blind.Morse_IsCriticalPointM

/-! Layer-2 check of `Morse.IsCriticalPointM` against the blind textbook definition: both are
`mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p = 0`, literally. -/

namespace RoundTrip.L2.Morse_IsCriticalPointM

theorem agree (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) :
    Morse.IsCriticalPointM E f p ↔ T E f p :=
  Iff.rfl

end RoundTrip.L2.Morse_IsCriticalPointM
