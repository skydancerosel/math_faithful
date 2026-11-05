import Morse
import RoundTrip.L2.Blind.Morse_IsNondegenerate

/-! Layer-2 check of `Morse.IsNondegenerate` (`nullSpace H = ⊥`, the null space being the kernel
of `v ↦ H v`) against the blind textbook definition (`∀ v, (∀ w, H v w = 0) → v = 0`). -/

namespace RoundTrip.L2.Morse_IsNondegenerate

theorem agree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (H : E →L[ℝ] E →L[ℝ] ℝ) :
    Morse.IsNondegenerate H ↔ T H :=
  Morse.isNondegenerate_iff

end RoundTrip.L2.Morse_IsNondegenerate
