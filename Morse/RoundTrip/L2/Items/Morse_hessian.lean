import Morse
import RoundTrip.L2.Blind.Morse_hessian

/-! Layer-2 check of `Morse.hessian` against the blind textbook definition: both are
`fderiv ℝ (fderiv ℝ f) p`, literally. -/

namespace RoundTrip.L2.Morse_hessian

theorem agree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (p : E) :
    Morse.hessian f p = T f p :=
  rfl

end RoundTrip.L2.Morse_hessian
