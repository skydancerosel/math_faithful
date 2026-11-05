import Morse
import RoundTrip.L2.Blind.Morse_torus

/-! Layer-2 check of `Morse.torus` against the blind textbook definition (torus of revolution
about the `x₃`-axis, `(√(x₁² + x₂²) − R)² + x₃² = r²`): definitionally equal, for all `R r`
(neither side imposes `0 < r < R`). -/

namespace RoundTrip.L2.Morse_torus

theorem agree (R r : ℝ) : Morse.torus R r = T R r := rfl

end RoundTrip.L2.Morse_torus
