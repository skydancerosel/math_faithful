import Morse
import RoundTrip.L2.Blind.Morse_jump

/-! Layer-2 check of `Morse.jump` (`f'(t⁺) − f'(t⁻)` from `derivWithin` on `Ici t`, `Iic t`)
against the blind textbook definition: the same formula, definitionally equal. -/

namespace RoundTrip.L2.Morse_jump

/-- **Agreement**: definitionally equal. -/
theorem agree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) (t : ℝ) :
    Morse.jump f t = T f t := rfl

end RoundTrip.L2.Morse_jump
