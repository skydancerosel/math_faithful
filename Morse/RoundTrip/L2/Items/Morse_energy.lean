import Morse
import RoundTrip.L2.Blind.Morse_energy

/-! Layer-2 check of `Morse.energy` (`E_a^b(c) = ∫ₐᵇ ‖c'(t)‖² dt`, no factor `1/2`) against the
blind textbook definition: the same formula, definitionally equal. -/

namespace RoundTrip.L2.Morse_energy

/-- **Agreement**: definitionally equal. -/
theorem agree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ → E) (a b : ℝ) :
    Morse.energy c a b = T c a b := rfl

end RoundTrip.L2.Morse_energy
