import Morse
import RoundTrip.L2.Blind.Morse_pathLength

/-! Layer-2 check of `Morse.pathLength` (`L(c) = ∫ₐᵇ ‖c'(t)‖ dt`) against the blind textbook
definition: the same formula, definitionally equal. -/

namespace RoundTrip.L2.Morse_pathLength

/-- **Agreement**: definitionally equal. -/
theorem agree {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ → V) (a b : ℝ) :
    Morse.pathLength c a b = T c a b := rfl

end RoundTrip.L2.Morse_pathLength
