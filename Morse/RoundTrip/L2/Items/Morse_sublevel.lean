import Morse
import RoundTrip.L2.Blind.Morse_sublevel

/-! Layer-2 check of `Morse.sublevel` against the blind textbook definition
`{p | F p ≤ c}`: definitionally equal. -/

namespace RoundTrip.L2.Morse_sublevel

theorem agree {X : Type*} (F : X → ℝ) (c : ℝ) : Morse.sublevel F c = T F c := rfl

end RoundTrip.L2.Morse_sublevel
