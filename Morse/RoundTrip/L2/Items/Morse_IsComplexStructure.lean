import Morse
import RoundTrip.L2.Blind.Morse_IsComplexStructure

/-! Layer-2 check of `Morse.IsComplexStructure` (Milnor p. 133: `J` orthogonal with `J² = −I`)
against the blind textbook definition: the two are literally the same formula. -/

namespace RoundTrip.L2.Morse_IsComplexStructure

theorem agree {n : Type*} [Fintype n] [DecidableEq n] (J : Matrix n n ℝ) :
    Morse.IsComplexStructure J ↔ T J :=
  Iff.rfl

end RoundTrip.L2.Morse_IsComplexStructure
