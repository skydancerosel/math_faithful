import Morse
import RoundTrip.L2.Blind.Morse_IsAnticommFamily

/-! Layer-2 check of `Morse.IsAnticommFamily` (Milnor p. 136: `J 1, …, J k` pairwise anticommuting
complex structures) against the blind textbook definition: the same two conditions, packaged as a
structure in the project and as a conjunction in the blind file (same indexing from `1`). -/

namespace RoundTrip.L2.Morse_IsAnticommFamily

theorem agree {n : Type*} [Fintype n] [DecidableEq n] (J : ℕ → Matrix n n ℝ) (k : ℕ) :
    Morse.IsAnticommFamily J k ↔ T J k :=
  ⟨fun h => ⟨h.cs, h.anti⟩, fun h => ⟨h.1, h.2⟩⟩

end RoundTrip.L2.Morse_IsAnticommFamily
