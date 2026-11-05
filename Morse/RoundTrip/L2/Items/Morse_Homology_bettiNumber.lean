import Morse
import RoundTrip.L2.Blind.Morse_Homology_bettiNumber
namespace RoundTrip.L2.Morse_Homology_bettiNumber

universe u

/-- Both are `finrank 𝕜` of Mathlib's singular homology `H_i(X; 𝕜)` (`0` if infinite). -/
theorem agree (𝕜 : Type u) [Field 𝕜] (X : Type u) [TopologicalSpace X] (i : ℕ) :
    Morse.Homology.bettiNumber 𝕜 X i = T 𝕜 X i := rfl

end RoundTrip.L2.Morse_Homology_bettiNumber
