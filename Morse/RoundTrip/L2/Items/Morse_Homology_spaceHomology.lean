import Morse
import RoundTrip.L2.Blind.Morse_Homology_spaceHomology
namespace RoundTrip.L2.Morse_Homology_spaceHomology

universe u

/-- Both are Mathlib's singular homology `H_i(X; 𝕜)` in `ModuleCat 𝕜`, coefficients `𝕜`. -/
theorem agree (𝕜 : Type u) [Field 𝕜] (i : ℕ) (X : Type u) [TopologicalSpace X] :
    Morse.Homology.spaceHomology 𝕜 i X = T 𝕜 i X := rfl

end RoundTrip.L2.Morse_Homology_spaceHomology
