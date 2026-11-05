import Morse
import RoundTrip.L2.Blind.Morse_IsNegDefOn
namespace RoundTrip.L2.Morse_IsNegDefOn

/-- The project's `IsNegDefOn` is literally the textbook notion. -/
theorem agree {M : Type*} [AddCommGroup M] [Module ℝ M] (B : LinearMap.BilinForm ℝ M)
    (S : Submodule ℝ M) : Morse.IsNegDefOn B S ↔ T B S :=
  Iff.rfl

end RoundTrip.L2.Morse_IsNegDefOn
