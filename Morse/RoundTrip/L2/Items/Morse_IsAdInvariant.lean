import Morse
import RoundTrip.L2.Blind.Morse_IsAdInvariant

/-! Layer-2 check of `Morse.IsAdInvariant` (Milnor 21.3(a): `B([X, Y], Z) = B(X, [Y, Z])`) against
the blind textbook definition: the two are literally the same formula (neither imposes symmetry or
positivity on `B`). -/

namespace RoundTrip.L2.Morse_IsAdInvariant

theorem agree {L : Type*} [LieRing L] [LieAlgebra ℝ L] (B : LinearMap.BilinForm ℝ L) :
    Morse.IsAdInvariant B ↔ T B :=
  Iff.rfl

end RoundTrip.L2.Morse_IsAdInvariant
