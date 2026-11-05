import Morse
import RoundTrip.L2.Blind.Morse_IsLeviCivita

/-! Layer-2 check of `Morse.IsLeviCivita` (a structure with fields `torsion_free :
D X Y − D Y X = ⁅X, Y⁆` and `metric : B (D X Y) Z + B Y (D X Z) = 0`, for left-invariant fields
identified with the Lie algebra `L`) against the blind textbook definition (the conjunction of the
same two conditions). Equivalent outright: `agree` is the structure's constructor/projections. -/

namespace RoundTrip.L2.Morse_IsLeviCivita

/-- **Agreement**, outright. -/
theorem agree {L : Type*} [LieRing L] [LieAlgebra ℝ L] (B : LinearMap.BilinForm ℝ L)
    (D : L →ₗ[ℝ] L →ₗ[ℝ] L) : Morse.IsLeviCivita B D ↔ T B D :=
  ⟨fun h => ⟨h.torsion_free, h.metric⟩, fun h => ⟨h.1, h.2⟩⟩

end RoundTrip.L2.Morse_IsLeviCivita
