import Morse
import RoundTrip.L2.Blind.Morse_IsSmoothCoord

/-! Layer-2 check of `Morse.IsSmoothCoord` against the blind textbook definition (an open partial
homeomorphism `M → E'` which is `C^∞` on its source with `C^∞` inverse on its target, in the
`ContMDiffOn` sense): the same two conditions. Equal for all arguments (no `IsManifold` instance
needed on either side). -/

namespace RoundTrip.L2.Morse_IsSmoothCoord

theorem agree (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (y : OpenPartialHomeomorph M E') :
    Morse.IsSmoothCoord E y ↔ T E y :=
  ⟨fun h => ⟨h.contMDiffOn, h.contMDiffOn_symm⟩, fun h => ⟨h.1, h.2⟩⟩

end RoundTrip.L2.Morse_IsSmoothCoord
