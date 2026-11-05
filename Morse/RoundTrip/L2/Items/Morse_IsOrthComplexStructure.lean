import Morse
import RoundTrip.L2.Blind.Morse_IsOrthComplexStructure

/-! Layer-2 check of `Morse.IsOrthComplexStructure` (a complex structure on a Euclidean space: `J`
preserves the inner product and `J² = −1`) against the blind textbook definition: the same two
conditions in the other order, for every real inner product space (neither assumes finite
dimension or adds surjectivity). -/

namespace RoundTrip.L2.Morse_IsOrthComplexStructure

theorem agree {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (J : V →L[ℝ] V) :
    Morse.IsOrthComplexStructure J ↔ T J :=
  ⟨fun h => ⟨h.inner, h.sq⟩, fun h => ⟨h.2, h.1⟩⟩

end RoundTrip.L2.Morse_IsOrthComplexStructure
