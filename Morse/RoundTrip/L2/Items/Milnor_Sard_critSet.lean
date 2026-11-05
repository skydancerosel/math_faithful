import Morse
import RoundTrip.L2.Blind.Milnor_Sard_critSet

/-! Layer-2 check of `Milnor.Sard.critSet` against the blind textbook definition: both are
`{x ∈ U | ¬ Surjective (fderiv ℝ f x)}`, literally. -/

namespace RoundTrip.L2.Milnor_Sard_critSet

theorem agree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (U : Set E) :
    Milnor.Sard.critSet f U = T f U :=
  rfl

end RoundTrip.L2.Milnor_Sard_critSet
