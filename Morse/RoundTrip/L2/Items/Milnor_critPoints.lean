import Morse
import RoundTrip.L2.Blind.Milnor_critPoints

/-! Layer-2 check of `Milnor.critPoints` against the blind textbook definition: both are
`{x | ¬ Surjective (mfderiv I J f x)}`, literally. -/

namespace RoundTrip.L2.Milnor_critPoints

universe u

theorem agree {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {H : Type*} [TopologicalSpace H]
    {G : Type*} [TopologicalSpace G] (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {N : Type*} [TopologicalSpace N]
    [ChartedSpace G N] (f : M → N) :
    Milnor.critPoints I J f = T I J f :=
  rfl

end RoundTrip.L2.Milnor_critPoints
