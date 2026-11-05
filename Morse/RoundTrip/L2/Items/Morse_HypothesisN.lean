import Morse
import RoundTrip.L2.Blind.Morse_HypothesisN

/-! Layer-2 check of `Morse.HypothesisN` against the blind textbook definition of Milnor's
Hypothesis (N) (p. 42): an open neighbourhood `U ⊇ A` and a homotopy `I × U → X` from the inclusion
into `A`, fixing `A` pointwise. The two are the same formula. -/

namespace RoundTrip.L2.Morse_HypothesisN

theorem agree {X : Type} [TopologicalSpace X] (A : Set X) : Morse.HypothesisN A ↔ T A :=
  Iff.rfl

end RoundTrip.L2.Morse_HypothesisN
