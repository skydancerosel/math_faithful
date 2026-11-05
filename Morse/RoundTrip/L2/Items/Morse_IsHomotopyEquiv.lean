import Morse
import RoundTrip.L2.Blind.Morse_IsHomotopyEquiv

/-! Layer-2 check of `Morse.IsHomotopyEquiv` against the blind textbook definition: both say that
`f` has a continuous two-sided homotopy inverse (Mathlib's `ContinuousMap.Homotopic`). They are the
same formula; the project's is universe-polymorphic, the blind one is at `Type`. -/

namespace RoundTrip.L2.Morse_IsHomotopyEquiv

theorem agree {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    Morse.IsHomotopyEquiv f ↔ T f :=
  Iff.rfl

end RoundTrip.L2.Morse_IsHomotopyEquiv
