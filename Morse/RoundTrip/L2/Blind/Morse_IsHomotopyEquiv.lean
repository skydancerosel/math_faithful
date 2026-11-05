import Morse
/-! Layer-2 blind definition of Morse_IsHomotopyEquiv. Textbook: Milnor, *Morse Theory*, §3, p. 12
(a continuous map `f : X → Y` is a homotopy equivalence if there is a continuous `g : Y → X` with
`g ∘ f ≃ id_X` and `f ∘ g ≃ id_Y`).
Choices: "homotopic" is Mathlib's `ContinuousMap.Homotopic` (free homotopy, a continuous map
`[0,1] × X → X`); no hypotheses on the spaces. -/
namespace RoundTrip.L2.Morse_IsHomotopyEquiv

/-- The textbook notion: `f` has a continuous homotopy inverse `g`. -/
def T {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) : Prop :=
  ∃ g : C(Y, X), (g.comp f).Homotopic (ContinuousMap.id X) ∧
    (f.comp g).Homotopic (ContinuousMap.id Y)

end RoundTrip.L2.Morse_IsHomotopyEquiv
