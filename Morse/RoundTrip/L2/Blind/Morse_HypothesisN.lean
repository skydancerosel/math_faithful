import Morse
/-! Layer-2 blind definition of Morse_HypothesisN. Textbook: Milnor, *Morse Theory*, §7, p. 42,
Hypothesis (N): `A` has a neighbourhood `U` in `X` which can be deformed into `A` within `X`,
keeping `A` pointwise fixed.
Choices: "neighbourhood" = open set `U ⊇ A` (equivalent to "a set containing an open set
containing `A`": restrict the deformation to the interior). "Deformed into `A` within `X`" = a
jointly continuous homotopy `h : [0,1] × U → X` (values in `X`, not required to stay in `U`)
with `h₀` the inclusion `U ↪ X`, `h₁(U) ⊆ A`, and `h_t(a) = a` for all `a ∈ A` and all `t`. -/
namespace RoundTrip.L2.Morse_HypothesisN

open scoped unitInterval

/-- The textbook notion: some open neighbourhood `U` of `A` deforms into `A` inside `X`, rel `A`. -/
def T {X : Type} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧
    ∃ h : C(I × U, X), (∀ u : U, h (0, u) = u) ∧ (∀ u : U, h (1, u) ∈ A) ∧
      ∀ t : I, ∀ u : U, (u : X) ∈ A → h (t, u) = u

end RoundTrip.L2.Morse_HypothesisN
