import Morse
/-! Layer-2 blind definition of Morse_IsStrongDeformationRetract. Textbook: Milnor, *Morse Theory*,
§3, p. 13 (`A ⊆ X` is a deformation retract of `X` if there is a homotopy `r_t : X → X`,
`0 ≤ t ≤ 1`, with `r₀ = id`, `r₁(X) ⊆ A` and `r_t(a) = a` for all `a ∈ A` and all `t`).
Choices: the homotopy is a jointly continuous map `[0,1] × X → X` (Mathlib `unitInterval`);
`A` is fixed pointwise at every time `t` (the "strong" version, as in Milnor). No hypothesis on
`A` (if `X` is nonempty the condition forces `A` nonempty). -/
namespace RoundTrip.L2.Morse_IsStrongDeformationRetract

open scoped unitInterval

/-- The textbook notion: a homotopy `r : [0,1] × X → X` from the identity into `A`, fixing `A`
pointwise throughout. -/
def T {X : Type} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ r : C(I × X, X), (∀ x, r (0, x) = x) ∧ (∀ x, r (1, x) ∈ A) ∧
    ∀ t : I, ∀ a ∈ A, r (t, a) = a

end RoundTrip.L2.Morse_IsStrongDeformationRetract
