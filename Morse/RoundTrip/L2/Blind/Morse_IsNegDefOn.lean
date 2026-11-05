import Morse
/-! Layer-2 blind definition of Morse_IsNegDefOn. Textbook: Milnor, *Morse Theory*, §2, p. 5
(used in §15): a bilinear form `B` is negative definite on a subspace `S` if `B(v, v) < 0` for
every nonzero `v ∈ S`.
Choices: none (no symmetry of `B` is required; `S = ⊥` is vacuously negative definite). -/
namespace RoundTrip.L2.Morse_IsNegDefOn

/-- The textbook notion: `B v v < 0` for every nonzero `v ∈ S`. -/
def T {M : Type*} [AddCommGroup M] [Module ℝ M] (B : LinearMap.BilinForm ℝ M)
    (S : Submodule ℝ M) : Prop :=
  ∀ v ∈ S, v ≠ 0 → B v v < 0

end RoundTrip.L2.Morse_IsNegDefOn
