import Morse
/-! Layer-2 blind definition of Morse_IsComplexStructure. Textbook: Milnor, *Morse Theory*, §24,
p. 133: a complex structure on `ℝⁿ` is an orthogonal linear transformation `J` with `J² = −I`.
Choices: `ℝⁿ` is `n → ℝ` for the finite index type `n`, linear maps are matrices; "orthogonal" is
membership in Mathlib's `Matrix.orthogonalGroup n ℝ` (`Jᵀ J = J Jᵀ = I`). Defined for every `n`
(Milnor assumes `n` even; for odd `n` no `J` satisfies `T`). -/
namespace RoundTrip.L2.Morse_IsComplexStructure

/-- The textbook notion: `J` is orthogonal and `J² = −I`. -/
def T {n : Type*} [Fintype n] [DecidableEq n] (J : Matrix n n ℝ) : Prop :=
  J ∈ Matrix.orthogonalGroup n ℝ ∧ J * J = -1

end RoundTrip.L2.Morse_IsComplexStructure
