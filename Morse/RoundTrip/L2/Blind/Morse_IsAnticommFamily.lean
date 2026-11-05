import Morse
/-! Layer-2 blind definition of Morse_IsAnticommFamily. Textbook: Milnor, *Morse Theory*, §24,
p. 136: `J₁, …, J_k` are anticommuting complex structures on `ℝⁿ`: each `J_α` is orthogonal with
`J_α² = −I`, and `J_αJ_β = −J_βJ_α` for `α ≠ β`.
Choices: indexing follows Milnor literally: the family is `J 1, …, J k` (`J 0` and `J α` for
`α > k` are ignored); `k = 0` is the empty family (always true). `ℝⁿ` is `n → ℝ`; orthogonal =
Mathlib's `Matrix.orthogonalGroup`. No parity condition on `card n`. -/
namespace RoundTrip.L2.Morse_IsAnticommFamily

/-- A complex structure (Milnor p. 133): orthogonal with `J² = −I`. -/
def IsCplxStr {n : Type*} [Fintype n] [DecidableEq n] (J : Matrix n n ℝ) : Prop :=
  J ∈ Matrix.orthogonalGroup n ℝ ∧ J * J = -1

/-- The textbook notion: `J 1, …, J k` are pairwise anticommuting complex structures. -/
def T {n : Type*} [Fintype n] [DecidableEq n] (J : ℕ → Matrix n n ℝ) (k : ℕ) : Prop :=
  (∀ α, 1 ≤ α → α ≤ k → IsCplxStr (J α)) ∧
  ∀ α β, 1 ≤ α → α ≤ k → 1 ≤ β → β ≤ k → α ≠ β → J α * J β = -(J β * J α)

end RoundTrip.L2.Morse_IsAnticommFamily
