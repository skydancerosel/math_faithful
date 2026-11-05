import Morse
/-! Layer-2 blind definition of Morse_Omega. Textbook: Milnor, *Morse Theory*, §24, p. 136: with
`J₁, …, J_{k−1}` fixed anticommuting complex structures on `ℝⁿ`, `Ω₀(n) = O(n)` and, for `k ≥ 1`,
`Ω_k(n)` is the set of all complex structures `J` on `ℝⁿ` (orthogonal, `J² = −I`) with
`JJ_α = −J_αJ` for `α = 1, …, k−1` (so `Ω₁(n)` is the set of all complex structures).
Choices: indexing follows Milnor literally: `J_α` is `J α` for `1 ≤ α ≤ k − 1` (`J 0` is never
used, `J α` for `α ≥ k` is ignored by `Ω_k`). The textbook's standing hypothesis that
`J 1, …, J (k−1)` are themselves anticommuting complex structures (and that `n` is even / a
multiple of `m_k`) is not imposed: the same formula is used for every sequence `J`. `O(n)` is
Mathlib's `Matrix.orthogonalGroup` as a subset of `M_n(ℝ)`. -/
namespace RoundTrip.L2.Morse_Omega

/-- A complex structure (Milnor p. 133): orthogonal with `J² = −I`. -/
def IsCplxStr {n : Type*} [Fintype n] [DecidableEq n] (J : Matrix n n ℝ) : Prop :=
  J ∈ Matrix.orthogonalGroup n ℝ ∧ J * J = -1

/-- The textbook notion: `Ω₀(n) = O(n)`, `Ω_{k+1}(n)` = complex structures anticommuting with
`J 1, …, J k`. -/
def T {n : Type*} [Fintype n] [DecidableEq n] (J : ℕ → Matrix n n ℝ) : ℕ → Set (Matrix n n ℝ)
  | 0 => (Matrix.orthogonalGroup n ℝ : Set (Matrix n n ℝ))
  | k + 1 => {K | IsCplxStr K ∧ ∀ α, 1 ≤ α → α ≤ k → K * J α = -(J α * K)}

end RoundTrip.L2.Morse_Omega
