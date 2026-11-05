import Morse
/-! Layer-2 blind definition of Morse_telescope. Textbook: Milnor, *Morse Theory*, Appendix, p. 149
(`X_Σ = X₀ × [0,1] ∪ X₁ × [1,2] ∪ X₂ × [2,3] ∪ ⋯ ⊆ X × ℝ`).
Choices: the telescope is returned as a subset of `X × ℝ` (its topology, when `X` is a space, is
the subspace topology of `X × ℝ`, which the result type cannot carry). Milnor assumes
`X₀ ⊆ X₁ ⊆ ⋯`; the formula is used verbatim for any sequence `A`. Closed intervals `[n, n+1]`. -/
namespace RoundTrip.L2.Morse_telescope

/-- The textbook notion: `⋃ₙ Aₙ × [n, n+1] ⊆ X × ℝ`. -/
def T {X : Type} (A : ℕ → Set X) : Set (X × ℝ) :=
  {z | ∃ n : ℕ, z.1 ∈ A n ∧ (n : ℝ) ≤ z.2 ∧ z.2 ≤ (n : ℝ) + 1}

end RoundTrip.L2.Morse_telescope
