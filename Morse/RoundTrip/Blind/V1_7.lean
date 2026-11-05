import Morse
/-! Blind formalization of V1_7 (Milnor Lemma 2.1, Hadamard). Choices:
- "convex neighbourhood V of 0": `V ⊆ ℝⁿ` (n = `Fin n → ℝ`) open, convex, `0 ∈ V` (open to make C^∞ on V meaningful).
- C^∞ on V: `ContDiffOn ℝ ∞ _ V`. Conclusion: ∃ `g i` C^∞ on V, `f x = Σ x_i g_i x` on V, `g_i 0 = ∂f/∂x_i (0)`.
- The integral formula of the proof is context, not asserted. -/
open scoped ContDiff
namespace RoundTrip.V1_7

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (V : Set (Fin n → ℝ)), IsOpen V → Convex ℝ V → (0 : Fin n → ℝ) ∈ V →
    ∀ f : (Fin n → ℝ) → ℝ, ContDiffOn ℝ ∞ f V → f 0 = 0 →
      ∃ g : Fin n → (Fin n → ℝ) → ℝ, (∀ i, ContDiffOn ℝ ∞ (g i) V) ∧
        (∀ x ∈ V, f x = ∑ i, x i * g i x) ∧
        (∀ i, g i 0 = fderiv ℝ f 0 (Pi.single i 1))

end RoundTrip.V1_7
