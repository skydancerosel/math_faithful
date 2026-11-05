import Morse
/-! Layer-2 blind definition of Morse_varField. Textbook: Milnor, *Morse Theory*, §11-12, p. 68:
the variation vector field of a variation `α : (−ε, ε) × [0, 1] → M` of `ω` is
`W_t = ∂α/∂u (0, t)`.
Choices: `α u t` is `α(u, t)`; `∂α/∂u (0, t)` is Mathlib's `deriv (fun u => α u t) 0`. Outside
the textbook's hypotheses (`α` a variation, hence smooth in `u` on each strip), a
non-differentiable `u ↦ α u t` gives `0`. -/
namespace RoundTrip.L2.Morse_varField

/-- The textbook notion: `W_t = ∂α/∂u (0, t)`. -/
noncomputable def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (α : ℝ → ℝ → V) (t : ℝ) : V :=
  deriv (fun u => α u t) 0

end RoundTrip.L2.Morse_varField
