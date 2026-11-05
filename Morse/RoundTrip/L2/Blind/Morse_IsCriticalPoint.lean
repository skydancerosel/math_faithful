import Morse
/-! Layer-2 blind definition of Morse_IsCriticalPoint. Textbook: Milnor, *Morse Theory*, §2, p. 4
(critical point of a real function on a vector space: `df_p = 0`).
Choices: the derivative is Mathlib's `fderiv ℝ f p`. The textbook assumes `f` smooth; at a point
where `f` is not differentiable Mathlib's `fderiv` is `0`, so such a point counts as critical
(the "not a regular point" convention). No finite-dimensionality is assumed. -/
namespace RoundTrip.L2.Morse_IsCriticalPoint

/-- The textbook notion: `p` is a critical point of `f` iff `df_p = 0`. -/
def T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (p : E) : Prop :=
  fderiv ℝ f p = 0

end RoundTrip.L2.Morse_IsCriticalPoint
