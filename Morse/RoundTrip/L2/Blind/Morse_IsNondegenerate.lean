import Morse
/-! Layer-2 blind definition of Morse_IsNondegenerate. Textbook: Milnor, *Morse Theory*, §2, p. 5
(a bilinear form is non-degenerate iff its null space `{v : H(v,w) = 0 ∀ w}` is `0`).
Choices: the null space is taken with `v` in the first slot, as in Milnor (`H v w = 0 ∀ w`); the
textbook forms are symmetric, so the slot does not matter there. No symmetry of `H` and no
finite-dimensionality of `E` is assumed (in infinite dimension this is "weak" non-degeneracy,
which is literally Milnor's null-space definition). -/
namespace RoundTrip.L2.Morse_IsNondegenerate

/-- The textbook notion: the null space of `H` is trivial. -/
def T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (H : E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  ∀ v : E, (∀ w : E, H v w = 0) → v = 0

end RoundTrip.L2.Morse_IsNondegenerate
