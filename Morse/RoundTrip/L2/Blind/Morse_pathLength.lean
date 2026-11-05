import Morse
/-! Layer-2 blind definition of Morse_pathLength. Textbook: Milnor, *Morse Theory*, §10, p. 59:
the length of a piecewise smooth path `c : [a, b] → N` is `L(c) = ∫ₐᵇ |dc/dt| dt`.
Choices: `dc/dt` is Mathlib's two-sided `deriv c t`; for a piecewise smooth `c` it is the true
velocity except at the finitely many break points (and possibly at `a`, `b`), a null set, so the
integral is the textbook one. The integral is the oriented interval integral `∫ t in a..b`;
outside the textbook's hypotheses (`a ≤ b`, `c` piecewise smooth) this gives
`L_a^b = -L_b^a` for `a > b`, and Mathlib's conventions (`deriv = 0` where `c` is not
differentiable, integral `0` if not integrable). -/
namespace RoundTrip.L2.Morse_pathLength

/-- The textbook notion: `L(c) = ∫ₐᵇ ‖c'(t)‖ dt`. -/
noncomputable def T {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ → V)
    (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv c t‖

end RoundTrip.L2.Morse_pathLength
