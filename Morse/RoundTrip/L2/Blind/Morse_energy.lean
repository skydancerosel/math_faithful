import Morse
/-! Layer-2 blind definition of Morse_energy. Textbook: Milnor, *Morse Theory*, §12, p. 70: the
energy of a piecewise smooth path `ω : [a, b] → M` is `E_a^b(ω) = ∫ₐᵇ |dω/dt|² dt` (no factor
`1/2`); `E(ω) = E_0^1(ω)`.
Choices: `dω/dt` is Mathlib's two-sided `deriv c t`; for a piecewise smooth `c` it is the true
velocity except at the finitely many break points (and possibly at `a`, `b`), a null set, so the
integral is the textbook one. The integral is the oriented interval integral `∫ t in a..b`;
outside the textbook's hypotheses (`a ≤ b`, `c` piecewise smooth) this gives
`E_a^b = -E_b^a` for `a > b`, and Mathlib's conventions (`deriv = 0` where `c` is not
differentiable, integral `0` if not integrable). -/
namespace RoundTrip.L2.Morse_energy

/-- The textbook notion: `E_a^b(c) = ∫ₐᵇ ‖c'(t)‖² dt`. -/
noncomputable def T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ → E)
    (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv c t‖ ^ 2

end RoundTrip.L2.Morse_energy
