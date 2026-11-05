import Morse
/-! Layer-2 blind definition of Morse_jump. Textbook: Milnor, *Morse Theory*, §12, p. 71: at a
point `t` of a piecewise smooth path `ω`, `Δ_t(dω/dt) = dω/dt(t⁺) − dω/dt(t⁻)`, the difference of
the one-sided derivatives (velocities).
Choices: `dω/dt(t⁺)` is the right derivative `derivWithin f (Ici t) t` and `dω/dt(t⁻)` the left
derivative `derivWithin f (Iic t) t` (for `f` smooth on the closed pieces these are also the
one-sided limits of the velocity). At a point where `f` is differentiable the jump is `0`.
Outside the textbook's hypotheses, if a one-sided derivative does not exist Mathlib's
`derivWithin` gives `0` for it. -/
namespace RoundTrip.L2.Morse_jump

open Set

/-- The textbook notion: `Δ_t(df/dt) = f'(t⁺) − f'(t⁻)`. -/
noncomputable def T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) (t : ℝ) :
    E :=
  derivWithin f (Ici t) t - derivWithin f (Iic t) t

end RoundTrip.L2.Morse_jump
