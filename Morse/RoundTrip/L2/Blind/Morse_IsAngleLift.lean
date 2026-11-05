import Morse
/-! Layer-2 blind definition of Morse_IsAngleLift. Textbook: Milnor, *Morse Theory*, §24 (the
winding argument; lifting a path through the covering `ℝ → S¹`): for a path
`t ↦ F(ω(t))`, `t ∈ [0, 1]`, in `ℂ ∖ {0}`, a continuous determination of its angle starting at `0`
is a continuous `θ : [0, 1] → ℝ` with `θ(0) = 0` and
`F(ω(t)) = |F(ω(t))| · e^{i(arg F(ω(0)) + θ(t))}` for all `t ∈ [0, 1]`.
Choices: `arg` is Mathlib's principal argument `Complex.arg` (in `(−π, π]`); continuity of `θ` is
built into `C([0,1], ℝ)`. The textbook hypothesis that `F(ω(t)) ≠ 0` for all `t` is NOT made a
conjunct: where `F(ω(t)) = 0` the equation holds for every value of `θ(t)` (so outside the
hypothesis `T` only constrains `θ` at the non-zero points). `ω` is only evaluated on `[0, 1]`. -/
namespace RoundTrip.L2.Morse_IsAngleLift

/-- The textbook notion: `θ(0) = 0` and `F(ω(t)) = |F(ω(t))| e^{i(arg F(ω(0)) + θ(t))}` for
`t ∈ [0,1]`. -/
def T {V : Type*} (F : V → ℂ) (ω : ℝ → V) (θ : C(unitInterval, ℝ)) : Prop :=
  θ 0 = 0 ∧ ∀ t : unitInterval,
    F (ω t) = (‖F (ω t)‖ : ℂ) * Complex.exp (((Complex.arg (F (ω 0)) + θ t : ℝ) : ℂ) * Complex.I)

end RoundTrip.L2.Morse_IsAngleLift
