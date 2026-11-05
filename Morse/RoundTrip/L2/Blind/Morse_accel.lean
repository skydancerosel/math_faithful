import Morse
/-! Layer-2 blind definition of Morse_accel. Textbook: Milnor, *Morse Theory*, §12, p. 71: the
acceleration of a piecewise smooth path `ω` is `A_t = D/dt (dω/dt)`, the covariant derivative of
the velocity field, defined away from the break points; for `N ⊆ V` (Euclidean space, induced
metric, §8 p. 46) `D/dt` is the tangential component of the ordinary derivative, so
`A_t = P_{c(t)}(c''(t))`, `P_x` the orthogonal projection of `V` onto `T_xN`.
Choices: `hN` (`N` a smooth slice submanifold of `V`) is the setting and is not used. The tangent
space is defined from scratch: span of the velocities `γ'(0)` of smooth curves
`γ : (−ε, ε) → N` with `γ(0) = x`; `P_x` is `Submodule.starProjection` (exists, `V` being
finite-dimensional). `c''(t)` is Mathlib's two-sided `deriv (deriv c) t`, which is the true second
derivative wherever `c` is smooth near `t`. Outside the textbook's hypotheses (at break points,
at the end points `0`, `1` if `c` is only meaningful on `[0, 1]`, or wherever `c` is not twice
differentiable) Mathlib's `deriv` conventions apply (non-differentiable ⇒ `0`); if `c t ∉ N` the
tangent space is `{0}` and the value is `0`. -/
namespace RoundTrip.L2.Morse_accel

open scoped ContDiff
open Set

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `v` is the velocity `γ'(0)` of a smooth curve `γ : (−ε, ε) → N` with `γ(0) = q`. -/
def IsVelocity (N : Set V) (q v : V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V, ContDiffOn ℝ ∞ γ (Ioo (-ε) ε) ∧
    MapsTo γ (Ioo (-ε) ε) N ∧ γ 0 = q ∧ HasDerivAt γ v 0

/-- The tangent space `T_qN ⊆ V` (span of the velocities at `q`). -/
def tangentSpace (N : Set V) (q : V) : Submodule ℝ V :=
  Submodule.span ℝ {v | IsVelocity N q v}

/-- The orthogonal projection `P_q : V → V` onto `T_qN`. -/
noncomputable def proj [FiniteDimensional ℝ V] (N : Set V) (q : V) : V →L[ℝ] V :=
  (tangentSpace N q).starProjection

end

/-- The textbook notion: `A_t = D/dt (dc/dt) = P_{c(t)} (c''(t))`. -/
noncomputable def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (c : ℝ → V) (t : ℝ) : V :=
  proj N (c t) (deriv (deriv c) t)

end RoundTrip.L2.Morse_accel
