import Morse
/-! Layer-2 blind definition of Morse_IsGeodesicOn. Textbook: Milnor, *Morse Theory*, §8 (p. 44-45)
and §10 (p. 55): a smooth path `γ : I → N` is a geodesic if `D/dt (dγ/dt) = 0`; for `N ⊆ V`
(Euclidean space) with the induced metric, `D/dt` is the tangential part of the ordinary
derivative, so this says that the acceleration `γ''(t)` is orthogonal to `T_{γ(t)}N` for all
`t ∈ I`.
Choices: `hN` (`N` a smooth slice submanifold of `V`) is the setting and is not used. The tangent
space is defined from scratch: span of the velocities `c'(0)` of smooth curves
`c : (−ε, ε) → N` with `c(0) = x`. `γ : ℝ → V`, of which only the values on `s` matter:
`γ` is `C^∞` on `s` (`ContDiffOn`), `γ(s) ⊆ N`, and `γ''(t) = derivWithin (derivWithin γ s) s t`
(one-sided at endpoints of a closed interval) is orthogonal to `T_{γ(t)}N` for `t ∈ s`. The
textbook takes `s` an interval with non-empty interior; for other `s` the same formula is used
(e.g. at isolated points of `s` the derivative is `0`, `s = ∅` gives `True`). -/
namespace RoundTrip.L2.Morse_IsGeodesicOn

open scoped ContDiff
open Set

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `v` is the velocity `c'(0)` of a smooth curve `c : (−ε, ε) → N` with `c(0) = q`. -/
def IsVelocity (N : Set V) (q v : V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ → V, ContDiffOn ℝ ∞ c (Ioo (-ε) ε) ∧
    MapsTo c (Ioo (-ε) ε) N ∧ c 0 = q ∧ HasDerivAt c v 0

/-- The tangent space `T_qN ⊆ V` (span of the velocities at `q`). -/
def tangentSpace (N : Set V) (q : V) : Submodule ℝ V :=
  Submodule.span ℝ {v | IsVelocity N q v}

end

/-- The textbook notion: `γ` is a geodesic of `N` on `s` (smooth, in `N`, acceleration normal
to `N`). -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {N : Set V} (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    (γ : ℝ → V) (s : Set ℝ) : Prop :=
  ContDiffOn ℝ ∞ γ s ∧ MapsTo γ s N ∧
    ∀ t ∈ s, ∀ w ∈ tangentSpace N (γ t), inner ℝ (derivWithin (derivWithin γ s) s t) w = 0

end RoundTrip.L2.Morse_IsGeodesicOn
