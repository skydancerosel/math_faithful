import Morse
/-! Layer-2 blind definition of Morse_IsUnbrokenGeodesic. Textbook: Milnor, *Morse Theory*, §12,
Theorem 12.3, p. 73: an unbroken geodesic is a path `ω ∈ Ω(M; p, q)` which is a geodesic on all
of `[0, 1]`: smooth on `[0, 1]` with `D/dt (dω/dt) = 0`.
Choices: `hN` (`N` a smooth slice submanifold of `V`) is the setting and is not used; `p := c 0`,
`q := c 1` (any end points). `c : ℝ → V`, only its values on `[0, 1]` matter: `c` is `C^∞` on
`[0, 1]` (`ContDiffOn`, one-sided derivatives at the ends; this makes `c` piecewise smooth),
`c([0, 1]) ⊆ N`. For `N ⊆ V` with the induced metric, `D/dt` is the tangential part of the
ordinary derivative, so `D/dt (dc/dt) = 0` says the acceleration
`c''(t) = derivWithin (derivWithin c (Icc 0 1)) (Icc 0 1) t` is orthogonal to `T_{c(t)}N` for
every `t ∈ [0, 1]` (no finite-dimensionality is carried, so "tangential part = 0" is stated as
membership in the orthogonal complement, which needs no projection). The tangent space is defined
from scratch: span of the velocities `γ'(0)` of smooth curves `γ : (−ε, ε) → N` with
`γ(0) = x`. -/
namespace RoundTrip.L2.Morse_IsUnbrokenGeodesic

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

end

/-- The textbook notion: `c` is a geodesic of `N` on all of `[0, 1]`. -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {N : Set V} (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    (c : ℝ → V) : Prop :=
  ContDiffOn ℝ ∞ c (Icc 0 1) ∧ MapsTo c (Icc 0 1) N ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      derivWithin (derivWithin c (Icc 0 1)) (Icc 0 1) t ∈ (tangentSpace N (c t))ᗮ

end RoundTrip.L2.Morse_IsUnbrokenGeodesic
