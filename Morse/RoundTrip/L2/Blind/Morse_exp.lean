import Morse
/-! Layer-2 blind definition of Morse_exp. Textbook: Milnor, *Morse Theory*, §10, p. 57:
`exp_q(v) = γ(1)`, `γ` the (unique) geodesic of `N` with `γ(0) = q`, `γ'(0) = v`, for those
`v ∈ T_qN` for which this geodesic is defined on `[0, 1]`.
Choices: `hN` (`N` a smooth slice submanifold of `V`) is the setting and is not used. Tangent
spaces from scratch (span of velocities of smooth curves in `N`). Geodesic (for `N ⊆ V` with the
induced metric): `C^∞` on the interval, values in `N`, acceleration orthogonal to `T_{γ(t)}N`.
"Defined on `[0,1]`": a geodesic on the closed interval `[0, 1]` (derivatives within `[0,1]`,
one-sided at the ends); `γ(1)` is taken from a chosen such geodesic (`Classical.choose`; any two
agree on `[0,1]` by uniqueness of geodesics). The conditions `q ∈ N`, `v ∈ T_qN` follow from
the existence of `γ`. Outside the textbook domain (no such geodesic: `q ∉ N`, `v ∉ T_qN`, or the
geodesic does not reach `t = 1`) the value is `q`. -/
namespace RoundTrip.L2.Morse_exp

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

/-- `γ` is a geodesic of `N` on `s`: `C^∞` on `s`, `γ(s) ⊆ N`, and the acceleration `γ''(t)` is
orthogonal to `T_{γ(t)}N` for `t ∈ s` (derivatives within `s`). -/
def IsGeo (N : Set V) (γ : ℝ → V) (s : Set ℝ) : Prop :=
  ContDiffOn ℝ ∞ γ s ∧ MapsTo γ s N ∧
    ∀ t ∈ s, ∀ w ∈ tangentSpace N (γ t), inner ℝ (derivWithin (derivWithin γ s) s t) w = 0

/-- `γ` is a geodesic of `N` on `[0, 1]` with `γ(0) = q`, `γ'(0) = v` (right derivative). -/
def IsGeoFrom (N : Set V) (q v : V) (γ : ℝ → V) : Prop :=
  IsGeo N γ (Icc 0 1) ∧ γ 0 = q ∧ HasDerivWithinAt γ v (Icc 0 1) 0

end

/-- The textbook notion: `exp_q(v) = γ(1)` (and `q` outside the domain of `exp_q`). -/
noncomputable def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {N : Set V} (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    (q v : V) : V :=
  open Classical in if h : ∃ γ : ℝ → V, IsGeoFrom N q v γ then Classical.choose h 1 else q

end RoundTrip.L2.Morse_exp
