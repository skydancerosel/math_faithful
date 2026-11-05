import Morse
/-! Layer-2 blind definition of Morse_expDom. Textbook: Milnor, *Morse Theory*, §10, p. 57: the
domain of `exp`: the pairs `(q, v)`, `q ∈ N`, `v ∈ T_qN`, such that the geodesic `γ` with
`γ(0) = q`, `γ'(0) = v` is defined on an open interval containing `[0, 1]`.
Choices: `hN` (`N` a smooth slice submanifold of `V`) is the setting and is not used. Tangent
spaces from scratch (span of velocities of smooth curves in `N`); geodesic of `N ⊆ V` (induced
metric): `C^∞`, values in `N`, acceleration orthogonal to `T_{γ(t)}N`. Open interval containing
`[0,1]` = `(a, b)` with `a < 0`, `1 < b`; `γ'(0) = v` as a two-sided derivative. The conditions
`q ∈ N`, `v ∈ T_qN` are stated (they also follow from the existence of `γ`). -/
namespace RoundTrip.L2.Morse_expDom

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

/-- The textbook notion: `(q, v)` with `v ∈ T_qN` whose geodesic exists on some `(a, b) ⊇ [0,1]`. -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {N : Set V} (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) :
    Set (V × V) :=
  {x | x.1 ∈ N ∧ x.2 ∈ tangentSpace N x.1 ∧ ∃ a b : ℝ, a < 0 ∧ 1 < b ∧
    ∃ γ : ℝ → V, IsGeo N γ (Ioo a b) ∧ γ 0 = x.1 ∧ HasDerivAt γ x.2 0}

end RoundTrip.L2.Morse_expDom
