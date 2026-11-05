import Morse
/-! Layer-2 blind definition of Morse_expDomAt. Textbook: Milnor, *Morse Theory*, §10, p. 55-57
(and §18): the domain of `exp_q`, i.e. the set of `v ∈ T_qN` such that the geodesic `γ` with
`γ(0) = q`, `γ'(0) = v` is defined on `[0, 1]`.
Choices: `hN` (`N` a smooth slice submanifold of `V`) is the setting; the carrier
`Morse.tangentSubspace hN q` (the setting's `T_qN`, from the result type) is used only as the
type of the elements. For the geodesic condition, tangent spaces are defined from scratch (span
of velocities of smooth curves in `N`); geodesic of `N ⊆ V` (induced metric): `C^∞`, values in
`N`, acceleration orthogonal to `T_{γ(t)}N`. "Defined on `[0,1]`" = a geodesic on the closed
interval `[0, 1]` with `γ(0) = q` and right derivative `v` at `0` (for a manifold without
boundary this is the same as being defined on an open interval containing `[0,1]`). -/
namespace RoundTrip.L2.Morse_expDomAt

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

/-- The textbook notion: the `v ∈ T_qN` whose geodesic exists on `[0, 1]`. -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {N : Set V} (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    (q : ↑N) : Set ↥(Morse.tangentSubspace hN q) :=
  {v | ∃ γ : ℝ → V, IsGeoFrom N (q : V) (v : V) γ}

end RoundTrip.L2.Morse_expDomAt
