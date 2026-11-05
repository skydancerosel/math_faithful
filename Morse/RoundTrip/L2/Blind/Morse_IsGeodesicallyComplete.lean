import Morse
/-! Layer-2 blind definition of Morse_IsGeodesicallyComplete. Textbook: Milnor, *Morse Theory*,
§10, p. 58 and p. 62: `N` is geodesically complete if `exp_q(v)` is defined for every `q ∈ N`
and every `v ∈ T_qN`, i.e. the geodesic `γ` with `γ(0) = q`, `γ'(0) = v` exists on `[0, 1]`
(equivalently, by rescaling, every geodesic extends to all of `ℝ`).
Choices: `hN` (`N` a smooth slice submanifold of `V`) is the setting and is not used. Tangent
spaces from scratch (span of velocities of smooth curves in `N`); geodesic of `N ⊆ V` (induced
metric): `C^∞`, values in `N`, acceleration orthogonal to `T_{γ(t)}N`; "defined on `[0,1]`" =
geodesic on the closed interval `[0, 1]`, right derivative `v` at `0`. The first formulation
(exp defined everywhere) is used. `N = ∅` is complete (vacuous). -/
namespace RoundTrip.L2.Morse_IsGeodesicallyComplete

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

/-- The textbook notion: `exp_q(v)` is defined for all `q ∈ N`, `v ∈ T_qN`. -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {N : Set V} (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) : Prop :=
  ∀ q ∈ N, ∀ v ∈ tangentSpace N q, ∃ γ : ℝ → V, IsGeoFrom N q v γ

end RoundTrip.L2.Morse_IsGeodesicallyComplete
