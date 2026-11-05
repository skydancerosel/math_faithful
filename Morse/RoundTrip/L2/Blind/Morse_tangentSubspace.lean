import Morse
/-! Layer-2 blind definition of Morse_tangentSubspace. Textbook: Milnor, *Morse Theory*, §2/§6
(standard): the tangent space `T_qN ⊆ V` of a smooth submanifold `N ⊆ V` at `q ∈ N` is the
linear subspace of velocity vectors `γ'(0)` of smooth curves `γ : (−ε, ε) → N` with `γ(0) = q`.
Choices: `hN` (`N` is a smooth slice submanifold of `V`, modelled on `Z × W`) is only the setting
and is not used. A curve is a map `γ : ℝ → V` that is `C^∞` on some `(−ε, ε)`, `ε > 0`, maps
`(−ε, ε)` into `N`, has `γ 0 = q` and (two-sided) derivative `v` at `0`. For a submanifold this
set of velocities is already a linear subspace; `T` is its `Submodule.span` (so `T` is a
`Submodule` without using that fact). The curve definition is used rather than the image of the
differential of a parametrisation (equal for submanifolds). -/
namespace RoundTrip.L2.Morse_tangentSubspace

open scoped ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `v` is the velocity `γ'(0)` of a smooth curve `γ : (−ε, ε) → N` with `γ(0) = q`. -/
def IsVelocity (N : Set V) (q v : V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V, ContDiffOn ℝ ∞ γ (Set.Ioo (-ε) ε) ∧
    Set.MapsTo γ (Set.Ioo (-ε) ε) N ∧ γ 0 = q ∧ HasDerivAt γ v 0

/-- The textbook notion: the tangent space `T_qN` (span of the velocities at `q`). -/
def T {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {N : Set V} (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    (q : ↑N) : Submodule ℝ V :=
  Submodule.span ℝ {v | IsVelocity N (q : V) v}

end RoundTrip.L2.Morse_tangentSubspace
