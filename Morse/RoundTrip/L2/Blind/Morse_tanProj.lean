import Morse
/-! Layer-2 blind definition of Morse_tanProj. Textbook: Milnor, *Morse Theory*, §8, p. 43: for a
submanifold `N ⊆ V` (Euclidean space) and `q ∈ N`, `P_q : V → V` is the orthogonal projection of
`V` onto the tangent space `T_qN ⊆ V`.
Choices: `hN` (`N` a smooth slice submanifold of `V` modelled on `Z × W`) is the setting and is not
used. The tangent space is defined from scratch (as in the layer-2 blind file of
`Morse_tangentSubspace`): the span of the velocities `γ'(0)` of smooth curves `γ : (−ε, ε) → N`
with `γ(0) = q`. The projection is Mathlib's `Submodule.starProjection` (orthogonal projection onto
a subspace composed with the inclusion), which exists as `V` is finite-dimensional. -/
namespace RoundTrip.L2.Morse_tanProj

open scoped ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `v` is the velocity `γ'(0)` of a smooth curve `γ : (−ε, ε) → N` with `γ(0) = q`. -/
def IsVelocity (N : Set V) (q v : V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V, ContDiffOn ℝ ∞ γ (Set.Ioo (-ε) ε) ∧
    Set.MapsTo γ (Set.Ioo (-ε) ε) N ∧ γ 0 = q ∧ HasDerivAt γ v 0

/-- The tangent space `T_qN ⊆ V` (span of the velocities at `q`). -/
def tangentSpace (N : Set V) (q : V) : Submodule ℝ V :=
  Submodule.span ℝ {v | IsVelocity N q v}

/-- The textbook notion: the orthogonal projection `P_q` of `V` onto `T_qN`. -/
noncomputable def T {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) [FiniteDimensional ℝ V]
    (q : ↑N) : V →L[ℝ] V :=
  (tangentSpace N (q : V)).starProjection

end RoundTrip.L2.Morse_tanProj
