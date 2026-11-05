import Morse
/-! Layer-2 blind definition of Morse_covAt. Textbook: Milnor, *Morse Theory*, §8, p. 43: for a
submanifold `N ⊆ V` (Euclidean space), a tangent vector `X_q ∈ T_qN` and a smooth vector field
`Y : N → V`, the covariant derivative `X_q ⊢ Y` is the tangential component `P_q(dY_q(X_q))` of
the ordinary directional derivative of `Y` (Gauss formula: `D_X Y = ∇_X Y + II(X, Y)`).
Choices: `hN` (`N` a smooth slice submanifold of `V`) is the setting and is not used. The tangent
space is defined from scratch: span of the velocities `γ'(0)` of smooth curves in `N` through `q`;
`P_q` is the orthogonal projection onto it (`Submodule.starProjection`). The directional
derivative of `Y : ↑N → V` at `q` in direction `v` is `fderivWithin ℝ Ỹ N q v`, `Ỹ` the extension
of `Y` by `0` off `N` (only its values on `N` matter); for `Y` smooth and `v ∈ T_qN` this is
`(Y ∘ γ)'(0)` for any smooth curve `γ` in `N` with `γ(0) = q`, `γ'(0) = v`. Outside the textbook
hypotheses: the direction is first projected, `v ↦ P_q v` (so a non-tangent `v` is replaced by
its tangential part); if `Y` is not differentiable within `N` at `q`, `fderivWithin` gives `0`. -/
namespace RoundTrip.L2.Morse_covAt

open scoped ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `v` is the velocity `γ'(0)` of a smooth curve `γ : (−ε, ε) → N` with `γ(0) = q`. -/
def IsVelocity (N : Set V) (q v : V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V, ContDiffOn ℝ ∞ γ (Set.Ioo (-ε) ε) ∧
    Set.MapsTo γ (Set.Ioo (-ε) ε) N ∧ γ 0 = q ∧ HasDerivAt γ v 0

/-- The tangent space `T_qN ⊆ V` (span of the velocities at `q`). -/
def tangentSpace (N : Set V) (q : V) : Submodule ℝ V :=
  Submodule.span ℝ {v | IsVelocity N q v}

/-- The orthogonal projection `P_q : V → V` onto `T_qN`. -/
noncomputable def proj [FiniteDimensional ℝ V] (N : Set V) (q : V) : V →L[ℝ] V :=
  (tangentSpace N q).starProjection

/-- A field `Y : N → V` extended by `0` to all of `V`. -/
noncomputable def extend {N : Set V} (Y : ↑N → V) : V → V :=
  open Classical in fun x => if h : x ∈ N then Y ⟨x, h⟩ else 0

/-- The textbook notion: `X_q ⊢ Y = P_q (dY_q(X_q))` (with `X_q = P_q v`). -/
noncomputable def T [FiniteDimensional ℝ V] {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (q : ↑N) (v : V)
    (Y : ↑N → V) : V :=
  proj N q (fderivWithin ℝ (extend Y) N q (proj N q v))

end RoundTrip.L2.Morse_covAt
