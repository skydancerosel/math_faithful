import Morse
/-! Layer-2 blind definition of Morse_secondFundForm. Textbook: second fundamental form of a
submanifold `N ⊆ V` (Euclidean space) at `q` (standard; Milnor §8–9, Gauss formula
`D_X Y = ∇_X Y + II(X, Y)`): for `v, w ∈ T_qN`, `II(v, w) = (1 − P_q)(dW_q(v))`, the normal
component of the ambient directional derivative of any smooth tangent field `W` on `N` with
`W(q) = w`.
Choices: `hN` (`N` a smooth slice submanifold of `V`) is the setting and is not used. The tangent
space is defined from scratch (span of velocities `γ'(0)` of smooth curves in `N` through the
point) and `P_p` is the orthogonal projection onto it (`Submodule.starProjection`). The tangent
field extending `w` is the canonical one, `W(p) = P_p w` (smooth and tangent on `N`, `W(q) = w`
for `w ∈ T_qN`; the value is independent of the extension). The directional derivative along `N`
is `fderivWithin ℝ · N q`. Outside the textbook hypotheses (`v` or `w` not tangent): the
direction is projected, `v ↦ P_q v`, and the field `p ↦ P_p w` has value `P_q w` at `q`, so
`T v w = II(P_q v, P_q w)` in the smooth setting; `fderivWithin` gives `0` where the field is not
differentiable within `N`. -/
namespace RoundTrip.L2.Morse_secondFundForm

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

/-- The textbook notion: `II(v, w) = (1 − P_q)(D_v W)` with `W(p) = P_p w`. -/
noncomputable def T [FiniteDimensional ℝ V] {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (q : ↑N) (v w : V) : V :=
  let d := fderivWithin ℝ (fun p => proj N p w) N q (proj N q v)
  d - proj N q d

end RoundTrip.L2.Morse_secondFundForm
