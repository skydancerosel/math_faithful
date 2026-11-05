import Morse
/-! Layer-2 blind definition of Morse_IsSmoothCurveIn. Textbook: a smooth curve `γ : [0, 1] → N`
in a submanifold `N ⊆ V`: `C^∞` on the closed interval `[0, 1]` (one-sided derivatives at the
end points) with values in `N`.
Choices: `hN` (`N` a smooth slice submanifold of `V`) is the setting and is not used; for an
embedded submanifold, smooth into `N` is the same as smooth into `V` with values in `N`.
`γ : ℝ → V`, only its values on `[0, 1]` matter: `ContDiffOn ℝ ∞ γ (Icc 0 1)` and
`γ([0, 1]) ⊆ N`. -/
namespace RoundTrip.L2.Morse_IsSmoothCurveIn

open scoped ContDiff
open Set

/-- The textbook notion: `γ` is a smooth curve `[0, 1] → N`. -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {N : Set V} (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    (γ : ℝ → V) : Prop :=
  ContDiffOn ℝ ∞ γ (Icc 0 1) ∧ MapsTo γ (Icc 0 1) N

end RoundTrip.L2.Morse_IsSmoothCurveIn
