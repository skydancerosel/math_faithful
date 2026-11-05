import Morse
import RoundTrip.L2.Blind.Morse_IsSmoothCurveIn

/-! Layer-2 check of `Morse.IsSmoothCurveIn` (`C^∞` on `[0, 1]`, values in `N` there) against the
blind textbook definition (`ContDiffOn ℝ ∞ γ (Icc 0 1) ∧ MapsTo γ (Icc 0 1) N`): the same two
conditions, a structure versus a conjunction. -/

namespace RoundTrip.L2.Morse_IsSmoothCurveIn

/-- **Agreement**: the same two conditions. -/
theorem agree {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {N : Set V} (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (γ : ℝ → V) :
    Morse.IsSmoothCurveIn hN γ ↔ T hN γ :=
  ⟨fun h => ⟨h.contDiffOn, h.mem⟩, fun h => ⟨h.1, h.2⟩⟩

end RoundTrip.L2.Morse_IsSmoothCurveIn
