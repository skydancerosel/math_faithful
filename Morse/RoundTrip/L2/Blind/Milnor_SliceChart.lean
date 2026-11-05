import Morse
/-! Layer-2 blind definition of Milnor_SliceChart. Textbook: Lee, *Introduction to Smooth
Manifolds*, ch. 5 (slice charts): a diffeomorphism `φ` from an open subset `U` of `M` onto an
open subset of `ℝᵏ × ℝˡ` (here `Z × W`) such that `φ(S ∩ U)` is exactly the set of points of
`φ(U)` of the form `(z, 0)`.
Choices: a slice chart is an `OpenPartialHomeomorph M (Z × W)` (open source `U`, open target)
together with the properties, packaged as a subtype. "Diffeomorphism" = `φ` is `C^∞` on its
source and `φ.symm` is `C^∞` on its target, in Mathlib's `ContMDiffOn` sense for the model `I` on
`M` and `𝓘(ℝ, Z × W)` on `Z × W` (the signature has no `IsManifold` instance; `ContMDiffOn` is
used as is). The slice is the zero slice `W`-coordinate `= 0` (as in the given description; Lee
allows a constant `c`, which a translation reduces to `0`). No centring, no non-emptiness of
`S ∩ U`, no finite-dimensionality of `Z`, `W`. -/
namespace RoundTrip.L2.Milnor_SliceChart

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- `φ` is a slice chart for `S`: a diffeomorphism onto an open subset of `Z × W` carrying
`S ∩ U` exactly onto the points `(z, 0)` of `φ(U)`. -/
def IsSlice (S : Set M) (φ : OpenPartialHomeomorph M (Z × W)) : Prop :=
  ContMDiffOn I 𝓘(ℝ, Z × W) ∞ φ φ.source ∧ ContMDiffOn 𝓘(ℝ, Z × W) I ∞ φ.symm φ.target ∧
    φ '' (φ.source ∩ S) = φ.target ∩ {x | x.2 = 0}

/-- The textbook notion: the type of slice charts for `S` in `M`, modelled on `Z × W`. -/
def T (S : Set M) : Type _ :=
  {φ : OpenPartialHomeomorph M (Z × W) // IsSlice I Z W S φ}

end RoundTrip.L2.Milnor_SliceChart
