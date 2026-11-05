import Morse
/-! Layer-2 blind definition of Morse_IsSmoothCoord. Textbook: Milnor, *Morse Theory*, §1/§2
(standard): a smooth local coordinate system `(y¹,…,yⁿ)` on a smooth manifold `M` is a
diffeomorphism from an open subset of `M` onto an open subset of a Euclidean (here: normed) space.
Choices: `y` is an `OpenPartialHomeomorph M E'` (open source and target); "diffeomorphism" =
`y` is `C^∞` on `y.source` and `y.symm` is `C^∞` on `y.target`, smoothness being Mathlib's
`ContMDiffOn` for the model `𝓘(ℝ, E)` on `M` (via `M`'s charts) and `𝓘(ℝ, E')` on `E'`.
The signature carries no `IsManifold` instance: when `M`'s atlas is not smooth, `T` still means
the same `ContMDiffOn` condition (chart-wise at each point). No dimension condition linking `E`
and `E'` (it follows for a diffeomorphism in finite dimension). -/
namespace RoundTrip.L2.Morse_IsSmoothCoord

open scoped ContDiff Manifold

/-- The textbook notion: `y` is a smooth coordinate chart (diffeomorphism onto an open set). -/
def T (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (y : OpenPartialHomeomorph M E') : Prop :=
  ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ y y.source ∧ ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ y.symm y.target

end RoundTrip.L2.Morse_IsSmoothCoord
