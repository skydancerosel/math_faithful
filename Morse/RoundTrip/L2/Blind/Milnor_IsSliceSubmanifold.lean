import Morse
/-! Layer-2 blind definition of Milnor_IsSliceSubmanifold. Textbook: Lee, *Introduction to Smooth
Manifolds*, ch. 5 (embedded submanifolds and the local slice condition); Milnor §2 uses smooth
submanifolds. `S ⊆ M` is an embedded submanifold modelled on `Z` with codimension model `W` if
every point of `S` lies in the domain of a slice chart: a diffeomorphism `φ` from an open
`U ⊆ M` onto an open subset of `Z × W` with `φ(S ∩ U) = {(z, 0)} ∩ φ(U)`.
Choices: as in the slice-chart file: `φ : OpenPartialHomeomorph M (Z × W)`, "diffeomorphism" =
`ContMDiffOn` `C^∞` both ways for the models `I` and `𝓘(ℝ, Z × W)` (the signature has no
`IsManifold` instance; used as is). Zero slice (Lee's constant `c` reduces to `0` by a
translation). `S = ∅` is a submanifold (vacuous). No finite-dimensionality, no compatibility
between `E` and `Z × W` is imposed (it follows from the diffeomorphisms in finite dimension). -/
namespace RoundTrip.L2.Milnor_IsSliceSubmanifold

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

/-- The textbook notion: every point of `S` lies in the domain of a slice chart for `S`. -/
def T (S : Set M) : Prop :=
  ∀ x ∈ S, ∃ φ : OpenPartialHomeomorph M (Z × W), IsSlice I Z W S φ ∧ x ∈ φ.source

end RoundTrip.L2.Milnor_IsSliceSubmanifold
