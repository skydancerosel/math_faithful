import Morse
/-! Layer-2 blind definition of Morse_formIndex. Textbook: Milnor, *Morse Theory*, §2, p. 5 and
§15, p. 83: the index of a (symmetric) bilinear form `H` on a real vector space `M` (possibly
infinite-dimensional) is the maximal dimension of a subspace of `M` on which `H` is negative
definite, i.e. on which `H(v, v) < 0` for every `v ≠ 0`; it may be `+∞`.
Choices: "maximal dimension" = supremum (in `ℕ∞`) over all negative definite subspaces `S` of
`dim S`, with `dim S = (Module.rank ℝ S).toENat` (an infinite-dimensional negative definite
subspace contributes `⊤`; the supremum is `⊤` also when the dimensions are unbounded). No symmetry
of `B` is required: negative definiteness only involves the values `B v v`. -/
namespace RoundTrip.L2.Morse_formIndex

/-- `B` is negative definite on `S`: `B v v < 0` for every nonzero `v ∈ S`. -/
def IsNegDef {M : Type*} [AddCommGroup M] [Module ℝ M] (B : LinearMap.BilinForm ℝ M)
    (S : Submodule ℝ M) : Prop :=
  ∀ v ∈ S, v ≠ 0 → B v v < 0

/-- The textbook notion: the supremum of the dimensions of the subspaces on which `B` is
negative definite. -/
noncomputable def T {M : Type*} [AddCommGroup M] [Module ℝ M] (B : LinearMap.BilinForm ℝ M) :
    ℕ∞ :=
  ⨆ (S : Submodule ℝ M) (_ : IsNegDef B S), (Module.rank ℝ S).toENat

end RoundTrip.L2.Morse_formIndex
