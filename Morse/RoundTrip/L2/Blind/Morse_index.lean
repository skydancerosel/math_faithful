import Morse
/-! Layer-2 blind definition of Morse_index. Textbook: Milnor, *Morse Theory*, §2, p. 5
(index of a symmetric bilinear form = maximal dimension of a subspace on which it is negative
definite).
Choices: "negative definite on `W`" means `H v v < 0` for every nonzero `v ∈ W`; only
finite-dimensional subspaces are measured. No symmetry of `H` is assumed (only the quadratic form
`v ↦ H v v` is used). Encoding: the index is the `sSup` in `ℕ` of the dimensions of such
subspaces; an infinite index (unbounded dimensions, possible only for infinite-dimensional `E`,
outside §2's finite-dimensional setting) is encoded as `0` (`sSup` of an unbounded set of `ℕ`). -/
namespace RoundTrip.L2.Morse_index

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `H` is negative definite on the subspace `W`. -/
def NegDefOn (H : E →L[ℝ] E →L[ℝ] ℝ) (W : Submodule ℝ E) : Prop :=
  ∀ v ∈ W, v ≠ 0 → H v v < 0

/-- The textbook notion: the maximal dimension of a subspace on which `H` is negative definite. -/
noncomputable def T (H : E →L[ℝ] E →L[ℝ] ℝ) : ℕ :=
  sSup {d : ℕ | ∃ W : Submodule ℝ E, FiniteDimensional ℝ W ∧ Module.finrank ℝ W = d ∧ NegDefOn H W}

end RoundTrip.L2.Morse_index
