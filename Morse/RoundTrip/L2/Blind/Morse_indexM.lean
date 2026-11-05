import Morse
/-! Layer-2 blind definition of Morse_indexM. Textbook: Milnor, *Morse Theory*, §2, p. 5 (index of
`f` at a critical point `p` = index of the Hessian `f_**` on `TM_p` = maximal dimension of a
subspace on which `f_**` is negative definite).
Choices: Hessian = coordinate Hessian in the preferred chart,
`fderiv ℝ (fderiv ℝ (f ∘ φ.symm)) (φ p)`.
The textbook works on a smooth (finite-dimensional, boundaryless) manifold `M` modelled on `E`;
the signature carries only a `ChartedSpace E M` (no smooth-structure or finite-dimensionality
instance), so local coordinates at `p` are the preferred chart `φ = chartAt E p` (the
identification `TM_p = E` that Mathlib uses for `TangentSpace 𝓘(ℝ, E) p`). For a smooth atlas the
textbook notions at a critical point do not depend on the chart, so this is the textbook value
there.
At a non-critical `p` (textbook: undefined) the value is the index of that coordinate Hessian;
criticality/non-degeneracy are not required. "Negative definite on `W`" = `H v v < 0` for nonzero
`v ∈ W`; only finite-dimensional `W` are measured. Encoding: `sSup` in `ℕ`, so an infinite index
(only possible for infinite-dimensional `E`) is encoded as `0`. Junk `fderiv` = `0` where `f` is
not twice differentiable. -/
namespace RoundTrip.L2.Morse_indexM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `H` is negative definite on the subspace `W`. -/
def NegDefOn (H : E →L[ℝ] E →L[ℝ] ℝ) (W : Submodule ℝ E) : Prop :=
  ∀ v ∈ W, v ≠ 0 → H v v < 0

/-- Index of a bilinear form: maximal dimension of a subspace on which it is negative definite. -/
noncomputable def idx (H : E →L[ℝ] E →L[ℝ] ℝ) : ℕ :=
  sSup {d : ℕ | ∃ W : Submodule ℝ E, FiniteDimensional ℝ W ∧ Module.finrank ℝ W = d ∧ NegDefOn H W}

/-- The Hessian of `f` at `p` in the preferred chart at `p`. -/
noncomputable def hess (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (f ∘ (chartAt E p).symm)) (chartAt E p p)

/-- The textbook notion: the index of the Hessian of `f` at `p`. -/
noncomputable def T (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) : ℕ :=
  idx (hess E f p)

end RoundTrip.L2.Morse_indexM
