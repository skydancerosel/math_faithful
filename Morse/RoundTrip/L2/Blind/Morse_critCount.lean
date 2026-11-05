import Morse
/-! Layer-2 blind definition of Morse_critCount. Textbook: Milnor, *Morse Theory*, §5, p. 29 (the
Morse number `C_λ` = number of critical points of index `λ` of a Morse function `f` on `M`,
finite e.g. for compact `M`).
Choices: counts all critical points `p` (`mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p = 0`) whose index is `k`,
the index being that of the coordinate Hessian in the preferred chart `φ = chartAt E p`
(`fderiv ℝ (fderiv ℝ (f ∘ φ.symm)) (φ p)`, maximal dimension of a finite-dimensional subspace on
which it is negative definite, `sSup` in `ℕ`). Non-degeneracy is not required (textbook: `f` is
Morse, so all critical points are non-degenerate; for non-Morse `f` the value is this count).
Encoding: `Set.ncard`, so infinitely many such critical points give `0`.
The textbook works on a smooth (finite-dimensional, boundaryless) manifold `M` modelled on `E`;
the signature carries only a `ChartedSpace E M` (no smooth-structure or finite-dimensionality
instance), so local coordinates at `p` are the preferred chart `φ = chartAt E p` (the
identification `TM_p = E` that Mathlib uses for `TangentSpace 𝓘(ℝ, E) p`). For a smooth atlas the
textbook notions at a critical point do not depend on the chart, so this is the textbook value
there. -/
namespace RoundTrip.L2.Morse_critCount

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `H` is negative definite on the subspace `W`. -/
def NegDefOn (H : E →L[ℝ] E →L[ℝ] ℝ) (W : Submodule ℝ E) : Prop :=
  ∀ v ∈ W, v ≠ 0 → H v v < 0

/-- Index of a bilinear form: maximal dimension of a subspace on which it is negative definite. -/
noncomputable def idx (H : E →L[ℝ] E →L[ℝ] ℝ) : ℕ :=
  sSup {d : ℕ | ∃ W : Submodule ℝ E, FiniteDimensional ℝ W ∧ Module.finrank ℝ W = d ∧ NegDefOn H W}

variable (E) {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- Critical point: `f_* = 0` at `p`. -/
def IsCrit (f : M → ℝ) (p : M) : Prop := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p = 0

/-- The Hessian of `f` at `p` in the preferred chart at `p`. -/
noncomputable def hess (f : M → ℝ) (p : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (f ∘ (chartAt E p).symm)) (chartAt E p p)

/-- The textbook notion: the number of critical points of `f` of index `k`. -/
noncomputable def T (f : M → ℝ) (k : ℕ) : ℕ :=
  Set.ncard {p : M | IsCrit E f p ∧ idx (hess E f p) = k}

end RoundTrip.L2.Morse_critCount
