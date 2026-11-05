import Morse
/-! Layer-2 blind definition of Morse_nullityM. Textbook: Milnor, *Morse Theory*, §2, p. 5 (nullity
of `f` at a critical point `p` = dimension of the null space `{v : f_**(v,w) = 0 ∀ w}` of the
Hessian on `TM_p`).
Choices: Hessian = coordinate Hessian in the preferred chart,
`fderiv ℝ (fderiv ℝ (f ∘ φ.symm)) (φ p)`.
The textbook works on a smooth (finite-dimensional, boundaryless) manifold `M` modelled on `E`;
the signature carries only a `ChartedSpace E M` (no smooth-structure or finite-dimensionality
instance), so local coordinates at `p` are the preferred chart `φ = chartAt E p` (the
identification `TM_p = E` that Mathlib uses for `TangentSpace 𝓘(ℝ, E) p`). For a smooth atlas the
textbook notions at a critical point do not depend on the chart, so this is the textbook value
there.
At a non-critical `p` (textbook: undefined) the value is the nullity of that coordinate Hessian.
Null space with `v` in the first slot (irrelevant for symmetric Hessians). Encoding:
`Module.finrank`, so an infinite-dimensional null space (only for infinite-dimensional `E`) is
encoded as `0`. Junk `fderiv` = `0` where `f` is not twice differentiable. -/
namespace RoundTrip.L2.Morse_nullityM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The null space `{v | ∀ w, H v w = 0}` of a bilinear form. -/
def nullSpace (H : E →L[ℝ] E →L[ℝ] ℝ) : Submodule ℝ E where
  carrier := {v | ∀ w, H v w = 0}
  add_mem' := by
    intro a b ha hb w
    simp [ha w, hb w]
  zero_mem' := by
    intro w
    simp
  smul_mem' := by
    intro c v hv w
    simp [hv w]

/-- The Hessian of `f` at `p` in the preferred chart at `p`. -/
noncomputable def hess (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (f ∘ (chartAt E p).symm)) (chartAt E p p)

/-- The textbook notion: the dimension of the null space of the Hessian of `f` at `p`. -/
noncomputable def T (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) : ℕ :=
  Module.finrank ℝ (nullSpace (hess E f p))

end RoundTrip.L2.Morse_nullityM
