import Morse
/-! Layer-2 blind definition of Morse_hessianM. Textbook: Milnor, *Morse Theory*, §2, pp. 4-5
(`f_**(v,w) = ṽ(w̃ f)(p)` on `TM_p`; in local coordinates the matrix `(∂²f/∂xⁱ∂xʲ(p))`,
chart-independent at a critical point).
Choices: the Hessian is the coordinate Hessian in the preferred chart `φ = chartAt E p`:
`T E f p = fderiv ℝ (fderiv ℝ (f ∘ φ.symm)) (φ p)`, so `T E f p v w = D_v D_w (f ∘ φ⁻¹)(φ p)`
(= `ṽ(w̃ f)(p)` with `v, w ∈ TM_p ≅ E` via `φ`).
The textbook works on a smooth (finite-dimensional, boundaryless) manifold `M` modelled on `E`;
the signature carries only a `ChartedSpace E M` (no smooth-structure or finite-dimensionality
instance), so local coordinates at `p` are the preferred chart `chartAt E p` (the identification
`TM_p = E` that Mathlib uses for `TangentSpace 𝓘(ℝ, E) p`). For a smooth atlas the textbook
notions at a critical point do not depend on the chart, so this is the textbook value there.
Outside critical points (where the textbook leaves the Hessian undefined) the value is still this
coordinate Hessian in the preferred chart. When `f ∘ φ⁻¹` is not twice differentiable at `φ p`,
Mathlib's junk (`fderiv` = `0`) is used. -/
namespace RoundTrip.L2.Morse_hessianM

/-- The textbook notion: the Hessian of `f` at `p` in local coordinates (preferred chart). -/
noncomputable def T (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (f ∘ (chartAt E p).symm)) (chartAt E p p)

end RoundTrip.L2.Morse_hessianM
