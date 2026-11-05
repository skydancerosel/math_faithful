import Morse
/-! Layer-2 blind definition of Morse_IsMorseFunction. Textbook: Milnor, *Morse Theory*, §2,
pp. 4-6 (a smooth real-valued function on a smooth manifold all of whose critical points are
non-degenerate).
Choices: smoothness of `f` is included as a conjunct, `ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f` (C^∞, not
analytic); a prover comparing under the hypothesis "`f` smooth" may simply drop it. Critical =
`mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p = 0`; Hessian = coordinate Hessian in the preferred chart
`φ = chartAt E p`, `fderiv ℝ (fderiv ℝ (f ∘ φ.symm)) (φ p)`; non-degenerate = trivial null space.
The textbook works on a smooth (finite-dimensional, boundaryless) manifold `M` modelled on `E`;
the signature carries only a `ChartedSpace E M` (no smooth-structure or finite-dimensionality
instance), so local coordinates at `p` are the preferred chart `φ = chartAt E p` (the
identification `TM_p = E` that Mathlib uses for `TangentSpace 𝓘(ℝ, E) p`). For a smooth atlas the
textbook notions at a critical point do not depend on the chart, so this is the textbook value
there. -/
namespace RoundTrip.L2.Morse_IsMorseFunction

open scoped Manifold ContDiff

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M]

/-- Critical point: `f_* = 0` at `p`. -/
def IsCrit (f : M → ℝ) (p : M) : Prop := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p = 0

/-- The Hessian of `f` at `p` in the preferred chart at `p`. -/
noncomputable def hess (f : M → ℝ) (p : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (f ∘ (chartAt E p).symm)) (chartAt E p p)

variable {E} in
/-- A bilinear form is non-degenerate iff its null space is trivial. -/
def Nondeg (H : E →L[ℝ] E →L[ℝ] ℝ) : Prop := ∀ v : E, (∀ w : E, H v w = 0) → v = 0

/-- The textbook notion: `f` is smooth and every critical point of `f` is non-degenerate. -/
def T (f : M → ℝ) : Prop :=
  ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ ∀ p : M, IsCrit E f p → Nondeg (hess E f p)

end RoundTrip.L2.Morse_IsMorseFunction
