import Morse
/-! Layer-2 blind definition of Morse_IsNondegenerateCriticalPointM. Textbook: Milnor,
*Morse Theory*, §2, pp. 4-5 (a critical point `p` at which the Hessian `f_**` on `TM_p` is a
non-degenerate bilinear form; in local coordinates: `(∂²f/∂xⁱ∂xʲ(p))` non-singular).
Choices: critical = `mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p = 0`; Hessian = coordinate Hessian in the
preferred chart `φ = chartAt E p`, i.e. `fderiv ℝ (fderiv ℝ (f ∘ φ.symm)) (φ p)`;
non-degenerate = trivial null space `{v | ∀ w, H v w = 0}` (= non-singular matrix in finite
dimension).
The textbook works on a smooth (finite-dimensional, boundaryless) manifold `M` modelled on `E`;
the signature carries only a `ChartedSpace E M` (no smooth-structure or finite-dimensionality
instance), so local coordinates at `p` are the preferred chart `chartAt E p` (the identification
`TM_p = E` that Mathlib uses for `TangentSpace 𝓘(ℝ, E) p`). For a smooth atlas the textbook
notions at a critical point do not depend on the chart, so this is the textbook value there.
Outside smoothness of `f`, Mathlib's junk values are used (`mfderiv`/`fderiv` = `0` where not
differentiable; a non-differentiable point counts as critical). -/
namespace RoundTrip.L2.Morse_IsNondegenerateCriticalPointM

open scoped Manifold

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

/-- The textbook notion: `p` is a critical point of `f` with non-degenerate Hessian. -/
def T (f : M → ℝ) (p : M) : Prop :=
  IsCrit E f p ∧ Nondeg (hess E f p)

end RoundTrip.L2.Morse_IsNondegenerateCriticalPointM
