import Morse
/-! Layer-2 blind definition of Morse_IsNondegenerateCriticalPoint. Textbook: Milnor,
*Morse Theory*, §2, pp. 4-5 (a critical point `p` (`df_p = 0`) at which the Hessian `d²f_p` is a
non-degenerate bilinear form, i.e. has trivial null space; in finite dimension: the matrix
`(∂²f/∂xⁱ∂xʲ(p))` is non-singular).
Choices: derivative and Hessian are Mathlib's `fderiv ℝ f p` and `fderiv ℝ (fderiv ℝ f) p`
(Hessian `H v w = D_v D_w f (p)`); non-degeneracy = trivial null space `{v | ∀ w, H v w = 0}`
(Milnor's definition; equals non-singularity of the matrix in finite dimension, and is "weak"
non-degeneracy in infinite dimension). The textbook assumes `f` smooth; outside, Mathlib's junk
values (`fderiv` = `0` where not differentiable) are used, so a non-differentiable point counts as
critical, and the Hessian there is computed from the junk derivative. -/
namespace RoundTrip.L2.Morse_IsNondegenerateCriticalPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Critical point: `df_p = 0`. -/
def IsCrit (f : E → ℝ) (p : E) : Prop := fderiv ℝ f p = 0

/-- The Hessian `d²f_p`. -/
noncomputable def hess (f : E → ℝ) (p : E) : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ f) p

/-- A bilinear form is non-degenerate iff its null space is trivial. -/
def Nondeg (H : E →L[ℝ] E →L[ℝ] ℝ) : Prop := ∀ v : E, (∀ w : E, H v w = 0) → v = 0

/-- The textbook notion: `p` is a critical point of `f` with non-degenerate Hessian. -/
def T (f : E → ℝ) (p : E) : Prop :=
  IsCrit f p ∧ Nondeg (hess f p)

end RoundTrip.L2.Morse_IsNondegenerateCriticalPoint
