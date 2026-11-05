import Morse
/-! Layer-2 blind definition of Morse_hessian. Textbook: Milnor, *Morse Theory*, §2, pp. 4-5
(Hessian `d²f_p`, matrix of second partials `∂²f/∂xⁱ∂xʲ(p)`).
Choices: the Hessian is Mathlib's second Fréchet derivative `fderiv ℝ (fderiv ℝ f) p`, so
`T f p v w = D_v (D_w f)(p)` (= `Σ vⁱ wʲ ∂²f/∂xⁱ∂xʲ(p)` in coordinates; symmetric when `f` is
`C²` near `p`). The textbook assumes `f` smooth; when `f` is not twice differentiable at `p` the
value is Mathlib's junk (`fderiv` of a non-differentiable map is `0`). No criticality of `p` is
required (on a vector space the Hessian makes sense at every point). -/
namespace RoundTrip.L2.Morse_hessian

/-- The textbook notion: the Hessian (second derivative) of `f` at `p`. -/
noncomputable def T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (p : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) p

end RoundTrip.L2.Morse_hessian
