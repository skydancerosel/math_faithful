import Morse
/-! Layer-2 blind definition of Morse_IsCriticalPointM. Textbook: Milnor, *Morse Theory*, §2, p. 4
(`p` is critical for `f : M → ℝ` iff `f_* : TM_p → Tℝ_{f(p)}` is zero).
Choices: `f_*` is Mathlib's `mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p` (computed in the preferred chart at `p`).
The textbook works on a smooth (finite-dimensional, boundaryless) manifold `M` modelled on `E`;
the signature carries only a `ChartedSpace E M` (no smooth-structure or finite-dimensionality
instance), so local coordinates at `p` are the preferred chart `chartAt E p` (the identification
`TM_p = E` that Mathlib uses for `TangentSpace 𝓘(ℝ, E) p`). For a smooth atlas the textbook
notions at a critical point do not depend on the chart, so this is the textbook value there.
The textbook assumes `f` smooth; where `f` is not differentiable Mathlib's `mfderiv` is `0`, so
such a point counts as critical (the "not a regular point" convention). -/
namespace RoundTrip.L2.Morse_IsCriticalPointM

open scoped Manifold

/-- The textbook notion: the differential of `f` at `p` vanishes. -/
def T (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] (f : M → ℝ) (p : M) : Prop :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p = 0

end RoundTrip.L2.Morse_IsCriticalPointM
