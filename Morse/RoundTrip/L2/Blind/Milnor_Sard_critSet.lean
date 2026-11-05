import Morse
/-! Layer-2 blind definition of Milnor_Sard_critSet. Textbook: Milnor, *Morse Theory*, §3 (Sard's
theorem, p. 10): for `f : U → ℝⁿ` smooth on an open `U ⊆ ℝᵐ`, `x ∈ U` is critical iff the
differential `df_x` is not surjective (rank < n); `T` is the set of critical points in `U`.
Choices: `df_x` is Mathlib's full `fderiv ℝ f x` (equal to `fderivWithin ℝ f U x` for open `U`;
for non-open `U` this is a choice). Only points of `U` are included. The textbook assumes `f`
smooth; where `f` is not differentiable Mathlib's `fderiv` is `0`, so such a point of `U` is
critical unless `F` is trivial (junk convention). No finite-dimensionality is assumed. -/
namespace RoundTrip.L2.Milnor_Sard_critSet

/-- The textbook notion: the points of `U` at which `df_x` is not surjective. -/
def T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F) (U : Set E) : Set E :=
  {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}

end RoundTrip.L2.Milnor_Sard_critSet
