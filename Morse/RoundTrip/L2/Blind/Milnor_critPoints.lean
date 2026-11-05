import Morse
/-! Layer-2 blind definition of Milnor_critPoints. Textbook: Milnor, *Morse Theory*, §2/§3 (Sard's
theorem, p. 10): `x ∈ M` is a critical point of `f : M → N` iff `df_x : T_xM → T_{f(x)}N` is not
surjective; `T` is the set `C` of critical points.
Choices: `df_x` is Mathlib's `mfderiv I J f x`. The textbook assumes `f` smooth between smooth
manifolds; the signature has no smoothness instances, and where `f` is not differentiable Mathlib's
`mfderiv` is `0`, so such a point is critical unless `T_{f(x)}N = F` is trivial (junk convention).
"Not surjective" is the textbook's "rank < dim N" in finite dimension. -/
namespace RoundTrip.L2.Milnor_critPoints

universe u

/-- The textbook notion: the set of points where the differential of `f` is not surjective. -/
def T {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {H : Type*} [TopologicalSpace H]
    {G : Type*} [TopologicalSpace G] (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {N : Type*} [TopologicalSpace N]
    [ChartedSpace G N] (f : M → N) : Set M :=
  {x | ¬ Function.Surjective (mfderiv I J f x)}

end RoundTrip.L2.Milnor_critPoints
