import Milnor.Chapter5.Orient

/-!
# The degree at a regular value

For `f : M → N` smooth, `M` compact, both oriented of dimension `n`, and `y` a regular value,
`degAt f y = ∑_{x ∈ f⁻¹(y)} signAt f x` (Milnor p. 27).  It is locally constant in `y`.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {n : ℕ}

/-- The signed count of preimages: `∑_{x ∈ f⁻¹(y)} signAt f x`. -/
def degAt (oM : Orient I M n) (oN : Orient J N n) (f : M → N) (y : N) : ℤ :=
  ∑ᶠ x ∈ f ⁻¹' {y}, signAt oM oN f x

/-- **Local constancy of the degree** near a regular value (Milnor p. 27, first paragraph after
the definition). -/
theorem IsRegularValue.eventually_degAt_eq [IsManifold I ∞ M] [IsManifold J ∞ N] [I.Boundaryless]
    [J.Boundaryless] [CompactSpace M] [T2Space M] [T2Space N] (hE : finrank ℝ E = n)
    (hF : finrank ℝ F = n) (oM : Orient I M n) (oN : Orient J N n) {f : M → N}
    (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y) :
    ∀ᶠ y' in 𝓝 y, degAt oM oN f y' = degAt oM oN f y :=
  hy.eventually_finsum_preimage_eq (hE.trans hF.symm) hf (by simp) fun x hx =>
    eventually_signAt_eq hE hF oM oN hf (hy x hx)

/-- The degree at a point outside the range is `0`. -/
theorem degAt_of_notMem_range (oM : Orient I M n) (oN : Orient J N n) {f : M → N} {y : N}
    (hy : y ∉ range f) : degAt oM oN f y = 0 := by
  have : f ⁻¹' {y} = ∅ := by
    ext x; simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    exact fun hx => hy ⟨x, hx⟩
  rw [degAt, this, finsum_mem_empty]

end Milnor
