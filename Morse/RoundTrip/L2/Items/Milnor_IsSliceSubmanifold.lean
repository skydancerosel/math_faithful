import Morse
import RoundTrip.L2.Blind.Milnor_IsSliceSubmanifold

/-! Layer-2 check of `Milnor.IsSliceSubmanifold` against the blind textbook definition (every point
of `S` lies in the domain of a slice chart: an open partial homeomorphism `φ : M → Z × W`, `C^∞`
both ways, with `φ(S ∩ U) = φ(U) ∩ (Z × {0})`). The project's `SliceChart` is a
`PartialDiffeomorph` (the same data: an open partial homeomorphism with `ContMDiffOn` both ways)
with the pointwise slice condition `p ∈ S ↔ (φ p).2 = 0` on the source (equivalent to the image
condition, `isSlice_iff`) and a base point `x₀ ∈ S ∩ source`, which is supplied by the point
itself. Equal for all arguments. -/

namespace RoundTrip.L2.Milnor_IsSliceSubmanifold

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedSpace ℝ Z] [NormedSpace ℝ W] in
/-- The image form of the slice condition is the pointwise one. -/
theorem image_eq_iff {S : Set M} (φ : OpenPartialHomeomorph M (Z × W)) :
    φ '' (φ.source ∩ S) = φ.target ∩ {x | x.2 = 0} ↔ ∀ p ∈ φ.source, p ∈ S ↔ (φ p).2 = 0 := by
  constructor
  · intro h p hp
    constructor
    · intro hpS
      have : φ p ∈ φ.target ∩ {x | x.2 = 0} := h ▸ Set.mem_image_of_mem _ ⟨hp, hpS⟩
      exact this.2
    · intro h0
      have : φ p ∈ φ '' (φ.source ∩ S) := h ▸ ⟨φ.map_source hp, h0⟩
      obtain ⟨p', ⟨hp', hp'S⟩, hpp'⟩ := this
      rwa [← φ.injOn hp' hp hpp']
  · intro h
    ext x
    constructor
    · rintro ⟨p, ⟨hp, hpS⟩, rfl⟩
      exact ⟨φ.map_source hp, (h p hp).1 hpS⟩
    · rintro ⟨hx, hx0⟩
      refine ⟨φ.symm x, ⟨φ.map_target hx, (h _ (φ.map_target hx)).2 ?_⟩, φ.right_inv hx⟩
      rw [φ.right_inv hx]
      exact hx0

/-- The open partial homeomorphism underlying a project slice chart is a blind slice chart. -/
theorem isSlice_of_sliceChart {S : Set M} (σ : Milnor.SliceChart I Z W S) :
    IsSlice I Z W S σ.φ.toOpenPartialHomeomorph :=
  ⟨σ.φ.contMDiffOn_toFun, σ.φ.contMDiffOn_invFun, (image_eq_iff _).2 σ.slice⟩

/-- A blind slice chart with a point of `S` in its domain gives a project slice chart. -/
def sliceChartOf {S : Set M} (φ : OpenPartialHomeomorph M (Z × W)) (hφ : IsSlice I Z W S φ)
    (x : M) (hx : x ∈ φ.source) (hxS : x ∈ S) : Milnor.SliceChart I Z W S where
  φ := { toPartialEquiv := φ.toPartialEquiv
         open_source := φ.open_source
         open_target := φ.open_target
         contMDiffOn_toFun := hφ.1
         contMDiffOn_invFun := hφ.2.1 }
  x₀ := x
  x₀_mem := hxS
  x₀_source := hx
  slice := (image_eq_iff φ).1 hφ.2.2

theorem agree (I : ModelWithCorners ℝ E H) (Z W : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (S : Set M) :
    Milnor.IsSliceSubmanifold I Z W S ↔ T I Z W S := by
  constructor
  · intro h x hx
    obtain ⟨σ, hσ⟩ := h x hx
    exact ⟨σ.φ.toOpenPartialHomeomorph, isSlice_of_sliceChart σ, hσ⟩
  · intro h x hx
    obtain ⟨φ, hφ, hxφ⟩ := h x hx
    exact ⟨sliceChartOf φ hφ x hxφ hx, hxφ⟩

end RoundTrip.L2.Milnor_IsSliceSubmanifold
