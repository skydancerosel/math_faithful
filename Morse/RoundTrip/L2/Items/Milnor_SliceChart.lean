import Morse
import RoundTrip.L2.Blind.Milnor_SliceChart

/-! Layer-2 check of `Milnor.SliceChart` against the blind textbook definition (the type of slice
charts: open partial homeomorphisms `φ : M → Z × W`, `C^∞` both ways, with
`φ(S ∩ U) = φ(U) ∩ (Z × {0})`).

The chart data agree: the project's `PartialDiffeomorph` is an open partial homeomorphism with
`ContMDiffOn` both ways, and its pointwise slice condition `p ∈ S ↔ (φ p).2 = 0` on the source is
equivalent to the image condition (`image_eq_iff`). But the project's structure also carries a
base point `x₀ ∈ S ∩ source` (documented in its docstring). So the project type is the type of
*pointed* slice charts, `Σ φ : T, ↥(φ.source ∩ S)` (`equiv`), not `T` itself; for `S = ∅` the
project type is empty while `T` contains the empty chart (`differ`). The difference is harmless:
the base point is extra data that never constrains the chart, and `IsSliceSubmanifold` (the only
consumer of existence) quantifies over charts around a point of `S`, which supplies it. -/

namespace RoundTrip.L2.Milnor_SliceChart

noncomputable section

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

/-- Forget the base point: a project slice chart gives a blind slice chart. -/
def toT {S : Set M} (σ : Milnor.SliceChart I Z W S) : T I Z W S :=
  ⟨σ.φ.toOpenPartialHomeomorph,
    σ.φ.contMDiffOn_toFun, σ.φ.contMDiffOn_invFun, (image_eq_iff _).2 σ.slice⟩

/-- A blind slice chart together with a point of `S` in its domain. -/
def ofT {S : Set M} (φ : T I Z W S) (x : ↥(φ.1.source ∩ S)) : Milnor.SliceChart I Z W S where
  φ := { toPartialEquiv := φ.1.toPartialEquiv
         open_source := φ.1.open_source
         open_target := φ.1.open_target
         contMDiffOn_toFun := φ.2.1
         contMDiffOn_invFun := φ.2.2.1 }
  x₀ := x.1
  x₀_mem := x.2.2
  x₀_source := x.2.1
  slice := (image_eq_iff φ.1).1 φ.2.2.2

/-- **The project's slice charts are the pointed blind slice charts.** -/
def equiv (I : ModelWithCorners ℝ E H) (Z W : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (S : Set M) :
    Milnor.SliceChart I Z W S ≃ Σ φ : T I Z W S, ↥(φ.1.source ∩ S) where
  toFun σ := ⟨toT σ, ⟨σ.x₀, σ.x₀_source, σ.x₀_mem⟩⟩
  invFun p := ofT p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- The forgetful map onto blind slice charts hits exactly the charts whose domain meets `S`. -/
theorem range_toT {S : Set M} :
    Set.range (toT (I := I) (Z := Z) (W := W) (S := S)) = {φ | (φ.1.source ∩ S).Nonempty} := by
  ext φ
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨σ.x₀, σ.x₀_source, σ.x₀_mem⟩
  · rintro ⟨x, hx⟩
    exact ⟨ofT φ ⟨x, hx⟩, rfl⟩

/-- The empty open partial homeomorphism `ℝ → ℝ × ℝ`. -/
def emptyChart : OpenPartialHomeomorph ℝ (ℝ × ℝ) where
  toFun _ := 0
  invFun _ := 0
  source := ∅
  target := ∅
  map_source' _ h := h.elim
  map_target' _ h := h.elim
  left_inv' _ h := h.elim
  right_inv' _ h := h.elim
  open_source := isOpen_empty
  open_target := isOpen_empty
  continuousOn_toFun := continuousOn_empty _
  continuousOn_invFun := continuousOn_empty _

/-- **They differ**: for `S = ∅` there are no project slice charts but the empty chart is a blind
one. -/
theorem differ :
    ¬ Nonempty (Milnor.SliceChart 𝓘(ℝ, ℝ) ℝ ℝ (∅ : Set ℝ) ≃ T 𝓘(ℝ, ℝ) ℝ ℝ (∅ : Set ℝ)) := by
  rintro ⟨e⟩
  have hT : IsSlice 𝓘(ℝ, ℝ) ℝ ℝ (∅ : Set ℝ) emptyChart :=
    ⟨contMDiffOn_empty, contMDiffOn_empty, by simp [emptyChart]⟩
  exact (e.symm ⟨emptyChart, hT⟩).x₀_mem

end

end RoundTrip.L2.Milnor_SliceChart
