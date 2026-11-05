import Milnor.Appendix.OneManifold
import Milnor.Chapter2.Boundary

/-!
# The boundary count for the manifolds with boundary of Chapter 2

`Milnor.OneManifold.even_ncard_boundary` is stated for an abstract charted space modelled on a
homeomorphic copy of `[0, ∞)`.  Here it is specialized to the half-slice submanifolds of
`Milnor.Chapter2.Boundary` (the output of Milnor's Lemma 4) whose model space `ℝ × Z` has `Z`
zero-dimensional, i.e. to compact 1-manifolds with boundary in the sense of the book.
-/

open Set
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- For a zero-dimensional `Z`, the half-space over `Z` is homeomorphic to `[0, ∞)`. -/
def halfSpaceHomeomorph [Subsingleton Z] : HalfSpace Z ≃ₜ Ici (0 : ℝ) where
  toFun h := ⟨h.1.1, h.2⟩
  invFun t := ⟨(t.1, 0), t.2⟩
  left_inv h := Subtype.ext (Prod.ext rfl (Subsingleton.elim _ _))
  right_inv t := Subtype.ext rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.prodMk continuous_const).subtype_mk _

@[simp] theorem halfSpaceHomeomorph_apply [Subsingleton Z] (h : HalfSpace Z) :
    ((halfSpaceHomeomorph h : Ici (0 : ℝ)) : ℝ) = h.1.1 := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The charted-space structure of a half-slice submanifold over a zero-dimensional `Z` is
boundary compatible in the sense of the Appendix: the boundary points are those sent to `0` by
every chart. -/
theorem IsHalfSliceSubmanifold.boundaryCompatible [Subsingleton Z] {X B : Set M}
    (hX : IsHalfSliceSubmanifold I Z X B) :
    letI := hX.chartedSpace
    OneManifold.BoundaryCompatible (M := X) (halfSpaceHomeomorph (Z := Z)) {q : X | q.1 ∈ B} := by
  letI := hX.chartedSpace
  rintro e ⟨σ, rfl⟩ q hq
  rw [HalfSliceChart.toChart_source] at hq
  show q.1 ∈ B ↔ _
  rw [σ.bdry q.1 hq]
  simp only [OneManifold.coord, halfSpaceHomeomorph_apply, σ.toChart_apply hq]

/-- **Milnor's Appendix, as used in the book.** A compact 1-manifold with boundary, presented as a
half-slice submanifold `X ⊆ M` with boundary `B` over a zero-dimensional `Z`, has an even (finite)
number of boundary points. -/
theorem IsHalfSliceSubmanifold.even_ncard_boundary [T2Space M] [Subsingleton Z] {X B : Set M}
    (hX : IsHalfSliceSubmanifold I Z X B) (hXc : IsCompact X) (hBX : B ⊆ X) :
    B.Finite ∧ Even B.ncard := by
  letI := hX.chartedSpace
  haveI : CompactSpace X := isCompact_iff_compactSpace.1 hXc
  have hB := hX.boundaryCompatible
  obtain ⟨hfin, heven⟩ := OneManifold.even_ncard_boundary (M := X) halfSpaceHomeomorph hB
  have himg : Subtype.val '' {q : X | q.1 ∈ B} = B := by
    ext y; constructor
    · rintro ⟨q, hq, rfl⟩; exact hq
    · intro hy; exact ⟨⟨y, hBX hy⟩, hy, rfl⟩
  rw [← himg]
  exact ⟨hfin.image _, by rw [Set.ncard_image_of_injective _ Subtype.val_injective]; exact heven⟩

/-- A zero-dimensional normed space is a subsingleton. -/
theorem subsingleton_of_finrank_eq_zero (hZ : Module.finrank ℝ Z = 0) [FiniteDimensional ℝ Z] :
    Subsingleton Z :=
  Module.finrank_zero_iff.1 hZ

end Milnor
