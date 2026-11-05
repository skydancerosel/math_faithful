import Milnor.Chapter2.Submanifold

/-!
# Corestriction to a slice submanifold

A smooth map into `M` whose values lie in a slice submanifold `S ⊆ M` is smooth as a map into
`S` (with the manifold structure of `Milnor.IsSliceSubmanifold.chartedSpace`).  Milnor uses this
silently whenever he regards a map into `∂X ⊆ X` as a map into the manifold `∂X` (§2, Lemma 5).
-/

open Set
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

namespace IsSliceSubmanifold

variable {S : Set M} (hS : IsSliceSubmanifold I Z W S)

/-- The chart of the slice submanifold at `p`, as an extended chart, is the slice chart chosen at
`p`. -/
theorem extChartAt_eq (p : S) :
    letI := hS.chartedSpace
    extChartAt 𝓘(ℝ, Z) p = (hS p.1 p.2).choose.toChart.toPartialEquiv := by
  letI := hS.chartedSpace
  rw [extChartAt, hS.chartAt_eq, OpenPartialHomeomorph.extend,
    modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl]

/-- **Corestriction.** A smooth map `F : M' → M` with values in `S` is smooth as a map into `S`. -/
theorem contMDiff_codRestrict {F : M' → M} (hF : ContMDiff I' I ∞ F) (hFS : ∀ x, F x ∈ S) :
    letI := hS.chartedSpace
    ContMDiff I' 𝓘(ℝ, Z) ∞ (fun x => (⟨F x, hFS x⟩ : S)) := by
  letI := hS.chartedSpace
  haveI := hS.isManifold
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨(hF.continuous.subtype_mk _).continuousAt, ?_⟩
  set σ := (hS (F x) (hFS x)).choose with hσ
  have hmem : F x ∈ σ.φ.source := (hS (F x) (hFS x)).choose_spec
  have hchart : extChartAt 𝓘(ℝ, Z) (⟨F x, hFS x⟩ : S) = σ.toChart.toPartialEquiv :=
    hS.extChartAt_eq ⟨F x, hFS x⟩
  rw [hchart]
  have hφ : ContMDiffAt I 𝓘(ℝ, Z × W) ∞ σ.φ (F x) :=
    (σ.φ.contMDiffOn (F x) hmem).contMDiffAt (σ.φ.open_source.mem_nhds hmem)
  have h1 : ContMDiffAt I' 𝓘(ℝ, Z × W) ∞ (σ.φ ∘ F) x := hφ.comp x (hF x)
  have hfst : ContMDiff 𝓘(ℝ, Z × W) 𝓘(ℝ, Z) ∞ (Prod.fst : Z × W → Z) :=
    (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Z × W → Z)).contMDiff
  have h2 : ContMDiffAt I' 𝓘(ℝ, Z) ∞ (Prod.fst ∘ (σ.φ ∘ F)) x := hfst.contMDiffAt.comp x h1
  exact h2

end IsSliceSubmanifold

end Milnor
