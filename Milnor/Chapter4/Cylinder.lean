import Milnor.Chapter2.WithBoundary

/-!
# Lemma 4 with two boundary components

Milnor's Lemma 4 produces the manifold with boundary `f⁻¹(y) ∩ {g ≥ 0}`.  The cylinder
`M × [0,1]` of §4 is `{g₀ ≥ 0} ∩ {g₁ ≥ 0}` for the two functions `g₀ = t`, `g₁ = 1 - t`, whose
zero sets are disjoint.  Since the half-slice condition is local, the structure on
`f⁻¹(y) ∩ {g₀ ≥ 0} ∩ {g₁ ≥ 0}` is obtained from Lemma 4 for `g₀` on the open set `{g₁ > 0}` and
from Lemma 4 for `g₁` on `{g₀ > 0}`.
-/

open Set Module
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

/-- Restricting a half-slice chart to an open set on which the two descriptions of `X` and `B`
agree with new ones. -/
theorem IsHalfSliceSubmanifold.of_local {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {X B X' B' : Set M'} (hX : IsHalfSliceSubmanifold I' Z X B) {U : Set M'} (hU : IsOpen U)
    (hXU : ∀ p ∈ U, p ∈ X' ↔ p ∈ X) (hBU : ∀ p ∈ U, p ∈ B' ↔ p ∈ B) {q : M'} (hq : q ∈ X')
    (hqU : q ∈ U) : ∃ σ : HalfSliceChart I' Z X' B', q ∈ σ.Φ.source := by
  obtain ⟨σ, hσ⟩ := hX q ((hXU q hqU).1 hq)
  refine ⟨⟨σ.Φ.restrOpen U hU, q, hq, ⟨hσ, hqU⟩, ?_, ?_⟩, ⟨hσ, hqU⟩⟩
  · intro p hp
    rw [hXU p hp.2, PartialDiffeomorph.restrOpen_apply]
    exact σ.half p hp.1
  · intro p hp
    rw [hBU p hp.2, PartialDiffeomorph.restrOpen_apply]
    exact σ.bdry p hp.1

/-- **Lemma 4 with two boundary functions.** -/
theorem isHalfSliceSubmanifold_levelSet_two {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (hZ : finrank ℝ Z + finrank ℝ F = finrank ℝ E)
    {Z' : Type*} [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] [FiniteDimensional ℝ Z']
    (hZ' : finrank ℝ Z' + 1 = finrank ℝ Z)
    {f : M → N} (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y)
    {g₀ g₁ : M → ℝ} (hg₀ : ContMDiff I 𝓘(ℝ, ℝ) ∞ g₀) (hg₁ : ContMDiff I 𝓘(ℝ, ℝ) ∞ g₁)
    (hreg₀ : ∀ x, f x = y → g₀ x = 0 →
      ∃ v, mfderiv I J f x v = 0 ∧ mfderiv I 𝓘(ℝ, ℝ) g₀ x v ≠ 0)
    (hreg₁ : ∀ x, f x = y → g₁ x = 0 →
      ∃ v, mfderiv I J f x v = 0 ∧ mfderiv I 𝓘(ℝ, ℝ) g₁ x v ≠ 0)
    (hdisj : ∀ x, f x = y → ¬ (g₀ x = 0 ∧ g₁ x = 0)) :
    letI := (isSliceSubmanifold_preimage hZ hf hy).chartedSpace
    IsHalfSliceSubmanifold 𝓘(ℝ, Z) Z' {q : f ⁻¹' {y} | 0 ≤ g₀ q.1 ∧ 0 ≤ g₁ q.1}
      {q | g₀ q.1 = 0 ∨ g₁ q.1 = 0} := by
  set hS := isSliceSubmanifold_preimage hZ hf hy
  letI := hS.chartedSpace
  haveI := hS.isManifold
  have hX₀ := isHalfSliceSubmanifold_levelSet hZ hZ' hf hy hg₀ hreg₀
  have hX₁ := isHalfSliceSubmanifold_levelSet hZ hZ' hf hy hg₁ hreg₁
  have hcont : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ (g₀ ∘ (Subtype.val : f ⁻¹' {y} → M)) :=
    hg₀.comp hS.contMDiff_val
  have hcont' : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ (g₁ ∘ (Subtype.val : f ⁻¹' {y} → M)) :=
    hg₁.comp hS.contMDiff_val
  intro q hq
  have hq0 : 0 ≤ g₀ q.1 := hq.1
  have hq1 : 0 ≤ g₁ q.1 := hq.2
  have hqy : f q.1 = y := q.2
  by_cases h1 : 0 < g₁ q.1
  · -- use the charts for `g₀` on the open set `{g₁ > 0}`
    have hU : IsOpen {p : f ⁻¹' {y} | 0 < g₁ p.1} :=
      isOpen_lt continuous_const hcont'.continuous
    refine IsHalfSliceSubmanifold.of_local hX₀ hU ?_ ?_ hq h1
    · intro p hp
      have hp' : 0 < g₁ p.1 := hp
      exact Iff.intro (fun h => h.1) (fun h => ⟨h, le_of_lt hp'⟩)
    · intro p hp
      have hp' : 0 < g₁ p.1 := hp
      exact Iff.intro (fun h => h.resolve_right (ne_of_gt hp')) (fun h => Or.inl h)
  · have h1' : g₁ q.1 = 0 := le_antisymm (not_lt.1 h1) hq1
    have h0 : 0 < g₀ q.1 :=
      lt_of_le_of_ne hq0 fun h => hdisj q.1 hqy ⟨h.symm, h1'⟩
    have hU : IsOpen {p : f ⁻¹' {y} | 0 < g₀ p.1} :=
      isOpen_lt continuous_const hcont.continuous
    refine IsHalfSliceSubmanifold.of_local hX₁ hU ?_ ?_ hq h0
    · intro p hp
      have hp' : 0 < g₀ p.1 := hp
      exact Iff.intro (fun h => h.2) (fun h => ⟨le_of_lt hp', h⟩)
    · intro p hp
      have hp' : 0 < g₀ p.1 := hp
      exact Iff.intro (fun h => h.resolve_left (ne_of_gt hp')) (fun h => Or.inr h)

end Milnor
