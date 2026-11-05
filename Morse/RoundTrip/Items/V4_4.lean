import Morse
import RoundTrip.Check
import RoundTrip.Blind.V4_4

open Module Function MeasureTheory
open scoped ContDiff Manifold

namespace RoundTrip.V4_4

/-- The project's statement: the one listed theorem; no universe parameters. -/
def A : Prop := type_of% @Morse.measure_focalSet_eq_zero

theorem A_holds : A := @Morse.measure_focalSet_eq_zero

/-- For an endomorphism of `ℝⁿ`: nontrivial kernel ↔ not surjective. -/
lemma finrank_ker_pos_iff {n : ℕ} (L : Rn n →L[ℝ] Rn n) :
    0 < finrank ℝ (LinearMap.ker (L : Rn n →ₗ[ℝ] Rn n)) ↔ ¬ Surjective L := by
  have : Surjective L ↔ Surjective (L : Rn n →ₗ[ℝ] Rn n) := Iff.rfl
  rw [this, ← LinearMap.injective_iff_surjective, Nat.pos_iff_ne_zero, Ne,
    Submodule.finrank_eq_zero, LinearMap.ker_eq_bot]

/-- **B holds outright**, for every slice structure `hNN` on `N`: a focal point is a critical value
of `E|N` (rank–nullity), and these are null by the project's Sard theorem on a manifold
`Morse.measure_image_critPoints_eq_zero` (not a listed theorem). -/
theorem B_holds : B := by
  intro K d m M hM hNN
  let _ := hNN.chartedSpace
  have := hNN.isManifold
  have hE : ContMDiff 𝓘(ℝ, Rn (K + 1)) 𝓘(ℝ, Rn (K + 1)) ∞ (fun x : NSet hM => endpt x.1) :=
    (contDiff_fst.add contDiff_snd).contMDiff.comp hNN.contMDiff_val
  have hnull := Morse.measure_image_critPoints_eq_zero volume hE
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro e he
  simp only [not_not, Set.mem_ofPred_eq] at he
  obtain ⟨q, μ, hμ, hnull⟩ := he
  have hmem : (q, e - q) ∈ NSet hM := by
    by_contra h
    simp [nullE, h] at hnull
    omega
  rw [nullE, dif_pos hmem] at hnull
  exact ⟨⟨(q, e - q), hmem⟩, (finrank_ker_pos_iff _).1 (hnull ▸ hμ), by simp [endpt]⟩

/-- A ⇒ B: B is true outright (`B_holds`); A is not needed. -/
theorem A_to_B : A → B := fun _ ↦ B_holds

/-- B ⇒ A, by re-proving A outright from the project's Sard theorem and
`focalSet_eq_image_critPoints` (neither listed here). B, which concerns an arbitrary slice
structure on `N ⊆ ℝ^{K+1} × ℝ^{K+1}` (complement `ℝ^{K+1}`, `dim M ≥ 1`), is not used: moving it
to the project's canonical structure would need uniqueness of the smooth structure of an embedded
submanifold. -/
theorem B_to_A : B → A := by
  intro _ n k w M hM hkw μ _
  have hN := Milnor.Problems.isSliceSubmanifold_normalBundle hM hkw
  let := hN.chartedSpace
  have := hN.isManifold
  rw [Morse.focalSet_eq_image_critPoints hM hkw]
  exact Morse.measure_image_critPoints_eq_zero μ (Milnor.Problems.contMDiff_normalSum hM hkw)

#rt_check RoundTrip.V4_4.A_to_B [Morse.measure_focalSet_eq_zero]
#rt_check RoundTrip.V4_4.B_to_A [Morse.measure_focalSet_eq_zero]
#rt_overlap RoundTrip.V4_4.B_to_A [Morse.measure_focalSet_eq_zero]

end RoundTrip.V4_4
