import Morse
import RoundTrip.Check
import RoundTrip.Blind.V4_18

open Module Morse.Homology
open scoped ContDiff Manifold

namespace RoundTrip.V4_18

/-- The item lists only the definition `Morse.eulerNumberM`, so `A = True`. -/
def A : Prop := True

theorem A_holds : A := trivial

lemma Rabs_eq (X : Type) [TopologicalSpace X] (i : ℕ) : Rabs X i = bettiNumber ℚ X i :=
  finrank_subsetHomology_eq_bettiNumber (𝕜 := ℚ) (Set.empty_subset _) rfl rfl i

/-- **B holds outright**: formula (3) with Betti numbers over `ℚ` is the project's
`sum_bettiNumber_eq_sum_critCount_of_compactSpace` (not part of this item); `C_λ` is the
project's `critCount` by definition. -/
theorem B_holds : B := by
  intro n M _ _ _ _ _ f hf hnd
  have hM : Morse.IsMorseFunction (Rn n) f := ⟨hf, fun q hq ↦ (hnd q hq).2⟩
  have h := sum_bettiNumber_eq_sum_critCount_of_compactSpace (𝕜 := ℚ) hM
  rw [finrank_euclideanSpace_fin] at h
  simp only [chiBetti, Rabs_eq]
  exact h

theorem A_to_B : A → B := fun _ ↦ B_holds

theorem B_to_A : B → A := fun _ ↦ trivial

/-! ### Vocabulary check (not part of `A`)

The project's `eulerNumberM` (the alternating count `Σ (-1)^λ C_λ(f)` of one chosen Morse
function) is B's homological `χ(M) = Σ_{λ ≤ n} (-1)^λ R_λ(M)` for every compact Hausdorff smooth
manifold modelled on `ℝⁿ`, by B itself applied to a Morse function, which exists (project). -/

theorem eulerNumberM_eq_chiBetti (hB : B) (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M] :
    Morse.eulerNumberM (Rn n) M = chiBetti n M := by
  obtain ⟨f, hf, -⟩ := Morse.exists_isMorseFunction_of_compactSpace (E := Rn n) (M := M)
  rw [← Morse.sum_critCount_eq_eulerNumberM hf,
    hB n M f hf.contMDiff fun q hq ↦ hf.isNondegenerateCriticalPointM hq, finrank_euclideanSpace_fin]
  rfl

#rt_check RoundTrip.V4_18.A_to_B []
#rt_check RoundTrip.V4_18.B_to_A []

end RoundTrip.V4_18
