import Morse
import RoundTrip.Check
import RoundTrip.Blind.V4_24

open Module Set
open scoped ContDiff Manifold

namespace RoundTrip.V4_24

/-- The project's statement: the one listed theorem, universes instantiated at `0`. -/
def A : Prop := type_of% @Morse.reeb_of_compactSpace.{0, 0}

theorem A_holds : A := @Morse.reeb_of_compactSpace.{0, 0}

/-- **A ⇒ B**: A with `E = ℝⁿ`. -/
theorem A_to_B : A → B := by
  intro hA n M _ _ _ _ _ f hf htwo hnd
  exact hA (E := Rn n) (M := M) finrank_euclideanSpace_fin hf htwo fun p hp ↦ (hnd p hp).2

/-- **B ⇒ A.** Move `M` (model `E`, `dim = n`) to a compact slice submanifold `N ⊆ ℝ^{K+1}`
modelled on `ℝⁿ` by the project's Whitney theorem `exists_diffeomorph_sliceSubmanifold` (V4_16),
transport `f` (critical points, their number and non-degeneracy are diffeomorphism invariant:
`ncard_setOf_isCriticalPointM_comp_symm`, `isNondegenerateCriticalPointM_comp_symm_iff`), apply
B on `N`, and compose the homeomorphisms. -/
theorem B_to_A : B → A := by
  intro hB E _ _ _ M _ _ _ _ _ n hn f hf htwo hnd
  obtain ⟨K, m, N, hN, -, hNc, -, ⟨Φ⟩⟩ :=
    Morse.exists_diffeomorph_sliceSubmanifold (E := E) (M := M) hn
  let _ := hN.chartedSpace
  have := hN.isManifold
  have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  have hg : ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ (f ∘ Φ.symm) := hf.comp Φ.symm.contMDiff
  have htwo' : {q : N | Morse.IsCriticalPointM (Rn n) (f ∘ Φ.symm) q}.ncard = 2 := by
    rw [Morse.ncard_setOf_isCriticalPointM_comp_symm Φ f, htwo]
  have hnd' : ∀ q : N, Morse.IsCriticalPointM (Rn n) (f ∘ Φ.symm) q →
      Morse.IsNondegenerateCriticalPointM (Rn n) (f ∘ Φ.symm) q := by
    intro q hq
    have hc := (Morse.isCriticalPointM_comp_symm_iff Φ).1 hq
    exact (Morse.isNondegenerateCriticalPointM_comp_symm_iff Φ
      (hf.contMDiffAt.of_le (by norm_cast))).2 ⟨hc, hnd _ hc⟩
  obtain ⟨h⟩ := hB n N (f ∘ Φ.symm) hg htwo' hnd'
  exact ⟨Φ.toHomeomorph.trans h⟩

#rt_check RoundTrip.V4_24.A_to_B [Morse.reeb_of_compactSpace]
#rt_check RoundTrip.V4_24.B_to_A [Morse.reeb_of_compactSpace]
#rt_overlap RoundTrip.V4_24.B_to_A [Morse.reeb_of_compactSpace]

end RoundTrip.V4_24
