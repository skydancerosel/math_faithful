import Morse
import RoundTrip.Check
import RoundTrip.Blind.V4_17

open Module Set
open scoped ContDiff Manifold

namespace RoundTrip.V4_17

/-- The project's statement: the one listed theorem, universes instantiated at `0`. -/
def A : Prop := type_of% @Morse.exists_isMorseFunction_of_compactSpace.{0, 0}

theorem A_holds : A := @Morse.exists_isMorseFunction_of_compactSpace.{0, 0}

/-- **A ⇒ B**: A with `E = ℝⁿ`; on a compact space sublevel sets are closed, hence compact. -/
theorem A_to_B : A → B := by
  intro hA n M _ _ _ _ _ _
  obtain ⟨f, hf, -⟩ := hA (E := Rn n) (M := M)
  exact ⟨f, hf.contMDiff, fun q hq ↦ hf.isNondegenerateCriticalPointM hq,
    fun a ↦ (isClosed_le hf.contMDiff.continuous continuous_const).isCompact⟩

/-- **B ⇒ A.** Move `M` (model `E`) to a compact slice submanifold `N ⊆ ℝ^{K+1}` modelled on
`ℝⁿ` by the project's Whitney theorem `exists_diffeomorph_sliceSubmanifold` (V4_16; it also makes
`N` second countable, which B assumes and A does not), apply B on `N`, pull back along the
diffeomorphism (`IsMorseFunction.comp_diffeomorph_symm`); finiteness of the critical points from
the project's `IsMorseFunction.finite_setOf_isCriticalPointM` (isolated critical points). -/
theorem B_to_A : B → A := by
  intro hB E _ _ _ M _ _ _ _ _
  obtain ⟨K, m, N, hN, -, hNc, -, ⟨Φ⟩⟩ :=
    Morse.exists_diffeomorph_sliceSubmanifold (E := E) (M := M) (n := finrank ℝ E) rfl
  let _ := hN.chartedSpace
  have := hN.isManifold
  have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  obtain ⟨g, hg, hnd, -⟩ := hB (finrank ℝ E) N
  have hgM : Morse.IsMorseFunction (Rn (finrank ℝ E)) g := ⟨hg, fun q hq ↦ (hnd q hq).2⟩
  have hf := hgM.comp_diffeomorph_symm Φ.symm
  exact ⟨_, hf, hf.finite_setOf_isCriticalPointM⟩

#rt_check RoundTrip.V4_17.A_to_B [Morse.exists_isMorseFunction_of_compactSpace]
#rt_check RoundTrip.V4_17.B_to_A [Morse.exists_isMorseFunction_of_compactSpace]
#rt_overlap RoundTrip.V4_17.B_to_A [Morse.exists_isMorseFunction_of_compactSpace]

end RoundTrip.V4_17
