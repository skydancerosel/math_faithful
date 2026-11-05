import Milnor.Chapter6.Region

/-!
# Extension of a locally defined vector field

A vector field smooth on an open set `W` agrees, near any compact `K ⊆ W`, with a vector field
smooth on the whole space (multiply by a smooth cut-off function).  This lets us apply the
global statements about the index to vector fields defined only on open sets.
-/

open Set Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Extension by a cut-off.**  A map smooth on an open `W` agrees near a compact `K ⊆ W`
with a globally smooth map. -/
theorem exists_extension {v : E → F} {W : Set E} (hW : IsOpen W)
    (hv : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ v W) {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ w : E → F, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ w ∧ ∀ᶠ x in 𝓝ˢ K, w x = v x := by
  classical
  obtain ⟨V, hVo, hKV, hVW, -⟩ := exists_open_between_and_isCompact_closure hK hW hKW
  obtain ⟨χ, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E) (n := ⊤)
    hW.isClosed_compl isClosed_closure (disjoint_compl_left_iff.2 hVW)
  refine ⟨fun x => if x ∈ W then χ x • v x else 0, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ W
    · have h1 : (fun x => if x ∈ W then χ x • v x else 0) =ᶠ[𝓝 x] fun x => χ x • v x := by
        filter_upwards [hW.mem_nhds hx] with y hy
        rw [if_pos hy]
      refine ContMDiffAt.congr_of_eventuallyEq ?_ h1
      exact (χ.contMDiff.contMDiffAt).smul (hv.contMDiffAt (hW.mem_nhds hx))
    · have h1 : (fun x => if x ∈ W then χ x • v x else 0) =ᶠ[𝓝 x] fun _ => 0 := by
        have h2 : ∀ᶠ y in 𝓝 x, χ y = 0 := eventually_nhdsSet_iff_forall.1 hχ0 x hx
        filter_upwards [h2] with y hy
        by_cases hyW : y ∈ W
        · rw [if_pos hyW, hy, zero_smul]
        · rw [if_neg hyW]
      exact ContMDiffAt.congr_of_eventuallyEq contMDiffAt_const h1
  · have h1 : ∀ᶠ x in 𝓝ˢ K, x ∈ W := hW.mem_nhdsSet.2 hKW
    have h2 : ∀ᶠ x in 𝓝ˢ K, χ x = 1 :=
      nhdsSet_mono (hKV.trans subset_closure) hχ1
    filter_upwards [h1, h2] with x hx hχ
    rw [if_pos hx, hχ, one_smul]

end Milnor
