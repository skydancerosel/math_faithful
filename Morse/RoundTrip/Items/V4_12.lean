import Morse
import RoundTrip.Check
import RoundTrip.Blind.V4_12

open Module MeasureTheory
open scoped ContDiff Manifold

namespace RoundTrip.V4_12

/-- The project's statement: the four listed theorems; no universe parameters. -/
def A : Prop :=
  type_of% @Morse.mem_focalSet_of_not_isMorseFunction ∧
  type_of% @Morse.ae_isMorseFunction_normSq_sub ∧
  type_of% @Morse.ae_volume_isMorseFunction_normSq_sub ∧
  type_of% @Morse.exists_mem_isMorseFunction_normSq_sub

theorem A_holds : A :=
  ⟨@Morse.mem_focalSet_of_not_isMorseFunction, @Morse.ae_isMorseFunction_normSq_sub,
    @Morse.ae_volume_isMorseFunction_normSq_sub, @Morse.exists_mem_isMorseFunction_normSq_sub⟩

/-- **A ⇒ B**: A's `ae_volume_isMorseFunction_normSq_sub`, specialized. -/
theorem A_to_B : A → B := by
  intro hA K d m M hM
  let _ := hM.chartedSpace
  filter_upwards [hA.2.2.1 (hM := hM)] with p hp q hq
  exact hp.isNondegenerateCriticalPointM hq

/-- `L_p|M` is smooth, so it is a Morse function iff its critical points are non-degenerate. -/
theorem isMorse_iff {n k w : ℕ} {M : Set (Rn n)}
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn n) (Rn k) (Rn w) M) (p : Rn n) :
    letI := hM.chartedSpace
    Morse.IsMorseFunction (Rn k) (fun x : M => ‖(x : Rn n) - p‖ ^ 2) ↔
      ∀ q : M, Morse.IsCriticalPointM (Rn k) (fun x : M => ‖(x : Rn n) - p‖ ^ 2) q →
        Morse.IsNondegenerate (Morse.hessianM (Rn k) (fun x : M => ‖(x : Rn n) - p‖ ^ 2) q) := by
  let _ := hM.chartedSpace
  exact ⟨fun h ↦ h.isNondegenerate,
    fun h ↦ ⟨Morse.contMDiff_comp_val hM (Morse.contDiff_normSq_sub p), h⟩⟩

/-- B gives the volume statement for every `M` (dimension `0` and empty `M` separately). -/
theorem ae_volume_of_B (hB : B) {n k w : ℕ} {M : Set (Rn n)}
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn n) (Rn k) (Rn w) M) :
    letI := hM.chartedSpace
    ∀ᵐ p ∂(volume : Measure (Rn n)),
      Morse.IsMorseFunction (Rn k) (fun x : M => ‖(x : Rn n) - p‖ ^ 2) := by
  let _ := hM.chartedSpace
  simp only [isMorse_iff hM]
  rcases M.eq_empty_or_nonempty with he | hne
  · subst he
    exact Filter.Eventually.of_forall fun p q ↦ absurd q.2 (Set.notMem_empty _)
  rcases k with _ | d
  · exact Filter.Eventually.of_forall fun p q _ ↦ Subsingleton.elim _ _
  have hkw := Morse.slice_dim_add_eq_of_nonempty hM hne
  obtain ⟨K, rfl⟩ : ∃ K, n = K + 1 := ⟨d + w, by omega⟩
  filter_upwards [hB K d w M hM] with p hp q hq
  exact (hp q hq).2

/-- **B ⇒ A.** The measure clauses come from B (volume; any Haar measure is absolutely continuous
with respect to it; dimension `0` and empty `M` are trivial); the dense-existence clause from
them. The clause `mem_focalSet_of_not_isMorseFunction` is not in B (B has no focal points): it is
re-proved from the project's `isDegenerate_normSq_sub_iff_isFocalPoint` (Lemma 6.5, V4_11). -/
theorem B_to_A : B → A := by
  intro hB
  have hvol := @ae_volume_of_B hB
  have hμ : type_of% @Morse.ae_isMorseFunction_normSq_sub := by
    intro n k w M hM μ _
    exact (Measure.absolutelyContinuous_isAddHaarMeasure μ volume).ae_le (hvol hM)
  refine ⟨?_, hμ, fun {n k w M hM} ↦ hvol hM, ?_⟩
  · intro n k w M hM hkw p hp
    let _ := hM.chartedSpace
    rw [isMorse_iff hM] at hp
    push_neg at hp
    obtain ⟨q, hc, hn⟩ := hp
    exact ⟨q, (Morse.isDegenerate_normSq_sub_iff_isFocalPoint hkw p q).1 ⟨hc, hn⟩⟩
  · intro n k w M hM U hU hne
    let _ := hM.chartedSpace
    by_contra hcon
    push_neg at hcon
    have h0 : volume U = 0 := by
      refine measure_mono_null (fun p hp ↦ ?_) (ae_iff.1 (hvol hM))
      exact hcon p hp
    exact (hU.measure_pos volume hne).ne' h0

#rt_check RoundTrip.V4_12.A_to_B [Morse.mem_focalSet_of_not_isMorseFunction,
  Morse.ae_isMorseFunction_normSq_sub, Morse.ae_volume_isMorseFunction_normSq_sub,
  Morse.exists_mem_isMorseFunction_normSq_sub]
#rt_check RoundTrip.V4_12.B_to_A [Morse.mem_focalSet_of_not_isMorseFunction,
  Morse.ae_isMorseFunction_normSq_sub, Morse.ae_volume_isMorseFunction_normSq_sub,
  Morse.exists_mem_isMorseFunction_normSq_sub]
#rt_overlap RoundTrip.V4_12.B_to_A [Morse.mem_focalSet_of_not_isMorseFunction,
  Morse.ae_isMorseFunction_normSq_sub, Morse.ae_volume_isMorseFunction_normSq_sub,
  Morse.exists_mem_isMorseFunction_normSq_sub]

end RoundTrip.V4_12
