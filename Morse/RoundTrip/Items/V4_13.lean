import Morse
import RoundTrip.Check
import RoundTrip.Blind.V4_13

open Module MeasureTheory Set
open scoped ContDiff Manifold

namespace RoundTrip.V4_13

/-- The project's statement: the five listed theorems; no universe parameters. -/
def A : Prop :=
  type_of% @Morse.isCompact_sublevel_normSq_sub ∧
  type_of% @Morse.ae_isMorseFunction_normSq_sub_and_isCompact_sublevel ∧
  type_of% @Morse.exists_isMorseFunction_isCompact_sublevel ∧
  type_of% @Morse.exists_isMorseFunction_finite_critPoints_sublevel ∧
  type_of% @Morse.exists_isMorseFunction_finite_critPoints

theorem A_holds : A :=
  ⟨@Morse.isCompact_sublevel_normSq_sub, @Morse.ae_isMorseFunction_normSq_sub_and_isCompact_sublevel,
    @Morse.exists_isMorseFunction_isCompact_sublevel,
    @Morse.exists_isMorseFunction_finite_critPoints_sublevel,
    @Morse.exists_isMorseFunction_finite_critPoints⟩

/-- **A ⇒ B**: A's `exists_isMorseFunction_isCompact_sublevel`. -/
theorem A_to_B : A → B := by
  intro hA K d m M hM hcl
  let _ := hM.chartedSpace
  obtain ⟨f, hf, hc⟩ := hA.2.2.1 hM hcl
  exact ⟨f, hf.contMDiff, fun q hq ↦ hf.isNondegenerateCriticalPointM hq, hc⟩

/-- B, extended to every slice submanifold `M ⊆ ℝⁿ` (dimension `0` by `L_p`; empty `M`), in A's
form. -/
theorem exists_of_B (hB : B) {n k w : ℕ} {M : Set (Rn n)}
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn n) (Rn k) (Rn w) M) (hcl : IsClosed M) :
    letI := hM.chartedSpace
    ∃ f : M → ℝ, Morse.IsMorseFunction (Rn k) f ∧ ∀ a : ℝ, IsCompact (f ⁻¹' Iic a) := by
  let _ := hM.chartedSpace
  have hLp : ∀ a, IsCompact ((fun x : M => ‖(x : Rn n) - 0‖ ^ 2) ⁻¹' Iic a) := fun a ↦
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (Morse.isCompact_setOf_normSq_sub_le 0 a)
  have hsm := Morse.contMDiff_comp_val hM (Morse.contDiff_normSq_sub (0 : Rn n))
  rcases M.eq_empty_or_nonempty with he | hne
  · subst he
    exact ⟨_, ⟨hsm, fun q ↦ absurd q.2 (Set.notMem_empty _)⟩, hLp⟩
  rcases k with _ | d
  · exact ⟨_, ⟨hsm, fun _ _ ↦ Subsingleton.elim _ _⟩, hLp⟩
  have hkw := Morse.slice_dim_add_eq_of_nonempty hM hne
  obtain ⟨K, rfl⟩ : ∃ K, n = K + 1 := ⟨d + w, by omega⟩
  obtain ⟨f, hf, hnd, hc⟩ := hB K d w M hM hcl
  exact ⟨f, ⟨hf, fun q hq ↦ (hnd q hq).2⟩, hc⟩

/-- **B ⇒ A.** The existence clauses (3)–(5) come from B (extended to dimension `0` / empty `M`),
with the project's `IsMorseFunction.finite_inter_setOf_isCriticalPointM` (critical points of a
Morse function are isolated) for the finiteness parts. Clauses (1)–(2) are not existence
statements and are re-proved without B: (1) is elementary (closed embedding, closed balls), (2)
is the project's `ae_isMorseFunction_normSq_sub` (Theorem 6.6, V4_12) plus (1). -/
theorem B_to_A : B → A := by
  intro hB
  have h1 : type_of% @Morse.isCompact_sublevel_normSq_sub := fun {n M} hcl p a ↦
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (Morse.isCompact_setOf_normSq_sub_le p a)
  have h3 : type_of% @Morse.exists_isMorseFunction_isCompact_sublevel :=
    fun {n k w M} hM hcl ↦ exists_of_B hB hM hcl
  refine ⟨h1, ?_, h3, ?_, ?_⟩
  · intro n k w M hM hcl μ _
    let _ := hM.chartedSpace
    filter_upwards [Morse.ae_isMorseFunction_normSq_sub (hM := hM) μ] with p hp
    exact ⟨hp, fun a ↦ h1 hcl p a⟩
  · intro n k w M hM hcl
    let _ := hM.chartedSpace
    have := hM.isManifold
    obtain ⟨f, hf, hc⟩ := h3 hM hcl
    exact ⟨f, hf, fun a ↦ ⟨hc a, hf.finite_inter_setOf_isCriticalPointM (hc a)⟩⟩
  · intro n k w M hM hcpt
    let _ := hM.chartedSpace
    have := hM.isManifold
    have : CompactSpace M := isCompact_iff_compactSpace.1 hcpt
    obtain ⟨f, hf, -⟩ := h3 hM hcpt.isClosed
    exact ⟨f, hf, hf.finite_setOf_isCriticalPointM⟩

#rt_check RoundTrip.V4_13.A_to_B [Morse.isCompact_sublevel_normSq_sub,
  Morse.ae_isMorseFunction_normSq_sub_and_isCompact_sublevel,
  Morse.exists_isMorseFunction_isCompact_sublevel,
  Morse.exists_isMorseFunction_finite_critPoints_sublevel,
  Morse.exists_isMorseFunction_finite_critPoints]
#rt_check RoundTrip.V4_13.B_to_A [Morse.isCompact_sublevel_normSq_sub,
  Morse.ae_isMorseFunction_normSq_sub_and_isCompact_sublevel,
  Morse.exists_isMorseFunction_isCompact_sublevel,
  Morse.exists_isMorseFunction_finite_critPoints_sublevel,
  Morse.exists_isMorseFunction_finite_critPoints]
#rt_overlap RoundTrip.V4_13.B_to_A [Morse.isCompact_sublevel_normSq_sub,
  Morse.ae_isMorseFunction_normSq_sub_and_isCompact_sublevel,
  Morse.exists_isMorseFunction_isCompact_sublevel,
  Morse.exists_isMorseFunction_finite_critPoints_sublevel,
  Morse.exists_isMorseFunction_finite_critPoints]

end RoundTrip.V4_13
