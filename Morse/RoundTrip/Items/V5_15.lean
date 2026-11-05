import Morse
import RoundTrip.Check
import RoundTrip.Blind.V5_15

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace
open Morse.Homology

namespace RoundTrip.V5_15

/-- The project's statement (Theorem 7.2): a closed slice submanifold `M ⊆ 𝔼 n` of dimension `2k`
with `J`-invariant tangent spaces has the homotopy type of a countable cell complex of the project
(`Morse.IsCountableCellComplexType`: homotopy equivalent to a mapping telescope of iterated
adjunction spaces) with all cells of dimension `≤ k`. -/
def A : Prop := type_of% @Morse.theorem_7_2

theorem A_holds : A := @Morse.theorem_7_2

/-- Everything of B except the passage to a Mathlib `CWComplex`, from A: the cell tower of A, after
fixing the model dimension `d + 1 = 2k` and converting B's isometry `J` into a CLM. -/
theorem A_cells {K d m k : ℕ} (hA : A) (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)
    (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)) (hJ : IsCplxStr J) (hc : IsCplxSub hM J)
    (hcl : IsClosed M) (hdk : d + 1 = 2 * k) :
    ∃ cells : ℕ → List ℕ, Morse.IsCountableCellComplexType M cells ∧ ∀ i, ∀ e ∈ cells i, e ≤ k := by
  have key : ∀ {D : ℕ} (hM' : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn D) (Rn m) M),
      Morse.IsComplexSubmanifold hM' (J.toContinuousLinearEquiv : Rn (K + 1) →L[ℝ] Rn (K + 1)) →
      D = 2 * k →
      ∃ cells : ℕ → List ℕ, Morse.IsCountableCellComplexType M cells ∧ ∀ i, ∀ e ∈ cells i, e ≤ k := by
    intro D hM' hc' hD
    subst hD
    exact hA hM' hcl ⟨fun v => hJ v, fun v w => J.inner_map_map v w⟩ hc'
  exact key hM (fun q v hv => hc q v hv) hdk

/-- B ⇒ A holds only vacuously: A is re-proved outright by the project's own argument
(Lemma 6.6 for a Morse `L_p`, compact sublevels, regular levels, Theorem 3.5 slab by slab, the
mapping telescope, and the index bound `Morse.indexM_normSq_sub_le`). B (a Mathlib CW complex)
cannot be turned into the project's mapping-telescope cell type. -/
theorem B_to_A : B → A := by
  intro _ n k w M hM hcl J hJ hc
  classical
  let _ := hM.chartedSpace
  obtain ⟨p, hp⟩ := Morse.exists_isMorseFunction_normSq_sub (hM := hM)
  set F : EuclideanSpace ℝ (Fin n) → ℝ := fun y => ‖y - p‖ ^ 2 with hF_def
  have hF : ContDiff ℝ ∞ F := Morse.contDiff_normSq_sub p
  have hK : ∀ a, IsCompact ((F ∘ Subtype.val : M → ℝ) ⁻¹' Iic a) :=
    fun a => Morse.isCompact_sublevel_normSq_sub hcl p a
  obtain ⟨a, ha0, ha, ha', hreg⟩ := Morse.exists_regular_levels hM hF hK hp.isNondegenerate
    fun _ => sq_nonneg _
  have hstep : ∀ m, ∃ ps : List M, (∀ q ∈ ps,
      Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin (2 * k))) (F ∘ Subtype.val) q) ∧
      Morse.IsRelCellComplexType
        (Morse.inclC (Morse.sublevel_mono (F ∘ Subtype.val : M → ℝ) (ha (Nat.le_succ m))))
        (ps.map (Morse.indexM (EuclideanSpace ℝ (Fin (2 * k))) (F ∘ Subtype.val))) := fun m => by
    obtain ⟨ps, -, hmem, -, hcell⟩ := Morse.isRelCellComplexType_sublevel_of_isCompact hM hF
      (hK (a (m + 1))) (fun q hq _ => hp.isNondegenerate q hq) (ha (Nat.le_succ m))
      (fun q hq => hreg m q hq) (fun q hq => hreg (m + 1) q hq)
    exact ⟨ps, fun q hq => ((hmem q).1 hq).1, hcell⟩
  choose ps hps hcell using hstep
  let cells : ℕ → List ℕ := fun m => match m with
    | 0 => []
    | m + 1 => (ps m).map (Morse.indexM (EuclideanSpace ℝ (Fin (2 * k))) (F ∘ Subtype.val))
  let E : C(M, ℝ) := ⟨F ∘ Subtype.val, hF.continuous.comp continuous_subtype_val⟩
  refine ⟨cells, Morse.isCountableCellComplexType_of_relSublevel E ha ha' ?_ fun m => hcell m, ?_⟩
  · have : IsEmpty ↥(Morse.sublevel E (a 0)) := ⟨fun x => by
      have h1 : F x.1 ≤ a 0 := x.2
      have := sq_nonneg ‖(x.1 : EuclideanSpace ℝ (Fin n)) - p‖
      linarith⟩
    exact Morse.IsFiniteCellComplexType.of_isEmpty _
  · rintro (_ | m) d hd
    · simp [cells] at hd
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hd
      exact Morse.indexM_normSq_sub_le hM hJ hc p q (hps m q hq)

#rt_check RoundTrip.V5_15.B_to_A [Morse.theorem_7_2]
#rt_check RoundTrip.V5_15.A_cells [Morse.theorem_7_2]
#rt_overlap RoundTrip.V5_15.B_to_A [Morse.theorem_7_2]

/-! A ⇒ B is not proved: `A_cells` gives B's setting the project's countable cell tower
(`IsCountableCellComplexType`, a mapping telescope of iterated adjunction spaces with arbitrary
attaching maps) with all cells of dimension `≤ k`; B asks for a Mathlib `CWComplex` with no cells
above `k`, which needs cellular approximation (absent from Mathlib and the project). -/

end RoundTrip.V5_15
