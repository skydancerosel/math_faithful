import Morse
import RoundTrip.Check
import RoundTrip.Blind.V9_13

open Set Module

namespace RoundTrip.V9_13

/-- The project's statement (universes instantiated at `0`): the defining property of
`Morse.formIndex` (every finite dimensional negative definite subspace has dimension `≤` the
index), monotonicity of the index under form-preserving linear maps, and, on a finite dimensional
space, `formIndex = sigNeg`. The definitions `Morse.IsNegDefOn`, `Morse.formIndex` are vocabulary;
the project has no separate notion of nullity in this item. -/
def A : Prop :=
  type_of% @Morse.le_formIndex.{0} ∧ type_of% @Morse.formIndex_le_of_map.{0, 0} ∧
    type_of% @Morse.formIndex_eq_sigNeg.{0}

theorem A_holds : A :=
  ⟨@Morse.le_formIndex, @Morse.formIndex_le_of_map, @Morse.formIndex_eq_sigNeg⟩

/-- The index of a form on the empty set is `0` (no subspace is contained in `∅`). -/
theorem bIndex_empty {V : Type} [AddCommGroup V] [Module ℝ V] (H : V → V → ℝ) :
    bIndex (∅ : Set V) H = 0 := by
  refine le_antisymm (iSup₂_le fun S hS => ?_) zero_le
  exact absurd (hS.1 S.zero_mem) (Set.notMem_empty _)

/-- **`B` is false**: its second clause ("if the index is finite it is attained") quantifies over
arbitrary sets `A ⊆ V`; for `A = ∅` the index is `0` (empty supremum) but no subspace lies in `∅`.
(Milnor's `A = TΩ_γ` is a vector space; the clause holds as soon as `0 ∈ A`, see `B_sub_holds`.) -/
theorem not_B : ¬ B := by
  intro hB
  obtain ⟨S, hS, -⟩ := (hB ℝ (∅ : Set ℝ) (fun _ _ => 0)).2.1 (by simp [bIndex_empty])
  exact absurd (hS S.zero_mem) (Set.notMem_empty _)

theorem B_to_A : B → A := fun h => (not_B h).elim

/-! ### The corrected statement: `A` a subspace -/

/-- `B` with the set `A` a subspace (as Milnor's `TΩ_γ` is). -/
def B_sub : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (A : Submodule ℝ V) (H : V → V → ℝ),
  (∀ S : Submodule ℝ V, (S : Set V) ⊆ A → FiniteDimensional ℝ S → IsNegDefSub H S →
      (Module.finrank ℝ S : ℕ∞) ≤ bIndex (A : Set V) H) ∧
  (bIndex (A : Set V) H ≠ ⊤ → ∃ S : Submodule ℝ V, (S : Set V) ⊆ A ∧ FiniteDimensional ℝ S ∧
      IsNegDefSub H S ∧ (Module.finrank ℝ S : ℕ∞) = bIndex (A : Set V) H) ∧
  (0 < setDim (bNullSet (A : Set V) H) ↔ ∃ v ∈ bNullSet (A : Set V) H, v ≠ 0)

theorem B_to_B_sub : B → B_sub := fun h V _ _ A H => h V A H

/-- `0 < dim span X` iff `X` has a nonzero element (for any set `X`). -/
theorem setDim_pos_iff {V : Type} [AddCommGroup V] [Module ℝ V] (X : Set V) :
    0 < setDim X ↔ ∃ v ∈ X, v ≠ 0 := by
  rw [setDim, pos_iff_ne_zero, Ne, Cardinal.toENat_eq_zero, Submodule.rank_eq_zero,
    Submodule.span_eq_bot]
  push Not
  rfl

/-- **The corrected statement holds outright** (it only unfolds the blind definitions: the
supremum of a bounded nonempty family in `ℕ∞` is attained, the zero subspace being admissible). -/
theorem B_sub_holds : B_sub := by
  intro V _ _ A H
  refine ⟨fun S hS hfin hneg => ?_, fun hne => ?_, setDim_pos_iff _⟩
  · exact le_iSup₂_of_le (f := fun (S : Submodule ℝ V)
      (_ : (S : Set V) ⊆ A ∧ FiniteDimensional ℝ S ∧ IsNegDefSub H S) =>
      (Module.finrank ℝ S : ℕ∞)) S ⟨hS, hfin, hneg⟩ le_rfl
  · set T := {S : Submodule ℝ V // (S : Set V) ⊆ A ∧ FiniteDimensional ℝ S ∧ IsNegDefSub H S}
    have hT : Nonempty T := ⟨⟨⊥, by simp, inferInstance, fun v hv h0 => absurd
      ((Submodule.mem_bot ℝ).1 hv) h0⟩⟩
    have e : bIndex (A : Set V) H = ⨆ S : T, (Module.finrank ℝ S.1 : ℕ∞) := by
      rw [bIndex, iSup_subtype']
    rw [e] at hne ⊢
    obtain ⟨S, hS⟩ := ENat.exists_eq_iSup_of_lt_top (lt_top_iff_ne_top.2 hne)
    exact ⟨S.1, S.2.1, S.2.2.1, S.2.2.2, hS⟩

/-- **The definitions agree** on the whole space: for a bilinear form, the blind index on
`Set.univ` is the project's `Morse.formIndex`. -/
theorem bIndex_univ_eq_formIndex {V : Type} [AddCommGroup V] [Module ℝ V]
    (H : LinearMap.BilinForm ℝ V) : bIndex (Set.univ : Set V) (fun x y => H x y) =
      Morse.formIndex H := by
  refine le_antisymm (iSup₂_le fun S hS => ?_) (iSup₂_le fun S hS => iSup_le fun hneg => ?_)
  · rw [Morse.formIndex]
    exact le_iSup₂_of_le (f := fun (S : Submodule ℝ V) (_ : FiniteDimensional ℝ S) =>
      ⨆ (_ : Morse.IsNegDefOn H S), (finrank ℝ S : ℕ∞)) S hS.2.1 (le_iSup_of_le hS.2.2 le_rfl)
  · exact le_iSup₂_of_le (f := fun (S : Submodule ℝ V)
      (_ : (S : Set V) ⊆ Set.univ ∧ FiniteDimensional ℝ S ∧ IsNegDefSub (fun x y => H x y) S) =>
      (Module.finrank ℝ S : ℕ∞)) S ⟨subset_univ _, hS, hneg⟩ le_rfl

/-- The project's `IsNegDefOn` is the blind `IsNegDefSub`. -/
theorem isNegDefOn_iff {V : Type} [AddCommGroup V] [Module ℝ V] (H : LinearMap.BilinForm ℝ V)
    (S : Submodule ℝ V) : Morse.IsNegDefOn H S ↔ IsNegDefSub (fun x y => H x y) S := Iff.rfl

/-- `A`'s first clause gives `B_sub`'s first clause for bilinear forms on the whole space, through
the agreement of the definitions. -/
theorem A_to_B_sub_univ_first : A → ∀ (V : Type) [AddCommGroup V] [Module ℝ V]
    (H : LinearMap.BilinForm ℝ V) (S : Submodule ℝ V), FiniteDimensional ℝ S →
    IsNegDefSub (fun x y => H x y) S →
      (Module.finrank ℝ S : ℕ∞) ≤ bIndex (Set.univ : Set V) (fun x y => H x y) := by
  intro hA V _ _ H S hS hneg
  rw [bIndex_univ_eq_formIndex]
  exact hA.1 hneg

/-- Conversely `B_sub`'s first clause (on `Set.univ`, for bilinear forms) is `A`'s first clause
`Morse.le_formIndex`. -/
theorem B_sub_to_A_first : B_sub → type_of% @Morse.le_formIndex.{0} := by
  intro hB M _ _ H S hS hneg
  have h := (hB M ⊤ (fun x y => H x y)).1 S (by simp) hS hneg
  rwa [Submodule.top_coe, bIndex_univ_eq_formIndex] at h

#rt_check RoundTrip.V9_13.B_to_A [Morse.le_formIndex, Morse.formIndex_le_of_map,
  Morse.formIndex_eq_sigNeg]
#rt_overlap RoundTrip.V9_13.B_to_A [Morse.le_formIndex, Morse.formIndex_le_of_map,
  Morse.formIndex_eq_sigNeg]
#rt_check RoundTrip.V9_13.A_to_B_sub_univ_first [Morse.le_formIndex, Morse.formIndex_le_of_map,
  Morse.formIndex_eq_sigNeg]
#rt_check RoundTrip.V9_13.B_sub_to_A_first [Morse.le_formIndex, Morse.formIndex_le_of_map,
  Morse.formIndex_eq_sigNeg]

end RoundTrip.V9_13
