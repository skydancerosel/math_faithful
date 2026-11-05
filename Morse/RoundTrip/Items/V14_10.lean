import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_10

open Finset

namespace RoundTrip.V14_10

/-- The project's statement (universes of `ι`, `ι'` instantiated at `0`; `Morse.bottIndex` is
vocabulary): for any finite index type, the formula is `≥ 0` for odd `k`, invariant under
`k ↦ −k` and under reindexing by any equivalence `ι' ≃ ι`, and vanishes when all `k_i = ±1`. -/
def A : Prop :=
  type_of% @Morse.bottIndex_nonneg.{0} ∧ type_of% @Morse.bottIndex_neg.{0} ∧
    type_of% @Morse.bottIndex_comp_equiv.{0, 0} ∧ type_of% @Morse.bottIndex_eq_zero_of_minimal.{0}

theorem A_holds : A :=
  ⟨@Morse.bottIndex_nonneg.{0}, @Morse.bottIndex_neg.{0}, @Morse.bottIndex_comp_equiv.{0, 0},
    @Morse.bottIndex_eq_zero_of_minimal.{0}⟩

/-! ### Vocabulary -/

/-- The blind formula (sum over the filtered ordered pairs) is the project's double sum. -/
theorem bottFormula_eq {n : ℕ} (k : Fin n → ℤ) : bottFormula k = Morse.bottIndex k := by
  rw [bottFormula, Morse.bottIndex, Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]

/-- Reindexing the project's formula along an equivalence `Fin m ≃ ι` (a change of summation
variables). -/
theorem bottIndex_eq_bottFormula {ι : Type} [Fintype ι] {m : ℕ} (f : Fin m ≃ ι) (k : ι → ℤ) :
    Morse.bottIndex k = bottFormula (k ∘ f) := by
  rw [bottFormula_eq, Morse.bottIndex, Morse.bottIndex, ← Equiv.sum_comp f]
  refine sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp f]
  rfl

/-- Milnor's normalization `k_1 ≥ ⋯ ≥ k_n`, outright (Mathlib's `Tuple.sort` of `−k`). -/
theorem exists_antitone {n : ℕ} (k : Fin n → ℤ) : ∃ σ : Equiv.Perm (Fin n), Antitone (k ∘ σ) := by
  refine ⟨Tuple.sort (-k), fun a b hab => ?_⟩
  have := Tuple.monotone_sort (-k) hab
  simp only [Function.comp_apply, Pi.neg_apply, neg_le_neg_iff] at this
  exact this

theorem A_to_B : A → B := by
  rintro ⟨-, hneg, hcomp, hmin⟩
  refine ⟨fun n k => exists_antitone k, fun n k σ => ?_, fun n k => ?_, fun n k h => ?_⟩
  · rw [bottFormula_eq, bottFormula_eq]
    exact hcomp k σ
  · rw [bottFormula_eq, bottFormula_eq]
    exact hneg k
  · rw [bottFormula_eq]
    exact hmin h

/-- `B ⇒ A`.  The `−k` and `±1` conjuncts come from `B` (after reindexing a general finite type
by `Fin n`); the reindexing invariance for a general equivalence `ι' ≃ ι` between two types is a
change of summation variables (B only speaks of permutations of `Fin n`); non-negativity for odd
`k` is not in `B` and is proved outright. -/
theorem B_to_A : B → A := by
  rintro ⟨-, -, hBneg, hBmin⟩
  refine ⟨fun {ι} _ k hk => ?_, fun {ι} _ k => ?_, fun {ι} _ {ι'} _ k e => ?_,
    fun {ι} _ k h => ?_⟩
  · -- outright: every term is `≥ 0`
    refine sum_nonneg fun i _ => sum_nonneg fun j _ => ?_
    split_ifs with hij
    · obtain ⟨x, hx⟩ := hk i
      obtain ⟨y, hy⟩ := hk j
      omega
    · exact le_rfl
  · rw [bottIndex_eq_bottFormula (Fintype.equivFin ι).symm,
      bottIndex_eq_bottFormula (Fintype.equivFin ι).symm]
    exact hBneg _ (k ∘ (Fintype.equivFin ι).symm)
  · rw [bottIndex_eq_bottFormula ((Fintype.equivFin ι').symm.trans e),
      bottIndex_eq_bottFormula (Fintype.equivFin ι').symm]
    rfl
  · rw [bottIndex_eq_bottFormula (Fintype.equivFin ι).symm]
    exact hBmin _ _ fun j => h _

#rt_check RoundTrip.V14_10.A_to_B [Morse.bottIndex_nonneg, Morse.bottIndex_neg, Morse.bottIndex_comp_equiv, Morse.bottIndex_eq_zero_of_minimal]
#rt_check RoundTrip.V14_10.B_to_A [Morse.bottIndex_nonneg, Morse.bottIndex_neg, Morse.bottIndex_comp_equiv, Morse.bottIndex_eq_zero_of_minimal]
#rt_overlap RoundTrip.V14_10.B_to_A [Morse.bottIndex_nonneg, Morse.bottIndex_neg, Morse.bottIndex_comp_equiv, Morse.bottIndex_eq_zero_of_minimal]
#rt_overlap RoundTrip.V14_10.A_to_B [Morse.bottIndex_nonneg, Morse.bottIndex_neg, Morse.bottIndex_comp_equiv, Morse.bottIndex_eq_zero_of_minimal]

end RoundTrip.V14_10
