import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_11

open Finset

namespace RoundTrip.V14_11

/-- The project's statement (universe of `ι` instantiated at `0`; `Morse.bottIndex` is
vocabulary): Lemma 23.2 for the formula (any finite index type of cardinality `2m`), plus the two
bookkeeping lemmas behind Milnor's cases, for arbitrary odd `k` (no condition on `Σ k_i`): the
sum over (positive, negative) pairs is a lower bound, and the data `P, N, S_p, S_n`. -/
def A : Prop :=
  type_of% @Morse.bottIndex_ge.{0} ∧ type_of% @Morse.exists_pos_neg_data.{0} ∧
    type_of% @Morse.sum_pos_neg_le_bottIndex.{0}

theorem A_holds : A :=
  ⟨@Morse.bottIndex_ge.{0}, @Morse.exists_pos_neg_data.{0}, @Morse.sum_pos_neg_le_bottIndex.{0}⟩

/-! ### Vocabulary -/

theorem bottFormula_eq {n : ℕ} (k : Fin n → ℤ) : bottFormula k = Morse.bottIndex k := by
  rw [bottFormula, Morse.bottIndex, Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]

theorem bottIndex_eq_bottFormula {ι : Type} [Fintype ι] {m : ℕ} (f : Fin m ≃ ι) (k : ι → ℤ) :
    Morse.bottIndex k = bottFormula (k ∘ f) := by
  rw [bottFormula_eq, Morse.bottIndex, Morse.bottIndex, ← Equiv.sum_comp f]
  refine sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp f]
  rfl

/-- With `Σ k_j = 0` and all `k_j = ±1`, exactly `m` are negative. -/
theorem card_neg_of_minimal {m : ℕ} {k : Fin (2 * m) → ℤ} (h : ∀ j, k j = 1 ∨ k j = -1)
    (hsum : ∑ j, k j = 0) : (univ.filter fun j => k j < 0).card = m ∧
      (univ.filter fun j => 0 < k j).card = m := by
  obtain ⟨h1, h2⟩ := Morse.card_eq_of_minimal h (Fintype.card_fin _) hsum
  have e1 : (univ.filter fun j => k j < 0) = univ.filter fun j => k j = -1 := by
    ext j; simp only [mem_filter, mem_univ, true_and]; rcases h j with h | h <;> simp [h]
  have e2 : (univ.filter fun j => 0 < k j) = univ.filter fun j => k j = 1 := by
    ext j; simp only [mem_filter, mem_univ, true_and]; rcases h j with h | h <;> simp [h]
  rw [e1, e2]
  exact ⟨h2, h1⟩

theorem A_to_B : A → B := by
  rintro ⟨hge, -, -⟩ m k hk hsum
  have key : ¬ (∀ j, k j = 1 ∨ k j = -1) → 2 * (m : ℤ) + 2 ≤ bottFormula k := fun hnm => by
    rw [bottFormula_eq]
    exact hge hk (Fintype.card_fin _) hsum hnm
  refine ⟨fun hN => key fun h => ?_, fun hP => key fun h => ?_, fun _ _ hnm => key hnm, key⟩
  · have := (card_neg_of_minimal h hsum).1; omega
  · have := (card_neg_of_minimal h hsum).2; omega

/-! ### `B ⇒ A`: Lemma 23.2 from `B`; the two bookkeeping lemmas outright -/

theorem sum_pos_neg_le {ι : Type} [Fintype ι] {k : ι → ℤ} (hk : ∀ i, Odd (k i)) :
    ∑ i ∈ univ.filter (fun i => 0 < k i), ∑ j ∈ univ.filter (fun j => k j < 0), (k i - k j - 2)
      ≤ Morse.bottIndex k := by
  unfold Morse.bottIndex
  calc ∑ i ∈ univ.filter (fun i => 0 < k i), ∑ j ∈ univ.filter (fun j => k j < 0), (k i - k j - 2)
      = ∑ i ∈ univ.filter (fun i => 0 < k i), ∑ j ∈ univ.filter (fun j => k j < 0),
          (if k j < k i then k i - k j - 2 else 0) := by
        refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
        simp only [mem_filter, mem_univ, true_and] at hi hj
        rw [if_pos (by omega)]
    _ ≤ ∑ i ∈ univ.filter (fun i => 0 < k i), ∑ j, (if k j < k i then k i - k j - 2 else 0) :=
        sum_le_sum fun i _ => sum_le_sum_of_subset_of_nonneg (subset_univ _)
          fun j _ _ => Morse.bottIndex_term_nonneg hk i j
    _ ≤ ∑ i, ∑ j, (if k j < k i then k i - k j - 2 else 0) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _)
          fun i _ _ => sum_nonneg fun j _ => Morse.bottIndex_term_nonneg hk i j

theorem pos_neg_data {ι : Type} [Fintype ι] {k : ι → ℤ} (hk : ∀ i, Odd (k i)) :
    ∃ P N Sp Sn : ℤ, 0 ≤ P ∧ 0 ≤ N ∧ P + N = Fintype.card ι ∧ Sp - Sn = ∑ i, k i ∧
      P ≤ Sp ∧ N ≤ Sn ∧ N * Sp + P * Sn - 2 * P * N ≤ Morse.bottIndex k ∧
      (∀ i, 3 ≤ k i → P + 2 ≤ Sp ∧ 1 ≤ P) ∧ (∀ i, k i ≤ -3 → N + 2 ≤ Sn ∧ 1 ≤ N) := by
  classical
  set Pos := univ.filter (fun i => 0 < k i) with hPos
  set Neg := univ.filter (fun j => k j < 0) with hNeg
  have hk0 : ∀ i, k i ≠ 0 := fun i h => by simpa [h] using hk i
  have hcompl : univ.filter (fun i => ¬ 0 < k i) = Neg := by
    ext i; simp only [mem_filter, mem_univ, true_and, not_lt, hNeg]
    exact ⟨fun h => lt_of_le_of_ne h (hk0 i), fun h => h.le⟩
  refine ⟨#Pos, #Neg, ∑ i ∈ Pos, k i, -∑ j ∈ Neg, k j, by positivity, by positivity, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · have := card_filter_add_card_filter_not (s := (univ : Finset ι)) (fun i => 0 < k i)
    rw [hcompl, card_univ] at this
    exact_mod_cast this
  · have := sum_filter_add_sum_filter_not (univ : Finset ι) (fun i => 0 < k i) k
    rw [hcompl] at this
    linarith
  · rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact sum_le_sum fun i hi => by simp only [hPos, mem_filter] at hi; omega
  · rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, ← sum_neg_distrib]
    exact sum_le_sum fun i hi => by simp only [hNeg, mem_filter] at hi; omega
  · have h1 := sum_pos_neg_le hk
    rw [Morse.sum_pos_neg_eq] at h1
    exact h1
  · intro i₀ h
    have hmem : i₀ ∈ Pos := by simp only [hPos, mem_filter, mem_univ, true_and]; omega
    have h1 : (#(Pos.erase i₀) : ℤ) ≤ ∑ i ∈ Pos.erase i₀, k i := by
      rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      exact sum_le_sum fun i hi => by simp only [hPos, mem_erase, mem_filter] at hi; omega
    have h2 : #(Pos.erase i₀) + 1 = #Pos := card_erase_add_one hmem
    have h3 : k i₀ + ∑ i ∈ Pos.erase i₀, k i = ∑ i ∈ Pos, k i := add_sum_erase _ _ hmem
    have h2' : (#(Pos.erase i₀) : ℤ) + 1 = #Pos := by rw [← h2]; push_cast; ring
    constructor <;> linarith
  · intro i₀ h
    have hmem : i₀ ∈ Neg := by simp only [hNeg, mem_filter, mem_univ, true_and]; omega
    have h1 : ∑ i ∈ Neg.erase i₀, k i ≤ -(#(Neg.erase i₀) : ℤ) := by
      rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, ← sum_neg_distrib]
      exact sum_le_sum fun i hi => by simp only [hNeg, mem_erase, mem_filter] at hi; omega
    have h2 : #(Neg.erase i₀) + 1 = #Neg := card_erase_add_one hmem
    have h3 : k i₀ + ∑ i ∈ Neg.erase i₀, k i = ∑ i ∈ Neg, k i := add_sum_erase _ _ hmem
    have h2' : (#(Neg.erase i₀) : ℤ) + 1 = #Neg := by rw [← h2]; push_cast; ring
    constructor <;> linarith

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {ι} _ m k hk hcard hsum hnm => ?_, fun {ι} _ k hk => pos_neg_data hk,
    fun {ι} _ k hk => sum_pos_neg_le hk⟩
  set f : Fin (2 * m) ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  rw [bottIndex_eq_bottFormula f]
  refine (hB m (k ∘ f) (fun j => hk _) ?_).2.2.2 ?_
  · rw [show ∑ j, (k ∘ f) j = ∑ i, k i from Equiv.sum_comp f k, hsum]
  · intro h
    exact hnm fun i => by simpa using h (f.symm i)

#rt_check RoundTrip.V14_11.A_to_B [Morse.bottIndex_ge, Morse.exists_pos_neg_data, Morse.sum_pos_neg_le_bottIndex]
#rt_check RoundTrip.V14_11.B_to_A [Morse.bottIndex_ge, Morse.exists_pos_neg_data, Morse.sum_pos_neg_le_bottIndex]
#rt_overlap RoundTrip.V14_11.B_to_A [Morse.bottIndex_ge, Morse.exists_pos_neg_data, Morse.sum_pos_neg_le_bottIndex]
#rt_overlap RoundTrip.V14_11.A_to_B [Morse.bottIndex_ge, Morse.exists_pos_neg_data, Morse.sum_pos_neg_le_bottIndex]

end RoundTrip.V14_11
