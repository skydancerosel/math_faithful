import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V3_11

open CategoryTheory Morse.Homology Finset Module
open scoped ContDiff Manifold

namespace RoundTrip.V3_11

/-- The project's statement (the five listed theorems), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.FiltrationHomology.finrank_le_morseNumber.{0, 0, 0} ∧
  type_of% @Morse.FiltrationHomology.sum_neg_one_pow_finrank_eq.{0, 0, 0} ∧
  type_of% @Morse.morseNumber_eq_card.{0, 0, 0, 0} ∧
  type_of% @Morse.morseNumber_eq_card_of_single.{0, 0, 0} ∧
  type_of% @Morse.FiltrationHomology.weak_morse_inequality.{0, 0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.FiltrationHomology.finrank_le_morseNumber.{0, 0, 0},
    @Morse.FiltrationHomology.sum_neg_one_pow_finrank_eq.{0, 0, 0},
    @Morse.morseNumber_eq_card.{0, 0, 0, 0}, @Morse.morseNumber_eq_card_of_single.{0, 0, 0},
    @Morse.FiltrationHomology.weak_morse_inequality.{0, 0, 0, 0}⟩

theorem A_to_B : A → B := by
  classical
  intro hA F _ E _ _ _ M _ _ _ _ _ f hf hnd
  have hg : Morse.IsMorseFunction E f := ⟨hf, fun p hp ↦ (hnd p hp).2⟩
  obtain ⟨n, X, hX, α, P, step, ind, hn, h0, htop, hfin, hstep, hcells, hind, hcrit⟩ :=
    RoundTrip.Glue.exists_cells_filtration_of_compactSpace F hg
  have h := truncatedFiltrationHomology F hX hfin
  have hcells' : ∀ k < n, ∀ i, finrank F (filtrationGroup F (monotone_truncate hX n) i k (k + 1))
      = #{p ∈ P | step p = k ∧ ind p = i} := by
    intro k hk i
    rw [← hcells k hk i]
    exact finrank_subsetHomology_congr _ _ (congrArg X (by omega)) (congrArg X (by omega)) i
  have hR : ∀ i, Rabs F M i =
      finrank F (filtrationGroup F (monotone_truncate hX n) i 0 n) := by
    intro i
    exact finrank_subsetHomology_congr _ _ (by simp [h0]) (by simp [htop]) i
  have hX' : ∀ k < n, id k ≤ id (k + 1) := fun k _ ↦ Nat.le_succ k
  refine ⟨fun l ↦ ?_, ?_⟩
  · rw [hR, show Cnum E f l = Morse.critCount E f l from rfl, hcrit]
    exact hA.2.2.2.2 h hX' hn hstep hcells' l
  · have hvan : ∀ k < n, finrank F (filtrationGroup F (monotone_truncate hX n)
        (finrank ℝ E + 1) (id k) (id (k + 1))) = 0 := by
      intro k hk
      rw [id, id, hcells' k hk, card_eq_zero, filter_eq_empty_iff]
      rintro p hp ⟨-, hi⟩
      have := hind p hp
      omega
    have key := hA.2.1 h hX' hn hvan
    simp only [hR]
    refine key.trans (sum_congr rfl fun i _ ↦ ?_)
    rw [hA.2.2.1 hstep hcells' i, show Cnum E f i = Morse.critCount E f i from rfl, hcrit]

#rt_check RoundTrip.V3_11.A_to_B [Morse.FiltrationHomology.finrank_le_morseNumber,
  Morse.FiltrationHomology.sum_neg_one_pow_finrank_eq, Morse.morseNumber_eq_card,
  Morse.morseNumber_eq_card_of_single, Morse.FiltrationHomology.weak_morse_inequality]

end RoundTrip.V3_11
