import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V3_13

open CategoryTheory Morse.Homology Finset Module
open scoped ContDiff Manifold

namespace RoundTrip.V3_13

/-- The project's statement (the two listed theorems), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.FiltrationHomology.altSum_le_morseNumber.{0, 0, 0} ∧
  type_of% @Morse.FiltrationHomology.morse_inequality.{0, 0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.FiltrationHomology.altSum_le_morseNumber.{0, 0, 0},
    @Morse.FiltrationHomology.morse_inequality.{0, 0, 0, 0}⟩

theorem A_to_B : A → B := by
  classical
  intro hA F _ X _ k Xs lam ⟨h0, hlast, hstep⟩ l
  obtain ⟨Y, hY, hY0, hYk, hfin, hcells⟩ :=
    RoundTrip.Glue.exists_nat_filtration (F := F) Xs lam hstep
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: `X = ∅`, both sides vanish
    have hR : ∀ i, Rabs F X i = 0 := by
      intro i
      have := subsingleton_subsetHomology_self (𝕜 := F) i (∅ : Set X)
      have e : finrank F (subsetHomology F i (Set.empty_subset (Set.univ : Set X))) =
          finrank F (subsetHomology F i (subset_refl (∅ : Set X))) :=
        finrank_subsetHomology_congr _ _ rfl (by rw [← hlast, ← h0]; rfl) i
      exact e.trans Module.finrank_zero_of_subsingleton
    have hC : ∀ i, Cabs lam i = 0 := fun i ↦ by simp [Cabs]
    simp [alt, hR, hC]
  · have h := truncatedFiltrationHomology F hY hfin
    have hcells' : ∀ j < k, ∀ i, finrank F (filtrationGroup F (monotone_truncate hY k) i j (j + 1))
        = #{p ∈ (univ : Finset (Fin k)) | p.val = j ∧ lam p = i} := by
      intro j hj i
      rw [← hcells j hj i]
      exact finrank_subsetHomology_congr _ _ (congrArg Y (by omega)) (congrArg Y (by omega)) i
    have hR : ∀ i, Rabs F X i =
        finrank F (filtrationGroup F (monotone_truncate hY k) i 0 k) := by
      intro i
      exact finrank_subsetHomology_congr _ _ (by simp [hY0, h0]) (by simp [hYk, hlast]) i
    have key := hA.2 h (X := id) (fun j _ ↦ Nat.le_succ j) hk
      (step := fun p : Fin k ↦ p.val) (ind := lam) (fun p _ ↦ p.2) hcells' l
    simp only [hR]
    exact key

#rt_check RoundTrip.V3_13.A_to_B [Morse.FiltrationHomology.altSum_le_morseNumber,
  Morse.FiltrationHomology.morse_inequality]

end RoundTrip.V3_13
