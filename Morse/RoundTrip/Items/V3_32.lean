import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V3_32

open CategoryTheory Morse.Homology Finset Module
open scoped ContDiff Manifold

namespace RoundTrip.V3_32

/-- The project's statement: the five listed theorems (`TopTriple.longExactSeq`,
`subsetHomology`, `filtrationHomology` are definitions), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.Homology.finiteDimensional_subsetHomology_of_steps.{0} ∧
  type_of% @Morse.Homology.singular_weak_morse_inequality.{0} ∧
  type_of% @Morse.Homology.singular_morse_inequality.{0} ∧
  type_of% @Morse.Homology.singular_euler_characteristic.{0} ∧
  type_of% @Morse.Homology.singular_morse_inequality_of_cells.{0, 0}

theorem A_holds : A :=
  ⟨@Morse.Homology.finiteDimensional_subsetHomology_of_steps.{0},
    @Morse.Homology.singular_weak_morse_inequality.{0},
    @Morse.Homology.singular_morse_inequality.{0},
    @Morse.Homology.singular_euler_characteristic.{0},
    @Morse.Homology.singular_morse_inequality_of_cells.{0, 0}⟩

theorem A_to_B : A → B := by
  classical
  intro hA F _ X _ k Xs lam ⟨h0, hlast, hstep⟩
  obtain ⟨Y, hY, hY0, hYk, hfin, hcells⟩ :=
    RoundTrip.Glue.exists_nat_filtration (F := F) Xs lam hstep
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: `X = ∅`, everything vanishes
    have hR : ∀ i, Rabs F X i = 0 := by
      intro i
      have := subsingleton_subsetHomology_self (𝕜 := F) i (∅ : Set X)
      have e : finrank F (subsetHomology F i (Set.empty_subset (Set.univ : Set X))) =
          finrank F (subsetHomology F i (subset_refl (∅ : Set X))) :=
        finrank_subsetHomology_congr _ _ rfl (by rw [← hlast, ← h0]; rfl) i
      exact e.trans Module.finrank_zero_of_subsingleton
    have hC : ∀ i, Cabs lam i = 0 := fun i ↦ by simp [Cabs]
    simp [alt, hR, hC]
  · have hR : ∀ i, Rabs F X i = finrank F (subsetHomology F i (hY (Nat.zero_le k))) := by
      intro i
      exact finrank_subsetHomology_congr _ _ (by simp [hY0, h0]) (by simp [hYk, hlast]) i
    have hstep' : ∀ p ∈ (univ : Finset (Fin k)), (fun p : Fin k ↦ p.val) p < k :=
      fun p _ ↦ p.2
    have hC : ∀ i, Cabs lam i = #{p ∈ (univ : Finset (Fin k)) | lam p = i} := fun i ↦ rfl
    -- (4_λ)
    have strong : ∀ l, alt (fun i => (Rabs F X i : ℤ)) l ≤ alt (fun i => (Cabs lam i : ℤ)) l := by
      intro l
      have key := hA.2.2.2.2 F hY hfin hk hstep' hcells l
      simp only [hR, hC]
      exact key
    have weak : ∀ l, Rabs F X l ≤ Cabs lam l := fun l ↦ by
      have := Morse.le_of_altSum_le strong l
      exact_mod_cast this
    -- (3), with `N` above every `λ_i`
    set N := (univ : Finset (Fin k)).sup lam
    have hlamN : ∀ p, lam p ≤ N := fun p ↦ Finset.le_sup (f := lam) (mem_univ p)
    have hCN : ∀ i, N < i → Cabs lam i = 0 := by
      intro i hi
      rw [hC, card_eq_zero, filter_eq_empty_iff]
      intro p _ hp
      have := hlamN p
      omega
    have hvan : ∀ j < k, finrank F (subsetHomology F (N + 1) (hY (Nat.le_succ j))) = 0 := by
      intro j hj
      rw [hcells j hj, card_eq_zero, filter_eq_empty_iff]
      rintro p - ⟨-, hp⟩
      have := hlamN p
      omega
    have heul := hA.2.2.2.1 F hY hfin hk hvan
    simp only [singularMorseNumber_eq_card F hY hstep' hcells] at heul
    have hsupp : ∀ g : ℕ → ℕ, (∀ i, N < i → g i = 0) →
        ∑ᶠ l : ℕ, (-1 : ℤ) ^ l * (g l : ℤ) = ∑ i ∈ range (N + 1), (-1 : ℤ) ^ i * (g i : ℤ) := by
      intro g hg
      apply finsum_eq_sum_of_support_subset
      intro i hi
      simp only [Function.mem_support] at hi
      simp only [coe_range, Set.mem_Iio]
      by_contra hc
      exact hi (by rw [hg i (by omega)]; simp)
    refine ⟨⟨weak, ?_⟩, strong⟩
    rw [hsupp _ fun i hi ↦ Nat.le_zero.1 ((weak i).trans (hCN i hi).le), hsupp _ hCN]
    simp only [hR, hC]
    exact heul

#rt_check RoundTrip.V3_32.A_to_B [Morse.Homology.finiteDimensional_subsetHomology_of_steps,
  Morse.Homology.singular_weak_morse_inequality, Morse.Homology.singular_morse_inequality,
  Morse.Homology.singular_euler_characteristic, Morse.Homology.singular_morse_inequality_of_cells]

end RoundTrip.V3_32
