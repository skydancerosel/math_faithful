import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_3

open Finset Real

namespace RoundTrip.V15_3

/-- The project's statement (no universe parameters): three arithmetic facts about the integers
`a_1, …, a_m`. (i) `spectralIndex (oSpectrum a) = bottIndexO a` for odd positive `a` — the number
of conjugate parameters in `(0,1)` produced by the list `oSpectrum a` (the numbers
`π²(a_i ± a_j)²/4`, each twice; by its docstring, "the spectrum of `K_{πA}`") is Milnor's `λ`;
(ii) `bottIndexO a = 0` when all `a_j = 1`; (iii) `bottIndexO a ≥ 2m − 2` for odd positive `a` not
all `1`. -/
def A : Prop :=
  type_of% @Morse.spectralIndex_oSpectrum ∧ type_of% @Morse.bottIndexO_eq_zero ∧
    type_of% @Morse.bottIndexO_ge

theorem A_holds : A := ⟨@Morse.spectralIndex_oSpectrum, @Morse.bottIndexO_eq_zero,
  @Morse.bottIndexO_ge⟩

/-- Vocabulary: B's `λ = Σ_{i<j} (a_i + a_j − 2) + Σ_{a_i > a_j} (a_i − a_j − 2)` is the project's
`bottIndexO`. -/
theorem lamFormula_eq_bottIndexO {m : ℕ} (a : Fin m → ℤ) : lamFormula a = Morse.bottIndexO a := by
  unfold lamFormula Morse.bottIndexO Morse.bottIndex
  congr 1
  · rw [← Fintype.sum_prod_type' (fun i j => if i < j then a i + a j - 2 else 0), ← sum_filter]
  · rw [← Fintype.sum_prod_type' (fun i j => if a j < a i then a i - a j - 2 else 0),
      ← sum_filter]

/-- B ⇒ A, only vacuously: A is pure arithmetic and is re-proved outright (the item's proofs,
re-run on the project's counting lemmas `spectralIndex_eq`, `two_mul_ncard_conjParams`,
`bottIndex_eq_sum_subtype`, `bottIndex_nonneg`). B's index is the geometric `idxIn` and B has no
`spectralIndex`, so B's content cannot be used: e.g. (iii) would follow from B's Claims 1 and 3
only after proving that `t ↦ exp(πtA)` is not minimal when some `a_j ≥ 3` (a length computation in
`O(2m)`), and (i) has no counterpart in B at all. -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨@fun m a hodd hpos => ?_, @fun m a h => ?_, @fun m a hodd hpos hnm => ?_⟩
  · rw [Morse.spectralIndex_eq, Fintype.sum_prod_type, Fintype.sum_sum_type, Nat.cast_add,
      Nat.cast_sum, Nat.cast_sum, Morse.bottIndexO, Morse.bottIndex_eq_sum_subtype]
    congr 1
    · rw [← Fintype.sum_prod_type' (fun i j => if i < j then a i + a j - 2 else 0), ← sum_filter,
        sum_subtype (p := fun p : Fin m × Fin m => p.1 < p.2) _ (fun p => by simp)
          (fun p : Fin m × Fin m => a p.1 + a p.2 - 2)]
      refine sum_congr rfl fun p _ => ?_
      have hneg : Odd (-a p.1.2) := (hodd _).neg
      have hlt : -a p.1.2 < a p.1.1 := by linarith [hpos p.1.1, hpos p.1.2]
      rw [Nat.cast_sum, Fin.sum_univ_two]
      have := Morse.two_mul_ncard_conjParams (hodd p.1.1) hneg hlt
      simp only [Morse.oSpectrum, Int.cast_neg, sub_neg_eq_add] at this ⊢
      linarith
    · refine sum_congr rfl fun p _ => ?_
      rw [Nat.cast_sum, Fin.sum_univ_two,
        ← Morse.two_mul_ncard_conjParams (hodd p.1.1) (hodd p.1.2) p.2]
      simp only [Morse.oSpectrum]
      ring
  · simp [Morse.bottIndexO, Morse.bottIndex, h]
  · push Not at hnm
    obtain ⟨i₀, hi₀⟩ := hnm
    have h3 : 3 ≤ a i₀ := by obtain ⟨x, hx⟩ := hodd i₀; have := hpos i₀; omega
    set g : Fin m → Fin m → ℤ := fun i j => if i < j then a i + a j - 2 else 0 with hg
    have hg0 : ∀ i j, 0 ≤ g i j := fun i j => by
      simp only [hg]; split_ifs <;> linarith [hpos i, hpos j]
    set r : Fin m → ℤ := fun i => ∑ j, g i j with hr
    have hr0 : ∀ i, 0 ≤ r i := fun i => sum_nonneg fun j _ => hg0 i j
    have hrow : ∀ i, (if i < i₀ then a i + a i₀ - 2 else 0) ≤ r i := fun i => by
      split_ifs with h
      · have := single_le_sum (fun j _ => hg0 i j) (mem_univ i₀)
        simpa [hg, h] using this
      · exact hr0 i
    have hF : (∑ i, ∑ j, if i < j then a i + a j - 2 else 0) = r i₀ + ∑ i ∈ univ.erase i₀, r i :=
      (add_sum_erase _ _ (mem_univ i₀)).symm
    have hcol : ∑ i, (if i < i₀ then a i + a i₀ - 2 else 0) ≤ ∑ i ∈ univ.erase i₀, r i := by
      rw [← add_sum_erase _ _ (mem_univ i₀), if_neg (lt_irrefl _), zero_add]
      exact sum_le_sum fun i _ => hrow i
    have hrow0 : r i₀ + ∑ i, (if i < i₀ then a i + a i₀ - 2 else 0)
        = ∑ j, ((if i₀ < j then a i₀ + a j - 2 else 0) +
          (if j < i₀ then a j + a i₀ - 2 else 0)) := by
      rw [sum_add_distrib]
    have hlow : ∑ j, (if j ≠ i₀ then (2 : ℤ) else 0) ≤
        ∑ j, ((if i₀ < j then a i₀ + a j - 2 else 0) +
          (if j < i₀ then a j + a i₀ - 2 else 0)) := by
      refine sum_le_sum fun j _ => ?_
      have := hpos j
      rcases lt_trichotomy j i₀ with h | h | h
      · rw [if_pos h.ne, if_neg (not_lt.2 h.le), if_pos h]; omega
      · subst h; simp
      · rw [if_pos h.ne', if_pos h, if_neg (not_lt.2 h.le)]; omega
    have hcount : ∑ j, (if j ≠ i₀ then (2 : ℤ) else 0) = 2 * ((m : ℤ) - 1) := by
      rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, filter_ne' univ i₀,
        card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
      have : 1 ≤ m := by have := i₀.pos; omega
      push_cast [this]; ring
    have hB := Morse.bottIndex_nonneg hodd
    unfold Morse.bottIndexO
    linarith

#rt_check RoundTrip.V15_3.B_to_A [Morse.spectralIndex_oSpectrum, Morse.bottIndexO_eq_zero,
  Morse.bottIndexO_ge]
#rt_overlap RoundTrip.V15_3.B_to_A [Morse.spectralIndex_oSpectrum, Morse.bottIndexO_eq_zero,
  Morse.bottIndexO_ge]

end RoundTrip.V15_3
