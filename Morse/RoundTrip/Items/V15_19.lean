import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_19

open Finset Real

namespace RoundTrip.V15_19

/-- The project's statement (universes instantiated at `0`): two counting facts about a list of
reals `e` (by its docstring, "the spectrum of `K_V`"), where `spectralIndex e` counts, with
multiplicity, the parameters `t = πs/√e_i ∈ (0,1)` (Theorem 20.5 by definition):
(i) `#{i | π² < e_i} ≤ spectralIndex e`; (ii) for integers `a_j ≥ 1` with `a_{h₀} ≥ 3`, the list
`π²(a_{h₀} + a_j)²/4`, `j ≠ h₀`, has `spectralIndex ≥ s − 1`. -/
def A : Prop :=
  type_of% @Morse.card_lt_le_spectralIndex.{0} ∧ type_of% @Morse.card_sub_one_le_spectralIndex

theorem A_holds : A := ⟨@Morse.card_lt_le_spectralIndex.{0}, @Morse.card_sub_one_le_spectralIndex⟩

/-- B ⇒ A, only vacuously: A is arithmetic about `spectralIndex` (a count of the parameters
`πs/√e ∈ (0,1)`) and is re-proved outright (the item's proofs, re-run on the project's counting
lemma `spectralIndex_eq`). B has no `spectralIndex` and no `K_A`: its index is the geometric
`idxIn` of a geodesic of `Ω_k(n)`, so B's content cannot be used. -/
theorem B_to_A : B → A := by
  intro _
  have hcard : ∀ {κ : Type} [Fintype κ] (e : κ → ℝ), #{i | π ^ 2 < e i} ≤ Morse.spectralIndex e := by
    intro κ _ e
    rw [Morse.spectralIndex_eq, card_filter]
    refine sum_le_sum fun i _ => ?_
    split_ifs with h
    · have he : 0 < e i := lt_trans (by positivity) h
      have hs : π < √(e i) := by
        rw [← Real.sqrt_sq pi_pos.le]
        exact Real.sqrt_lt_sqrt (by positivity) h
      have hmem : π * ((1 : ℤ) : ℝ) / √(e i) ∈ Morse.conjParams (e i) := by
        refine ⟨he, by simp [pi_pos, Real.sqrt_pos.2 he], ?_, 1, rfl⟩
        rw [Int.cast_one, mul_one, div_lt_one (Real.sqrt_pos.2 he)]
        exact hs
      exact (Set.ncard_pos (Morse.conjParams_finite (e i))).2 ⟨_, hmem⟩
    · exact Nat.zero_le _
  refine ⟨@fun κ _ e => hcard e, @fun s a hpos h₀ h3 => ?_⟩
  refine le_trans (le_of_eq ?_) (hcard _)
  rw [filter_true_of_mem, card_univ, Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_unique]
  intro j _
  have h1 : (4 : ℝ) ≤ ((a h₀ : ℝ) + a j) := by
    have := hpos j
    have : (4 : ℤ) ≤ a h₀ + a j := by omega
    exact_mod_cast this
  have h2 : (16 : ℝ) ≤ ((a h₀ : ℝ) + a j) ^ 2 := by nlinarith
  have h3 : 0 < π ^ 2 := by positivity
  nlinarith

#rt_check RoundTrip.V15_19.B_to_A [Morse.card_lt_le_spectralIndex,
  Morse.card_sub_one_le_spectralIndex]
#rt_overlap RoundTrip.V15_19.B_to_A [Morse.card_lt_le_spectralIndex,
  Morse.card_sub_one_le_spectralIndex]

end RoundTrip.V15_19
