import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_3

open Finset

namespace RoundTrip.V14_3

/-- The project's statement (universes of `ι` instantiated at `0`): pure arithmetic of the odd
integers `k_j` — `n ≤ Σ k_j²`, with equality iff every `k_j = ±1`, and, if every `k_j = ±1`,
`n = 2m` and `Σ k_j = 0`, then `m` of the `k_j` are `+1` and `m` are `−1`. -/
def A : Prop :=
  type_of% @Morse.card_le_sum_sq.{0} ∧ type_of% @Morse.sum_sq_eq_card_iff.{0} ∧
    type_of% @Morse.card_eq_of_minimal.{0}

theorem A_holds : A :=
  ⟨@Morse.card_le_sum_sq.{0}, @Morse.sum_sq_eq_card_iff.{0}, @Morse.card_eq_of_minimal.{0}⟩

/-! `A_to_B` is not proved: `B`'s minimality claims (`IsMinimalIn` in `U(n)` and in `SU(2m)`) need a
lower bound `π√n` for the length of EVERY piecewise smooth path from `I` to `−I` in the group
(Milnor: Hopf–Rinow plus "every geodesic from `I` is `exp tA`"; or: `U(n)` lies on the sphere of
radius `√n` in `M_n(ℂ)` and `I`, `−I` are antipodal), which `A` (arithmetic only) does not contain.
The project proves this lower bound only for `SU(2m)`, outside the item
(`Morse.riemDist_one_neg_one`, `Morse.isMinimalGeodesic_exp_iff`, which themselves use
`card_le_sum_sq` / `sum_sq_eq_card_iff`), and not at all for `U(n)`. -/

/-- `A` is elementary arithmetic and is proved outright (the hypothesis `B` is not used). -/
theorem B_to_A : B → A := by
  intro _
  have one_le : ∀ {a : ℤ}, Odd a → 1 ≤ a ^ 2 := by
    intro a ha
    have h0 : a ≠ 0 := by rintro rfl; simp at ha
    have h1 := Int.one_le_abs h0
    nlinarith [sq_abs a]
  refine ⟨?_, ?_, ?_⟩
  · intro ι _ k hk
    rw [← Finset.card_univ, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact sum_le_sum fun i _ => one_le (hk i)
  · intro ι _ k hk
    rw [← Finset.card_univ, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, eq_comm,
      sum_eq_sum_iff_of_le fun i _ => one_le (hk i)]
    simp only [mem_univ, true_imp_iff]
    exact forall_congr' fun i => by rw [eq_comm, sq, mul_self_eq_one_iff]
  · intro ι _ m k h hcard hsum
    have hcompl : univ.filter (fun i => ¬ k i = 1) = univ.filter (fun i => k i = -1) := by
      ext i; simp only [mem_filter, mem_univ, true_and]
      rcases h i with hi | hi <;> simp [hi]
    have h1 := card_filter_add_card_filter_not (s := (univ : Finset ι)) (fun i => k i = 1)
    rw [hcompl, card_univ, hcard] at h1
    have h2 := sum_filter_add_sum_filter_not (univ : Finset ι) (fun i => k i = 1) k
    rw [hcompl, hsum] at h2
    have e1 : ∑ i ∈ univ.filter (fun i => k i = 1), k i = #{i | k i = 1} := by
      rw [sum_congr rfl fun i hi => (mem_filter.1 hi).2]; simp
    have e2 : ∑ i ∈ univ.filter (fun i => k i = -1), k i = -(#{i | k i = -1} : ℤ) := by
      rw [sum_congr rfl fun i hi => (mem_filter.1 hi).2]; simp
    rw [e1, e2] at h2
    omega

#rt_check RoundTrip.V14_3.B_to_A [Morse.card_le_sum_sq, Morse.sum_sq_eq_card_iff, Morse.card_eq_of_minimal]
#rt_overlap RoundTrip.V14_3.B_to_A [Morse.card_le_sum_sq, Morse.sum_sq_eq_card_iff, Morse.card_eq_of_minimal]

end RoundTrip.V14_3
