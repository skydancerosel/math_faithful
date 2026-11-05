import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_14

namespace RoundTrip.V3_14

/-- The project's statement (the five listed theorems), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.le_of_altSum_le ∧
  type_of% @Morse.altSum_eq_of_altSum_le ∧
  type_of% @Morse.sum_neg_one_pow_eq_of_altSum_le ∧
  type_of% @Morse.FiltrationHomology.finrank_eq_zero_of_forall_ne.{0, 0, 0, 0} ∧
  type_of% @Morse.FiltrationHomology.euler_characteristic_eq.{0, 0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.le_of_altSum_le, @Morse.altSum_eq_of_altSum_le, @Morse.sum_neg_one_pow_eq_of_altSum_le,
    @Morse.FiltrationHomology.finrank_eq_zero_of_forall_ne.{0, 0, 0, 0},
    @Morse.FiltrationHomology.euler_characteristic_eq.{0, 0, 0, 0}⟩

/-- B's `alt` is the project's `altSum`. -/
theorem alt_eq (a : ℕ → ℤ) (l : ℕ) : alt a l = Morse.altSum a l := rfl

theorem A_to_B : A → B := by
  intro hA R C n hvan h4
  have h4' : ∀ l, Morse.altSum (fun i ↦ (R i : ℤ)) l ≤ Morse.altSum (fun i ↦ (C i : ℤ)) l := h4
  have weak : ∀ l, R l ≤ C l := fun l ↦ by exact_mod_cast hA.1 h4' l
  refine ⟨weak, ?_, fun l hC ↦ ⟨?_, ?_⟩⟩
  · exact hA.2.2.1 (fun i ↦ Nat.cast_nonneg _) h4' (by simp [(hvan (n + 1) (by omega)).2])
  · have := weak (l + 1); omega
  · exact hA.2.1 h4' (Nat.cast_nonneg _) (by simp [hC])

#rt_check RoundTrip.V3_14.A_to_B [Morse.le_of_altSum_le, Morse.altSum_eq_of_altSum_le,
  Morse.sum_neg_one_pow_eq_of_altSum_le, Morse.FiltrationHomology.finrank_eq_zero_of_forall_ne,
  Morse.FiltrationHomology.euler_characteristic_eq]

end RoundTrip.V3_14
