import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_15

open CategoryTheory Morse.Homology Module
open scoped ContDiff Manifold

namespace RoundTrip.V3_15

/-- The project's statement (the seven listed theorems), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.eq_of_altSum_le_succ ∧
  type_of% @Morse.eq_of_altSum_le_zero ∧
  type_of% @Morse.FiltrationHomology.finrank_eq_morseNumber_of_succ.{0, 0, 0} ∧
  type_of% @Morse.FiltrationHomology.finrank_eq_morseNumber_of_zero.{0, 0, 0} ∧
  type_of% @Morse.eq_of_altSum_le_of_lacunary ∧
  type_of% @Morse.lacunary_of_odd ∧
  type_of% @Morse.FiltrationHomology.finrank_eq_morseNumber_of_lacunary.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.eq_of_altSum_le_succ, @Morse.eq_of_altSum_le_zero,
    @Morse.FiltrationHomology.finrank_eq_morseNumber_of_succ.{0, 0, 0},
    @Morse.FiltrationHomology.finrank_eq_morseNumber_of_zero.{0, 0, 0},
    @Morse.eq_of_altSum_le_of_lacunary, @Morse.lacunary_of_odd,
    @Morse.FiltrationHomology.finrank_eq_morseNumber_of_lacunary.{0, 0, 0}⟩

/-- A ⇒ B: the Morse inequalities `(4_λ)` for a compact manifold are the project's
`altSum_bettiNumber_le_of_compactSpace` (not among the listed declarations); Corollary 5.4 is then
A's arithmetic `eq_of_altSum_le_succ` / `eq_of_altSum_le_zero`. -/
theorem A_to_B : A → B := by
  intro hA F _ E _ _ _ M _ _ _ _ _ f hf hnd l hC1 hC0
  have hg : Morse.IsMorseFunction E f := ⟨hf, fun p hp ↦ (hnd p hp).2⟩
  have hR : ∀ i, Rabs F M i = bettiNumber F M i := fun i ↦
    finrank_subsetHomology_eq_bettiNumber (𝕜 := F) (Set.empty_subset _) rfl rfl i
  have hCn : ∀ i, Cnum E f i = Morse.critCount E f i := fun _ ↦ rfl
  have h4 := altSum_bettiNumber_le_of_compactSpace (𝕜 := F) hg
  simp only [hR, hCn] at hC1 hC0 ⊢
  rcases l with _ | l
  · have := hA.2.1 (fun _ ↦ Nat.cast_nonneg _) h4 (by simp [hC1])
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2, Or.inl rfl⟩
  · have hC0' : Morse.critCount E f l = 0 := hC0.resolve_left (by omega)
    have := hA.1 (fun _ ↦ Nat.cast_nonneg _) h4 (l := l) (by simp [hC1]) (by simp [hC0'])
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2.1, Or.inr (by exact_mod_cast this.2.2)⟩

#rt_check RoundTrip.V3_15.A_to_B [Morse.eq_of_altSum_le_succ, Morse.eq_of_altSum_le_zero,
  Morse.FiltrationHomology.finrank_eq_morseNumber_of_succ,
  Morse.FiltrationHomology.finrank_eq_morseNumber_of_zero, Morse.eq_of_altSum_le_of_lacunary,
  Morse.lacunary_of_odd, Morse.FiltrationHomology.finrank_eq_morseNumber_of_lacunary]

end RoundTrip.V3_15
