import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_8

namespace RoundTrip.V14_8

/-- The project's statement (universe of `κ` instantiated at `0`; `Morse.conjMult`,
`Morse.spectralIndex` are vocabulary): the index of a spectrum is the sum over the eigenvalues of
their numbers of conjugate parameters in `(0,1)`, and doubling every eigenvalue doubles it. -/
def A : Prop :=
  type_of% @Morse.spectralIndex_eq.{0} ∧ type_of% @Morse.spectralIndex_double.{0}

theorem A_holds : A := ⟨@Morse.spectralIndex_eq.{0}, @Morse.spectralIndex_double.{0}⟩

/-! ### Vocabulary -/

/-- The project's `conjParams` is the blind one restricted to `(0,1)`. -/
theorem conjParams_inter (e : ℝ) : conjParams e ∩ Set.Ioo 0 1 = Morse.conjParams e := by
  ext t
  simp only [conjParams, Morse.conjParams, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨ht0, he, s, rfl⟩, -, ht1⟩
    exact ⟨he, ht0, ht1, s, by ring⟩
  · rintro ⟨he, ht0, ht1, s, rfl⟩
    exact ⟨⟨ht0, he, s, by ring⟩, ht0, ht1⟩

theorem mem_conjParams_iff {e t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    t ∈ conjParams e ↔ t ∈ Morse.conjParams e := by
  rw [← conjParams_inter]
  exact ⟨fun h => ⟨h, ht⟩, fun h => h.1⟩

/-- The blind index of a spectrum is the project's `spectralIndex`. -/
theorem specIndex_eq_spectralIndex {κ : Type} [Fintype κ] (e : κ → ℝ) :
    specIndex e = Morse.spectralIndex e := by
  classical
  rw [specIndex, Morse.spectralIndex, finsum_mem_def]
  congr 1
  funext t
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
  · rw [Set.indicator_of_mem ht, specMult, Morse.conjMult]
    have : {i | t ∈ conjParams (e i)} =
        ((Finset.univ.filter fun i => t ∈ Morse.conjParams (e i) : Finset κ) : Set κ) := by
      ext i
      simp [mem_conjParams_iff ht]
    rw [this, Set.ncard_coe_finset]
  · rw [Set.indicator_of_notMem ht, Morse.conjMult]
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hi
    exact ht ⟨hi.2.1, hi.2.2.1⟩

theorem A_to_B : A → B := by
  rintro ⟨hA1, -⟩ κ _ e
  refine ⟨?_, ?_⟩
  · simp_rw [conjParams_inter]
    exact Set.finite_iUnion fun i => Morse.conjParams_finite (e i)
  · rw [specIndex_eq_spectralIndex, hA1]
    simp_rw [conjParams_inter]

theorem B_to_A : B → A := by
  intro hB
  have heq : ∀ {κ : Type} [Fintype κ] (e : κ → ℝ),
      Morse.spectralIndex e = ∑ i, (Morse.conjParams (e i)).ncard := by
    intro κ _ e
    rw [← specIndex_eq_spectralIndex, (hB κ e).2]
    simp_rw [conjParams_inter]
  refine ⟨@heq, fun {κ} _ e => ?_⟩
  rw [heq, heq, Fintype.sum_prod_type, Finset.mul_sum]
  simp [two_mul]

#rt_check RoundTrip.V14_8.A_to_B [Morse.spectralIndex_eq, Morse.spectralIndex_double]
#rt_check RoundTrip.V14_8.B_to_A [Morse.spectralIndex_eq, Morse.spectralIndex_double]
#rt_overlap RoundTrip.V14_8.B_to_A [Morse.spectralIndex_eq, Morse.spectralIndex_double]
#rt_overlap RoundTrip.V14_8.A_to_B [Morse.spectralIndex_eq, Morse.spectralIndex_double]

end RoundTrip.V14_8
