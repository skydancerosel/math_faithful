import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_10

open CategoryTheory Morse.Homology

namespace RoundTrip.V3_10

/-- The project's statement (the six listed theorems), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.LongExactSeq.finrank_le.{0, 0, 0, 0} ∧
  type_of% @Morse.LongExactSeq.finiteDimensional_middle.{0, 0, 0, 0} ∧
  type_of% @Morse.FiltrationHomology.isSubadditive_finrank.{0, 0, 0} ∧
  type_of% @Morse.altSum_finrank_eq_zero_of_exact.{0, 0} ∧
  type_of% @Morse.LongExactSeq.altSum_eq_of_finrank_eq_zero.{0, 0, 0, 0} ∧
  type_of% @Morse.FiltrationHomology.isAdditive_eulerChar.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.LongExactSeq.finrank_le.{0, 0, 0, 0},
    @Morse.LongExactSeq.finiteDimensional_middle.{0, 0, 0, 0},
    @Morse.FiltrationHomology.isSubadditive_finrank.{0, 0, 0},
    @Morse.altSum_finrank_eq_zero_of_exact.{0, 0},
    @Morse.LongExactSeq.altSum_eq_of_finrank_eq_zero.{0, 0, 0, 0},
    @Morse.FiltrationHomology.isAdditive_eulerChar.{0, 0, 0}⟩

/-- `χ` as a finite sum, once `R_i = 0` for `i > N`. -/
lemma chi_eq {F : Type} [Field F] {E : Type} [TopologicalSpace E] {P Q : Set E} (h : P ⊆ Q)
    (N : ℕ) (hN : ∀ i, N < i → R F h i = 0) :
    chi F h = ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (R F h i : ℤ) := by
  unfold chi
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simp only [Function.mem_support] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  exact hi (by rw [hN i (by omega)]; simp)

theorem A_to_B : A → B := by
  intro hA F _ E _ X Y Z hZY hYX h1 h2 h3
  let L := subsetTripleLongExactSeq F hZY hYX
  have : ∀ i, FiniteDimensional F (subsetHomology F i hZY) := h1
  have : ∀ i, FiniteDimensional F (subsetHomology F i hYX) := h2
  have : ∀ i, FiniteDimensional F (subsetHomology F i (hZY.trans hYX)) := h3
  have hle : ∀ l, R F (hZY.trans hYX) l ≤ R F hZY l + R F hYX l :=
    fun l => hA.1 L l
  refine ⟨fun l => by have := hle l; unfold R at this ⊢; omega, ?_⟩
  rintro ⟨N1, hN1⟩ ⟨N2, hN2⟩ ⟨N3, hN3⟩
  set N := N1 + N2 + N3
  have hv : ∀ {P Q : Set E} (h : P ⊆ Q) (M : ℕ), (∀ i, M ≤ i → R F h i = 0) → M ≤ N →
      ∀ i, N < i → R F h i = 0 := fun h M hM hMN i hi => hM i (by omega)
  rw [chi_eq _ N (hv _ N3 hN3 (by omega)), chi_eq _ N (hv _ N2 hN2 (by omega)),
    chi_eq _ N (hv _ N1 hN1 (by omega))]
  have key := hA.2.2.2.2.1 L (N := N) (hv _ N2 hN2 (by omega) (N + 1) (by omega))
  have e : ∀ {P Q : Set E} (h : P ⊆ Q), ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (R F h i : ℤ)
      = (-1) ^ N * Morse.altSum (fun i => (Module.finrank F (subsetHomology F i h) : ℤ)) N :=
    fun h => Morse.sum_neg_one_pow_mul_eq _ N
  rw [e, e, e]
  rw [key]
  ring

#rt_check RoundTrip.V3_10.A_to_B [Morse.LongExactSeq.finrank_le,
  Morse.LongExactSeq.finiteDimensional_middle, Morse.FiltrationHomology.isSubadditive_finrank,
  Morse.altSum_finrank_eq_zero_of_exact, Morse.LongExactSeq.altSum_eq_of_finrank_eq_zero,
  Morse.FiltrationHomology.isAdditive_eulerChar]

end RoundTrip.V3_10
