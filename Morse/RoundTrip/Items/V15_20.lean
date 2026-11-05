import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_20

open Finset

namespace RoundTrip.V15_20

/-- The project's statement (universes instantiated at `0`): for odd integers `a_i` (`i ∈ ι`, any
finite type) with some `|a_i| ≥ 3`, `card ι − |Σ a_i| ≤ 2 · bottIndex a` and
`card ι − |Σ a_i| ≤ 4 · spectralIndex (pairSpectrum a)`. -/
def A : Prop :=
  type_of% @Morse.card_sub_abs_sum_le_two_mul_bottIndex.{0} ∧
    type_of% @Morse.card_sub_abs_sum_le_four_mul_spectralIndex.{0}

theorem A_holds : A :=
  ⟨@Morse.card_sub_abs_sum_le_two_mul_bottIndex.{0},
    @Morse.card_sub_abs_sum_le_four_mul_spectralIndex.{0}⟩

/-- Vocabulary: B's `Σ_{a_h > a_j} (a_h − a_j − 2)` is the project's `bottIndex`. -/
theorem gapSum_eq_bottIndex {r : ℕ} (a : Fin r → ℤ) : gapSum a = Morse.bottIndex a := by
  unfold gapSum Morse.bottIndex
  rw [Finset.sum_filter, ← Fintype.sum_prod_type' (fun i j => if a j < a i then a i - a j - 2 else 0)]

/-- Outright: if some `a_h ≤ −3` then `r + Σ a ≤ 2 · bottIndex a` (Milnor's `2p ≥ r + c`, with
`bottIndex ≥ Σ_{a_i > 0, a_j < 0} (a_i − a_j − 2) ≥ p + P`). -/
theorem card_add_sum_le {ι : Type} [Fintype ι] {a : ι → ℤ} (ha : ∀ i, Odd (a i))
    (h3 : ∃ i, a i ≤ -3) : (Fintype.card ι : ℤ) + ∑ i, a i ≤ 2 * Morse.bottIndex a := by
  obtain ⟨P, N, Sp, Sn, hP0, hN0, hPN, hc, hSpP, hSnN, hbound, -, hneg3⟩ :=
    Morse.exists_pos_neg_data ha
  obtain ⟨i₀, hi₀⟩ := h3
  obtain ⟨h1, h2⟩ := hneg3 i₀ hi₀
  rw [← hPN, ← hc]
  nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 hSpP), mul_nonneg hP0 (sub_nonneg.2 h1)]

/-- A ⇒ B. If `c = Σ a_h ≤ 0`, B's `r + c ≤ 4λ` is A's `r − |c| ≤ 2 · bottIndex ≤ 4λ`. If `c > 0`,
B's bound is sharper than A's (`r + c > r − |c|`) and is proved outright (`card_add_sum_le`):
A only records the combined conclusion `r − |c|` of the two cases `a_h = −3`, `a_h = +3`. -/
theorem A_to_B : A → B := by
  rintro ⟨hA, -⟩ r a lam hodd hbig hgap h3
  rw [gapSum_eq_bottIndex] at hgap
  rcases le_or_gt (∑ h, a h) 0 with hc | hc
  · have := hA (ι := Fin r) hodd (by
      obtain ⟨h, hh⟩ := hbig
      exact ⟨h, by rcases le_abs'.1 hh with h' | h' <;> [right; left] <;> linarith⟩)
    rw [Fintype.card_fin, abs_of_nonpos hc] at this
    linarith
  · have := card_add_sum_le (ι := Fin r) hodd (by obtain ⟨h, hh⟩ := h3; exact ⟨h, hh.le⟩)
    rw [Fintype.card_fin] at this
    linarith

/-- A sequence on an arbitrary finite type, transported to `Fin (card ι)`. -/
theorem B_reindex (hB : B) {ι : Type} [Fintype ι] {a : ι → ℤ} (ha : ∀ i, Odd (a i))
    (h3 : ∃ i, a i = -3) : (Fintype.card ι : ℤ) + ∑ i, a i ≤ 2 * Morse.bottIndex a := by
  set e := (Fintype.equivFin ι).symm
  set a' : Fin (Fintype.card ι) → ℤ := a ∘ e
  have hb : Morse.bottIndex a' = Morse.bottIndex a := Morse.bottIndex_comp_equiv a e
  have hs : ∑ i, a' i = ∑ i, a i := Equiv.sum_comp e a
  have h2 := Morse.two_mul_spectralIndex_pairSpectrum (k := a') (fun i => ha _)
  obtain ⟨i₀, hi₀⟩ := h3
  have := hB (Fintype.card ι) a' (Morse.spectralIndex (Morse.pairSpectrum a')) (fun i => ha _)
    ⟨e.symm i₀, by simp [a', hi₀]⟩ (by rw [gapSum_eq_bottIndex, ← h2])
    ⟨e.symm i₀, by simp [a', hi₀]⟩
  rw [hs] at this
  linarith

/-- B ⇒ A. B is Milnor's example case "some `a_h = −3`" (with the sharper `r + c`); with `a ↦ −a`
(`bottIndex_neg`) it also gives the case `a_h = +3`, and both give A's `r − |c|`. When the only
large `|a_h|` are `≥ 5` (no `a_h = ±3`), B does not apply and A's bound is re-proved outright from
the project's counting lemma `exists_pos_neg_data` (Milnor's "for example" leaves this case to the
reader). A's spectral form is the `bottIndex` form via `two_mul_spectralIndex_pairSpectrum`. -/
theorem B_to_A : B → A := by
  intro hB
  have key : ∀ {ι : Type} [Fintype ι] {a : ι → ℤ}, (∀ i, Odd (a i)) →
      (∃ i, 3 ≤ a i ∨ a i ≤ -3) → (Fintype.card ι : ℤ) - |∑ i, a i| ≤ 2 * Morse.bottIndex a := by
    intro ι _ a ha hnm
    by_cases hm3 : ∃ i, a i = -3
    · have := B_reindex hB ha hm3
      linarith [neg_abs_le (∑ i, a i)]
    by_cases hp3 : ∃ i, a i = 3
    · have := B_reindex hB (a := -a) (fun i => (ha i).neg)
        (by obtain ⟨i, hi⟩ := hp3; exact ⟨i, by simp [hi]⟩)
      rw [Morse.bottIndex_neg] at this
      simp only [Pi.neg_apply, Finset.sum_neg_distrib] at this
      linarith [le_abs_self (∑ i, a i)]
    · -- outright (no `a_h = ±3`)
      obtain ⟨P, N, Sp, Sn, hP0, hN0, hPN, hc, hSpP, hSnN, hbound, hpos3, hneg3⟩ :=
        Morse.exists_pos_neg_data ha
      obtain ⟨i₀, hi₀⟩ := hnm
      rw [← hPN, ← hc]
      rcases hi₀ with h | h
      · obtain ⟨h1, h2⟩ := hpos3 i₀ h
        have : Sn + N ≤ Morse.bottIndex a := by
          nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 hSnN),
            mul_nonneg hN0 (sub_nonneg.2 h1)]
        have := le_abs_self (Sp - Sn)
        linarith
      · obtain ⟨h1, h2⟩ := hneg3 i₀ h
        have : Sp + P ≤ Morse.bottIndex a := by
          nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 hSpP),
            mul_nonneg hP0 (sub_nonneg.2 h1)]
        have := neg_abs_le (Sp - Sn)
        linarith
  refine ⟨@fun ι _ a ha hnm => key ha hnm, @fun ι _ a ha hnm => ?_⟩
  have h1 := key ha hnm
  have h2 := Morse.two_mul_spectralIndex_pairSpectrum ha
  linarith

#rt_check RoundTrip.V15_20.A_to_B [Morse.card_sub_abs_sum_le_two_mul_bottIndex,
  Morse.card_sub_abs_sum_le_four_mul_spectralIndex]
#rt_check RoundTrip.V15_20.B_to_A [Morse.card_sub_abs_sum_le_two_mul_bottIndex,
  Morse.card_sub_abs_sum_le_four_mul_spectralIndex]
#rt_overlap RoundTrip.V15_20.B_to_A [Morse.card_sub_abs_sum_le_two_mul_bottIndex,
  Morse.card_sub_abs_sum_le_four_mul_spectralIndex]

end RoundTrip.V15_20
