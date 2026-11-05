import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V3_38

open CategoryTheory Morse Morse.Homology Module Finset
open scoped ContDiff Manifold

namespace RoundTrip.V3_38

/-- The project's statement: the two listed theorems, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.IsEulerNumber.eq_sum_bettiNumber.{0} ∧
  type_of% @Morse.Homology.eulerNumberM_eq_sum_bettiNumber.{0, 0}

theorem A_holds : A :=
  ⟨@Morse.IsEulerNumber.eq_sum_bettiNumber.{0},
    @Morse.Homology.eulerNumberM_eq_sum_bettiNumber.{0, 0}⟩

lemma Rabs_eq (F : Type) [Field F] (X : Type) [TopologicalSpace X] (i : ℕ) :
    Rabs F X i = bettiNumber F X i :=
  finrank_subsetHomology_eq_bettiNumber (𝕜 := F) (Set.empty_subset _) rfl rfl i

lemma chiN_eq (F : Type) [Field F] {K : ℕ} (d : ℕ) (N : Set (Rn (K + 1))) :
    chiN F d N = ∑ i ∈ range (d + 2), (-1 : ℤ) ^ i * (bettiNumber F N i : ℤ) := by
  unfold chiN
  simp only [Rabs_eq]

/-- A ⇒ B. `K = 0` is vacuous (`Glue.no_sliceSubmanifold_R1`). Otherwise the Poincaré–Hopf
integer `χN` (the project's `exists_isEulerNumber`, outside the item) is `χ(N; F)` by A's first
clause, which gives B's index-sum clause; B's formula (3) is A's second clause for `N` as an
abstract manifold, with the project's `sum_critCount_eq_eulerNumberM` (well-definedness of the
alternating count, outside the item). -/
theorem A_to_B : A → B := by
  intro hA F _ K d m N hN hc hne
  let _ := hN.chartedSpace
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact (Glue.no_sliceSubmanifold_R1 hN hc hne).elim
  obtain ⟨χN, hχ⟩ := exists_isEulerNumber hN hc hne hK
  have hχc : χN = chiN F d N := by
    rw [chiN_eq]
    exact hA.1 hN hc hne (Homeomorph.refl N) hK hχ
  refine ⟨fun v hv hvT hfin ↦ ?_, fun Φ hΦ hnd ↦ ?_⟩
  · obtain ⟨j, z, hz, hzS⟩ := Glue.exists_enum hfin
    rw [← Glue.sum_enum_eq_finsum _ _ z hz hzS, hχ v hv hvT z hz hzS, hχc]
  · have := hN.isManifold
    have : CompactSpace N := isCompact_iff_compactSpace.1 hc
    have hΦ' : ContDiff ℝ ∞ Φ := contMDiff_iff_contDiff.1 hΦ
    have hM : IsMorseFunction (Rn (d + 1)) (Φ ∘ Subtype.val : N → ℝ) :=
      ⟨contMDiff_comp_val hN hΦ', fun q hq ↦ (hnd q hq).2⟩
    have h1 := sum_critCount_eq_eulerNumberM hM
    have h2 := hA.2 (𝕜 := F) (E := Rn (d + 1)) (M := N)
    rw [finrank_euclideanSpace_fin] at h1 h2
    rw [chiN_eq, ← h2, ← h1]
    rfl

/-- B ⇒ A. First clause: an Euler number is the index sum of the tangential gradient of `L_p`,
which B's first clause identifies with `χ(N; 𝕜)` (`Glue.eq_of_isEulerNumber`). Second clause: for
a nonempty `M` of dimension `d + 1 ≥ 1`, B's formula (3) on a Whitney copy `N` (with `L_p`).
B has no content for `dim M = 0` or `M = ∅` (its `N` is nonempty and of dimension `≥ 1`); there the
identity is the project's Morse inequality `sum_bettiNumber_eq_sum_critCount` (outside the item)
for `L_p` on a Whitney copy. -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · intro 𝕜 _ K d m N hN hNc hne T _ e hK χN hχ
    rw [Glue.eq_of_isEulerNumber hN hNc hne hχ (hB 𝕜 K d m N hN hNc hne).1, chiN_eq]
    simp only [bettiNumber_eq_of_homeomorph e]
  · intro 𝕜 _ E _ _ _ M _ _ _ _ _
    obtain ⟨n, hn⟩ : ∃ n, finrank ℝ E = n := ⟨_, rfl⟩
    by_cases hgood : 0 < n ∧ Nonempty M
    · obtain ⟨hn0, ⟨x₀⟩⟩ := hgood
      obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
      obtain ⟨K, m, N, hN, hK, hNc, -, ⟨Φ⟩⟩ :=
        exists_diffeomorph_sliceSubmanifold (E := E) (M := M) hn
      let _ := hN.chartedSpace
      have := hN.isManifold
      have hne : N.Nonempty := ⟨_, (Φ x₀).2⟩
      obtain ⟨p, hp⟩ := exists_isMorseFunction_normSq_sub (hM := hN)
      have hf : IsMorseFunction E
          (((fun x : Rn (K + 1) ↦ ‖x - p‖ ^ 2) ∘ (Subtype.val : N → Rn (K + 1))) ∘ Φ) :=
        hp.comp_diffeomorph_symm Φ.symm
      have hcount : ∀ k, critCount E
          (((fun x : Rn (K + 1) ↦ ‖x - p‖ ^ 2) ∘ (Subtype.val : N → Rn (K + 1))) ∘ Φ) k =
          critCount (Rn (d + 1)) ((fun x : Rn (K + 1) ↦ ‖x - p‖ ^ 2) ∘ (Subtype.val : N → Rn (K + 1))) k :=
        fun k ↦ critCount_comp_symm Φ.symm (hp.contMDiff.of_le (by norm_cast)) k
      have h3 := (hB 𝕜 K d m N hN hNc hne).2 _
        (contMDiff_iff_contDiff.2 (Homology.contDiff_normSq_sub p))
        (fun q hq ↦ ⟨hq, hp.isNondegenerate q hq⟩)
      rw [← sum_critCount_eq_eulerNumberM hf, hn]
      simp only [hcount]
      rw [chiN_eq] at h3
      simp only [bettiNumber_eq_of_homeomorph Φ.toHomeomorph]
      exact h3
    · -- `dim M = 0` or `M = ∅`: B says nothing; the project's Morse inequality (3) for `L_p`
      obtain ⟨K, m, N, hN, p, Φ, hNc, hp, f, -, hf, hcount⟩ := exists_whitney_normSq E M
      let _ := hN.chartedSpace
      rw [← sum_critCount_eq_eulerNumberM hf]
      simp only [hcount]
      have h := sum_bettiNumber_eq_sum_critCount (𝕜 := 𝕜) hN hNc (Homology.contDiff_normSq_sub p)
        hp.isNondegenerate Φ
      rw [finrank_euclideanSpace_fin] at h
      exact h.symm

#rt_check RoundTrip.V3_38.A_to_B [Morse.IsEulerNumber.eq_sum_bettiNumber,
  Morse.Homology.eulerNumberM_eq_sum_bettiNumber]
#rt_check RoundTrip.V3_38.B_to_A [Morse.IsEulerNumber.eq_sum_bettiNumber,
  Morse.Homology.eulerNumberM_eq_sum_bettiNumber]
#rt_overlap RoundTrip.V3_38.B_to_A [Morse.IsEulerNumber.eq_sum_bettiNumber,
  Morse.Homology.eulerNumberM_eq_sum_bettiNumber]

end RoundTrip.V3_38
