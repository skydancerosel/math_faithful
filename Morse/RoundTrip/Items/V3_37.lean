import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V3_37

open CategoryTheory Morse Morse.Homology Module Finset
open scoped ContDiff Manifold

namespace RoundTrip.V3_37

/-- The project's statement: the three listed theorems, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.Homology.bettiNumber_eq_critCount_of_succ.{0, 0, 0, 0} ∧
  type_of% @Morse.Homology.bettiNumber_eq_critCount_of_zero.{0, 0, 0, 0} ∧
  type_of% @Morse.Homology.bettiNumber_eq_critCount_of_lacunary.{0, 0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.Homology.bettiNumber_eq_critCount_of_succ.{0, 0, 0, 0},
    @Morse.Homology.bettiNumber_eq_critCount_of_zero.{0, 0, 0, 0},
    @Morse.Homology.bettiNumber_eq_critCount_of_lacunary.{0, 0, 0, 0}⟩

lemma Rabs_eq (F : Type) [Field F] (X : Type) [TopologicalSpace X] (i : ℕ) :
    Rabs F X i = bettiNumber F X i :=
  finrank_subsetHomology_eq_bettiNumber (𝕜 := F) (Set.empty_subset _) rfl rfl i

/-- A ⇒ B: Whitney copy (`Glue.exists_ambient_any_dim`), then A's `of_succ` (`λ ≥ 1`) or
`of_zero` (`λ = 0`) with `e = Φ`. -/
theorem A_to_B : A → B := by
  intro hA F _ E _ _ _ M _ _ _ _ _ f hf hnd l hC1 hC0
  have hg : IsMorseFunction E f := ⟨hf, fun p hp ↦ (hnd p hp).2⟩
  obtain ⟨n, K, m, N, hN, G, Φ, -, hNc, hG, hGnd, hcount⟩ := Glue.exists_ambient_any_dim hg
  let _ := hN.chartedSpace
  have hCn : ∀ i, Cnum E f i = critCount E f i := fun _ ↦ rfl
  simp only [Rabs_eq, hCn, hcount] at hC1 hC0 ⊢
  rcases l with _ | l
  · obtain ⟨h1, h2⟩ := hA.2.1 (𝕜 := F) hN hNc hG hGnd Φ hC1
    exact ⟨h1, h2, Or.inl rfl⟩
  · have hC0' := hC0.resolve_left (by omega)
    obtain ⟨h1, h2, h3⟩ := hA.1 (𝕜 := F) hN hNc hG hGnd Φ (l := l) hC1 hC0'
    exact ⟨h1, h2, Or.inr h3⟩

/-- The lacunary principle from Corollary 5.4 alone (pure arithmetic): if `C_i = 0` one of the
neighbouring corollaries (at `i - 1`, `i` or `i + 1`) applies. -/
lemma lacunary_of_cor {b c : ℕ → ℕ}
    (hcor : ∀ l, c (l + 1) = 0 → (l = 0 ∨ c (l - 1) = 0) →
      b l = c l ∧ b (l + 1) = 0 ∧ (l = 0 ∨ b (l - 1) = 0))
    (hc : ∀ i, c i = 0 ∨ c (i + 1) = 0) (i : ℕ) : b i = c i := by
  by_cases hci : c i = 0
  · by_cases hci1 : c (i + 1) = 0
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact (hcor 0 hci1 (Or.inl rfl)).1
      · by_cases hcm : c (i - 1) = 0
        · exact (hcor i hci1 (Or.inr hcm)).1
        · -- `C_{i-1} ≠ 0`: Corollary 5.4 at `i - 1`
          obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
          have hj : j = 0 ∨ c (j - 1) = 0 := by
            rcases Nat.eq_zero_or_pos j with h | h
            · exact Or.inl h
            · right
              have := hc (j - 1)
              rw [show j - 1 + 1 = j by omega] at this
              exact this.resolve_right (by simpa using hcm)
          rw [hci]
          exact (hcor j hci hj).2.1
    · -- `C_{i+1} ≠ 0`, so `C_{i+2} = 0`: Corollary 5.4 at `i + 1`
      have h2 : c (i + 2) = 0 := (hc (i + 1)).resolve_left hci1
      have := (hcor (i + 1) h2 (Or.inr (by simpa using hci))).2.2
      rw [hci]
      simpa using this
  · have h1 : c (i + 1) = 0 := (hc i).resolve_left hci
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact (hcor 0 h1 (Or.inl rfl)).1
    · have hm : c (i - 1) = 0 := by
        have := hc (i - 1)
        rw [show i - 1 + 1 = i by omega] at this
        exact this.resolve_right hci
      exact (hcor i h1 (Or.inr hm)).1

/-- B ⇒ A: B on the compact manifold `N` with `F|N`, transported along `e`; the lacunary
principle is derived from B's Corollary 5.4 by `lacunary_of_cor`. -/
theorem B_to_A : B → A := by
  intro hB
  have key : ∀ (𝕜 : Type) [Field 𝕜] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
      {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V} {T : Type}
      [TopologicalSpace T] (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N), IsCompact N →
      ∀ {F : V → ℝ}, ContDiff ℝ ∞ F →
      (letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
        IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) → T ≃ₜ N →
      letI := hN.chartedSpace
      ∀ l, critCount Z (F ∘ Subtype.val : N → ℝ) (l + 1) = 0 →
        (l = 0 ∨ critCount Z (F ∘ Subtype.val : N → ℝ) (l - 1) = 0) →
        bettiNumber 𝕜 T l = critCount Z (F ∘ Subtype.val : N → ℝ) l ∧
          bettiNumber 𝕜 T (l + 1) = 0 ∧ (l = 0 ∨ bettiNumber 𝕜 T (l - 1) = 0) := by
    intro 𝕜 _ V _ _ Z _ _ _ W _ _ N T _ hN hNc F hF hnd e
    let _ := hN.chartedSpace
    have := hN.isManifold
    have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
    have h := hB 𝕜 Z N (F ∘ Subtype.val) (contMDiff_comp_val hN hF)
      (fun p hp ↦ ⟨hp, hnd p hp⟩)
    have hb : ∀ i, bettiNumber 𝕜 T i = Rabs 𝕜 N i := fun i ↦
      (bettiNumber_eq_of_homeomorph e i).trans (Rabs_eq 𝕜 N i).symm
    simp only [hb]
    exact h
  refine ⟨?_, ?_, ?_⟩
  · intro 𝕜 _ V _ _ _ Z _ _ _ W _ _ N T _ hN hNc F hF hnd e l h₂ h₀
    have := key 𝕜 hN hNc hF hnd e (l + 1) h₂ (Or.inr h₀)
    exact ⟨this.1, this.2.1, this.2.2.resolve_left (by omega)⟩
  · intro 𝕜 _ V _ _ _ Z _ _ _ W _ _ N T _ hN hNc F hF hnd e h₁
    have := key 𝕜 hN hNc hF hnd e 0 h₁ (Or.inl rfl)
    exact ⟨this.1, this.2.1⟩
  · intro 𝕜 _ V _ _ _ Z _ _ _ W _ _ N T _ hN hNc F hF hnd e hc i
    exact lacunary_of_cor (key 𝕜 hN hNc hF hnd e) hc i

#rt_check RoundTrip.V3_37.A_to_B [Morse.Homology.bettiNumber_eq_critCount_of_succ,
  Morse.Homology.bettiNumber_eq_critCount_of_zero, Morse.Homology.bettiNumber_eq_critCount_of_lacunary]
#rt_check RoundTrip.V3_37.B_to_A [Morse.Homology.bettiNumber_eq_critCount_of_succ,
  Morse.Homology.bettiNumber_eq_critCount_of_zero, Morse.Homology.bettiNumber_eq_critCount_of_lacunary]
#rt_overlap RoundTrip.V3_37.B_to_A [Morse.Homology.bettiNumber_eq_critCount_of_succ,
  Morse.Homology.bettiNumber_eq_critCount_of_zero, Morse.Homology.bettiNumber_eq_critCount_of_lacunary]

end RoundTrip.V3_37
