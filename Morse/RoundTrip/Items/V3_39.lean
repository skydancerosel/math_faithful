import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_39

open CategoryTheory Morse Morse.Homology Module Finset
open scoped ContDiff Manifold

namespace RoundTrip.V3_39

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

/-- The project's statement: the seven listed theorems, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.Homology.finiteDimensional_spaceHomology_of_isCompact.{0} ∧
  type_of% @Morse.Homology.finiteDimensional_spaceHomology_of_compactSpace.{0, 0} ∧
  type_of% @Morse.Homology.bettiNumber_eq_zero_of_compactSpace.{0, 0} ∧
  type_of% @Morse.Homology.bettiNumber_le_critCount_of_compactSpace.{0, 0} ∧
  type_of% @Morse.Homology.altSum_bettiNumber_le_of_compactSpace.{0, 0} ∧
  type_of% @Morse.Homology.sum_bettiNumber_eq_sum_critCount_of_compactSpace.{0, 0} ∧
  type_of% @Morse.Homology.bettiNumber_eq_critCount_of_lacunary_of_compactSpace.{0, 0}

theorem A_holds : A :=
  ⟨@Morse.Homology.finiteDimensional_spaceHomology_of_isCompact.{0},
    @Morse.Homology.finiteDimensional_spaceHomology_of_compactSpace.{0, 0},
    @Morse.Homology.bettiNumber_eq_zero_of_compactSpace.{0, 0},
    @Morse.Homology.bettiNumber_le_critCount_of_compactSpace.{0, 0},
    @Morse.Homology.altSum_bettiNumber_le_of_compactSpace.{0, 0},
    @Morse.Homology.sum_bettiNumber_eq_sum_critCount_of_compactSpace.{0, 0},
    @Morse.Homology.bettiNumber_eq_critCount_of_lacunary_of_compactSpace.{0, 0}⟩

lemma Rabs_eq (F : Type) [Field F] (X : Type) [TopologicalSpace X] (i : ℕ) :
    Rabs F X i = bettiNumber F X i :=
  finrank_subsetHomology_eq_bettiNumber (𝕜 := F) (Set.empty_subset _) rfl rfl i

lemma alt_eq (d : ℕ → ℤ) (l : ℕ) : alt d l = altSum d l := rfl

/-- A ⇒ B: A's clauses 4–6 are B's (2), (3), `(4_λ)`; Corollary 5.4 is the project's arithmetic
`eq_of_altSum_le_succ` / `eq_of_altSum_le_zero` applied to `(4_λ)`. -/
theorem A_to_B : A → B := by
  intro hA F _ E _ _ _ M _ _ _ _ _ f hf hnd
  have hg : IsMorseFunction E f := ⟨hf, fun p hp ↦ (hnd p hp).2⟩
  have hCn : ∀ i, Cnum E f i = critCount E f i := fun _ ↦ rfl
  have h4 : ∀ l, altSum (fun i ↦ (bettiNumber F M i : ℤ)) l ≤
      altSum (fun i ↦ (critCount E f i : ℤ)) l := hA.2.2.2.2.1 (𝕜 := F) hg
  simp only [alt_eq, Rabs_eq, hCn]
  refine ⟨⟨fun l ↦ hA.2.2.2.1 (𝕜 := F) hg l, hA.2.2.2.2.2.1 (𝕜 := F) hg⟩, h4, ?_⟩
  intro l hC1 hC0
  rcases l with _ | l
  · have := eq_of_altSum_le_zero (fun _ ↦ Nat.cast_nonneg _) h4 (by simp [hC1])
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2, Or.inl rfl⟩
  · have hC0' : critCount E f l = 0 := hC0.resolve_left (by omega)
    have := eq_of_altSum_le_succ (fun _ ↦ Nat.cast_nonneg _) h4 (l := l) (by simp [hC1])
      (by simp [hC0'])
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2.1,
      Or.inr (by exact_mod_cast this.2.2)⟩

/-- B ⇒ A. B's clauses give (2), (3), `(4_λ)`, the lacunary principle (`eq_of_altSum_le_of_lacunary`
on `(4_λ)`) and `b_i = 0` above the dimension (`b_i ≤ C_i = 0`). B is stated with `finrank` and
says nothing about finite-dimensionality: the two finiteness clauses are proved from the project's
`finiteDimensional_spaceHomology` (the Morse filtration of `L_p`, not a listed theorem) and the
Whitney embedding `exists_whitney_normSq`, exactly as the project does; B is not used for them. -/
theorem B_to_A : B → A := by
  intro hB
  have hfinN : type_of% @Morse.Homology.finiteDimensional_spaceHomology_of_isCompact.{0} := by
    intro 𝕜 _ n k w N hN hNc T _ e i
    let _ := hN.chartedSpace
    obtain ⟨p, hp⟩ := Morse.exists_isMorseFunction_normSq_sub (hM := hN)
    exact finiteDimensional_spaceHomology hN hNc (Homology.contDiff_normSq_sub p) hp.isNondegenerate e i
  have hB' : ∀ (𝕜 : Type) [Field 𝕜] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
      [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] (g : M → ℝ),
      IsMorseFunction E g → _ := fun 𝕜 _ E _ _ _ M _ _ _ _ _ g hg ↦
    hB 𝕜 E M g hg.contMDiff (fun p hp ↦ ⟨hp, hg.isNondegenerate p hp⟩)
  have hCn : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (M : Type)
      [TopologicalSpace M] [ChartedSpace E M] (g : M → ℝ) i,
      Cnum E g i = critCount E g i := fun _ _ _ _ _ _ _ _ ↦ rfl
  have hstrong : type_of% @Morse.Homology.altSum_bettiNumber_le_of_compactSpace.{0, 0} := by
    intro 𝕜 _ E _ _ _ M _ _ _ _ _ g hg l
    have := (hB' 𝕜 E M g hg).2.1 l
    simpa only [alt_eq, Rabs_eq, hCn] using this
  refine ⟨hfinN, ?_, ?_, ?_, hstrong, ?_, ?_⟩
  · intro 𝕜 _ E _ _ _ M _ _ _ _ _ i
    obtain ⟨K, m, N, hN, p, Φ, hNc, -⟩ := exists_whitney_normSq E M
    exact hfinN hN hNc Φ i
  · intro 𝕜 _ E _ _ _ M _ _ _ _ _ i hi
    obtain ⟨K, m, N, hN, p, Φ, hNc, -, f, -, hf, -⟩ := exists_whitney_normSq E M
    have h := (hB' 𝕜 E M f hf).1.1 i
    have hempty : {q : M | IsCriticalPointM E f q ∧ indexM E f q = i} = ∅ :=
      Set.eq_empty_of_forall_notMem fun q hq ↦
        absurd (indexM_le_finrank (E := E) f q) (by have := hq.2; omega)
    have h0 : Cnum E f i = 0 := by
      unfold Cnum
      rw [hempty, Set.ncard_empty]
    rw [Rabs_eq] at h
    omega
  · intro 𝕜 _ E _ _ _ M _ _ _ _ _ g hg l
    have := (hB' 𝕜 E M g hg).1.1 l
    simpa only [Rabs_eq, hCn] using this
  · intro 𝕜 _ E _ _ _ M _ _ _ _ _ g hg
    have := (hB' 𝕜 E M g hg).1.2
    simpa only [Rabs_eq, hCn] using this
  · intro 𝕜 _ E _ _ _ M _ _ _ _ _ g hg hc i
    have := eq_of_altSum_le_of_lacunary (b := fun i ↦ (bettiNumber 𝕜 M i : ℤ))
      (c := fun i ↦ (critCount E g i : ℤ)) (fun _ ↦ Nat.cast_nonneg _)
      (hstrong hg) (fun i ↦ by exact_mod_cast hc i) i
    exact_mod_cast this

#rt_check RoundTrip.V3_39.A_to_B [Morse.Homology.finiteDimensional_spaceHomology_of_isCompact,
  Morse.Homology.finiteDimensional_spaceHomology_of_compactSpace,
  Morse.Homology.bettiNumber_eq_zero_of_compactSpace,
  Morse.Homology.bettiNumber_le_critCount_of_compactSpace,
  Morse.Homology.altSum_bettiNumber_le_of_compactSpace,
  Morse.Homology.sum_bettiNumber_eq_sum_critCount_of_compactSpace,
  Morse.Homology.bettiNumber_eq_critCount_of_lacunary_of_compactSpace]
#rt_check RoundTrip.V3_39.B_to_A [Morse.Homology.finiteDimensional_spaceHomology_of_isCompact,
  Morse.Homology.finiteDimensional_spaceHomology_of_compactSpace,
  Morse.Homology.bettiNumber_eq_zero_of_compactSpace,
  Morse.Homology.bettiNumber_le_critCount_of_compactSpace,
  Morse.Homology.altSum_bettiNumber_le_of_compactSpace,
  Morse.Homology.sum_bettiNumber_eq_sum_critCount_of_compactSpace,
  Morse.Homology.bettiNumber_eq_critCount_of_lacunary_of_compactSpace]
#rt_overlap RoundTrip.V3_39.B_to_A [Morse.Homology.finiteDimensional_spaceHomology_of_isCompact,
  Morse.Homology.finiteDimensional_spaceHomology_of_compactSpace,
  Morse.Homology.bettiNumber_eq_zero_of_compactSpace,
  Morse.Homology.bettiNumber_le_critCount_of_compactSpace,
  Morse.Homology.altSum_bettiNumber_le_of_compactSpace,
  Morse.Homology.sum_bettiNumber_eq_sum_critCount_of_compactSpace,
  Morse.Homology.bettiNumber_eq_critCount_of_lacunary_of_compactSpace]

end RoundTrip.V3_39
