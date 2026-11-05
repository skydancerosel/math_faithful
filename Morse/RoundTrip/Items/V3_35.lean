import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V3_35

open CategoryTheory Morse Morse.Homology Module Finset
open scoped ContDiff Manifold

namespace RoundTrip.V3_35

/-- The project's statement: the six listed theorems, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.Homology.bettiNumber_le_critCount.{0, 0, 0, 0} ∧
  type_of% @Morse.Homology.bettiNumber_le_critCount'.{0, 0, 0} ∧
  type_of% @Morse.Homology.sum_bettiNumber_eq_sum_critCount.{0, 0, 0, 0} ∧
  type_of% @Morse.Homology.sum_bettiNumber_eq_sum_critCount'.{0, 0, 0} ∧
  type_of% @Morse.Homology.bettiNumber_eq_zero_of_finrank_lt.{0, 0, 0, 0} ∧
  type_of% @Morse.Homology.subsingleton_spaceHomology_of_finrank_lt.{0, 0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.Homology.bettiNumber_le_critCount.{0, 0, 0, 0},
    @Morse.Homology.bettiNumber_le_critCount'.{0, 0, 0},
    @Morse.Homology.sum_bettiNumber_eq_sum_critCount.{0, 0, 0, 0},
    @Morse.Homology.sum_bettiNumber_eq_sum_critCount'.{0, 0, 0},
    @Morse.Homology.bettiNumber_eq_zero_of_finrank_lt.{0, 0, 0, 0},
    @Morse.Homology.subsingleton_spaceHomology_of_finrank_lt.{0, 0, 0, 0}⟩

lemma Rabs_eq (F : Type) [Field F] (X : Type) [TopologicalSpace X] (i : ℕ) :
    Rabs F X i = bettiNumber F X i :=
  finrank_subsetHomology_eq_bettiNumber (𝕜 := F) (Set.empty_subset _) rfl rfl i

/-- A ⇒ B: move the abstract compact manifold to a slice submanifold (`Glue.exists_ambient_any_dim`,
from the project's Whitney embedding) and apply A's first and third clauses with `e = Φ`. -/
theorem A_to_B : A → B := by
  intro hA F _ E _ _ _ M _ _ _ _ _ f hf hnd
  have hg : IsMorseFunction E f := ⟨hf, fun p hp ↦ (hnd p hp).2⟩
  obtain ⟨n, K, m, N, hN, G, Φ, hn, hNc, hG, hGnd, hcount⟩ := Glue.exists_ambient_any_dim hg
  let _ := hN.chartedSpace
  have hCn : ∀ i, Cnum E f i = critCount E f i := fun _ ↦ rfl
  refine ⟨fun l ↦ ?_, ?_⟩
  · rw [Rabs_eq, hCn, hcount]
    exact hA.1 (𝕜 := F) hN hNc hG hGnd Φ l
  · have h := hA.2.2.1 (𝕜 := F) hN hNc hG hGnd Φ
    rw [finrank_euclideanSpace_fin] at h
    rw [← hn]
    simp only [Rabs_eq, hCn, hcount]
    exact h

section BtoA

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}

/-- B specialized to a compact slice submanifold `N` and `f = F|N`, read in a space `T ≃ₜ N`. -/
lemma B_sub (hB : B) (𝕜 : Type) [Field 𝕜] (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) {T : Type} [TopologicalSpace T]
    (e : T ≃ₜ N) :
    letI := hN.chartedSpace
    (∀ l, bettiNumber 𝕜 T l ≤ critCount Z (F ∘ Subtype.val : N → ℝ) l) ∧
      ∑ i ∈ range (finrank ℝ Z + 1), (-1 : ℤ) ^ i * (bettiNumber 𝕜 T i : ℤ) =
        ∑ i ∈ range (finrank ℝ Z + 1), (-1 : ℤ) ^ i * (critCount Z (F ∘ Subtype.val : N → ℝ) i : ℤ) := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  obtain ⟨h1, h2⟩ := hB 𝕜 Z N (F ∘ Subtype.val) (contMDiff_comp_val hN hF)
    (fun p hp ↦ ⟨hp, hnd p hp⟩)
  have hb : ∀ i, bettiNumber 𝕜 T i = Rabs 𝕜 N i := fun i ↦
    (bettiNumber_eq_of_homeomorph e i).trans (Rabs_eq 𝕜 N i).symm
  simp only [hb]
  exact ⟨h1, h2⟩

/-- B ⇒ A. The vanishing of `H_i` above the dimension follows from B's `R_i ≤ C_i = 0`; the
`Subsingleton` form needs finite-dimensionality, which B (stated with `finrank`) does not give:
it is the project's `finiteDimensional_spaceHomology_of_isCompact` (not a listed theorem). -/
theorem B_to_A : B → A := by
  intro hB
  have hvan : type_of% @Morse.Homology.bettiNumber_eq_zero_of_finrank_lt.{0, 0, 0, 0} := by
    intro 𝕜 _ V _ _ _ Z _ _ _ W _ _ N T _ hN hNc F hF hnd e i hi
    let _ := hN.chartedSpace
    have h := (B_sub hB 𝕜 hN hNc hF hnd e).1 i
    have hempty : {p : N | IsCriticalPointM Z (F ∘ Subtype.val) p ∧
        indexM Z (F ∘ Subtype.val) p = i} = ∅ :=
      Set.eq_empty_of_forall_notMem fun p hp ↦
        absurd (indexM_le_finrank (E := Z) (F ∘ Subtype.val) p) (by have := hp.2; omega)
    have h0 : critCount Z (F ∘ Subtype.val : N → ℝ) i = 0 := by
      unfold critCount
      rw [hempty, Set.ncard_empty]
    omega
  refine ⟨?_, ?_, ?_, ?_, hvan, ?_⟩
  · intro 𝕜 _ V _ _ _ Z _ _ _ W _ _ N T _ hN hNc F hF hnd e l
    exact (B_sub hB 𝕜 hN hNc hF hnd e).1 l
  · intro V _ _ _ Z _ _ _ W _ _ N 𝕜 _ hN hNc F hF hnd l
    exact (B_sub hB 𝕜 hN hNc hF hnd (Homeomorph.refl N)).1 l
  · intro 𝕜 _ V _ _ _ Z _ _ _ W _ _ N T _ hN hNc F hF hnd e
    exact (B_sub hB 𝕜 hN hNc hF hnd e).2
  · intro V _ _ _ Z _ _ _ W _ _ N 𝕜 _ hN hNc F hF hnd
    exact (B_sub hB 𝕜 hN hNc hF hnd (Homeomorph.refl N)).2
  · intro 𝕜 _ V _ _ _ Z _ _ _ W _ _ N T _ hN hNc F hF hnd e i hi
    -- finiteness: the project's Morse function `L_p` argument, carried by `e` (outside the item)
    have hfin : FiniteDimensional 𝕜 (spaceHomology 𝕜 i T) := by
      let _ := hN.chartedSpace
      have := hN.isManifold
      have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
      obtain ⟨n, K, m, N', hN', G, Φ, -, hN'c, -⟩ :=
        Glue.exists_ambient_any_dim (E := Z) (M := N)
          ⟨contMDiff_comp_val hN hF, hnd⟩
      exact finiteDimensional_spaceHomology_of_isCompact hN' hN'c (e.trans Φ) i
    exact Module.finrank_zero_iff.1 (hvan hN hNc hF hnd e hi)

end BtoA

#rt_check RoundTrip.V3_35.A_to_B [Morse.Homology.bettiNumber_le_critCount,
  Morse.Homology.bettiNumber_le_critCount', Morse.Homology.sum_bettiNumber_eq_sum_critCount,
  Morse.Homology.sum_bettiNumber_eq_sum_critCount', Morse.Homology.bettiNumber_eq_zero_of_finrank_lt,
  Morse.Homology.subsingleton_spaceHomology_of_finrank_lt]
#rt_check RoundTrip.V3_35.B_to_A [Morse.Homology.bettiNumber_le_critCount,
  Morse.Homology.bettiNumber_le_critCount', Morse.Homology.sum_bettiNumber_eq_sum_critCount,
  Morse.Homology.sum_bettiNumber_eq_sum_critCount', Morse.Homology.bettiNumber_eq_zero_of_finrank_lt,
  Morse.Homology.subsingleton_spaceHomology_of_finrank_lt]
#rt_overlap RoundTrip.V3_35.B_to_A [Morse.Homology.bettiNumber_le_critCount,
  Morse.Homology.bettiNumber_le_critCount', Morse.Homology.sum_bettiNumber_eq_sum_critCount,
  Morse.Homology.sum_bettiNumber_eq_sum_critCount', Morse.Homology.bettiNumber_eq_zero_of_finrank_lt,
  Morse.Homology.subsingleton_spaceHomology_of_finrank_lt]

end RoundTrip.V3_35
