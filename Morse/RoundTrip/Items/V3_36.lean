import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V3_36

open CategoryTheory Morse Morse.Homology Module Finset
open scoped ContDiff Manifold

namespace RoundTrip.V3_36

/-- The project's statement: the two listed theorems, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.Homology.altSum_bettiNumber_le.{0, 0, 0, 0} ∧
  type_of% @Morse.Homology.altSum_bettiNumber_le'.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.Homology.altSum_bettiNumber_le.{0, 0, 0, 0},
    @Morse.Homology.altSum_bettiNumber_le'.{0, 0, 0}⟩

lemma Rabs_eq (F : Type) [Field F] (X : Type) [TopologicalSpace X] (i : ℕ) :
    Rabs F X i = bettiNumber F X i :=
  finrank_subsetHomology_eq_bettiNumber (𝕜 := F) (Set.empty_subset _) rfl rfl i

lemma alt_eq (d : ℕ → ℤ) (l : ℕ) : alt d l = altSum d l := rfl

/-- A ⇒ B: Whitney copy (`Glue.exists_ambient_any_dim`) and A's first clause with `e = Φ`. -/
theorem A_to_B : A → B := by
  intro hA F _ E _ _ _ M _ _ _ _ _ f hf hnd l
  have hg : IsMorseFunction E f := ⟨hf, fun p hp ↦ (hnd p hp).2⟩
  obtain ⟨n, K, m, N, hN, G, Φ, -, hNc, hG, hGnd, hcount⟩ := Glue.exists_ambient_any_dim hg
  let _ := hN.chartedSpace
  have hCn : ∀ i, Cnum E f i = critCount E f i := fun _ ↦ rfl
  simp only [alt_eq, Rabs_eq, hCn, hcount]
  exact hA.1 (𝕜 := F) hN hNc hG hGnd Φ l

/-- B ⇒ A: a compact slice submanifold with `F|N` is a compact manifold with a Morse function;
transport the Betti numbers along `e : T ≃ₜ N`. -/
theorem B_to_A : B → A := by
  intro hB
  have key : type_of% @Morse.Homology.altSum_bettiNumber_le.{0, 0, 0, 0} := by
    intro 𝕜 _ V _ _ _ Z _ _ _ W _ _ N T _ hN hNc F hF hnd e l
    let _ := hN.chartedSpace
    have := hN.isManifold
    have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
    have h := hB 𝕜 Z N (F ∘ Subtype.val) (contMDiff_comp_val hN hF)
      (fun p hp ↦ ⟨hp, hnd p hp⟩) l
    have hb : ∀ i, bettiNumber 𝕜 T i = Rabs 𝕜 N i := fun i ↦
      (bettiNumber_eq_of_homeomorph e i).trans (Rabs_eq 𝕜 N i).symm
    simp only [hb]
    exact h
  refine ⟨key, ?_⟩
  intro V _ _ _ Z _ _ _ W _ _ N 𝕜 _ hN hNc F hF hnd l
  exact key hN hNc hF hnd (Homeomorph.refl N) l

#rt_check RoundTrip.V3_36.A_to_B [Morse.Homology.altSum_bettiNumber_le,
  Morse.Homology.altSum_bettiNumber_le']
#rt_check RoundTrip.V3_36.B_to_A [Morse.Homology.altSum_bettiNumber_le,
  Morse.Homology.altSum_bettiNumber_le']
#rt_overlap RoundTrip.V3_36.B_to_A [Morse.Homology.altSum_bettiNumber_le,
  Morse.Homology.altSum_bettiNumber_le']

end RoundTrip.V3_36
