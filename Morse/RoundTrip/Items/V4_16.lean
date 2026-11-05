import Morse
import RoundTrip.Check
import RoundTrip.Blind.V4_16

open Module Set Function Topology
open scoped ContDiff Manifold

namespace RoundTrip.V4_16

/-- The project's statement: the three listed theorems, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.exists_isSliceSubmanifold_whitney.{0, 0} ∧
  type_of% @Morse.exists_embedding_euclidean.{0, 0} ∧
  type_of% @Morse.exists_diffeomorph_sliceSubmanifold.{0, 0}

theorem A_holds : A :=
  ⟨@Morse.exists_isSliceSubmanifold_whitney.{0, 0}, @Morse.exists_embedding_euclidean.{0, 0},
    @Morse.exists_diffeomorph_sliceSubmanifold.{0, 0}⟩

/-- A's second clause, re-proved from Mathlib's `exists_embedding_euclidean_of_compact` (Whitney
for compact manifolds, into some `ℝᴺ`) followed by a linear inclusion. -/
theorem embed : type_of% @Morse.exists_embedding_euclidean.{0, 0} := by
  intro E _ _ _ M _ _ _ _ _ n
  obtain ⟨N₀, e₀, he₀, hce₀, hinj₀⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓘(ℝ, E)) (M := M)
  let ι : Rn N₀ →L[ℝ] Rn (N₀ + (n + 1) + 1) :=
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N₀) (m := n + 2)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ (Rn N₀) (Rn (n + 2)))
  have hι : Injective ι := by
    intro a b hab
    have := congrArg (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N₀) (m := n + 2)) hab
    simpa [ι] using this
  refine ⟨N₀ + (n + 1), N₀ + 2, ι ∘ e₀, by omega, by omega, ?_, ?_, ?_⟩
  · exact ι.contDiff.contMDiff.comp he₀
  · exact (ι.continuous.comp he₀.continuous).isClosedEmbedding (hι.comp hce₀.injective)
  · intro x
    rw [mfderiv_comp x ι.mdifferentiableAt (he₀.mdifferentiableAt (by simp)), ι.mfderiv_eq]
    exact hι.comp (hinj₀ x)

/-! `A_to_B` is not proved, and fails genuinely: A is Whitney's theorem for COMPACT manifolds
only, into some unspecified `ℝᴺ` (Mathlib's weak Whitney theorem); B is Whitney's theorem as Milnor
quotes it, for every (second countable, possibly non-compact) `n`-manifold, into exactly
`ℝ^{2n+1}`, as a closed smooth embedding. Neither the non-compact case nor the dimension `2n+1`
(a general-position argument) is in the project or Mathlib. -/

/-- **B ⇒ A**, by re-proving A outright (B is not used): A is Mathlib's compact Whitney theorem
plus the project's `isSliceSubmanifold_range` and `diffeomorphRange` (an embedding with injective
differential has a slice-submanifold image, diffeomorphic to the source), none of which is listed.
B cannot be used: it needs a second countable manifold modelled on `ℝⁿ`, while A's `M` has an
arbitrary model `E` and (although compact) changing the model is not in the project. -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, embed, ?_⟩
  · intro E _ _ _ M _ _ _ _ _
    obtain ⟨n, e, he, hce, hinj⟩ :=
      exists_embedding_euclidean_of_compact (I := 𝓘(ℝ, E)) (M := M)
    refine ⟨n, e, he, hce, hinj, ?_⟩
    rcases isEmpty_or_nonempty M with hM | ⟨⟨x⟩⟩
    · rintro _ ⟨y, -⟩
      exact isEmptyElim y
    have hle : finrank ℝ E ≤ n := by
      have := Morse.finrank_le_of_injective_clm (E := E) (F := Rn n)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) e x) (hinj x)
      rwa [finrank_euclideanSpace_fin] at this
    exact Morse.isSliceSubmanifold_range he hce.isEmbedding hinj rfl
      (by rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]; omega)
  · intro E _ _ _ M _ _ _ _ _ n hn
    obtain ⟨K, m, e, hK, hnm, he, hce, hinj⟩ := embed (E := E) (M := M) n
    have hZ : finrank ℝ (Rn n) = finrank ℝ E := by rw [finrank_euclideanSpace_fin, hn]
    have hW : finrank ℝ (Rn n) + finrank ℝ (Rn m) = finrank ℝ (Rn (K + 1)) := by
      simp only [finrank_euclideanSpace_fin, hnm]
    have hN := Morse.isSliceSubmanifold_range he hce.isEmbedding hinj hZ hW
    exact ⟨K, m, range e, hN, hK, isCompact_range he.continuous, hce.isClosed_range,
      ⟨Morse.diffeomorphRange hN he hce.isEmbedding hinj hZ hW⟩⟩

#rt_check RoundTrip.V4_16.B_to_A [Morse.exists_isSliceSubmanifold_whitney,
  Morse.exists_embedding_euclidean, Morse.exists_diffeomorph_sliceSubmanifold]
#rt_overlap RoundTrip.V4_16.B_to_A [Morse.exists_isSliceSubmanifold_whitney,
  Morse.exists_embedding_euclidean, Morse.exists_diffeomorph_sliceSubmanifold]

end RoundTrip.V4_16
