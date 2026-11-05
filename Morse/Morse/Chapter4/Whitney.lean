import Morse.Chapter4.WhitneySlice
import Morse.Chapter4.WhitneyInvariance
import Morse.Chapter4.Compact
import Morse.Chapter4.Approximation
import Morse.Chapter3.Reeb
import Mathlib.Geometry.Manifold.WhitneyEmbedding

/-!
Milnor, *Morse Theory*, §6, pp. 36–37 (the appeal to Whitney's embedding theorem in the proofs of
Corollaries 6.7 and 6.8), applied to the results of Part I proved for submanifolds of Euclidean
space: §3 Theorem 3.1, §4 Theorem 4.1 (Reeb), §5 p. 29 (`χ(M) = Σ (-1)^λ C_λ`), §6 Theorem 6.6
and Corollaries 6.7, 6.8, and Application 2 (p. 37).

# Part I for an abstract compact manifold

## Milnor's text, paraphrased

Milnor's manifolds are abstract smooth manifolds.  In §6 (p. 36) he quotes Whitney: "an
`n`-dimensional manifold can be embedded differentiably as a closed subset of `ℝ²ⁿ⁺¹`", and so
proves Corollary 6.7 (every manifold carries a function with only non-degenerate critical points
and compact sublevel sets) from Theorem 6.6, which is about manifolds in Euclidean space.  From
then on every theorem of Part I is available for every manifold, with χ(M) in §5 the Euler
characteristic of the manifold, independent of any embedding.

## What is proved here

In this project Theorem 3.1, Reeb's theorem, the Euler number and Theorem 6.6 are proved for
slice submanifolds `N ⊆ ℝᴷ` (`Milnor.IsSliceSubmanifold`).  This file transfers them to an
**abstract compact Hausdorff manifold** `M` without boundary, modelled on a finite-dimensional
real normed space `E` (`[ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
[CompactSpace M]`), through three ingredients:

1. Mathlib's Whitney embedding for compact manifolds (`exists_embedding_euclidean_of_compact`: a
   smooth closed embedding `M → ℝⁿ` with injective derivative), padded by two zero coordinates
   so that the ambient space is `ℝᴷ⁺¹` with `K ≥ 1` as the Poincaré–Hopf theorem of the
   companion project requires (`Morse.exists_embedding_euclidean`);
2. the image of such an embedding is a slice submanifold and the embedding is a diffeomorphism
   onto it (`Morse/Chapter4/WhitneySlice.lean`); together:
   `Morse.exists_diffeomorph_sliceSubmanifold`, **every compact manifold is diffeomorphic to a
   compact slice submanifold of some `ℝᴷ⁺¹`**, modelled on `ℝⁿ`, `n = dim M`;
   `Morse.exists_isSliceSubmanifold_whitney` records the statement for Mathlib's embedding
   itself, modelled on `E`;
3. critical points, non-degeneracy, indices, Morse functions and the numbers `C_λ` are invariant
   under diffeomorphisms (`Morse/Chapter4/WhitneyInvariance.lean`).

The consequences:

* (Theorem 6.6, Corollary 6.7) `Morse.exists_isMorseFunction_of_compactSpace`: **`M` carries a
  Morse function**, and it has finitely many critical points.
* (Corollary 6.8) `Morse.ae_isMorseFunction_add_inner_comp`: for any embedding `e : M → ℝⁿ` and
  smooth `f`, `f + ⟪a, e(·)⟫` is a Morse function for almost every `a`;
  `Morse.exists_isMorseFunction_approx_of_compactSpace`: **every smooth `f` is approximated by
  Morse functions**, uniformly on `M` and with its derivatives up to any order on compact sets
  of finitely many coordinate systems.
* (§5, p. 29) `Morse.eulerNumberM E M`, **the Euler number of `M`**:
  `Σ_{λ=0}^{dim M} (-1)^λ C_λ(f)` for a Morse function `f` chosen once and for all.
  `Morse.sum_critCount_eq_eulerNumberM`: the same sum for **every** Morse function on `M` is
  `χ(M)` (`Morse.exists_eulerNumber_of_compactSpace` is the existence form).
  `Morse.IsEulerNumber.eq_eulerNumberM`: the integer of the Poincaré–Hopf theorem of every compact
  submanifold of `ℝᴷ⁺¹` diffeomorphic to `M` (e.g. the image of any embedding) is `χ(M)`, so it
  **does not depend on the embedding**; `Morse.exists_isEulerNumber_eulerNumberM` (Application 2,
  p. 37, on an embedded copy): `M` is diffeomorphic to a compact `N ⊆ ℝᴷ⁺¹` on which every smooth
  tangent field with finitely many zeros has index sum `χ(M)`.
  `Morse.eulerNumberM_eq_of_diffeomorph`: `χ` is a diffeomorphism invariant.  In dimension `0`,
  `χ(M) = #M` (`Morse.sum_critCount_of_finrank_eq_zero`).
* (Theorem 4.1) `Morse.reeb_of_compactSpace`: **Reeb's theorem**: if a smooth `f : M → ℝ` has
  exactly two critical points, both non-degenerate, `M` is homeomorphic to `Sⁿ`, `n = dim M`.
* (Theorem 3.1) `Morse.theorem_3_1_of_compactSpace`: **Theorem 3.1 for compact `M`**: if a smooth
  `f : M → ℝ` has no critical point in `f⁻¹[a, b]`, a diffeomorphism of `M` carries `M^a` onto
  `M^b`, `M^a` is a strong deformation retract of `M^b`, and the inclusion is a homotopy
  equivalence.  The smooth function `f ∘ Φ⁻¹` on the image `N = Φ(M)` is the restriction of a
  smooth function on `ℝᴷ⁺¹` (`Morse.exists_contDiff_comp_val_eq`), so
  `Morse.theorem_3_1_submanifold_of_isCompact` applies; the diffeomorphism, the sublevel sets
  and the deformation retraction are carried back by `Φ`
  (`Morse.IsStrongDeformationRetract.preimage_homeomorph`).

## What Milnor leaves implicit, and what is not done

* **Hausdorff.**  Abstract manifolds need not be Hausdorff; Whitney's theorem (and Mathlib's
  version of it) needs it, as do the results transferred here.  Milnor's "manifold" must be read as
  Hausdorff (with a countable basis, automatic here by compactness).
* **Only compact manifolds.**  Mathlib (v4.33.1) proves Whitney's theorem only for compact
  manifolds, into some `ℝⁿ` (not `ℝ²ᵐ⁺¹`).  Corollary 6.7 for a non-compact manifold (a closed
  embedding into Euclidean space, and with it Theorem 3.1 when `f⁻¹[a, b]` is compact) is
  therefore not transferred; the submanifold versions
  (`Morse.exists_isMorseFunction_isCompact_sublevel`, `Morse.theorem_3_1_submanifold`) need a
  closed embedding as input.
* **The image of an embedding is a submanifold, and the embedding is a diffeomorphism onto it**:
  see `Morse/Chapter4/WhitneySlice.lean` (an injective immersion is not enough).
* **Invariance under diffeomorphisms** is never stated by Milnor: see
  `Morse/Chapter4/WhitneyInvariance.lean`.
* **The ambient dimension.**  Milnor's `ℝ²ⁿ⁺¹` plays no role; any `ℝᴷ⁺¹` with `K ≥ 1` will do.
  The two extra coordinates are a convenience: the companion project's Poincaré–Hopf theorem is
  stated for `K ≥ 1`, and a compact `1`-manifold in `ℝ¹` would otherwise have to be ruled out.
* **χ(M) is not identified with the homological Euler characteristic** `Σ (-1)^i dim Hᵢ(M)`
  (see `Morse/Chapter3/EulerChar.lean`): Mathlib lacks the relative homology needed for formula
  (3) of Theorem 5.2.  It is the integer of the Poincaré–Hopf theorem of any embedding, and the
  alternating count of the critical points of any Morse function.
* **Corollary 6.8**: Milnor perturbs by `L_p` composed with an embedding whose first coordinate
  is `f`; here, as in `Morse/Chapter4/Approximation.lean`, `f` is perturbed by a small linear
  function of a Whitney embedding.  Milnor's hypothesis that `f` be bounded is automatic for
  compact `M`.
* **Vector fields on `M` itself.**  Application 2 is stated on an embedded copy `N` of `M`: tangent
  fields and their indices are defined in the companion project for submanifolds of Euclidean
  space only.
* **Theorems 3.2 and 3.5** are not transferred here.
-/

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

namespace Morse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-! ### Embedding a compact manifold in Euclidean space -/

section Embedding

omit [FiniteDimensional ℝ E] in
/-- An injective linear map does not decrease dimension. -/
theorem finrank_le_of_injective_clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (A : E →L[ℝ] F) (hA : Injective A) : finrank ℝ E ≤ finrank ℝ F :=
  LinearMap.finrank_le_finrank_of_injective (f := (A : E →ₗ[ℝ] F)) hA

/-- **The image of Mathlib's Whitney embedding is a submanifold modelled on the model space of
`M`.**  A compact Hausdorff manifold `M` has a smooth closed embedding `e : M → ℝⁿ` with injective
derivative (`exists_embedding_euclidean_of_compact`), and `e(M)` is a slice submanifold of `ℝⁿ`
modelled on `E`, with normal model `ℝⁿ⁻ᵐ`, `m = dim E`. -/
theorem exists_isSliceSubmanifold_whitney [T2Space M] [CompactSpace M] :
    ∃ (n : ℕ) (e : M → 𝔼 n), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, 𝔼 n) ∞ e ∧ IsClosedEmbedding e ∧
      (∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, 𝔼 n) e x)) ∧
      Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) E (𝔼 (n - finrank ℝ E)) (range e) := by
  obtain ⟨n, e, he, hce, hinj⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓘(ℝ, E)) (M := M)
  refine ⟨n, e, he, hce, hinj, ?_⟩
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x⟩⟩
  · rintro _ ⟨y, -⟩
    exact isEmptyElim y
  have hle : finrank ℝ E ≤ n := by
    have := finrank_le_of_injective_clm (E := E) (F := 𝔼 n) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, 𝔼 n) e x)
      (hinj x)
    rwa [finrank_euclideanSpace_fin] at this
  exact isSliceSubmanifold_range he hce.isEmbedding hinj rfl
    (by rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]; omega)

/-- **Whitney's embedding with room**: a compact Hausdorff manifold has a smooth closed embedding
`e` into some `ℝᴷ⁺¹`, `K ≥ 1`, with injective derivative, such that `n + m = K + 1` for a given
`n` and some `m` (`n = dim M` is the case of interest).  This is Mathlib's embedding followed by
`v ↦ (v, 0) ∈ ℝᴺ × ℝⁿ⁺² = ℝᴺ⁺ⁿ⁺²`. -/
theorem exists_embedding_euclidean [T2Space M] [CompactSpace M] (n : ℕ) :
    ∃ (K m : ℕ) (e : M → 𝔼 (K + 1)), 0 < K ∧ n + m = K + 1 ∧
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, 𝔼 (K + 1)) ∞ e ∧ IsClosedEmbedding e ∧
      ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, 𝔼 (K + 1)) e x) := by
  obtain ⟨N₀, e₀, he₀, hce₀, hinj₀⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓘(ℝ, E)) (M := M)
  -- `ι v = (v, 0)`, read in `ℝ^{N₀ + (n + 2)} = ℝ^{N₀ + (n + 1) + 1}`
  let ι : 𝔼 N₀ →L[ℝ] 𝔼 (N₀ + (n + 1) + 1) :=
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N₀) (m := n + 2)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ (𝔼 N₀) (𝔼 (n + 2)))
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

/-- **Every compact manifold is a compact submanifold of Euclidean space**, up to diffeomorphism:
a compact Hausdorff manifold `M` of dimension `n` is diffeomorphic to a compact (and closed) slice
submanifold `N ⊆ ℝᴷ⁺¹`, `K ≥ 1`, modelled on `ℝⁿ`. -/
theorem exists_diffeomorph_sliceSubmanifold [T2Space M] [CompactSpace M] {n : ℕ}
    (hn : finrank ℝ E = n) :
    ∃ (K m : ℕ) (N : Set (𝔼 (K + 1)))
      (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 (K + 1)) (𝔼 n) (𝔼 m) N),
      0 < K ∧ IsCompact N ∧ IsClosed N ∧
      Nonempty (letI := hN.chartedSpace; Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, 𝔼 n) M N ∞) := by
  obtain ⟨K, m, e, hK, hnm, he, hce, hinj⟩ := exists_embedding_euclidean (E := E) (M := M) n
  have hZ : finrank ℝ (𝔼 n) = finrank ℝ E := by rw [finrank_euclideanSpace_fin, hn]
  have hW : finrank ℝ (𝔼 n) + finrank ℝ (𝔼 m) = finrank ℝ (𝔼 (K + 1)) := by
    simp only [finrank_euclideanSpace_fin, hnm]
  have hN := isSliceSubmanifold_range he hce.isEmbedding hinj hZ hW
  exact ⟨K, m, range e, hN, hK, isCompact_range he.continuous, hce.isClosed_range,
    ⟨diffeomorphRange hN he hce.isEmbedding hinj hZ hW⟩⟩

end Embedding

/-! ### Morse functions exist (Theorem 6.6, Corollary 6.7) -/

/-- **A compact manifold carries a Morse function** (Milnor, Theorem 6.6 and Corollary 6.7, for
compact `M`), with finitely many critical points (Corollary 2.3).  It is `L_p` on an embedded copy
of `M`, for almost every `p`, pulled back to `M`. -/
theorem exists_isMorseFunction_of_compactSpace [T2Space M] [CompactSpace M] :
    ∃ f : M → ℝ, IsMorseFunction E f ∧ {p : M | IsCriticalPointM E f p}.Finite := by
  obtain ⟨K, m, N, hN, -, hNc, -, ⟨Φ⟩⟩ :=
    exists_diffeomorph_sliceSubmanifold (E := E) (M := M) (n := finrank ℝ E) rfl
  let _ := hN.chartedSpace
  have := hN.isManifold
  obtain ⟨f₀, hf₀, -⟩ := exists_isMorseFunction_finite_critPoints hN hNc
  have hf : IsMorseFunction E (f₀ ∘ Φ.symm.symm) := hf₀.comp_diffeomorph_symm Φ.symm
  exact ⟨f₀ ∘ Φ.symm.symm, hf, hf.finite_setOf_isCriticalPointM⟩

/-! ### Approximation by Morse functions (Corollary 6.8) -/

/-- **Morse functions are generic** (Milnor, the proof of Corollary 6.8, for an abstract
manifold): if `e : M → ℝⁿ` is a smooth embedding with injective derivative and `f : M → ℝ` is
smooth, then `f + ⟪a, e(·)⟫` is a Morse function for almost every `a ∈ ℝⁿ`. -/
theorem ae_isMorseFunction_add_inner_comp {n : ℕ} {e : M → 𝔼 n}
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, 𝔼 n) ∞ e) (hemb : IsEmbedding e)
    (hinj : ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, 𝔼 n) e x))
    (μ : Measure (𝔼 n)) [μ.IsAddHaarMeasure] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    ∀ᵐ a ∂μ, IsMorseFunction E (fun x => f x + ⟪a, e x⟫) := by
  have hsmooth : ∀ a : 𝔼 n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => f x + ⟪a, e x⟫) :=
    fun a => hf.add ((innerBilin n a).contDiff.contMDiff.comp he)
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact Eventually.of_forall fun a => ⟨hsmooth a, fun p => isEmptyElim p⟩
  have hle : finrank ℝ E ≤ n := by
    have := finrank_le_of_injective_clm (E := E) (F := 𝔼 n) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, 𝔼 n) e x₀)
      (hinj x₀)
    rwa [finrank_euclideanSpace_fin] at this
  have hZ : finrank ℝ (𝔼 (finrank ℝ E)) = finrank ℝ E := finrank_euclideanSpace_fin
  have hW : finrank ℝ (𝔼 (finrank ℝ E)) + finrank ℝ (𝔼 (n - finrank ℝ E)) =
      finrank ℝ (𝔼 n) := by
    simp only [finrank_euclideanSpace_fin]
    omega
  have hN := isSliceSubmanifold_range he hemb hinj hZ hW
  let _ := hN.chartedSpace
  have := hN.isManifold
  let Φ := diffeomorphRange hN he hemb hinj hZ hW
  have hf' : ContMDiff 𝓘(ℝ, 𝔼 (finrank ℝ E)) 𝓘(ℝ, ℝ) ∞ (f ∘ Φ.symm) :=
    hf.comp Φ.symm.contMDiff
  filter_upwards [ae_isMorseFunction_add_inner hN μ hf'] with a ha
  have h := (isMorseFunction_comp_symm_iff Φ.symm).2 ha
  have hfun : (fun x => f x + ⟪a, e x⟫) =
      (fun x : range e => (f ∘ Φ.symm) x + ⟪a, (x : 𝔼 n)⟫) ∘ Φ.symm.symm := by
    funext x
    change f x + ⟪a, e x⟫ = f (Φ.symm (Φ x)) + ⟪a, ((Φ x : range e) : 𝔼 n)⟫
    rw [Φ.symm_apply_apply]
    rfl
  rw [hfun]
  exact h

/-- **Corollary 6.8** (Milnor, p. 37) **for an abstract compact manifold**: every smooth
`f : M → ℝ` on a compact Hausdorff manifold is uniformly approximated by Morse functions `g`, and
`g` can be chosen so that, in finitely many given smooth coordinate systems `y_j` and on given
compact subsets `K_j` of their domains, the derivatives of order `≤ r` of `g` are uniformly close to
those of `f`.  One can take `g = f + ⟪a, e(·)⟫`, `e` a Whitney embedding and `a` small. -/
theorem exists_isMorseFunction_approx_of_compactSpace [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {ι : Type*} [Finite ι]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (y : ι → OpenPartialHomeomorph M E')
    (hy : ∀ j, IsSmoothCoord E (y j)) (K : ι → Set E') (hK : ∀ j, IsCompact (K j))
    (hKy : ∀ j, K j ⊆ (y j).target) (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : M → ℝ, IsMorseFunction E g ∧ (∀ x, |g x - f x| < ε) ∧
      ∀ j, ∀ i ≤ r, ∀ u ∈ K j,
        ‖iteratedFDeriv ℝ i ((fun x => g x - f x) ∘ (y j).symm) u‖ < ε := by
  have := Fintype.ofFinite ι
  obtain ⟨n, e, he, hce, hinj⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓘(ℝ, E)) (M := M)
  -- bounds for `‖e x‖` and for the derivatives of `e ∘ y_j⁻¹` on `K_j`
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn he.continuous.continuousOn
  have hsm : ∀ j, ContDiffOn ℝ ∞ (e ∘ (y j).symm) (y j).target := fun j => by
    rw [← contMDiffOn_iff_contDiffOn]
    exact he.comp_contMDiffOn (hy j).contMDiffOn_symm
  have hC : ∀ j i, ∃ C, ∀ u ∈ K j, ‖iteratedFDeriv ℝ i (e ∘ (y j).symm) u‖ ≤ C := by
    intro j i
    have hcont : ContinuousOn (iteratedFDeriv ℝ i (e ∘ (y j).symm)) (y j).target :=
      ((hsm j).continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast le_top)
        (y j).open_target.uniqueDiffOn).congr fun u hu =>
        (iteratedFDerivWithin_of_isOpen i (y j).open_target hu).symm
    exact (hK j).exists_bound_of_continuousOn (hcont.mono (hKy j))
  choose C hC using hC
  obtain ⟨D, hD0, hRD, hCD⟩ : ∃ D : ℝ, 0 ≤ D ∧ (∀ x : M, ‖e x‖ ≤ D) ∧
      ∀ j, ∀ i ≤ r, C j i ≤ D := by
    refine ⟨|R| + ∑ j, ∑ i ∈ Finset.range (r + 1), |C j i|, by positivity, fun x => ?_,
      fun j i hi => ?_⟩
    · have h1 := hR x (mem_univ x)
      have h2 : 0 ≤ ∑ j, ∑ i ∈ Finset.range (r + 1), |C j i| := by positivity
      linarith [le_abs_self R]
    · have h1 : |C j i| ≤ ∑ i ∈ Finset.range (r + 1), |C j i| :=
        Finset.single_le_sum (f := fun i => |C j i|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
      have h2 : ∑ i ∈ Finset.range (r + 1), |C j i| ≤
          ∑ j, ∑ i ∈ Finset.range (r + 1), |C j i| :=
        Finset.single_le_sum (f := fun j => ∑ i ∈ Finset.range (r + 1), |C j i|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      linarith [le_abs_self (C j i), abs_nonneg R]
  -- a small `a` with `f + ⟪a, e(·)⟫` Morse
  obtain ⟨δ, hδ0, hδD⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * D < ε := by
    refine ⟨ε / (D + 1), div_pos hε (by linarith), ?_⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  obtain ⟨a, ha, hmorse⟩ : ∃ a ∈ Metric.ball (0 : 𝔼 n) δ,
      IsMorseFunction E (fun x => f x + ⟪a, e x⟫) := by
    have hpos : (volume : Measure (𝔼 n)) (Metric.ball 0 δ) ≠ 0 :=
      (Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.2 hδ0)).ne'
    exact Measure.exists_mem_of_measure_ne_zero_of_ae hpos
      (ae_restrict_of_ae (ae_isMorseFunction_add_inner_comp he hce.isEmbedding hinj volume hf))
  have ha' : ‖a‖ < δ := by
    rw [Metric.mem_ball, dist_zero_right] at ha
    exact ha
  have hdiff : ∀ x : M, (f x + ⟪a, e x⟫) - f x = innerBilin n a (e x) := fun x => by
    rw [innerBilin_apply]
    ring
  have hnorm : ‖innerBilin n a‖ ≤ ‖a‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun v => by
      rw [innerBilin_apply]
      exact norm_inner_le_norm a v
  refine ⟨fun x => f x + ⟪a, e x⟫, hmorse, fun x => ?_, fun j i hi u hu => ?_⟩
  · rw [hdiff, innerBilin_apply, ← Real.norm_eq_abs]
    calc ‖⟪a, e x⟫‖ ≤ ‖a‖ * ‖e x‖ := norm_inner_le_norm _ _
      _ ≤ δ * D := mul_le_mul ha'.le (hRD x) (norm_nonneg _) hδ0.le
      _ < ε := hδD
  · have hfun : (fun x : M => (f x + ⟪a, e x⟫) - f x) ∘ (y j).symm =
        innerBilin n a ∘ (e ∘ (y j).symm) := by
      funext u
      exact hdiff _
    have hsmu : ContDiffAt ℝ ∞ (e ∘ (y j).symm) u :=
      (hsm j).contDiffAt ((y j).open_target.mem_nhds (hKy j hu))
    rw [hfun, (innerBilin n a).iteratedFDeriv_comp_left hsmu (by exact_mod_cast le_top)]
    calc _ ≤ ‖innerBilin n a‖ * ‖iteratedFDeriv ℝ i (e ∘ (y j).symm) u‖ :=
          ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ ≤ δ * D := mul_le_mul (hnorm.trans ha'.le) ((hC j i u hu).trans (hCD j i hi))
          (norm_nonneg _) hδ0.le
      _ < ε := hδD

/-! ### The Euler number (§5, p. 29) -/

section Euler

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- In dimension `0` every point is a critical point (of every function). -/
theorem isCriticalPointM_of_finrank_eq_zero (h0 : finrank ℝ E = 0) (f : M → ℝ) (p : M) :
    IsCriticalPointM E f p := by
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p = 0
  ext v
  have hv : v = (0 : TangentSpace 𝓘(ℝ, E) p) := finrank_zero_iff_forall_zero.1 h0 v
  rw [hv, map_zero, map_zero]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- In dimension `0` every point is a critical point of index `0`, so
`Σ_λ (-1)^λ C_λ(f) = C₀(f) = #M` for every `f`. -/
theorem sum_critCount_of_finrank_eq_zero (h0 : finrank ℝ E = 0) (f : M → ℝ) :
    ∑ k ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ k * critCount E f k = Nat.card M := by
  rw [h0, zero_add, Finset.sum_range_one, pow_zero, one_mul, critCount]
  have : {p : M | IsCriticalPointM E f p ∧ indexM E f p = 0} = univ := by
    refine eq_univ_of_forall fun p => ⟨isCriticalPointM_of_finrank_eq_zero h0 f p, ?_⟩
    have := indexM_le_finrank (E := E) f p
    omega
  rw [this, Set.ncard_univ]

/-- **The Euler number of a manifold** (Milnor, p. 29: `χ(M) = C₀ - C₁ + ⋯ ± Cₙ`): the
alternating count `Σ_{λ=0}^{dim M} (-1)^λ C_λ(f)` of the critical points of a Morse function `f`
on `M`, for one Morse function chosen once and for all (`0` if there is none).  On a compact
Hausdorff manifold every Morse function gives the same value
(`Morse.sum_critCount_eq_eulerNumberM`). -/
def eulerNumberM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] : ℤ :=
  open Classical in
  if h : ∃ f : M → ℝ, IsMorseFunction E f then
    ∑ k ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ k * critCount E h.choose k
  else 0

/-- **The alternating count of critical points is the same for all Morse functions** on a compact
Hausdorff manifold (Milnor, p. 29: both sides of formula (3) are `χ(M)`).  In positive dimension
this is the Poincaré–Hopf theorem on an embedded copy of `M`
(`Morse.sum_critCount_eq_of_isMorseFunction`); in dimension `0` both sides are `#M`. -/
theorem sum_critCount_eq_of_isMorseFunction_of_compactSpace [T2Space M] [CompactSpace M]
    {f g : M → ℝ} (hf : IsMorseFunction E f) (hg : IsMorseFunction E g) :
    ∑ k ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ k * critCount E f k =
      ∑ k ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ k * critCount E g k := by
  obtain ⟨n, hn⟩ : ∃ n, finrank ℝ E = n := ⟨_, rfl⟩
  rcases n with _ | d
  · rw [sum_critCount_of_finrank_eq_zero hn f, sum_critCount_of_finrank_eq_zero hn g]
  rcases isEmpty_or_nonempty M with hM | hM
  · have h0 : ∀ (h : M → ℝ) (k : ℕ), critCount E h k = 0 := fun h k => by
      rw [critCount, Set.eq_empty_of_isEmpty {p : M | _}, Set.ncard_empty]
    simp only [h0]
  obtain ⟨K, m, N, hN, hK, hNc, -, ⟨Φ⟩⟩ :=
    exists_diffeomorph_sliceSubmanifold (E := E) (M := M) hn
  let _ := hN.chartedSpace
  have := hN.isManifold
  have hne : N.Nonempty := ⟨_, (Φ (Classical.arbitrary M)).2⟩
  have h := sum_critCount_eq_of_isMorseFunction hN hNc hne hK (hf.comp_diffeomorph_symm Φ)
    (hg.comp_diffeomorph_symm Φ)
  simp only [critCount_comp_symm Φ (hf.contMDiff.of_le (by norm_cast)),
    critCount_comp_symm Φ (hg.contMDiff.of_le (by norm_cast))] at h
  rw [hn]
  exact h

/-- **`Σ_λ (-1)^λ C_λ = χ(M)`** (Milnor, p. 29, formula (3) of Theorem 5.2, without homology) for
an abstract compact Hausdorff manifold: for every Morse function `f` on `M`, the alternating count
of its critical points is the Euler number `χ(M) = Morse.eulerNumberM E M`. -/
theorem sum_critCount_eq_eulerNumberM [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : IsMorseFunction E f) :
    ∑ k ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ k * critCount E f k = eulerNumberM E M := by
  have h : ∃ f : M → ℝ, IsMorseFunction E f := ⟨f, hf⟩
  rw [eulerNumberM, dif_pos h]
  exact sum_critCount_eq_of_isMorseFunction_of_compactSpace hf h.choose_spec

/-- **Existence form**: a compact Hausdorff manifold has an integer `χ` with
`Σ_{λ=0}^{dim M} (-1)^λ C_λ(f) = χ` for every Morse function `f`; it is unique, `M` carrying a
Morse function (`Morse.exists_isMorseFunction_of_compactSpace`). -/
theorem exists_eulerNumber_of_compactSpace [T2Space M] [CompactSpace M] :
    ∃ χ : ℤ, ∀ f : M → ℝ, IsMorseFunction E f →
      ∑ k ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ k * critCount E f k = χ :=
  ⟨eulerNumberM E M, fun _ hf => sum_critCount_eq_eulerNumberM hf⟩

/-- **`χ(M)` is the Poincaré–Hopf number of every embedded copy of `M`**: if `N ⊆ ℝᴷ⁺¹` is a
compact submanifold diffeomorphic to `M` (for instance the image of any embedding of `M`,
`Morse.diffeomorphRange`), then the integer of the Poincaré–Hopf theorem of `N`
(`Morse.IsEulerNumber`, the index sum of every tangent field on `N`) is `χ(M)`.  In particular it
does not depend on the embedding. -/
theorem IsEulerNumber.eq_eulerNumberM [T2Space M] [CompactSpace M] {K d m : ℕ}
    (hd : finrank ℝ E = d + 1) {N : Set (EuclideanSpace ℝ (Fin (K + 1)))}
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (EuclideanSpace ℝ (Fin (d + 1))) (EuclideanSpace ℝ (Fin m)) N)
    (hNc : IsCompact N) (hne : N.Nonempty) (hK : 0 < K)
    (Φ : letI := hN.chartedSpace;
      Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) M N ∞)
    {χN : ℤ} (hχ : IsEulerNumber hN hNc hne χN) : χN = eulerNumberM E M := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  obtain ⟨f, hf, -⟩ := exists_isMorseFunction_of_compactSpace (E := E) (M := M)
  rw [← sum_critCount_eq_eulerNumberM hf, ← hχ.sum_critCount_eq hN hNc hne hK
    (hf.comp_diffeomorph_symm Φ), hd]
  simp only [critCount_comp_symm Φ (hf.contMDiff.of_le (by norm_cast))]

/-- **The Euler number is a diffeomorphism invariant.** -/
theorem eulerNumberM_eq_of_diffeomorph [T2Space M] [CompactSpace M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M'] [IsManifold 𝓘(ℝ, E') ∞ M']
    [T2Space M'] [CompactSpace M'] (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E') M M' ∞) :
    eulerNumberM E M = eulerNumberM E' M' := by
  obtain ⟨f, hf, -⟩ := exists_isMorseFunction_of_compactSpace (E := E) (M := M)
  rw [← sum_critCount_eq_eulerNumberM hf,
    ← sum_critCount_eq_eulerNumberM (hf.comp_diffeomorph_symm g)]
  simp only [critCount_comp_symm g (hf.contMDiff.of_le (by norm_cast))]
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x⟩⟩
  · have h0 : ∀ k : ℕ, critCount E f k = 0 := fun k => by
      rw [critCount, Set.eq_empty_of_isEmpty {p : M | _}, Set.ncard_empty]
    simp only [h0, Nat.cast_zero, mul_zero, Finset.sum_const_zero]
  · have : finrank ℝ E = finrank ℝ E' :=
      (g.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.finrank_eq
    rw [this]

/-- **`χ(M)` is the index sum of every tangent field on an embedded copy of `M`**: a compact
Hausdorff manifold of dimension `d + 1` is diffeomorphic to a compact submanifold `N ⊆ ℝᴷ⁺¹` whose
Euler number in the sense of the Poincaré–Hopf theorem is `χ(M)`. -/
theorem exists_isEulerNumber_eulerNumberM [T2Space M] [CompactSpace M] [Nonempty M] {d : ℕ}
    (hd : finrank ℝ E = d + 1) :
    ∃ (K m : ℕ) (N : Set (EuclideanSpace ℝ (Fin (K + 1))))
      (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (EuclideanSpace ℝ (Fin (d + 1))) (EuclideanSpace ℝ (Fin m)) N)
      (hNc : IsCompact N) (hne : N.Nonempty),
      Nonempty (letI := hN.chartedSpace;
        Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) M N ∞) ∧
      IsEulerNumber hN hNc hne (eulerNumberM E M) := by
  obtain ⟨K, m, N, hN, hK, hNc, -, ⟨Φ⟩⟩ :=
    exists_diffeomorph_sliceSubmanifold (E := E) (M := M) hd
  have hne : N.Nonempty := ⟨_, (Φ (Classical.arbitrary M)).2⟩
  obtain ⟨χN, hχ⟩ := exists_isEulerNumber hN hNc hne hK
  refine ⟨K, m, N, hN, hNc, hne, ⟨Φ⟩, ?_⟩
  rwa [← hχ.eq_eulerNumberM hd hN hNc hne hK Φ]

end Euler

/-! ### Reeb's theorem (Theorem 4.1) -/

/-- **Theorem 4.1 (Reeb)** (Milnor, p. 25) **for an abstract compact manifold**: if a smooth
function `f` on a compact Hausdorff manifold `M` of dimension `n` has exactly two critical points,
both non-degenerate, then `M` is homeomorphic to the sphere `Sⁿ ⊆ ℝⁿ⁺¹`. -/
theorem reeb_of_compactSpace [T2Space M] [CompactSpace M] {n : ℕ} (hn : finrank ℝ E = n)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (htwo : {p : M | IsCriticalPointM E f p}.ncard = 2)
    (hnd : ∀ p, IsCriticalPointM E f p → IsNondegenerate (hessianM E f p)) :
    Nonempty (M ≃ₜ Metric.sphere (0 : 𝔼 (n + 1)) 1) := by
  obtain ⟨K, m, N, hN, -, hNc, -, ⟨Φ⟩⟩ := exists_diffeomorph_sliceSubmanifold (E := E) (M := M) hn
  let _ := hN.chartedSpace
  have := hN.isManifold
  -- the function `f ∘ Φ⁻¹` on the embedded copy `N`
  set f' : N → ℝ := f ∘ Φ.symm with hf'
  have hf's : ContMDiff 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, ℝ) ∞ f' := hf.comp Φ.symm.contMDiff
  have htwo' : {q : N | IsCriticalPointM (𝔼 n) f' q}.ncard = 2 := by
    rw [hf', ncard_setOf_isCriticalPointM_comp_symm Φ f, htwo]
  have hnd' : ∀ q : N, IsCriticalPointM (𝔼 n) f' q → IsNondegenerate (hessianM (𝔼 n) f' q) := by
    intro q hq
    have hcrit := (isCriticalPointM_comp_symm_iff Φ).1 hq
    exact (isNondegenerate_hessianM_comp_symm_iff Φ (hf.contMDiffAt.of_le (by norm_cast))
      hcrit).2 (hnd _ hcrit)
  obtain ⟨h⟩ : Nonempty (N ≃ₜ Metric.sphere (0 : 𝔼 (n + 1)) 1) := by
    rcases n with _ | d
    · exact reeb_of_finrank_eq_zero hN finrank_euclideanSpace_fin htwo'
    · exact reeb_of_contMDiff hN hNc hf's htwo' hnd'
  exact ⟨Φ.toHomeomorph.trans h⟩

/-! ### Theorem 3.1 -/

/-- **Strong deformation retracts are carried by homeomorphisms**: if `B` is a strong deformation
retract of `Y` and `h : X ≃ Y`, then `h⁻¹(B)` is one of `X` (retraction `h⁻¹ ∘ r ∘ h`, homotopy
`h⁻¹ ∘ H ∘ (id × h)`). -/
theorem IsStrongDeformationRetract.preimage_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₜ Y) {B : Set Y} (hB : IsStrongDeformationRetract B) :
    IsStrongDeformationRetract (h ⁻¹' B) := by
  obtain ⟨r, hr, ⟨H⟩⟩ := hB
  let r' : C(X, X) := (h.symm : C(Y, X)).comp (r.comp (h : C(X, Y)))
  refine ⟨r', fun x => ?_, ⟨?_⟩⟩
  · change h (h.symm (r (h x))) ∈ B
    rw [h.apply_symm_apply]
    exact hr _
  · exact
      { toFun := fun p => h.symm (H (p.1, h p.2))
        continuous_toFun := h.symm.continuous.comp (H.continuous.comp
          (continuous_fst.prodMk (h.continuous.comp continuous_snd)))
        map_zero_left := fun x => by simp
        map_one_left := fun x => by simp [r']
        prop' := fun t x hx => by
          have := H.eq_fst t hx
          simp [this] }

/-- **Theorem 3.1** (Milnor, pp. 12–13) **for an abstract compact manifold.**  Let `f` be a
smooth function on a compact Hausdorff manifold `M`, `a ≤ b`, and suppose that `f⁻¹[a, b]`
contains no critical point of `f`.  Then

1. there is a diffeomorphism `Ψ` of `M` with `Ψ(M^a) = M^b`;
2. `M^a` is a strong deformation retract of `M^b`;
3. the inclusion `M^a → M^b` is a homotopy equivalence. -/
theorem theorem_3_1_of_compactSpace [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hcrit : ∀ p, f p ∈ Icc a b → ¬IsCriticalPointM E f p) :
    (∃ Ψ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, Ψ '' sublevel f a = sublevel f b) ∧
      IsStrongDeformationRetract (Subtype.val ⁻¹' sublevel f a : Set (sublevel f b)) ∧
      ∃ h : ContinuousMap.HomotopyEquiv (sublevel f a) (sublevel f b),
        ⇑h = Set.inclusion (sublevel_mono f hab) := by
  suffices H : (∃ Ψ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, Ψ '' sublevel f a = sublevel f b) ∧
      IsStrongDeformationRetract (Subtype.val ⁻¹' sublevel f a : Set (sublevel f b)) from
    ⟨H.1, H.2, H.2.exists_homotopyEquiv (sublevel_mono f hab)⟩
  obtain ⟨n, hn⟩ : ∃ n, finrank ℝ E = n := ⟨_, rfl⟩
  -- the trivial case: no value of `f` lies in `[a, b]`, and `M^a = M^b`
  by_cases hempty : ∀ p, f p ∉ Icc a b
  · have heq : sublevel f a = sublevel f b := by
      ext p
      simp only [mem_sublevel]
      constructor
      · intro h
        linarith
      · intro h
        by_contra h'
        exact hempty p ⟨(not_le.1 h').le, h⟩
    refine ⟨⟨Diffeomorph.refl _ _ _, by rw [heq]; simp⟩, ?_⟩
    have : (Subtype.val ⁻¹' sublevel f a : Set (sublevel f b)) = univ := by
      ext p
      simp only [mem_preimage, mem_univ, iff_true, heq]
      exact p.2
    rw [this]
    exact ⟨ContinuousMap.id _, fun _ => mem_univ _, ⟨ContinuousMap.HomotopyRel.refl _ _⟩⟩
  push Not at hempty
  obtain ⟨p₀, hp₀⟩ := hempty
  -- otherwise `dim M > 0`: in dimension `0` every point is critical
  rcases n with _ | d
  · exact absurd (isCriticalPointM_of_finrank_eq_zero hn f p₀) (hcrit p₀ hp₀)
  obtain ⟨K, m, N, hN, hK, hNc, -, ⟨Φ⟩⟩ :=
    exists_diffeomorph_sliceSubmanifold (E := E) (M := M) hn
  let _ := hN.chartedSpace
  have := hN.isManifold
  have hne : N.Nonempty := ⟨_, (Φ p₀).2⟩
  -- `f ∘ Φ⁻¹` is the restriction of a smooth `F` on `ℝᴷ⁺¹`
  obtain ⟨F, hF, hFeq⟩ := exists_contDiff_comp_val_eq hN hNc hne (hf.comp Φ.symm.contMDiff)
  have hFΦ : ∀ x, F (Φ x) = f x := by
    intro x
    have := congrFun hFeq (Φ x)
    simpa using this
  have hcrit' : ∀ q : N, F q ∈ Icc a b →
      ¬IsCriticalPointM (𝔼 (d + 1)) (F ∘ Subtype.val) q := by
    intro q hq hc
    rw [hFeq] at hc
    have hc' := (isCriticalPointM_comp_symm_iff Φ).1 hc
    refine hcrit _ ?_ hc'
    have := hFΦ (Φ.symm q)
    rw [Φ.apply_symm_apply] at this
    rwa [← this]
  -- Theorem 3.1 on the submanifold `N`
  obtain ⟨⟨ΦN, hΦN⟩, hSDR, -⟩ := theorem_3_1_submanifold_of_isCompact hN hNc hF hab hcrit'
  -- transport back to `M`
  set f' : N → ℝ := F ∘ Subtype.val with hf'
  have hsub : ∀ c x, x ∈ sublevel f c ↔ Φ x ∈ sublevel f' c := by
    intro c x
    simp only [mem_sublevel, hf', comp_apply, hFΦ]
  refine ⟨⟨Φ.trans (ΦN.trans Φ.symm), ?_⟩, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : ΦN (Φ x) ∈ sublevel f' b := by
        rw [← hΦN]
        exact ⟨Φ x, (hsub a x).1 hx, rfl⟩
      rw [hsub b]
      simpa using h1
    · intro hy
      have h1 : Φ y ∈ ΦN '' sublevel f' a := by
        rw [hΦN]
        exact (hsub b y).1 hy
      obtain ⟨z, hz, hzy⟩ := h1
      refine ⟨Φ.symm z, (hsub a _).2 (by simpa using hz), ?_⟩
      simp [hzy]
  · let hom : sublevel f b ≃ₜ sublevel f' b := Φ.toHomeomorph.subtype (fun x => hsub b x)
    have hpre : (Subtype.val ⁻¹' sublevel f a : Set (sublevel f b)) =
        hom ⁻¹' (Subtype.val ⁻¹' sublevel f' a : Set (sublevel f' b)) := by
      ext x
      simp only [mem_preimage, hom]
      exact hsub a x
    rw [hpre]
    exact hSDR.preimage_homeomorph hom

end Morse
