import Morse.Homology.MorseHomology
import Morse.Chapter4.Compact
import Morse.Chapter3.Torus
import Morse.Chapter3.EulerCharSphere

/-!
Milnor, *Morse Theory*, §5, pp. 28–31 (Theorem 5.2, `(4_λ)`, Corollary 5.4) for compact
manifolds, and the identification of `χ(M)` (p. 29 and §6, Application 2, pp. 36–37).

# The Morse inequalities and the Euler characteristic of a compact manifold

## Milnor's text, paraphrased

On p. 28 Milnor writes `χ(X, Y) = Σ (-1)^λ R_λ(X, Y)` for the Euler characteristic, `R_λ` the
Betti numbers over a field `F`, and on p. 29 formula (3) of Theorem 5.2 reads
`χ(M) = Σ_λ (-1)^λ C_λ` for every function with non-degenerate critical points on a compact
manifold `M`.  In §6, Application 2 (pp. 36–37), the same `χ(M)` is the index sum of a gradient
field, hence (by the topological invariance of the index sum, quoted from Steenrod) of every
vector field.  Milnor's manifolds are abstract; §6 (p. 36) quotes Whitney's embedding theorem
to place them in Euclidean space.

## What is proved here

Everything is over an arbitrary field `𝕜`, `b_i(X) = dim H_i(X; 𝕜)` (singular homology,
`Morse.Homology.bettiNumber`), on top of `Morse/Homology/MorseHomology.lean`.

* **Compact submanifolds of `ℝⁿ`** (and spaces homeomorphic to one):
  `Morse.Homology.finiteDimensional_spaceHomology_of_isCompact` (`H_i(N; 𝕜)` is
  finite-dimensional) and `Morse.Homology.bettiNumber_eq_zero_of_isCompact` (`b_i(N) = 0` above
  the dimension), from the Morse function `L_p = ‖· - p‖²` of Theorem 6.6.
* **`χ` identified**: `Morse.IsEulerNumber.eq_sum_bettiNumber`: the integer of the
  Poincaré–Hopf theorem of a compact submanifold `N ⊆ ℝᴷ⁺¹` (`Morse.IsEulerNumber`, the index
  sum of every tangent field) is `Σ_i (-1)^i dim H_i(N; 𝕜)`, for every field `𝕜`.
  `Morse.Homology.eulerNumberM_eq_sum_bettiNumber`: the Euler number `Morse.eulerNumberM E M` of
  a compact abstract manifold (the alternating count `Σ (-1)^λ C_λ` of any Morse function) is
  `Σ_i (-1)^i dim H_i(M; 𝕜)`.
* **Abstract compact manifolds** `M` (Hausdorff, without boundary, modelled on a
  finite-dimensional `E`), through a Whitney embedding `M ≅ N ⊆ ℝᴷ⁺¹`
  (`Morse.exists_diffeomorph_sliceSubmanifold`) and the homeomorphism invariance of singular
  homology: `H_i(M; 𝕜)` is finite-dimensional and vanishes above `dim M`
  (`Morse.Homology.finiteDimensional_spaceHomology_of_compactSpace`,
  `Morse.Homology.bettiNumber_eq_zero_of_compactSpace`); for every Morse function `g` on `M`,
  `b_λ(M) ≤ C_λ(g)`, `(4_λ)`, `Σ (-1)^i b_i(M) = Σ (-1)^λ C_λ(g)` and the lacunary principle
  (`Morse.Homology.bettiNumber_le_critCount_of_compactSpace`,
  `Morse.Homology.altSum_bettiNumber_le_of_compactSpace`,
  `Morse.Homology.sum_bettiNumber_eq_sum_critCount_of_compactSpace`,
  `Morse.Homology.bettiNumber_eq_critCount_of_lacunary_of_compactSpace`); and, in Reeb's
  situation of a function with exactly two critical points, both non-degenerate,
  `b_0 = b_n = 1` and `b_i = 0` otherwise, `n = dim M ≥ 2`
  (`Morse.Homology.bettiNumber_of_ncard_eq_two`).
* **Examples.**  The torus of `Morse/Chapter3/Torus.lean` (`C = (1, 2, 1)`):
  `b_0 ≤ 1`, `b_1 ≤ 2`, `b_2 ≤ 1`, `b_i = 0` for `i ≥ 3`, and `b_0 - b_1 + b_2 = 0`
  (`Morse.Homology.torus_bettiNumber`).  The spheres, with the height function of
  `Morse/Chapter3/EulerCharSphere.lean` (`C_0 = C_n = 1`, as in Reeb's theorem):
  `Σ_i (-1)^i b_i(Sⁿ) = 1 + (-1)ⁿ` (`Morse.Homology.sphere_sum_bettiNumber`); for `n ≥ 2` the
  lacunary principle gives the whole homology, `b_0 = b_n = 1` and `b_i = 0` otherwise
  (`Morse.Homology.sphere_bettiNumber`); for the circle `b_0 = b_1 ≤ 1`
  (`Morse.Homology.circle_bettiNumber`).

## What Milnor leaves implicit

* **`χ(M)` does not depend on the field.**  Milnor's `χ(M)` on p. 29 is computed over a field
  `F` and then used without reference to `F` in §6.  That `Σ (-1)^i dim H_i(M; F)` is the same
  integer for all fields is a consequence of formula (3) itself (both sides of
  `Morse.Homology.eulerNumberM_eq_sum_bettiNumber` are compared for each `𝕜`, and the left side
  does not involve `𝕜`).  For the individual `b_i` no such statement holds or is claimed.
* **Homeomorphism invariance.**  Passing from an abstract `M` to its embedded copy uses that
  singular homology is invariant under homeomorphisms (functoriality); Milnor's appeal to
  Whitney (p. 36) is silent about it.
* **Morse functions on abstract manifolds as ambient functions.**  The results of Chapter 2 are
  for restrictions `F|N` of smooth functions on the ambient space.  A Morse function `g` on `M`
  becomes one on the embedded copy through a smooth extension of `g ∘ Φ⁻¹`
  (`Morse.exists_contDiff_comp_val_eq`, dimension `≥ 1`); in dimension `0` the inequalities are
  equalities (`b_0 = #M = C_0`), obtained from formula (3) for `L_p` instead.
* **Universes.**  Singular homology with coefficients in `𝕜` is taken for spaces in the universe
  of `𝕜`.  The results for an abstract `M` hold for `M` and `𝕜` in the same, arbitrary, universe;
  this is why `Morse/Homology/MorseHomology.lean` works with spaces homeomorphic to `N`.
* **Application 2** identifies `χ(M)` with an index sum only for *some* vector field (a gradient)
  and appeals to Steenrod for all others; here the Poincaré–Hopf theorem of the companion project
  provides the invariance, and `Morse.IsEulerNumber.eq_sum_bettiNumber` closes the circle with the
  homological Euler characteristic.
-/

open Set Finset Module MeasureTheory
open scoped ContDiff Manifold

universe u

noncomputable section

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

namespace Morse.Homology

variable {𝕜 : Type u} [Field 𝕜]

/-! ### Compact submanifolds of `ℝⁿ` -/

section Euclidean

variable {n k w : ℕ} {N : Set (𝔼 n)} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) N)
  (hNc : IsCompact N) {T : Type u} [TopologicalSpace T]

/-- `L_p = ‖· - p‖²` is smooth on `ℝⁿ`. -/
theorem contDiff_normSq_sub (p : 𝔼 n) : ContDiff ℝ ∞ fun x : 𝔼 n ↦ ‖x - p‖ ^ 2 :=
  (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)

include hN hNc in
/-- **The homology of a compact submanifold of `ℝⁿ` is finite-dimensional** (and so is that of
any space `T` homeomorphic to it): Morse theory for the Morse function `L_p` of Theorem 6.6. -/
theorem finiteDimensional_spaceHomology_of_isCompact (e : T ≃ₜ N) (i : ℕ) :
    FiniteDimensional 𝕜 (spaceHomology 𝕜 i T) := by
  let _ := hN.chartedSpace
  obtain ⟨p, hp⟩ := Morse.exists_isMorseFunction_normSq_sub (hM := hN)
  exact finiteDimensional_spaceHomology hN hNc (contDiff_normSq_sub p) hp.isNondegenerate e i

include hN hNc in
/-- **The homology of a compact `k`-dimensional submanifold of `ℝⁿ` vanishes above `k`** (and
so does that of any space homeomorphic to it). -/
theorem bettiNumber_eq_zero_of_isCompact (e : T ≃ₜ N) {i : ℕ} (hi : k < i) :
    bettiNumber 𝕜 T i = 0 := by
  let _ := hN.chartedSpace
  obtain ⟨p, hp⟩ := Morse.exists_isMorseFunction_normSq_sub (hM := hN)
  exact bettiNumber_eq_zero_of_finrank_lt hN hNc (contDiff_normSq_sub p) hp.isNondegenerate
    e (by rwa [finrank_euclideanSpace_fin])

end Euclidean

/-! ### The Euler number of Poincaré–Hopf is the Euler characteristic -/

section PoincareHopf

variable {K d m : ℕ} {N : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
    (EuclideanSpace ℝ (Fin (d + 1))) (𝔼 m) N)
  (hNc : IsCompact N) (hne : N.Nonempty) {T : Type u} [TopologicalSpace T]

/-- **The Euler number of Poincaré–Hopf is the homological Euler characteristic** (Milnor p. 29,
formula (3), with §6, Application 2).  If `N ⊆ ℝᴷ⁺¹` is a compact submanifold of dimension
`d + 1` and `χN` its Euler number in the sense of `Morse.IsEulerNumber` (the index sum of every
smooth tangent field with finitely many zeros), then `χN = Σ_{i ≤ d+1} (-1)^i dim H_i(N; 𝕜)` for
every field `𝕜` (homology read in any space `T` homeomorphic to `N`). -/
theorem _root_.Morse.IsEulerNumber.eq_sum_bettiNumber (e : T ≃ₜ N) (hK : 0 < K) {χN : ℤ}
    (hχ : IsEulerNumber hN hNc hne χN) :
    χN = ∑ i ∈ range (d + 2), (-1 : ℤ) ^ i * (bettiNumber 𝕜 T i : ℤ) := by
  let _ := hN.chartedSpace
  obtain ⟨p, hp⟩ := Morse.exists_isMorseFunction_normSq_sub (hM := hN)
  rw [← hχ.sum_critCount_eq hN hNc hne hK hp]
  have h := sum_bettiNumber_eq_sum_critCount (𝕜 := 𝕜) hN hNc (contDiff_normSq_sub p)
    hp.isNondegenerate e
  rw [finrank_euclideanSpace_fin] at h
  exact h.symm

end PoincareHopf

/-! ### Abstract compact manifolds -/

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  [CompactSpace M]

variable (E M) in
/-- A compact manifold `M` is homeomorphic, through a Whitney embedding `Φ`, to a compact
submanifold `N ⊆ ℝᴷ⁺¹` modelled on `ℝ^{dim M}` on which some `L_p = ‖· - p‖²` is a Morse
function; `L_p ∘ Φ` is then a Morse function on `M` with the same numbers `C_λ`. -/
theorem exists_whitney_normSq :
    ∃ (K m : ℕ) (N : Set (𝔼 (K + 1)))
      (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 (K + 1)) (𝔼 (finrank ℝ E)) (𝔼 m) N) (p : 𝔼 (K + 1))
      (Φ : M ≃ₜ N), IsCompact N ∧
      (letI := hN.chartedSpace; IsMorseFunction (𝔼 (finrank ℝ E))
        ((fun x : 𝔼 (K + 1) ↦ ‖x - p‖ ^ 2) ∘ (Subtype.val : N → 𝔼 (K + 1)))) ∧
      ∃ f : M → ℝ, f = (fun x : 𝔼 (K + 1) ↦ ‖x - p‖ ^ 2) ∘ Subtype.val ∘ Φ ∧
        IsMorseFunction E f ∧ ∀ k, critCount E f k =
        (letI := hN.chartedSpace; critCount (𝔼 (finrank ℝ E))
          ((fun x : 𝔼 (K + 1) ↦ ‖x - p‖ ^ 2) ∘ (Subtype.val : N → 𝔼 (K + 1))) k) := by
  obtain ⟨K, m, N, hN, -, hNc, -, ⟨Φ⟩⟩ :=
    exists_diffeomorph_sliceSubmanifold (E := E) (M := M) (n := finrank ℝ E) rfl
  let _ := hN.chartedSpace
  have := hN.isManifold
  obtain ⟨p, hp⟩ := Morse.exists_isMorseFunction_normSq_sub (hM := hN)
  refine ⟨K, m, N, hN, p, Φ.toHomeomorph, hNc, hp, _, rfl, hp.comp_diffeomorph_symm Φ.symm,
    fun k ↦ critCount_comp_symm Φ.symm (hp.contMDiff.of_le (by norm_cast)) k⟩

variable (E) in
include E in
/-- **The homology of a compact manifold is finite-dimensional** (Milnor pp. 28–29, where the
Betti numbers `R_λ(M)` are used as numbers). -/
theorem finiteDimensional_spaceHomology_of_compactSpace (i : ℕ) :
    FiniteDimensional 𝕜 (spaceHomology 𝕜 i M) := by
  obtain ⟨K, m, N, hN, p, Φ, hNc, -⟩ := exists_whitney_normSq E M
  exact finiteDimensional_spaceHomology_of_isCompact hN hNc Φ i

variable (E) in
include E in
/-- **The homology of a compact manifold vanishes above its dimension**: `H_i(M; 𝕜) = 0` for
`i > dim M`. -/
theorem bettiNumber_eq_zero_of_compactSpace {i : ℕ} (hi : finrank ℝ E < i) :
    bettiNumber 𝕜 M i = 0 := by
  obtain ⟨K, m, N, hN, p, Φ, hNc, -⟩ := exists_whitney_normSq E M
  exact bettiNumber_eq_zero_of_isCompact hN hNc Φ hi

/-- **`χ(M)` identified** (Milnor p. 29, formula (3)): the Euler number `Morse.eulerNumberM E M`
of a compact manifold (`Σ_λ (-1)^λ C_λ` for any Morse function,
`Morse.sum_critCount_eq_eulerNumberM`) is its homological Euler characteristic
`Σ_{i ≤ dim M} (-1)^i dim H_i(M; 𝕜)`, for every field `𝕜`. -/
theorem eulerNumberM_eq_sum_bettiNumber :
    eulerNumberM E M = ∑ i ∈ range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (bettiNumber 𝕜 M i : ℤ) := by
  obtain ⟨K, m, N, hN, p, Φ, hNc, hp, f, -, hf, hcount⟩ := exists_whitney_normSq E M
  let _ := hN.chartedSpace
  rw [← sum_critCount_eq_eulerNumberM hf]
  simp only [hcount]
  have h := sum_bettiNumber_eq_sum_critCount (𝕜 := 𝕜) hN hNc (contDiff_normSq_sub p)
    hp.isNondegenerate Φ
  rw [finrank_euclideanSpace_fin] at h
  exact h.symm

variable (M) in
/-- **A Morse function on `M` is the restriction of an ambient function on an embedded copy**
(dimension `d + 1 ≥ 1`): `M` is homeomorphic, through `Φ`, to a compact submanifold
`N ⊆ ℝᴷ⁺¹` and `g = G ∘ Φ` for a smooth `G : ℝᴷ⁺¹ → ℝ` whose restriction to `N` has
non-degenerate critical points, with the same numbers `C_λ` as `g`. -/
theorem exists_ambient_of_isMorseFunction {d : ℕ} (hd : finrank ℝ E = d + 1) {g : M → ℝ}
    (hg : IsMorseFunction E g) :
    ∃ (K m : ℕ) (N : Set (𝔼 (K + 1)))
      (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 (K + 1)) (𝔼 (d + 1)) (𝔼 m) N)
      (G : 𝔼 (K + 1) → ℝ) (Φ : M ≃ₜ N), IsCompact N ∧ ContDiff ℝ ∞ G ∧ (∀ x, G (Φ x) = g x) ∧
      (letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM (𝔼 (d + 1)) (G ∘ Subtype.val) q →
        IsNondegenerate (hessianM (𝔼 (d + 1)) (G ∘ Subtype.val : N → ℝ) q)) ∧
      ∀ k, critCount E g k = (letI := hN.chartedSpace;
        critCount (𝔼 (d + 1)) (G ∘ Subtype.val : N → ℝ) k) := by
  obtain ⟨K, m, N, hN, -, hNc, -, ⟨Φ⟩⟩ := exists_diffeomorph_sliceSubmanifold (E := E) (M := M) hd
  let _ := hN.chartedSpace
  have := hN.isManifold
  have hg' : IsMorseFunction (𝔼 (d + 1)) (g ∘ Φ.symm) := hg.comp_diffeomorph_symm Φ
  obtain ⟨G, hG, hGeq⟩ : ∃ G : 𝔼 (K + 1) → ℝ, ContDiff ℝ ∞ G ∧ G ∘ Subtype.val = g ∘ Φ.symm := by
    rcases N.eq_empty_or_nonempty with hempty | hne
    · refine ⟨0, contDiff_const, funext fun q ↦ ?_⟩
      have hq : (q : 𝔼 (K + 1)) ∈ (∅ : Set (𝔼 (K + 1))) := hempty ▸ q.2
      exact absurd hq (Set.notMem_empty _)
    · exact exists_contDiff_comp_val_eq hN hNc hne hg'.contMDiff
  refine ⟨K, m, N, hN, G, Φ.toHomeomorph, hNc, hG, fun x ↦ ?_, ?_, fun k ↦ ?_⟩
  · simpa using congrFun hGeq (Φ x)
  · rw [hGeq]
    exact hg'.isNondegenerate
  · rw [hGeq]
    exact (critCount_comp_symm Φ (hg.contMDiff.of_le (by norm_cast)) k).symm

/-- **Theorem 5.2 (3) for a compact manifold** (Milnor p. 29): for every Morse function `g` on
`M`, `Σ_{i ≤ dim M} (-1)^i dim H_i(M; 𝕜) = Σ_{λ ≤ dim M} (-1)^λ C_λ(g)`. -/
theorem sum_bettiNumber_eq_sum_critCount_of_compactSpace {g : M → ℝ}
    (hg : IsMorseFunction E g) :
    ∑ i ∈ range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (bettiNumber 𝕜 M i : ℤ) =
      ∑ i ∈ range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (critCount E g i : ℤ) := by
  rw [← eulerNumberM_eq_sum_bettiNumber, sum_critCount_eq_eulerNumberM hg]

/-- **The Morse inequalities `(4_λ)` for a compact manifold** (Milnor p. 30): for every Morse
function `g` on `M`, `b_λ - b_{λ-1} + ⋯ ± b_0 ≤ C_λ - C_{λ-1} + ⋯ ± C_0`. -/
theorem altSum_bettiNumber_le_of_compactSpace {g : M → ℝ} (hg : IsMorseFunction E g)
    (l : ℕ) :
    altSum (fun i ↦ (bettiNumber 𝕜 M i : ℤ)) l ≤ altSum (fun i ↦ (critCount E g i : ℤ)) l := by
  obtain ⟨n, hn⟩ : ∃ n, finrank ℝ E = n := ⟨_, rfl⟩
  rcases n with _ | d
  · -- dimension `0`: `b_i = C_i` for every `i`
    refine le_of_eq (altSum_congr fun i _ ↦ ?_)
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have h := sum_bettiNumber_eq_sum_critCount_of_compactSpace (𝕜 := 𝕜) hg
      simpa [hn] using h
    · rw [bettiNumber_eq_zero_of_compactSpace E (by omega)]
      have hempty : {p : M | IsCriticalPointM E g p ∧ indexM E g p = i} = ∅ :=
        Set.eq_empty_of_forall_notMem fun p hp ↦
          absurd (indexM_le_finrank (E := E) g p) (by have := hp.2; omega)
      unfold critCount
      rw [hempty, Set.ncard_empty]
  · obtain ⟨K, m, N, hN, G, Φ, hNc, hG, -, hnd, hcount⟩ :=
      exists_ambient_of_isMorseFunction M hn hg
    simp only [hcount]
    exact altSum_bettiNumber_le hN hNc hG hnd Φ l

/-- **Theorem 5.2 (2), the weak Morse inequalities, for a compact manifold** (Milnor p. 29):
`dim H_λ(M; 𝕜) ≤ C_λ(g)` for every Morse function `g` on `M`. -/
theorem bettiNumber_le_critCount_of_compactSpace {g : M → ℝ} (hg : IsMorseFunction E g)
    (l : ℕ) : bettiNumber 𝕜 M l ≤ critCount E g l := by
  have := le_of_altSum_le (b := fun i ↦ (bettiNumber 𝕜 M i : ℤ))
    (c := fun i ↦ (critCount E g i : ℤ)) (altSum_bettiNumber_le_of_compactSpace hg) l
  exact_mod_cast this

/-- **The lacunary principle for a compact manifold** (Milnor p. 31): if no two consecutive
`C_i(g)` are nonzero, then `dim H_i(M; 𝕜) = C_i(g)` for every `i`. -/
theorem bettiNumber_eq_critCount_of_lacunary_of_compactSpace {g : M → ℝ}
    (hg : IsMorseFunction E g) (hc : ∀ i, critCount E g i = 0 ∨ critCount E g (i + 1) = 0) (i : ℕ) :
    bettiNumber 𝕜 M i = critCount E g i := by
  have := eq_of_altSum_le_of_lacunary (b := fun i ↦ (bettiNumber 𝕜 M i : ℤ))
    (c := fun i ↦ (critCount E g i : ℤ)) (fun _ ↦ Nat.cast_nonneg _)
    (altSum_bettiNumber_le_of_compactSpace hg) (fun i ↦ by exact_mod_cast hc i) i
  exact_mod_cast this

/-- **The homology of a manifold carrying a function with exactly two critical points, both
non-degenerate** (Reeb's situation, Theorem 4.1, p. 25, with the lacunary principle of p. 31):
if `dim M = n ≥ 2`, then `dim H_i(M; 𝕜)` is `1` for `i = 0, n` and `0` otherwise, over every field.
The two critical points are the minimum, of index `0`, and the maximum, of index `n`
(`Morse.exists_min_max_of_ncard_eq_two`), so `C_0 = C_n = 1` are the only nonzero Morse numbers.
(Reeb's theorem itself says more, `M ≅ Sⁿ`, `Morse.reeb_of_compactSpace`.) -/
theorem bettiNumber_of_ncard_eq_two (h2 : 2 ≤ finrank ℝ E)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (htwo : {x : M | IsCriticalPointM E f x}.ncard = 2)
    (hnd : ∀ x, IsCriticalPointM E f x → IsNondegenerate (hessianM E f x)) (i : ℕ) :
    bettiNumber 𝕜 M i = (if i = 0 then 1 else 0) + (if i = finrank ℝ E then 1 else 0) := by
  obtain ⟨p, q, hlt, hcrit, -, -, hp, hq⟩ :=
    exists_min_max_of_ncard_eq_two (by omega) hf htwo hnd
  have hpq : p ≠ q := fun h ↦ hlt.ne (h ▸ rfl)
  have hC : ∀ k, critCount E f k =
      (if k = 0 then 1 else 0) + (if k = finrank ℝ E then 1 else 0) := by
    intro k
    unfold critCount
    by_cases h0 : k = 0
    · subst h0
      have hset : {x : M | IsCriticalPointM E f x ∧ indexM E f x = 0} = {p} := by
        ext x
        simp only [mem_ofPred_eq, Set.mem_singleton_iff, hcrit]
        constructor
        · rintro ⟨rfl | rfl, hi⟩
          · rfl
          · omega
        · rintro rfl
          exact ⟨Or.inl rfl, hp⟩
      rw [hset, ncard_singleton, if_pos rfl, if_neg (by omega)]
    · by_cases hk : k = finrank ℝ E
      · have hset : {x : M | IsCriticalPointM E f x ∧ indexM E f x = k} = {q} := by
          ext x
          simp only [mem_ofPred_eq, Set.mem_singleton_iff, hcrit]
          constructor
          · rintro ⟨rfl | rfl, hi⟩
            · omega
            · rfl
          · rintro rfl
            exact ⟨Or.inr rfl, hq.trans hk.symm⟩
        rw [hset, ncard_singleton, if_neg h0, if_pos hk]
      · have hset : {x : M | IsCriticalPointM E f x ∧ indexM E f x = k} = ∅ := by
          ext x
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, hcrit]
          rintro (rfl | rfl) hi <;> omega
        rw [hset, ncard_empty, if_neg h0, if_neg hk]
  have hm : IsMorseFunction E f := ⟨hf, hnd⟩
  rw [bettiNumber_eq_critCount_of_lacunary_of_compactSpace hm (fun j ↦ ?_) i, hC]
  rw [hC, hC]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · right
    rw [if_neg (by omega), if_neg (by omega)]
  · by_cases hjn : j = finrank ℝ E
    · right
      rw [if_neg (by omega), if_neg (by omega)]
    · left
      rw [if_neg (by omega), if_neg hjn]

end Manifold

/-! ### Examples: the torus and the spheres -/

section Torus

variable {R r : ℝ} (hr : 0 < r) (hrR : r < R)

include hr hrR in
/-- **The homology of the torus, from its height function** (Milnor §1, pp. 1–3, with §5): the
height function has `C_0 = 1`, `C_1 = 2`, `C_2 = 1` (`Morse.Torus.critCount_height`), so over any
field `b_0 ≤ 1`, `b_1 ≤ 2`, `b_2 ≤ 1`, `b_i = 0` for `i ≥ 3`, and `b_0 - b_1 + b_2 = 0`: the
Euler characteristic of the torus is `0`, in agreement with its Poincaré–Hopf number
(`Morse.isEulerNumber_torus`). -/
theorem torus_bettiNumber {𝕜 : Type} [Field 𝕜] :
    bettiNumber 𝕜 (torus R r) 0 ≤ 1 ∧ bettiNumber 𝕜 (torus R r) 1 ≤ 2 ∧
      bettiNumber 𝕜 (torus R r) 2 ≤ 1 ∧ (∀ i, 3 ≤ i → bettiNumber 𝕜 (torus R r) i = 0) ∧
      (bettiNumber 𝕜 (torus R r) 0 : ℤ) - bettiNumber 𝕜 (torus R r) 1 +
        bettiNumber 𝕜 (torus R r) 2 = 0 := by
  have hT := isSliceSubmanifold_torus hr hrR
  let _ := hT.chartedSpace
  have hc := isCompact_torus hr hrR
  have hm := Torus.isMorseFunction_height hr hrR
  have hb := fun l ↦ bettiNumber_le_critCount (𝕜 := 𝕜) hT hc Torus.contDiff_height
    hm.isNondegenerate (Homeomorph.refl _) l
  simp only [Torus.critCount_height hr hrR] at hb
  have he := sum_bettiNumber_eq_sum_critCount (𝕜 := 𝕜) hT hc Torus.contDiff_height
    hm.isNondegenerate (Homeomorph.refl _)
  simp only [Torus.critCount_height hr hrR, finrank_euclideanSpace_fin, Finset.sum_range_succ,
    Finset.sum_range_zero] at he
  refine ⟨by simpa using hb 0, by simpa using hb 1, by simpa using hb 2, fun i hi ↦ ?_, ?_⟩
  · exact bettiNumber_eq_zero_of_finrank_lt hT hc Torus.contDiff_height hm.isNondegenerate
      (Homeomorph.refl _) (by rw [finrank_euclideanSpace_fin]; omega)
  · norm_num at he
    linarith

end Torus

section Sphere

variable {d : ℕ}

local notation "𝕊" => Milnor.Sphere.Sph (d + 1)
local notation "hS" => Milnor.Sphere.sphSub (d + 1)

/-- **The Euler characteristic of `Sⁿ`**, `n = d + 1 ≥ 1`: `Σ_i (-1)^i dim H_i(Sⁿ; 𝕜) = 1 + (-1)ⁿ`
for every field `𝕜`, from the Poincaré–Hopf number of `Sⁿ` (`Morse.isEulerNumber_sph`). -/
theorem sphere_sum_bettiNumber {𝕜 : Type} [Field 𝕜] :
    ∑ i ∈ range (d + 2), (-1 : ℤ) ^ i * (bettiNumber 𝕜 𝕊 i : ℤ) = 1 + (-1) ^ (d + 1) := by
  rw [← Morse.IsEulerNumber.eq_sum_bettiNumber hS Milnor.Sphere.isCompact_sph
    Milnor.Sphere.nonempty_sph_set (Homeomorph.refl _) (Nat.succ_pos d) isEulerNumber_sph]

/-- **The homology of `Sⁿ`, `n = d + 1 ≥ 2`, over any field** (Milnor p. 31, the lacunary
principle): the height function has `C_0 = C_n = 1` and `C_i = 0` otherwise
(`Morse.critCount_heightFun`), no two consecutive of which are nonzero, so `b_0 = b_n = 1` and
`b_i = 0` for all other `i`, in agreement with the direct computation of
`Morse/Homology/Spheres.lean` (`Morse.Homology.finrank_sphereHomology`). -/
theorem sphere_bettiNumber {𝕜 : Type} [Field 𝕜] (hd : 1 ≤ d) (i : ℕ) :
    bettiNumber 𝕜 𝕊 i = (if i = 0 then 1 else 0) + (if i = d + 1 then 1 else 0) := by
  let _ := (hS).chartedSpace
  obtain ⟨e, he⟩ := Milnor.Sphere.nonempty_sph_set (n := d + 1)
  have hm := isMorseFunction_heightFun he
  rw [bettiNumber_eq_critCount_of_lacunary hS Milnor.Sphere.isCompact_sph
    (contDiff_heightFun e) hm.isNondegenerate (Homeomorph.refl _) (fun j ↦ ?_) i,
    critCount_heightFun he]
  simp only [critCount_heightFun he]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · right
    rw [if_neg (by omega), if_neg (by omega)]
  · by_cases hjd : j = d + 1
    · right
      rw [if_neg (by omega), if_neg (by omega)]
    · left
      rw [if_neg (by omega), if_neg hjd]

/-- **The circle** (`n = 1`), where the lacunary principle does not apply (`C_0 = C_1 = 1`):
Morse theory gives `b_0 = b_1 ≤ 1`.  (The direct computation of `Morse/Homology/Spheres.lean`,
`Morse.Homology.finrank_sphereHomology`, gives `b_0 = b_1 = 1`.) -/
theorem circle_bettiNumber {𝕜 : Type} [Field 𝕜] :
    bettiNumber 𝕜 (Milnor.Sphere.Sph 1) 0 ≤ 1 ∧ bettiNumber 𝕜 (Milnor.Sphere.Sph 1) 1 ≤ 1 ∧
      bettiNumber 𝕜 (Milnor.Sphere.Sph 1) 0 = bettiNumber 𝕜 (Milnor.Sphere.Sph 1) 1 := by
  let _ := (Milnor.Sphere.sphSub 1).chartedSpace
  obtain ⟨e, he⟩ := Milnor.Sphere.nonempty_sph_set (n := 1)
  have hm := isMorseFunction_heightFun (d := 0) he
  have hb := fun l ↦ bettiNumber_le_critCount (𝕜 := 𝕜) (Milnor.Sphere.sphSub 1)
    Milnor.Sphere.isCompact_sph (contDiff_heightFun e) hm.isNondegenerate (Homeomorph.refl _) l
  have h : ∑ i ∈ range 2, (-1 : ℤ) ^ i * (bettiNumber 𝕜 (Milnor.Sphere.Sph 1) i : ℤ) =
      1 + (-1) ^ 1 := sphere_sum_bettiNumber (d := 0)
  simp only [critCount_heightFun he] at hb
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  refine ⟨by simpa using hb 0, by simpa using hb 1, ?_⟩
  norm_num at h
  omega

end Sphere

end Morse.Homology
