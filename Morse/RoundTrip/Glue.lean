import Morse

/-! Reusable glue for the round-trip audit (namespace `RoundTrip.Glue`). -/

open Set Finset Module
open scoped ContDiff Manifold

namespace RoundTrip.Glue

/-! ### The Morse filtration of an abstract compact manifold (any dimension) -/

section CellsFiltration

open Morse Morse.Homology

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

/-- On a compact manifold `M`, every Morse function `g` has a "cell filtration" in the sense of
`Morse.Homology.exists_cells_filtration`, with critical points counted by `critCount E g`.
Built from the project's Whitney embedding and `exists_cells_filtration`, without any of the
abstract Morse-inequality lemmas of `Morse/Chapter3/Inequalities.lean`. In dimension `0` the
filtration is the one of `L_p ∘ Φ`, which has the same `critCount` as `g` (all points critical of
index `0`). -/
theorem exists_cells_filtration_of_compactSpace {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] (𝕜 : Type) [Field 𝕜] {g : M → ℝ}
    (hg : IsMorseFunction E g) :
    ∃ (n : ℕ) (X : ℕ → Set M) (hX : Monotone X) (α : Type) (P : Finset α) (step ind : α → ℕ),
      0 < n ∧ X 0 = ∅ ∧ X n = univ ∧
      (∀ k < n, ∀ i, FiniteDimensional 𝕜 (subsetHomology 𝕜 i (hX (Nat.le_succ k)))) ∧
      (∀ p ∈ P, step p < n) ∧
      (∀ k < n, ∀ i, finrank 𝕜 (subsetHomology 𝕜 i (hX (Nat.le_succ k))) =
        #{p ∈ P | step p = k ∧ ind p = i}) ∧
      (∀ p ∈ P, ind p ≤ finrank ℝ E) ∧
      ∀ i, critCount E g i = #{p ∈ P | ind p = i} := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, finrank ℝ E = d := ⟨_, rfl⟩
  rcases d with _ | d
  · obtain ⟨K, m, N, hN, p, Φ, hNc, hp, f, -, hf, hcount⟩ := exists_whitney_normSq E M
    let _ := hN.chartedSpace
    obtain ⟨n, X, hX, P, step, hn, h0, htop, hP, hfin, hstep, hcells⟩ :=
      exists_cells_filtration (𝕜 := 𝕜) hN hNc (Morse.Homology.contDiff_normSq_sub p) hp.isNondegenerate Φ
    refine ⟨n, X, hX, N, P, step, indexM (𝔼 (finrank ℝ E)) _, hn, h0, htop, hfin, hstep,
      hcells, fun q _ ↦ ?_, fun i ↦ ?_⟩
    · have := indexM_le_finrank (E := 𝔼 (finrank ℝ E))
        ((fun x : 𝔼 (K + 1) ↦ ‖x - p‖ ^ 2) ∘ (Subtype.val : N → 𝔼 (K + 1))) q
      rwa [finrank_euclideanSpace_fin] at this
    · rw [← critCount_eq_card hN hP i, ← hcount i]
      unfold critCount
      congr 1
      ext q
      simp only [mem_ofPred_eq, isCriticalPointM_of_finrank_eq_zero hd, true_and]
      have h1 := indexM_le_finrank (E := E) g q
      have h2 := indexM_le_finrank (E := E) f q
      omega
  · obtain ⟨K, m, N, hN, G, Φ, hNc, hG, -, hnd, hcount⟩ :=
      exists_ambient_of_isMorseFunction M hd hg
    let _ := hN.chartedSpace
    obtain ⟨n, X, hX, P, step, hn, h0, htop, hP, hfin, hstep, hcells⟩ :=
      exists_cells_filtration (𝕜 := 𝕜) hN hNc hG hnd Φ
    refine ⟨n, X, hX, N, P, step, indexM (𝔼 (d + 1)) _, hn, h0, htop, hfin, hstep,
      hcells, fun q _ ↦ ?_, fun i ↦ ?_⟩
    · have := indexM_le_finrank (E := 𝔼 (d + 1)) (G ∘ (Subtype.val : N → 𝔼 (K + 1))) q
      rw [finrank_euclideanSpace_fin] at this
      omega
    · rw [hcount i, critCount_eq_card hN hP i]

end CellsFiltration

/-! ### Compact slice submanifolds of `ℝ¹` of positive dimension do not exist -/

section NoKZero

/-- A nonempty compact slice submanifold of `ℝ¹` modelled on `ℝ^{d+1}` does not exist: a slice
chart forces the complement to be `ℝ⁰`, so every slice chart domain lies in `N` and `N` is a
nonempty compact open subset of `ℝ¹`. (Used to dispose of `K = 0` in statements quantifying over
`N ⊆ ℝ^{K+1}`.) -/
theorem no_sliceSubmanifold_R1 {d m : ℕ} {N : Set (EuclideanSpace ℝ (Fin (0 + 1)))}
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (0 + 1)))
      (EuclideanSpace ℝ (Fin (d + 1))) (EuclideanSpace ℝ (Fin m)) N) (hc : IsCompact N)
    (hne : N.Nonempty) : False := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨σ, hσ⟩ := hN x hx
  have hloc := σ.φ.isLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (0 + 1)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)) × EuclideanSpace ℝ (Fin m)) ∞ hσ
  have hbij := (hloc.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv.finrank_eq
  have hm : m = 0 := by
    have : finrank ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (0 + 1))) x) = 1 :=
      finrank_euclideanSpace_fin
    have h2 : finrank ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)) ×
        EuclideanSpace ℝ (Fin m)) (σ.φ x)) = d + 1 + m := by
      change finrank ℝ (EuclideanSpace ℝ (Fin (d + 1)) × EuclideanSpace ℝ (Fin m)) = _
      simp [finrank_prod]
    omega
  subst hm
  have hopen : IsOpen N := by
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨τ, hτ⟩ := hN p hp
    exact ⟨τ.φ.source, fun q hq ↦ (τ.slice q hq).2 (Subsingleton.elim _ _), τ.φ.open_source, hτ⟩
  rcases isClopen_iff.1 ⟨hc.isClosed, hopen⟩ with h | h
  · exact (Set.nonempty_of_mem hx).ne_empty h
  · rw [h] at hc
    exact noncompact_univ _ hc

end NoKZero

/-! ### A `Fin`-indexed chain of subsets with one-cell steps, as a monotone `ℕ`-filtration -/

section FinFiltration

open Morse.Homology

/-- A chain `X_0 ⊆ X_1 ⊆ ⋯ ⊆ X_k` (`Xs : Fin (k+1) → Set X`, each step an inclusion) whose step
`i` has homology `F` in degree `lam i` and `0` otherwise, extended to a monotone `ℕ`-filtration
`Y j = X_{min j k}` with the cell data of `Morse.Homology.exists_cells_filtration` (`P = univ`,
`step = val`, `ind = lam`). -/
theorem exists_nat_filtration {F : Type} [Field F] {X : Type} [TopologicalSpace X] {k : ℕ}
    (Xs : Fin (k + 1) → Set X) (lam : Fin k → ℕ)
    (hstep : ∀ i : Fin k, ∃ h : Xs i.castSucc ⊆ Xs i.succ, ∀ n,
      Module.Finite F (subsetHomology F n h) ∧
        finrank F (subsetHomology F n h) = if n = lam i then 1 else 0) :
    ∃ (Y : ℕ → Set X) (hY : Monotone Y), Y 0 = Xs 0 ∧ Y k = Xs (Fin.last k) ∧
      (∀ j < k, ∀ n, FiniteDimensional F (subsetHomology F n (hY (Nat.le_succ j)))) ∧
      (∀ j < k, ∀ n, finrank F (subsetHomology F n (hY (Nat.le_succ j))) =
        #{p ∈ (Finset.univ : Finset (Fin k)) | p.val = j ∧ lam p = n}) := by
  classical
  let Y : ℕ → Set X := fun j ↦ Xs ⟨min j k, by omega⟩
  have hsucc : ∀ j, Y j ⊆ Y (j + 1) := by
    intro j
    rcases lt_or_ge j k with hj | hj
    · obtain ⟨h, -⟩ := hstep ⟨j, hj⟩
      have e1 : Y j = Xs (Fin.castSucc ⟨j, hj⟩) := by
        simp only [Y]; congr 1; ext; simp; omega
      have e2 : Y (j + 1) = Xs (Fin.succ ⟨j, hj⟩) := by
        simp only [Y]; congr 1; ext; simp; omega
      rw [e1, e2]; exact h
    · have e1 : Y j = Y (j + 1) := by simp only [Y]; congr 2; omega
      rw [e1]
  have hY : Monotone Y := monotone_nat_of_le_succ hsucc
  refine ⟨Y, hY, by simp [Y], by simp only [Y]; congr 1; ext; simp, fun j hj n ↦ ?_,
    fun j hj n ↦ ?_⟩
  · obtain ⟨h, hh⟩ := hstep ⟨j, hj⟩
    have := (hh n).1
    exact finiteDimensional_subsetHomology_congr h _ (by simp only [Y]; congr 1; ext; simp; omega)
      (by simp only [Y]; congr 1; ext; simp; omega) n
  · obtain ⟨h, hh⟩ := hstep ⟨j, hj⟩
    rw [finrank_subsetHomology_congr _ h (by simp only [Y]; congr 1; ext; simp; omega)
      (by simp only [Y]; congr 1; ext; simp; omega) n, (hh n).2]
    have : ({p ∈ (Finset.univ : Finset (Fin k)) | p.val = j ∧ lam p = n} : Finset (Fin k)) =
        if n = lam ⟨j, hj⟩ then {⟨j, hj⟩} else ∅ := by
      ext p
      split_ifs with hn
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, -⟩; exact Fin.ext h1
        · rintro rfl; exact ⟨rfl, hn.symm⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
          not_and]
        rintro h1 rfl
        exact hn (by rw [show p = ⟨j, hj⟩ from Fin.ext h1])
    rw [this]
    split_ifs <;> simp

end FinFiltration

/-! ### A Morse function on a compact manifold, as an ambient function on an embedded copy -/

section AmbientAnyDim

open Morse

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

/-- Every Morse function `g` on a compact manifold `M` (any dimension) has the Morse numbers of
`G|N` for a compact slice submanifold `N ⊆ ℝᴷ⁺¹` of dimension `n = dim M`, homeomorphic to `M`,
and a smooth `G` whose restriction to `N` has non-degenerate critical points.  Dimension `≥ 1`:
the project's `exists_ambient_of_isMorseFunction`; dimension `0`: `L_p` on a Whitney copy
(`exists_whitney_normSq`), all of whose points are critical of index `0`, like those of `g`. -/
theorem exists_ambient_any_dim {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {g : M → ℝ}
    (hg : IsMorseFunction E g) :
    ∃ (n K m : ℕ) (N : Set (𝔼 (K + 1)))
      (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 (K + 1)) (𝔼 n) (𝔼 m) N)
      (G : 𝔼 (K + 1) → ℝ) (_Φ : M ≃ₜ N), n = finrank ℝ E ∧ IsCompact N ∧ ContDiff ℝ ∞ G ∧
      (letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM (𝔼 n) (G ∘ Subtype.val) q →
        IsNondegenerate (hessianM (𝔼 n) (G ∘ Subtype.val : N → ℝ) q)) ∧
      ∀ k, critCount E g k = (letI := hN.chartedSpace;
        critCount (𝔼 n) (G ∘ Subtype.val : N → ℝ) k) := by
  obtain ⟨d, hd⟩ : ∃ d, finrank ℝ E = d := ⟨_, rfl⟩
  rcases d with _ | d
  · obtain ⟨K, m, N, hN, p, Φ, hNc, hp, f, -, hf, hcount⟩ := Homology.exists_whitney_normSq E M
    let _ := hN.chartedSpace
    refine ⟨finrank ℝ E, K, m, N, hN, _, Φ, rfl, hNc, Homology.contDiff_normSq_sub p,
      hp.isNondegenerate, fun k ↦ ?_⟩
    rw [← hcount k]
    unfold critCount
    congr 1
    ext q
    simp only [Set.mem_ofPred_eq, isCriticalPointM_of_finrank_eq_zero hd, true_and]
    have h1 := indexM_le_finrank (E := E) g q
    have h2 := indexM_le_finrank (E := E) f q
    omega
  · obtain ⟨K, m, N, hN, G, Φ, hNc, hG, -, hnd, hcount⟩ :=
      Homology.exists_ambient_of_isMorseFunction M hd hg
    exact ⟨d + 1, K, m, N, hN, G, Φ, hd.symm, hNc, hG, hnd, hcount⟩

end AmbientAnyDim

/-! ### Euler numbers (`Morse.IsEulerNumber`) and index sums over finite zero sets -/

section EulerNumber

open Morse

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

/-- An index sum over an injective enumeration of the zeros is the `finsum` over the zero set. -/
lemma sum_enum_eq_finsum {α : Type} (S : Set α) (g : α → ℤ) {j : ℕ} (z : Fin j → α)
    (hz : Function.Injective z) (hzS : ∀ q, q ∈ S ↔ ∃ i, q = z i) :
    ∑ i, g (z i) = ∑ᶠ q ∈ S, g q := by
  classical
  have hS : S = Set.range z := by
    ext q; rw [hzS]; exact ⟨fun ⟨i, h⟩ ↦ ⟨i, h.symm⟩, fun ⟨i, h⟩ ↦ ⟨i, h.symm⟩⟩
  rw [hS, finsum_mem_range hz]
  exact (finsum_eq_sum_of_fintype _).symm

/-- A finite set admits an injective enumeration. -/
lemma exists_enum {α : Type} {S : Set α} (hS : S.Finite) :
    ∃ (j : ℕ) (z : Fin j → α), Function.Injective z ∧ ∀ q, q ∈ S ↔ ∃ i, q = z i := by
  classical
  let s := hS.toFinset
  let e := s.equivFin
  refine ⟨s.card, fun i ↦ (e.symm i).1, fun i i' h ↦ e.symm.injective (Subtype.ext h), fun q ↦ ?_⟩
  constructor
  · intro hq
    exact ⟨e ⟨q, hS.mem_toFinset.2 hq⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    exact hS.mem_toFinset.1 (e.symm i).2

variable {K d m : ℕ} {N : Set (𝔼 (K + 1))}
  (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 (K + 1)) (𝔼 (d + 1)) (𝔼 m) N)
  (hc : IsCompact N) (hne : N.Nonempty)

include hc in
/-- The zeros of the tangential gradient of an ambient `F` whose restriction has non-degenerate
critical points are finitely many (they are the critical points). -/
lemma finite_zeros_tangentialGradient {F : 𝔼 (K + 1) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM (𝔼 (d + 1)) (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM (𝔼 (d + 1)) (F ∘ Subtype.val) q)) :
    {q : N | tangentialGradient hN F q = 0}.Finite := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have : CompactSpace N := isCompact_iff_compactSpace.1 hc
  have hM : IsMorseFunction (𝔼 (d + 1)) (F ∘ Subtype.val) := ⟨contMDiff_comp_val hN hF, hnd⟩
  exact hM.finite_setOf_isCriticalPointM.subset fun q hq ↦
    (tangentialGradient_eq_zero_iff hN (hF.differentiable (by simp) _)).1 hq

/-- If every smooth tangent field with finitely many zeros has index sum `c`, then every Euler
number of `N` (`Morse.IsEulerNumber`) is `c`: compare on the tangential gradient of a Morse
function `L_p = ‖· - p‖²`. -/
lemma eq_of_isEulerNumber {c χN : ℤ} (hχ : IsEulerNumber hN hc hne χN)
    (h1 : letI := hN.chartedSpace; ∀ (v : N → 𝔼 (K + 1))
      (hv : ContMDiff 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (K + 1)) ∞ v),
      (∀ q, v q ∈ Milnor.Tub.tanN hN q) → {q : N | v q = 0}.Finite →
      ∑ᶠ q ∈ {q : N | v q = 0}, Milnor.Tub.indexN hN hc hne v hv q = c) :
    χN = c := by
  let _ := hN.chartedSpace
  obtain ⟨p, hp⟩ := exists_isMorseFunction_normSq_sub (hM := hN)
  have hF := Homology.contDiff_normSq_sub p
  have hfin := finite_zeros_tangentialGradient hN hc hF hp.isNondegenerate
  obtain ⟨j, z, hz, hzS⟩ := exists_enum hfin
  have := hχ _ (contMDiff_tangentialGradient hN hc hne hF)
    (tangentialGradient_mem_range hN _) z hz hzS
  rw [← this, sum_enum_eq_finsum _ _ z hz hzS]
  exact h1 _ _ (tangentialGradient_mem_range hN _) hfin

end EulerNumber

/-! ### Changing the complement of a slice submanifold along a linear isomorphism -/

section SliceComplement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W']

/-- A slice submanifold with complement `W` is one with complement `W'` for any `W ≃L W'`:
compose each slice chart with `id × L`. -/
theorem isSliceSubmanifold_congr_complement {S : Set M}
    (hS : Milnor.IsSliceSubmanifold I Z W S) (L : W ≃L[ℝ] W') :
    Milnor.IsSliceSubmanifold I Z W' S := by
  intro p hp
  obtain ⟨σ, hσ⟩ := hS p hp
  let e : Diffeomorph 𝓘(ℝ, Z × W) 𝓘(ℝ, Z × W') (Z × W) (Z × W') ∞ :=
    ((ContinuousLinearEquiv.refl ℝ Z).prodCongr L).toDiffeomorph
  let φ' := σ.φ.trans e.toPartialDiffeomorph
  have hsrc : φ'.source = σ.φ.source := by
    change σ.φ.source ∩ _ = _
    exact Set.inter_eq_left.2 fun _ _ ↦ Set.mem_univ _
  have happ : ∀ q, φ' q = ((σ.φ q).1, L (σ.φ q).2) := fun q ↦ rfl
  refine ⟨⟨φ', σ.x₀, σ.x₀_mem, hsrc ▸ σ.x₀_source, fun q hq ↦ ?_⟩, hsrc ▸ hσ⟩
  rw [hsrc] at hq
  rw [happ, σ.slice q hq]
  simp

end SliceComplement

/-! ### Structure independence of tangent spaces and of the nullity of `dE` -/

section StructIndep

open Morse

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W']
  {S : Set V}

/-- A slice chart with complement `W`, re-read with complement `W'` along `L : W ≃L W'`. -/
noncomputable def sliceChartCongr (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W S) (L : W ≃L[ℝ] W') :
    Milnor.SliceChart 𝓘(ℝ, V) Z W' S where
  φ := σ.φ.trans ((ContinuousLinearEquiv.refl ℝ Z).prodCongr L).toDiffeomorph.toPartialDiffeomorph
  x₀ := σ.x₀
  x₀_mem := σ.x₀_mem
  x₀_source := ⟨σ.x₀_source, Set.mem_univ _⟩
  slice q hq := by
    rw [σ.slice q hq.1]
    change (σ.φ q).2 = 0 ↔ L (σ.φ q).2 = 0
    simp

theorem sliceChartCongr_source (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W S) (L : W ≃L[ℝ] W') :
    (sliceChartCongr σ L).φ.source = σ.φ.source := by
  change σ.φ.source ∩ _ = _
  exact Set.inter_eq_left.2 fun _ _ ↦ Set.mem_univ _

theorem sliceChartCongr_apply_fst (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W S) (L : W ≃L[ℝ] W') (q : V) :
    ((sliceChartCongr σ L).φ q).1 = (σ.φ q).1 := rfl

theorem sliceParam_sliceChartCongr (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W S) (L : W ≃L[ℝ] W') :
    sliceParam (sliceChartCongr σ L) = sliceParam σ := by
  ext1 z
  change σ.φ.invFun (z, L.symm 0) = σ.φ.invFun (z, 0)
  simp

/-- **The tangent space `T_qS ⊆ V` does not depend on the slice structure**, nor on its
complement (any two complements of the same dimension). -/
theorem tangentSubspace_congr (hS : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W S)
    (hS' : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W' S) (L : W' ≃L[ℝ] W) (q : S) :
    tangentSubspace hS q = tangentSubspace hS' q := by
  obtain ⟨σ, hσ⟩ := hS' q q.2
  have hσ' : q.1 ∈ (sliceChartCongr σ L).φ.source := by rwa [sliceChartCongr_source]
  rw [tangentSubspace_eq_range_fderiv_sliceParam hS _ hσ',
    tangentSubspace_eq_range_fderiv_sliceParam hS' σ hσ, sliceParam_sliceChartCongr,
    sliceChartCongr_apply_fst]

variable {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']

/-- The derivative of `F ∘ val` (`F` linear) on a slice submanifold, by the chain rule. -/
theorem mfderiv_clm_comp_val (hS : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W S) (F : V →L[ℝ] V')
    (q : S) :
    letI := hS.chartedSpace
    (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, V') (fun x : S => F x.1) q : Z →L[ℝ] V') =
      F.comp (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : S → V) q) := by
  letI := hS.chartedSpace
  have := hS.isManifold
  have hv : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : S → V) q :=
    (hS.contMDiff_val q).mdifferentiableAt (by simp)
  have hF : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, V') F q.1 := F.differentiableAt.mdifferentiableAt
  have h := mfderiv_comp q hF hv
  rw [mfderiv_eq_fderiv, F.fderiv] at h
  exact h

/-- **Rank–nullity for `d(F ∘ val)`**: the nullity of `d(F|S)` at `q` is `dim Z` minus the
dimension of `F(T_qS)`. -/
theorem finrank_ker_mfderiv_clm_comp_val [FiniteDimensional ℝ Z]
    (hS : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W S) (F : V →L[ℝ] V') (q : S) :
    letI := hS.chartedSpace
    finrank ℝ (LinearMap.ker (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, V') (fun x : S => F x.1) q).toLinearMap) +
      finrank ℝ ((tangentSubspace hS q).map (F : V →ₗ[ℝ] V')) = finrank ℝ Z := by
  let _ := hS.chartedSpace
  rw [mfderiv_clm_comp_val hS F q, tangentSubspace, ← LinearMap.range_comp, add_comm]
  exact LinearMap.finrank_range_add_finrank_ker _

/-- The endpoint map `(q, v) ↦ q + v` as a continuous linear map. -/
noncomputable def endptCLM (n : ℕ) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.fst ℝ _ _ + ContinuousLinearMap.snd ℝ _ _

/-- **The nullity of `dE` on the normal bundle does not depend on the slice structure of `N`**:
the project's `endpointNullity` (canonical structure `isSliceSubmanifold_normalBundle`) equals
the nullity of `d(E|N)` for any other slice structure `hNN` on `N` modelled on `ℝⁿ` (complement
`W'` of the same dimension as the canonical one). -/
theorem endpointNullity_eq_of_slice {n k w : ℕ} {M : Set (EuclideanSpace ℝ (Fin n))}
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin k))
      (EuclideanSpace ℝ (Fin w)) M) (hkw : k + w = n)
    (hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)) W' (Milnor.Problems.normalBundleSet hM))
    (L : W' ≃L[ℝ] (EuclideanSpace ℝ (Fin w) × EuclideanSpace ℝ (Fin k)))
    (x : Milnor.Problems.normalBundleSet hM) :
    endpointNullity hM hkw x =
      (letI := hNN.chartedSpace
      finrank ℝ (LinearMap.ker (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun y : Milnor.Problems.normalBundleSet hM => y.1.1 + y.1.2) x).toLinearMap)) := by
  have hc := Milnor.Problems.isSliceSubmanifold_normalBundle hM hkw
  have h1 := finrank_ker_mfderiv_clm_comp_val hc (endptCLM n) x
  have h2 := finrank_ker_mfderiv_clm_comp_val hNN (endptCLM n) x
  rw [tangentSubspace_congr hc hNN L x] at h1
  have h1' : endpointNullity hM hkw x + finrank ℝ ((tangentSubspace hNN x).map
      (endptCLM n : _ →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) = finrank ℝ (EuclideanSpace ℝ (Fin n)) := h1
  have e2 : (fun y : Milnor.Problems.normalBundleSet hM => y.1.1 + y.1.2) =
      (fun y : Milnor.Problems.normalBundleSet hM => endptCLM n y.1) := rfl
  rw [e2]
  have h2' : (letI := hNN.chartedSpace
      finrank ℝ (LinearMap.ker (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun y : Milnor.Problems.normalBundleSet hM => endptCLM n y.1) x).toLinearMap)) +
      finrank ℝ ((tangentSubspace hNN x).map
      (endptCLM n : _ →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) = finrank ℝ (EuclideanSpace ℝ (Fin n)) := h2
  exact Nat.add_right_cancel (h1'.trans h2'.symm)

end StructIndep

/-! ### Derivatives of a difference in a smooth coordinate system -/

section IterSub

open Morse

/-- In a smooth coordinate system `y` of `M`, the iterated derivative of `(g - f) ∘ y⁻¹` at a
point of the target is the difference of those of `g ∘ y⁻¹` and `f ∘ y⁻¹`. -/
theorem iteratedFDeriv_sub_comp_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] {y : OpenPartialHomeomorph M E'} (hy : IsSmoothCoord E y) {f g : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g) {u : E'}
    (hu : u ∈ y.target) (i : ℕ) :
    iteratedFDeriv ℝ i ((fun x => g x - f x) ∘ y.symm) u =
      iteratedFDeriv ℝ i (g ∘ y.symm) u - iteratedFDeriv ℝ i (f ∘ y.symm) u := by
  have hcd : ∀ h : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ h → ContDiffAt ℝ i (h ∘ y.symm) u := by
    intro h hh
    have h1 : ContDiffOn ℝ ∞ (h ∘ y.symm) y.target := by
      rw [← contMDiffOn_iff_contDiffOn]
      exact hh.comp_contMDiffOn hy.contMDiffOn_symm
    exact ((h1.contDiffAt (y.open_target.mem_nhds hu))).of_le (by exact_mod_cast le_top)
  have : ((fun x => g x - f x) ∘ y.symm) = (g ∘ y.symm) - (f ∘ y.symm) := rfl
  rw [this, iteratedFDeriv_sub_apply (hcd g hg) (hcd f hf)]

end IterSub

end RoundTrip.Glue
