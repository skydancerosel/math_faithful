import Morse.Homology.MorseHomologyCells

/-!
Milnor, *Morse Theory*, §5, pp. 28–31: Theorem 5.2, the inequalities `(4_λ)` and Corollary 5.4
in singular homology, for a compact submanifold of Euclidean space.

# The Morse inequalities in singular homology

## Milnor's text, paraphrased

* **p. 29.**  `M` is compact and `f` a differentiable function on `M` with only isolated,
  non-degenerate critical points.  Milnor chooses `a_1 < ⋯ < a_k` such that `M^{a_i}` contains
  exactly `i` critical points and `M^{a_k} = M`, and reads off from Theorems 3.1, 3.2 and
  excision that `H_*(M^{a_i}, M^{a_{i-1}})` is the coefficient field in the dimension `λ_i` of the
  `i`-th critical point and zero otherwise.  Lemma 5.1, applied to the Betti numbers `R_λ` and to
  the Euler characteristic `χ`, gives **Theorem 5.2** (the weak Morse inequalities):
  `(2) R_λ(M) ≤ C_λ` and `(3) Σ_λ (-1)^λ R_λ(M) = Σ_λ (-1)^λ C_λ`, where
  `R_λ(M) = dim H_λ(M; F)` over a field `F` and `C_λ` is the number of critical points of index
  `λ`.
* **p. 30.**  Lemma 5.3 (the subadditivity of `S_λ = R_λ - R_{λ-1} + ⋯ ± R_0`) gives the
  stronger inequalities `(4_λ)`: `R_λ - R_{λ-1} + ⋯ ± R_0 ≤ C_λ - C_{λ-1} + ⋯ ± C_0`.
* **p. 31.**  **Corollary 5.4**: if `C_{λ+1} = C_{λ-1} = 0`, then `R_λ = C_λ` and
  `R_{λ+1} = R_{λ-1} = 0`; hence the homology of `ℂPⁿ` (the lacunary principle).

## What is proved here

Let `N` be a compact slice submanifold of a finite-dimensional real normed space `V` (Milnor's
`ℝᴷ`), `f = F|N` the restriction of a smooth `F : V → ℝ` all of whose critical points on `N`
are non-degenerate, and `𝕜` any field.  The statements are made for any space `T` homeomorphic to
`N` (`e : T ≃ₜ N`; for `N` itself take `e = Homeomorph.refl N`, as in the primed versions
`Morse.Homology.bettiNumber_le_critCount'` etc.): homology is computed in the universe of `𝕜`,
and this lets an abstract manifold in any universe use the proof through a Whitney embedding
(`Morse/Homology/MorseHomologyManifold.lean`).  Throughout, `b_i = dim H_i(T; 𝕜)`
(`Morse.Homology.bettiNumber`) and `C_λ = Morse.critCount Z f λ`.

* `Morse.Homology.sublevel_step`: **the homology of a slab** (p. 29).  If `a' ≤ a` are regular
  values and `(a', a)` contains at most one critical value, then `H_i(N^a, N^{a'}; 𝕜)` is
  finite-dimensional, of dimension the number of critical points of index `i` in
  `f⁻¹(a', a)` (Theorem 3.1 when there is no critical value; Remark 3.3, Theorem 3.1 twice and
  the cell computation `Morse.Homology.cellAttachHomology` otherwise, through
  `Morse.Homology.finrank_subsetHomology_of_cells`).
* `Morse.Homology.exists_morse_filtration` (`exists_morse_filtration'` for `N` itself): **the
  filtration** `∅ = N^{a_0} ⊆ ⋯ ⊆ N^{a_n} = N` by regular values with at most one critical value
  in each `(a_k, a_{k+1})`, each step having the homology of its critical points.
* `Morse.Homology.finiteDimensional_spaceHomology`: `H_i(N; 𝕜)` is finite-dimensional.
* `Morse.Homology.bettiNumber_le_critCount`: **Theorem 5.2 (2)**, `b_λ ≤ C_λ`.
* `Morse.Homology.altSum_bettiNumber_le`: **the inequalities `(4_λ)`**.
* `Morse.Homology.sum_bettiNumber_eq_sum_critCount`: **Theorem 5.2 (3)**,
  `Σ_{i ≤ n} (-1)^i b_i = Σ_{λ ≤ n} (-1)^λ C_λ`, `n = dim N`.
* `Morse.Homology.bettiNumber_eq_zero_of_finrank_lt`, `subsingleton_spaceHomology_of_finrank_lt`:
  `H_i(N; 𝕜) = 0` for `i > dim N`.
* `Morse.Homology.bettiNumber_eq_critCount_of_succ`, `bettiNumber_eq_critCount_of_zero`:
  **Corollary 5.4**; `Morse.Homology.bettiNumber_eq_critCount_of_lacunary`: **the lacunary
  principle**, `b_i = C_i` for all `i` if no two consecutive `C_i` are nonzero.

The homology of the cells attached at a critical level is `Morse.Homology.cellAttachHomology`
(`Morse/Homology/MorseHomologyCells.lean`), the cell-attachment lemma of
`Morse/Homology/CellAttach.lean`.

## What Milnor's text leaves implicit

Besides the points recorded in `Morse/Homology/MorseHomologyBasic.lean` (moving the bottom of a
pair needs the exact sequence of a triple; strong deformation retractions; "excision") and in
`Morse/Chapter3/Inequalities.lean` (the algebra):

* **Several critical points on one level.**  "`M^{a_i}` contains exactly `i` critical points"
  needs distinct critical values.  Here each slab contains at most one critical *level*, with any
  number of critical points on it; Remark 3.3 attaches all their cells at once
  (`Morse.remark_3_3_submanifold`), and the homology of the slab counts them by index.
* **The bottom and the top of the filtration.**  Milnor's chain starts at `M^{a_0} = ∅` without
  naming `a_0`, and ends at `M^{a_k} = M`.  Both rest on the minimum and the maximum of `f` on
  the compact `M` being critical values (`Morse.isCriticalPointM_of_forall_le`,
  `Morse.isCriticalPointM_of_forall_ge`): any value below every critical value has an empty
  sublevel set, any value above every critical value has `M^a = M`.
* **"Theorem 3.1 in disguise".**  Passing from `(M^{a_i}, M^{a_{i-1}})` to
  `(M^{c+ε}, M^{c-ε})` uses Theorem 3.1 on the two regular slabs `[a_{i-1}, c - ε]` and
  `[c + ε, a_i]`, with `ε` smaller than the `ε` of Theorem 3.2 / Remark 3.3 and than the
  distances from `c` to `a_{i-1}` and `a_i`.  On a compact manifold the slabs are compact, as
  Theorems 3.1 and 3.2 require.
* **Finiteness.**  `R_λ(M)` is only defined when `H_λ(M; F)` is finite-dimensional; this is a
  consequence of the computation (each slab has finite-dimensional homology, and finiteness
  propagates along the exact sequences), not an assumption.
* **`R_λ(M) = 0` for `λ > dim M`**, which makes `Σ_λ (-1)^λ R_λ(M)` a finite sum, follows from
  (2), since every index is at most `dim M`.
* **Isolated critical points.**  Non-degenerate critical points are isolated (Corollary 2.3), so
  on a compact manifold there are finitely many; "isolated" is redundant.
* **`ℂPⁿ`** is not treated in this file.  Its Morse function `Σ c_j|z_j|²` and its homology
  over any field are in `Morse/Chapter3/ProjectiveMorse.lean`
  (`Morse.bettiNumber_complexProjectiveSpace`).  The spheres, for which the lacunary principle
  also gives the whole homology, are in `Morse/Homology/MorseHomologyManifold.lean`.
-/

open CategoryTheory Limits AlgebraicTopology Module Set Finset
open scoped ContDiff Manifold

universe u v

noncomputable section

namespace Morse.Homology

variable {𝕜 : Type u} [Field 𝕜]

/-! ### The slabs of a function on a compact submanifold -/

section Submanifold

variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} {T : Type u} [TopologicalSpace T]

/-- **One critical level** (Milnor p. 29, with Remark 3.3).  Let `S` be a finite set of
non-degenerate critical points of `f = F|N`, all on the level `c`, and `a' < c < a` such that no
other critical value lies in `[a', a]`.  Then `H_i(N^a, N^{a'}; 𝕜)` (read in a space `T`
homeomorphic to `N`) is finite-dimensional, of dimension the number of points of `S` of index
`i`.  Proof: Remark 3.3 at `c` for a small `ε`, Theorem 3.1 on `[a', c - ε]` and `[c + ε, a]`,
and `Morse.Homology.finrank_subsetHomology_of_cells`, all carried to `T` by `e`. -/
theorem sublevel_step_critical (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F) (e : T ≃ₜ N) {S : Finset N} {c : ℝ}
    (hS : letI := hN.chartedSpace;
      ∀ p ∈ S, IsNondegenerateCriticalPointM Z (F ∘ Subtype.val) p ∧ F p = c)
    {a' a : ℝ} (ha' : a' < c) (ha : c < a)
    (hother : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q → q ∉ S →
      F q < a' ∨ a < F q) (i : ℕ) :
    letI := hN.chartedSpace
    FiniteDimensional 𝕜 (subsetHomology 𝕜 i (preimage_mono (f := e)
        (sublevel_mono (F ∘ Subtype.val : N → ℝ) (ha'.trans ha).le))) ∧
      finrank 𝕜 (subsetHomology 𝕜 i (preimage_mono (f := e)
        (sublevel_mono (F ∘ Subtype.val : N → ℝ) (ha'.trans ha).le))) =
        #{p ∈ S | indexM Z (F ∘ Subtype.val) p = i} := by
  classical
  let _ := hN.chartedSpace
  have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  have : T2Space T := e.isEmbedding.t2Space
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfc : Continuous f := hF.continuous.comp continuous_subtype_val
  set ε₀ := min (c - a') (a - c) with hε₀_def
  have hε₀ : 0 < ε₀ := lt_min (by linarith) (by linarith)
  have hK : IsCompact (f ⁻¹' Icc (c - ε₀) (c + ε₀)) := (isClosed_Icc.preimage hfc).isCompact
  have honly : ∀ q : N, F q ∈ Icc (c - ε₀) (c + ε₀) → IsCriticalPointM Z f q → q ∈ S := by
    intro q hq hc
    by_contra hqS
    rcases hother q hc hqS with h1 | h1
    · linarith [hq.1, min_le_left (c - a') (a - c)]
    · linarith [hq.2, min_le_right (c - a') (a - c)]
  -- Remark 3.3 at the level `c`
  obtain ⟨ε₁, hε₁, H⟩ := remark_3_3_submanifold hN hF S hS hε₀ hK honly
  set ε := min ε₁ (ε₀ / 2) with hε_def
  have hε : 0 < ε := lt_min hε₁ (by linarith)
  have hεε₀ : ε < ε₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h1 : ε < c - a' := lt_of_lt_of_le hεε₀ (min_le_left _ _)
  have h2 : ε < a - c := lt_of_lt_of_le hεε₀ (min_le_right _ _)
  obtain ⟨χ, hprops, hdisj, hsdr⟩ := H ε hε (min_le_left _ _)
  -- Theorem 3.1 on `[a', c - ε]` and `[c + ε, a]`
  have hno : ∀ {b b' : ℝ}, a' ≤ b → b' ≤ a → (b' < c ∨ c < b) →
      ∀ q : N, F q ∈ Icc b b' → ¬IsCriticalPointM Z f q := by
    intro b b' hb hb' hbp q hq hc
    by_cases hqS : q ∈ S
    · have := (hS q hqS).2
      rcases hbp with h | h <;> linarith [hq.1, hq.2]
    · rcases hother q hc hqS with h | h <;> linarith [hq.1, hq.2]
  have hsdr₁ := (theorem_3_1_submanifold_of_isCompact hN hNc hF (a := a') (b := c - ε)
    (by linarith) (hno le_rfl (by linarith) (Or.inl (by linarith)))).2.1
  have hsdr₂ := (theorem_3_1_submanifold_of_isCompact hN hNc hF (a := c + ε) (b := a)
    (by linarith) (hno (by linarith) le_rfl (Or.inr (by linarith)))).2.1
  -- the cells, indexed by `Fin #S` and carried to `T`
  set σ : Fin #S ≃ S := S.equivFin.symm with hσ
  set χ' : (j : Fin #S) → EuclideanSpace ℝ (Fin (indexM Z f (σ j))) → T :=
    fun j z ↦ e.symm (χ (σ j) z) with hχ'
  have himage : ∀ j, χ' j '' Metric.closedBall 0 1 = e ⁻¹' (χ (σ j) '' Metric.closedBall 0 1) :=
    fun j ↦ by rw [← e.image_symm, ← image_comp]; rfl
  have hunion : e ⁻¹' (sublevel f (c - ε) ∪ ⋃ p, χ p '' Metric.closedBall 0 1) =
      e ⁻¹' sublevel f (c - ε) ∪ ⋃ j, χ' j '' Metric.closedBall 0 1 := by
    rw [preimage_union, preimage_iUnion]
    congr 1
    simp only [himage]
    exact (σ.surjective.iUnion_comp fun p ↦ e ⁻¹' (χ p '' Metric.closedBall 0 1)).symm
  have hcells := finrank_subsetHomology_of_cells (𝕜 := 𝕜) (cellAttachHomology 𝕜) (χ := χ')
    (A := e ⁻¹' sublevel f a') (B := e ⁻¹' sublevel f (c - ε)) (X' := e ⁻¹' sublevel f (c + ε))
    (X := e ⁻¹' sublevel f a)
    ((isClosed_le hfc continuous_const).preimage e.continuous)
    (fun j ↦ ⟨e.symm.continuous.comp_continuousOn (hprops (σ j)).1,
      e.symm.injective.comp_injOn (hprops (σ j)).2.1, fun z hz ↦ by
        change e (e.symm (χ (σ j) z)) ∈ sublevel f (c - ε) ↔ _
        rw [e.apply_symm_apply]
        exact (hprops (σ j)).2.2.1 z hz⟩)
    (fun j j' hjj' ↦ by
      dsimp only
      rw [himage, himage]
      exact ((hdisj (σ.injective.ne hjj')).preimage e))
    (preimage_mono (sublevel_mono f (by linarith)))
    (by
      rw [← hunion]
      exact preimage_mono (union_subset (sublevel_mono f (by linarith))
        (iUnion_subset fun p ↦ (hprops p).2.2.2)))
    (preimage_mono (sublevel_mono f (by linarith)))
    (hsdr₁.preimage_subtype e) (by rw [← hunion]; exact hsdr.preimage_subtype e)
    (hsdr₂.preimage_subtype e)
    (preimage_mono (sublevel_mono f (ha'.trans ha).le)) i
  refine ⟨hcells.1, hcells.2.trans ?_⟩
  rw [card_filter_equiv σ (fun p : S ↦ indexM Z f p = i), Finset.card_filter, Finset.card_filter,
    ← Finset.sum_attach S]
  rfl

/-- **The homology of a slab between two regular values** (Milnor p. 29).  Let `P` be the
(finite) set of critical points of `f = F|N`, and `a' ≤ a` regular values such that all critical
values in `(a', a)` are equal.  Then `H_i(N^a, N^{a'}; 𝕜)` is finite-dimensional, of dimension the
number of critical points of index `i` in `f⁻¹(a', a)`.  With no critical value in `(a', a)` this
is Theorem 3.1 (`N^{a'}` is a strong deformation retract of `N^a`, so the group is `0`). -/
theorem sublevel_step (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (e : T ≃ₜ N) {P : Finset N}
    (hP : letI := hN.chartedSpace; ∀ q, q ∈ P ↔ IsCriticalPointM Z (F ∘ Subtype.val) q)
    {a' a : ℝ} (haa : a' ≤ a) (ha' : ∀ q ∈ P, F q ≠ a') (ha : ∀ q ∈ P, F q ≠ a)
    (hone : ∀ q ∈ P, ∀ q' ∈ P, a' < F q → F q < a → a' < F q' → F q' < a → F q = F q')
    (i : ℕ) :
    letI := hN.chartedSpace
    FiniteDimensional 𝕜 (subsetHomology 𝕜 i (preimage_mono (f := e)
        (sublevel_mono (F ∘ Subtype.val : N → ℝ) haa))) ∧
      finrank 𝕜 (subsetHomology 𝕜 i (preimage_mono (f := e)
        (sublevel_mono (F ∘ Subtype.val : N → ℝ) haa))) =
        #(P.filter fun p : N ↦ (a' < F p ∧ F p < a) ∧ indexM Z (F ∘ Subtype.val) p = i) := by
  classical
  let _ := hN.chartedSpace
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  by_cases hex : ∃ q ∈ P, a' < F q ∧ F q < a
  · -- one critical level `c` in `(a', a)`: Remark 3.3
    obtain ⟨q₀, hq₀P, hq₀a', hq₀a⟩ := hex
    set c := F q₀ with hc_def
    set S := P.filter (fun p : N ↦ F p = c) with hS_def
    have hS : ∀ p ∈ S, IsNondegenerateCriticalPointM Z f p ∧ F p = c := by
      intro p hp
      obtain ⟨hpP, hpc⟩ := Finset.mem_filter.1 hp
      exact ⟨⟨(hP p).1 hpP, hnd p ((hP p).1 hpP)⟩, hpc⟩
    have hother : ∀ q : N, IsCriticalPointM Z f q → q ∉ S → F q < a' ∨ a < F q := by
      intro q hq hqS
      have hqP := (hP q).2 hq
      by_contra hcon
      push Not at hcon
      have h1 : a' < F q := lt_of_le_of_ne hcon.1 (ha' q hqP).symm
      have h2 : F q < a := lt_of_le_of_ne hcon.2 (ha q hqP)
      exact hqS (Finset.mem_filter.2 ⟨hqP, hone q hqP q₀ hq₀P h1 h2 hq₀a' hq₀a⟩)
    obtain ⟨hfd, hfr⟩ := sublevel_step_critical (𝕜 := 𝕜) hN hNc hF e hS hq₀a' hq₀a hother i
    refine ⟨hfd, hfr.trans (congrArg Finset.card ?_)⟩
    ext p
    simp only [hS_def, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpP, hpc⟩, hpi⟩
      exact ⟨hpP, ⟨hpc ▸ hq₀a', hpc ▸ hq₀a⟩, hpi⟩
    · rintro ⟨hpP, ⟨h1, h2⟩, hpi⟩
      exact ⟨⟨hpP, hone p hpP q₀ hq₀P h1 h2 hq₀a' hq₀a⟩, hpi⟩
  · -- no critical value in `[a', a]`: Theorem 3.1
    push Not at hex
    have hcrit : ∀ q : N, F q ∈ Icc a' a → ¬IsCriticalPointM Z f q := by
      intro q hq hc
      have hqP := (hP q).2 hc
      exact absurd (lt_of_le_of_ne hq.2 (ha q hqP))
        (not_lt.2 (hex q hqP (lt_of_le_of_ne hq.1 (ha' q hqP).symm)))
    have hsdr := ((theorem_3_1_submanifold_of_isCompact hN hNc hF haa hcrit).2.1).preimage_subtype e
    have hsub := subsingleton_subsetHomology_of_isSDR (𝕜 := 𝕜)
      (preimage_mono (f := e) (sublevel_mono f haa)) hsdr i
    refine ⟨inferInstance, ?_⟩
    rw [finrank_zero_of_subsingleton, eq_comm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro p hp ⟨⟨h1, h2⟩, -⟩
    exact absurd h2 (not_lt.2 (hex p hp h1))

/-- **The Morse filtration of a compact submanifold** (Milnor p. 29).  For `f = F|N` with
non-degenerate critical points there are `n > 0` and regular values `a_0 ≤ a_1 ≤ ⋯` with
`N^{a_0} = ∅`, `N^{a_n} = N`, at most one critical value in each `(a_k, a_{k+1})`, and
`dim H_i(N^{a_{k+1}}, N^{a_k}; 𝕜)` (finite) the number of critical points of index `i` in
`f⁻¹(a_k, a_{k+1})`.  (The homology is read in a space `T` homeomorphic to `N`, through `e`.) -/
theorem exists_morse_filtration (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (e : T ≃ₜ N) :
    letI := hN.chartedSpace
    ∃ (n : ℕ) (a : ℕ → ℝ) (ha : Monotone a), 0 < n ∧
      sublevel (F ∘ Subtype.val : N → ℝ) (a 0) = ∅ ∧
      sublevel (F ∘ Subtype.val : N → ℝ) (a n) = univ ∧
      (∀ k (q : N), IsCriticalPointM Z (F ∘ Subtype.val) q → F q ≠ a k) ∧
      (∀ k (q q' : N), IsCriticalPointM Z (F ∘ Subtype.val) q →
        IsCriticalPointM Z (F ∘ Subtype.val) q' → a k < F q → F q < a (k + 1) → a k < F q' →
        F q' < a (k + 1) → F q = F q') ∧
      ∀ k i, FiniteDimensional 𝕜 (subsetHomology 𝕜 i (preimage_mono (f := e)
          (sublevel_mono (F ∘ Subtype.val : N → ℝ) (ha (Nat.le_succ k))))) ∧
        finrank 𝕜 (subsetHomology 𝕜 i (preimage_mono (f := e)
          (sublevel_mono (F ∘ Subtype.val : N → ℝ) (ha (Nat.le_succ k))))) =
          {q : N | IsCriticalPointM Z (F ∘ Subtype.val) q ∧ (a k < F q ∧ F q < a (k + 1)) ∧
            indexM Z (F ∘ Subtype.val) q = i}.ncard := by
  classical
  let _ := hN.chartedSpace
  have := hN.isManifold
  have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfc : Continuous f := hF.continuous.comp continuous_subtype_val
  have hfin := (IsMorseFunction.mk (contMDiff_comp_val hN hF) hnd).finite_setOf_isCriticalPointM
  set P := hfin.toFinset with hP_def
  have hP : ∀ q, q ∈ P ↔ IsCriticalPointM Z f q := fun q ↦ hfin.mem_toFinset
  set cv := P.image (fun q : N ↦ F q) with hcv
  have hcvP : ∀ q ∈ P, F q ∈ cv := fun q hq ↦ Finset.mem_image_of_mem (fun q : N ↦ F q) hq
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ c ∈ cv, L < c := ⟨-(∑ c ∈ cv, |c|) - 1, fun c hc ↦ by
    have h1 := Finset.single_le_sum (f := fun c ↦ |c|) (fun _ _ ↦ abs_nonneg _) hc
    have h2 := neg_abs_le c
    linarith⟩
  obtain ⟨n, a, hn, hmono, -, hin, hne, hsep⟩ := exists_separating_seq cv L hL
  have hsep' : ∀ k (q q' : N), q ∈ P → q' ∈ P → a k < F q → F q < a (k + 1) → a k < F q' →
      F q' < a (k + 1) → F q = F q' := by
    intro k q q' hq hq' h1 h2 h3 h4
    rcases lt_or_ge k n with hk | hk
    · exact hsep k hk _ (hcvP q hq) _ (hcvP q' hq') h1 h2 h3 h4
    · linarith [(hin _ (hcvP q hq)).2, hmono hk]
  refine ⟨n, a, hmono, hn, ?_, ?_, fun k q hq ↦ (hne _ (hcvP q ((hP q).2 hq)) k).symm,
    fun k q q' hq hq' ↦ hsep' k q q' ((hP q).2 hq) ((hP q').2 hq'), fun k i ↦ ?_⟩
  · -- `N^{a_0}` is empty: the minimum of `f` is a critical value
    ext q
    simp only [mem_sublevel, mem_empty_iff_false, iff_false, not_le]
    obtain ⟨q₀, -, hq₀⟩ := isCompact_univ.exists_isMinOn ⟨q, Set.mem_univ q⟩ hfc.continuousOn
    have hc : IsCriticalPointM Z f q₀ := isCriticalPointM_of_forall_le fun x ↦ hq₀ (Set.mem_univ x)
    exact (hin _ (hcvP q₀ ((hP q₀).2 hc))).1.trans_le (hq₀ (Set.mem_univ q))
  · -- `N^{a_n} = N`: the maximum of `f` is a critical value
    ext q
    simp only [mem_sublevel, Set.mem_univ, iff_true]
    obtain ⟨q₀, -, hq₀⟩ := isCompact_univ.exists_isMaxOn ⟨q, Set.mem_univ q⟩ hfc.continuousOn
    have hc : IsCriticalPointM Z f q₀ := isCriticalPointM_of_forall_ge fun x ↦ hq₀ (Set.mem_univ x)
    exact (hq₀ (Set.mem_univ q)).trans (hin _ (hcvP q₀ ((hP q₀).2 hc))).2.le
  · obtain ⟨hfd, hfr⟩ := sublevel_step (𝕜 := 𝕜) hN hNc hF hnd e hP (hmono (Nat.le_succ k))
      (fun q hq ↦ (hne _ (hcvP q hq) k).symm) (fun q hq ↦ (hne _ (hcvP q hq) (k + 1)).symm)
      (fun q hq q' hq' ↦ hsep' k q q' hq hq') i
    refine ⟨hfd, hfr.trans ?_⟩
    rw [← Set.ncard_coe_finset]
    congr 1
    ext q
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, hP]
    exact Iff.rfl

/-- The Morse filtration in the form used by `Morse/Homology/TripleFiltration.lean`: a monotone
sequence `X` of subsets of `T` with `X 0 = ∅` and `X n = T`, the finite set `P` of critical
points, and the step `step p < n` containing each of them, such that
`dim H_i(X_{k+1}, X_k; 𝕜) = #{p ∈ P | step p = k ∧ index p = i}`. -/
theorem exists_cells_filtration (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (e : T ≃ₜ N) :
    letI := hN.chartedSpace
    ∃ (n : ℕ) (X : ℕ → Set T) (hX : Monotone X) (P : Finset N) (step : N → ℕ), 0 < n ∧
      X 0 = ∅ ∧ X n = univ ∧ (∀ q, q ∈ P ↔ IsCriticalPointM Z (F ∘ Subtype.val) q) ∧
      (∀ k < n, ∀ i, FiniteDimensional 𝕜 (subsetHomology 𝕜 i (hX (Nat.le_succ k)))) ∧
      (∀ p ∈ P, step p < n) ∧
      ∀ k < n, ∀ i, finrank 𝕜 (subsetHomology 𝕜 i (hX (Nat.le_succ k))) =
        #{p ∈ P | step p = k ∧ indexM Z (F ∘ Subtype.val) p = i} := by
  classical
  let _ := hN.chartedSpace
  have := hN.isManifold
  have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  obtain ⟨n, a, ha, hn, h0, htop, hreg, -, hsteps⟩ :=
    exists_morse_filtration (𝕜 := 𝕜) hN hNc hF hnd e
  have hfin := (IsMorseFunction.mk (contMDiff_comp_val hN hF) hnd).finite_setOf_isCriticalPointM
  set P := hfin.toFinset with hP_def
  have hP : ∀ q, q ∈ P ↔ IsCriticalPointM Z f q := fun q ↦ hfin.mem_toFinset
  have hex : ∀ p ∈ P, ∃ k < n, a k < F p ∧ F p < a (k + 1) := by
    intro p hp
    have hc := (hP p).1 hp
    refine exists_mem_Ioo_of_lt ?_ ?_ fun k ↦ (hreg k p hc).symm
    · by_contra h
      have : p ∈ sublevel f (a 0) := not_lt.1 h
      rw [h0] at this
      exact this
    · exact lt_of_le_of_ne (show p ∈ sublevel f (a n) from htop ▸ Set.mem_univ p) (hreg n p hc)
  choose! step hstep hstepmem using hex
  refine ⟨n, fun k ↦ e ⁻¹' sublevel f (a k), fun i j h ↦ preimage_mono (sublevel_mono f (ha h)),
    P, step, hn, by dsimp only; rw [hf_def, h0, Set.preimage_empty],
    by dsimp only; rw [hf_def, htop, Set.preimage_univ], hP,
    fun k _ i ↦ (hsteps k i).1, hstep, fun k _ i ↦ (hsteps k i).2.trans ?_⟩
  rw [← Set.ncard_coe_finset]
  congr 1
  ext q
  simp only [Finset.coe_filter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hq, hslab, hi⟩
    have hqP := (hP q).2 hq
    exact ⟨hqP, eq_of_mem_Ioo_of_monotone ha (hstepmem q hqP) hslab, hi⟩
  · rintro ⟨hqP, rfl, hi⟩
    exact ⟨(hP q).1 hqP, hstepmem q hqP, hi⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] in
/-- `C_i` counts the critical points of index `i` in any finset of all the critical points. -/
theorem critCount_eq_card {P : Finset N} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    {f : N → ℝ} (hP : letI := hN.chartedSpace; ∀ q, q ∈ P ↔ IsCriticalPointM Z f q) (i : ℕ) :
    letI := hN.chartedSpace
    critCount Z f i = #{p ∈ P | indexM Z f p = i} := by
  classical
  let _ := hN.chartedSpace
  rw [critCount, ← Set.ncard_coe_finset]
  congr 1
  ext q
  simp only [Finset.coe_filter, Set.mem_ofPred_eq, hP]

/-- **The homology of a compact submanifold is finite-dimensional** (Milnor pp. 28–29, where
`R_λ(M)` is used as a number): the steps of the Morse filtration have finite-dimensional
homology, and finiteness propagates along the exact sequences of the triples. -/
theorem finiteDimensional_spaceHomology (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (e : T ≃ₜ N) (i : ℕ) :
    FiniteDimensional 𝕜 (spaceHomology 𝕜 i T) := by
  obtain ⟨n, X, hX, P, step, hn, h0, htop, hP, hfin, hstep, hcells⟩ :=
    exists_cells_filtration (𝕜 := 𝕜) hN hNc hF hnd e
  have := finiteDimensional_subsetHomology_of_steps 𝕜 hX hfin i
  exact finiteDimensional_spaceHomology_of_subsetHomology (hX (Nat.zero_le n)) h0 htop i

/-- **Theorem 5.2 (2), the weak Morse inequalities** (Milnor p. 29): `b_λ ≤ C_λ`, where
`b_λ = dim H_λ(N; 𝕜)` and `C_λ` is the number of critical points of `f = F|N` of index `λ`. -/
theorem bettiNumber_le_critCount (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (e : T ≃ₜ N) (l : ℕ) :
    letI := hN.chartedSpace
    bettiNumber 𝕜 T l ≤ critCount Z (F ∘ Subtype.val : N → ℝ) l := by
  let _ := hN.chartedSpace
  obtain ⟨n, X, hX, P, step, hn, h0, htop, hP, hfin, hstep, hcells⟩ :=
    exists_cells_filtration (𝕜 := 𝕜) hN hNc hF hnd e
  rw [← finrank_subsetHomology_eq_bettiNumber (hX (Nat.zero_le n)) h0 htop, critCount_eq_card hN hP]
  exact singular_weak_morse_inequality_of_cells 𝕜 hX hfin hn hstep hcells l

/-- **The Morse inequalities `(4_λ)`** (Milnor p. 30):
`b_λ - b_{λ-1} + ⋯ ± b_0 ≤ C_λ - C_{λ-1} + ⋯ ± C_0`. -/
theorem altSum_bettiNumber_le (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (e : T ≃ₜ N) (l : ℕ) :
    letI := hN.chartedSpace
    altSum (fun i ↦ (bettiNumber 𝕜 T i : ℤ)) l ≤
      altSum (fun i ↦ (critCount Z (F ∘ Subtype.val : N → ℝ) i : ℤ)) l := by
  let _ := hN.chartedSpace
  obtain ⟨n, X, hX, P, step, hn, h0, htop, hP, hfin, hstep, hcells⟩ :=
    exists_cells_filtration (𝕜 := 𝕜) hN hNc hF hnd e
  simp only [← finrank_subsetHomology_eq_bettiNumber (hX (Nat.zero_le n)) h0 htop,
    critCount_eq_card hN hP]
  exact singular_morse_inequality_of_cells 𝕜 hX hfin hn hstep hcells l

/-- **Theorem 5.2 (3)** (Milnor p. 29): `Σ_{i ≤ n} (-1)^i b_i = Σ_{λ ≤ n} (-1)^λ C_λ`,
`n = dim N`.  (The left side is the whole Euler characteristic of `N`:
`Morse.Homology.bettiNumber_eq_zero_of_finrank_lt`.) -/
theorem sum_bettiNumber_eq_sum_critCount (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (e : T ≃ₜ N) :
    letI := hN.chartedSpace
    ∑ i ∈ range (finrank ℝ Z + 1), (-1 : ℤ) ^ i * (bettiNumber 𝕜 T i : ℤ) =
      ∑ i ∈ range (finrank ℝ Z + 1),
        (-1 : ℤ) ^ i * (critCount Z (F ∘ Subtype.val : N → ℝ) i : ℤ) := by
  let _ := hN.chartedSpace
  obtain ⟨n, X, hX, P, step, hn, h0, htop, hP, hfin, hstep, hcells⟩ :=
    exists_cells_filtration (𝕜 := 𝕜) hN hNc hF hnd e
  have hvan : ∀ k < n,
      finrank 𝕜 (subsetHomology 𝕜 (finrank ℝ Z + 1) (hX (Nat.le_succ k))) = 0 := by
    intro k hk
    rw [hcells k hk, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro p - ⟨-, hi⟩
    have := indexM_le_finrank (E := Z) (F ∘ Subtype.val) p
    omega
  have h := singular_euler_characteristic 𝕜 hX hfin hn hvan
  simp only [singularMorseNumber_eq_card 𝕜 hX hstep hcells,
    finrank_subsetHomology_eq_bettiNumber (hX (Nat.zero_le n)) h0 htop] at h
  simp only [critCount_eq_card hN hP]
  exact h

/-- **No homology above the dimension**: `H_i(N; 𝕜) = 0` for `i > dim N`, by (2), every index
being at most `dim N` (used implicitly by Milnor on p. 30, in "`λ > n`"). -/
theorem bettiNumber_eq_zero_of_finrank_lt (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (e : T ≃ₜ N) {i : ℕ}
    (hi : finrank ℝ Z < i) : bettiNumber 𝕜 T i = 0 := by
  let _ := hN.chartedSpace
  have h := bettiNumber_le_critCount (𝕜 := 𝕜) hN hNc hF hnd e i
  have hempty : {p : N | IsCriticalPointM Z (F ∘ Subtype.val) p ∧
      indexM Z (F ∘ Subtype.val) p = i} = ∅ :=
    Set.eq_empty_of_forall_notMem fun p hp ↦
      absurd (indexM_le_finrank (E := Z) (F ∘ Subtype.val) p) (by have := hp.2; omega)
  have h0 : critCount Z (F ∘ Subtype.val : N → ℝ) i = 0 := by
    unfold critCount
    rw [hempty, Set.ncard_empty]
  omega

/-- `H_i(N; 𝕜) = 0` for `i > dim N`. -/
theorem subsingleton_spaceHomology_of_finrank_lt (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (e : T ≃ₜ N) {i : ℕ}
    (hi : finrank ℝ Z < i) : Subsingleton (spaceHomology 𝕜 i T) := by
  have := finiteDimensional_spaceHomology (𝕜 := 𝕜) hN hNc hF hnd e i
  exact Module.finrank_zero_iff.1 (bettiNumber_eq_zero_of_finrank_lt hN hNc hF hnd e hi)

/-- **Corollary 5.4** (Milnor p. 31), for `λ = l + 1 ≥ 1`: if `C_{λ+1} = C_{λ-1} = 0`, then
`b_λ = C_λ` and `b_{λ+1} = b_{λ-1} = 0`. -/
theorem bettiNumber_eq_critCount_of_succ (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (e : T ≃ₜ N) {l : ℕ}
    (h₂ : letI := hN.chartedSpace; critCount Z (F ∘ Subtype.val : N → ℝ) (l + 2) = 0)
    (h₀ : letI := hN.chartedSpace; critCount Z (F ∘ Subtype.val : N → ℝ) l = 0) :
    letI := hN.chartedSpace
    bettiNumber 𝕜 T (l + 1) = critCount Z (F ∘ Subtype.val : N → ℝ) (l + 1) ∧
      bettiNumber 𝕜 T (l + 2) = 0 ∧ bettiNumber 𝕜 T l = 0 := by
  let _ := hN.chartedSpace
  have := eq_of_altSum_le_succ (b := fun i ↦ (bettiNumber 𝕜 T i : ℤ))
    (c := fun i ↦ (critCount Z (F ∘ Subtype.val : N → ℝ) i : ℤ)) (fun _ ↦ Nat.cast_nonneg _)
    (altSum_bettiNumber_le hN hNc hF hnd e) (l := l) (by simp [h₂]) (by simp [h₀])
  exact_mod_cast this

/-- **Corollary 5.4** (Milnor p. 31), for `λ = 0`, where `C_{λ-1}` is read as `0`: if
`C_1 = 0`, then `b_0 = C_0` and `b_1 = 0`. -/
theorem bettiNumber_eq_critCount_of_zero (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (e : T ≃ₜ N)
    (h₁ : letI := hN.chartedSpace; critCount Z (F ∘ Subtype.val : N → ℝ) 1 = 0) :
    letI := hN.chartedSpace
    bettiNumber 𝕜 T 0 = critCount Z (F ∘ Subtype.val : N → ℝ) 0 ∧ bettiNumber 𝕜 T 1 = 0 := by
  let _ := hN.chartedSpace
  have := eq_of_altSum_le_zero (b := fun i ↦ (bettiNumber 𝕜 T i : ℤ))
    (c := fun i ↦ (critCount Z (F ∘ Subtype.val : N → ℝ) i : ℤ)) (fun _ ↦ Nat.cast_nonneg _)
    (altSum_bettiNumber_le hN hNc hF hnd e) (by simp [h₁])
  exact_mod_cast this

/-- **The lacunary principle** (Milnor p. 31, the remark on `ℂPⁿ`): if no two consecutive Morse
numbers `C_i, C_{i+1}` are both nonzero, then `b_i = C_i` for every `i`. -/
theorem bettiNumber_eq_critCount_of_lacunary (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (e : T ≃ₜ N)
    (hc : letI := hN.chartedSpace; ∀ i, critCount Z (F ∘ Subtype.val : N → ℝ) i = 0 ∨
      critCount Z (F ∘ Subtype.val : N → ℝ) (i + 1) = 0) (i : ℕ) :
    letI := hN.chartedSpace
    bettiNumber 𝕜 T i = critCount Z (F ∘ Subtype.val : N → ℝ) i := by
  let _ := hN.chartedSpace
  have := eq_of_altSum_le_of_lacunary (b := fun i ↦ (bettiNumber 𝕜 T i : ℤ))
    (c := fun i ↦ (critCount Z (F ∘ Subtype.val : N → ℝ) i : ℤ)) (fun _ ↦ Nat.cast_nonneg _)
    (altSum_bettiNumber_le hN hNc hF hnd e) (fun i ↦ by exact_mod_cast hc i) i
  exact_mod_cast this


/-! ### The statements for `N` itself -/

variable {𝕜' : Type v} [Field 𝕜']

/-- **The Morse filtration of a compact submanifold `N`** (Milnor p. 29): for `f = F|N` with
non-degenerate critical points there are regular values `a_0 ≤ a_1 ≤ ⋯`, `n > 0`, with
`∅ = N^{a_0} ⊆ N^{a_1} ⊆ ⋯ ⊆ N^{a_n} = N`, at most one critical value in each
`(a_k, a_{k+1})`, and `H_i(N^{a_{k+1}}, N^{a_k}; 𝕜)` finite-dimensional, of dimension the number
of critical points of index `i` in `f⁻¹(a_k, a_{k+1})`, for every field `𝕜`. -/
theorem exists_morse_filtration' (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) :
    letI := hN.chartedSpace
    ∃ (n : ℕ) (a : ℕ → ℝ) (ha : Monotone a), 0 < n ∧
      sublevel (F ∘ Subtype.val : N → ℝ) (a 0) = ∅ ∧
      sublevel (F ∘ Subtype.val : N → ℝ) (a n) = univ ∧
      (∀ k (q : N), IsCriticalPointM Z (F ∘ Subtype.val) q → F q ≠ a k) ∧
      (∀ k (q q' : N), IsCriticalPointM Z (F ∘ Subtype.val) q →
        IsCriticalPointM Z (F ∘ Subtype.val) q' → a k < F q → F q < a (k + 1) → a k < F q' →
        F q' < a (k + 1) → F q = F q') ∧
      ∀ k i, FiniteDimensional 𝕜' (subsetHomology 𝕜' i
          (sublevel_mono (F ∘ Subtype.val : N → ℝ) (ha (Nat.le_succ k)))) ∧
        finrank 𝕜' (subsetHomology 𝕜' i
          (sublevel_mono (F ∘ Subtype.val : N → ℝ) (ha (Nat.le_succ k)))) =
          {q : N | IsCriticalPointM Z (F ∘ Subtype.val) q ∧ (a k < F q ∧ F q < a (k + 1)) ∧
            indexM Z (F ∘ Subtype.val) q = i}.ncard :=
  exists_morse_filtration hN hNc hF hnd (Homeomorph.refl N)

/-- **Theorem 5.2 (2) for a compact submanifold `N`** (Milnor p. 29): for `f = F|N` with
non-degenerate critical points and every field `𝕜`, `dim H_λ(N; 𝕜) ≤ C_λ`. -/
theorem bettiNumber_le_critCount' (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (l : ℕ) :
    letI := hN.chartedSpace
    bettiNumber 𝕜' N l ≤ critCount Z (F ∘ Subtype.val : N → ℝ) l :=
  bettiNumber_le_critCount hN hNc hF hnd (Homeomorph.refl N) l

/-- **The Morse inequalities `(4_λ)` for a compact submanifold `N`** (Milnor p. 30). -/
theorem altSum_bettiNumber_le' (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (l : ℕ) :
    letI := hN.chartedSpace
    altSum (fun i ↦ (bettiNumber 𝕜' N i : ℤ)) l ≤
      altSum (fun i ↦ (critCount Z (F ∘ Subtype.val : N → ℝ) i : ℤ)) l :=
  altSum_bettiNumber_le hN hNc hF hnd (Homeomorph.refl N) l

/-- **Theorem 5.2 (3) for a compact submanifold `N`** (Milnor p. 29):
`Σ_{i ≤ n} (-1)^i dim H_i(N; 𝕜) = Σ_{λ ≤ n} (-1)^λ C_λ`, `n = dim N`. -/
theorem sum_bettiNumber_eq_sum_critCount' (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) :
    letI := hN.chartedSpace
    ∑ i ∈ range (finrank ℝ Z + 1), (-1 : ℤ) ^ i * (bettiNumber 𝕜' N i : ℤ) =
      ∑ i ∈ range (finrank ℝ Z + 1),
        (-1 : ℤ) ^ i * (critCount Z (F ∘ Subtype.val : N → ℝ) i : ℤ) :=
  sum_bettiNumber_eq_sum_critCount hN hNc hF hnd (Homeomorph.refl N)

end Submanifold

end Morse.Homology
