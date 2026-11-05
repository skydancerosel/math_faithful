import Morse.Chapter2.CWType

/-!
Milnor, *Morse Theory*, §3, p. 20 (Theorem 3.5) and the Remark on p. 24, for a compact sublevel
set of a submanifold of Euclidean space that need not be compact; with an extension lemma for
functions which are smooth in Milnor's sense on a subset of Euclidean space.

# One cell for each critical point in a compact sublevel set

Milnor proves Theorem 16.3 by "16.2 together with §3.5" (p. 90).  The manifold `B` of broken
geodesics is not compact, only its sublevel sets `B^a`, `a < c`, are; and Part I's Theorem 3.5
(`Morse.theorem_3_5'`) is formalized for a compact submanifold, with the function the restriction
of a smooth function on the ambient space.  This file supplies the two missing pieces.

* `Morse.isFiniteCellComplexType_sublevel_of_isCompact`: **Theorem 3.5 for a compact sublevel
  set** (the Remark on p. 24, for a regular value `a`): let `N ⊆ V` be a slice submanifold,
  `F : V → ℝ` smooth, `f = F|N`, and `a` a regular value of `f` such that `N^a = f⁻¹(−∞, a]` is
  compact and every critical point of `f` in `N^a` is non-degenerate.  Then `N^a` has the
  homotopy type of an iterated adjunction space (`Morse.IsFiniteCellComplexType`) with one cell
  of dimension `λ` for each critical point of index `λ` in `N^a`.  The proof is Milnor's
  induction over the critical values (`Morse.isFiniteCellComplexType_sublevel'`), all slabs being
  closed subsets of the compact `N^a`; no assumption is made on the critical points above `a`.
* `Morse.exists_contDiff_eq_of_locally`: **a function which near every point of a compact `K` is
  the restriction to `S ⊇ K` of a smooth function agrees on `K` with a smooth function on `V`**
  (a smooth partition of unity subordinate to a finite cover).

## What Milnor leaves implicit

* Theorem 3.5 is stated for functions all of whose sublevel sets are compact, with no degenerate
  critical points at all.  For 16.3 only the critical points in `B^a` matter: the cells are
  attached by Theorems 3.1 and 3.2 (with Remark 3.3) on slabs inside `B^a`.  The exposition
  instead reparametrizes `E'` on `{E' < a'}` for a level `a' > a` without critical values in
  `(a, a']`; the version here makes that step unnecessary.
-/

open Set Filter Topology Function Module CategoryTheory Limits TopCat
open scoped ContDiff Manifold

universe u

noncomputable section

namespace Morse

/-! ### Smooth extension from a compact set -/

section Extension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Smooth extension from a compact set**: if every point of the compact set `K ⊆ S` has an open
neighbourhood `O` on which `f|S` is the restriction of a function `G` smooth on `O`, then some
smooth `F : E → ℝ` agrees with `f` on `K`. -/
theorem exists_contDiff_eq_of_locally {K S : Set E} (hK : IsCompact K) (hKS : K ⊆ S)
    {f : E → ℝ} (hloc : ∀ x ∈ K, ∃ O : Set E, IsOpen O ∧ x ∈ O ∧ ∃ G : E → ℝ,
      ContDiffOn ℝ ∞ G O ∧ ∀ y ∈ S ∩ O, f y = G y) :
    ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧ ∀ y ∈ K, F y = f y := by
  classical
  choose! O hO hxO G hG hfG using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => O x) (fun x => hO x x.2)
    fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxO x hx⟩
  obtain ⟨φ, hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) hK.isClosed
    (fun i : t => O (i : K)) (fun i => hO _ (i : K).2) fun x hx => by
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  have hφs : ∀ i : t, ContDiff ℝ ∞ (φ i) := fun i =>
    contMDiff_iff_contDiff.1 (φ i).contMDiff
  refine ⟨fun x => ∑ i : t, φ i x • G (i : K) x, ?_, fun y hy => ?_⟩
  · exact ContDiff.sum fun i _ => contDiff_smul_of_tsupport (hO _ (i : K).2) (hφs i)
      (hG _ (i : K).2) (hφ i)
  · have hsum := φ.sum_eq_one hy
    rw [finsum_eq_sum_of_fintype] at hsum
    have hterm : ∀ i : t, φ i y • G (i : K) y = φ i y • f y := by
      intro i
      by_cases h0 : φ i y = 0
      · simp [h0]
      · have hyO : y ∈ O (i : K) := hφ i (subset_tsupport _ h0)
        rw [hfG _ (i : K).2 y ⟨hKS hy, hyO⟩]
    simp only [hterm, ← Finset.sum_smul, hsum, one_smul]

end Extension

/-! ### Theorem 3.5 for a compact sublevel set -/

section Sublevel

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V}

/-- **Passing one critical level inside a compact sublevel set** (Milnor, p. 23, with Remark 3.3):
as `Morse.IsFiniteCellComplexType.sublevel_step_finset`, for a non-compact `N`, the slabs being
closed subsets of a compact sublevel set `N^{a₀}`, `a ≤ a₀`. -/
theorem IsFiniteCellComplexType.sublevel_step_of_isCompact
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F) {a₀ : ℝ}
    (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Iic a₀)) {S : Finset N} {c : ℝ}
    (hS : letI := hN.chartedSpace;
      ∀ p ∈ S, IsNondegenerateCriticalPointM Z (F ∘ Subtype.val) p ∧ F p = c)
    {a' a : ℝ} (ha' : a' < c) (ha : c < a) (haa₀ : a ≤ a₀)
    (hother : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q → q ∉ S →
      F q < a' ∨ a < F q)
    {cells : List ℕ} (h : IsFiniteCellComplexType (sublevel (F ∘ Subtype.val : N → ℝ) a') cells) :
    letI := hN.chartedSpace
    ∃ l : List N, l.Nodup ∧ (∀ q, q ∈ l ↔ q ∈ S) ∧
      IsFiniteCellComplexType (sublevel (F ∘ Subtype.val : N → ℝ) a)
        (cells ++ l.map (indexM Z (F ∘ Subtype.val))) := by
  classical
  let _ := hN.chartedSpace
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfc : Continuous f := hF.continuous.comp continuous_subtype_val
  -- every slab below `a₀` is compact
  have hslab : ∀ b b' : ℝ, b' ≤ a₀ → IsCompact (f ⁻¹' Icc b b') := fun b b' hb' =>
    hK.of_isClosed_subset (isClosed_Icc.preimage hfc) fun q hq => (hq.2.trans hb' : f q ≤ a₀)
  set ε₀ := min (c - a') (a - c) with hε₀_def
  have hε₀ : 0 < ε₀ := lt_min (by linarith) (by linarith)
  have hKε : IsCompact (f ⁻¹' Icc (c - ε₀) (c + ε₀)) :=
    hslab _ _ (by linarith [min_le_right (c - a') (a - c)])
  have honly : ∀ q : N, F q ∈ Icc (c - ε₀) (c + ε₀) → IsCriticalPointM Z f q → q ∈ S := by
    intro q hq hc
    by_contra hqS
    rcases hother q hc hqS with h1 | h1
    · linarith [hq.1, min_le_left (c - a') (a - c)]
    · linarith [hq.2, min_le_right (c - a') (a - c)]
  obtain ⟨ε₁, hε₁, H⟩ := remark_3_3_submanifold hN hF S hS hε₀ hKε honly
  set ε := min ε₁ (ε₀ / 2) with hε_def
  have hε : 0 < ε := lt_min hε₁ (by linarith)
  have hεε₀ : ε < ε₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h1 : ε < c - a' := lt_of_lt_of_le hεε₀ (min_le_left _ _)
  have h2 : ε < a - c := lt_of_lt_of_le hεε₀ (min_le_right _ _)
  obtain ⟨χ, hprops, hdisj, hsdr⟩ := H ε hε (min_le_left _ _)
  -- no critical values in `[a', c - ε]` and `[c + ε, a]`
  have hno : ∀ {b b' : ℝ}, a' ≤ b → b' ≤ a → (b' < c ∨ c < b) →
      ∀ q : N, F q ∈ Icc b b' → ¬IsCriticalPointM Z f q := by
    intro b b' hb hb' hbp q hq hc
    by_cases hqS : q ∈ S
    · have := (hS q hqS).2
      rcases hbp with h | h <;> linarith [hq.1, hq.2]
    · rcases hother q hc hqS with h | h <;> linarith [hq.1, hq.2]
  obtain ⟨e₂, -⟩ := (theorem_3_1_submanifold hN hF (a := a') (b := c - ε) (by linarith)
    (hslab _ _ (by linarith)) (hno le_rfl (by linarith) (Or.inl (by linarith)))).2.2
  obtain ⟨e₃, -⟩ := (theorem_3_1_submanifold hN hF (a := c + ε) (b := a) (by linarith)
    (hslab _ _ haa₀) (hno (by linarith) le_rfl (Or.inr (by linarith)))).2.2
  have h4 : IsFiniteCellComplexType (sublevel f (c - ε)) cells := h.of_homotopyEquiv e₂.symm
  -- attach the cells one at a time
  set l : List S := Finset.univ.toList with hl_def
  have hlnd : l.Nodup := Finset.nodup_toList _
  have h5 := isFiniteCellComplexType_union_cells χ l (isClosed_le hfc continuous_const) h4
    (fun p _ => ⟨(hprops p).1, (hprops p).2.1, (hprops p).2.2.1⟩)
    (hlnd.pairwise_of_forall_ne fun p _ p' _ hpp' => hdisj hpp')
  have hU : sublevel f (c - ε) ∪ ⋃ p ∈ l, χ p '' Metric.closedBall 0 1 =
      sublevel f (c - ε) ∪ ⋃ p, χ p '' Metric.closedBall 0 1 := by
    simp [hl_def]
  have hsub : sublevel f (c - ε) ∪ ⋃ p, χ p '' Metric.closedBall 0 1 ⊆ sublevel f (c + ε) :=
    union_subset (sublevel_mono f (by linarith)) (iUnion_subset fun p => (hprops p).2.2.2)
  obtain ⟨e₁, -⟩ := hsdr.exists_homotopyEquiv hsub
  refine ⟨l.map Subtype.val, hlnd.map Subtype.val_injective, fun q => ?_, ?_⟩
  · simp only [List.mem_map, hl_def, Finset.mem_toList, Finset.mem_univ, true_and]
    exact ⟨fun ⟨p, hp⟩ => hp ▸ p.2, fun hq => ⟨⟨q, hq⟩, rfl⟩⟩
  · rw [List.map_map]
    refine (h5.of_homotopyEquiv (Homeomorph.setCongr hU).symm.toHomotopyEquiv).of_homotopyEquiv
      (e₃.symm.trans e₁.symm)

/-- **Theorem 3.5 for a compact sublevel set** (Milnor p. 20 and the Remark on p. 24, for a
regular value): let `N ⊆ V` be a slice submanifold, `F : V → ℝ` smooth and `f = F|N`; let `a` be
a regular value of `f` such that `N^a` is compact and every critical point of `f` in `N^a` is
non-degenerate.  Then the critical points of `f` in `N^a` can be listed as `p₁, …, p_j` with
`f(p₁) ≤ ⋯ ≤ f(p_j)`, and `N^a` has the homotopy type of the space obtained from the empty space
by attaching cells of dimensions `index(p₁), …, index(p_j)`, one at a time. -/
theorem isFiniteCellComplexType_sublevel_of_isCompact
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F) {a₀ : ℝ}
    (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Iic a₀))
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q → F q ≤ a₀ →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q))
    (ha₀ : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      F q ≠ a₀) :
    letI := hN.chartedSpace
    ∃ ps : List N, ps.Nodup ∧
      (∀ q, q ∈ ps ↔ IsCriticalPointM Z (F ∘ Subtype.val) q ∧ F q < a₀) ∧
      ps.Pairwise (fun q q' : N => F q ≤ F q') ∧
      IsFiniteCellComplexType (sublevel (F ∘ Subtype.val : N → ℝ) a₀)
        (ps.map (indexM Z (F ∘ Subtype.val))) := by
  classical
  let _ := hN.chartedSpace
  have := hN.isManifold
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfc : Continuous f := hF.continuous.comp continuous_subtype_val
  have hfs : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ f := contMDiff_comp_val hN hF
  -- the critical points in `N^{a₀}` form a finite set
  set K := f ⁻¹' Iic a₀ with hK_def
  have hfin : (K ∩ {q | IsCriticalPointM Z f q}).Finite := by
    have hC : IsCompact (K ∩ {x | IsCriticalPointM Z f x}) :=
      hK.inter_right (isClosed_setOf_isCriticalPointM (hfs.of_le (by norm_cast)))
    have hD : IsDiscrete (K ∩ {x | IsCriticalPointM Z f x}) :=
      isDiscrete_inter_setOf_isCriticalPointM (fun x _ => (hfs x).of_le (by norm_cast))
        fun x hx hc => hnd x hc hx
    exact hC.finite hD
  set C := hfin.toFinset with hC_def
  have hmemC : ∀ q, q ∈ C ↔ F q ≤ a₀ ∧ IsCriticalPointM Z f q := fun q => by
    simp only [C, Set.Finite.mem_toFinset, mem_inter_iff, K, mem_preimage, mem_Iic, mem_ofPred_eq]
    rfl
  suffices key : ∀ m : ℕ, ∀ a : ℝ, a ≤ a₀ → (C.filter (fun q : N => F q < a)).card = m →
      (∀ q : N, IsCriticalPointM Z f q → F q ≠ a) →
      ∃ ps : List N, ps.Nodup ∧ (∀ q, q ∈ ps ↔ IsCriticalPointM Z f q ∧ F q < a) ∧
        ps.Pairwise (fun q q' : N => F q ≤ F q') ∧
        IsFiniteCellComplexType (sublevel f a) (ps.map (indexM Z f)) from
    key _ a₀ le_rfl rfl ha₀
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a haa₀ hm ha
  have hcrit_lt : ∀ q, IsCriticalPointM Z f q → F q < a → q ∈ C.filter (fun q : N => F q < a) :=
    fun q hq hqa => Finset.mem_filter.2 ⟨(hmemC q).2 ⟨(hqa.le.trans haa₀), hq⟩, hqa⟩
  by_cases hS : (C.filter (fun q : N => F q < a)).Nonempty
  · obtain ⟨p, hpS, hpmax⟩ := Finset.exists_max_image _ (fun q : N => F q) hS
    set c := F p with hc_def
    have hpa : c < a := (Finset.mem_filter.1 hpS).2
    have hpC := (hmemC p).1 (Finset.mem_filter.1 hpS).1
    set S := C.filter (fun q : N => F q = c) with hS_def
    have hSc : ∀ q ∈ S, IsNondegenerateCriticalPointM Z f q ∧ F q = c := fun q hq => by
      have hqC := (hmemC q).1 (Finset.mem_filter.1 hq).1
      exact ⟨⟨hqC.2, hnd q hqC.2 hqC.1⟩, (Finset.mem_filter.1 hq).2⟩
    -- a regular value `a'` just below `c`
    obtain ⟨a', ha'p, hTa'⟩ : ∃ a', a' < c ∧
        ∀ q ∈ C.filter (fun q : N => F q < c), F q < a' := by
      by_cases hT : (C.filter (fun q : N => F q < c)).Nonempty
      · obtain ⟨q₀, hq₀T, hq₀max⟩ := Finset.exists_max_image _ (fun q : N => F q) hT
        have : F q₀ < c := (Finset.mem_filter.1 hq₀T).2
        exact ⟨(F q₀ + c) / 2, by linarith, fun q hq => by have := hq₀max q hq; linarith⟩
      · exact ⟨c - 1, by linarith, fun q hq => absurd ⟨q, hq⟩ hT⟩
    have hother : ∀ q : N, IsCriticalPointM Z f q → q ∉ S → F q < a' ∨ a < F q := by
      intro q hq hqS
      rcases lt_trichotomy (F q) c with h | h | h
      · exact Or.inl (hTa' q (Finset.mem_filter.2 ⟨(hmemC q).2 ⟨by linarith, hq⟩, h⟩))
      · exact absurd (Finset.mem_filter.2 ⟨(hmemC q).2 ⟨by linarith, hq⟩, h⟩) hqS
      · right
        by_contra hle
        have hqa : F q < a := lt_of_le_of_ne (not_lt.1 hle) (ha q hq)
        have := hpmax q (hcrit_lt q hq hqa)
        linarith
    have ha'reg : ∀ q : N, IsCriticalPointM Z f q → F q ≠ a' := by
      intro q hq heq
      by_cases hqS : q ∈ S
      · have := (hSc q hqS).2
        linarith
      · rcases hother q hq hqS with h | h <;> linarith
    have hfilter : C.filter (fun q : N => F q < a') = (C.filter (fun q : N => F q < a)) \ S := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_sdiff, hS_def, not_and]
      constructor
      · rintro ⟨hq, hqa'⟩
        exact ⟨⟨hq, by linarith⟩, fun _ h => by linarith⟩
      · rintro ⟨⟨hq, hqa⟩, hqS⟩
        refine ⟨hq, ?_⟩
        rcases hother q ((hmemC q).1 hq).2 (fun h => hqS hq (Finset.mem_filter.1 h).2)
          with h | h
        · exact h
        · linarith
    have hpS' : p ∈ S := Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hpS).1, rfl⟩
    have hcard : (C.filter (fun q : N => F q < a')).card < m := by
      rw [hfilter, ← hm]
      exact Finset.card_lt_card (Finset.sdiff_ssubset (fun q hq => Finset.mem_filter.2
        ⟨(Finset.mem_filter.1 hq).1, by rw [(Finset.mem_filter.1 hq).2]; exact hpa⟩)
        ⟨p, hpS'⟩)
    obtain ⟨ps', hnd', hmem', hsort', hcell'⟩ :=
      ih _ hcard a' (by linarith) rfl ha'reg
    obtain ⟨l, hlnd, hlmem, hcell⟩ :=
      IsFiniteCellComplexType.sublevel_step_of_isCompact hN hF hK hSc ha'p hpa haa₀ hother hcell'
    have hlc : ∀ q ∈ l, F q = c := fun q hq => (hSc q ((hlmem q).1 hq)).2
    refine ⟨ps' ++ l, ?_, fun q => ?_, ?_, ?_⟩
    · refine hnd'.append hlnd (List.disjoint_left.2 fun q hq hql => ?_)
      have h1 := ((hmem' q).1 hq).2
      have h2 := hlc q hql
      linarith
    · rw [List.mem_append, hmem', hlmem]
      constructor
      · rintro (⟨hq, hqa'⟩ | hqS)
        · exact ⟨hq, by linarith⟩
        · exact ⟨(hSc q hqS).1.1, by rw [(hSc q hqS).2]; exact hpa⟩
      · rintro ⟨hq, hqa⟩
        by_cases hqS : q ∈ S
        · exact Or.inr hqS
        · refine Or.inl ⟨hq, ?_⟩
          rcases hother q hq hqS with h | h
          · exact h
          · linarith
    · rw [List.pairwise_append]
      refine ⟨hsort', List.pairwise_of_forall_mem_list fun q hq q' hq' =>
        le_of_eq ((hlc q hq).trans (hlc q' hq').symm), fun q hq q' hq' => ?_⟩
      · have h1 := ((hmem' q).1 hq).2
        have h2 := hlc q' hq'
        linarith
    · rw [List.map_append]
      exact hcell
  · -- no critical point below `a`: `N^a` is empty
    have hempty : sublevel f a = ∅ := by
      by_contra hne
      obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.2 hne
      have hKa : IsCompact (sublevel f a) :=
        hK.of_isClosed_subset (isClosed_le hfc continuous_const) fun x hx =>
          (show f x ≤ a₀ from le_trans hx haa₀)
      obtain ⟨q₀, hq₀, hmin⟩ := hKa.exists_isMinOn ⟨q, hq⟩ hfc.continuousOn
      have hglob : ∀ x, f q₀ ≤ f x := fun x => by
        by_cases hx : x ∈ sublevel f a
        · exact hmin hx
        · exact le_trans hq₀ (le_of_lt (not_le.1 hx))
      have hc : IsCriticalPointM Z f q₀ := isCriticalPointM_of_forall_le hglob
      have hq₀a : F q₀ < a := lt_of_le_of_ne hq₀ (ha q₀ hc)
      exact hS ⟨q₀, hcrit_lt q₀ hc hq₀a⟩
    refine ⟨[], List.nodup_nil, fun q => ?_, List.Pairwise.nil, ?_⟩
    · simp only [List.not_mem_nil, false_iff, not_and]
      intro hc hqa
      exact hS ⟨q, hcrit_lt q hc hqa⟩
    · have : IsEmpty (sublevel f a) := Set.isEmpty_coe_sort.2 hempty
      exact IsFiniteCellComplexType.of_isEmpty _

end Sublevel

end Morse
