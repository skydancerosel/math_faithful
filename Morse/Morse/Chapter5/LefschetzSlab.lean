import Morse.Chapter5.Lefschetz

/-!
Milnor, *Morse Theory*, §3, Theorems 3.1, 3.2 and Remark 3.3 (pp. 12–19), §5, p. 29, as used in the
proof of Theorem 7.4 (§7, p. 42); Exposition/Chapter5.md, §5, Lemma 5.1.

# The homology of a compact slab

## Milnor's text, paraphrased

Theorem 3.1 (p. 12) assumes only that `f⁻¹[a, b]` is compact and contains no critical point;
Theorem 3.2 (p. 14) only that `f⁻¹[c − ε, c + ε]` is compact and contains one non-degenerate
critical point.  In the proof of Theorem 7.4 (p. 42) they are applied to `f = 1/L_p` on a
projective variety, whose sublevel sets (neighbourhoods of the hyperplane section) are not compact.

## What is formalized

The project's homology computations for sublevel sets (`Morse/Chapter10/SublevelHomology.lean`,
`Morse/Chapter5/Lefschetz.lean`) assume a compact sublevel set `N^{a₀}`, but use it only through
the compactness of the slabs below `a₀`.  Here are the same statements under the hypothesis that a
slab is compact:

* `Morse.Homology.sublevel_step_critical_of_slab`, `Morse.Homology.sublevel_step_of_slab`: the
  homology of a compact slab `(N^a, N^{a'})` with at most one critical level;
* `Morse.subsingleton_subsetHomology_slab`: `H_j(N^b, N^a; 𝕜) = 0` if the compact slab contains
  no critical point of index `j`.

The proofs are those of the compact-sublevel versions, with the compact slabs `f⁻¹[b, b']` taken
inside the given compact slab.

## What Milnor leaves implicit

That the slab hypothesis of Theorems 3.1 and 3.2 is all that the homology computation of p. 29
needs; it is used without comment in §7.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

universe u v

namespace Morse.Homology

section Submanifold

open Finset

variable {𝕜 : Type u} [Field 𝕜]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} {T : Type u} [TopologicalSpace T]

/-- **One critical level in a compact slab** (Milnor p. 29, with Remark 3.3):
`Morse.Homology.sublevel_step_critical_of_isCompact` when only the slab `f⁻¹[a', a]` is compact
(the sublevel sets themselves may be non-compact, as for `−L_p` on an affine variety).  Let `S` be
a finite set of non-degenerate critical points of `f = F|N`, all on the level `c ∈ (a', a)`, and no
other critical value in `[a', a]`.  Then `H_i(N^a, N^{a'}; 𝕜)` is finite-dimensional, of dimension
the number of points of `S` of index `i`: Milnor's Theorems 3.1, 3.2 and Remark 3.3 only use the
compactness of the slab. -/
theorem sublevel_step_critical_of_slab (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    {F : V → ℝ} (hF : ContDiff ℝ ∞ F) (e : T ≃ₜ N) {S : Finset N} {c : ℝ}
    (hS : letI := hN.chartedSpace;
      ∀ p ∈ S, IsNondegenerateCriticalPointM Z (F ∘ Subtype.val) p ∧ F p = c)
    {a' a : ℝ} (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Icc a' a)) (ha' : a' < c)
    (ha : c < a)
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
  -- `N` is a subspace of a normed space, hence Hausdorff
  have : T2Space T := e.isEmbedding.t2Space
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfc : Continuous f := hF.continuous.comp continuous_subtype_val
  -- every slab inside `[a', a]` is compact
  have hslab : ∀ b b' : ℝ, a' ≤ b → b' ≤ a → IsCompact (f ⁻¹' Icc b b') := fun b b' hb hb' ↦
    hK.of_isClosed_subset (isClosed_Icc.preimage hfc) fun q hq ↦ ⟨hb.trans hq.1, hq.2.trans hb'⟩
  set ε₀ := min (c - a') (a - c) with hε₀_def
  have hε₀ : 0 < ε₀ := lt_min (by linarith) (by linarith)
  have hKε : IsCompact (f ⁻¹' Icc (c - ε₀) (c + ε₀)) :=
    hslab _ _ (by linarith [min_le_left (c - a') (a - c)])
      (by linarith [min_le_right (c - a') (a - c)])
  have honly : ∀ q : N, F q ∈ Icc (c - ε₀) (c + ε₀) → IsCriticalPointM Z f q → q ∈ S := by
    intro q hq hc
    by_contra hqS
    rcases hother q hc hqS with h1 | h1
    · linarith [hq.1, min_le_left (c - a') (a - c)]
    · linarith [hq.2, min_le_right (c - a') (a - c)]
  -- Remark 3.3 at the level `c`
  obtain ⟨ε₁, hε₁, H⟩ := remark_3_3_submanifold hN hF S hS hε₀ hKε honly
  set ε := min ε₁ (ε₀ / 2) with hε_def
  have hε : 0 < ε := lt_min hε₁ (by linarith)
  have hεε₀ : ε < ε₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h1 : ε < c - a' := lt_of_lt_of_le hεε₀ (min_le_left _ _)
  have h2 : ε < a - c := lt_of_lt_of_le hεε₀ (min_le_right _ _)
  obtain ⟨χ, hprops, hdisj, hsdr⟩ := H ε hε (min_le_left _ _)
  -- Theorem 3.1 on the compact slabs `[a', c - ε]` and `[c + ε, a]`
  have hno : ∀ {b b' : ℝ}, a' ≤ b → b' ≤ a → (b' < c ∨ c < b) →
      ∀ q : N, F q ∈ Icc b b' → ¬IsCriticalPointM Z f q := by
    intro b b' hb hb' hbp q hq hc
    by_cases hqS : q ∈ S
    · have := (hS q hqS).2
      rcases hbp with h | h <;> linarith [hq.1, hq.2]
    · rcases hother q hc hqS with h | h <;> linarith [hq.1, hq.2]
  have hsdr₁ := (theorem_3_1_submanifold hN hF (a := a') (b := c - ε) (by linarith)
    (hslab _ _ le_rfl (by linarith)) (hno le_rfl (by linarith) (Or.inl (by linarith)))).2.1
  have hsdr₂ := (theorem_3_1_submanifold hN hF (a := c + ε) (b := a) (by linarith)
    (hslab _ _ (by linarith) le_rfl) (hno (by linarith) le_rfl (Or.inr (by linarith)))).2.1
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

/-- **The homology of a compact slab** (Milnor p. 29): `Morse.Homology.sublevel_step_of_isCompact`
when only the slab `f⁻¹[a', a]` is compact.  If the critical points in the slab are
non-degenerate, `P` is a finite set whose points in the slab are exactly its critical points,
`a' ≤ a` are regular values and all critical values in `(a', a)` are equal, then
`H_i(N^a, N^{a'}; 𝕜)` is finite-dimensional, of dimension the number of critical points of index
`i` in `f⁻¹(a', a)`. -/
theorem sublevel_step_of_slab (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    {F : V → ℝ} (hF : ContDiff ℝ ∞ F) {a' a : ℝ}
    (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Icc a' a))
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      a' ≤ F q → F q ≤ a →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (e : T ≃ₜ N) {P : Finset N}
    (haa : a' ≤ a)
    (hP : letI := hN.chartedSpace;
      ∀ q : N, a' ≤ F q → F q ≤ a → (q ∈ P ↔ IsCriticalPointM Z (F ∘ Subtype.val) q))
    (ha' : ∀ q ∈ P, F q ≠ a') (ha : ∀ q ∈ P, F q ≠ a)
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
  have hfc : Continuous f := hF.continuous.comp continuous_subtype_val
  by_cases hex : ∃ q ∈ P, a' < F q ∧ F q < a
  · -- one critical level `c` in `(a', a)`: Remark 3.3
    obtain ⟨q₀, hq₀P, hq₀a', hq₀a⟩ := hex
    set c := F q₀ with hc_def
    set S := P.filter (fun p : N ↦ F p = c) with hS_def
    have hS : ∀ p ∈ S, IsNondegenerateCriticalPointM Z f p ∧ F p = c := by
      intro p hp
      obtain ⟨hpP, hpc⟩ := Finset.mem_filter.1 hp
      have hpa : F p ≤ a := by rw [hpc]; exact hq₀a.le
      have hpa' : a' ≤ F p := by rw [hpc]; exact hq₀a'.le
      have hpcrit := (hP p hpa' hpa).1 hpP
      exact ⟨⟨hpcrit, hnd p hpcrit hpa' hpa⟩, hpc⟩
    have hother : ∀ q : N, IsCriticalPointM Z f q → q ∉ S → F q < a' ∨ a < F q := by
      intro q hq hqS
      by_contra hcon
      push Not at hcon
      have hqP := (hP q hcon.1 hcon.2).2 hq
      have h1 : a' < F q := lt_of_le_of_ne hcon.1 (ha' q hqP).symm
      have h2 : F q < a := lt_of_le_of_ne hcon.2 (ha q hqP)
      exact hqS (Finset.mem_filter.2 ⟨hqP, hone q hqP q₀ hq₀P h1 h2 hq₀a' hq₀a⟩)
    obtain ⟨hfd, hfr⟩ := sublevel_step_critical_of_slab (𝕜 := 𝕜) hN hF e hS hK hq₀a' hq₀a
      hother i
    refine ⟨hfd, hfr.trans (congrArg Finset.card ?_)⟩
    ext p
    simp only [hS_def, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpP, hpc⟩, hpi⟩
      exact ⟨hpP, ⟨hpc ▸ hq₀a', hpc ▸ hq₀a⟩, hpi⟩
    · rintro ⟨hpP, ⟨h1, h2⟩, hpi⟩
      exact ⟨⟨hpP, hone p hpP q₀ hq₀P h1 h2 hq₀a' hq₀a⟩, hpi⟩
  · -- no critical value in `[a', a]`: Theorem 3.1 on the compact slab `[a', a]`
    push Not at hex
    have hcrit : ∀ q : N, F q ∈ Icc a' a → ¬IsCriticalPointM Z f q := by
      intro q hq hc
      have hqP := (hP q hq.1 hq.2).2 hc
      exact absurd (lt_of_le_of_ne hq.2 (ha q hqP))
        (not_lt.2 (hex q hqP (lt_of_le_of_ne hq.1 (ha' q hqP).symm)))
    have hslab : IsCompact (f ⁻¹' Icc a' a) := hK
    have hsdr := ((theorem_3_1_submanifold hN hF haa hslab hcrit).2.1).preimage_subtype e
    have hsub := subsingleton_subsetHomology_of_isSDR (𝕜 := 𝕜)
      (preimage_mono (f := e) (sublevel_mono f haa)) hsdr i
    refine ⟨inferInstance, ?_⟩
    rw [finrank_zero_of_subsingleton, eq_comm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro p hp ⟨⟨h1, h2⟩, -⟩
    exact absurd h2 (not_lt.2 (hex p hp h1))

end Submanifold

end Morse.Homology

namespace Morse

open Morse.Homology

section Slab

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

omit [FiniteDimensional ℝ W] in
/-- **A compact slab without critical points of index `j` has no homology in degree `j`**:
`Morse.subsingleton_subsetHomology_sublevel` when only the slab `f⁻¹[lo, a₀]` is compact: for
`lo ≤ a ≤ b ≤ a₀` regular values, if the critical points in the slab are non-degenerate and none
with value in `(a, b)` has index `j`, then `H_j(N^b, N^a; 𝕜) = 0`. -/
theorem subsingleton_subsetHomology_slab {𝕜 : Type u} [Field 𝕜] {F : V → ℝ}
    (hF : ContDiff ℝ ∞ F) {lo a₀ : ℝ} (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Icc lo a₀))
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q → lo ≤ F q →
      F q ≤ a₀ → IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (j : ℕ) (m : ℕ) :
    letI := hN.chartedSpace
    ∀ {a b : ℝ} (hab : a ≤ b), lo ≤ a → b ≤ a₀ → (critValuesIn hN F a b).ncard = m →
      (∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q → F q ≠ a) →
      (∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q → F q ≠ b) →
      (∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q → a < F q → F q < b →
        indexM Z (F ∘ Subtype.val) q ≠ j) →
      Subsingleton (subsetHomology 𝕜 j (sublevel_mono (F ∘ Subtype.val : N → ℝ) hab)) := by
  classical
  let _ := hN.chartedSpace
  have := hN.isManifold
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfs : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ f := contMDiff_comp_val hN hF
  have hfin : (f ⁻¹' Icc lo a₀ ∩ {q | IsCriticalPointM Z f q}).Finite := by
    have hC : IsCompact (f ⁻¹' Icc lo a₀ ∩ {x | IsCriticalPointM Z f x}) :=
      hK.inter_right (isClosed_setOf_isCriticalPointM (hfs.of_le (by norm_cast)))
    have hD : IsDiscrete (f ⁻¹' Icc lo a₀ ∩ {x | IsCriticalPointM Z f x}) :=
      isDiscrete_inter_setOf_isCriticalPointM (fun x _ => (hfs x).of_le (by norm_cast))
        fun x hx hc => hnd x hc hx.1 hx.2
    exact hC.finite hD
  set P := hfin.toFinset with hP_def
  have hPmem : ∀ q, q ∈ P ↔ F q ∈ Icc lo a₀ ∧ IsCriticalPointM Z f q := fun q => by
    rw [hP_def, Set.Finite.mem_toFinset]
    rfl
  have hfinV : ∀ a b, lo ≤ a → b ≤ a₀ → (critValuesIn hN F a b).Finite := fun a b ha hb =>
    (hfin.image f).subset fun e ⟨q, hq, he, h1, h2⟩ => ⟨q, ⟨by
      change F q ∈ Icc lo a₀
      exact ⟨by linarith, by linarith⟩, hq⟩, he⟩
  induction m using Nat.strong_induction_on with
  | _ m ih => ?_
  intro a b hab hlo hb hm hra hrb hidx
  rcases le_or_gt m 1 with hm1 | hm1
  · -- at most one critical value: Theorem 3.2 / Remark 3.3
    have hone : ∀ e ∈ critValuesIn hN F a b, ∀ e' ∈ critValuesIn hN F a b, e = e' :=
      (Set.ncard_le_one (hfinV a b hlo hb)).1 (hm ▸ hm1)
    have hKab : IsCompact (f ⁻¹' Icc a b) :=
      hK.of_isClosed_subset (isClosed_Icc.preimage hfs.continuous)
        fun q hq => ⟨hlo.trans hq.1, hq.2.trans hb⟩
    obtain ⟨hfd, hfr⟩ := sublevel_step_of_slab (𝕜 := 𝕜) hN hF hKab
      (fun q hq h1 h2 => hnd q hq (hlo.trans h1) (h2.trans hb)) (Homeomorph.refl N)
      (P := P) hab (fun q hq1 hq2 => by
        rw [hPmem]; exact ⟨fun h => h.2, fun h => ⟨⟨hlo.trans hq1, hq2.trans hb⟩, h⟩⟩)
      (fun q hq => hra q ((hPmem q).1 hq).2) (fun q hq => hrb q ((hPmem q).1 hq).2)
      (fun q hq q' hq' h1 h2 h3 h4 => hone _ ⟨q, ((hPmem q).1 hq).2, rfl, h1, h2⟩ _
        ⟨q', ((hPmem q').1 hq').2, rfl, h3, h4⟩) j
    have h0 : (P.filter fun p : N ↦ (a < F p ∧ F p < b) ∧ indexM Z f p = j).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro q hq ⟨⟨h1, h2⟩, h3⟩
      exact hidx q ((hPmem q).1 hq).2 h1 h2 h3
    rw [h0] at hfr
    have : FiniteDimensional 𝕜 (subsetHomology 𝕜 j (sublevel_mono f hab)) := hfd
    have hfr' : finrank 𝕜 (subsetHomology 𝕜 j (sublevel_mono f hab)) = 0 := hfr
    exact Module.finrank_zero_iff.1 hfr'
  · -- several critical values: split between the two smallest
    set S := critValuesIn hN F a b with hS_def
    have hfinS := hfinV a b hlo hb
    have hne : S.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    set e₁ := hfinS.toFinset.min' (by simpa using hne) with he₁_def
    have he₁S : e₁ ∈ S := hfinS.mem_toFinset.1 (Finset.min'_mem _ _)
    have he₁min : ∀ e ∈ S, e₁ ≤ e := fun e he => Finset.min'_le _ _ (hfinS.mem_toFinset.2 he)
    have hS' : (S \ {e₁}).Finite := hfinS.sdiff
    have hS'card : (S \ {e₁}).ncard = m - 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem he₁S, hm]
    have hne' : (S \ {e₁}).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    set e₂ := hS'.toFinset.min' (by simpa using hne') with he₂_def
    have he₂S : e₂ ∈ S \ {e₁} := hS'.mem_toFinset.1 (Finset.min'_mem _ _)
    have he₂min : ∀ e ∈ S \ {e₁}, e₂ ≤ e := fun e he =>
      Finset.min'_le _ _ (hS'.mem_toFinset.2 he)
    have h12 : e₁ < e₂ := lt_of_le_of_ne (he₁min e₂ he₂S.1) (Ne.symm he₂S.2)
    obtain ⟨-, -, -, ha₁, -⟩ := id he₁S
    obtain ⟨-, -, -, -, hb₂⟩ := id he₂S.1
    set c := (e₁ + e₂) / 2 with hc_def
    have hac : a ≤ c := by linarith
    have hcb : c ≤ b := by linarith
    have hmid : ∀ e ∈ S, e ≠ e₁ → c < e := fun e he he1 => by
      have := he₂min e ⟨he, he1⟩
      linarith
    have hrc : ∀ q : N, IsCriticalPointM Z f q → F q ≠ c := by
      intro q hq he
      have hS : F q ∈ S := ⟨q, hq, rfl, by linarith, by linarith⟩
      have := hmid _ hS (by rw [he]; linarith)
      linarith
    have hSac : critValuesIn hN F a c = {e₁} := by
      ext e
      constructor
      · rintro ⟨q, hq, rfl, h1, h2⟩
        by_contra hne1
        have := hmid _ ⟨q, hq, rfl, h1, by linarith⟩ hne1
        linarith
      · rintro rfl
        obtain ⟨q, hq, he, h1, -⟩ := he₁S
        exact ⟨q, hq, he, h1, by linarith⟩
    have hScb : critValuesIn hN F c b = S \ {e₁} := by
      ext e
      constructor
      · rintro ⟨q, hq, rfl, h1, h2⟩
        exact ⟨⟨q, hq, rfl, by linarith, h2⟩, fun h => by
          rw [mem_singleton_iff] at h
          linarith⟩
      · rintro ⟨⟨q, hq, rfl, h1, h2⟩, hne1⟩
        exact ⟨q, hq, rfl, hmid _ ⟨q, hq, rfl, h1, h2⟩ hne1, h2⟩
    have hz1 := ih 1 (by omega) hac hlo (hcb.trans hb) (by rw [hSac, Set.ncard_singleton]) hra hrc
      fun q hq h1 h2 => hidx q hq h1 (by linarith)
    have hz2 := ih (m - 1) (by omega) hcb (hlo.trans hac) hb (by rw [hScb, hS'card]) hrc hrb
      fun q hq h1 h2 => hidx q hq (by linarith) h2
    exact (subsetTripleLongExactSeq 𝕜 (sublevel_mono f hac) (sublevel_mono f hcb)).subsingleton_B
      hz1 hz2


end Slab

end Morse
