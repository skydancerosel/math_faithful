import Morse.Chapter5.ComplexIndex
import Morse.Chapter4.Existence
import Morse.Chapter10.RelativeCells
import Morse.Chapter10.SublevelHomology

/-!
Milnor, *Morse Theory*, §7, Theorems 7.1 and 7.2 (pp. 39–41); Exposition/Chapter5.md, §§1 and 4.

# The Lefschetz theorem: complex submanifolds have no high cells

## Milnor's text, paraphrased

* **Theorem 7.1** (p. 39): a non-singular affine algebraic variety `M ⊂ ℂⁿ` of real dimension
  `2k` has `H_i(M; ℤ) = 0` for `i > k`.  It follows from
* **Theorem 7.2** (p. 39): a complex analytic manifold `M` of complex dimension `k`,
  bianalytically embedded as a closed subset of `ℂⁿ`, has the homotopy type of a `k`-dimensional
  CW-complex.  *Proof* (pp. 40–41): for almost every `p`, `L_p = ‖· − p‖²` is a Morse function on
  `M` with compact sublevel sets (6.6, 6.7); its indices are `≤ k` (Assertions 1, 2 and Lemma
  6.9); apply Theorem 3.5.

## What is formalized

`ℂⁿ` is a Euclidean space `𝔼 n = ℝⁿ` with a complex structure `J` (`Morse.IsOrthComplexStructure`,
e.g. `n` even and `J` multiplication by `i`), and `M ⊆ 𝔼 n` a slice submanifold of real dimension
`2k` whose tangent spaces are `J`-invariant (`Morse.IsComplexSubmanifold`).

* `Morse.subsingleton_subsetHomology_sublevel` (any slice submanifold): a slab `N^b ⊇ N^a`
  between regular levels, in a compact sublevel set with non-degenerate critical points, has no
  homology in degree `j` if no critical point in the slab has index `j`.
* `Morse.exists_regular_levels`: regular levels `a₀ < 0 ≤ a₁ ≤ ⋯ → ∞` for a proper Morse function.
* `Morse.indexM_normSq_sub_le`: on a complex submanifold of real dimension `2k`, **every critical
  point of `L_p` has index `≤ k`** (`Morse.two_mul_indexM_normSq_sub_le`).
* `Morse.theorem_7_2`: **Theorem 7.2**: a closed complex submanifold of complex dimension `k` has
  the homotopy type of a countable cell complex (`Morse.IsCountableCellComplexType`) all of whose
  cells have dimension `≤ k`.
* `Morse.theorem_7_1`: **Theorem 7.1 over a field**: such an `M` has `H_i(M; 𝕜) = 0` for
  `i > k`, for every field `𝕜`.

## Deviations from Milnor, and what he leaves implicit

* **Hypotheses.**  "Non-singular affine algebraic variety" and "bianalytically embedded closed
  complex manifold" are replaced by "closed slice submanifold with complex tangent spaces"; a
  non-singular variety is such a submanifold (the zero set is closed; non-singularity makes it a
  complex submanifold, whose tangent spaces are complex), which is not formalized.  The real
  dimension `2k` is fixed by the model space, so `M` has pure dimension (Milnor's statements are
  for connected `M` implicitly; the exposition notes components of different dimensions are
  harmless for 7.1–7.2, but not for 7.3–7.4).
* **"A `k`-dimensional CW-complex"** is "of dimension at most `k`" (the exposition: `ℂ` is
  contractible).  The complex is the countable cell tower of the project (the Appendix route of
  Theorem 3.5 for a proper Morse function with possibly infinitely many critical points), not a
  CW complex in the sense of Whitehead.
* **Homology over a field**, not over `ℤ`: the project's homology is singular homology with field
  coefficients.  It is computed from the sublevel filtration (Theorem 3.2 and Remark 3.3 slab by
  slab, and the homology of an exhaustion), not from cellular chains.
* **The index bound** is proved without focal points (`Morse/Chapter5/ComplexIndex.lean`).
* **Corollary 7.3** (over a field, with the pure-dimension hypothesis and Hypothesis (N), without
  Lefschetz duality) is `Morse.corollary_7_3` (`Morse/Chapter5/ProjectiveSection.lean`, from
  `Morse/Chapter5/HyperplaneSection.lean`).  **Theorem 7.4** is `Morse.theorem_7_4`
  (`Morse/Chapter5/LefschetzHomotopy.lean`).  **Not formalized**: the integral-homology form
  of 7.1.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

universe u

open Morse.Homology

section Slab

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-- The critical values of `F|N` in `(a, b)`. -/
def critValuesIn (F : V → ℝ) (a b : ℝ) : Set ℝ :=
  letI := hN.chartedSpace
  {e | ∃ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q ∧ F q = e ∧ a < e ∧ e < b}

omit [FiniteDimensional ℝ W] in
/-- **A slab without critical points of index `j` has no homology in degree `j`**: for `N` a
slice submanifold, `F` smooth with `N^{a₀}` compact and non-degenerate critical points there, and
`a ≤ b ≤ a₀` regular values, if no critical point with value in `(a, b)` has index `j`, then
`H_j(N^b, N^a; 𝕜) = 0` (Theorem 3.2 and Remark 3.3 with the exact sequences of triples, by
induction on the number of critical values in the slab). -/
theorem subsingleton_subsetHomology_sublevel {𝕜 : Type u} [Field 𝕜] {F : V → ℝ}
    (hF : ContDiff ℝ ∞ F) {a₀ : ℝ} (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Iic a₀))
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q → F q ≤ a₀ →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (j : ℕ) (m : ℕ) :
    letI := hN.chartedSpace
    ∀ {a b : ℝ} (hab : a ≤ b), b ≤ a₀ → (critValuesIn hN F a b).ncard = m →
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
  have hfin : (f ⁻¹' Iic a₀ ∩ {q | IsCriticalPointM Z f q}).Finite := by
    have hC : IsCompact (f ⁻¹' Iic a₀ ∩ {x | IsCriticalPointM Z f x}) :=
      hK.inter_right (isClosed_setOf_isCriticalPointM (hfs.of_le (by norm_cast)))
    have hD : IsDiscrete (f ⁻¹' Iic a₀ ∩ {x | IsCriticalPointM Z f x}) :=
      isDiscrete_inter_setOf_isCriticalPointM (fun x _ => (hfs x).of_le (by norm_cast))
        fun x hx hc => hnd x hc hx
    exact hC.finite hD
  set P := hfin.toFinset with hP_def
  have hPmem : ∀ q, q ∈ P ↔ F q ≤ a₀ ∧ IsCriticalPointM Z f q := fun q => by
    rw [hP_def, Set.Finite.mem_toFinset]
    rfl
  have hfinV : ∀ a b, b ≤ a₀ → (critValuesIn hN F a b).Finite := fun a b hb =>
    (hfin.image f).subset fun e ⟨q, hq, he, h1, h2⟩ => ⟨q, ⟨by
      change F q ≤ a₀
      linarith, hq⟩, he⟩
  induction m using Nat.strong_induction_on with
  | _ m ih => ?_
  intro a b hab hb hm hra hrb hidx
  rcases le_or_gt m 1 with hm1 | hm1
  · -- at most one critical value: Theorem 3.2 / Remark 3.3
    have hone : ∀ e ∈ critValuesIn hN F a b, ∀ e' ∈ critValuesIn hN F a b, e = e' :=
      (Set.ncard_le_one (hfinV a b hb)).1 (hm ▸ hm1)
    obtain ⟨hfd, hfr⟩ := sublevel_step_of_isCompact (𝕜 := 𝕜) hN hF hK hnd (Homeomorph.refl N)
      (P := P) hab hb (fun q hq => by rw [hPmem]; exact ⟨fun h => h.2, fun h => ⟨hq.trans hb, h⟩⟩)
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
    have hfinS := hfinV a b hb
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
    have hz1 := ih 1 (by omega) hac (hcb.trans hb) (by rw [hSac, Set.ncard_singleton]) hra hrc
      fun q hq h1 h2 => hidx q hq h1 (by linarith)
    have hz2 := ih (m - 1) (by omega) hcb hb (by rw [hScb, hS'card]) hrc hrb
      fun q hq h1 h2 => hidx q hq (by linarith) h2
    exact (subsetTripleLongExactSeq 𝕜 (sublevel_mono f hac) (sublevel_mono f hcb)).subsingleton_B
      hz1 hz2

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- **Regular levels for a proper Morse function** `F|N ≥ 0`: levels `a₀ < 0 ≤ a₁ ≤ ⋯ → ∞`, none
of them a critical value. -/
theorem exists_regular_levels {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hK : ∀ a, IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Iic a))
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (hpos : ∀ x, 0 ≤ F x) :
    letI := hN.chartedSpace
    ∃ a : ℕ → ℝ, a 0 < 0 ∧ Monotone a ∧ Tendsto a atTop atTop ∧
      ∀ m (q : N), IsCriticalPointM Z (F ∘ Subtype.val) q → F q ≠ a m := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfs : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ f := contMDiff_comp_val hN hF
  have hfin : ∀ b, (f ⁻¹' Iic b ∩ {q | IsCriticalPointM Z f q}).Finite := fun b =>
    (hK b).inter_right (isClosed_setOf_isCriticalPointM (hfs.of_le (by norm_cast))) |>.finite
      (isDiscrete_inter_setOf_isCriticalPointM (fun x _ => (hfs x).of_le (by norm_cast))
        fun x _ hc => hnd x hc)
  have hlev : ∀ m : ℕ, ∃ x ∈ Ioo (m : ℝ) (m + 1),
      x ∉ f '' (f ⁻¹' Iic ((m : ℝ) + 1) ∩ {q | IsCriticalPointM Z f q}) := fun m =>
    ((Ioo_infinite (by linarith : (m : ℝ) < m + 1)).sdiff ((hfin _).image f)).nonempty
  choose x hx hxreg using hlev
  let a : ℕ → ℝ := fun m => match m with
    | 0 => -1
    | m + 1 => x m
  have haS : ∀ m, a (m + 1) = x m := fun m => rfl
  have ha_gt : ∀ m : ℕ, (m : ℝ) - 1 ≤ a m := by
    intro m
    cases m with
    | zero => simp [a]
    | succ m => rw [haS]; push_cast; linarith [(hx m).1]
  have ha_lt : ∀ m, a m < m := by
    intro m
    cases m with
    | zero => simp [a]
    | succ m => rw [haS]; push_cast; exact (hx m).2
  refine ⟨a, by simp [a], monotone_nat_of_le_succ fun m => ?_, ?_, fun m q hq he => ?_⟩
  · have h1 := ha_lt m
    have h2 := ha_gt (m + 1)
    push_cast at h2
    linarith
  · exact tendsto_atTop_mono ha_gt (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  · cases m with
    | zero =>
      have := hpos q
      simp only [a] at he
      linarith
    | succ m =>
      rw [haS] at he
      exact hxreg m ⟨q, ⟨by
        change F q ≤ (m : ℝ) + 1
        rw [he]; exact (hx m).2.le, hq⟩, he⟩

end Slab

/-! ### Theorems 7.2 and 7.1 -/

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

variable {n k w : ℕ} {M : Set (𝔼 n)}
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 (2 * k)) (𝔼 w) M)

/-- On a complex submanifold of real dimension `2k`, the index of `L_p` is `≤ k` at every
critical point. -/
theorem indexM_normSq_sub_le {J : 𝔼 n →L[ℝ] 𝔼 n} (hJ : IsOrthComplexStructure J)
    (hc : IsComplexSubmanifold hM J) (p : 𝔼 n) (q : M)
    (hcrit : letI := hM.chartedSpace;
      IsCriticalPointM (𝔼 (2 * k)) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) q) :
    letI := hM.chartedSpace
    indexM (𝔼 (2 * k)) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) q ≤ k := by
  have h := two_mul_indexM_normSq_sub_le hJ hc p q hcrit
  rw [finrank_euclideanSpace_fin] at h
  omega

/-- **Theorem 7.2** (Milnor p. 39): a complex submanifold `M` of `ℂⁿ` (here: a slice submanifold
of real dimension `2k` of a Euclidean space with a complex structure `J`, with `J`-invariant
tangent spaces) which is a closed subset has the homotopy type of a countable cell complex with
all cells of dimension `≤ k`. -/
theorem theorem_7_2 (hcl : IsClosed M) {J : 𝔼 n →L[ℝ] 𝔼 n} (hJ : IsOrthComplexStructure J)
    (hc : IsComplexSubmanifold hM J) :
    ∃ cells : ℕ → List ℕ, IsCountableCellComplexType M cells ∧ ∀ i, ∀ d ∈ cells i, d ≤ k := by
  classical
  let _ := hM.chartedSpace
  obtain ⟨p, hp⟩ := exists_isMorseFunction_normSq_sub (hM := hM)
  set F : 𝔼 n → ℝ := fun y => ‖y - p‖ ^ 2 with hF_def
  have hF : ContDiff ℝ ∞ F := contDiff_normSq_sub p
  have hK : ∀ a, IsCompact ((F ∘ Subtype.val : M → ℝ) ⁻¹' Iic a) :=
    fun a => isCompact_sublevel_normSq_sub hcl p a
  obtain ⟨a, ha0, ha, ha', hreg⟩ := exists_regular_levels hM hF hK hp.isNondegenerate
    fun _ => sq_nonneg _
  have hstep : ∀ m, ∃ ps : List M, (∀ q ∈ ps,
      IsCriticalPointM (𝔼 (2 * k)) (F ∘ Subtype.val) q) ∧
      IsRelCellComplexType (inclC (sublevel_mono (F ∘ Subtype.val : M → ℝ) (ha (Nat.le_succ m))))
        (ps.map (indexM (𝔼 (2 * k)) (F ∘ Subtype.val))) := fun m => by
    obtain ⟨ps, -, hmem, -, hcell⟩ := isRelCellComplexType_sublevel_of_isCompact hM hF
      (hK (a (m + 1))) (fun q hq _ => hp.isNondegenerate q hq) (ha (Nat.le_succ m))
      (fun q hq => hreg m q hq) (fun q hq => hreg (m + 1) q hq)
    exact ⟨ps, fun q hq => ((hmem q).1 hq).1, hcell⟩
  choose ps hps hcell using hstep
  let cells : ℕ → List ℕ := fun m => match m with
    | 0 => []
    | m + 1 => (ps m).map (indexM (𝔼 (2 * k)) (F ∘ Subtype.val))
  let E : C(M, ℝ) := ⟨F ∘ Subtype.val, hF.continuous.comp continuous_subtype_val⟩
  refine ⟨cells, isCountableCellComplexType_of_relSublevel E ha ha' ?_ fun m => hcell m, ?_⟩
  · have : IsEmpty ↥(sublevel E (a 0)) := ⟨fun x => by
      have h1 : F x.1 ≤ a 0 := x.2
      have := sq_nonneg ‖(x.1 : 𝔼 n) - p‖
      linarith⟩
    exact IsFiniteCellComplexType.of_isEmpty _
  · rintro (_ | m) d hd
    · simp [cells] at hd
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hd
      exact indexM_normSq_sub_le hM hJ hc p q (hps m q hq)

/-- **Theorem 7.1** (Milnor p. 39), over a field: a closed complex submanifold `M` of `ℂⁿ` of
complex dimension `k` (as in `Morse.theorem_7_2`) has `H_i(M; 𝕜) = 0` for `i > k`. -/
theorem theorem_7_1 {𝕜 : Type} [Field 𝕜] (hcl : IsClosed M) {J : 𝔼 n →L[ℝ] 𝔼 n}
    (hJ : IsOrthComplexStructure J) (hc : IsComplexSubmanifold hM J) {i : ℕ} (hi : k < i) :
    Subsingleton (spaceHomology 𝕜 i M) := by
  classical
  let _ := hM.chartedSpace
  obtain ⟨p, hp⟩ := exists_isMorseFunction_normSq_sub (hM := hM)
  set F : 𝔼 n → ℝ := fun y => ‖y - p‖ ^ 2 with hF_def
  have hF : ContDiff ℝ ∞ F := contDiff_normSq_sub p
  have hK : ∀ a, IsCompact ((F ∘ Subtype.val : M → ℝ) ⁻¹' Iic a) :=
    fun a => isCompact_sublevel_normSq_sub hcl p a
  obtain ⟨a, ha0, ha, ha', hreg⟩ := exists_regular_levels hM hF hK hp.isNondegenerate
    fun _ => sq_nonneg _
  set A : ℕ → Set M := fun m => sublevel (F ∘ Subtype.val : M → ℝ) (a m) with hA_def
  have hA : Monotone A := fun _ _ h => sublevel_mono _ (ha h)
  have hcpt : ∀ K : Set M, IsCompact K → ∃ m, K ⊆ A m := fun K hK' =>
    exists_subset_sublevel_of_isCompact (hF.continuous.comp continuous_subtype_val)
      (fun r => (ha'.eventually_ge_atTop r).exists) hK'
  have hsteps : ∀ j, k < j → ∀ m, 0 ≤ m → Subsingleton (subsetHomology 𝕜 j (hA (Nat.le_succ m))) :=
    fun j hj m _ => subsingleton_subsetHomology_sublevel hM hF (hK (a (m + 1)))
      (fun q hq _ => hp.isNondegenerate q hq) j _ (ha (Nat.le_succ m)) le_rfl rfl
      (fun q hq => hreg m q hq) (fun q hq => hreg (m + 1) q hq)
      fun q hq _ _ h => by
        have : indexM (𝔼 (2 * k)) (F ∘ Subtype.val) q ≤ k := indexM_normSq_sub_le hM hJ hc p q hq
        omega
  have e := spaceHomologyEquivOfSteps (𝕜 := 𝕜) hA hcpt (i := i) (k₀ := 0)
    (hsteps i hi) (hsteps (i + 1) (by omega))
  have hA0 : A 0 = ∅ := eq_empty_of_forall_notMem fun x hx => by
    have h1 : F x ≤ a 0 := hx
    have := sq_nonneg ‖(x : 𝔼 n) - p‖
    linarith
  have h0 : ∀ (S : Set M) (h : ∅ ⊆ S), S = ∅ → Subsingleton (subsetHomology 𝕜 i h) := by
    intro S h hS
    subst hS
    exact subsingleton_subsetHomology_self i ∅
  have := h0 (A 0) (empty_subset _) hA0
  exact e.symm.injective.subsingleton

end Morse
