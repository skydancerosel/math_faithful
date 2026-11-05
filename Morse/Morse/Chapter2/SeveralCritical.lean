import Morse.Chapter2.CellAttachSubmanifold

/-!
Milnor, *Morse Theory*, §3, p. 19: Remark 3.3, for a submanifold of Euclidean space.

# Several critical points on one level

**Remark 3.3** (p. 19), paraphrased: if `f⁻¹(c)` contains `k` non-degenerate critical points
`p₁, …, p_k` of indices `λ₁, …, λ_k`, a similar proof shows that `M^{c+ε}` has the homotopy type of
`M^{c-ε} ∪ e^{λ₁} ∪ ⋯ ∪ e^{λ_k}`.

This file proves it for `M = N` a slice submanifold of a finite-dimensional real normed space and
`f = F|N` (the setting of `Morse/Chapter2/CellAttachSubmanifold.lean`), as a strong deformation
retraction of `N^{c+ε}` onto `N^{c-ε} ∪ e^{λ₁} ∪ ⋯ ∪ e^{λ_k}` for pairwise disjoint cells
(`Morse.remark_3_3_submanifold`).

## The proof

As in the exposition (`Exposition/Chapter2.md`, §3): Morse patches `ψᵢ` around the `pᵢ` with
pairwise disjoint domains, and `F = f - ∑ᵢ μ(ξᵢ + 2ηᵢ)`. Instead of redoing Assertions 1–4 "chart
by chart" for this `F`, the bumps are subtracted one at a time, `F_s = f - ∑_{i ∈ s} μ(ξᵢ + 2ηᵢ)`
for a finite set `s` of indices (`Morse.multiF`), and the single-patch statements of
`Morse/Chapter2/CellPatch.lean` and `Morse/Chapter2/CellAttachSubmanifold.lean` are applied to
`F_s` and the patch `ψᵢ`, `i ∉ s`: since the domains are disjoint, `F_s = f` on the domain of `ψᵢ`,
so `ψᵢ` is a Morse patch of `F_s` at `pᵢ`, and `F_{s ∪ {i}}` is Milnor's modification of `F_s` in
that patch (`Morse.multi_induction`). Assertion 4 for `F_{s ∪ {i}}` is the single-patch Assertion 4
followed by the deformation for `F_s`, the latter extended by the identity over the new cell `eᵢ`
(`Morse.IsStrongDeformationRetract.union_of_isClosed`).

## What Milnor's text leaves implicit

* **The hypotheses**: as for Theorem 3.2, `f⁻¹[c - ε₀, c + ε₀]` must be compact and contain no
  critical points other than the `pᵢ`.
* **Disjoint coordinate neighbourhoods**: the `pᵢ` have pairwise disjoint neighbourhoods because `N`
  is Hausdorff (`Set.Finite.t2_separation`), and the Morse charts are taken inside them
  (`Morse.exists_isMorsePatch_submanifold_subset`); `ε` must be small for all of them at once.
* **The cells are attached one at a time**: `M^{c-ε} ∪ e^{λ₁} ∪ ⋯ ∪ e^{λ_j}` is
  `(M^{c-ε} ∪ ⋯ ∪ e^{λ_{j-1}}) ∪ e^{λ_j}`, and Lemma D applies at each step because the cells are
  disjoint, so that `e^{λ_j}` meets the earlier space exactly in its boundary
  (`Morse.isFiniteCellComplexType_union_cells` in `Morse/Chapter2/CWType.lean`).

## Main results

* `Morse.IsStrongDeformationRetract.union_of_isClosed`: a strong deformation retraction extends by
  the identity over a closed set which meets the domain only inside the retract.
* `Morse.multi_induction`: Assertions 1–4 for `F_s`, by induction on `s`.
* `Morse.remark_3_3_submanifold`: **Remark 3.3** for `f = F|N`.
-/

open Set Filter Topology Function Module CategoryTheory Limits TopCat
open scoped ContDiff Manifold unitInterval

universe u

noncomputable section

namespace Morse

open CellModel

/-! ### Extending a strong deformation retraction by the identity -/

/-- A set is a strong deformation retract of a space which it fills. -/
theorem isStrongDeformationRetract_of_eq_univ {T : Type*} [TopologicalSpace T] {A : Set T}
    (h : A = univ) : IsStrongDeformationRetract A :=
  ⟨ContinuousMap.id T, fun x => h ▸ mem_univ x, ⟨ContinuousMap.HomotopyRel.refl _ _⟩⟩

/-- **Extending a strong deformation retraction by the identity.** If `A ⊆ B` is a strong
deformation retract of `B`, and `C` is a closed set with `B ∩ C ⊆ A` (`B` closed too), then
`A ∪ C` is a strong deformation retract of `B ∪ C`: the deformation of `B`, extended by the
identity on `C`, is continuous by the pasting lemma, as it is the identity on `B ∩ C ⊆ A`. -/
theorem IsStrongDeformationRetract.union_of_isClosed {T : Type*} [TopologicalSpace T]
    {A B C : Set T} (hB : IsClosed B) (hC : IsClosed C) (hBC : B ∩ C ⊆ A)
    (h : IsStrongDeformationRetract ((↑) ⁻¹' A : Set B)) :
    IsStrongDeformationRetract ((↑) ⁻¹' (A ∪ C) : Set ↥(B ∪ C)) := by
  classical
  obtain ⟨r, hr, ⟨H⟩⟩ := h
  have hfix : ∀ (t : I) (x : B), (x : T) ∈ A → H (t, x) = x := fun t x hx => H.eq_fst t hx
  let K : I × ↥(B ∪ C) → ↥(B ∪ C) := fun p =>
    if hp : (p.2 : T) ∈ B then ⟨H (p.1, ⟨p.2, hp⟩), Or.inl (H (p.1, ⟨p.2, hp⟩)).2⟩ else p.2
  have hK₂ : ∀ p : I × ↥(B ∪ C), (p.2 : T) ∈ C → K p = p.2 := by
    intro p hp
    simp only [K]
    split_ifs with hpB
    · apply Subtype.ext
      change ((H (p.1, ⟨p.2, hpB⟩) : B) : T) = (p.2 : T)
      rw [hfix p.1 ⟨p.2, hpB⟩ (hBC ⟨hpB, hp⟩)]
    · rfl
  have hK : Continuous K := by
    rw [← continuousOn_univ]
    have hU : {p : I × ↥(B ∪ C) | (p.2 : T) ∈ B} ∪ {p | (p.2 : T) ∈ C} = univ :=
      eq_univ_of_forall fun p => p.2.2
    rw [← hU]
    have hc : Continuous fun p : I × ↥(B ∪ C) => (p.2 : T) :=
      continuous_subtype_val.comp continuous_snd
    refine ContinuousOn.union_of_isClosed ?_ ?_ (hB.preimage hc) (hC.preimage hc)
    · rw [continuousOn_iff_continuous_domRestrict]
      let g₁ : {p : I × ↥(B ∪ C) | (p.2 : T) ∈ B} → ↥(B ∪ C) := fun p =>
        ⟨H (p.1.1, ⟨p.1.2, p.2⟩), Or.inl (H (p.1.1, ⟨p.1.2, p.2⟩)).2⟩
      have h1 : Continuous fun p : {p : I × ↥(B ∪ C) | (p.2 : T) ∈ B} =>
          ((p.1.1, ⟨p.1.2, p.2⟩) : I × B) :=
        (continuous_fst.comp continuous_subtype_val).prodMk
          ((hc.comp continuous_subtype_val).subtype_mk _)
      have hg₁ : Continuous g₁ :=
        (continuous_subtype_val.comp (H.continuous.comp h1)).subtype_mk _
      refine hg₁.congr fun p => ?_
      simp only [domRestrict_apply, K, g₁]
      rw [dif_pos (show ((p : I × ↥(B ∪ C)).2 : T) ∈ B from p.2)]
    · exact continuous_snd.continuousOn.congr fun p hp => hK₂ p hp
  have hK0 : ∀ x, K (0, x) = x := fun x => by
    simp only [K]
    split_ifs with hx
    · apply Subtype.ext
      change ((H (0, ⟨x, hx⟩) : B) : T) = (x : T)
      rw [H.apply_zero]
      rfl
    · rfl
  have hKA : ∀ (t : I) (x : ↥(B ∪ C)), (x : T) ∈ A ∪ C → K (t, x) = x := by
    rintro t x (hx | hx)
    · simp only [K]
      split_ifs with hxB
      · apply Subtype.ext
        change ((H (t, ⟨x, hxB⟩) : B) : T) = (x : T)
        rw [hfix t ⟨x, hxB⟩ hx]
      · rfl
    · exact hK₂ (t, x) hx
  let r' : C(↥(B ∪ C), ↥(B ∪ C)) :=
    ⟨fun x => K (1, x), hK.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨r', fun x => ?_, ⟨?_⟩⟩
  · change ((K (1, x) : ↥(B ∪ C)) : T) ∈ A ∪ C
    simp only [K]
    split_ifs with hx
    · rw [H.apply_one]
      exact Or.inl (hr _)
    · exact Or.inr (x.2.resolve_left hx)
  · exact
      { toFun := K
        continuous_toFun := hK
        map_zero_left := hK0
        map_one_left := fun _ => rfl
        prop' := fun t x hx => hKA t x hx }

/-! ### Several Morse patches -/

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V}

/-- Milnor's function for several patches: `F_s = F - ∑_{i ∈ s} Bᵢ`, where `Bᵢ` extends the bump
`μ(ξᵢ + 2ηᵢ)` of the `i`-th patch to `V`. -/
def multiF {ι : Type*} (F : V → ℝ) (B : ι → V → ℝ) (s : Finset ι) (x : V) : ℝ :=
  F x - ∑ i ∈ s, B i x

theorem contDiff_multiF {ι : Type*} {F : V → ℝ} (hF : ContDiff ℝ ∞ F) {B : ι → V → ℝ}
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (s : Finset ι) : ContDiff ℝ ∞ (multiF F B s) :=
  hF.sub (ContDiff.sum fun i _ => hB i)

section Induction

variable {ι : Type*} {X Y : ι → Type*} [∀ i, NormedAddCommGroup (X i)]
  [∀ i, InnerProductSpace ℝ (X i)] [∀ i, FiniteDimensional ℝ (X i)]
  [∀ i, NormedAddCommGroup (Y i)] [∀ i, InnerProductSpace ℝ (Y i)]
  [∀ i, FiniteDimensional ℝ (Y i)]

/-- **Assertions 1, 2 and 4 for several patches**, by induction on the set `s` of patches whose
bumps have been subtracted. For `F_s = F - ∑_{i ∈ s} Bᵢ` (restricted to `N`):
`F_s⁻¹(-∞, c+ε] = N^{c+ε}`; `F_s` and `f` have the same critical points; `F_s(pᵢ) = c - μ(0)` for
`i ∈ s`; the cells `eᵢ`, `i ∈ s`, lie in `F_s⁻¹(-∞, c-ε]`; and `N^{c-ε} ∪ ⋃_{i ∈ s} eᵢ` is a strong
deformation retract of `F_s⁻¹(-∞, c-ε]`. -/
theorem multi_induction (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {F : V → ℝ}
    (hF : ContDiff ℝ ∞ F) {p : ι → N} {ψ : (i : ι) → OpenPartialHomeomorph N (X i × Y i)}
    {c ε : ℝ} {μ : ℝ → ℝ}
    (hφ : ∀ i, IsMorsePatch (F ∘ Subtype.val) (p i) (ψ i))
    (hψ : ∀ i, letI := hN.chartedSpace; IsSmoothCoord Z (ψ i)) (hc : ∀ i, F (p i) = c)
    (hdisj : Pairwise fun i j => Disjoint (ψ i).source (ψ j).source)
    (hball : ∀ i, {v : X i × Y i | xi v + eta v ≤ 2 * ε} ⊆ (ψ i).target)
    (hμ : IsMilnorMu ε μ) {B : ι → V → ℝ} (hB : ∀ i, ContDiff ℝ ∞ (B i))
    (hBN : ∀ i, B i ∘ Subtype.val = patchBump (ψ i) μ) (s : Finset ι) :
    letI := hN.chartedSpace
    sublevel (multiF F B s ∘ Subtype.val : N → ℝ) (c + ε) =
        sublevel (F ∘ Subtype.val : N → ℝ) (c + ε) ∧
      (∀ q : N, IsCriticalPointM Z (multiF F B s ∘ Subtype.val) q ↔
        IsCriticalPointM Z (F ∘ Subtype.val) q) ∧
      (∀ i ∈ s, multiF F B s (p i) = c - μ 0) ∧
      (∀ i ∈ s, patchCell (ψ i) ε ⊆ sublevel (multiF F B s ∘ Subtype.val : N → ℝ) (c - ε)) ∧
      IsStrongDeformationRetract
        ((↑) ⁻¹' (sublevel (F ∘ Subtype.val : N → ℝ) (c - ε) ∪ ⋃ i ∈ s, patchCell (ψ i) ε) :
          Set (sublevel (multiF F B s ∘ Subtype.val : N → ℝ) (c - ε))) := by
  classical
  let _ := hN.chartedSpace
  have := hN.isManifold
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  -- the bumps of the patches in `s` vanish on the domain of any other patch
  have hBq : ∀ i j (q : N), i ≠ j → q ∈ (ψ i).source → B j q = 0 := by
    intro i j q hij hq
    have := congrFun (hBN j) q
    simp only [Function.comp_apply] at this
    rw [this, patchBump, indicator_of_notMem fun h => (hdisj hij).le_bot ⟨hq, h⟩]
  have hout : ∀ (s : Finset ι) i, i ∉ s → ∀ q ∈ (ψ i).source, multiF F B s q = F q := by
    intro s i hi q hq
    rw [multiF, Finset.sum_eq_zero fun j hj => hBq i j q (fun h => hi (h ▸ hj)) hq, sub_zero]
  have hmd : ∀ s : Finset ι, MDifferentiable 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) (multiF F B s ∘ Subtype.val) :=
    fun s => (contMDiff_comp_val hN (contDiff_multiF hF hB s)).mdifferentiable (by simp)
  induction s using Finset.induction_on with
  | empty =>
    have h0 : multiF F B ∅ = F := funext fun x => by simp [multiF]
    rw [h0]
    refine ⟨rfl, fun q => Iff.rfl, fun i hi => absurd hi (Finset.notMem_empty i),
      fun i hi => absurd hi (Finset.notMem_empty i),
      isStrongDeformationRetract_of_eq_univ (eq_univ_of_forall fun x => Or.inl x.2)⟩
  | insert i s hi ih =>
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih
    set g : N → ℝ := multiF F B s ∘ Subtype.val with hg_def
    have hgp : g (p i) = c := by
      rw [hg_def, Function.comp_apply, hout s i hi _ (hφ i).mem_source, hc]
    -- `ψᵢ` is a Morse patch of `g`
    have hφg : IsMorsePatch g (p i) (ψ i) :=
      ⟨(hφ i).mem_source, (hφ i).apply_self, fun q hq => by
        rw [hgp, ← hc i]
        have h1 : g q = F q := hout s i hi q hq
        rw [h1]
        exact (hφ i).apply_eq q hq⟩
    -- `F_{s ∪ {i}}` is Milnor's modification of `g` in the patch `ψᵢ`
    have hins : multiF F B (insert i s) ∘ Subtype.val = patchF g (ψ i) μ := by
      funext q
      have := congrFun (hBN i) q
      simp only [Function.comp_apply] at this
      simp only [Function.comp_apply, multiF, Finset.sum_insert hi, patchF, hg_def, ← this]
      ring
    rw [hins]
    have hpF : ∀ q, patchF g (ψ i) μ q ≤ g q := fun q => patchF_le hμ q
    refine ⟨?_, fun q => ?_, ?_, ?_, ?_⟩
    · rw [← hgp, sublevel_patchF_add hφg hμ, hgp, ih1]
    · rw [isCriticalPointM_patchF_iff hN hφg (hψ i) (hball i) hμ (hmd s)
        (by rw [← hins]; exact hmd _) q, ih2]
    · intro j hj
      have hj' := congrFun hins (p j)
      simp only [Function.comp_apply] at hj'
      rw [hj']
      rcases Finset.mem_insert.1 hj with rfl | hj
      · rw [patchF_apply_self hφg, hgp]
      · have hpj : p j ∉ (ψ i).source := fun h =>
          (hdisj (fun hij : i = j => hi (hij ▸ hj))).le_bot ⟨h, (hφ j).mem_source⟩
        rw [patchF, patchBump, indicator_of_notMem hpj, sub_zero]
        exact ih3 j hj
    · intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · have := patchCell_subset_sublevel_patchF (hball j) hφg hμ
        rwa [hgp] at this
      · exact fun q hq => (hpF q).trans (ih4 j hj hq)
    · -- Assertion 4: the patch deformation, then the deformation for `g` extended over `eᵢ`
      have hcell : IsCompact (patchCell (ψ i) ε) := by
        have hcm : IsCompact (cellModel ε : Set (X i × Y i)) :=
          (isCompact_ellipsoid ε).of_isClosed_subset
            ((isClosed_le continuous_xi continuous_const).inter
              (isClosed_eq continuous_snd continuous_const)) cellModel_subset_ellipsoid
        exact hcm.image_of_continuousOn ((ψ i).continuousOn_symm.mono fun v hv =>
          hball i (ellipsoid_subset_ball ε (cellModel_subset_ellipsoid hv)))
      have hgc : Continuous g := (contDiff_multiF hF hB s).continuous.comp continuous_subtype_val
      have hsrc : patchCell (ψ i) ε ⊆ (ψ i).source := (image_mono cellModel_subset_ellipsoid).trans
        (patchEllipsoid_subset_source (hball i))
      have hU := IsStrongDeformationRetract.union_of_isClosed (C := patchCell (ψ i) ε)
        (isClosed_le hgc continuous_const) hcell.isClosed (fun q ⟨hq1, hq2⟩ => Or.inl (by
          have h1 : g q ≤ c - ε := hq1
          rw [hg_def, Function.comp_apply, hout s i hi q (hsrc hq2)] at h1
          exact h1)) ih5
      have hP := isStrongDeformationRetract_patch_handle (hball i) hφg hμ
      rw [hgp] at hP
      have hset : sublevel f (c - ε) ∪ ⋃ j ∈ insert i s, patchCell (ψ j) ε =
          (sublevel f (c - ε) ∪ ⋃ j ∈ s, patchCell (ψ j) ε) ∪ patchCell (ψ i) ε := by
        rw [Finset.set_biUnion_insert]
        ext q
        simp only [mem_union]
        tauto
      rw [hset]
      refine IsStrongDeformationRetract.trans ?_ ?_ hU hP
      · refine union_subset_union_left _ (union_subset (fun q hq => ?_) ?_)
        · exact (show g q ≤ f q by
            simp only [hg_def, hf_def, Function.comp_apply, multiF]
            exact sub_le_self _ (Finset.sum_nonneg fun j _ => by
              have := congrFun (hBN j) q
              simp only [Function.comp_apply] at this
              rw [this]
              exact indicator_nonneg (fun _ _ => hμ.nonneg _) _)).trans hq
        · exact iUnion₂_subset fun j hj => ih4 j hj
      · exact union_subset (fun q hq => (hpF q).trans hq)
          (by have := patchCell_subset_sublevel_patchF (hball i) hφg hμ; rwa [hgp] at this)

end Induction

/-! ### Remark 3.3 -/

/-- **The lemma of Morse on `N` in split form, inside a given neighbourhood**: as
`Morse.exists_isMorsePatch_submanifold`, with the domain of the patch inside a given open set
`U ∋ p`. -/
theorem exists_isMorsePatch_submanifold_subset [FiniteDimensional ℝ Z]
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {f : N → ℝ}
    (hf : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ f) {p : N}
    (hp : letI := hN.chartedSpace; IsNondegenerateCriticalPointM Z f p) {U : Set N}
    (hU : IsOpen U) (hpU : p ∈ U) :
    letI := hN.chartedSpace
    ∃ (sc : Milnor.SliceChart 𝓘(ℝ, V) Z W N)
      (ψ : OpenPartialHomeomorph N
        (EuclideanSpace ℝ {i : Fin (finrank ℝ Z) // (i : ℕ) < indexM Z f p} ×
          EuclideanSpace ℝ {i : Fin (finrank ℝ Z) // indexM Z f p ≤ (i : ℕ)})),
      IsMorsePatch f p ψ ∧ IsSmoothCoord Z ψ ∧
        ∀ q ∈ ψ.source, (q : V) ∈ sc.φ.source ∧ q ∈ U := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  obtain ⟨sc, hsc⟩ := hN p p.2
  have hU' : IsOpen ({q : N | (q : V) ∈ sc.φ.source} ∩ U) :=
    (sc.φ.open_source.preimage continuous_subtype_val).inter hU
  obtain ⟨y, hy, hpy, hyU, hyp, hfy⟩ := morse_lemmaM hU' ⟨hsc, hpU⟩ hf.contMDiffOn hp
  set e := splitCoord (finrank ℝ Z) (indexM Z f p) with he
  refine ⟨sc, y.transHomeomorph e.toHomeomorph, ⟨hpy, ?_, ?_⟩, ⟨?_, ?_⟩, fun q hq => hyU hq⟩
  · change e (y p) = 0
    rw [hyp, map_zero]
  · intro q hq
    rw [hfy q hq]
    change _ = morseQuad (f p) (e (y q))
    simp only [morseQuad, xi, eta, he, norm_sq_splitCoord_fst, norm_sq_splitCoord_snd]
  · exact e.contDiff.contMDiff.comp_contMDiffOn hy.contMDiffOn
  · exact hy.contMDiffOn_symm.comp e.symm.contDiff.contMDiff.contMDiffOn fun v hv => hv

/-- The cell of a Morse patch, parametrized by the closed unit ball of `ℝ^λ`: continuous and
injective, meeting `M^{c-ε}` exactly in the image of the unit sphere, and contained in
`M^{c+ε}`. -/
theorem patchCell_props {M : Type*} [TopologicalSpace M] {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] {f : M → ℝ} {p : M}
    {φ : OpenPartialHomeomorph M (X × Y)} {ε : ℝ}
    (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target) (hφ : IsMorsePatch f p φ)
    (hε : 0 < ε) {k : ℕ} (ι : X ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    let χ : EuclideanSpace ℝ (Fin k) → M := fun z => φ.symm (Real.sqrt ε • ι.symm z, 0)
    χ '' Metric.closedBall 0 1 = patchCell φ ε ∧ ContinuousOn χ (Metric.closedBall 0 1) ∧
      InjOn χ (Metric.closedBall 0 1) ∧
      (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1,
        χ z ∈ sublevel f (f p - ε) ↔ ‖z‖ = 1) ∧
      χ '' Metric.closedBall 0 1 ⊆ sublevel f (f p + ε) := by
  intro χ
  obtain ⟨himage, hcont, hinj, hval⟩ := patchCell_parametrization hball hφ hε ι
  refine ⟨himage, hcont, hinj, fun z hz => ?_, ?_⟩
  · rw [mem_sublevel, hval z hz]
    rw [mem_closedBall_zero_iff] at hz
    constructor
    · intro h
      have : 1 ≤ ‖z‖ ^ 2 := by
        by_contra h'
        nlinarith
      nlinarith [norm_nonneg z]
    · intro h
      rw [h]
      linarith
  · rintro _ ⟨z, hz, rfl⟩
    rw [mem_sublevel, hval z hz]
    nlinarith [sq_nonneg ‖z‖]

/-- **Remark 3.3** (Milnor, p. 19) for a function on a submanifold. Let `N ⊆ V` be a slice
submanifold of a finite-dimensional real normed space, `F : V → ℝ` smooth, `f = F|N`, and `S` a
finite set of non-degenerate critical points of `f`, all with value `c`. Suppose that for some
`ε₀ > 0`, `f⁻¹[c - ε₀, c + ε₀]` is compact and its critical points all lie in `S`. Then for all
sufficiently small `ε > 0` there are cells `e_p = χ_p(D^{λ_p})`, `p ∈ S`, `λ_p` the index of `p`
(each `χ_p` continuous and injective on the closed unit ball, meeting `N^{c-ε}` exactly in the
image of the unit sphere, contained in `N^{c+ε}`), pairwise disjoint, such that
`N^{c-ε} ∪ ⋃_{p ∈ S} e_p` is a strong deformation retract of `N^{c+ε}`. -/
theorem remark_3_3_submanifold [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z]
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F) {c : ℝ}
    (S : Finset N)
    (hS : letI := hN.chartedSpace;
      ∀ p ∈ S, IsNondegenerateCriticalPointM Z (F ∘ Subtype.val) p ∧ F p = c)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Icc (c - ε₀) (c + ε₀)))
    (honly : letI := hN.chartedSpace; ∀ q : N, F q ∈ Icc (c - ε₀) (c + ε₀) →
      IsCriticalPointM Z (F ∘ Subtype.val) q → q ∈ S) :
    letI := hN.chartedSpace
    ∃ ε₁ > 0, ∀ ε, 0 < ε → ε ≤ ε₁ →
      ∃ χ : (p : S) → EuclideanSpace ℝ (Fin (indexM Z (F ∘ Subtype.val : N → ℝ) (p : N))) → N,
        (∀ p : S, ContinuousOn (χ p) (Metric.closedBall 0 1) ∧ InjOn (χ p) (Metric.closedBall 0 1) ∧
          (∀ z ∈ Metric.closedBall
              (0 : EuclideanSpace ℝ (Fin (indexM Z (F ∘ Subtype.val : N → ℝ) (p : N)))) 1,
            χ p z ∈ sublevel (F ∘ Subtype.val) (c - ε) ↔ ‖z‖ = 1) ∧
          χ p '' Metric.closedBall 0 1 ⊆ sublevel (F ∘ Subtype.val) (c + ε)) ∧
        Pairwise (fun p p' => Disjoint (χ p '' Metric.closedBall 0 1)
          (χ p' '' Metric.closedBall 0 1)) ∧
        IsStrongDeformationRetract
          ((↑) ⁻¹' (sublevel (F ∘ Subtype.val) (c - ε) ∪ ⋃ p, χ p '' Metric.closedBall 0 1) :
            Set (sublevel (F ∘ Subtype.val : N → ℝ) (c + ε))) := by
  classical
  let _ := hN.chartedSpace
  have := hN.isManifold
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfs : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ f := contMDiff_comp_val hN hF
  -- Morse patches inside pairwise disjoint neighbourhoods of the critical points
  obtain ⟨U, hU, hUd⟩ := S.finite_toSet.t2_separation
  have hpatch : ∀ p : S, ∃ (sc : Milnor.SliceChart 𝓘(ℝ, V) Z W N)
      (ψ : OpenPartialHomeomorph N
        (EuclideanSpace ℝ {i : Fin (finrank ℝ Z) // (i : ℕ) < indexM Z f p} ×
          EuclideanSpace ℝ {i : Fin (finrank ℝ Z) // indexM Z f p ≤ (i : ℕ)})),
      IsMorsePatch f p ψ ∧ IsSmoothCoord Z ψ ∧
        ∀ q ∈ ψ.source, (q : V) ∈ sc.φ.source ∧ q ∈ U p := fun p =>
    exists_isMorsePatch_submanifold_subset hN hfs (hS p p.2).1 (hU p).2 (hU p).1
  choose sc ψ hφ hψ hsrc using hpatch
  have hdisj : Pairwise fun p p' : S => Disjoint (ψ p).source (ψ p').source := by
    intro p p' hpp'
    refine Set.disjoint_left.2 fun q hq hq' => ?_
    have h := hUd (Finset.mem_coe.2 p.2) (Finset.mem_coe.2 p'.2) fun h => hpp' (Subtype.ext h)
    exact Set.disjoint_left.1 h (hsrc p q hq).2 (hsrc p' q hq').2
  -- `ε` small for all patches
  have h0 : ∀ p : S, (0 : _) ∈ (ψ p).target := fun p =>
    (hφ p).apply_self ▸ (ψ p).map_source (hφ p).mem_source
  choose ε₂ hε₂ hball₂ using fun p => exists_forall_ball_subset_patch_target (h0 p)
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ p : S, δ ≤ ε₂ p := by
    by_cases hne : Nonempty S
    · obtain ⟨p₀, hp₀⟩ := Finite.exists_min ε₂
      exact ⟨ε₂ p₀, hε₂ p₀, hp₀⟩
    · exact ⟨1, one_pos, fun p => (hne ⟨p⟩).elim⟩
  refine ⟨min ε₀ δ, lt_min hε₀ hδ, fun ε hε hεε₁ => ?_⟩
  have hball : ∀ p : S, {v | xi v + eta v ≤ 2 * ε} ⊆ (ψ p).target := fun p =>
    hball₂ p ε (hεε₁.trans ((min_le_right _ _).trans (hδle p)))
  have hεε₀ : ε ≤ ε₀ := hεε₁.trans (min_le_left _ _)
  have hμ := isMilnorMu_milnorMu hε
  set μ := milnorMu ε with hμ_def
  -- the bumps, extended to `V`
  have hext : ∀ p : S, ∃ B : V → ℝ, ContDiff ℝ ∞ B ∧ B ∘ Subtype.val = patchBump (ψ p) μ :=
    fun p => exists_contDiff_comp_val_eq_of_chart hN (sc p)
      (contMDiff_patchBump hN (hψ p) (hball p) hμ) (isCompact_patchEllipsoid (hball p))
      (fun q hq => (hsrc p q (patchEllipsoid_subset_source (hball p) hq)).1)
      (fun q hq => patchBump_eq_zero (hball p) hμ hq)
  choose B hB hBN using hext
  obtain ⟨h1, h2, h3, h4, h5⟩ := multi_induction hN hF (p := fun p : S => (p : N)) hφ hψ
    (fun p => (hS p p.2).2) hdisj hball hμ hB hBN Finset.univ
  set G := multiF F B Finset.univ with hG_def
  have hG : ContDiff ℝ ∞ G := contDiff_multiF hF hB _
  have hGle : ∀ q : N, G q ≤ F q := fun q => by
    simp only [hG_def, multiF]
    refine sub_le_self _ (Finset.sum_nonneg fun p _ => ?_)
    have := congrFun (hBN p) q
    simp only [Function.comp_apply] at this
    rw [this]
    exact indicator_nonneg (fun _ _ => hμ.nonneg _) _
  -- Assertion 3: Theorem 3.1 for `G`
  have hsub : (G ∘ Subtype.val : N → ℝ) ⁻¹' Icc (c - ε) (c + ε) ⊆
      f ⁻¹' Icc (c - ε₀) (c + ε₀) := by
    intro q hq
    have hq2 : q ∈ sublevel f (c + ε) := h1 ▸ hq.2
    have a1 : c - ε ≤ G q := hq.1
    have a2 : G q ≤ F q := hGle q
    have a3 : F q ≤ c + ε := hq2
    exact ⟨show c - ε₀ ≤ F q by linarith, show F q ≤ c + ε₀ by linarith⟩
  have hK' : IsCompact ((G ∘ Subtype.val : N → ℝ) ⁻¹' Icc (c - ε) (c + ε)) :=
    hK.of_isClosed_subset (isClosed_Icc.preimage (hG.continuous.comp continuous_subtype_val)) hsub
  have hcrit : ∀ q : N, G q ∈ Icc (c - ε) (c + ε) →
      ¬IsCriticalPointM Z (G ∘ Subtype.val) q := by
    intro q hq hc
    have hqS := honly q (hsub hq) ((h2 q).1 hc)
    have := h3 ⟨q, hqS⟩ (Finset.mem_univ _)
    have h' : G q = c - μ 0 := this
    linarith [hq.1, hμ.lt_apply_zero]
  have hA3 := (theorem_3_1_submanifold hN hG (by linarith) hK' hcrit).2.1
  rw [h1] at hA3
  -- the cells
  have hk : ∀ p : S, indexM Z f p ≤ finrank ℝ Z := fun p => indexM_le_finrank f p
  let ι : (p : S) → EuclideanSpace ℝ {i : Fin (finrank ℝ Z) // (i : ℕ) < indexM Z f p} ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (indexM Z f p)) := fun p =>
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (negIdxEquiv (hk p))
  have hprops := fun p : S => patchCell_props (hball p) (hφ p) hε (ι p)
  refine ⟨fun p z => (ψ p).symm (Real.sqrt ε • (ι p).symm z, 0), fun p => ?_, ?_, ?_⟩
  · obtain ⟨-, hcont, hinj, hbdry, hsub'⟩ := hprops p
    have hfp : f p = c := (hS p p.2).2
    rw [hfp] at hbdry hsub'
    exact ⟨hcont, hinj, hbdry, hsub'⟩
  · intro p p' hpp'
    rw [(hprops p).1, (hprops p').1]
    exact (hdisj hpp').mono
      ((image_mono cellModel_subset_ellipsoid).trans (patchEllipsoid_subset_source (hball p)))
      ((image_mono cellModel_subset_ellipsoid).trans (patchEllipsoid_subset_source (hball p')))
  · have hU : (⋃ p : S, (fun z => (ψ p).symm (Real.sqrt ε • (ι p).symm z, 0)) ''
        Metric.closedBall 0 1) = ⋃ p ∈ (Finset.univ : Finset S), patchCell (ψ p) ε := by
      simp only [Finset.mem_univ, iUnion_true]
      exact iUnion_congr fun p => (hprops p).1
    rw [hU]
    refine IsStrongDeformationRetract.trans (union_subset (fun q hq => (hGle q).trans hq)
      (iUnion₂_subset fun p _ => h4 p (Finset.mem_univ _))) ?_ h5 hA3
    rw [← h1]
    exact sublevel_mono _ (by linarith)

end Morse
