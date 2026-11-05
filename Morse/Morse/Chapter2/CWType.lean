import Morse.Chapter2.Attaching
import Morse.Chapter2.SeveralCritical

/-!
Milnor, *Morse Theory*, §3, p. 20 (statement) and pp. 23–24 (proof): Theorem 3.5, for a compact
submanifold of Euclidean space.

# One cell for each critical point

**Theorem 3.5** (p. 20), paraphrased: if `f` is a differentiable function on a manifold `M` with no
degenerate critical points, and each `M^a` is compact, then `M` has the homotopy type of a
CW-complex with one cell of dimension `λ` for each critical point of index `λ`.

Milnor's proof (pp. 23–24): list the critical values `c₁ < c₂ < ⋯`; `M^a` is empty for `a < c₁`;
for `a` regular and `c` the smallest critical value above `a`, Theorems 3.1, 3.2 and Remark 3.3 give
`M^{c+ε} ≃ M^{c-ε} ∪ e^{λ₁} ∪ ⋯` and a homotopy equivalence `h : M^{c-ε} → M^a`; if
`h' : M^a → K` is a homotopy equivalence to a CW-complex, each `h' ∘ h ∘ φ_j` is homotopic, by
cellular approximation, to a map `ψ_j` into the `(λ_j - 1)`-skeleton of `K`, and
`K ∪_{ψ₁} e^{λ₁} ∪ ⋯` is a CW-complex homotopy equivalent to `M^{c+ε}` by Lemmas 3.6 and 3.7. The
non-compact case is finished with Whitehead's theorem.

## What is proved here, and how it differs from Milnor's statement

* **The manifold** is a compact slice submanifold `N` of a finite-dimensional real normed space `V`
  (Milnor's `ℝᴷ`, the companion project's `Milnor.IsSliceSubmanifold`), and `f = F|N` is the
  restriction of a smooth `F : V → ℝ` all of whose critical points on `N` are non-degenerate: the
  setting of `Morse.theorem_3_1_submanifold` and `Morse.theorem_3_2_submanifold`. Then every `N^a`
  is compact. The non-compact case (infinitely many critical points, Whitehead's theorem, the
  Appendix) is not done.
* **One critical point per critical value**, the case the task statement singles out, is
  `Morse.theorem_3_5` (hypothesis `hdist`: distinct critical points have distinct values), proved
  with Theorem 3.2 one point at a time. The general case, several critical points on a level, is
  `Morse.theorem_3_5'`, proved with Remark 3.3 (`Morse.remark_3_3_submanifold`); there the
  critical points are listed by non-decreasing value, those on one level in some order.
* **"CW-complex" is replaced by an iterated adjunction space.** `Morse.IsCellAttachment K cells`
  says that `K` is obtained from the empty space by attaching cells of the dimensions listed in
  `cells`, one at a time and in the order of the list, each along an arbitrary continuous map
  `S^{λ-1} → (the space built so far)`, the attaching space being the pushout in `TopCat`
  (`Morse.AttachCell`). `Morse.IsFiniteCellComplexType X cells` says that `X` is homotopy
  equivalent to such a `K`. The differences with Milnor's (J. H. C. Whitehead's) finite
  CW-complexes:
  - the attaching maps are arbitrary, not cellular. Milnor makes them cellular by the cellular
    approximation theorem (the attaching map of a `λ`-cell is homotopic to one into the
    `(λ-1)`-skeleton) and then replaces them by Lemma 3.6. Cellular approximation is not in
    Mathlib, so only Lemma 3.7 is used in the induction below;
  - the cells are attached in order of increasing critical value, not of dimension. An iterated
    adjunction space whose cells are attached in order of non-decreasing dimension, each along a
    map into the union of the cells of smaller dimension, is a finite CW-complex with these cells.
    Without the last condition it is still homotopy equivalent to one, with the same number of
    cells in each dimension (cellular approximation and Lemmas 3.6, 3.7), but not necessarily
    homeomorphic to one with these cells.
  The dimensions, and the number of cells of each dimension, are those of Milnor's statement:
  `cells` is the list of the indices of the critical points, in order of critical value
  (`Morse.theorem_3_5_count'`).
* **The Remark on p. 24** (each `M^a` has the homotopy type of a finite complex with one cell per
  critical point in `M^a`) is proved for regular values `a`
  (`Morse.isFiniteCellComplexType_sublevel`, `Morse.isFiniteCellComplexType_sublevel'`), which is
  the induction itself; for a critical value it would need Remark 3.4 on `N`, not done.

## What Milnor's text leaves implicit

* **"The set `M^a` is vacuous for `a < c₁`"** (p. 23): if `M^a ≠ ∅`, the minimum of `f` on the
  compact `M` is attained at a point which is critical (`Morse.isCriticalPointM_of_forall_le`) and
  lies in `M^a`. So `N^a = ∅` when no critical value is `≤ a`.
* **The induction runs over regular values.** Between the regular values `a' < c < a` with only the
  critical value `c` in `[a', a]`, the proof chooses `ε` smaller than both `c - a'`, `a - c` and the
  `ε₁` of Theorem 3.2, and applies Theorem 3.1 on `[a', c - ε]` and `[c + ε, a]`
  (`Morse.IsFiniteCellComplexType.sublevel_step`). The hypotheses of Theorem 3.2 at `p` (a compact
  slab containing no other critical point) hold with `ε₀ = min(c - a', a - c)`.
* **The cells are transported through homotopy equivalences** by Lemma 3.7: if `M^{c-ε} ≃ K`, then
  `M^{c-ε} ∪_φ e^λ ≃ K ∪_{hφ} e^λ` (`Morse.IsFiniteCellComplexType.attach`). Milnor's "by Lemmas
  3.6, 3.7" (p. 23).
* **Several cells on one level are attached one at a time**: by Lemma D, since the cells of
  Remark 3.3 are disjoint, `e^{λ_j}` meets `M^{c-ε} ∪ e^{λ₁} ∪ ⋯ ∪ e^{λ_{j-1}}` exactly in its
  boundary (`Morse.isFiniteCellComplexType_union_cells`).

## Main results

* `Morse.IsCellAttachment`, `Morse.IsFiniteCellComplexType`, `Morse.IsFiniteCellComplexType.attach`.
* `Morse.isCriticalPointM_of_forall_le`: a global minimum is a critical point.
* `Morse.isFiniteCellComplexType_sublevel`: for every regular value `a`, `N^a` has the homotopy type
  of an iterated adjunction space with one cell of dimension `λ` for each critical point of index
  `λ` in `N^a`, attached in order of critical value.
* `Morse.theorem_3_5`: **Theorem 3.5** for compact `N` and distinct critical values: listing the
  critical points `p₁, …, p_k` of `f` by increasing value, `N` has the homotopy type of the space
  obtained from `∅` by attaching cells of dimensions `index(p₁), …, index(p_k)`, one at a time.
* `Morse.theorem_3_5_count`: the same, counted: `N` has the homotopy type of an iterated adjunction
  space with exactly `C_λ` cells of dimension `λ`, `C_λ` the number of critical points of index `λ`.
* `Morse.isFiniteCellComplexType_union_cells`, `Morse.IsFiniteCellComplexType.sublevel_step_finset`,
  `Morse.isFiniteCellComplexType_sublevel'`: the same with several critical points on a level.
* `Morse.theorem_3_5'`, `Morse.theorem_3_5_count'`: **Theorem 3.5** for compact `N` and any `F`
  whose critical points on `N` are non-degenerate.
-/

open Set Filter Topology Function Module CategoryTheory Limits TopCat
open scoped ContDiff Manifold

universe u

noncomputable section

namespace Morse

/-! ### Iterated adjunction spaces -/

/-- **Iterated adjunction spaces.** `IsCellAttachment K cells`: the space `K` is obtained from the
empty space by attaching cells of the dimensions listed in `cells`, one at a time and in the order
of the list, each along an arbitrary continuous map of its boundary sphere into the space built so
far (the attaching space being the pushout `Morse.AttachCell φ` in `TopCat`). -/
inductive IsCellAttachment : TopCat.{u} → List ℕ → Prop
  | empty : IsCellAttachment (TopCat.of PEmpty) []
  | attach {K : TopCat.{u}} {cells : List ℕ} (hK : IsCellAttachment K cells) (n : ℕ)
      (φ : ∂𝔻 n ⟶ K) : IsCellAttachment (AttachCell φ) (cells ++ [n])

/-- **`X` has the homotopy type of a finite cell complex with cells of dimensions `cells`**: it is
homotopy equivalent to a space obtained from the empty space by attaching cells of these dimensions
one at a time, in this order, along arbitrary continuous attaching maps (`Morse.IsCellAttachment`).
See the module docstring for the comparison with CW-complexes. -/
def IsFiniteCellComplexType (X : Type u) [TopologicalSpace X] (cells : List ℕ) : Prop :=
  ∃ K : TopCat.{u}, IsCellAttachment K cells ∧ Nonempty (ContinuousMap.HomotopyEquiv X K)

namespace IsFiniteCellComplexType

/-- The empty space has the homotopy type of the complex without cells. -/
theorem of_isEmpty (X : Type u) [TopologicalSpace X] [IsEmpty X] :
    IsFiniteCellComplexType X [] :=
  ⟨TopCat.of PEmpty, .empty, ⟨(Homeomorph.empty : X ≃ₜ PEmpty).toHomotopyEquiv⟩⟩

/-- The property is invariant under homotopy equivalence. -/
theorem of_homotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {cells : List ℕ} (h : IsFiniteCellComplexType Y cells) (e : ContinuousMap.HomotopyEquiv X Y) :
    IsFiniteCellComplexType X cells := by
  obtain ⟨K, hK, ⟨e'⟩⟩ := h
  exact ⟨K, hK, ⟨e.trans e'⟩⟩

/-- **Attaching a cell** (Milnor, p. 23, "by Lemmas 3.6, 3.7"): if `X` is homotopy equivalent to an
iterated adjunction space `K` with cells `cells`, then `X ∪_φ e^n` is homotopy equivalent to the
iterated adjunction space `K ∪_{hφ} e^n` with cells `cells ++ [n]` (Lemma 3.7). -/
theorem attach {X : TopCat.{u}} {cells : List ℕ} (h : IsFiniteCellComplexType X cells) (n : ℕ)
    (φ : ∂𝔻 n ⟶ X) : IsFiniteCellComplexType (AttachCell φ) (cells ++ [n]) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := h
  obtain ⟨F, -, -⟩ := lemma_3_7 φ e
  exact ⟨_, hK.attach n (φ ≫ TopCat.ofHom e.toFun), ⟨F⟩⟩

end IsFiniteCellComplexType

/-! ### Minima are critical points -/

/-- **A global minimum is a critical point** (used for "`M^a` is vacuous for `a < c₁`", p. 23): the
local representative in the preferred chart has a minimum at the image of the point. -/
theorem isCriticalPointM_of_forall_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (hp : ∀ x, f p ≤ f x) : IsCriticalPointM E f p := by
  rw [isCriticalPointM_iff_fderiv]
  refine IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun u => ?_)
  rw [localRep_self]
  exact hp _

/-! ### Theorem 3.5 for a compact submanifold -/

section Submanifold

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V}

/-- **Passing one critical level** (Milnor, p. 23). Let `p` be a non-degenerate critical point of
`f = F|N`, `c = f(p)`, and `a' < c < a` such that no other critical value of `f` lies in `[a', a]`.
If `N^{a'}` has the homotopy type of an iterated adjunction space with cells `cells`, then `N^a` has
that of one with cells `cells ++ [λ]`, `λ` the index of `p`. Theorem 3.1 on `[a', c - ε]` and
`[c + ε, a]`, Theorem 3.2 at `p`, and Lemma 3.7. -/
theorem IsFiniteCellComplexType.sublevel_step (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F) {p : N}
    (hp : letI := hN.chartedSpace; IsNondegenerateCriticalPointM Z (F ∘ Subtype.val) p)
    {a' a : ℝ} (ha' : a' < F p) (ha : F p < a)
    (hother : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q → q ≠ p →
      F q < a' ∨ a < F q)
    {cells : List ℕ} (h : IsFiniteCellComplexType (sublevel (F ∘ Subtype.val : N → ℝ) a') cells) :
    letI := hN.chartedSpace
    IsFiniteCellComplexType (sublevel (F ∘ Subtype.val : N → ℝ) a)
      (cells ++ [indexM Z (F ∘ Subtype.val) p]) := by
  let _ := hN.chartedSpace
  have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfc : Continuous f := hF.continuous.comp continuous_subtype_val
  set ε₀ := min (F p - a') (a - F p) with hε₀_def
  have hε₀ : 0 < ε₀ := lt_min (by linarith) (by linarith)
  have hK : IsCompact (f ⁻¹' Icc (F p - ε₀) (F p + ε₀)) := (isClosed_Icc.preimage hfc).isCompact
  have honly : ∀ q : N, F q ∈ Icc (F p - ε₀) (F p + ε₀) → IsCriticalPointM Z f q → q = p := by
    intro q hq hc
    by_contra hqp
    rcases hother q hc hqp with h1 | h1
    · linarith [hq.1, min_le_left (F p - a') (a - F p)]
    · linarith [hq.2, min_le_right (F p - a') (a - F p)]
  obtain ⟨ε₁, hε₁, H⟩ := theorem_3_2_attach_submanifold hN hF hp hε₀ hK honly
  set ε := min ε₁ (ε₀ / 2) with hε_def
  have hε : 0 < ε := lt_min hε₁ (by linarith)
  have hεε₀ : ε < ε₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h1 : ε < F p - a' := lt_of_lt_of_le hεε₀ (min_le_left _ _)
  have h2 : ε < a - F p := lt_of_lt_of_le hεε₀ (min_le_right _ _)
  obtain ⟨φ, -, ⟨e₁⟩⟩ := H ε hε (min_le_left _ _)
  -- no critical values in `[a', c - ε]` and `[c + ε, a]`
  have hno : ∀ {b b' : ℝ}, a' ≤ b → b' ≤ a → (b' < F p ∨ F p < b) →
      ∀ q : N, F q ∈ Icc b b' → ¬IsCriticalPointM Z f q := by
    intro b b' hb hb' hbp q hq hc
    by_cases hqp : q = p
    · subst hqp
      rcases hbp with h | h <;> linarith [hq.1, hq.2]
    · rcases hother q hc hqp with h | h <;> linarith [hq.1, hq.2]
  obtain ⟨e₂, -⟩ := (theorem_3_1_submanifold_of_isCompact hN hNc hF (a := a') (b := F p - ε)
    (by linarith) (hno le_rfl (by linarith) (Or.inl (by linarith)))).2.2
  obtain ⟨e₃, -⟩ := (theorem_3_1_submanifold_of_isCompact hN hNc hF (a := F p + ε) (b := a)
    (by linarith) (hno (by linarith) le_rfl (Or.inr (by linarith)))).2.2
  have h4 : IsFiniteCellComplexType (TopCat.of (sublevel f (F p - ε))) cells :=
    h.of_homotopyEquiv e₂.symm
  exact (h4.attach _ φ).of_homotopyEquiv (e₃.symm.trans e₁)

/-- **Every regular sublevel set has the homotopy type of an iterated adjunction space with one
cell per critical point below it** (Milnor, p. 23: the induction over the regular values `a'`, and
the Remark on p. 24). Let `N` be compact, `f = F|N` with
non-degenerate critical points and distinct critical values, and `a` not a critical value. Then,
listing the critical points `p₁, …, p_j` with `f(pᵢ) < a` by increasing value, `N^a` has the
homotopy type of the space obtained from `∅` by attaching cells of dimensions
`index(p₁), …, index(p_j)`, one at a time. -/
theorem isFiniteCellComplexType_sublevel (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q))
    (hdist : letI := hN.chartedSpace; ∀ q q' : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsCriticalPointM Z (F ∘ Subtype.val) q' → F q = F q' → q = q')
    (a : ℝ) (ha : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      F q ≠ a) :
    letI := hN.chartedSpace
    ∃ ps : List N, ps.Nodup ∧
      (∀ q, q ∈ ps ↔ IsCriticalPointM Z (F ∘ Subtype.val) q ∧ F q < a) ∧
      ps.Pairwise (fun q q' : N => F q < F q') ∧
      IsFiniteCellComplexType (sublevel (F ∘ Subtype.val : N → ℝ) a)
        (ps.map (indexM Z (F ∘ Subtype.val))) := by
  classical
  let _ := hN.chartedSpace
  have := hN.isManifold
  have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfc : Continuous f := hF.continuous.comp continuous_subtype_val
  have hMorse : IsMorseFunction Z f := ⟨contMDiff_comp_val hN hF, hnd⟩
  have hfin := hMorse.finite_setOf_isCriticalPointM
  -- strong induction on the number of critical points below the level
  suffices key : ∀ m : ℕ, ∀ a : ℝ, (hfin.toFinset.filter (fun q : N => F q < a)).card = m →
      (∀ q : N, IsCriticalPointM Z f q → F q ≠ a) →
      ∃ ps : List N, ps.Nodup ∧ (∀ q, q ∈ ps ↔ IsCriticalPointM Z f q ∧ F q < a) ∧
        ps.Pairwise (fun q q' : N => F q < F q') ∧
        IsFiniteCellComplexType (sublevel f a) (ps.map (indexM Z f)) from key _ a rfl ha
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a hm ha
  by_cases hS : (hfin.toFinset.filter (fun q : N => F q < a)).Nonempty
  · -- `p`: the highest critical point below `a`
    obtain ⟨p, hpS, hpmax⟩ := Finset.exists_max_image _ (fun q : N => F q) hS
    have hpc : IsCriticalPointM Z f p := hfin.mem_toFinset.1 (Finset.mem_filter.1 hpS).1
    have hpa : F p < a := (Finset.mem_filter.1 hpS).2
    -- a regular value `a'` just below `F p`
    obtain ⟨a', ha'p, hTa'⟩ : ∃ a', a' < F p ∧
        ∀ q ∈ hfin.toFinset.filter (fun q : N => F q < F p), F q < a' := by
      by_cases hT : (hfin.toFinset.filter (fun q : N => F q < F p)).Nonempty
      · obtain ⟨q₀, hq₀T, hq₀max⟩ := Finset.exists_max_image _ (fun q : N => F q) hT
        have : F q₀ < F p := (Finset.mem_filter.1 hq₀T).2
        exact ⟨(F q₀ + F p) / 2, by linarith, fun q hq => by have := hq₀max q hq; linarith⟩
      · exact ⟨F p - 1, by linarith, fun q hq => absurd ⟨q, hq⟩ hT⟩
    have hother : ∀ q : N, IsCriticalPointM Z f q → q ≠ p → F q < a' ∨ a < F q := by
      intro q hq hqp
      rcases lt_trichotomy (F q) (F p) with h | h | h
      · exact Or.inl (hTa' q (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hq, h⟩))
      · exact absurd (hdist q p hq hpc h) hqp
      · right
        by_contra hle
        have hqa : F q < a := lt_of_le_of_ne (not_lt.1 hle) (ha q hq)
        have := hpmax q (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hq, hqa⟩)
        linarith
    have ha'reg : ∀ q : N, IsCriticalPointM Z f q → F q ≠ a' := by
      intro q hq heq
      by_cases hqp : q = p
      · subst hqp
        linarith
      · rcases hother q hq hqp with h | h <;> linarith
    have hfilter : hfin.toFinset.filter (fun q : N => F q < a') =
        (hfin.toFinset.filter (fun q : N => F q < a)).erase p := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hq, hqa'⟩
        exact ⟨by rintro rfl; linarith, hq, by linarith⟩
      · rintro ⟨hqp, hq, hqa⟩
        refine ⟨hq, ?_⟩
        rcases hother q (hfin.mem_toFinset.1 hq) hqp with h | h
        · exact h
        · linarith
    have hcard : (hfin.toFinset.filter (fun q : N => F q < a')).card < m := by
      rw [hfilter, ← hm]
      exact Finset.card_erase_lt_of_mem hpS
    obtain ⟨ps', hnd', hmem', hsort', hcell'⟩ := ih _ hcard a' rfl ha'reg
    have hp' : p ∉ ps' := fun h => by linarith [((hmem' p).1 h).2]
    refine ⟨ps' ++ [p], ?_, fun q => ?_, ?_, ?_⟩
    · exact hnd'.append (List.nodup_singleton p)
        (List.disjoint_singleton.2 hp')
    · rw [List.mem_append, List.mem_singleton, hmem']
      constructor
      · rintro (⟨hq, hqa'⟩ | rfl)
        · exact ⟨hq, by linarith⟩
        · exact ⟨hpc, hpa⟩
      · rintro ⟨hq, hqa⟩
        by_cases hqp : q = p
        · exact Or.inr hqp
        · refine Or.inl ⟨hq, ?_⟩
          rcases hother q hq hqp with h | h
          · exact h
          · linarith
    · rw [List.pairwise_append]
      refine ⟨hsort', List.pairwise_singleton _ _, fun q hq q' hq' => ?_⟩
      rw [List.mem_singleton] at hq'
      subst hq'
      have := ((hmem' q).1 hq).2
      linarith
    · rw [List.map_append, List.map_singleton]
      exact IsFiniteCellComplexType.sublevel_step hN hNc hF ⟨hpc, hnd p hpc⟩ ha'p hpa hother
        hcell'
  · -- no critical point below `a`: `N^a` is empty ("vacuous for `a < c₁`")
    have hempty : sublevel f a = ∅ := by
      by_contra hne
      obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.2 hne
      obtain ⟨q₀, -, hq₀⟩ := isCompact_univ.exists_isMinOn ⟨q, mem_univ q⟩ hfc.continuousOn
      have hc : IsCriticalPointM Z f q₀ :=
        isCriticalPointM_of_forall_le fun x => hq₀ (mem_univ x)
      have hq₀a : F q₀ < a := lt_of_le_of_ne ((hq₀ (mem_univ q)).trans hq) (ha q₀ hc)
      exact hS ⟨q₀, Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hc, hq₀a⟩⟩
    refine ⟨[], List.nodup_nil, fun q => ?_, List.Pairwise.nil, ?_⟩
    · simp only [List.not_mem_nil, false_iff, not_and]
      intro hc hqa
      exact hS ⟨q, Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hc, hqa⟩⟩
    · have : IsEmpty (sublevel f a) := Set.isEmpty_coe_sort.2 hempty
      exact IsFiniteCellComplexType.of_isEmpty _

/-- **Theorem 3.5** (Milnor, p. 20) for a compact submanifold of Euclidean space and a Morse
function with distinct critical values. Let `N ⊆ V` be a compact slice submanifold and
`F : V → ℝ` smooth, and suppose that all critical points of `f = F|N` are non-degenerate and have
distinct values. Then the critical points of `f` can be listed as `p₁, …, p_k` with
`f(p₁) < ⋯ < f(p_k)`, and `N` has the homotopy type of the space obtained from the empty space by
attaching cells of dimensions `index(p₁), …, index(p_k)`, one at a time and in this order, along
continuous attaching maps. -/
theorem theorem_3_5 (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (hNc : IsCompact N)
    {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q))
    (hdist : letI := hN.chartedSpace; ∀ q q' : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsCriticalPointM Z (F ∘ Subtype.val) q' → F q = F q' → q = q') :
    letI := hN.chartedSpace
    ∃ ps : List N, ps.Nodup ∧ (∀ q, q ∈ ps ↔ IsCriticalPointM Z (F ∘ Subtype.val) q) ∧
      ps.Pairwise (fun q q' : N => F q < F q') ∧
      IsFiniteCellComplexType N (ps.map (indexM Z (F ∘ Subtype.val))) := by
  let _ := hN.chartedSpace
  have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfc : Continuous f := hF.continuous.comp continuous_subtype_val
  obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image hfc.continuousOn
  have hle : ∀ q : N, F q < M + 1 := fun q => by
    have := hM ⟨q, mem_univ q, rfl⟩
    change f q ≤ M at this
    simp only [hf_def, comp_apply] at this
    linarith
  obtain ⟨ps, h1, h2, h3, h4⟩ :=
    isFiniteCellComplexType_sublevel hN hNc hF hnd hdist (M + 1) fun q _ => (hle q).ne
  refine ⟨ps, h1, fun q => (h2 q).trans (and_iff_left (hle q)), h3, h4.of_homotopyEquiv ?_⟩
  have huniv : sublevel f (M + 1) = univ := eq_univ_of_forall fun q => (hle q).le
  exact ((Homeomorph.Set.univ N).symm.trans (Homeomorph.setCongr huniv.symm)).toHomotopyEquiv

/-- **Theorem 3.5, counting cells** (Milnor, p. 20: "one cell of dimension `λ` for each critical
point of index `λ`"): under the hypotheses of `Morse.theorem_3_5`, `N` has the homotopy type of an
iterated adjunction space whose number of cells of dimension `λ` is, for every `λ`, the number
`C_λ` of critical points of `f` of index `λ`. -/
theorem theorem_3_5_count (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (hNc : IsCompact N)
    {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q))
    (hdist : letI := hN.chartedSpace; ∀ q q' : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsCriticalPointM Z (F ∘ Subtype.val) q' → F q = F q' → q = q') :
    letI := hN.chartedSpace
    ∃ cells : List ℕ, IsFiniteCellComplexType N cells ∧ ∀ k : ℕ, cells.count k =
      {q : N | IsCriticalPointM Z (F ∘ Subtype.val) q ∧
        indexM Z (F ∘ Subtype.val) q = k}.ncard := by
  let _ := hN.chartedSpace
  classical
  obtain ⟨ps, hnd', hmem, -, hcell⟩ := theorem_3_5 hN hNc hF hnd hdist
  refine ⟨_, hcell, fun k => ?_⟩
  have hset : {q : N | IsCriticalPointM Z (F ∘ Subtype.val) q ∧
      indexM Z (F ∘ Subtype.val) q = k} =
      ↑(ps.filter (fun q => indexM Z (F ∘ Subtype.val) q = k)).toFinset := by
    ext q
    simp [hmem]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hnd'.filter _), List.count,
    List.countP_map, List.countP_eq_length_filter]
  rfl

end Submanifold

/-! ### Several critical points on one level -/

/-- **Attaching disjoint cells one at a time** (Lemma D, repeatedly; Remark 3.3). Let `A` be a
closed subset of a Hausdorff space, and `χᵢ`, for `i` in a list `l`, maps of closed unit balls,
continuous and injective, with pairwise disjoint images, each meeting `A` exactly in the image of
the unit sphere. If `A` has the homotopy type of an iterated adjunction space with cells `cells`,
then `A ∪ ⋃_{i ∈ l} χᵢ(D)` has that of one with cells `cells` followed by the dimensions of the
`χᵢ`, `i ∈ l`. -/
theorem isFiniteCellComplexType_union_cells {M : Type u} [TopologicalSpace M] [T2Space M]
    {ι : Type*} {k : ι → ℕ} (χ : (i : ι) → EuclideanSpace ℝ (Fin (k i)) → M) :
    ∀ (l : List ι) {A : Set M} {cells : List ℕ}, IsClosed A → IsFiniteCellComplexType A cells →
      (∀ i ∈ l, ContinuousOn (χ i) (Metric.closedBall 0 1) ∧
        InjOn (χ i) (Metric.closedBall 0 1) ∧
        ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k i))) 1, χ i z ∈ A ↔ ‖z‖ = 1) →
      l.Pairwise (fun i j => Disjoint (χ i '' Metric.closedBall 0 1)
        (χ j '' Metric.closedBall 0 1)) →
      IsFiniteCellComplexType ↥(A ∪ ⋃ i ∈ l, χ i '' Metric.closedBall 0 1) (cells ++ l.map k) := by
  intro l
  induction l with
  | nil =>
    intro A cells _ h _ _
    have hs : A ∪ ⋃ i ∈ ([] : List ι), χ i '' Metric.closedBall 0 1 = A := by simp
    rw [List.map_nil, List.append_nil]
    exact h.of_homotopyEquiv (Homeomorph.setCongr hs).toHomotopyEquiv
  | cons i l ih =>
    intro A cells hA h hprops hdisj
    obtain ⟨hcont, hinj, hbdry⟩ := hprops i (List.mem_cons_self ..)
    obtain ⟨φ, χ', -, -, hpo⟩ := exists_isPushout_union_cell_of_t2 hA hcont hinj hbdry
    set A' := A ∪ χ i '' Metric.closedBall 0 1 with hA'_def
    have hA' : IsClosed A' :=
      hA.union ((isCompact_closedBall _ _).image_of_continuousOn hcont).isClosed
    have h' : IsFiniteCellComplexType A' (cells ++ [k i]) := by
      have h1 : IsFiniteCellComplexType (TopCat.of A) cells := h
      exact (h1.attach (k i) φ).of_homotopyEquiv (homeoOfIso hpo.isoPushout).toHomotopyEquiv
    rw [List.pairwise_cons] at hdisj
    have hprops' : ∀ j ∈ l, ContinuousOn (χ j) (Metric.closedBall 0 1) ∧
        InjOn (χ j) (Metric.closedBall 0 1) ∧
        ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k j))) 1, χ j z ∈ A' ↔ ‖z‖ = 1 := by
      intro j hj
      obtain ⟨hcj, hij, hbj⟩ := hprops j (List.mem_cons_of_mem _ hj)
      refine ⟨hcj, hij, fun z hz => ⟨fun hzA => ?_, fun hz1 => Or.inl ((hbj z hz).2 hz1)⟩⟩
      rcases hzA with hzA | hzA
      · exact (hbj z hz).1 hzA
      · exact absurd (Set.disjoint_left.1 (hdisj.1 j hj) hzA (mem_image_of_mem _ hz)) not_false
    have := ih hA' h' hprops' hdisj.2
    have hs : A ∪ ⋃ j ∈ i :: l, χ j '' Metric.closedBall 0 1 =
        A' ∪ ⋃ j ∈ l, χ j '' Metric.closedBall 0 1 := by
      ext q
      simp only [hA'_def, mem_union, mem_iUnion, List.mem_cons, exists_prop]
      constructor
      · rintro (h | ⟨j, rfl | hj, hq⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr hq)
        · exact Or.inr ⟨j, hj, hq⟩
      · rintro ((h | h) | ⟨j, hj, hq⟩)
        · exact Or.inl h
        · exact Or.inr ⟨i, Or.inl rfl, h⟩
        · exact Or.inr ⟨j, Or.inr hj, hq⟩
    rw [List.map_cons, show cells ++ k i :: l.map k = (cells ++ [k i]) ++ l.map k by simp]
    exact this.of_homotopyEquiv (Homeomorph.setCongr hs).toHomotopyEquiv

section SubmanifoldSeveral

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V}

/-- **Passing one critical level with several critical points** (Milnor, p. 23, with Remark 3.3).
Let `S` be the set of critical points of `f = F|N` with value `c`, all non-degenerate, and
`a' < c < a` such that no other critical value lies in `[a', a]`. If `N^{a'}` has the homotopy type
of an iterated adjunction space with cells `cells`, then, for some enumeration `l` of `S`, `N^a`
has that of one with cells `cells` followed by the indices of the points of `l`. -/
theorem IsFiniteCellComplexType.sublevel_step_finset
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (hNc : IsCompact N) {F : V → ℝ}
    (hF : ContDiff ℝ ∞ F) {S : Finset N} {c : ℝ}
    (hS : letI := hN.chartedSpace;
      ∀ p ∈ S, IsNondegenerateCriticalPointM Z (F ∘ Subtype.val) p ∧ F p = c)
    {a' a : ℝ} (ha' : a' < c) (ha : c < a)
    (hother : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q → q ∉ S →
      F q < a' ∨ a < F q)
    {cells : List ℕ} (h : IsFiniteCellComplexType (sublevel (F ∘ Subtype.val : N → ℝ) a') cells) :
    letI := hN.chartedSpace
    ∃ l : List N, l.Nodup ∧ (∀ q, q ∈ l ↔ q ∈ S) ∧
      IsFiniteCellComplexType (sublevel (F ∘ Subtype.val : N → ℝ) a)
        (cells ++ l.map (indexM Z (F ∘ Subtype.val))) := by
  classical
  let _ := hN.chartedSpace
  have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
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
  obtain ⟨ε₁, hε₁, H⟩ := remark_3_3_submanifold hN hF S hS hε₀ hK honly
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
  obtain ⟨e₂, -⟩ := (theorem_3_1_submanifold_of_isCompact hN hNc hF (a := a') (b := c - ε)
    (by linarith) (hno le_rfl (by linarith) (Or.inl (by linarith)))).2.2
  obtain ⟨e₃, -⟩ := (theorem_3_1_submanifold_of_isCompact hN hNc hF (a := c + ε) (b := a)
    (by linarith) (hno (by linarith) le_rfl (Or.inr (by linarith)))).2.2
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

/-- **Every regular sublevel set has the homotopy type of an iterated adjunction space with one
cell per critical point below it**, without assuming distinct critical values (Milnor, p. 23, with
Remark 3.3, and the Remark on p. 24, for regular values). The critical points `p₁, …, p_j` with
`f(pᵢ) < a` can be listed with `f(p₁) ≤ ⋯ ≤ f(p_j)` so that `N^a` has the homotopy type of the
space obtained from `∅` by attaching cells of dimensions `index(p₁), …, index(p_j)`, one at a
time. -/
theorem isFiniteCellComplexType_sublevel' (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hNc : IsCompact N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q))
    (a : ℝ) (ha : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      F q ≠ a) :
    letI := hN.chartedSpace
    ∃ ps : List N, ps.Nodup ∧
      (∀ q, q ∈ ps ↔ IsCriticalPointM Z (F ∘ Subtype.val) q ∧ F q < a) ∧
      ps.Pairwise (fun q q' : N => F q ≤ F q') ∧
      IsFiniteCellComplexType (sublevel (F ∘ Subtype.val : N → ℝ) a)
        (ps.map (indexM Z (F ∘ Subtype.val))) := by
  classical
  let _ := hN.chartedSpace
  have := hN.isManifold
  have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfc : Continuous f := hF.continuous.comp continuous_subtype_val
  have hMorse : IsMorseFunction Z f := ⟨contMDiff_comp_val hN hF, hnd⟩
  have hfin := hMorse.finite_setOf_isCriticalPointM
  suffices key : ∀ m : ℕ, ∀ a : ℝ, (hfin.toFinset.filter (fun q : N => F q < a)).card = m →
      (∀ q : N, IsCriticalPointM Z f q → F q ≠ a) →
      ∃ ps : List N, ps.Nodup ∧ (∀ q, q ∈ ps ↔ IsCriticalPointM Z f q ∧ F q < a) ∧
        ps.Pairwise (fun q q' : N => F q ≤ F q') ∧
        IsFiniteCellComplexType (sublevel f a) (ps.map (indexM Z f)) from key _ a rfl ha
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a hm ha
  by_cases hS : (hfin.toFinset.filter (fun q : N => F q < a)).Nonempty
  · -- `c`: the highest critical value below `a`, and `S` the critical points on it
    obtain ⟨p, hpS, hpmax⟩ := Finset.exists_max_image _ (fun q : N => F q) hS
    set c := F p with hc_def
    have hpa : c < a := (Finset.mem_filter.1 hpS).2
    set S := hfin.toFinset.filter (fun q : N => F q = c) with hS_def
    have hSc : ∀ q ∈ S, IsNondegenerateCriticalPointM Z f q ∧ F q = c := fun q hq =>
      ⟨hMorse.isNondegenerateCriticalPointM (hfin.mem_toFinset.1 (Finset.mem_filter.1 hq).1),
        (Finset.mem_filter.1 hq).2⟩
    -- a regular value `a'` just below `c`
    obtain ⟨a', ha'p, hTa'⟩ : ∃ a', a' < c ∧
        ∀ q ∈ hfin.toFinset.filter (fun q : N => F q < c), F q < a' := by
      by_cases hT : (hfin.toFinset.filter (fun q : N => F q < c)).Nonempty
      · obtain ⟨q₀, hq₀T, hq₀max⟩ := Finset.exists_max_image _ (fun q : N => F q) hT
        have : F q₀ < c := (Finset.mem_filter.1 hq₀T).2
        exact ⟨(F q₀ + c) / 2, by linarith, fun q hq => by have := hq₀max q hq; linarith⟩
      · exact ⟨c - 1, by linarith, fun q hq => absurd ⟨q, hq⟩ hT⟩
    have hother : ∀ q : N, IsCriticalPointM Z f q → q ∉ S → F q < a' ∨ a < F q := by
      intro q hq hqS
      rcases lt_trichotomy (F q) c with h | h | h
      · exact Or.inl (hTa' q (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hq, h⟩))
      · exact absurd (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hq, h⟩) hqS
      · right
        by_contra hle
        have hqa : F q < a := lt_of_le_of_ne (not_lt.1 hle) (ha q hq)
        have := hpmax q (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hq, hqa⟩)
        linarith
    have ha'reg : ∀ q : N, IsCriticalPointM Z f q → F q ≠ a' := by
      intro q hq heq
      by_cases hqS : q ∈ S
      · have := (hSc q hqS).2
        linarith
      · rcases hother q hq hqS with h | h <;> linarith
    have hfilter : hfin.toFinset.filter (fun q : N => F q < a') =
        (hfin.toFinset.filter (fun q : N => F q < a)) \ S := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_sdiff, hS_def, not_and]
      constructor
      · rintro ⟨hq, hqa'⟩
        exact ⟨⟨hq, by linarith⟩, fun _ h => by linarith⟩
      · rintro ⟨⟨hq, hqa⟩, hqS⟩
        refine ⟨hq, ?_⟩
        rcases hother q (hfin.mem_toFinset.1 hq) (fun h => hqS hq (Finset.mem_filter.1 h).2)
          with h | h
        · exact h
        · linarith
    have hpS' : p ∈ S := Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hpS).1, rfl⟩
    have hcard : (hfin.toFinset.filter (fun q : N => F q < a')).card < m := by
      rw [hfilter, ← hm]
      exact Finset.card_lt_card (Finset.sdiff_ssubset (fun q hq => Finset.mem_filter.2
        ⟨(Finset.mem_filter.1 hq).1, by rw [(Finset.mem_filter.1 hq).2]; exact hpa⟩)
        ⟨p, hpS'⟩)
    obtain ⟨ps', hnd', hmem', hsort', hcell'⟩ := ih _ hcard a' rfl ha'reg
    obtain ⟨l, hlnd, hlmem, hcell⟩ :=
      IsFiniteCellComplexType.sublevel_step_finset hN hNc hF hSc ha'p hpa hother hcell'
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
      obtain ⟨q₀, -, hq₀⟩ := isCompact_univ.exists_isMinOn ⟨q, mem_univ q⟩ hfc.continuousOn
      have hc : IsCriticalPointM Z f q₀ :=
        isCriticalPointM_of_forall_le fun x => hq₀ (mem_univ x)
      have hq₀a : F q₀ < a := lt_of_le_of_ne ((hq₀ (mem_univ q)).trans hq) (ha q₀ hc)
      exact hS ⟨q₀, Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hc, hq₀a⟩⟩
    refine ⟨[], List.nodup_nil, fun q => ?_, List.Pairwise.nil, ?_⟩
    · simp only [List.not_mem_nil, false_iff, not_and]
      intro hc hqa
      exact hS ⟨q, Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hc, hqa⟩⟩
    · have : IsEmpty (sublevel f a) := Set.isEmpty_coe_sort.2 hempty
      exact IsFiniteCellComplexType.of_isEmpty _

/-- **Theorem 3.5** (Milnor, p. 20) for a compact submanifold of Euclidean space, in general: let
`N ⊆ V` be a compact slice submanifold and `F : V → ℝ` smooth such that all critical points of
`f = F|N` are non-degenerate. Then the critical points of `f` can be listed as `p₁, …, p_k` with
`f(p₁) ≤ ⋯ ≤ f(p_k)`, and `N` has the homotopy type of the space obtained from the empty space by
attaching cells of dimensions `index(p₁), …, index(p_k)`, one at a time and in this order, along
continuous attaching maps. (Several critical points on one level are handled by Remark 3.3,
`Morse.remark_3_3_submanifold`.) -/
theorem theorem_3_5' (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (hNc : IsCompact N)
    {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) :
    letI := hN.chartedSpace
    ∃ ps : List N, ps.Nodup ∧ (∀ q, q ∈ ps ↔ IsCriticalPointM Z (F ∘ Subtype.val) q) ∧
      ps.Pairwise (fun q q' : N => F q ≤ F q') ∧
      IsFiniteCellComplexType N (ps.map (indexM Z (F ∘ Subtype.val))) := by
  let _ := hN.chartedSpace
  have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfc : Continuous f := hF.continuous.comp continuous_subtype_val
  obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image hfc.continuousOn
  have hle : ∀ q : N, F q < M + 1 := fun q => by
    have := hM ⟨q, mem_univ q, rfl⟩
    change f q ≤ M at this
    simp only [hf_def, Function.comp_apply] at this
    linarith
  obtain ⟨ps, h1, h2, h3, h4⟩ :=
    isFiniteCellComplexType_sublevel' hN hNc hF hnd (M + 1) fun q _ => (hle q).ne
  refine ⟨ps, h1, fun q => (h2 q).trans (and_iff_left (hle q)), h3, h4.of_homotopyEquiv ?_⟩
  have huniv : sublevel f (M + 1) = univ := eq_univ_of_forall fun q => (hle q).le
  exact ((Homeomorph.Set.univ N).symm.trans (Homeomorph.setCongr huniv.symm)).toHomotopyEquiv

/-- **Theorem 3.5, counting cells** (Milnor, p. 20: "one cell of dimension `λ` for each critical
point of index `λ`"), for a compact submanifold and any function with non-degenerate critical
points: `N` has the homotopy type of an iterated adjunction space whose number of cells of
dimension `λ` is, for every `λ`, the number `C_λ` of critical points of `f` of index `λ`. -/
theorem theorem_3_5_count' (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (hNc : IsCompact N)
    {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) :
    letI := hN.chartedSpace
    ∃ cells : List ℕ, IsFiniteCellComplexType N cells ∧ ∀ k : ℕ, cells.count k =
      {q : N | IsCriticalPointM Z (F ∘ Subtype.val) q ∧
        indexM Z (F ∘ Subtype.val) q = k}.ncard := by
  let _ := hN.chartedSpace
  classical
  obtain ⟨ps, hnd', hmem, -, hcell⟩ := theorem_3_5' hN hNc hF hnd
  refine ⟨_, hcell, fun k => ?_⟩
  have hset : {q : N | IsCriticalPointM Z (F ∘ Subtype.val) q ∧
      indexM Z (F ∘ Subtype.val) q = k} =
      ↑(ps.filter (fun q => indexM Z (F ∘ Subtype.val) q = k)).toFinset := by
    ext q
    simp [hmem]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hnd'.filter _), List.count,
    List.countP_map, List.countP_eq_length_filter]
  rfl

end SubmanifoldSeveral

end Morse
