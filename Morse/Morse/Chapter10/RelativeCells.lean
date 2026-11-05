import Morse.Chapter10.SublevelCW
import Morse.Appendix.MonotoneUnion

/-!
Milnor, *Morse Theory*, §3, p. 23 (the proof of Theorem 3.5), §17, p. 95 (the proof of
Theorem 17.3, "just as in the proof of 3.5") and the Appendix, p. 150: the relative form of
Theorem 3.5 and the inductive construction of a countable cell complex.

# Relative cell complexes and towers

## Milnor's text, paraphrased

(p. 23) In the proof of Theorem 3.5, passing a critical level `c` replaces `M^{c−ε}` by
`M^{c−ε} ∪ e^{λ₁} ∪ ⋯`, and a homotopy equivalence from the lower sublevel set to a CW-complex
is carried over the new cells by Lemmas 3.6 and 3.7.  (p. 95) In the proof of Theorem 17.3 the
same construction is said to give CW-complexes `K₀ ⊂ K₁ ⊂ ⋯` and homotopy equivalences
`Ω^{a_i} → K_i`, each extending the previous one; (p. 150) Theorem A of the Appendix then shows
that the limit map `Ω → K` is a homotopy equivalence.

## What is proved here

* `Morse.IsRelCellComplexType ι cells`: **`ι : A → X` is, up to homotopy, the inclusion of `A`
  into `A` with cells attached**: there are a space `K` obtained from `A` itself by attaching
  cells of the dimensions `cells`, one at a time (`Morse.IsRelCellAttachment`, `j : A → K` the
  composite of the inclusions), and a homotopy equivalence `e : X → K` with `e ∘ ι ≃ j`.  This is
  the relative counterpart of `Morse.IsFiniteCellComplexType`.
* `Morse.IsRelCellAttachment.transport`: **Lemma 3.7, relative and iterated**: a relative cell
  attachment `L → K` and a homotopy equivalence `L → L'` give a relative cell attachment
  `L' → K'` with the same cells and a homotopy equivalence `K → K'` extending `L → L'`.
* `Morse.IsRelCellComplexType.of_square`: invariance under homotopy-commutative squares of
  homotopy equivalences; `Morse.IsRelCellComplexType.attach`, `.mono`, `.comp_homotopyEquiv`.
* `Morse.isRelCellComplexType_union_cells`: Lemma D, relative: disjoint cells meeting a closed set
  in their boundaries are attached to it one at a time.
* `Morse.IsRelCellComplexType.sublevel_step_of_isCompact`,
  `Morse.isRelCellComplexType_sublevel_of_isCompact`: **the relative Theorem 3.5** (with
  Remark 3.3): for `f = F|N` on a slice submanifold, regular values `b ≤ a₀` with `N^{a₀}` compact
  and non-degenerate critical points in `N^{a₀}`, the inclusion `N^b → N^{a₀}` is, up to homotopy,
  the inclusion of `N^b` into `N^b` with one cell of dimension `λ` attached for each critical
  point of index `λ` in `f⁻¹(b, a₀)`, in order of critical value.
* `Morse.isCountableCellComplexType_of_rel`, `Morse.isCountableCellComplexType_of_relSublevel`:
  **the inductive construction of the tower** (Milnor p. 95): if `X` is the homotopy direct limit
  of `X₀ ⊆ X₁ ⊆ ⋯` (for instance the sublevel sets `X^{a_n}` of a continuous function, `a_n ↗ ∞`),
  `X₀` has the homotopy type of a finite cell complex and each inclusion `X_n → X_{n+1}` is a
  relative cell complex as above, then `X` has the homotopy type of the countable cell complex
  (`Morse.IsCountableCellComplexType`) with these cells.

## What Milnor leaves implicit

* **"Each extending the previous one."**  Lemma 3.7 extends a homotopy equivalence `g_n` over the
  cells of `X_n ∪ e^{λ₁} ∪ ⋯`, but `X_{n+1}` is only homotopy equivalent to this space, by
  retractions (Theorems 3.1, 3.2) which move `X_n`; so the composite `X_{n+1} → K_{n+1}` extends
  `g_n` only up to homotopy.  Strict compatibility needs more care (in §17, nested subdivisions:
  Lemma 17.E of the exposition).  It is not needed: the Appendix's comparison of telescopes
  (`Morse.isCountableCellComplexType_of_tower`) only uses **homotopy-commutative** squares
  `c_n ∘ g_n ≃ g_{n+1} ∘ (X_n ⊆ X_{n+1})`, which is what the induction here produces.
* **The relative form of Theorem 3.5.**  Theorem 3.5 and the Remark on p. 24 describe one sublevel
  set at a time; the tower needs the pairs `(M^{a_{n+1}}, M^{a_n})`, with control of the
  inclusion.  The proof is Milnor's (Theorems 3.1, 3.2, Remark 3.3 and Lemma 3.7), run relative to
  the bottom level.
-/

open Set Filter Topology Function Module CategoryTheory Limits TopCat
open scoped ContDiff Manifold

universe u

noncomputable section

namespace Morse

/-- The inclusion of a subset as a continuous map. -/
def inclC {T : Type*} [TopologicalSpace T] {A B : Set T} (h : A ⊆ B) : C(A, B) :=
  ⟨Set.inclusion h, continuous_inclusion h⟩

@[simp] theorem inclC_apply {T : Type*} [TopologicalSpace T] {A B : Set T} (h : A ⊆ B) (x : A) :
    inclC h x = Set.inclusion h x := rfl

/-- **Lemma 3.7, relative and iterated** (Milnor pp. 21–23): if `K` is obtained from `L` by
attaching cells `cells` (`j : L → K` the inclusion) and `e : L → L'` is a homotopy equivalence,
then the same cells can be attached to `L'`, giving `j' : L' → K'`, and there is a homotopy
equivalence `E : K → K'` with `E ∘ j = j' ∘ e` (the cells are attached along the composites with
`e`, one at a time). -/
theorem IsRelCellAttachment.transport {L K : TopCat.{u}} {j : L ⟶ K} {cells : List ℕ}
    (h : IsRelCellAttachment L K j cells) {L' : TopCat.{u}} (e : ContinuousMap.HomotopyEquiv L L') :
    ∃ (K' : TopCat.{u}) (j' : L' ⟶ K') (E : ContinuousMap.HomotopyEquiv K K'),
      IsRelCellAttachment L' K' j' cells ∧ ∀ x, E (j x) = j' (e x) := by
  induction h with
  | refl => exact ⟨L', 𝟙 L', e, .refl, fun x => rfl⟩
  | @attach K₁ j₁ c₁ h n φ ih =>
    obtain ⟨K', j', E, hrel, hcomm⟩ := ih
    obtain ⟨F, hF, -⟩ := lemma_3_7 φ E
    refine ⟨_, j' ≫ cellInl (φ ≫ TopCat.ofHom E.toFun), F, hrel.attach n _, fun x => ?_⟩
    change F (cellInl φ (j₁ x)) = cellInl (φ ≫ TopCat.ofHom E.toFun) (j' (e x))
    rw [hF, hcomm]

/-- **`ι : A → X` is, up to homotopy, the inclusion of `A` into `A` with cells of the dimensions
`cells` attached** (the relative counterpart of `Morse.IsFiniteCellComplexType`): there are a
space `K` obtained from `A` by attaching these cells one at a time, `j : A → K` the composite of
the inclusions, and a homotopy equivalence `e : X → K` with `e ∘ ι ≃ j`. -/
def IsRelCellComplexType {A X : Type u} [TopologicalSpace A] [TopologicalSpace X] (ι : C(A, X))
    (cells : List ℕ) : Prop :=
  ∃ (K : TopCat.{u}) (j : TopCat.of A ⟶ K), IsRelCellAttachment (TopCat.of A) K j cells ∧
    ∃ e : ContinuousMap.HomotopyEquiv X K, (e.toFun.comp ι).Homotopic j.hom

namespace IsRelCellComplexType

variable {A X Y : Type u} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
  {cells : List ℕ}

/-- A homotopy equivalence is a relative cell complex without cells. -/
theorem of_homotopyEquiv (e : ContinuousMap.HomotopyEquiv A X) :
    IsRelCellComplexType e.toFun [] :=
  ⟨TopCat.of A, 𝟙 _, .refl, e.symm, e.left_inv⟩

/-- The property only depends on the homotopy class of `ι`. -/
theorem congr {ι ι' : C(A, X)} (h : IsRelCellComplexType ι cells) (hι : ι.Homotopic ι') :
    IsRelCellComplexType ι' cells := by
  obtain ⟨K, j, hrel, e, he⟩ := h
  exact ⟨K, j, hrel, e, ((ContinuousMap.Homotopic.refl e.toFun).comp hι.symm).trans he⟩

/-- The property only depends on `ι` as a function. -/
theorem of_eq {ι ι' : C(A, X)} (h : IsRelCellComplexType ι cells) (hι : ∀ x, ι x = ι' x) :
    IsRelCellComplexType ι' cells := by
  rwa [← ContinuousMap.ext hι]

/-- Composing with a homotopy equivalence `X → Y`. -/
theorem comp_homotopyEquiv {ι : C(A, X)} (h : IsRelCellComplexType ι cells)
    (e' : ContinuousMap.HomotopyEquiv X Y) :
    IsRelCellComplexType (e'.toFun.comp ι) cells := by
  obtain ⟨K, j, hrel, e, he⟩ := h
  refine ⟨K, j, hrel, e'.symm.trans e, ?_⟩
  have h2 := (ContinuousMap.Homotopic.refl e.toFun).comp
    (e'.left_inv.comp (ContinuousMap.Homotopic.refl ι))
  rw [ContinuousMap.id_comp] at h2
  exact h2.trans he

/-- **Invariance under homotopy-commutative squares**: if `α : A → A'` and `β : X → X'` are
homotopy equivalences with `β ∘ ι ≃ ι' ∘ α` and `ι'` is a relative cell complex, so is `ι`, with
the same cells (transported along `α⁻¹` by Lemma 3.7). -/
theorem of_square {A' X' : Type u} [TopologicalSpace A'] [TopologicalSpace X'] {ι : C(A, X)}
    {ι' : C(A', X')} (h : IsRelCellComplexType ι' cells) (α : ContinuousMap.HomotopyEquiv A A')
    (β : ContinuousMap.HomotopyEquiv X X')
    (hsq : (β.toFun.comp ι).Homotopic (ι'.comp α.toFun)) :
    IsRelCellComplexType ι cells := by
  obtain ⟨K, j, hrel, e, he⟩ := h
  obtain ⟨K'', j'', E, hrel'', hcomm⟩ := hrel.transport (L' := TopCat.of A) α.symm
  refine ⟨K'', j'', hrel'', β.trans (e.trans E), ?_⟩
  have s1 : (E.toFun.comp (e.toFun.comp (β.toFun.comp ι))).Homotopic
      (E.toFun.comp (e.toFun.comp (ι'.comp α.toFun))) :=
    (ContinuousMap.Homotopic.refl _).comp ((ContinuousMap.Homotopic.refl _).comp hsq)
  have s2 : (E.toFun.comp ((e.toFun.comp ι').comp α.toFun)).Homotopic
      (E.toFun.comp (j.hom.comp α.toFun)) :=
    (ContinuousMap.Homotopic.refl _).comp (he.comp (ContinuousMap.Homotopic.refl _))
  have s3 : E.toFun.comp (j.hom.comp α.toFun) =
      j''.hom.comp (α.symm.toFun.comp α.toFun) := by
    ext x
    exact hcomm (α x)
  have s4 : (j''.hom.comp (α.symm.toFun.comp α.toFun)).Homotopic
      (j''.hom.comp (ContinuousMap.id A)) :=
    (ContinuousMap.Homotopic.refl _).comp α.left_inv
  rw [ContinuousMap.comp_id] at s4
  rw [s3] at s2
  exact s1.trans (s2.trans s4)

/-- **Attaching a cell** (Lemma 3.7): if `ι : A → X` is a relative cell complex with cells
`cells`, then `A → X ∪_φ e^n` is one with cells `cells ++ [n]`. -/
theorem attach {X : TopCat.{u}} {ι : C(A, X)} (h : IsRelCellComplexType ι cells) (n : ℕ)
    (φ : ∂𝔻 n ⟶ X) : IsRelCellComplexType ((cellInl φ).hom.comp ι) (cells ++ [n]) := by
  obtain ⟨K, j, hrel, e, he⟩ := h
  obtain ⟨F, hF, -⟩ := lemma_3_7 φ e
  refine ⟨_, j ≫ cellInl (φ ≫ TopCat.ofHom e.toFun), hrel.attach n _, F, ?_⟩
  have h1 : F.toFun.comp ((cellInl φ).hom.comp ι) =
      (cellInl (φ ≫ TopCat.ofHom e.toFun)).hom.comp (e.toFun.comp ι) := by
    ext x
    exact hF (ι x)
  rw [h1]
  exact (ContinuousMap.Homotopic.refl _).comp he

/-- **Enlarging the top by a homotopy equivalence which is an inclusion**: for `A ⊆ B ⊆ C`, if
`A → B` is a relative cell complex and `B → C` is a homotopy equivalence (given as `e` with
`e x = x`), then `A → C` is one, with the same cells. -/
theorem mono {T : Type u} [TopologicalSpace T] {A B C : Set T} {hAB : A ⊆ B}
    (h : IsRelCellComplexType (inclC hAB) cells) (hBC : B ⊆ C) (e : ContinuousMap.HomotopyEquiv B C)
    (he : ∀ x, (e x : T) = x) : IsRelCellComplexType (inclC (hAB.trans hBC)) cells :=
  (h.comp_homotopyEquiv e).of_eq fun x => Subtype.ext (he (inclC hAB x))

end IsRelCellComplexType

/-- **Lemma D, relative** (Milnor p. 16 and Remark 3.3): let `A₀ ⊆ A` be subsets of a Hausdorff
space with `A` closed, and `χᵢ`, `i ∈ l`, maps of closed unit balls, continuous and injective, with
pairwise disjoint images each meeting `A` exactly in the image of the sphere.  If `A₀ → A` is a
relative cell complex with cells `cells`, then `A₀ → A ∪ ⋃_{i ∈ l} χᵢ(D)` is one with cells
`cells` followed by the dimensions of the `χᵢ`. -/
theorem isRelCellComplexType_union_cells {M : Type u} [TopologicalSpace M] [T2Space M]
    {ι : Type*} {k : ι → ℕ} (χ : (i : ι) → EuclideanSpace ℝ (Fin (k i)) → M) {A₀ : Set M} :
    ∀ (l : List ι) {A : Set M} (hA₀ : A₀ ⊆ A) {cells : List ℕ}, IsClosed A →
      IsRelCellComplexType (inclC hA₀) cells →
      (∀ i ∈ l, ContinuousOn (χ i) (Metric.closedBall 0 1) ∧
        InjOn (χ i) (Metric.closedBall 0 1) ∧
        ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k i))) 1, χ i z ∈ A ↔ ‖z‖ = 1) →
      l.Pairwise (fun i j => Disjoint (χ i '' Metric.closedBall 0 1)
        (χ j '' Metric.closedBall 0 1)) →
      IsRelCellComplexType
        (inclC (hA₀.trans subset_union_left :
          A₀ ⊆ A ∪ ⋃ i ∈ l, χ i '' Metric.closedBall 0 1)) (cells ++ l.map k) := by
  intro l
  induction l with
  | nil =>
    intro A hA₀ cells _ h _ _
    have hs : A = A ∪ ⋃ i ∈ ([] : List ι), χ i '' Metric.closedBall 0 1 := by simp
    rw [List.map_nil, List.append_nil]
    exact h.mono subset_union_left (Homeomorph.setCongr hs).toHomotopyEquiv fun x => rfl
  | cons i l ih =>
    intro A hA₀ cells hA h hprops hdisj
    obtain ⟨hcont, hinj, hbdry⟩ := hprops i (List.mem_cons_self ..)
    obtain ⟨φ, χ', -, -, hpo⟩ := exists_isPushout_union_cell_of_t2 hA hcont hinj hbdry
    set A' := A ∪ χ i '' Metric.closedBall 0 1 with hA'_def
    have hA' : IsClosed A' :=
      hA.union ((isCompact_closedBall _ _).image_of_continuousOn hcont).isClosed
    have hA₀' : A₀ ⊆ A' := hA₀.trans subset_union_left
    have h' : IsRelCellComplexType (inclC hA₀') (cells ++ [k i]) := by
      have h1 : IsRelCellComplexType (X := TopCat.of A) (inclC hA₀) cells := h
      refine ((h1.attach (k i) φ).comp_homotopyEquiv
        (homeoOfIso hpo.isoPushout).symm.toHomotopyEquiv).of_eq fun x => ?_
      have := ConcreteCategory.congr_hom hpo.inl_isoPushout_inv (inclC hA₀ x)
      exact this
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
    have := ih hA₀' hA' h' hprops' hdisj.2
    have hs : A' ∪ ⋃ j ∈ l, χ j '' Metric.closedBall 0 1 =
        A ∪ ⋃ j ∈ i :: l, χ j '' Metric.closedBall 0 1 := by
      ext q
      simp only [hA'_def, mem_union, mem_iUnion, List.mem_cons, exists_prop]
      constructor
      · rintro ((h | h) | ⟨j, hj, hq⟩)
        · exact Or.inl h
        · exact Or.inr ⟨i, Or.inl rfl, h⟩
        · exact Or.inr ⟨j, Or.inr hj, hq⟩
      · rintro (h | ⟨j, rfl | hj, hq⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr hq)
        · exact Or.inr ⟨j, hj, hq⟩
    rw [List.map_cons, show cells ++ k i :: l.map k = (cells ++ [k i]) ++ l.map k by simp]
    exact this.mono (hs ▸ subset_rfl) (Homeomorph.setCongr hs).toHomotopyEquiv fun x => rfl

section Sublevel

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V}

/-- **Passing one critical level, relative to a lower level** (Milnor p. 23, with Remark 3.3):
let `S` be the critical points of `f = F|N` on the level `c`, all non-degenerate, `b ≤ a' < c < a`
with no other critical value in `[a', a]`, and `N^{a₀}` compact, `a ≤ a₀`.  If `N^b → N^{a'}` is
a relative cell complex with cells `cells`, then `N^b → N^a` is one with cells `cells` followed by
the indices of the points of `S` (in some order). -/
theorem IsRelCellComplexType.sublevel_step_of_isCompact
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F) {a₀ : ℝ}
    (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Iic a₀)) {S : Finset N} {c : ℝ}
    (hS : letI := hN.chartedSpace;
      ∀ p ∈ S, IsNondegenerateCriticalPointM Z (F ∘ Subtype.val) p ∧ F p = c)
    {b a' a : ℝ} (hba' : b ≤ a') (ha' : a' < c) (ha : c < a) (haa₀ : a ≤ a₀)
    (hother : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q → q ∉ S →
      F q < a' ∨ a < F q)
    {cells : List ℕ}
    (h : IsRelCellComplexType (inclC (sublevel_mono (F ∘ Subtype.val : N → ℝ) hba')) cells) :
    letI := hN.chartedSpace
    ∃ l : List N, l.Nodup ∧ (∀ q, q ∈ l ↔ q ∈ S) ∧
      IsRelCellComplexType
        (inclC (sublevel_mono (F ∘ Subtype.val : N → ℝ) (hba'.trans (ha'.trans ha).le)))
        (cells ++ l.map (indexM Z (F ∘ Subtype.val))) := by
  classical
  let _ := hN.chartedSpace
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfc : Continuous f := hF.continuous.comp continuous_subtype_val
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
  have hno : ∀ {b b' : ℝ}, a' ≤ b → b' ≤ a → (b' < c ∨ c < b) →
      ∀ q : N, F q ∈ Icc b b' → ¬IsCriticalPointM Z f q := by
    intro b b' hb hb' hbp q hq hc
    by_cases hqS : q ∈ S
    · have := (hS q hqS).2
      rcases hbp with h | h <;> linarith [hq.1, hq.2]
    · rcases hother q hc hqS with h | h <;> linarith [hq.1, hq.2]
  obtain ⟨e₂, he₂⟩ := (theorem_3_1_submanifold hN hF (a := a') (b := c - ε) (by linarith)
    (hslab _ _ (by linarith)) (hno le_rfl (by linarith) (Or.inl (by linarith)))).2.2
  obtain ⟨e₃, he₃⟩ := (theorem_3_1_submanifold hN hF (a := c + ε) (b := a) (by linarith)
    (hslab _ _ haa₀) (hno (by linarith) le_rfl (Or.inr (by linarith)))).2.2
  have h4 : IsRelCellComplexType
      (inclC ((sublevel_mono f hba').trans (sublevel_mono f (by linarith : a' ≤ c - ε)))) cells :=
    h.mono (sublevel_mono f (by linarith : a' ≤ c - ε)) e₂ fun x => by rw [he₂]; try rfl
  -- attach the cells one at a time
  set l : List S := Finset.univ.toList with hl_def
  have hlnd : l.Nodup := Finset.nodup_toList _
  have h5 := isRelCellComplexType_union_cells χ l _ (isClosed_le hfc continuous_const) h4
    (fun p _ => ⟨(hprops p).1, (hprops p).2.1, (hprops p).2.2.1⟩)
    (hlnd.pairwise_of_forall_ne fun p _ p' _ hpp' => hdisj hpp')
  have hU : sublevel f (c - ε) ∪ ⋃ p ∈ l, χ p '' Metric.closedBall 0 1 =
      sublevel f (c - ε) ∪ ⋃ p, χ p '' Metric.closedBall 0 1 := by
    simp [hl_def]
  have hsub : sublevel f (c - ε) ∪ ⋃ p, χ p '' Metric.closedBall 0 1 ⊆ sublevel f (c + ε) :=
    union_subset (sublevel_mono f (by linarith)) (iUnion_subset fun p => (hprops p).2.2.2)
  obtain ⟨e₁, he₁⟩ := hsdr.exists_homotopyEquiv hsub
  refine ⟨l.map Subtype.val, hlnd.map Subtype.val_injective, fun q => ?_, ?_⟩
  · simp only [List.mem_map, hl_def, Finset.mem_toList, Finset.mem_univ, true_and]
    exact ⟨fun ⟨p, hp⟩ => hp ▸ p.2, fun hq => ⟨⟨q, hq⟩, rfl⟩⟩
  · rw [List.map_map]
    have h6 := h5.mono (hU ▸ subset_rfl) (Homeomorph.setCongr hU).toHomotopyEquiv fun x => rfl
    have h7 := h6.mono hsub e₁ fun x => by rw [he₁]; try rfl
    exact h7.mono (sublevel_mono f (by linarith)) e₃ fun x => by rw [he₃]; try rfl

/-- **The relative Theorem 3.5** (Milnor pp. 20–24, relative to a lower level): let `N ⊆ V` be a
slice submanifold, `F : V → ℝ` smooth, `f = F|N`, `N^{a₀}` compact, every critical point of `f` in
`N^{a₀}` non-degenerate, and `b ≤ a₀` regular values.  Then the critical points of `f` in
`f⁻¹(b, a₀)` can be listed as `p₁, …, p_j` with `f(p₁) ≤ ⋯ ≤ f(p_j)` so that the inclusion
`N^b → N^{a₀}` is, up to homotopy, the inclusion of `N^b` into the space obtained from `N^b` by
attaching cells of dimensions `index(p₁), …, index(p_j)`, one at a time. -/
theorem isRelCellComplexType_sublevel_of_isCompact
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F) {a₀ : ℝ}
    (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Iic a₀))
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q → F q ≤ a₀ →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q))
    {b : ℝ} (hb : b ≤ a₀)
    (hbreg : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q → F q ≠ b)
    (ha₀ : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      F q ≠ a₀) :
    letI := hN.chartedSpace
    ∃ ps : List N, ps.Nodup ∧
      (∀ q, q ∈ ps ↔ IsCriticalPointM Z (F ∘ Subtype.val) q ∧ b < F q ∧ F q < a₀) ∧
      ps.Pairwise (fun q q' : N => F q ≤ F q') ∧
      IsRelCellComplexType (inclC (sublevel_mono (F ∘ Subtype.val : N → ℝ) hb))
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
  suffices key : ∀ m : ℕ, ∀ a : ℝ, ∀ hba : b ≤ a, a ≤ a₀ →
      (C.filter (fun q : N => b < F q ∧ F q < a)).card = m →
      (∀ q : N, IsCriticalPointM Z f q → F q ≠ a) →
      ∃ ps : List N, ps.Nodup ∧ (∀ q, q ∈ ps ↔ IsCriticalPointM Z f q ∧ b < F q ∧ F q < a) ∧
        ps.Pairwise (fun q q' : N => F q ≤ F q') ∧
        IsRelCellComplexType (inclC (sublevel_mono f hba)) (ps.map (indexM Z f)) from
    key _ a₀ hb le_rfl rfl ha₀
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a hba haa₀ hm ha
  have hcrit_lt : ∀ q, IsCriticalPointM Z f q → b < F q → F q < a →
      q ∈ C.filter (fun q : N => b < F q ∧ F q < a) :=
    fun q hq hqb hqa => Finset.mem_filter.2 ⟨(hmemC q).2 ⟨(hqa.le.trans haa₀), hq⟩, hqb, hqa⟩
  by_cases hS : (C.filter (fun q : N => b < F q ∧ F q < a)).Nonempty
  · obtain ⟨p, hpS, hpmax⟩ := Finset.exists_max_image _ (fun q : N => F q) hS
    set c := F p with hc_def
    have hpb : b < c := (Finset.mem_filter.1 hpS).2.1
    have hpa : c < a := (Finset.mem_filter.1 hpS).2.2
    set S := C.filter (fun q : N => F q = c) with hS_def
    have hSc : ∀ q ∈ S, IsNondegenerateCriticalPointM Z f q ∧ F q = c := fun q hq => by
      have hqC := (hmemC q).1 (Finset.mem_filter.1 hq).1
      exact ⟨⟨hqC.2, hnd q hqC.2 hqC.1⟩, (Finset.mem_filter.1 hq).2⟩
    -- a regular value `a'` in `[b, c)` above every other critical value in `(b, c)`
    obtain ⟨a', hba', ha'p, hTa', ha'reg0⟩ : ∃ a', b ≤ a' ∧ a' < c ∧
        (∀ q ∈ C.filter (fun q : N => b < F q ∧ F q < c), F q < a') ∧
        (∀ q : N, IsCriticalPointM Z f q → F q ≠ a') := by
      by_cases hT : (C.filter (fun q : N => b < F q ∧ F q < c)).Nonempty
      · obtain ⟨q₀, hq₀T, hq₀max⟩ := Finset.exists_max_image _ (fun q : N => F q) hT
        have h1 : b < F q₀ := (Finset.mem_filter.1 hq₀T).2.1
        have h2 : F q₀ < c := (Finset.mem_filter.1 hq₀T).2.2
        refine ⟨(F q₀ + c) / 2, by linarith, by linarith,
          fun q hq => by have := hq₀max q hq; linarith, fun q hq heq => ?_⟩
        -- a critical point at the level `(F q₀ + c) / 2` would lie in `(F q₀, c)`
        have hqC : q ∈ C := (hmemC q).2 ⟨by linarith, hq⟩
        have := hq₀max q (Finset.mem_filter.2 ⟨hqC, by linarith, by linarith⟩)
        linarith
      · exact ⟨b, le_rfl, hpb, fun q hq => absurd ⟨q, hq⟩ hT, hbreg⟩
    have hother : ∀ q : N, IsCriticalPointM Z f q → q ∉ S → F q < a' ∨ a < F q := by
      intro q hq hqS
      rcases lt_trichotomy (F q) c with h | h | h
      · left
        by_cases hqb : b < F q
        · exact hTa' q (Finset.mem_filter.2 ⟨(hmemC q).2 ⟨by linarith, hq⟩, hqb, h⟩)
        · exact lt_of_lt_of_le (lt_of_le_of_ne (not_lt.1 hqb) (hbreg q hq)) hba'
      · exact absurd (Finset.mem_filter.2 ⟨(hmemC q).2 ⟨by linarith, hq⟩, h⟩) hqS
      · right
        by_contra hle
        have hqa : F q < a := lt_of_le_of_ne (not_lt.1 hle) (ha q hq)
        have := hpmax q (hcrit_lt q hq (by linarith) hqa)
        linarith
    have hfilter : C.filter (fun q : N => b < F q ∧ F q < a') =
        (C.filter (fun q : N => b < F q ∧ F q < a)) \ S := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_sdiff, hS_def, not_and]
      constructor
      · rintro ⟨hq, hqb, hqa'⟩
        exact ⟨⟨hq, hqb, by linarith⟩, fun _ h => by linarith⟩
      · rintro ⟨⟨hq, hqb, hqa⟩, hqS⟩
        refine ⟨hq, hqb, ?_⟩
        rcases hother q ((hmemC q).1 hq).2 (fun h => hqS hq (Finset.mem_filter.1 h).2)
          with h | h
        · exact h
        · linarith
    have hpS' : p ∈ S := Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hpS).1, rfl⟩
    have hcard : (C.filter (fun q : N => b < F q ∧ F q < a')).card < m := by
      rw [hfilter, ← hm]
      exact Finset.card_lt_card (Finset.sdiff_ssubset (fun q hq => Finset.mem_filter.2
        ⟨(Finset.mem_filter.1 hq).1, by
          rw [(Finset.mem_filter.1 hq).2]; exact ⟨hpb, hpa⟩⟩) ⟨p, hpS'⟩)
    obtain ⟨ps', hnd', hmem', hsort', hcell'⟩ :=
      ih _ hcard a' hba' (by linarith) rfl ha'reg0
    obtain ⟨l, hlnd, hlmem, hcell⟩ :=
      IsRelCellComplexType.sublevel_step_of_isCompact hN hF hK hSc hba' ha'p hpa haa₀ hother
        hcell'
    have hlc : ∀ q ∈ l, F q = c := fun q hq => (hSc q ((hlmem q).1 hq)).2
    refine ⟨ps' ++ l, ?_, fun q => ?_, ?_, ?_⟩
    · refine hnd'.append hlnd (List.disjoint_left.2 fun q hq hql => ?_)
      have h1 := ((hmem' q).1 hq).2.2
      have h2 := hlc q hql
      linarith
    · rw [List.mem_append, hmem', hlmem]
      constructor
      · rintro (⟨hq, hqb, hqa'⟩ | hqS)
        · exact ⟨hq, hqb, by linarith⟩
        · exact ⟨(hSc q hqS).1.1, by rw [(hSc q hqS).2]; exact hpb,
            by rw [(hSc q hqS).2]; exact hpa⟩
      · rintro ⟨hq, hqb, hqa⟩
        by_cases hqS : q ∈ S
        · exact Or.inr hqS
        · refine Or.inl ⟨hq, hqb, ?_⟩
          rcases hother q hq hqS with h | h
          · exact h
          · linarith
    · rw [List.pairwise_append]
      refine ⟨hsort', List.pairwise_of_forall_mem_list fun q hq q' hq' =>
        le_of_eq ((hlc q hq).trans (hlc q' hq').symm), fun q hq q' hq' => ?_⟩
      have h1 := ((hmem' q).1 hq).2.2
      have h2 := hlc q' hq'
      linarith
    · rw [List.map_append]
      exact hcell
  · -- no critical point in `(b, a)`: Theorem 3.1
    have hno : ∀ q : N, F q ∈ Icc b a → ¬IsCriticalPointM Z f q := by
      intro q hq hc
      have h1 : b < F q := lt_of_le_of_ne hq.1 (hbreg q hc).symm
      have h2 : F q < a := lt_of_le_of_ne hq.2 (ha q hc)
      exact hS ⟨q, hcrit_lt q hc h1 h2⟩
    have hslab : IsCompact (f ⁻¹' Icc b a) :=
      hK.of_isClosed_subset (isClosed_Icc.preimage hfc) fun q hq => (hq.2.trans haa₀ : f q ≤ a₀)
    obtain ⟨e, he⟩ := (theorem_3_1_submanifold hN hF hba hslab hno).2.2
    refine ⟨[], List.nodup_nil, fun q => ?_, List.Pairwise.nil, ?_⟩
    · simp only [List.not_mem_nil, false_iff, not_and]
      intro hc hqb hqa
      exact hS ⟨q, hcrit_lt q hc hqb hqa⟩
    · refine (IsRelCellComplexType.of_homotopyEquiv e).of_eq fun x => ?_
      rw [he]
      rfl

end Sublevel

section Tower

variable {X : Type u} [TopologicalSpace X] {A : ℕ → Set X}

/-- A stage of the inductive construction of the tower: a space `K` and a homotopy equivalence
`X_n → K`. -/
structure TowerStage (A : ℕ → Set X) (n : ℕ) where
  K : TopCat.{u}
  g : ContinuousMap.HomotopyEquiv (A n) K

/-- The next stage of the tower: `K'` obtained from `K` by attaching the cells `c`, and a homotopy
equivalence `X_{n+1} → K'` extending `X_n → K → K'` up to homotopy. -/
structure TowerStep (hA : Monotone A) {n : ℕ} (s : TowerStage A n) (c : List ℕ) where
  K' : TopCat.{u}
  j : s.K ⟶ K'
  g' : ContinuousMap.HomotopyEquiv (A (n + 1)) K'
  rel : IsRelCellAttachment s.K K' j c
  sq : (g'.toFun.comp (up hA n)).Homotopic (j.hom.comp s.g.toFun)

/-- **The inductive step** (Milnor p. 95, "just as in the proof of 3.5"): if `X_n → X_{n+1}` is
a relative cell complex with cells `c`, every stage `X_n ≃ K` extends to the next one. -/
theorem nonempty_towerStep (hA : Monotone A) {n : ℕ} (s : TowerStage A n) {c : List ℕ}
    (h : IsRelCellComplexType (up hA n) c) : Nonempty (TowerStep hA s c) := by
  obtain ⟨K, jA, hrel, e, he⟩ := h
  obtain ⟨K', j', E, hrel', hcomm⟩ := hrel.transport (L' := s.K) s.g
  refine ⟨⟨K', j', e.trans E, hrel', ?_⟩⟩
  have h1 : ((e.trans E).toFun.comp (up hA n)) = E.toFun.comp (e.toFun.comp (up hA n)) := rfl
  have h2 : E.toFun.comp jA.hom = j'.hom.comp s.g.toFun := by
    ext x
    exact hcomm x
  rw [h1, ← h2]
  exact (ContinuousMap.Homotopic.refl _).comp he

variable {cells : ℕ → List ℕ}

/-- The stages of the tower, built by induction (with choice at each step). -/
noncomputable def towerStages (hA : Monotone A) (s₀ : TowerStage A 0)
    (hstep : ∀ n, IsRelCellComplexType (up hA n) (cells (n + 1))) : ∀ n, TowerStage A n
  | 0 => s₀
  | n + 1 =>
    ⟨(Classical.choice (nonempty_towerStep hA (towerStages hA s₀ hstep n) (hstep n))).K',
      (Classical.choice (nonempty_towerStep hA (towerStages hA s₀ hstep n) (hstep n))).g'⟩

/-- The inductive steps of the tower. -/
noncomputable def towerStepAt (hA : Monotone A) (s₀ : TowerStage A 0)
    (hstep : ∀ n, IsRelCellComplexType (up hA n) (cells (n + 1))) (n : ℕ) :
    TowerStep hA (towerStages hA s₀ hstep n) (cells (n + 1)) :=
  Classical.choice (nonempty_towerStep hA _ (hstep n))

/-- **The countable cell complex of a filtered space** (Milnor pp. 95 and 150): if `X` is the
homotopy direct limit of `X₀ ⊆ X₁ ⊆ ⋯`, `X₀` has the homotopy type of a finite cell complex with
cells `cells 0`, and each inclusion `X_n → X_{n+1}` is a relative cell complex with cells
`cells (n + 1)`, then `X` has the homotopy type of the countable cell complex with cells
`cells 0, cells 1, …`. -/
theorem isCountableCellComplexType_of_rel (hA : Monotone A) (hX : IsHomotopyDirectLimit A)
    (h0 : IsFiniteCellComplexType (A 0) (cells 0))
    (hstep : ∀ n, IsRelCellComplexType (up hA n) (cells (n + 1))) :
    IsCountableCellComplexType X cells := by
  obtain ⟨K₀, hK₀, ⟨e₀⟩⟩ := h0
  set s₀ : TowerStage A 0 := ⟨K₀, e₀⟩
  refine isCountableCellComplexType_of_tower hA hX
    (CellTower.ofSequence (fun n => (towerStages hA s₀ hstep n).K)
      (fun n => (towerStepAt hA s₀ hstep n).j) hK₀ (fun n => (towerStepAt hA s₀ hstep n).rel))
    (fun n => (towerStages hA s₀ hstep n).g.toFun)
    (fun n => IsHomotopyEquiv.of_homotopyEquiv _) fun n => ?_
  have ht := CellTower.tmap_ofSequence (cells := cells) (fun n => (towerStages hA s₀ hstep n).K)
    (fun n => (towerStepAt hA s₀ hstep n).j) hK₀ (fun n => (towerStepAt hA s₀ hstep n).rel) n
  refine (ContinuousMap.Homotopic.refl _).trans ?_ |>.trans (towerStepAt hA s₀ hstep n).sq.symm
  rw [ht]
  exact ContinuousMap.Homotopic.refl _

/-- **The countable cell complex of the sublevel sets of a continuous function**: as
`Morse.isCountableCellComplexType_of_rel`, for `X_n = {E ≤ a_n}`, `E` continuous and
`a_n ↗ ∞` (no paracompactness needed, `Morse.isHomotopyDirectLimit_sublevel`). -/
theorem isCountableCellComplexType_of_relSublevel (E : C(X, ℝ)) {a : ℕ → ℝ} (ha : Monotone a)
    (ha' : Tendsto a atTop atTop) (h0 : IsFiniteCellComplexType (sublevel E (a 0)) (cells 0))
    (hstep : ∀ n, IsRelCellComplexType (inclC (sublevel_mono E (ha (Nat.le_succ n))))
      (cells (n + 1))) :
    IsCountableCellComplexType X cells :=
  isCountableCellComplexType_of_rel (fun _ _ h => sublevel_mono E (ha h))
    (isHomotopyDirectLimit_sublevel E ha ha') h0 hstep

end Tower

end Morse
