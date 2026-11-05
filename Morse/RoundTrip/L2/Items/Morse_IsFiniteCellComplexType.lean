import Morse
import RoundTrip.L2.Blind.Morse_IsFiniteCellComplexType

/-! Layer-2 check of `Morse.IsFiniteCellComplexType X cells` (`X ≃ₕ K` for a project iterated
adjunction space `K` with cells attached IN THE LISTED ORDER) against the blind textbook definition
(`T X cells`: `X ≃ₕ K` for an iterated adjunction space with cells attached in SOME ORDER of the
list, i.e. `cells` read as a multiset).

* `T_iff`: `T X cells ↔ ∃ cells' ~ cells, P X cells'` (the homeomorphism-closure difference of
  `Morse.IsCellAttachment` is absorbed by the homotopy equivalence).
* `P_imp_T`: the project's notion implies the blind one.
* `differ`: they differ. With `cells = [1, 0]` the project's notion is false for every space (the
  first cell attached to `∅` must be a `0`-cell), while the blind one holds for the circle
  (`[0, 1]` attached in that order). More substantially (blind file, not proved here): the interval
  satisfies the blind notion for `[0, 1, 0]` but not the project's.
The difference is a documented convention of the project (its docstrings: "in this order"); the
project's notion is the stronger one and is only produced as a conclusion (Theorem 3.5 with the
cells listed by critical value). Up to homotopy, any order can be rearranged to non-decreasing
dimension (cellular approximation and Lemmas 3.6, 3.7), not formalized. -/

namespace RoundTrip.L2.Morse_IsFiniteCellComplexType

open CategoryTheory Limits TopCat

noncomputable section

/-! ### Glue: the blind iterated adjunction spaces versus the project's (pushouts in `TopCat`) -/

section Core

variable {n : ℕ} {X : TopCat.{0}}

/-- The characteristic map `Dⁿ → X ∪_φ eⁿ` of the blind adjunction space. -/
def inr (φ : diskBoundary.{0} n ⟶ X) : disk.{0} n ⟶ Attach φ :=
  TopCat.ofHom ⟨fun d => Quot.mk (Rel φ) (Sum.inr d), continuous_quot_mk.comp continuous_inr⟩

theorem inl_glue (φ : diskBoundary.{0} n ⟶ X) (s : diskBoundary.{0} n) :
    (inl φ).hom (φ s) = (inr φ).hom (diskBoundaryInclusion n s) :=
  (Quot.sound ⟨s, rfl, rfl⟩).symm

/-- `X ∪_φ eⁿ` (blind) `→ X ∪_φ eⁿ` (project), on representatives. -/
def fwd (φ : diskBoundary.{0} n ⟶ X) : Attach φ ⟶ Morse.AttachCell φ :=
  TopCat.ofHom ⟨Quot.lift (r := Rel φ) (Sum.elim (Morse.cellInl φ) (Morse.cellInr φ)) (by
      rintro _ _ ⟨s, rfl, rfl⟩
      exact (Morse.cellInl_apply_eq φ s).symm),
    continuous_quot_lift _
      ((Morse.cellInl φ).hom.continuous.sumElim (Morse.cellInr φ).hom.continuous)⟩

/-- The blind adjunction space (a `Quot` of `X ⊔ Dⁿ`) is the project's pushout `X ∪_φ eⁿ`. -/
def attachIso (φ : diskBoundary.{0} n ⟶ X) : Attach φ ≅ Morse.AttachCell φ where
  hom := fwd φ
  inv := Morse.cellDesc φ (inl φ).hom (inr φ).hom (inl_glue φ)
  hom_inv_id := by
    ext z
    induction z using Quot.ind with
    | mk a =>
      rcases a with x | d
      · exact Morse.cellDesc_inl φ _ _ _ x
      · exact Morse.cellDesc_inr φ _ _ _ d
  inv_hom_id := Morse.attachCell_hom_ext φ
    (fun x => by
      change fwd φ (Morse.cellDesc φ _ _ _ (Morse.cellInl φ x)) = _
      rw [Morse.cellDesc_inl]
      rfl)
    (fun d => by
      change fwd φ (Morse.cellDesc φ _ _ _ (Morse.cellInr φ d)) = _
      rw [Morse.cellDesc_inr]
      rfl)

@[reassoc (attr := simp)]
theorem inl_attachIso_hom (φ : diskBoundary.{0} n ⟶ X) :
    inl φ ≫ (attachIso φ).hom = Morse.cellInl φ := by
  ext x
  rfl

@[reassoc (attr := simp)]
theorem cellInl_attachIso_inv (φ : diskBoundary.{0} n ⟶ X) :
    Morse.cellInl φ ≫ (attachIso φ).inv = inl φ := by
  rw [← inl_attachIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- `X ∪_φ eⁿ` only depends on `X` up to homeomorphism: for `e : Y ≅ X`,
`Y ∪_{e⁻¹φ} eⁿ ≅ X ∪_φ eⁿ`, compatibly with the inclusions. -/
def cellIso {Y : TopCat.{0}} (e : Y ≅ X) (φ : diskBoundary.{0} n ⟶ X) :
    Morse.AttachCell (φ ≫ e.inv) ≅ Morse.AttachCell φ where
  hom := Morse.cellDesc (φ ≫ e.inv) (e.hom ≫ Morse.cellInl φ).hom (Morse.cellInr φ).hom
    (fun s => by
      change Morse.cellInl φ (e.hom (e.inv (φ s))) = _
      rw [Iso.inv_hom_id_apply]
      exact Morse.cellInl_apply_eq φ s)
  inv := Morse.cellDesc φ (e.inv ≫ Morse.cellInl (φ ≫ e.inv)).hom
    (Morse.cellInr (φ ≫ e.inv)).hom (fun s => Morse.cellInl_apply_eq (φ ≫ e.inv) s)
  hom_inv_id := Morse.attachCell_hom_ext _
    (fun x => by
      change Morse.cellDesc φ _ _ _ (Morse.cellDesc (φ ≫ e.inv) _ _ _ (Morse.cellInl _ x)) = _
      rw [Morse.cellDesc_inl]
      change Morse.cellDesc φ _ _ _ (Morse.cellInl φ (e.hom x)) = _
      rw [Morse.cellDesc_inl]
      change Morse.cellInl (φ ≫ e.inv) (e.inv (e.hom x)) = _
      rw [Iso.hom_inv_id_apply]
      rfl)
    (fun d => by
      change Morse.cellDesc φ _ _ _ (Morse.cellDesc (φ ≫ e.inv) _ _ _ (Morse.cellInr _ d)) = _
      rw [Morse.cellDesc_inr, Morse.cellDesc_inr]
      rfl)
  inv_hom_id := Morse.attachCell_hom_ext _
    (fun x => by
      change Morse.cellDesc (φ ≫ e.inv) _ _ _ (Morse.cellDesc φ _ _ _ (Morse.cellInl _ x)) = _
      rw [Morse.cellDesc_inl]
      change Morse.cellDesc (φ ≫ e.inv) _ _ _ (Morse.cellInl (φ ≫ e.inv) (e.inv x)) = _
      rw [Morse.cellDesc_inl]
      change Morse.cellInl φ (e.hom (e.inv x)) = _
      rw [Iso.inv_hom_id_apply]
      rfl)
    (fun d => by
      change Morse.cellDesc (φ ≫ e.inv) _ _ _ (Morse.cellDesc φ _ _ _ (Morse.cellInr _ d)) = _
      rw [Morse.cellDesc_inr, Morse.cellDesc_inr]
      rfl)

@[reassoc (attr := simp)]
theorem cellInl_cellIso_hom {Y : TopCat.{0}} (e : Y ≅ X) (φ : diskBoundary.{0} n ⟶ X) :
    Morse.cellInl (φ ≫ e.inv) ≫ (cellIso e φ).hom = e.hom ≫ Morse.cellInl φ := by
  ext x
  exact Morse.cellDesc_inl (φ ≫ e.inv) _ _ _ x

end Core

/-- (R1) Post-composing with a homeomorphism. -/
theorem relAttach_comp_iso : ∀ {ds : List ℕ} {L K K' : TopCat.{0}} {f : L ⟶ K},
    RelAttach ds L K f → ∀ e : K ≅ K', RelAttach ds L K' (f ≫ e.hom)
  | [], _, _, _, f, h, e => by
      have : IsIso f := h
      exact (inferInstance : IsIso (f ≫ e.hom))
  | _ :: _, _, _, _, _, ⟨φ, g, hf, h⟩, e =>
      ⟨φ, g ≫ e.hom, by rw [hf, Category.assoc], relAttach_comp_iso h e⟩

/-- (R2) Attaching one more cell at the end. -/
theorem relAttach_snoc : ∀ {ds : List ℕ} {L K : TopCat.{0}} {f : L ⟶ K},
    RelAttach ds L K f → ∀ {n : ℕ} (φ : diskBoundary.{0} n ⟶ K),
      RelAttach (ds ++ [n]) L (Morse.AttachCell φ) (f ≫ Morse.cellInl φ)
  | [], _, _, f, h, _, φ => by
      have : IsIso f := h
      refine ⟨φ ≫ (asIso f).inv, (attachIso _).hom ≫ (cellIso (asIso f) φ).hom, ?_, ?_⟩
      · rw [inl_attachIso_hom_assoc, cellInl_cellIso_hom, asIso_hom]
      · exact (inferInstance : IsIso ((attachIso _).hom ≫ (cellIso (asIso f) φ).hom))
  | _ :: _, _, _, _, ⟨φ₁, g₁, hf, h⟩, _, φ =>
      ⟨φ₁, g₁ ≫ Morse.cellInl φ, by rw [hf, Category.assoc], relAttach_snoc h φ⟩

/-- (R6) Splitting off the last cell. -/
theorem relAttach_unsnoc : ∀ {ds : List ℕ} {n : ℕ} {L K : TopCat.{0}} {f : L ⟶ K},
    RelAttach (ds ++ [n]) L K f → ∃ (K₁ : TopCat.{0}) (f₁ : L ⟶ K₁)
      (φ : diskBoundary.{0} n ⟶ K₁) (e : Morse.AttachCell φ ≅ K),
      RelAttach ds L K₁ f₁ ∧ f₁ ≫ Morse.cellInl φ ≫ e.hom = f
  | [], _, L, _, _, h => by
      obtain ⟨φ, g, hf, hg⟩ := h
      have : IsIso g := hg
      refine ⟨L, 𝟙 L, φ, (attachIso φ).symm ≪≫ asIso g, (inferInstance : IsIso (𝟙 L)), ?_⟩
      simp [hf]
  | _ :: _, _, _, _, _, h => by
      obtain ⟨φ₁, g₁, hf, h⟩ := h
      obtain ⟨K₁, f₁, φ, e, h₁, hfe⟩ := relAttach_unsnoc h
      exact ⟨K₁, inl φ₁ ≫ f₁, φ, e, ⟨φ₁, f₁, rfl, h₁⟩, by rw [hf, ← hfe]; simp only [Category.assoc]⟩

/-- (R3) The project's relative iterated adjunction spaces are blind ones. -/
theorem relAttach_of_isRel {L K : TopCat.{0}} {j : L ⟶ K} {ds : List ℕ}
    (h : Morse.IsRelCellAttachment L K j ds) : RelAttach ds L K j := by
  induction h with
  | refl => exact (inferInstance : IsIso (𝟙 L))
  | attach _ n φ ih => exact relAttach_snoc ih φ

/-- (R5) A blind relative iterated adjunction space is, up to a homeomorphism compatible with the
maps, a project one; the base may be changed along a homeomorphism `e : L' ≅ L` at the same
time. -/
theorem exists_isRel_of_relAttach {L K : TopCat.{0}} (ds : List ℕ) {f : L ⟶ K}
    (h : RelAttach ds L K f) {L' : TopCat.{0}} (e : L' ≅ L) :
    ∃ (K' : TopCat.{0}) (j : L' ⟶ K') (e' : K' ≅ K),
      Morse.IsRelCellAttachment L' K' j ds ∧ j ≫ e'.hom = e.hom ≫ f := by
  induction ds using List.reverseRecOn generalizing K f with
  | nil =>
    have : IsIso f := h
    exact ⟨L', 𝟙 L', e ≪≫ asIso f, .refl, by simp⟩
  | append_singleton ds n ih =>
    obtain ⟨K₁, f₁, φ, e₁, h₁, hf⟩ := relAttach_unsnoc h
    obtain ⟨K', j, e', hj, hje⟩ := ih h₁
    refine ⟨Morse.AttachCell (φ ≫ e'.inv), j ≫ Morse.cellInl (φ ≫ e'.inv), cellIso e' φ ≪≫ e₁,
      hj.attach n _, ?_⟩
    rw [Iso.trans_hom, Category.assoc, cellInl_cellIso_hom_assoc, reassoc_of% hje, hf]

/-- `∅` (the project's `PEmpty`) `≅ ∅` (the blind `Empty`). -/
def emptyIso : TopCat.of PEmpty.{1} ≅ TopCat.of Empty :=
  TopCat.isoOfHomeo (Homeomorph.empty)

/-- (R4) The project's iterated adjunction spaces are blind ones. -/
theorem relAttach_of_isCellAttachment {K : TopCat.{0}} {ds : List ℕ}
    (h : Morse.IsCellAttachment K ds) :
    ∃ f : TopCat.of Empty ⟶ K, RelAttach ds (TopCat.of Empty) K f := by
  induction h with
  | empty => exact ⟨emptyIso.inv, (inferInstance : IsIso emptyIso.inv)⟩
  | attach _ n φ ih =>
    obtain ⟨f, hf⟩ := ih
    exact ⟨f ≫ Morse.cellInl φ, relAttach_snoc hf φ⟩

/-- (R7) A blind iterated adjunction space is homeomorphic to a project one. -/
theorem exists_isCellAttachment_of_relAttach {K : TopCat.{0}} {ds : List ℕ}
    {f : TopCat.of Empty ⟶ K} (h : RelAttach ds (TopCat.of Empty) K f) :
    ∃ K' : TopCat.{0}, Morse.IsCellAttachment K' ds ∧ Nonempty (K' ≅ K) := by
  obtain ⟨K', j, e', hj, -⟩ := exists_isRel_of_relAttach ds h emptyIso
  exact ⟨K', Morse.IsCellAttachment.of_rel .empty hj, ⟨e'⟩⟩

/-! ### The comparison -/

/-- The blind notion is the project's for some reordering of the cells. -/
theorem T_iff (X : Type) [TopologicalSpace X] (cells : List ℕ) :
    T X cells ↔ ∃ cells' : List ℕ, cells'.Perm cells ∧ Morse.IsFiniteCellComplexType X cells' := by
  constructor
  · rintro ⟨cells', hp, K, ⟨f, hf⟩, ⟨e⟩⟩
    obtain ⟨K', hK', ⟨e'⟩⟩ := exists_isCellAttachment_of_relAttach hf
    exact ⟨cells', hp, K', hK', ⟨e.trans (TopCat.homeoOfIso e'.symm).toHomotopyEquiv⟩⟩
  · rintro ⟨cells', hp, K, hK, he⟩
    exact ⟨cells', hp, K, relAttach_of_isCellAttachment hK, he⟩

theorem P_imp_T (X : Type) [TopologicalSpace X] (cells : List ℕ) :
    Morse.IsFiniteCellComplexType X cells → T X cells :=
  fun h => (T_iff X cells).2 ⟨cells, List.Perm.refl _, h⟩

/-! ### The difference: the order of the cells -/

instance isEmpty_diskBoundary_zero : IsEmpty (diskBoundary.{0} 0) :=
  ⟨fun ⟨⟨x, hx⟩⟩ => by
    have h0 : x = 0 := by ext i; exact i.elim0
    simp [h0] at hx⟩

theorem nonempty_diskBoundary {d : ℕ} (hd : d ≠ 0) : Nonempty (diskBoundary.{0} d) :=
  ⟨⟨⟨EuclideanSpace.single ⟨0, Nat.pos_of_ne_zero hd⟩ 1, by simp⟩⟩⟩

/-- In the project's iterated adjunction spaces, the first cell is a `0`-cell (nothing else can
be attached to `∅`). -/
theorem first_cell_zero {K : TopCat.{0}} {ds : List ℕ} (h : Morse.IsCellAttachment K ds) :
    (ds = [] → IsEmpty K) ∧ ∀ d ds', ds = d :: ds' → d = 0 := by
  induction h with
  | empty => exact ⟨fun _ => inferInstanceAs (IsEmpty PEmpty), fun d ds' h => by simp at h⟩
  | @attach K cells hK n φ ih =>
    refine ⟨fun h => by simp at h, fun d ds' h => ?_⟩
    cases cells with
    | nil =>
      obtain ⟨rfl, -⟩ : n = d ∧ [] = ds' := by simpa using h
      by_contra hd
      have := ih.1 rfl
      obtain ⟨s⟩ := nonempty_diskBoundary (d := n) hd
      exact isEmptyElim (φ s)
    | cons c cs =>
      obtain ⟨rfl, -⟩ : c = d ∧ cs ++ [n] = ds' := by simpa using h
      exact ih.2 c cs rfl

/-- The unique map `∂D⁰ = ∅ → ∅`. -/
def ψ₀ : diskBoundary.{0} 0 ⟶ TopCat.of PEmpty.{1} :=
  TopCat.ofHom ⟨fun s => isEmptyElim s, continuous_of_discreteTopology⟩

/-- The center of `D⁰`. -/
def pt0 : disk.{0} 0 :=
  ⟨⟨0, by simp⟩⟩

/-- The circle `(∅ ∪ e⁰) ∪ e¹`, the `1`-cell attached along the constant map. -/
def circle : TopCat.{0} :=
  Morse.AttachCell (TopCat.ofHom (ContinuousMap.const _ (Morse.cellInr ψ₀ pt0)) :
    diskBoundary.{0} 1 ⟶ Morse.AttachCell ψ₀)

theorem circle_isCellAttachment : Morse.IsCellAttachment circle [0, 1] :=
  (Morse.IsCellAttachment.empty.attach 0 ψ₀).attach 1 _

/-- **Difference**: the circle has cells `{1, 0}` as a multiset (attached as `[0, 1]`), but no
space is built from `∅` with cells in the order `[1, 0]`. -/
theorem differ : T circle [1, 0] ∧ ¬ Morse.IsFiniteCellComplexType circle [1, 0] := by
  refine ⟨⟨[0, 1], List.Perm.swap 1 0 [], circle,
    relAttach_of_isCellAttachment circle_isCellAttachment,
    ⟨ContinuousMap.HomotopyEquiv.refl _⟩⟩, ?_⟩
  rintro ⟨K, hK, -⟩
  exact one_ne_zero ((first_cell_zero hK).2 1 [0] rfl)

/-- The project's notion is false for `[1, 0]` for every space. -/
theorem not_P_one_zero (X : Type) [TopologicalSpace X] :
    ¬ Morse.IsFiniteCellComplexType X [1, 0] := by
  rintro ⟨K, hK, -⟩
  exact one_ne_zero ((first_cell_zero hK).2 1 [0] rfl)

end

end RoundTrip.L2.Morse_IsFiniteCellComplexType
