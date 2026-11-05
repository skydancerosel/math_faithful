import Morse
import RoundTrip.L2.Blind.Morse_IsCellAttachment

/-! Layer-2 check of `Morse.IsCellAttachment K cells` (an inductive predicate: `K` is LITERALLY the
iterated pushout `∅ ∪_{φ₁} e^{d₁} ∪ ⋯` in `TopCat`, `∅ = PEmpty`, cells attached in the listed
order, head first) against the blind textbook definition (`T K cells`: the same iterated
adjunction space, built from `Empty` with `Quot`s, and `K` only up to homeomorphism).

* `P_imp_T`: the project's notion implies the blind one.
* `agree`: the blind notion is exactly the closure of the project's under homeomorphism:
  `T K cells ↔ ∃ K', P K' cells ∧ Nonempty (K' ≅ K)`.
The project's predicate depends on the literal `TopCat` object `K` (not only on its homeomorphism
class); no concrete `K` separating the two can be exhibited in Lean (it would require refuting an
equality of types of the same cardinality), and the project only uses the predicate inside
`∃ K, IsCellAttachment K cells ∧ (X ≃ₕ K)`, which is invariant. Ordering conventions agree (both
in the listed order, head first, each cell along any continuous map into the space built so far).

The glue is shared with the other cell-complex items of this group (see
`Morse_IsRelCellAttachment`). -/

namespace RoundTrip.L2.Morse_IsCellAttachment

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

theorem P_imp_T (K : TopCat.{0}) (ds : List ℕ) : Morse.IsCellAttachment K ds → T K ds :=
  relAttach_of_isCellAttachment

/-- **Agreement up to homeomorphism**: the blind notion is the closure of the project's under
homeomorphism. -/
theorem agree (K : TopCat.{0}) (ds : List ℕ) :
    T K ds ↔ ∃ K' : TopCat.{0}, Morse.IsCellAttachment K' ds ∧ Nonempty (K' ≅ K) := by
  constructor
  · rintro ⟨f, hf⟩
    exact exists_isCellAttachment_of_relAttach hf
  · rintro ⟨K', hK', ⟨e⟩⟩
    obtain ⟨f, hf⟩ := relAttach_of_isCellAttachment hK'
    exact ⟨f ≫ e.hom, relAttach_comp_iso hf e⟩

end

end RoundTrip.L2.Morse_IsCellAttachment
