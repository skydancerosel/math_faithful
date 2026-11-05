import Morse
import RoundTrip.L2.Blind.Morse_CellTower

/-! Layer-2 check of `Morse.CellTower cells` (a functor `K : ℕ ⥤ TopCat`, `K₀` an iterated pushout
from `∅` with cells `cells 0`, each `K_{n+1}` LITERALLY `Kₙ` with the cells `cells (n+1)`
attached by pushouts, `K(n ≤ n+1)` the composite of the inclusions) against the blind textbook
presentations (`T cells = Tower cells`: stages `Kₙ` and maps `ιₙ`, the attachments only up to
homeomorphism compatible with `ιₙ`, adjunction spaces as `Quot`s, `K₀` from `Empty`). Both attach
the cells of a stage in the listed order, head first, along arbitrary continuous maps into the
space built so far.

Data-valued: compared up to isomorphism of towers.
* `toT`: every project tower is a blind tower with the same stages and maps (`toT_K`, `toT_ι`).
* `exists_cellTower`: every blind tower is isomorphic (stagewise homeomorphic, compatibly with
  the inclusions) to a project tower.
So the two notions present the same towers up to isomorphism; the project's is the rigid
(literal-pushout) model. -/

namespace RoundTrip.L2.Morse_CellTower

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

/-! ### Towers: project (`Morse.CellTower`, literal pushouts, a functor) versus blind (`Tower`) -/

section Towers

variable {cells : ℕ → List ℕ}

/-- A project tower is a blind one, with the same stages and the same maps. -/
def toT (C : Morse.CellTower.{0} cells) : Tower cells where
  K n := C.K.obj n
  ι n := C.K.map (homOfLE (Nat.le_add_right n 1))
  base := relAttach_of_isCellAttachment C.zero
  step n := relAttach_of_isRel (C.step n)

/-- A space together with a homeomorphism to `K`. -/
structure Lifted (K : TopCat.{0}) : Type 1 where
  obj : TopCat.{0}
  iso : obj ≅ K

theorem exists_next (τ : Tower cells) (n : ℕ) (s : Lifted (τ.K n)) :
    ∃ (K' : TopCat.{0}) (j : s.obj ⟶ K') (e : K' ≅ τ.K (n + 1)),
      Morse.IsRelCellAttachment s.obj K' j (cells (n + 1)) ∧ j ≫ e.hom = s.iso.hom ≫ τ.ι n :=
  exists_isRel_of_relAttach _ (τ.step n) s.iso

/-- The next stage, rebuilt with the project's pushouts. -/
def next (τ : Tower cells) (n : ℕ) (s : Lifted (τ.K n)) : Lifted (τ.K (n + 1)) :=
  ⟨(exists_next τ n s).choose, (exists_next τ n s).choose_spec.choose_spec.choose⟩

/-- The project's inclusion into the next stage. -/
def nextMap (τ : Tower cells) (n : ℕ) (s : Lifted (τ.K n)) : s.obj ⟶ (next τ n s).obj :=
  (exists_next τ n s).choose_spec.choose

theorem nextMap_spec (τ : Tower cells) (n : ℕ) (s : Lifted (τ.K n)) :
    Morse.IsRelCellAttachment s.obj (next τ n s).obj (nextMap τ n s) (cells (n + 1)) ∧
      nextMap τ n s ≫ (next τ n s).iso.hom = s.iso.hom ≫ τ.ι n :=
  (exists_next τ n s).choose_spec.choose_spec.choose_spec

theorem exists_base (τ : Tower cells) :
    ∃ K' : TopCat.{0}, Morse.IsCellAttachment K' (cells 0) ∧ Nonempty (K' ≅ τ.K 0) := by
  obtain ⟨f, hf⟩ := τ.base
  exact exists_isCellAttachment_of_relAttach hf

/-- The stages, rebuilt with the project's pushouts. -/
def stage (τ : Tower cells) : ∀ n, Lifted (τ.K n)
  | 0 => ⟨(exists_base τ).choose, (exists_base τ).choose_spec.2.some⟩
  | n + 1 => next τ n (stage τ n)

/-- The project tower rebuilt from a blind one. -/
def ofT (τ : Tower cells) : Morse.CellTower.{0} cells :=
  Morse.CellTower.ofSequence (fun n => (stage τ n).obj) (fun n => nextMap τ n (stage τ n))
    (exists_base τ).choose_spec.1 (fun n => (nextMap_spec τ n (stage τ n)).1)

/-- Every blind tower is isomorphic (stagewise homeomorphic, compatibly with the inclusions) to
a project tower. -/
theorem ofT_iso (τ : Tower cells) (n : ℕ) :
    (ofT τ).K.map (homOfLE (Nat.le_add_right n 1)) ≫ (stage τ (n + 1)).iso.hom =
      (stage τ n).iso.hom ≫ τ.ι n := by
  have h := Functor.ofSequence_map_homOfLE_succ (X := fun n => (stage τ n).obj)
    (fun n => nextMap τ n (stage τ n)) n
  change (Functor.ofSequence (fun n => nextMap τ n (stage τ n))).map _ ≫ _ = _
  rw [h]
  exact (nextMap_spec τ n (stage τ n)).2

theorem exists_cellTower (τ : Tower cells) :
    ∃ (C : Morse.CellTower.{0} cells) (e : ∀ n, C.K.obj n ≅ τ.K n),
      ∀ n, C.K.map (homOfLE (Nat.le_add_right n 1)) ≫ (e (n + 1)).hom = (e n).hom ≫ τ.ι n :=
  ⟨ofT τ, fun n => (stage τ n).iso, ofT_iso τ⟩

end Towers

theorem toT_K {cells : ℕ → List ℕ} (C : Morse.CellTower.{0} cells) (n : ℕ) :
    (toT C).K n = C.K.obj n :=
  rfl

theorem toT_ι {cells : ℕ → List ℕ} (C : Morse.CellTower.{0} cells) (n : ℕ) :
    (toT C).ι n = C.K.map (homOfLE (Nat.le_add_right n 1)) :=
  rfl

/-- **Agreement up to isomorphism of towers**: every project tower is a blind one (`toT`, same
stages and maps) and every blind tower is isomorphic to (the image of) a project one. -/
theorem agree {cells : ℕ → List ℕ} (τ : T cells) :
    ∃ (C : Morse.CellTower.{0} cells) (e : ∀ n, (toT C).K n ≅ τ.K n),
      ∀ n, (toT C).ι n ≫ (e (n + 1)).hom = (e n).hom ≫ τ.ι n :=
  exists_cellTower τ

end

end RoundTrip.L2.Morse_CellTower
