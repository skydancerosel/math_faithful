import Morse
import RoundTrip.L2.Blind.Morse_IsCountableCellComplexType

/-! Layer-2 check of `Morse.IsCountableCellComplexType X cells` (`X ≃ₕ` the MAPPING TELESCOPE of a
project cell tower) against the blind textbook definition (`T X cells`: `X ≃ₕ` the UNION
`⋃ Kₙ` with the weak topology, i.e. the COLIMIT in `TopCat`, of a blind tower).

* The towers agree up to isomorphism (as in the `Morse_CellTower` item: `toT`,
  `exists_cellTower`), and mapping telescopes of isomorphic sequences are homeomorphic
  (`teleHomeo`). Hence (`P_iff_Ttele`, proved) the project's notion is EXACTLY the blind one with
  the colimit replaced by the mapping telescope of the same tower.
* The remaining gap is the comparison `telescope ≃ₕ colimit` for a tower of cell attachments
  (Milnor's Appendix, Example 2 / J. H. C. Whitehead; true since each `Kₙ → K_{n+1}` is a closed
  cofibration), which the project explicitly does not formalize (docstring of
  `Morse.IsCountableCellComplexType`). Under it the two notions agree (`agree_of`); proving it
  needs the homotopy extension property of cell attachments, substantial new mathematics. -/

namespace RoundTrip.L2.Morse_IsCountableCellComplexType

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

/-! ### Mapping telescopes of isomorphic sequences -/

open scoped unitInterval

section Tele

variable {F G : ℕ ⥤ TopCat.{0}}

/-- The map of mapping telescopes induced by maps of the stages commuting with the successor
maps. -/
def teleMap (α : ∀ n, F.obj n ⟶ G.obj n)
    (hα : ∀ n, F.map (homOfLE (Nat.le_add_right n 1)) ≫ α (n + 1) =
      α n ≫ G.map (homOfLE (Nat.le_add_right n 1))) :
    C(Morse.MappingTelescope F, Morse.MappingTelescope G) :=
  Morse.MappingTelescope.desc F
    (fun n => ⟨fun q => Morse.MappingTelescope.mk G n (α n q.1) q.2,
      (Morse.MappingTelescope.continuous_mk G n).comp
        ((α n).hom.continuous.prodMap continuous_id)⟩)
    (fun n k => by
      change Morse.MappingTelescope.mk G (n + 1) (α (n + 1) (Morse.tmap F _ k)) 0 =
        Morse.MappingTelescope.mk G n (α n k) 1
      rw [Morse.MappingTelescope.mk_one]
      congr 1
      exact ConcreteCategory.congr_hom (hα n) k)

theorem teleMap_mk (α : ∀ n, F.obj n ⟶ G.obj n)
    (hα : ∀ n, F.map (homOfLE (Nat.le_add_right n 1)) ≫ α (n + 1) =
      α n ≫ G.map (homOfLE (Nat.le_add_right n 1))) (n : ℕ) (k : F.obj n) (t : I) :
    teleMap α hα (Morse.MappingTelescope.mk F n k t) = Morse.MappingTelescope.mk G n (α n k) t :=
  rfl

/-- Mapping telescopes of isomorphic sequences are homeomorphic. -/
def teleHomeo (α : ∀ n, F.obj n ≅ G.obj n)
    (hα : ∀ n, F.map (homOfLE (Nat.le_add_right n 1)) ≫ (α (n + 1)).hom =
      (α n).hom ≫ G.map (homOfLE (Nat.le_add_right n 1))) :
    Morse.MappingTelescope F ≃ₜ Morse.MappingTelescope G where
  toFun := teleMap (fun n => (α n).hom) hα
  invFun := teleMap (fun n => (α n).inv) (fun n => by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hα n, Category.assoc, Iso.hom_inv_id,
      Category.comp_id])
  left_inv z := by
    obtain ⟨n, k, t, rfl⟩ := Morse.MappingTelescope.exists_mk F z
    rw [teleMap_mk, teleMap_mk, Iso.hom_inv_id_apply]
  right_inv z := by
    obtain ⟨n, k, t, rfl⟩ := Morse.MappingTelescope.exists_mk G z
    rw [teleMap_mk, teleMap_mk, Iso.inv_hom_id_apply]
  continuous_toFun := (teleMap _ _).continuous
  continuous_invFun := (teleMap _ _).continuous

end Tele

/-! ### The comparison -/

/-- The blind notion with the union (colimit) replaced by the mapping telescope. -/
def Ttele (X : Type) [TopologicalSpace X] (cells : ℕ → List ℕ) : Prop :=
  ∃ τ : Tower cells,
    Nonempty (ContinuousMap.HomotopyEquiv X (Morse.MappingTelescope (Functor.ofSequence τ.ι)))

/-- **The project's notion is the blind one with the colimit replaced by the telescope.** -/
theorem P_iff_Ttele (X : Type) [TopologicalSpace X] (cells : ℕ → List ℕ) :
    Morse.IsCountableCellComplexType X cells ↔ Ttele X cells := by
  constructor
  · rintro ⟨C, ⟨e⟩⟩
    refine ⟨toT C, ⟨e.trans (teleHomeo (G := Functor.ofSequence (toT C).ι)
      (fun n => Iso.refl (C.K.obj n)) (fun n => ?_)).toHomotopyEquiv⟩⟩
    have h := Functor.ofSequence_map_homOfLE_succ (toT C).ι n
    simp only [Iso.refl_hom]
    exact h.symm
  · rintro ⟨τ, ⟨e⟩⟩
    obtain ⟨C, eC, hC⟩ := exists_cellTower τ
    refine ⟨C, ⟨e.trans (teleHomeo (F := C.K) (G := Functor.ofSequence τ.ι) eC
      (fun n => ?_)).symm.toHomotopyEquiv⟩⟩
    have h := Functor.ofSequence_map_homOfLE_succ τ.ι n
    rw [h]
    exact hC n

/-- **Agreement, given the telescope/colimit comparison** (Milnor's Appendix, Example 2; not
formalized in the project). -/
theorem agree_of (cells : ℕ → List ℕ)
    (hW : ∀ τ : Tower cells, Nonempty (ContinuousMap.HomotopyEquiv
      (Morse.MappingTelescope (Functor.ofSequence τ.ι)) τ.total))
    (X : Type) [TopologicalSpace X] :
    Morse.IsCountableCellComplexType X cells ↔ T X cells := by
  rw [P_iff_Ttele]
  constructor
  · rintro ⟨τ, ⟨e⟩⟩
    exact ⟨τ, ⟨e.trans (hW τ).some⟩⟩
  · rintro ⟨τ, ⟨e⟩⟩
    exact ⟨τ, ⟨e.trans (hW τ).some.symm⟩⟩

end

end RoundTrip.L2.Morse_IsCountableCellComplexType
