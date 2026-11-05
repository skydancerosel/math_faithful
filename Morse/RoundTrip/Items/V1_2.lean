import Morse
import RoundTrip.Check
import RoundTrip.Blind.V1_2

namespace RoundTrip.V1_2

/-- The declarations of this item (`Morse.AttachCell`, `Morse.cellDesc`) are both definitions:
there is no listed theorem, so the project's formal statement is the empty conjunction. -/
def A : Prop := True

theorem A_holds : A := trivial

instance : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance

theorem bdry_zero_isEmpty : IsEmpty (Bdry 0) :=
  ⟨fun x => by
    have h1 : ‖(x : EuclideanSpace ℝ (Fin 0))‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
    rw [Subsingleton.elim (x : EuclideanSpace ℝ (Fin 0)) 0, norm_zero] at h1
    exact zero_ne_one h1⟩

/-- The point of `e^0`. -/
def cell0 : Cell 0 := ⟨0, Metric.mem_closedBall_self zero_le_one⟩

instance : Subsingleton (Cell 0) :=
  ⟨fun _ _ => Subtype.ext (Subsingleton.elim (α := EuclideanSpace ℝ (Fin 0)) _ _)⟩

/-- `Y ∪_g e^0 ≃ₜ Y ⊕ pt`. -/
noncomputable def attachZero (Y : Type) [TopologicalSpace Y] (g : C(Bdry 0, Y)) :
    Attach g ≃ₜ (Y ⊕ Unit) where
  toFun := Quot.lift (Sum.map id (fun _ => ())) (by
    rintro _ _ ⟨x, -⟩
    exact (bdry_zero_isEmpty.false x).elim)
  invFun := Sum.elim (inl g) (fun _ => inr g cell0)
  left_inv := by
    intro a
    induction a using Quot.ind with
    | mk a =>
      rcases a with y | c
      · rfl
      · change Quot.mk _ (Sum.inr cell0) = Quot.mk _ (Sum.inr c)
        rw [Subsingleton.elim cell0 c]
  right_inv := by
    rintro (y | u)
    · rfl
    · rfl
  continuous_toFun := continuous_quot_lift _ (continuous_id.sumMap continuous_const)
  continuous_invFun := (inl g).continuous.sumElim continuous_const

/-- `B` holds outright. -/
theorem B_holds : B := by
  refine ⟨fun Y _ k g x => (Quot.sound ⟨x, rfl, rfl⟩), bdry_zero_isEmpty, ⟨cell0⟩, inferInstance,
    fun Y _ g => ⟨attachZero Y g⟩⟩

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

/-! ### Vocabulary check (not part of `A`): the blind `Attach g` is homeomorphic to the
project's `Morse.AttachCell` (Mathlib pushout), compatibly with the inclusion of `Y`. -/

section VocabularyCheck
open CategoryTheory Limits TopCat
noncomputable section

/-! ### Glue: the blind `Attach g` (a `Quot`) is homeomorphic to the project's pushout. -/

section Glue

variable {k : ℕ} {Y : Type} [TopologicalSpace Y] (g : C(Bdry k, Y))
  (φ : ∂𝔻 k ⟶ TopCat.of Y) (hg : ∀ x : Bdry k, φ (ULift.up x) = g x)
include hg

/-- `Attach g → X ∪_φ e^k`. -/
def fwd : C(Attach g, Morse.AttachCell φ) :=
  ⟨Quot.lift (Sum.elim (Morse.cellInl φ) (fun c => Morse.cellInr φ (ULift.up c : 𝔻 k)))
    (by
      rintro _ _ ⟨x, rfl, rfl⟩
      have h := Morse.cellInl_apply_eq φ (ULift.up x)
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← hg x]
      exact h.symm),
   continuous_quot_lift _ ((Morse.cellInl φ).hom.continuous.sumElim
      ((Morse.cellInr φ).hom.continuous.comp continuous_uliftUp))⟩

/-- `X ∪_φ e^k → Attach g`. -/
def bwd : Morse.AttachCell φ ⟶ TopCat.of (Attach g) :=
  Morse.cellDesc φ (inl g) ((inr g).comp ⟨ULift.down, continuous_uliftDown⟩) (by
      rintro ⟨x⟩
      change Quot.mk _ (Sum.inl (φ (ULift.up x))) = Quot.mk _ (Sum.inr (bdryToCell x))
      rw [hg x]
      exact (Quot.sound ⟨x, rfl, rfl⟩).symm)

theorem bwd_inl (y : Y) : bwd g φ hg (Morse.cellInl φ y) = inl g y :=
  by unfold bwd; exact Morse.cellDesc_inl (X := TopCat.of Y) _ _ _ _ y

theorem bwd_inr (d : 𝔻 k) : bwd g φ hg (Morse.cellInr φ d) = inr g d.down :=
  by unfold bwd; exact Morse.cellDesc_inr (X := TopCat.of Y) _ _ _ _ d

/-- The homeomorphism `Attach g ≃ₜ X ∪_φ e^k`. -/
def homeo : Attach g ≃ₜ Morse.AttachCell φ where
  toFun := fwd g φ hg
  invFun := bwd g φ hg
  left_inv := by
    intro a
    induction a using Quot.ind with
    | mk a =>
      rcases a with y | c
      · exact bwd_inl g φ hg y
      · exact bwd_inr g φ hg (ULift.up c)
  right_inv := by
    intro z
    have h : bwd g φ hg ≫ TopCat.ofHom (fwd g φ hg) = 𝟙 _ :=
      Morse.attachCell_hom_ext φ (fun y => by
        change fwd g φ hg (bwd g φ hg (Morse.cellInl φ y)) = _
        rw [bwd_inl]; rfl) (fun d => by
        change fwd g φ hg (bwd g φ hg (Morse.cellInr φ d)) = _
        rw [bwd_inr]; rfl)
    exact ConcreteCategory.congr_hom h z
  continuous_toFun := (fwd g φ hg).continuous
  continuous_invFun := (bwd g φ hg).hom.continuous

theorem homeo_inl (y : Y) : homeo g φ hg (inl g y) = Morse.cellInl φ y := rfl

theorem homeo_symm_inl (y : Y) : (homeo g φ hg).symm (Morse.cellInl φ y) = inl g y :=
  bwd_inl g φ hg y

end Glue

end
end VocabularyCheck

#rt_check RoundTrip.V1_2.A_to_B [Morse.AttachCell, Morse.cellDesc]
#rt_check RoundTrip.V1_2.B_to_A [Morse.AttachCell, Morse.cellDesc]
#rt_overlap RoundTrip.V1_2.B_to_A [Morse.AttachCell, Morse.cellDesc]

end RoundTrip.V1_2
