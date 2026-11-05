import Morse
import RoundTrip.Check
import RoundTrip.Blind.V2_13

open CategoryTheory Limits TopCat

noncomputable section

namespace RoundTrip.V2_13

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

/-- The project's statement (Lemma 3.6), universe instantiated at `0`. -/
def A : Prop := type_of% @Morse.lemma_3_6.{0}

theorem A_holds : A := @Morse.lemma_3_6.{0}

theorem A_to_B : A → B := by
  intro hA X _ lam φ₀ φ₁ hφ
  let ψ₀ : ∂𝔻 lam ⟶ TopCat.of X := TopCat.ofHom (φ₀.comp ⟨ULift.down, continuous_uliftDown⟩)
  let ψ₁ : ∂𝔻 lam ⟶ TopCat.of X := TopCat.ofHom (φ₁.comp ⟨ULift.down, continuous_uliftDown⟩)
  have hψ : ψ₀.hom.Homotopic ψ₁.hom := hφ.comp (ContinuousMap.Homotopic.refl _)
  obtain ⟨K, hK⟩ := @hA lam (TopCat.of X) ψ₀ ψ₁ hψ
  let e₀ := homeo φ₀ ψ₀ (fun _ => rfl)
  let e₁ := homeo φ₁ ψ₁ (fun _ => rfl)
  refine ⟨e₀.toHomotopyEquiv.trans (K.trans e₁.symm.toHomotopyEquiv), fun x => ?_⟩
  change e₁.symm (K (e₀ (inl φ₀ x))) = inl φ₁ x
  rw [homeo_inl, hK, homeo_symm_inl]

theorem B_to_A : B → A := by
  intro hB n X φ₀ φ₁ hφ
  let g₀ : C(Bdry n, X) := φ₀.hom.comp ⟨ULift.up, continuous_uliftUp⟩
  let g₁ : C(Bdry n, X) := φ₁.hom.comp ⟨ULift.up, continuous_uliftUp⟩
  have hg : g₀.Homotopic g₁ := hφ.comp (ContinuousMap.Homotopic.refl _)
  obtain ⟨K, hK⟩ := hB X n g₀ g₁ hg
  let e₀ := homeo g₀ (Y := X) φ₀ (fun _ => rfl)
  let e₁ := homeo g₁ (Y := X) φ₁ (fun _ => rfl)
  refine ⟨e₀.symm.toHomotopyEquiv.trans (K.trans e₁.toHomotopyEquiv), fun x => ?_⟩
  change e₁ (K (e₀.symm (Morse.cellInl φ₀ x))) = Morse.cellInl φ₁ x
  rw [homeo_symm_inl, hK, homeo_inl]

#rt_check RoundTrip.V2_13.A_to_B [Morse.lemma_3_6, Morse.lemma36Homotopy, Morse.cellHomotopy]
#rt_check RoundTrip.V2_13.B_to_A [Morse.lemma_3_6, Morse.lemma36Homotopy, Morse.cellHomotopy]
#rt_overlap RoundTrip.V2_13.B_to_A [Morse.lemma_3_6, Morse.lemma36Homotopy, Morse.cellHomotopy]

end RoundTrip.V2_13

end
