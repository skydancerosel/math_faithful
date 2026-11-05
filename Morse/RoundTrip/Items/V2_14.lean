import Morse
import RoundTrip.Check
import RoundTrip.Blind.V2_14

open CategoryTheory Limits TopCat

noncomputable section

namespace RoundTrip.V2_14

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

theorem homeo_inr (c : Cell k) : homeo g φ hg (inr g c) = Morse.cellInr φ (ULift.up c : 𝔻 k) := rfl

theorem homeo_symm_inr (d : 𝔻 k) : (homeo g φ hg).symm (Morse.cellInr φ d) = inr g d.down :=
  bwd_inr g φ hg d

end Glue

/-- The project's statement (Lemma 3.7 and the Assertion), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.lemma_3_7.{0} ∧ type_of% @Morse.homotopic_of_leftInv_rightInv.{0, 0}

theorem A_holds : A := ⟨@Morse.lemma_3_7.{0}, @Morse.homotopic_of_leftInv_rightInv.{0, 0}⟩

theorem A_to_B : A → B := by
  intro hA
  refine ⟨?_, ?_⟩
  · intro X Y _ _ lam φ f
    let ψ : ∂𝔻 lam ⟶ TopCat.of X := TopCat.ofHom (φ.comp ⟨ULift.down, continuous_uliftDown⟩)
    obtain ⟨K, hK1, hK2⟩ := hA.1 ψ (Y := TopCat.of Y) f
    let e₀ := homeo φ ψ (fun _ => rfl)
    let e₁ := homeo (f.toFun.comp φ) (ψ ≫ TopCat.ofHom f.toFun) (fun _ => rfl)
    refine ⟨e₀.toHomotopyEquiv.trans (K.trans e₁.symm.toHomotopyEquiv), fun x => ?_, fun c => ?_⟩
    · change e₁.symm (K.toFun (e₀ (inl φ x))) = inl (f.toFun.comp φ) (f x)
      rw [homeo_inl, hK1, homeo_symm_inl]
    · change e₁.symm (K.toFun (e₀ (inr φ c))) = inr (f.toFun.comp φ) c
      rw [homeo_inr]
      exact (congrArg e₁.symm (hK2 (ULift.up c : 𝔻 lam))).trans (homeo_symm_inr _ _ _ _)
  · intro A' B' _ _ F L R hL hR
    have hRF := hA.2 hL hR
    refine ⟨⟨⟨F, R, hRF, hR⟩, fun _ => rfl⟩, hRF, ?_⟩
    -- `L ≃ L (F R) = (L F) R ≃ R`, hence `F L ≃ F R ≃ id`
    have h1 : (L.comp (F.comp R)).Homotopic (L.comp (ContinuousMap.id B')) :=
      (ContinuousMap.Homotopic.refl L).comp hR
    have h2 : ((L.comp F).comp R).Homotopic ((ContinuousMap.id A').comp R) :=
      hL.comp (ContinuousMap.Homotopic.refl R)
    rw [ContinuousMap.comp_id] at h1
    rw [ContinuousMap.id_comp, ContinuousMap.comp_assoc] at h2
    have hLR : L.Homotopic R := h1.symm.trans h2
    exact ((ContinuousMap.Homotopic.refl F).comp hLR).trans hR

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, fun {A' B'} _ _ {F L R} hL hR => (hB.2 A' B' F L R hL hR).2.1⟩
  intro n X φ Y e
  let g : C(Bdry n, X) := φ.hom.comp ⟨ULift.up, continuous_uliftUp⟩
  obtain ⟨K, hK1, hK2⟩ := hB.1 X Y n g e
  let e₀ := homeo g (Y := X) φ (fun _ => rfl)
  let e₁ := homeo (e.toFun.comp g) (Y := Y) (φ ≫ TopCat.ofHom e.toFun) (fun _ => rfl)
  refine ⟨e₀.symm.toHomotopyEquiv.trans (K.trans e₁.toHomotopyEquiv), fun x => ?_, fun d => ?_⟩
  · change e₁ (K (e₀.symm (Morse.cellInl φ x))) = _
    rw [homeo_symm_inl, hK1, homeo_inl]
  · change e₁ (K (e₀.symm (Morse.cellInr φ d))) = _
    rw [homeo_symm_inr, hK2, homeo_inr]
    rfl

#rt_check RoundTrip.V2_14.A_to_B [Morse.lemma_3_7, Morse.homotopic_of_leftInv_rightInv]
#rt_check RoundTrip.V2_14.B_to_A [Morse.lemma_3_7, Morse.homotopic_of_leftInv_rightInv]
#rt_overlap RoundTrip.V2_14.B_to_A [Morse.lemma_3_7, Morse.homotopic_of_leftInv_rightInv]

end RoundTrip.V2_14

end
