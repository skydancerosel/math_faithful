import Morse
import RoundTrip.L2.Blind.Morse_AttachCell

/-! Layer-2 check of `Morse.AttachCell φ` (`X ∪_φ eⁿ` as the pushout of `X ← ∂Dⁿ → Dⁿ` in `TopCat`,
an object chosen by `colimit`) against the blind textbook adjunction space (`T φ`: the `Quot` of
`X ⊔ Dⁿ` by `b ∼ φ b`, with the quotient topology). Both use Mathlib's `TopCat.disk`,
`TopCat.diskBoundary` and `TopCat.diskBoundaryInclusion`. They are homeomorphic (isomorphic in
`TopCat`), compatibly with the inclusions of `X` and with the characteristic maps of the cell:
the pushout is characterised by its universal property and the quotient has it. -/

namespace RoundTrip.L2.Morse_AttachCell

open CategoryTheory Limits TopCat

noncomputable section

variable {n : ℕ} {X : TopCat.{0}}

/-- The inclusion `X → T φ`. -/
def inl (φ : diskBoundary.{0} n ⟶ X) : X ⟶ T φ :=
  TopCat.ofHom ⟨fun x => Quot.mk (Rel φ) (Sum.inl x), continuous_quot_mk.comp continuous_inl⟩

/-- The characteristic map `Dⁿ → T φ`. -/
def inr (φ : diskBoundary.{0} n ⟶ X) : disk.{0} n ⟶ T φ :=
  TopCat.ofHom ⟨fun d => Quot.mk (Rel φ) (Sum.inr d), continuous_quot_mk.comp continuous_inr⟩

theorem inl_glue (φ : diskBoundary.{0} n ⟶ X) (s : diskBoundary.{0} n) :
    (inl φ).hom (φ s) = (inr φ).hom (diskBoundaryInclusion n s) :=
  (Quot.sound ⟨s, rfl, rfl⟩).symm

/-- `T φ → X ∪_φ eⁿ`, on representatives. -/
def fwd (φ : diskBoundary.{0} n ⟶ X) : T φ ⟶ Morse.AttachCell φ :=
  TopCat.ofHom ⟨Quot.lift (r := Rel φ) (Sum.elim (Morse.cellInl φ) (Morse.cellInr φ)) (by
      rintro _ _ ⟨s, rfl, rfl⟩
      exact (Morse.cellInl_apply_eq φ s).symm),
    continuous_quot_lift _
      ((Morse.cellInl φ).hom.continuous.sumElim (Morse.cellInr φ).hom.continuous)⟩

/-- **Agreement**: the blind adjunction space is isomorphic in `TopCat` (homeomorphic) to the
project's pushout. -/
def agree (φ : diskBoundary.{0} n ⟶ X) : T φ ≅ Morse.AttachCell φ where
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

/-- The homeomorphism carries the inclusion of `X` to the inclusion of `X`. -/
theorem inl_agree (φ : diskBoundary.{0} n ⟶ X) : inl φ ≫ (agree φ).hom = Morse.cellInl φ := by
  ext x
  rfl

/-- The homeomorphism carries the characteristic map of the cell to that of the cell. -/
theorem inr_agree (φ : diskBoundary.{0} n ⟶ X) : inr φ ≫ (agree φ).hom = Morse.cellInr φ := by
  ext x
  rfl

/-- The same, as a homeomorphism of the underlying spaces. -/
def agreeHomeo (φ : diskBoundary.{0} n ⟶ X) : T φ ≃ₜ Morse.AttachCell φ :=
  TopCat.homeoOfIso (agree φ)

end

end RoundTrip.L2.Morse_AttachCell
