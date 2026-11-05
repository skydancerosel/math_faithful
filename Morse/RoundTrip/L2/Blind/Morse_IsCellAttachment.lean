import Morse
/-! Layer-2 blind definition of Morse_IsCellAttachment. Textbook: Milnor, *Morse Theory*, §3,
p. 14 and Theorem 3.5 (a space obtained from the empty space by attaching cells `e^{d₁}, e^{d₂},
…` one after another, each along an arbitrary continuous map `S^{dᵢ-1} → (space built so far)`).
Choices:
- Cells attached in the listed order, head first; each attaching map lands in the whole space
  built so far. (Necessarily the first cell is a 0-cell, since `S^{d-1} → ∅` exists only for
  `d = 0`.)
- Adjunction space built literally (own `Attach`: quotient of `Y ⊔ Dᵈ` by `b ∼ φ b`, Mathlib's
  `TopCat.disk`/`diskBoundary`), and "`K` is" that iterated adjunction space up to
  homeomorphism (`RelAttach`, as in the blind file of Morse_IsRelCellAttachment: the last
  comparison map is an isomorphism of `TopCat`). The empty space is `TopCat.of Empty`; the map
  out of it is unique, so `∃` over it is harmless. `T K []` iff `K` is empty. -/
namespace RoundTrip.L2.Morse_IsCellAttachment

open CategoryTheory TopCat

/-- The identification on `X ⊔ Dⁿ`: a boundary point `b ∈ ∂Dⁿ` is glued to `φ b ∈ X`. -/
def Rel {n : ℕ} {X : TopCat.{0}} (φ : diskBoundary.{0} n ⟶ X) :
    (X ⊕ disk.{0} n) → (X ⊕ disk.{0} n) → Prop :=
  fun a c => ∃ b : diskBoundary.{0} n,
    a = Sum.inr ((diskBoundaryInclusion n).hom b) ∧ c = Sum.inl (φ.hom b)

/-- The adjunction space `X ∪_φ eⁿ = (X ⊔ Dⁿ)/(b ∼ φ b)` with the quotient topology. -/
noncomputable def Attach {n : ℕ} {X : TopCat.{0}} (φ : diskBoundary.{0} n ⟶ X) : TopCat.{0} :=
  TopCat.of (Quot (Rel φ))

/-- The inclusion `X ↪ X ∪_φ eⁿ`. -/
noncomputable def inl {n : ℕ} {X : TopCat.{0}} (φ : diskBoundary.{0} n ⟶ X) : X ⟶ Attach φ :=
  TopCat.ofHom ⟨fun x => Quot.mk (Rel φ) (Sum.inl x), continuous_quot_mk.comp continuous_inl⟩

/-- `f : L → K` exhibits `K` as `L` with cells of dimensions `ds` attached one at a time. -/
def RelAttach : List ℕ → (L K : TopCat.{0}) → (L ⟶ K) → Prop
  | [], _, _, f => IsIso f
  | d :: ds, L, K, f => ∃ (φ : diskBoundary.{0} d ⟶ L) (g : Attach φ ⟶ K),
      f = inl φ ≫ g ∧ RelAttach ds (Attach φ) K g

/-- The textbook notion: `K ≅ ∅ ∪ e^{d₁} ∪ e^{d₂} ∪ ⋯` (cells `ds` attached in order). -/
def T : TopCat.{0} → List ℕ → Prop :=
  fun K ds => ∃ f : TopCat.of Empty ⟶ K, RelAttach ds (TopCat.of Empty) K f

end RoundTrip.L2.Morse_IsCellAttachment
