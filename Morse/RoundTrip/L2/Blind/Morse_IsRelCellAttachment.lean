import Morse
/-! Layer-2 blind definition of Morse_IsRelCellAttachment. Textbook: Milnor, *Morse Theory*, §3,
p. 14 and Appendix; Hatcher, *Algebraic Topology*, ch. 0 / ch. 4 (`K` is obtained from `L` by
attaching cells `e^{d₁}, e^{d₂}, …` one at a time: `K ≅ L ∪_{φ₁} e^{d₁} ∪_{φ₂} e^{d₂} ∪ ⋯`, each
`φᵢ : S^{dᵢ-1} → (space built so far)` an arbitrary continuous map, and `f : L → K` the
inclusion).
Choices:
- The cells are attached in the listed order, head of the list first; each attaching map lands in
  the space built so far (so it may meet earlier cells of the list).
- Adjunction space `Y ∪_φ eᵈ` built literally (own `Attach`): quotient of the topological sum
  `Y ⊔ Dᵈ` by `b ∼ φ b` for `b ∈ ∂Dᵈ`, with Mathlib's `TopCat.disk`/`diskBoundary`.
- "`K` is" the iterated adjunction space up to homeomorphism compatible with `f`: `T L K f []`
  iff `f` is an isomorphism of `TopCat` (a homeomorphism); `T L K f (d :: ds)` iff
  `f = (L ↪ L ∪_φ eᵈ) ≫ g` for some `φ : ∂Dᵈ → L` and some `g` with `T (L ∪_φ eᵈ) K g ds`. -/
namespace RoundTrip.L2.Morse_IsRelCellAttachment

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

/-- The textbook notion. -/
def T (L K : TopCat.{0}) : (L ⟶ K) → List ℕ → Prop :=
  fun f ds => RelAttach ds L K f

end RoundTrip.L2.Morse_IsRelCellAttachment
