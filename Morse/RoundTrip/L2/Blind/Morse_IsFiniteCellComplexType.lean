import Morse
/-! Layer-2 blind definition of Morse_IsFiniteCellComplexType. Textbook: Milnor, *Morse Theory*,
§3, Theorem 3.5, p. 20 ("`X` has the homotopy type of a finite CW-complex with one cell of
dimension `λ` for each …"): `X` is homotopy equivalent to a space built from `∅` by successively
attaching cells of the given dimensions along continuous attaching maps.
Choices:
- DOUBT (order): a CW complex's cells are unordered, so the list `cells` is read as a multiset:
  `T` asks for SOME ordering `cells'` of `cells` (`List.Perm`) and a space `K` obtained from `∅`
  by attaching cells of dimensions `cells'` one at a time in that order. (With arbitrary
  attaching maps, up to homotopy type this is the same as "homotopy equivalent to a genuine
  finite CW complex with these cells", by cellular approximation and Milnor's Lemmas 3.6-3.7.)
  The listed-order reading would be strictly stronger: e.g. `[0,1]` (an interval) satisfies `T`
  for `[0,1,0]` via the order `[0,0,1]`, but no space built in the order `0,1,0` is contractible.
- Adjunction spaces built literally (own `Attach`: quotient of `Y ⊔ Dᵈ` by `b ∼ φ b`,
  Mathlib's `TopCat.disk`/`diskBoundary`), "built from `∅`" up to homeomorphism (`RelAttach`,
  `TopCat.of Empty`); homotopy equivalence = Mathlib's `ContinuousMap.HomotopyEquiv`. -/
namespace RoundTrip.L2.Morse_IsFiniteCellComplexType

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

/-- `K ≅ ∅ ∪ e^{d₁} ∪ e^{d₂} ∪ ⋯` (cells `ds` attached in the listed order). -/
def IsCellAttach (K : TopCat.{0}) (ds : List ℕ) : Prop :=
  ∃ f : TopCat.of Empty ⟶ K, RelAttach ds (TopCat.of Empty) K f

/-- The textbook notion: `X` has the homotopy type of a cell complex with cells of dimensions
`cells` (attached in some order). -/
def T (X : Type) [TopologicalSpace X] (cells : List ℕ) : Prop :=
  ∃ cells' : List ℕ, cells'.Perm cells ∧
    ∃ K : TopCat.{0}, IsCellAttach K cells' ∧ Nonempty (ContinuousMap.HomotopyEquiv X K)

end RoundTrip.L2.Morse_IsFiniteCellComplexType
