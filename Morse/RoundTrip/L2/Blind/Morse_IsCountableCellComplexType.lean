import Morse
/-! Layer-2 blind definition of Morse_IsCountableCellComplexType. Textbook: Milnor, *Morse Theory*,
§17, Theorem 17.3 and Appendix ("`Ω` has the homotopy type of a countable CW-complex which
contains one cell of dimension `λ` for each …"); Hatcher ch. 4: `X` is homotopy equivalent to a
countable cell complex `K = ⋃ Kₙ` (weak topology) presented in stages, with cells of the given
dimensions attached in the given order.
Choices:
- Stages as in the blind file of Morse_CellTower (`Tower cells`): `K₀` from the EMPTY space by
  attaching `cells 0`, `K_{n+1}` from `Kₙ` by attaching `cells (n+1)`; within a stage the cells
  are attached one at a time in the listed order, each along an arbitrary continuous map
  `S^{d-1} → (space built so far)` (no cellularity imposed); "obtained from" = up to
  homeomorphism compatible with the inclusions. Unlike my Morse_IsFiniteCellComplexType file,
  the order is NOT permuted here, since the notion fixes "a given order".
- `K = ⋃ Kₙ` with the weak topology = Mathlib's colimit in `TopCat` of the sequence
  `K₀ → K₁ → ⋯` (`Functor.ofSequence`); homotopy equivalence = Mathlib's
  `ContinuousMap.HomotopyEquiv`.
- Adjunction spaces built literally (own `Attach`: quotient of `Y ⊔ Dᵈ` by `b ∼ φ b`, Mathlib's
  `TopCat.disk`/`diskBoundary`). -/
namespace RoundTrip.L2.Morse_IsCountableCellComplexType

open CategoryTheory Limits TopCat

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

/-- A countable cell complex presented by finite stages: spaces `K₀ → K₁ → K₂ → ⋯`, `K₀` built
from `∅` by attaching the cells `cells 0`, and `K_{n+1}` built from `Kₙ` (via `ι n`) by attaching
the cells `cells (n+1)`. -/
structure Tower (cells : ℕ → List ℕ) : Type 1 where
  /-- The `n`-th stage `Kₙ`. -/
  K : ℕ → TopCat.{0}
  /-- The inclusion `Kₙ ↪ K_{n+1}` of the subcomplex. -/
  ι : ∀ n, K n ⟶ K (n + 1)
  /-- `K₀` is obtained from `∅` by attaching the cells `cells 0`. -/
  base : IsCellAttach (K 0) (cells 0)
  /-- `K_{n+1}` is obtained from `Kₙ` by attaching the cells `cells (n+1)`. -/
  step : ∀ n, RelAttach (cells (n + 1)) (K n) (K (n + 1)) (ι n)

/-- The union `K = ⋃ Kₙ` with the weak topology: the colimit of the stages. -/
noncomputable def Tower.total {cells : ℕ → List ℕ} (τ : Tower cells) : TopCat.{0} :=
  colimit (Functor.ofSequence τ.ι)

/-- The textbook notion: `X` is homotopy equivalent to the union of some tower with cells
`cells`. -/
def T (X : Type) [TopologicalSpace X] (cells : ℕ → List ℕ) : Prop :=
  ∃ τ : Tower cells, Nonempty (ContinuousMap.HomotopyEquiv X τ.total)

end RoundTrip.L2.Morse_IsCountableCellComplexType
