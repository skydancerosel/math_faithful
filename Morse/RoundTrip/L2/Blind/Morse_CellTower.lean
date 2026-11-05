import Morse
/-! Layer-2 blind definition of Morse_CellTower. Textbook: Milnor, *Morse Theory*, Appendix and
Theorem 17.3; J.H.C. Whitehead; Hatcher, *Algebraic Topology*, Appendix (a countable CW complex
presented by finite stages `K₀ ⊆ K₁ ⊆ ⋯`, `K₀` obtained by attaching finitely many cells, `K_{n+1}`
obtained from `Kₙ` by attaching finitely many cells along continuous attaching maps).
Choices:
- `T cells` is the type of such presentations: the stages `Kₙ : TopCat` and inclusions
  `ι n : Kₙ ⟶ K_{n+1}` are data; the cell attachments are Prop-valued witnesses (existence of
  attaching maps), the attaching maps themselves are not stored. The complex itself, `⋃ Kₙ` with
  the weak topology, is the colimit of the stages (determined by the data, not stored).
- `K₀` is built from the EMPTY space (a base point, if wanted, is a 0-cell listed in `cells 0`).
- Within a stage, the cells of `cells n` are attached one at a time in the listed order (head
  first), each along an arbitrary continuous map `S^{d-1} → (space built so far)` (so a cell may
  meet earlier cells of the same stage); "obtained from" = up to homeomorphism compatible with
  `ι n` (`RelAttach`, as in the blind file of Morse_IsRelCellAttachment). Genuine CW conditions
  (cellular attaching maps) are not imposed, as in Milnor's §3 cell complexes.
- Adjunction spaces built literally (own `Attach`: quotient of `Y ⊔ Dᵈ` by `b ∼ φ b`, Mathlib's
  `TopCat.disk`/`diskBoundary`); `∅ = TopCat.of Empty`. -/
namespace RoundTrip.L2.Morse_CellTower

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

/-- The textbook notion: presentations of a countable cell complex by finite stages. -/
def T (cells : ℕ → List ℕ) : Type 1 :=
  Tower cells

end RoundTrip.L2.Morse_CellTower
