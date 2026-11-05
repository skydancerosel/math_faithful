import Morse
/-! Blind formalization of V2_13 (Milnor Lemma 3.6, Whitehead). Choices:
- Cells/attaching spaces as in V1_2 (own `Attach` quotient; ė^λ = unit sphere in ℝ^λ).
- "homotopic" = `ContinuousMap.Homotopic` (free homotopy), `X` any topological space in `Type`.
- "identity of X extends to a homotopy equivalence k": ∃ `ContinuousMap.HomotopyEquiv` h with h ∘ inl₀ = inl₁.
- The explicit formulas for k, ℓ and the claims kℓ ≃ id ≃ ℓk are not expressed separately (only existence of
  the homotopy equivalence extending id_X; the inverse ℓ is the HomotopyEquiv's inverse, unspecified). -/
open Topology

namespace RoundTrip.V2_13

/-- The closed unit ball `e^k` in ℝ^k. -/
abbrev Cell (k : ℕ) : Type := Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1
/-- Its boundary sphere `ė^k = S^{k-1}`. -/
abbrev Bdry (k : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1
/-- The inclusion of the boundary sphere into the cell. -/
def bdryToCell {k : ℕ} (x : Bdry k) : Cell k := ⟨x.1, Metric.sphere_subset_closedBall x.2⟩

variable {Y : Type} [TopologicalSpace Y]

/-- Identification relation on the topological sum: `x ∈ S^{k-1}` is glued to `g x`. -/
def Rel {k : ℕ} (g : C(Bdry k, Y)) : (Y ⊕ Cell k) → (Y ⊕ Cell k) → Prop :=
  fun a b => ∃ x : Bdry k, a = Sum.inr (bdryToCell x) ∧ b = Sum.inl (g x)

/-- `Y ∪_g e^k`: quotient of the topological sum `Y ⊕ e^k` by the identifications. -/
def Attach {k : ℕ} (g : C(Bdry k, Y)) : Type := Quot (Rel g)

instance {k : ℕ} (g : C(Bdry k, Y)) : TopologicalSpace (Attach g) :=
  inferInstanceAs (TopologicalSpace (Quot (Rel g)))

/-- Inclusion of `Y`. -/
def inl {k : ℕ} (g : C(Bdry k, Y)) : C(Y, Attach g) :=
  ⟨fun y => Quot.mk _ (Sum.inl y), continuous_quot_mk.comp continuous_inl⟩

/-- Characteristic map of the cell. -/
def inr {k : ℕ} (g : C(Bdry k, Y)) : C(Cell k, Attach g) :=
  ⟨fun c => Quot.mk _ (Sum.inr c), continuous_quot_mk.comp continuous_inr⟩

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (lam : ℕ) (φ₀ φ₁ : C(Bdry lam, X)),
    φ₀.Homotopic φ₁ →
      ∃ h : ContinuousMap.HomotopyEquiv (Attach φ₀) (Attach φ₁),
        ∀ x : X, h (inl φ₀ x) = inl φ₁ x

end RoundTrip.V2_13
