import Morse
/-! Blind formalization of V1_2 (Milnor §1, pp. 2–3, attaching a cell). Choices:
- `e^k` = closed unit ball of `EuclideanSpace ℝ (Fin k)`, `ė^k` = unit sphere there (empty for k=0).
- `Y ∪_g e^k` = `Quot` of the topological sum `Y ⊕ e^k` by the relation `inr x ~ inl (g x)` (Quot gets the
  quotient topology); the Prop claims: (a) identification `inr x = inl (g x)`; (b) the sphere for k=0 is
  empty and `e^0` is a point; (c) for k=0, `Y ∪_g e^0 ≃ₜ Y ⊕ Unit` (disjoint point added).
- Spaces in `Type` (universe 0). Milnor's definition itself is the `Attach` def; the Prop records its stated consequences. -/
open Topology

namespace RoundTrip.V1_2

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
  (∀ (Y : Type) [TopologicalSpace Y] (k : ℕ) (g : C(Bdry k, Y)) (x : Bdry k),
      inr g (bdryToCell x) = inl g (g x)) ∧
  IsEmpty (Bdry 0) ∧ Nonempty (Cell 0) ∧ Subsingleton (Cell 0) ∧
  (∀ (Y : Type) [TopologicalSpace Y] (g : C(Bdry 0, Y)), Nonempty (Attach g ≃ₜ (Y ⊕ Unit)))

end RoundTrip.V1_2
