import Morse
/-! Blind formalization of V2_11 (Milnor §3, Thm 3.5 proof, p. 23: attaching cells to a CW-complex). Choices:
- CW-complex = Mathlib's `CWComplex (Set.univ : Set X)` (classical CW complex structure on the whole space `X`; `X : Type`).
- Claim (cellular approximation step): for a CW-complex `X` and an attaching map `φ : S^{λ-1} → X`, there is a map
  `ψ` homotopic to `φ` with image in the `(λ-1)`-skeleton (`skeletonLT univ λ`: cells of dimension `< λ`), such that the adjunction
  space `X ∪_ψ e^λ` (own `Attach`) is again a CW-complex (`Nonempty (CWComplex univ)`).
- `T2Space X` is assumed (needed by Mathlib for skeleta; CW-complexes are Hausdorff).
- "Iterated adjunction spaces" is the induction (one cell at a time); one step is what is asserted. -/
open Topology
namespace RoundTrip.V2_11

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
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)] (l : ℕ) (φ : C(Bdry l, X)),
    ∃ ψ : C(Bdry l, X), φ.Homotopic ψ ∧
      Set.range ψ ⊆ ((RelCWComplex.skeletonLT (Set.univ : Set X) (l : ℕ∞) : RelCWComplex.Subcomplex (Set.univ : Set X)) : Set X) ∧
      Nonempty (CWComplex (Set.univ : Set (Attach ψ)))

end RoundTrip.V2_11
