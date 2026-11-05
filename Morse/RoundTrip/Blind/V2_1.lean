import Morse
/-! Blind formalization of V2_1 (Milnor §3, pp. 12-13: sublevel sets, deformation retract). Choices:
- `M^a = f⁻¹(-∞, a] = {p | f p ≤ a}`: claim that these coincide (set identity).
- "Deformation retract": the family `r_t` with `r_0 = id`, `r_1` a retraction onto `A`, each `r_t` fixing `A` pointwise
  (my `DefRetract`). Claim: if `A ⊆ X` is a deformation retract of the topological space `X`, the inclusion `A → X` is a homotopy
  equivalence (a `HomotopyEquiv` whose underlying map is the inclusion). Stated for arbitrary spaces `X`, so in particular for
  `M^a ⊆ M^b`. -/
open scoped ContDiff Manifold unitInterval
namespace RoundTrip.V2_1

/-- `A` is a deformation retract of `X`: a continuous family `r t : X → X`, `r 0 = id`, `r 1` maps into `A`,
and each `r t` fixes `A` pointwise (as in Milnor's `r_t`). -/
def DefRetract {X : Type} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ r : unitInterval → X → X, Continuous (fun z : unitInterval × X => r z.1 z.2) ∧
    (∀ x, r 0 x = x) ∧ (∀ x, r 1 x ∈ A) ∧ ∀ a ∈ A, ∀ t, r t a = a

/-- Milnor's claim. -/
def B : Prop :=
  (∀ (M : Type) (f : M → ℝ) (a : ℝ), {p | f p ≤ a} = f ⁻¹' Set.Iic a) ∧
  ∀ (X : Type) [TopologicalSpace X] (A : Set X), DefRetract A →
    ∃ h : ContinuousMap.HomotopyEquiv A X, ∀ x, h x = x.1

end RoundTrip.V2_1
