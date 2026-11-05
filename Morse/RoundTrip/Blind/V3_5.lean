import Morse
/-! Blind formalization of V3_5 (Milnor §4, proof of Thm 4.1: two n-cells matched along their boundary give a sphere). Choices:
- Topological statement: `X` any topological space, `A, B ⊆ X` closed with `A ∪ B = X`, `h₁ : A ≃ₜ e^n`, `h₂ : B ≃ₜ e^n`
  (`e^n` = closed unit ball of ℝⁿ), and the common boundary condition: for `x ∈ A`, `x ∈ B ↔ ‖h₁ x‖ = 1`, similarly for `B`
  (so `A ∩ B` is the boundary sphere of each). Conclusion: `X ≃ₜ Sⁿ` (unit sphere in `EuclideanSpace ℝ (Fin (n+1))`).
- Milnor's phrase "matched along their common boundary" is read as: `A ∩ B = ∂A = ∂B` in `X` (gluing by identity in `X`).
- The homeomorphism is not constructed (Milnor does not). -/
namespace RoundTrip.V3_5

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (X : Type) [TopologicalSpace X] (A C : Set X), IsClosed A → IsClosed C → A ∪ C = Set.univ →
    ∀ (h₁ : A ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
      (h₂ : C ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
      (∀ x : A, x.1 ∈ C ↔ ‖(h₁ x).1‖ = 1) → (∀ x : C, x.1 ∈ A ↔ ‖(h₂ x).1‖ = 1) →
      Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

end RoundTrip.V3_5
