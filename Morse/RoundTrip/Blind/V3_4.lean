import Morse
/-! Blind formalization of V3_4 (Milnor §4, proof of Thm 4.1: M is two closed cells matched along the boundary). Choices:
- Setting and normalisation as in V3_2 (compact manifold on `EuclideanSpace ℝ (Fin n)`, two non-degenerate critical points,
  min `f p = 0`, max `f q = 1`).
- Claim (for small ε): (1) `M^ε` is homeomorphic to `M^{1-ε}` (Theorem 3.1); (2) `M = M^{1-ε} ∪ f⁻¹[1-ε,1]` where both pieces
  are closed n-cells (homeomorphic to the unit ball `h₁, h₂`) and the common boundary is the level `f = 1-ε`: a point of the piece
  lies on the unit sphere under its homeomorphism iff it lies in the other piece.
- "matched along their common boundary": the two pieces intersect exactly in the boundary spheres, which is the identification. -/
open scoped ContDiff Manifold
namespace RoundTrip.V3_4

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    (f : M → ℝ) (p q : M),
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ f → p ≠ q →
    Morse.IsNondegenerateCriticalPointM (EuclideanSpace ℝ (Fin n)) f p →
    Morse.IsNondegenerateCriticalPointM (EuclideanSpace ℝ (Fin n)) f q →
    (∀ x, Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin n)) f x → x = p ∨ x = q) →
    f p = 0 → f q = 1 → (∀ x, f p ≤ f x ∧ f x ≤ f q) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Nonempty ({x : M // f x ≤ ε} ≃ₜ {x : M // f x ≤ 1 - ε}) ∧
      (∀ x : M, f x ≤ 1 - ε ∨ 1 - ε ≤ f x) ∧
      ∃ (h₁ : {x : M // f x ≤ 1 - ε} ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
        (h₂ : {x : M // 1 - ε ≤ f x} ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
        (∀ x, ‖(h₁ x).1‖ = 1 ↔ f x.1 = 1 - ε) ∧ (∀ x, ‖(h₂ x).1‖ = 1 ↔ f x.1 = 1 - ε)

end RoundTrip.V3_4
