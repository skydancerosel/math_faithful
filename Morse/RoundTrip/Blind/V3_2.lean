import Morse
/-! Blind formalization of V3_2 (Milnor §4, proof of Thm 4.1: small sublevel sets at extrema are closed cells). Choices:
- Setting: compact smooth Hausdorff manifold `M` modelled on `EuclideanSpace ℝ (Fin n)`, `f` smooth with exactly two critical
  points `p ≠ q`, both non-degenerate (project defs), `f p = 0` the minimum, `f q = 1` the maximum (Milnor's normalisation as
  hypotheses: `f x ∈ [0,1]` for all `x`).
- "closed n-cell" := homeomorphic to the closed unit ball of ℝⁿ (`Metric.closedBall 0 1` in `EuclideanSpace ℝ (Fin n)`).
- Claim: ∃ ε₀ > 0, for all 0 < ε < ε₀ the sets `f⁻¹[0,ε]` and `f⁻¹[1-ε,1]` (subtypes) are closed n-cells. -/
open scoped ContDiff Manifold
namespace RoundTrip.V3_2

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
      Nonempty ({x : M // x ∈ f ⁻¹' Set.Icc 0 ε} ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
      Nonempty ({x : M // x ∈ f ⁻¹' Set.Icc (1 - ε) 1} ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

end RoundTrip.V3_2
