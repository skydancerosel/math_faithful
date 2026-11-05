import Morse
/-! Blind formalization of V3_6 (Milnor Theorem 4.1, Reeb). Choices:
- Setting: compact smooth (C^∞) Hausdorff manifold `M` modelled on `EuclideanSpace ℝ (Fin n)`; "differentiable" = C^∞;
  `f` has exactly two critical points `p ≠ q`, both non-degenerate (project defs).
- Conclusion: `M` homeomorphic to the unit sphere `Sⁿ ⊂ ℝ^{n+1}` (`Metric.sphere 0 1` in `EuclideanSpace ℝ (Fin (n+1))`).
- Not included (context note only): Remark 1 (degenerate case) and Remark 2 (M need not be diffeomorphic to Sⁿ). The proof
  is not asserted. -/
open scoped ContDiff Manifold
namespace RoundTrip.V3_6

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    (f : M → ℝ) (p q : M),
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ f → p ≠ q →
    Morse.IsNondegenerateCriticalPointM (EuclideanSpace ℝ (Fin n)) f p →
    Morse.IsNondegenerateCriticalPointM (EuclideanSpace ℝ (Fin n)) f q →
    (∀ x, Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin n)) f x → x = p ∨ x = q) →
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

end RoundTrip.V3_6
