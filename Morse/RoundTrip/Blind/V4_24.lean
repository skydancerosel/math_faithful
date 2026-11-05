import Morse
/-! Blind formalization of V4_24 (Milnor §4, Theorem 4.1 (Reeb)). Choices:
- Abstract manifold `M : Type`, compact Hausdorff (`CompactSpace`, `T2Space`), smooth (`C^∞`), modelled on `ℝⁿ`, without boundary; `f : M → ℝ` smooth ("differentiable").
- "Only two critical points": the set of critical points (`Morse.IsCriticalPointM`) has exactly 2 elements (`Set.ncard = 2`; finite since `ncard` of an infinite set is 0); both non-degenerate (`Morse.IsNondegenerateCriticalPointM`).
- "Homeomorphic to a sphere": homeomorphic to the unit sphere `Metric.sphere (0 : ℝ^{n+1}) 1` (`n = dim M`). -/
namespace RoundTrip.V4_24
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
    (f : M → ℝ), ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ f →
    {p : M | Morse.IsCriticalPointM (Rn n) f p}.ncard = 2 →
    (∀ p, Morse.IsCriticalPointM (Rn n) f p → Morse.IsNondegenerateCriticalPointM (Rn n) f p) →
    Nonempty (M ≃ₜ Metric.sphere (0 : Rn (n + 1)) 1)
end RoundTrip.V4_24
