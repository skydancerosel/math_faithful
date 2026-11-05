import Morse
/-! Blind formalization of V1_10 (Milnor Corollary 2.3). Choices:
- Setting: abstract smooth (C^∞) finite-dimensional real manifold `M` modelled on a normed space `E`
  (`ChartedSpace E M`, `IsManifold 𝓘(ℝ,E) ∞ M`), Hausdorff; `f : M → ℝ` smooth (`ContMDiff`).
- Non-degenerate critical point: project definition `Morse.IsNondegenerateCriticalPointM` (Hessian in a chart); critical:
  `Morse.IsCriticalPointM`.
- "isolated": ∃ neighbourhood `U` of `p` containing no other critical point of `f`. -/
open scoped ContDiff Manifold Topology
namespace RoundTrip.V1_10

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : M → ℝ) (p : M), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f →
    Morse.IsNondegenerateCriticalPointM E f p →
    ∃ U ∈ 𝓝 p, ∀ q ∈ U, Morse.IsCriticalPointM E f q → q = p

end RoundTrip.V1_10
