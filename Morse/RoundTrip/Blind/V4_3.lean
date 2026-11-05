import Morse
/-! Blind formalization of V4_3 (Milnor §6, Theorem 6.1 (Sard)). Choices:
- Manifolds: smooth (C^∞) Hausdorff, second countable (countable basis), both modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)` (same dimension), `f` of class `C^1` (`ContMDiff 1`).
- Critical point: `mfderiv f p` (Jacobian) is singular, i.e. not bijective (square case). "Measure 0 in `M₂`": for every `y ∈ M₂`, the image under the preferred chart `extChartAt y`
  of (image of critical set) ∩ (chart source) has Lebesgue measure `0` in `ℝⁿ` (Mathlib has no measure on a manifold; this is Milnor's chart-wise definition).
- Manifolds without boundary. -/
namespace RoundTrip.V4_3
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M₁ M₂ : Type) [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁] [ChartedSpace (Rn n) M₁]
    [IsManifold 𝓘(ℝ, Rn n) ∞ M₁] [TopologicalSpace M₂] [T2Space M₂] [SecondCountableTopology M₂]
    [ChartedSpace (Rn n) M₂] [IsManifold 𝓘(ℝ, Rn n) ∞ M₂] (f : M₁ → M₂),
    ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) 1 f →
    ∀ y : M₂, MeasureTheory.volume
      ((extChartAt 𝓘(ℝ, Rn n) y) '' ((f '' {p | ¬ Function.Bijective (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) f p)}) ∩
        (extChartAt 𝓘(ℝ, Rn n) y).source)) = 0
end RoundTrip.V4_3
