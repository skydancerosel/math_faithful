import Morse
/-! Blind formalization of V3_3 (Milnor §4, proof of Thm 4.1). Choices:
- Setting: compact smooth Hausdorff manifold `M` (finite-dim), `f : M → ℝ` smooth with exactly two critical points
  `p ≠ q`, both non-degenerate (project defs `Morse.IsCriticalPointM`, `Morse.IsNondegenerateCriticalPointM`).
- Claim: one of them is the global minimum point and the other the global maximum point.
- The normalization f(min)=0, f(max)=1 (an affine rescaling) is not expressed: it needs f min ≠ f max, which fails for
  0-dimensional M, and Milnor leaves it implicit. -/

open scoped ContDiff Manifold
namespace RoundTrip.V3_3

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (f : M → ℝ) (p q : M),
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f → p ≠ q →
    Morse.IsNondegenerateCriticalPointM E f p → Morse.IsNondegenerateCriticalPointM E f q →
    (∀ x, Morse.IsCriticalPointM E f x → x = p ∨ x = q) →
    ∃ a b : M, (a = p ∧ b = q ∨ a = q ∧ b = p) ∧ (∀ x, f a ≤ f x ∧ f x ≤ f b)

end RoundTrip.V3_3
