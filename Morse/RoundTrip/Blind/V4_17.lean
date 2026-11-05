import Morse
/-! Blind formalization of V4_17 (Milnor §6, Corollary 6.7 (compact manifold)). Choices:
- Abstract manifold: `M : Type`, Hausdorff, second countable (standard convention; Milnor's manifolds are second countable, needed for Whitney), smooth (`C^∞`, `IsManifold 𝓘(ℝ,ℝⁿ) ∞`),
  modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, without boundary.
- Following the item title, `M` is also compact (`CompactSpace M`), so the sublevel-set compactness is automatic but is still stated, as in Milnor's corollary (which is for every manifold; see V4_13 for the closed-submanifold case).
- B: there is a smooth `f : M → ℝ` with no degenerate critical points (every critical point is non-degenerate) all of whose sublevel sets `M^a = {f ≤ a}` are compact. -/
namespace RoundTrip.V4_17
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M] [CompactSpace M],
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ f ∧
      (∀ q, Morse.IsCriticalPointM (Rn n) f q → Morse.IsNondegenerateCriticalPointM (Rn n) f q) ∧
      ∀ a : ℝ, IsCompact {q : M | f q ≤ a}
end RoundTrip.V4_17
