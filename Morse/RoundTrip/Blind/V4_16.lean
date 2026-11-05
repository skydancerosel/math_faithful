import Morse
/-! Blind formalization of V4_16 (Milnor §6, proof of Corollary 6.7: Whitney's embedding theorem). Choices:
- Abstract manifold: `M : Type`, Hausdorff, second countable (standard convention; Milnor's manifolds are second countable, needed for Whitney), smooth (`C^∞`, `IsManifold 𝓘(ℝ,ℝⁿ) ∞`),
  modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, without boundary.
- Item title says "compact" but the text says "an `n`-dimensional manifold"; the general (not nec. compact) statement is formalized (it contains the compact case).
- "Embedded differentiably as a closed subset of `ℝ^{2n+1}`": a `C^∞` map `e : M → ℝ^{2n+1}` that is a smooth embedding (Mathlib `Manifold.IsSmoothEmbedding`: immersion + topological embedding) with closed image
  (`Topology.IsClosedEmbedding e`). -/
namespace RoundTrip.V4_16
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M],
    ∃ e : M → Rn (2 * n + 1), Manifold.IsSmoothEmbedding 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn (2 * n + 1)) ∞ e ∧ Topology.IsClosedEmbedding e
end RoundTrip.V4_16
