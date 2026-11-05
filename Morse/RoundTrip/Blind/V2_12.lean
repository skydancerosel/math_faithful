import Morse
/-! Blind formalization of V2_12 (Milnor Theorem 3.5). Choices:
- Setting (per the stated theorem, abstract manifold; submanifold of ℝⁿ is a special case): smooth Hausdorff finite-dim manifold
  `M`, `f` smooth (C^∞) with no degenerate critical points (every critical point satisfies project's
  `Morse.IsNondegenerateCriticalPointM`), and every `M^a = {f ≤ a}` compact.
- CW-complex := Mathlib `CWComplex (Set.univ : Set Y)` on a Hausdorff space `Y : Type`; "homotopy equivalent" := `ContinuousMap.HomotopyEquiv M Y`.
- "one cell of dimension λ for each critical point of index λ": for each `l`, a bijection between the `l`-cells (`CWComplex.cell univ l`)
  and `{p | critical ∧ indexM = l}`.
- Proof sketch (listing critical values, Lemmas 3.6/3.7, direct limit) not asserted. -/
open scoped ContDiff Manifold
open Topology
namespace RoundTrip.V2_12

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : M → ℝ), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f →
    (∀ p, Morse.IsCriticalPointM E f p → Morse.IsNondegenerateCriticalPointM E f p) →
    (∀ a : ℝ, IsCompact {x | f x ≤ a}) →
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (_ : CWComplex (Set.univ : Set Y)),
      Nonempty (ContinuousMap.HomotopyEquiv M Y) ∧
      ∀ l : ℕ, Nonempty (Topology.CWComplex.cell (Set.univ : Set Y) l ≃
        {p : M // Morse.IsCriticalPointM E f p ∧ Morse.indexM E f p = l})

end RoundTrip.V2_12
