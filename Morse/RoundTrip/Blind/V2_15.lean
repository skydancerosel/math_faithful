import Morse
/-! Blind formalization of V2_15 (Milnor, Remark after Thm 3.5). Choices:
- Setting as Theorem 3.5 (V2_12): smooth Hausdorff finite-dim manifold, `f` smooth with only non-degenerate critical points,
  all `M^a = {f ≤ a}` compact.
- Claim: for EVERY real `a` (regular or critical value), the subtype `M^a` is homotopy equivalent to a finite CW-complex
  (`CWComplex (univ : Set Y)`, finitely many cells in total) with one `λ`-cell for each critical point of index `λ` lying in `M^a`
  (bijection of `l`-cells with `{p | critical ∧ indexM = l ∧ f p ≤ a}`).
- Mathlib CW structure, project defs for critical points/index. -/
open scoped ContDiff Manifold
open Topology
namespace RoundTrip.V2_15

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : M → ℝ), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f →
    (∀ p, Morse.IsCriticalPointM E f p → Morse.IsNondegenerateCriticalPointM E f p) →
    (∀ a : ℝ, IsCompact {x | f x ≤ a}) →
    ∀ a : ℝ, ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (_ : CWComplex (Set.univ : Set Y)),
      Finite (Σ l : ℕ, Topology.CWComplex.cell (Set.univ : Set Y) l) ∧
      Nonempty (ContinuousMap.HomotopyEquiv {x : M | f x ≤ a} Y) ∧
      ∀ l : ℕ, Nonempty (Topology.CWComplex.cell (Set.univ : Set Y) l ≃
        {p : M // Morse.IsCriticalPointM E f p ∧ Morse.indexM E f p = l ∧ f p ≤ a})

end RoundTrip.V2_15
