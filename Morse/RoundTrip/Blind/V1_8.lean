import Morse
/-! Blind formalization of V1_8 (Milnor Lemma 2.2, Morse). Choices:
- Setting: smooth Hausdorff manifold `M` modelled on `EuclideanSpace ℝ (Fin n)` (dimension n), `f` smooth, `p` a non-degenerate
  critical point (project defs `Morse.IsCriticalPointM`/`IsNondegenerateCriticalPointM`); index `λ = Morse.indexM`.
- "local coordinates (y¹..yⁿ) on U, vanishing at p": Mathlib `PartialDiffeomorph` `y` from `M` onto an open subset of
  `EuclideanSpace ℝ (Fin n)` with `p ∈ y.source`, `y p = 0`; `U = y.source` (open nbhd of p).
- Conclusion: `f q = f p - Σ_{i<λ} (y q i)² + Σ_{i≥λ} (y q i)²` for all `q ∈ U`.
- Proof sketch not asserted. -/
open scoped ContDiff Manifold
namespace RoundTrip.V1_8

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] (f : M → ℝ) (p : M),
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ f →
    Morse.IsNondegenerateCriticalPointM (EuclideanSpace ℝ (Fin n)) f p →
    ∃ y : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M
        (EuclideanSpace ℝ (Fin n)) ∞,
      p ∈ y.source ∧ y p = 0 ∧
      ∀ q ∈ y.source, f q = f p
        - ∑ i : Fin n with i.val < Morse.indexM (EuclideanSpace ℝ (Fin n)) f p, (y q i) ^ 2
        + ∑ i : Fin n with Morse.indexM (EuclideanSpace ℝ (Fin n)) f p ≤ i.val, (y q i) ^ 2

end RoundTrip.V1_8
