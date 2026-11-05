import Morse
/-! Blind formalization of V1_9 (Milnor §2, proof of Lemma 2.2: the index is forced by the normal form). Choices:
- Setting as in V1_8 (manifold modelled on `EuclideanSpace ℝ (Fin n)`, smooth `f`).
- Hypothesis: a coordinate system `z` (Mathlib `PartialDiffeomorph`) around `p` (`p ∈ z.source`, `z p = 0` -- coordinates
  vanish at p, as in the lemma) with `f = f p - Σ_{i<λ} z_i² + Σ_{i≥λ} z_i²` on `z.source`, `λ ≤ n`.
- Conclusion: `λ = Morse.indexM f p` (the Hessian matrix computation and the dimension count of negative definite
  subspaces are the proof, not asserted; in addition I assert `p` is a non-degenerate critical point, which Milnor uses).
-/
open scoped ContDiff Manifold
namespace RoundTrip.V1_9

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] (f : M → ℝ) (p : M) (l : ℕ),
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ f → l ≤ n →
    ∀ z : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M
        (EuclideanSpace ℝ (Fin n)) ∞,
      p ∈ z.source → z p = 0 →
      (∀ q ∈ z.source, f q = f p - ∑ i : Fin n with i.val < l, (z q i) ^ 2
        + ∑ i : Fin n with l ≤ i.val, (z q i) ^ 2) →
      Morse.IsNondegenerateCriticalPointM (EuclideanSpace ℝ (Fin n)) f p ∧
        l = Morse.indexM (EuclideanSpace ℝ (Fin n)) f p

end RoundTrip.V1_9
