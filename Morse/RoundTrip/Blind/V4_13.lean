import Morse
/-! Blind formalization of V4_13 (Milnor §6, Corollary 6.7 (closed submanifold of ℝⁿ)). Choices:
- Following the item title, `M` is a smooth embedded submanifold of `ℝⁿ` (project's `Milnor.IsSliceSubmanifold 𝓘(ℝ,ℝ^{K+1}) ℝ^{d+1} ℝ^m M`, chart structure `hM.chartedSpace`) that is a closed subset of `ℝⁿ`
  (the case to which Milnor's proof reduces by Whitney's theorem). The abstract-manifold version is V4_17.
- B: there is a smooth (`C^∞`) `f : M → ℝ` with no degenerate critical points (every critical point, `Morse.IsCriticalPointM`, is non-degenerate, `Morse.IsNondegenerateCriticalPointM`)
  and all sublevel sets `M^a = {f ≤ a}` compact. -/
namespace RoundTrip.V4_13
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (K d m : ℕ) (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M), IsClosed M →
    letI := hM.chartedSpace
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, Rn (d + 1)) 𝓘(ℝ) ∞ f ∧
      (∀ q, Morse.IsCriticalPointM (Rn (d + 1)) f q → Morse.IsNondegenerateCriticalPointM (Rn (d + 1)) f q) ∧
      ∀ a : ℝ, IsCompact {q : M | f q ≤ a}
end RoundTrip.V4_13
