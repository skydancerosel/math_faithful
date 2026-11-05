import Morse
/-! Blind formalization of V4_21 (Milnor §6, Corollary 6.8 (submanifold of ℝⁿ)). Choices:
- `M ⊆ ℝⁿ` a smooth embedded submanifold (project's `Milnor.IsSliceSubmanifold 𝓘(ℝ,ℝ^{K+1}) ℝ^{d+1} ℝ^m M`, chart structure `hM.chartedSpace`), not assumed closed (the statement is intrinsic to `M`).
- Manifold `M` smooth (`C^∞`), Hausdorff, second countable, modelled on `ℝⁿ`; `f : M → ℝ` smooth and bounded (`∃ C, ∀ x, |f x| ≤ C`).
- "Uniform limit of smooth functions without degenerate critical points": for every `ε > 0` there is a smooth `g` with every critical point non-degenerate (`Morse.IsCriticalPointM`,
  `Morse.IsNondegenerateCriticalPointM`) and `|g x - f x| < ε` for all `x`.
- "On a given compact set `K`, derivatives of every order `i ≤ k` uniformly close": a manifold has no global derivatives, so closeness is measured in charts. A compact set `K` is given as a finite
  family of compact pieces `C_j ⊆ source of φ_j`, where `φ_j` is a chart of the maximal smooth atlas (every compact set is a finite union of such pieces); the condition is
  `‖D^i (g ∘ φ_j⁻¹)(y) - D^i (f ∘ φ_j⁻¹)(y)‖ < ε` (Mathlib `iteratedFDeriv`) for all `i ≤ k`, `y ∈ φ_j '' C_j`, all `j`. -/
namespace RoundTrip.V4_21
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The conclusion of Corollary 6.8 for a smooth bounded `f` on a manifold `M` modelled on `ℝⁿ`. -/
def ApproxStmt (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Rn n) M] (f : M → ℝ) : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (k : ℕ) (r : ℕ) (φ : Fin r → OpenPartialHomeomorph M (Rn n))
    (_ : ∀ j, φ j ∈ IsManifold.maximalAtlas 𝓘(ℝ, Rn n) ∞ M) (C : Fin r → Set M),
    (∀ j, IsCompact (C j) ∧ C j ⊆ (φ j).source) →
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ g ∧
      (∀ q, Morse.IsCriticalPointM (Rn n) g q → Morse.IsNondegenerateCriticalPointM (Rn n) g q) ∧
      (∀ x, |g x - f x| < ε) ∧
      ∀ j, ∀ i ≤ k, ∀ y ∈ (φ j) '' (C j),
        ‖iteratedFDeriv ℝ i (g ∘ (φ j).symm) y - iteratedFDeriv ℝ i (f ∘ (φ j).symm) y‖ < ε

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (K d m : ℕ) (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M),
    letI := hM.chartedSpace
    ∀ f : M → ℝ, ContMDiff 𝓘(ℝ, Rn (d + 1)) 𝓘(ℝ) ∞ f → (∃ C, ∀ x, |f x| ≤ C) → ApproxStmt (d + 1) M f
end RoundTrip.V4_21
