import Morse
/-! Blind formalization of V4_12 (Milnor §6, Theorem 6.6). Choices:
- `M ⊆ ℝⁿ` a smooth embedded submanifold (project's `Milnor.IsSliceSubmanifold 𝓘(ℝ,ℝ^{K+1}) ℝ^{d+1} ℝ^m M`, any `d, m`; chart structure `hM.chartedSpace`), no boundary.
- "Outside a set of measure 0": `∀ᵐ p ∂volume` on `ℝⁿ = EuclideanSpace ℝ (Fin (K+1))`.
- `L_p(y) = ‖y - p‖²` restricted to `M`; "no degenerate critical point": every critical point (`Morse.IsCriticalPointM`) is non-degenerate (`Morse.IsNondegenerateCriticalPointM`).
- The derivation from Lemma 6.5 and Corollary 6.2 is not part of B. -/
namespace RoundTrip.V4_12
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- `L_p(y) = ‖y - p‖²`. -/
noncomputable def Lp {n : ℕ} (p : Rn n) (y : Rn n) : ℝ := ‖y - p‖ ^ 2

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (K d m : ℕ) (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M),
    letI := hM.chartedSpace
    ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure (Rn (K + 1))),
      ∀ q : M, Morse.IsCriticalPointM (Rn (d + 1)) (fun y : M => Lp p y.1) q →
        Morse.IsNondegenerateCriticalPointM (Rn (d + 1)) (fun y : M => Lp p y.1) q
end RoundTrip.V4_12
