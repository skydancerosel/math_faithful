import Morse.Chapter4.Existence

/-!
Milnor, *Morse Theory*, §6, pp. 36–37, as used in §5 (p. 29).

# A compact submanifold of `ℝⁿ` carries a Morse function with finitely many critical points

Milnor's §5 (p. 29) starts from a compact manifold `M` and a differentiable function on `M` with
only isolated, non-degenerate critical points; that such functions exist is Theorem 6.6 (or
Corollary 6.7), and that there are then only finitely many critical points is Corollary 2.3 on the
compact manifold `M`.  This file records the combination, for compact slice submanifolds of `ℝⁿ`.

* `Morse.ae_isMorseFunction_normSq_sub_finite_critPoints`: for almost every `p ∈ ℝⁿ`, `L_p` is a
  Morse function on the compact submanifold `M` with finitely many critical points;
* `Morse.exists_isMorseFunction_finite_critPoints`: `M` carries a Morse function with finitely
  many critical points.

The passage from an abstract compact manifold to a submanifold of `ℝⁿ` (Mathlib's Whitney
embedding theorem for compact manifolds, together with the fact that the image of an embedding is
a submanifold, `Morse/Chapter4/WhitneySlice.lean`) is `Morse/Chapter4/Whitney.lean`; there the
combination recorded here gives `Morse.exists_isMorseFunction_of_compactSpace`.
-/

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

namespace Morse

variable {n k w : ℕ} {M : Set (𝔼 n)}
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M)

/-- For almost every `p ∈ ℝⁿ`, `L_p = ‖· − p‖²` is a Morse function on the compact submanifold `M`
with finitely many critical points. -/
theorem ae_isMorseFunction_normSq_sub_finite_critPoints (hc : IsCompact M)
    (μ : Measure (𝔼 n)) [μ.IsAddHaarMeasure] :
    letI := hM.chartedSpace
    ∀ᵐ p ∂μ, IsMorseFunction (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) ∧
      {x : M | IsCriticalPointM (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) x}.Finite := by
  let := hM.chartedSpace
  have := hM.isManifold
  have : CompactSpace M := isCompact_iff_compactSpace.1 hc
  filter_upwards [ae_isMorseFunction_normSq_sub (hM := hM) μ] with p hp
  exact ⟨hp, hp.finite_setOf_isCriticalPointM⟩

/-- **A compact slice submanifold of `ℝⁿ` carries a Morse function with finitely many critical
points** (Theorem 6.6 and Corollary 2.3); one can take `L_p` for almost every `p`. -/
theorem exists_isMorseFunction_finite_critPoints (hc : IsCompact M) :
    letI := hM.chartedSpace
    ∃ f : M → ℝ, IsMorseFunction (𝔼 k) f ∧ {x : M | IsCriticalPointM (𝔼 k) f x}.Finite := by
  let := hM.chartedSpace
  obtain ⟨p, hp⟩ := (ae_isMorseFunction_normSq_sub_finite_critPoints hM hc volume).exists
  exact ⟨_, hp⟩

end Morse
