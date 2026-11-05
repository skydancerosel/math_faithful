import Morse.Chapter4.Focal
import Morse.Chapter1.ManifoldMorse

/-!
Milnor, *Morse Theory*, §6, p. 36.

# Every closed submanifold of `ℝⁿ` carries a Morse function with compact sublevel sets
(Corollary 6.7)

Milnor, p. 36, paraphrased: **Corollary 6.7.** *On any manifold `M` there is a differentiable
function with no degenerate critical points for which each `M^a` is compact.*  Proof: Theorem 6.6
and the fact that an `n`-dimensional manifold can be embedded differentiably as a closed subset of
`ℝ²ⁿ⁺¹` (Whitney, *Geometric Integration Theory*, p. 113).

## What is proved here

For `M` a slice submanifold of `ℝⁿ` (`Milnor.IsSliceSubmanifold 𝓘(ℝ, ℝⁿ) ℝᵏ ℝʷ M`) which is a
**closed subset** of `ℝⁿ`:

* `Morse.isCompact_sublevel_normSq_sub`: for every `p ∈ ℝⁿ` and `a ∈ ℝ`, the sublevel set
  `M^a = {q ∈ M | ‖q − p‖² ≤ a}` of `L_p` is compact (it is `M ∩ B̄(p, √a)`, closed and bounded in
  `ℝⁿ`, and `M → ℝⁿ` is a closed embedding);
* `Morse.ae_isMorseFunction_normSq_sub_and_isCompact_sublevel`: for almost every `p`, `L_p` is a
  Morse function on `M` with compact sublevel sets;
* `Morse.exists_isMorseFunction_isCompact_sublevel` (**Corollary 6.7**): `M` carries a Morse
  function `f` with every `M^a = f⁻¹(−∞, a]` compact;
* `Morse.exists_isMorseFunction_finite_critPoints_sublevel`: moreover each `M^a` contains only
  finitely many critical points of `f` (Corollary 2.3 on the compact set `M^a`,
  `Morse.IsMorseFunction.finite_inter_setOf_isCriticalPointM`); this is the form used in §3
  (Theorem 3.5) and §5.

## Gaps in Milnor's text, and what is not done

* **The embedding theorem is available only for compact manifolds.**  Mathlib (v4.33.1) proves
  Whitney's embedding theorem for compact manifolds, and `Morse/Chapter4/WhitneySlice.lean` shows
  that the image of an embedding is a slice submanifold; with them `Morse/Chapter4/Whitney.lean`
  proves the corollary for every abstract compact Hausdorff manifold
  (`Morse.exists_isMorseFunction_of_compactSpace`).  Mathlib has no closed embedding of an
  arbitrary second countable Hausdorff manifold into a Euclidean space, so for non-compact
  manifolds the corollary is proved here for closed slice submanifolds of `ℝⁿ`; "any manifold" in
  Milnor's statement must in any case be read as Hausdorff with a countable basis (on the long
  line every continuous real function is eventually constant, so some sublevel set is not
  compact).
* **Closedness of the embedding is essential**, and Milnor's appeal to Whitney's theorem uses that
  the image is closed: for the open unit interval in `ℝ`, `L_p` has non-compact sublevel sets for
  every `p` (e.g. `L_0^{1}` is the whole interval).
-/

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

namespace Morse

variable {n k w : ℕ} {M : Set (𝔼 n)}
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M)

/-- The sublevel sets `{y | ‖y − p‖² ≤ a}` of `L_p` on `ℝⁿ` are compact. -/
theorem isCompact_setOf_normSq_sub_le (p : 𝔼 n) (a : ℝ) :
    IsCompact {y : 𝔼 n | ‖y - p‖ ^ 2 ≤ a} := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le (by fun_prop) continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := p) (r := max 1 a)).subset fun y hy => ?_
  rw [Metric.mem_closedBall, dist_eq_norm]
  rcases le_or_gt ‖y - p‖ 1 with h | h
  · exact h.trans (le_max_left _ _)
  · have hy' : ‖y - p‖ ^ 2 ≤ a := hy
    nlinarith [le_max_right 1 a]

/-- **The sublevel sets of `L_p` on a closed submanifold are compact** (Milnor, proof of
Corollary 6.7). -/
theorem isCompact_sublevel_normSq_sub (hclosed : IsClosed M) (p : 𝔼 n) (a : ℝ) :
    IsCompact {x : M | ‖(x : 𝔼 n) - p‖ ^ 2 ≤ a} :=
  hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_setOf_normSq_sub_le p a)

/-- For almost every `p ∈ ℝⁿ`, `L_p` is a Morse function on the closed submanifold `M` with compact
sublevel sets. -/
theorem ae_isMorseFunction_normSq_sub_and_isCompact_sublevel (hclosed : IsClosed M)
    (μ : Measure (𝔼 n)) [μ.IsAddHaarMeasure] :
    letI := hM.chartedSpace
    ∀ᵐ p ∂μ, IsMorseFunction (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) ∧
      ∀ a : ℝ, IsCompact ((fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) ⁻¹' Iic a) := by
  let := hM.chartedSpace
  filter_upwards [ae_isMorseFunction_normSq_sub (hM := hM) μ] with p hp
  exact ⟨hp, fun a => isCompact_sublevel_normSq_sub hclosed p a⟩

/-- **Corollary 6.7** (Milnor, p. 36), for a closed slice submanifold `M` of `ℝⁿ`: *there is a
smooth function on `M` with no degenerate critical points for which each `M^a = f⁻¹(−∞, a]` is
compact*; one can take `f = L_p` for almost every `p`. -/
theorem exists_isMorseFunction_isCompact_sublevel (hclosed : IsClosed M) :
    letI := hM.chartedSpace
    ∃ f : M → ℝ, IsMorseFunction (𝔼 k) f ∧ ∀ a : ℝ, IsCompact (f ⁻¹' Iic a) := by
  let := hM.chartedSpace
  obtain ⟨p, hp⟩ := exists_isMorseFunction_normSq_sub (hM := hM)
  exact ⟨_, hp, fun a => isCompact_sublevel_normSq_sub hclosed p a⟩

/-- **Corollary 6.7 with finitely many critical points in each `M^a`**: on a closed slice
submanifold of `ℝⁿ` there is a Morse function whose sublevel sets `M^a` are compact and contain only
finitely many critical points each. -/
theorem exists_isMorseFunction_finite_critPoints_sublevel (hclosed : IsClosed M) :
    letI := hM.chartedSpace
    ∃ f : M → ℝ, IsMorseFunction (𝔼 k) f ∧ ∀ a : ℝ, IsCompact (f ⁻¹' Iic a) ∧
      (f ⁻¹' Iic a ∩ {x | IsCriticalPointM (𝔼 k) f x}).Finite := by
  let := hM.chartedSpace
  have := hM.isManifold
  obtain ⟨f, hf, hc⟩ := exists_isMorseFunction_isCompact_sublevel hM hclosed
  exact ⟨f, hf, fun a => ⟨hc a, hf.finite_inter_setOf_isCriticalPointM (hc a)⟩⟩

end Morse
