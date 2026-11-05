import Milnor.Chapter3.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §3, Step 3 (p. 19).

# Step 3: `f(Cₖ)` has measure zero for `k` large

Milnor's argument: by Taylor's theorem, for `x ∈ Cₖ` and `x + h` in a cube `Iⁿ ⊆ U`,
`‖f(x+h) - f(x)‖ ≤ c ‖h‖^{k+1}`. Subdividing `Iⁿ` into `rⁿ` cubes of edge `δ/r`, the image of
`Cₖ ∩ Iⁿ` is covered by `rⁿ` cubes of edge `a / r^{k+1}`, of total volume `aᵖ rⁿ⁻⁽ᵏ⁺¹⁾ᵖ → 0`
when `(k+1)p > n`.

We follow a slightly different route to the same estimate. The Taylor bound says exactly that
`f` restricted to `Cₖ ∩ K` (`K` a compact convex set in `U`) is Hölder continuous with exponent
`k + 1`. A Hölder map with exponent `α` cannot raise Hausdorff dimension by more than a factor
`1/α` (Mathlib's `HolderOnWith.dimH_image_le`), so `f(Cₖ ∩ K)` has Hausdorff dimension at most
`n/(k+1) < p` and therefore measure zero. Milnor's cube count is precisely the standard proof of
that Hausdorff-dimension estimate, so nothing is lost; we simply reuse it from the library.

The Taylor bound itself (`norm_sub_le_of_iteratedFDeriv_eq_zero`) is proved by induction on `k`
using only the mean value inequality on segments: if `‖dfₓ‖ ≤ c ‖z - x‖ᵏ` along the segment from
`x` to `y`, then `‖f y - f x‖ ≤ c ‖y - x‖^{k+1}`.
-/

open Set Filter Topology Function MeasureTheory Module
open scoped ContDiff NNReal ENNReal

noncomputable section

namespace Milnor

namespace Sard

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On a segment from `x` to `y`, every point `z` satisfies `‖z - x‖ ≤ ‖y - x‖`. -/
theorem norm_sub_le_of_mem_segment {x y z : E} (hz : z ∈ segment ℝ x y) : ‖z - x‖ ≤ ‖y - x‖ := by
  rw [segment_eq_image'] at hz
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hz
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
  exact mul_le_of_le_one_left (norm_nonneg _) h1

/-- **Taylor-type bound.** Let `f` be smooth on an open set `U`, let `K ⊆ U` be convex, and
suppose `‖D^{k+1} f‖ ≤ c` on `K`. If all derivatives of `f` of order `1, …, k` vanish at `x ∈ K`,
then `‖f y - f x‖ ≤ c ‖y - x‖^{k+1}` for all `y ∈ K`. -/
theorem norm_sub_le_of_iteratedFDeriv_eq_zero (k : ℕ) :
    ∀ {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → G} {U K : Set E},
      IsOpen U → K ⊆ U → Convex ℝ K → ContDiffOn ℝ ∞ f U →
      ∀ {c : ℝ}, (∀ z ∈ K, ‖iteratedFDeriv ℝ (k + 1) f z‖ ≤ c) →
      ∀ {x : E}, x ∈ K → (∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j f x = 0) →
      ∀ y ∈ K, ‖f y - f x‖ ≤ c * ‖y - x‖ ^ (k + 1) := by
  induction k with
  | zero =>
    intro G _ _ f U K hU hKU hK hf c hc x hx _ y hy
    have hseg : segment ℝ x y ⊆ K := hK.segment_subset hx hy
    have hderiv : ∀ z ∈ segment ℝ x y,
        HasFDerivWithinAt f (fderiv ℝ f z) (segment ℝ x y) z := fun z hz =>
      (((hf.differentiableOn (by simp)) z (hKU (hseg hz))).differentiableAt
        (hU.mem_nhds (hKU (hseg hz)))).hasFDerivAt.hasFDerivWithinAt
    have hbound : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ f z‖ ≤ c := fun z hz => by
      have := hc z (hseg hz)
      rwa [zero_add, norm_iteratedFDeriv_one] at this
    have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound
      (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
    simpa using this
  | succ k ih =>
    intro G _ _ f U K hU hKU hK hf c hc x hx hvan y hy
    -- Apply the induction hypothesis to `df : E → (E →L[ℝ] G)`.
    have hf' : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
    have hc' : ∀ z ∈ K, ‖iteratedFDeriv ℝ (k + 1) (fderiv ℝ f) z‖ ≤ c := fun z hz => by
      rw [norm_iteratedFDeriv_fderiv]
      exact hc z hz
    have hvan' : ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j (fderiv ℝ f) x = 0 := fun j hj hjk => by
      have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (n := j) (x := x)
      rw [hvan (j + 1) (by omega) (by omega), norm_zero, norm_eq_zero] at h
      exact h
    have hdf0 : fderiv ℝ f x = 0 := by
      have h := congrArg norm (hvan 1 le_rfl (by omega))
      rwa [norm_iteratedFDeriv_one, norm_zero, norm_eq_zero] at h
    have key : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ c * ‖z - x‖ ^ (k + 1) := fun z hz => by
      have := ih hU hKU hK hf' hc' hx hvan' z hz
      rwa [hdf0, sub_zero] at this
    have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc x hx)
    -- Mean value inequality on the segment, with the bound `c ‖y - x‖^{k+1}`.
    have hseg : segment ℝ x y ⊆ K := hK.segment_subset hx hy
    have hderiv : ∀ z ∈ segment ℝ x y,
        HasFDerivWithinAt f (fderiv ℝ f z) (segment ℝ x y) z := fun z hz =>
      (((hf.differentiableOn (by simp)) z (hKU (hseg hz))).differentiableAt
        (hU.mem_nhds (hKU (hseg hz)))).hasFDerivAt.hasFDerivWithinAt
    have hbound : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ f z‖ ≤ c * ‖y - x‖ ^ (k + 1) := fun z hz => by
      refine (key z (hseg hz)).trans ?_
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le_of_mem_segment hz) _) hc0
    have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound
      (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
    calc ‖f y - f x‖ ≤ c * ‖y - x‖ ^ (k + 1) * ‖y - x‖ := this
      _ = c * ‖y - x‖ ^ (k + 1 + 1) := by ring

variable [FiniteDimensional ℝ E]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Step 3 of Sard's theorem.** If `(k+1) p > n`, then `f(Cₖ ∩ K)` has measure zero for every
compact convex `K ⊆ U`. -/
theorem measure_image_vanishSet_inter_eq_zero (μ : Measure F) [μ.IsAddHaarMeasure]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {k : ℕ} (hk : finrank ℝ E < (k + 1) * finrank ℝ F)
    {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) (hKU : K ⊆ U) :
    μ (f '' (vanishSet f U k ∩ K)) = 0 := by
  -- If `K` is empty there is nothing to prove.
  rcases K.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · simp
  -- A bound `c` for `‖D^{k+1} f‖` on the compact set `K`.
  have hcont : ContinuousOn (iteratedFDeriv ℝ (k + 1) f) K :=
    ((hf.continuousOn_iteratedFDerivWithin (m := k + 1) (mod_cast le_top) hU.uniqueDiffOn).congr
      (iteratedFDerivWithin_of_isOpen (k + 1) hU).symm).mono hKU
  obtain ⟨c, hc⟩ := hK.exists_bound_of_continuousOn hcont
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc z₀ hz₀)
  -- `f` is Hölder of exponent `k+1` on `Cₖ ∩ K`.
  set S := vanishSet f U k ∩ K with hS
  let C : ℝ≥0 := ⟨c, hc0⟩
  have hC : (C : ℝ≥0∞) = ENNReal.ofReal c := (ENNReal.ofReal_coe_nnreal).symm
  have hholder : HolderOnWith C (k + 1 : ℕ) f S := by
    intro x hx y hy
    have hb := norm_sub_le_of_iteratedFDeriv_eq_zero k hU hKU hKc hf hc hx.2 hx.1.2 y hy.2
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, norm_sub_rev (f x)]
    calc ENNReal.ofReal ‖f y - f x‖ ≤ ENNReal.ofReal (c * ‖y - x‖ ^ (k + 1)) :=
          ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal c * ENNReal.ofReal ‖y - x‖ ^ (k + 1) := by
          rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_pow (norm_nonneg _)]
      _ = (C : ℝ≥0∞) * ENNReal.ofReal ‖x - y‖ ^ (((k + 1 : ℕ) : ℝ≥0) : ℝ) := by
          rw [norm_sub_rev, hC]
          congr 1
          rw [NNReal.coe_natCast, ENNReal.rpow_natCast]
  -- Hence the image has Hausdorff dimension `≤ n/(k+1) < p`.
  have hdim : dimH (f '' S) < finrank ℝ F := by
    have h1 : dimH (f '' S) ≤ dimH S / ((k + 1 : ℕ) : ℝ≥0) :=
      hholder.dimH_image_le (by positivity)
    have h2 : dimH S ≤ finrank ℝ E := by
      rw [← Real.dimH_univ_eq_finrank E]
      exact dimH_mono (subset_univ _)
    have h3 : (dimH S / ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0∞) < finrank ℝ F := by
      rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp))]
      calc dimH S ≤ (finrank ℝ E : ℝ≥0∞) := h2
        _ < ((k + 1) * finrank ℝ F : ℕ) := by exact_mod_cast hk
        _ = (finrank ℝ F : ℝ≥0∞) * ((k + 1 : ℕ) : ℝ≥0) := by
          push_cast
          ring
    exact h1.trans_lt h3
  exact addHaar_eq_zero_of_dimH_lt_finrank μ hdim

end Sard

end Milnor
