import Milnor.Chapter3.Step1
import Milnor.Chapter3.Step3

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §3 (pp. 16–19) and §2 (p. 10).

# Sard's theorem

> **Theorem of Sard.** Let `f : U → ℝᵖ` be a smooth map, with `U` open in `ℝⁿ`, and let `C` be the
> set of critical points; that is the set of all `x ∈ U` with `rank dfₓ < p`. Then `f(C) ⊆ ℝᵖ` has
> measure zero.

The proof is by induction on `n` (Milnor p. 16): "To start the induction, the theorem is
certainly true for `n = 0`", and for `n ≥ 1` the set `C` is the union of `C ∖ C₁`, the sets
`Cᵢ ∖ Cᵢ₊₁` for `1 ≤ i < k`, and `Cₖ`, whose images are null by Steps 1, 2, 3 respectively.
Steps 1 and 2 use the induction hypothesis in dimension `n - 1`; Step 3 does not.

Two small points that Milnor leaves implicit:
* if the target is zero-dimensional, every linear map onto it is surjective, so `C = ∅` and there
  is nothing to prove; this case has to be treated separately because a Haar measure on a
  zero-dimensional space is a point mass, not the zero measure;
* the case `n = 0` needs the target to be nontrivial, so that points have measure zero.

We also record Milnor's remark on p. 10: "Since a set of measure zero cannot contain any
nonvacuous open set, it follows that the complement `ℝᵖ ∖ f(C)` must be everywhere dense."
-/

open Set Filter Topology Function MeasureTheory Module
open scoped ContDiff

noncomputable section

namespace Milnor

namespace Sard

universe u

/-- If the target is a subsingleton, there are no critical points. -/
theorem critSet_eq_empty_of_subsingleton {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Subsingleton F] (f : E → F) (U : Set E) :
    critSet f U = ∅ := by
  ext x
  simp only [critSet, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_not]
  intro _
  exact Function.surjective_to_subsingleton _

/-- **Sard's theorem**, in the form proved by induction on the dimension of the domain. -/
theorem sardStatement : ∀ n : ℕ, SardStatement.{u} n := by
  intro n
  induction n with
  | zero =>
    intro E _ _ _ hE F _ _ _ _ _ μ _ U hU f hf
    rcases subsingleton_or_nontrivial F with hF | hF
    · rw [critSet_eq_empty_of_subsingleton, image_empty, measure_empty]
    · have : Subsingleton E := Module.finrank_zero_iff.1 hE
      exact (Set.subsingleton_of_subsingleton.image f).measure_zero μ
  | succ m ih =>
    intro E _ _ _ hE F _ _ _ _ _ μ _ U hU f hf
    rcases subsingleton_or_nontrivial F with hF | hF
    · rw [critSet_eq_empty_of_subsingleton, image_empty, measure_empty]
    · have ih' : SardStatement.{u} (finrank ℝ E - 1) := by
        rw [hE]
        simpa using ih
      have hp : 0 < finrank ℝ F := Module.finrank_pos
      set k := m + 1 with hk_def
      have hk : finrank ℝ E < (k + 1) * finrank ℝ F := by
        rw [hE, hk_def]
        nlinarith
      refine measure_mono_null (Set.image_mono (critSet_subset_union f U k)) ?_
      rw [image_union, image_union]
      refine measure_union_null (measure_union_null ?_ ?_) ?_
      · -- Step 1: `f(C ∖ C₁)`.
        have := measure_image_eq_zero_of_locally μ (S := critSet f U \ vanishSet f U 1)
          (T := critSet f U) fun x hx => step1_local ih' μ hU hf hx
        rwa [inter_eq_right.2 diff_subset] at this
      · -- Step 2: `f(Cᵢ ∖ Cᵢ₊₁)` for `1 ≤ i < k`.
        rw [image_iUnion₂]
        rw [measure_iUnion_null_iff]
        intro i
        rw [measure_iUnion_null_iff]
        intro hi
        have hi1 : 1 ≤ i := (Finset.mem_Ico.1 hi).1
        have := measure_image_eq_zero_of_locally μ (S := vanishSet f U i \ vanishSet f U (i + 1))
          (T := vanishSet f U i) fun x hx => step2_local ih' μ hU hf hi1 hx
        rwa [inter_eq_right.2 diff_subset] at this
      · -- Step 3: `f(Cₖ)`.
        have hloc : ∀ x ∈ vanishSet f U k, ∃ V ∈ 𝓝 x, μ (f '' (vanishSet f U k ∩ V)) = 0 := by
          intro x hx
          obtain ⟨r, hr, hB⟩ : ∃ r > 0, Metric.closedBall x r ⊆ U := by
            obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx.1
            exact ⟨r / 2, by positivity,
              (Metric.closedBall_subset_ball (by linarith)).trans hball⟩
          exact ⟨Metric.closedBall x r, Metric.closedBall_mem_nhds x hr,
            measure_image_vanishSet_inter_eq_zero μ hU hf hk (isCompact_closedBall x r)
              (convex_closedBall x r) hB⟩
        have := measure_image_eq_zero_of_locally μ hloc
        rwa [inter_self] at this

end Sard

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Sard's theorem** (Milnor p. 16). Let `f : U → F` be smooth on an open set `U` of a
finite-dimensional real normed space `E`, with values in a finite-dimensional real normed space
`F`, and let `C` be the set of points of `U` where `dfₓ` is not surjective. Then `f(C)` has measure
zero for every Haar measure on `F`. -/
theorem sard (μ : Measure F) [μ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) : μ (f '' Sard.critSet f U) = 0 :=
  Sard.sardStatement (finrank ℝ E) E rfl F μ U hU f hf

/-- Milnor p. 10: "Since a set of measure zero cannot contain any nonvacuous open set, it follows
that the complement `ℝᵖ ∖ f(C)` must be everywhere dense." -/
theorem dense_compl_image_critSet {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) : Dense (f '' Sard.critSet f U)ᶜ := by
  let μ : Measure F := (Module.Basis.ofVectorSpace ℝ F).addHaar
  exact interior_eq_empty_iff_dense_compl.1 (μ.interior_eq_empty_of_null (sard μ hU hf))

end Milnor
