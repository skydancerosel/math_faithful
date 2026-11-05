import Milnor.Chapter5.Degree
import Milnor.Chapter5.LevelOrient

/-!
# Orientations restricted to open subsets

An open subset `U` of a manifold `M` is a manifold (Mathlib), with charts the restrictions of
the charts of `M`.  The inclusion has derivative the identity in these charts, so orientations,
signs and regular values restrict without change.  This is used in Chapter 6 for maps such as
`v/|v|`, which are smooth only away from the zeros of `v`.
-/

open Set Module Filter Topology Function TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] {n : ℕ}

theorem extChartAt_opens_eq (U : Opens M) (x : U) :
    (extChartAt I x : U → E) = extChartAt I x.1 ∘ Subtype.val := rfl

/-- The derivative of the inclusion `U → M` is the identity (in the restricted charts). -/
theorem mfd_subtype_val_opens (U : Opens M) (y : U) :
    mfd I I (Subtype.val : U → M) y = ContinuousLinearMap.id ℝ E := by
  have h1 := (hasMFDerivAt_extChartAt_self (I := I) y.1).comp y
    (hasMFDerivAt_mfd (I := I) (J := I) ((contMDiff_subtype_val (I := I) (n := ∞) (U := U)).mdifferentiableAt (x := y) (by simp)))
  have h2 : (extChartAt I y.1 ∘ Subtype.val : U → E) = extChartAt I y := rfl
  rw [h2] at h1
  have h3 := hasMFDerivAt_unique h1 (hasMFDerivAt_extChartAt_self (I := I) y)
  have h4 : (ContinuousLinearMap.id ℝ E).comp (mfd I I (Subtype.val : U → M) y) =
      mfd I I (Subtype.val : U → M) y := ContinuousLinearMap.id_comp _
  rw [← h4]
  exact h3

/-- The derivative of a restricted map. -/
theorem mfd_comp_subtype_val (U : Opens M) {f : M → N} {y : U} (hf : MDifferentiableAt I J f y.1) :
    mfd I J (f ∘ Subtype.val) y = mfd I J f y.1 := by
  have := HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (I := I) (J := J) hf).comp y
    (hasMFDerivAt_mfd (I := I) (J := I) ((contMDiff_subtype_val (I := I) (n := ∞) (U := U)).mdifferentiableAt (x := y) (by simp))))
  rw [this, mfd_subtype_val_opens]
  exact ContinuousLinearMap.ext fun v => rfl

/-- An orientation restricted to an open subset. -/
def Orient.restrict (oM : Orient I M n) (U : Opens M) : Orient I U n where
  or x := oM.or x.1
  cont x := by
    have h := continuous_subtype_val.continuousAt.eventually (oM.cont x.1)
    filter_upwards [h, (isOpen_extChartAt_source (I := I) x).mem_nhds
      (mem_extChartAt_source (I := I) x)] with y hy hy2
    have hy1 : y.1 ∈ (chartAt H x.1).source := by
      rw [extChartAt_source] at hy2
      change y ∈ ((chartAt H x.1).subtypeRestr ⟨x⟩).source at hy2
      rw [OpenPartialHomeomorph.subtypeRestr_source] at hy2
      exact hy2
    have h1 : mfd I 𝓘(ℝ, E) (extChartAt I x) y = mfd I 𝓘(ℝ, E) (extChartAt I x.1) y.1 := by
      rw [extChartAt_opens_eq]
      exact mfd_comp_subtype_val U ((contMDiffAt_extChartAt' (I := I) (n := ∞) (x := x.1)
        hy1).mdifferentiableAt (by simp))
    rw [h1]
    exact hy

@[simp] theorem Orient.restrict_or (oM : Orient I M n) (U : Opens M) (x : U) :
    (oM.restrict U).or x = oM.or x.1 := rfl

/-- The sign of a restricted map. -/
theorem signAt_restrict (oM : Orient I M n) (oN : Orient J N n) (U : Opens M) {f : M → N} {y : U}
    (hf : MDifferentiableAt I J f y.1) :
    signAt (oM.restrict U) oN (f ∘ Subtype.val) y = signAt oM oN f y.1 := by
  unfold signAt
  rw [mfd_comp_subtype_val U hf]
  rfl

/-- Regular values of a restricted map. -/
theorem IsRegularValue.comp_subtype_val_opens (U : Opens M) {f : M → N} {y : N}
    (hf : ∀ x : U, MDifferentiableAt I J f x.1) (hy : IsRegularValue I J f y) :
    IsRegularValue I J (f ∘ Subtype.val : U → N) y := by
  intro x hx
  show Function.Surjective (mfd I J (f ∘ Subtype.val) x)
  rw [mfd_comp_subtype_val U (hf x)]
  exact hy x.1 hx

end Milnor
