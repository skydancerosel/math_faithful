import Milnor.Chapter2.WithBoundary
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §2, p. 12.

> **Example.** The unit disk `Dᵐ`, consisting of all `x ∈ ℝᵐ` with `1 - Σ xᵢ² ≥ 0`, is a smooth
> manifold, with boundary equal to `Sᵐ⁻¹`.

This is Lemma 3 applied to `g(x) = 1 - ‖x‖²`, whose derivative at `x` is `-2⟨x, ·⟩`, nonzero
whenever `x ≠ 0`, in particular on the sphere `g = 0`.
-/

open Set Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The function `g(x) = 1 - ‖x‖²`. -/
def diskFun (x : E) : ℝ := 1 - ‖x‖ ^ 2

theorem contMDiff_diskFun : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (diskFun : E → ℝ) :=
  (contDiff_const.sub (contDiff_norm_sq ℝ)).contMDiff

/-- `0` is a regular value of `x ↦ 1 - ‖x‖²`. -/
theorem isRegularValue_diskFun : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (diskFun : E → ℝ) 0 := by
  intro x hx
  have hx1 : ‖x‖ ^ 2 = 1 := by
    have : (1 : ℝ) - ‖x‖ ^ 2 = 0 := hx
    linarith
  have hderiv : HasFDerivAt (diskFun : E → ℝ) (-(2 • innerSL ℝ x)) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_sub 1
  show Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (diskFun : E → ℝ) x)
  rw [mfderiv_eq_fderiv, hderiv.fderiv]
  intro t
  let t' : ℝ := t
  refine ⟨(-t' / 2) • x, ?_⟩
  show (-(2 • innerSL ℝ x)) ((-t' / 2) • x) = t'
  have h1 : (innerSL ℝ x) ((-t' / 2) • x) = -t' / 2 := by
    show inner ℝ x ((-t' / 2) • x) = -t' / 2
    rw [inner_smul_right, real_inner_self_eq_norm_sq, hx1, mul_one]
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, h1, nsmul_eq_mul]
  ring

/-- **Milnor's example** (p. 12): the closed unit ball in `E = ℝᵐ` is a manifold with boundary
the unit sphere. -/
theorem isHalfSliceSubmanifold_closedBall {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (hZ : finrank ℝ Z + 1 = finrank ℝ E) :
    IsHalfSliceSubmanifold 𝓘(ℝ, E) Z (Metric.closedBall (0 : E) 1) (Metric.sphere (0 : E) 1) := by
  have h := isHalfSliceSubmanifold_of_regularValue hZ contMDiff_diskFun
    (isRegularValue_diskFun (E := E))
  have h1 : {p : E | 0 ≤ diskFun p} = Metric.closedBall 0 1 := by
    ext x
    simp only [mem_setOf_eq, diskFun, Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro hx
      have : ‖x‖ ^ 2 ≤ 1 := by linarith
      nlinarith [norm_nonneg x]
    · intro hx
      have : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
      linarith
  have h2 : {p : E | diskFun p = 0} = Metric.sphere 0 1 := by
    ext x
    simp only [mem_setOf_eq, diskFun, mem_sphere_iff_norm, sub_zero]
    constructor
    · intro hx
      have : ‖x‖ ^ 2 = 1 := by linarith
      nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1), sq_nonneg (‖x‖ + 1)]
    · intro hx
      rw [hx]; ring
  rw [h1, h2] at h
  exact h

/-- The unit disk `Dᵐ⁺¹ ⊆ ℝᵐ⁺¹` is a manifold with boundary `Sᵐ`, modelled on the half-space
over `ℝᵐ`. -/
theorem isHalfSliceSubmanifold_unitDisk (m : ℕ) :
    IsHalfSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (EuclideanSpace ℝ (Fin m))
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :=
  isHalfSliceSubmanifold_closedBall (by simp [finrank_euclideanSpace_fin])

end Milnor
