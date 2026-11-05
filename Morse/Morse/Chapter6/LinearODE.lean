import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
Milnor, *Morse Theory*, §8, proof of Lemma 8.2 (p. 47): global solutions of linear differential
equations.

# Linear ordinary differential equations

In the proof of Lemma 8.2 Milnor writes the equation of a parallel field in local coordinates,
observes that it is linear, and concludes (citing Graves, *The Theory of Functions of Real
Variables*, p. 152) that its solutions are uniquely determined by their initial values and "can be
defined for all relevant values of `t`".  Mathlib (v4.33.1) has the Picard–Lindelöf theorem
(`IsPicardLindelof`) on intervals whose length is limited by a bound for the field on a ball, and
Grönwall-type uniqueness (`ODE_solution_unique_of_mem_Ioo`), but no global existence theorem for
linear equations.  This file supplies what is needed for parallel transport
(`Morse/Chapter6/Parallel.lean`), for a continuous family `A : ℝ → (E →L E)`:

* `Morse.linearODE_eqOn`, `Morse.linearODE_eq`: **uniqueness**.  Two solutions of `x' = A(t)x` on
  an open interval, or on `ℝ`, which agree at one time agree everywhere (Grönwall; `A` is
  uniformly bounded on compact intervals, hence uniformly Lipschitz there).
* `Morse.exists_skewLinearODE`: **global existence when `A(t)` is skew-adjoint**
  (`⟨A(t)x, x⟩ = 0`), the case of parallel transport on `N ⊆ ℝᴷ`.  Solutions then have constant
  norm, and the field `A(t)` may be replaced by `A(t) ∘ ρ_R`, `ρ_R` the radial retraction onto
  the ball of radius `R > |x₀|` (`Morse.radTrunc`, 2-Lipschitz), which is bounded; Picard–Lindelöf
  gives a solution of the truncated equation on any compact interval in one step, its norm is
  constant, so the truncation is never active, and solutions on nested intervals are glued by
  uniqueness.

## What Milnor leaves implicit

"Since these equations are linear, the solutions can be defined for all relevant values of `t`":
the local existence theorem gives solutions only on intervals of length about `1/sup‖A‖`, and the
global statement needs either an a priori bound (here: the norm is constant) together with a
truncation, or a continuation argument.  On a manifold Milnor's coordinate equations also have to
be patched from chart to chart along the curve; in the embedded setting of
`Morse/Chapter6/Parallel.lean` there is a single linear equation in `ℝᴷ` and no patching.
-/

open Set Filter Topology Metric
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace Morse

/-! ### Uniqueness -/

section Unique

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous family of operators is uniformly bounded on a compact interval. -/
theorem exists_nnnorm_le_Icc {A : ℝ → E →L[ℝ] E} (hA : Continuous A) (a b : ℝ) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA.continuousOn
  refine ⟨C.toNNReal, fun t ht => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact (hC t ht).trans (Real.le_coe_toNNReal C)

/-- **Uniqueness for linear equations** `x' = A(t)x` on an open interval. -/
theorem linearODE_eqOn {A : ℝ → E →L[ℝ] E} (hA : Continuous A) {f g : ℝ → E} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) (hf : ∀ t ∈ Ioo a b, HasDerivAt f (A t (f t)) t)
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (A t (g t)) t) (h : f t₀ = g t₀) : EqOn f g (Ioo a b) := by
  obtain ⟨K, hK⟩ := exists_nnnorm_le_Icc hA a b
  exact ODE_solution_unique_of_mem_Ioo (v := fun t => A t) (s := fun _ => univ) (K := K)
    (fun t ht => ((A t).lipschitz.weaken (hK t (Ioo_subset_Icc_self ht))).lipschitzOnWith) ht₀
    (fun t ht => ⟨hf t ht, mem_univ _⟩) (fun t ht => ⟨hg t ht, mem_univ _⟩) h

/-- **Uniqueness for linear equations** `x' = A(t)x` on `ℝ`. -/
theorem linearODE_eq {A : ℝ → E →L[ℝ] E} (hA : Continuous A) {f g : ℝ → E} {t₀ : ℝ}
    (hf : ∀ t, HasDerivAt f (A t (f t)) t) (hg : ∀ t, HasDerivAt g (A t (g t)) t)
    (h : f t₀ = g t₀) : f = g := by
  funext t
  have h1 := abs_nonneg t
  have h2 := abs_nonneg t₀
  have hmem : ∀ s, |s| ≤ |t| + |t₀| → s ∈ Ioo (-(|t| + |t₀| + 1)) (|t| + |t₀| + 1) :=
    fun s hs => ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩
  exact linearODE_eqOn hA (hmem t₀ (by linarith)) (fun s _ => hf s) (fun s _ => hg s) h
    (hmem t (by linarith))

end Unique

/-! ### The radial truncation -/

section Trunc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial retraction `x ↦ (R / max R ‖x‖) • x` of `E` onto the closed ball of radius `R`. -/
def radTrunc (R : ℝ) (x : E) : E := (R / max R ‖x‖) • x

theorem radTrunc_of_norm_le {R : ℝ} {x : E} (hR : 0 < R) (hx : ‖x‖ ≤ R) : radTrunc R x = x := by
  rw [radTrunc, max_eq_left hx, div_self hR.ne', one_smul]

theorem norm_radTrunc_le {R : ℝ} (hR : 0 < R) (x : E) : ‖radTrunc R x‖ ≤ R := by
  have hm : 0 < max R ‖x‖ := lt_max_of_lt_left hR
  rw [radTrunc, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hR.le hm.le),
    div_mul_eq_mul_div, div_le_iff₀ hm]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hR.le

/-- The radial retraction is `2`-Lipschitz. -/
theorem lipschitzWith_radTrunc {R : ℝ} (hR : 0 < R) : LipschitzWith 2 (radTrunc (E := E) R) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  set mx := max R ‖x‖ with hmx_def
  set my := max R ‖y‖ with hmy_def
  have hmx : 0 < mx := lt_max_of_lt_left hR
  have hmy : 0 < my := lt_max_of_lt_left hR
  have hc : R / my = R / mx - R * (my - mx) / (mx * my) := by
    field_simp
    ring
  have key : radTrunc R x - radTrunc R y =
      (R / mx) • (x - y) + (R * (my - mx) / (mx * my)) • y := by
    rw [radTrunc, radTrunc, ← hmx_def, ← hmy_def, hc, sub_smul, smul_sub]
    abel
  have h1 : ‖(R / mx) • (x - y)‖ ≤ ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hR.le hmx.le)]
    exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one hmx).2 (le_max_left _ _))
  have hd : |my - mx| ≤ ‖x - y‖ := by
    calc |my - mx| ≤ |‖y‖ - ‖x‖| := by
          rw [hmx_def, hmy_def, max_comm R ‖y‖, max_comm R ‖x‖]
          exact abs_max_sub_max_le_abs _ _ _
      _ ≤ ‖y - x‖ := abs_norm_sub_norm_le _ _
      _ = ‖x - y‖ := norm_sub_rev _ _
  have h2 : ‖(R * (my - mx) / (mx * my)) • y‖ ≤ ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hR, abs_of_pos (mul_pos hmx hmy)]
    have hy : ‖y‖ ≤ my := le_max_right _ _
    calc R * |my - mx| / (mx * my) * ‖y‖ ≤ R * |my - mx| / (mx * my) * my :=
          mul_le_mul_of_nonneg_left hy (by positivity)
      _ = (R / mx) * |my - mx| := by field_simp
      _ ≤ 1 * |my - mx| :=
          mul_le_mul_of_nonneg_right ((div_le_one hmx).2 (le_max_left _ _)) (abs_nonneg _)
      _ ≤ ‖x - y‖ := by rw [one_mul]; exact hd
  rw [dist_eq_norm, dist_eq_norm, key]
  calc ‖(R / mx) • (x - y) + (R * (my - mx) / (mx * my)) • y‖
      ≤ ‖(R / mx) • (x - y)‖ + ‖(R * (my - mx) / (mx * my)) • y‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ + ‖x - y‖ := add_le_add h1 h2
    _ = (2 : ℝ≥0) * ‖x - y‖ := by push_cast; ring

end Trunc

/-! ### Global existence for skew-adjoint coefficients -/

section Exist

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Solutions of `x' = A(t)x` on an interval `[t₀ − a, t₀ + a]`, `A(t)` skew-adjoint, through any
initial value. -/
theorem exists_skewLinearODE_Ioo {A : ℝ → E →L[ℝ] E} (hA : Continuous A)
    (hskew : ∀ t x, ⟪A t x, x⟫ = 0) (t₀ : ℝ) (x₀ : E) {a : ℝ} (ha : 0 < a) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ∀ t ∈ Ioo (t₀ - a) (t₀ + a), HasDerivAt α (A t (α t)) t := by
  obtain ⟨C, hC⟩ := exists_nnnorm_le_Icc hA (t₀ - a) (t₀ + a)
  set R : ℝ := ‖x₀‖ + 1 with hRdef
  have hR : 0 < R := by positivity
  set f : ℝ → E → E := fun t x => A t (radTrunc R x) with hf
  set L : ℝ≥0 := C * R.toNNReal with hL
  have ht₀ : t₀ ∈ Icc (t₀ - a) (t₀ + a) := ⟨by linarith, by linarith⟩
  have hpl : IsPicardLindelof f (⟨t₀, ht₀⟩ : Icc (t₀ - a) (t₀ + a)) x₀ (L * a.toNNReal) 0 L
      (C * 2) :=
    { lipschitzOnWith := fun t ht =>
        (((A t).lipschitz.weaken (hC t ht)).comp (lipschitzWith_radTrunc hR)).lipschitzOnWith
      continuousOn := fun x _ => (hA.clm_apply continuous_const).continuousOn
      norm_le := fun t ht x _ => by
        calc ‖A t (radTrunc R x)‖ ≤ ‖A t‖ * ‖radTrunc R x‖ := (A t).le_opNorm _
          _ ≤ C * R := mul_le_mul (hC t ht) (norm_radTrunc_le hR x) (norm_nonneg _) C.2
          _ = L := by rw [hL, NNReal.coe_mul, Real.coe_toNNReal R hR.le]
      mul_max_le := by
        simp only [NNReal.coe_mul, Real.coe_toNNReal a ha.le, NNReal.coe_zero, sub_zero]
        rw [show t₀ + a - t₀ = a by ring, show t₀ - (t₀ - a) = a by ring, max_self] }
  obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  -- the norm of `α` is constant
  have hd : ∀ t ∈ Icc (t₀ - a) (t₀ + a),
      HasDerivWithinAt (fun s => ‖α s‖ ^ 2) 0 (Icc (t₀ - a) (t₀ + a)) t := by
    intro t ht
    have h := (hα t ht).norm_sq
    have h0 : 2 * ⟪α t, f t (α t)⟫ = 0 := by
      simp only [hf, radTrunc, map_smul, inner_smul_right]
      rw [real_inner_comm (A t (α t)) (α t), hskew, mul_zero, mul_zero]
    rwa [h0] at h
  have hcont : ContinuousOn (fun s => ‖α s‖ ^ 2) (Icc (t₀ - a) (t₀ + a)) :=
    fun t ht => (hd t ht).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont fun t ht =>
    (hd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))
  have hnorm : ∀ t ∈ Icc (t₀ - a) (t₀ + a), ‖α t‖ ≤ R := by
    intro t ht
    have h1 := (hconst t ht).trans (hconst t₀ ht₀).symm
    simp only [hα0] at h1
    have h2 : ‖α t‖ = ‖x₀‖ := by
      have := congrArg Real.sqrt h1
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
    linarith
  refine ⟨α, hα0, fun t ht => ?_⟩
  have h1 := (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have h2 : f t (α t) = A t (α t) := by
    simp only [hf]
    rw [radTrunc_of_norm_le hR (hnorm t (Ioo_subset_Icc_self ht))]
  rwa [h2] at h1

/-- **Global existence for linear equations with skew-adjoint coefficients**: if `A` is continuous
and `⟨A(t)x, x⟩ = 0`, then `x' = A(t)x` has a solution on all of `ℝ` through any initial
value. -/
theorem exists_skewLinearODE {A : ℝ → E →L[ℝ] E} (hA : Continuous A)
    (hskew : ∀ t x, ⟪A t x, x⟫ = 0) (t₀ : ℝ) (x₀ : E) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ∀ t, HasDerivAt α (A t (α t)) t := by
  choose β hβ0 hβ using fun a : {a : ℝ // 0 < a} => exists_skewLinearODE_Ioo hA hskew t₀ x₀ a.2
  have key : ∀ (a b : {a : ℝ // 0 < a}) (t : ℝ), |t - t₀| < a → |t - t₀| < b → β a t = β b t := by
    intro a b t ha hb
    have hc : 0 < min a.1 b.1 := lt_min a.2 b.2
    have hmin1 := min_le_left a.1 b.1
    have hmin2 := min_le_right a.1 b.1
    refine linearODE_eqOn hA (a := t₀ - min a.1 b.1) (b := t₀ + min a.1 b.1) (t₀ := t₀)
      ⟨by linarith, by linarith⟩
      (fun s hs => hβ a s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (fun s hs => hβ b s ⟨by linarith [hs.1], by linarith [hs.2]⟩) (by rw [hβ0, hβ0]) ?_
    have hlt : |t - t₀| < min a.1 b.1 := lt_min ha hb
    rw [abs_lt] at hlt
    exact ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
  refine ⟨fun t => β ⟨|t - t₀| + 1, by positivity⟩ t, hβ0 _, fun t => ?_⟩
  have ht : t ∈ Ioo (t₀ - (|t - t₀| + 1)) (t₀ + (|t - t₀| + 1)) := by
    constructor <;> linarith [neg_abs_le (t - t₀), le_abs_self (t - t₀)]
  refine (hβ _ t ht).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  refine key _ _ s (lt_add_one _) ?_
  rw [abs_lt]
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

end Exist

end Morse
