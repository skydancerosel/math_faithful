import Morse.Chapter6.LinearODE
import Mathlib.Analysis.ODE.Gronwall

/-!
Milnor, *Morse Theory*, §14, p. 77: "Thus the Jacobi equation has `2n` linearly independent
solutions, each of which can be defined throughout `γ`" — the global solution theory of linear
equations (Lemma 14.A of the exposition).

# Linear ordinary differential equations: global existence and the propagator

`Morse/Chapter6/LinearODE.lean` proves uniqueness for `x' = A(t)x` and global existence when
`A(t)` is skew-adjoint (parallel transport).  The Jacobi equation is not of that kind, so here:

* `Morse.exists_linearODE`: **global existence** for any continuous `A : ℝ → (E →L E)`, `E`
  complete.  As in Chapter 6 the field is truncated radially, `A(t)ρ_R(x)`, which is bounded and
  Lipschitz, so Picard–Lindelöf gives a solution on any compact interval in one step; now the a
  priori bound comes from **Grönwall's inequality** (`‖x(t)‖ ≤ ‖x₀‖ e^{C|t − t₀|}`, in both time
  directions), and for `R` above that bound the truncation is never active.
* `Morse.linSol A s ξ`: the solution with `x(s) = ξ` (the *propagator*), linear in `ξ`
  (`Morse.linSol_add`, `Morse.linSol_smul`), and `Morse.linFlow A s t : E →L E`, continuous in
  `t` for finite dimensional `E` (`Morse.continuous_linFlow`).
* `Morse.eqOn_Icc_linSol`: a function continuous on `[a, b]` that solves the equation on `(a, b)`
  agrees on `[a, b]` with the propagated solution through any of its values, also at the end
  points: so solutions on a closed interval are determined by their value at any point of it.

## What Milnor leaves implicit

"The solutions can be defined throughout `γ`" for a linear equation is not the local existence
theorem: the local theorem gives solutions on intervals of length about `1/sup‖A‖` only.  Some
global argument is needed (Grönwall's bound plus truncation here; Picard iteration on the whole
interval in the exposition, Lemma 14.A).
-/

open Set Filter Topology Metric
open scoped NNReal

noncomputable section

namespace Morse

section Exist

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_radTrunc_le_norm {R : ℝ} (hR : 0 < R) (x : E) : ‖radTrunc R x‖ ≤ ‖x‖ := by
  have hm : 0 < max R ‖x‖ := lt_max_of_lt_left hR
  rw [radTrunc, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hR.le hm.le)]
  exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one hm).2 (le_max_left _ _))

/-- **Grönwall's bound, forward in time**, for `‖f'‖ ≤ C‖f‖`. -/
theorem norm_le_of_norm_deriv_le {f f' : ℝ → E} {C a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (hb : ∀ t ∈ Ico a b, ‖f' t‖ ≤ C * ‖f t‖) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ ‖f a‖ * Real.exp (C * (t - a)) := by
  intro t ht
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖f a‖) (ε := 0) hf hd le_rfl
    (fun t ht => by simpa using hb t ht) t ht
  rwa [gronwallBound_ε0] at h

variable [CompleteSpace E]

/-- Solutions of `x' = A(t)x` on `(t₀ − a, t₀ + a)` through any initial value, `A` continuous. -/
theorem exists_linearODE_Ioo {A : ℝ → E →L[ℝ] E} (hA : Continuous A) (t₀ : ℝ) (x₀ : E) {a : ℝ}
    (ha : 0 < a) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ∀ t ∈ Ioo (t₀ - a) (t₀ + a), HasDerivAt α (A t (α t)) t := by
  obtain ⟨C, hC⟩ := exists_nnnorm_le_Icc hA (t₀ - a) (t₀ + a)
  set R : ℝ := ‖x₀‖ * Real.exp (C * a) + 1 with hRdef
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
  have hbd : ∀ t ∈ Icc (t₀ - a) (t₀ + a), ‖f t (α t)‖ ≤ C * ‖α t‖ := fun t ht =>
    calc ‖A t (radTrunc R (α t))‖ ≤ ‖A t‖ * ‖radTrunc R (α t)‖ := (A t).le_opNorm _
      _ ≤ C * ‖α t‖ := mul_le_mul (hC t ht) (norm_radTrunc_le_norm hR _) (norm_nonneg _) C.2
  have hcont : ContinuousOn α (Icc (t₀ - a) (t₀ + a)) := fun t ht => (hα t ht).continuousWithinAt
  -- forward in time
  have hfwd : ∀ t ∈ Icc t₀ (t₀ + a), ‖α t‖ ≤ ‖x₀‖ * Real.exp (C * a) := by
    intro t ht
    have h := norm_le_of_norm_deriv_le (f := α) (f' := fun t => f t (α t)) (C := C)
      (hcont.mono (Icc_subset_Icc (by linarith) le_rfl))
      (fun s hs => ((hα s ⟨by linarith [hs.1], hs.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨by linarith [hs.1], hs.2⟩)))
      (fun s hs => hbd s ⟨by linarith [hs.1], hs.2.le⟩) t ht
    rw [hα0] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) C.2
  -- backward in time, by reversing
  have hbwd : ∀ s ∈ Icc (0 : ℝ) a, ‖α (t₀ - s)‖ ≤ ‖x₀‖ * Real.exp (C * a) := by
    have hmaps : MapsTo (fun s : ℝ => t₀ - s) (Icc 0 a) (Icc (t₀ - a) (t₀ + a)) :=
      fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hd : ∀ s ∈ Icc (0 : ℝ) a, HasDerivWithinAt (fun s => α (t₀ - s))
        (-f (t₀ - s) (α (t₀ - s))) (Icc 0 a) s := by
      intro s hs
      have h1 : HasDerivWithinAt (fun s : ℝ => t₀ - s) (-1) (Icc 0 a) s :=
        ((hasDerivAt_id s).const_sub t₀).hasDerivWithinAt
      have := (hα (t₀ - s) (hmaps hs)).scomp s h1 hmaps
      simp only [neg_one_smul] at this
      exact this
    intro s hs
    have h := norm_le_of_norm_deriv_le (f := fun s => α (t₀ - s))
      (f' := fun s => -f (t₀ - s) (α (t₀ - s))) (C := C)
      (fun s hs => (hd s hs).continuousWithinAt)
      (fun s hs => (hd s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs))
      (fun s hs => by rw [norm_neg]; exact hbd _ (hmaps ⟨hs.1, hs.2.le⟩)) s hs
    simp only [sub_zero, hα0] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left hs.2 C.2
  have hnorm : ∀ t ∈ Icc (t₀ - a) (t₀ + a), ‖α t‖ ≤ R := by
    intro t ht
    rcases le_total t₀ t with h | h
    · linarith [hfwd t ⟨h, ht.2⟩]
    · have := hbwd (t₀ - t) ⟨by linarith, by linarith [ht.1]⟩
      rw [sub_sub_cancel] at this
      linarith
  refine ⟨α, hα0, fun t ht => ?_⟩
  have h1 := (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have h2 : f t (α t) = A t (α t) := by
    simp only [hf]
    rw [radTrunc_of_norm_le hR (hnorm t (Ioo_subset_Icc_self ht))]
  rwa [h2] at h1

/-- **Global existence for linear equations** `x' = A(t)x`, `A` continuous (Lemma 14.A of the
exposition): there is a solution on all of `ℝ` through any initial value. -/
theorem exists_linearODE {A : ℝ → E →L[ℝ] E} (hA : Continuous A) (t₀ : ℝ) (x₀ : E) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ∀ t, HasDerivAt α (A t (α t)) t := by
  choose β hβ0 hβ using fun a : {a : ℝ // 0 < a} => exists_linearODE_Ioo hA t₀ x₀ a.2
  have key : ∀ (a b : {a : ℝ // 0 < a}) (t : ℝ), |t - t₀| < a → |t - t₀| < b → β a t = β b t := by
    intro a b t ha hb
    have hmin1 := min_le_left a.1 b.1
    have hmin2 := min_le_right a.1 b.1
    refine linearODE_eqOn hA (a := t₀ - min a.1 b.1) (b := t₀ + min a.1 b.1) (t₀ := t₀)
      ⟨by linarith [lt_min a.2 b.2], by linarith [lt_min a.2 b.2]⟩
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

/-! ### The propagator -/

section Propagator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A : ℝ → E →L[ℝ] E}

open Classical in
/-- **The propagator**: the solution of `x' = A(t)x` with `x(s) = ξ` (for continuous `A`; a junk
constant otherwise). -/
def linSol (A : ℝ → E →L[ℝ] E) (s : ℝ) (ξ : E) : ℝ → E :=
  if h : ∃ α : ℝ → E, α s = ξ ∧ ∀ t, HasDerivAt α (A t (α t)) t then h.choose else fun _ => ξ

theorem linSol_spec (hA : Continuous A) (s : ℝ) (ξ : E) :
    linSol A s ξ s = ξ ∧ ∀ t, HasDerivAt (linSol A s ξ) (A t (linSol A s ξ t)) t := by
  have h := exists_linearODE hA s ξ
  rw [linSol, dif_pos h]
  exact h.choose_spec

theorem linSol_self (hA : Continuous A) (s : ℝ) (ξ : E) : linSol A s ξ s = ξ :=
  (linSol_spec hA s ξ).1

theorem hasDerivAt_linSol (hA : Continuous A) (s : ℝ) (ξ : E) (t : ℝ) :
    HasDerivAt (linSol A s ξ) (A t (linSol A s ξ t)) t :=
  (linSol_spec hA s ξ).2 t

/-- Every global solution is the propagated solution through any of its values. -/
theorem eq_linSol (hA : Continuous A) {α : ℝ → E} (hα : ∀ t, HasDerivAt α (A t (α t)) t)
    (s : ℝ) : α = linSol A s (α s) :=
  linearODE_eq hA hα (hasDerivAt_linSol hA s _) (linSol_self hA s _).symm

theorem linSol_add (hA : Continuous A) (s : ℝ) (ξ η : E) :
    linSol A s (ξ + η) = linSol A s ξ + linSol A s η := by
  have h : ∀ t, HasDerivAt (linSol A s ξ + linSol A s η)
      (A t ((linSol A s ξ + linSol A s η) t)) t := fun t => by
    rw [Pi.add_apply, map_add]
    exact (hasDerivAt_linSol hA s ξ t).add (hasDerivAt_linSol hA s η t)
  rw [eq_linSol hA h s, Pi.add_apply, linSol_self hA, linSol_self hA]

theorem linSol_smul (hA : Continuous A) (s : ℝ) (c : ℝ) (ξ : E) :
    linSol A s (c • ξ) = c • linSol A s ξ := by
  have h : ∀ t, HasDerivAt (c • linSol A s ξ) (A t ((c • linSol A s ξ) t)) t := fun t => by
    rw [Pi.smul_apply, map_smul]
    exact (hasDerivAt_linSol hA s ξ t).const_smul c
  rw [eq_linSol hA h s, Pi.smul_apply, linSol_self hA]

/-- Propagating from `s` to `s'` and then on is propagating from `s`. -/
theorem linSol_trans (hA : Continuous A) (s s' : ℝ) (ξ : E) :
    linSol A s' (linSol A s ξ s') = linSol A s ξ :=
  (eq_linSol hA (hasDerivAt_linSol hA s ξ) s').symm

theorem continuous_linSol (hA : Continuous A) (s : ℝ) (ξ : E) : Continuous (linSol A s ξ) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_linSol hA s ξ t).continuousAt

/-- **Uniqueness on a closed interval**: a function continuous on `[a, b]` solving
`x' = A(t)x` on `(a, b)` agrees on `[a, b]` with the propagated solution through its value at
any point `s` of `[a, b]` (end points included). -/
theorem eqOn_Icc_linSol (hA : Continuous A) {f : ℝ → E} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hd : ∀ t ∈ Ioo a b, HasDerivAt f (A t (f t)) t) {s : ℝ}
    (hs : s ∈ Icc a b) : EqOn f (linSol A s (f s)) (Icc a b) := by
  set m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  set g := linSol A m (f m)
  have h1 : EqOn f g (Ioo a b) := linearODE_eqOn hA hm hd
    (fun t _ => hasDerivAt_linSol hA m _ t) (linSol_self hA m _).symm
  have h2 : EqOn f g (Icc a b) := by
    have hcl : Icc a b ⊆ closure (Ioo a b) := by rw [closure_Ioo hab.ne]
    exact h1.of_subset_closure hf (continuous_linSol hA m _).continuousOn Ioo_subset_Icc_self hcl
  have h3 : g = linSol A s (f s) := by
    have h4 : g s = f s := (h2 hs).symm
    have := eq_linSol hA (hasDerivAt_linSol hA m (f m)) s
    change g = linSol A s (g s) at this
    rw [h4] at this
    exact this
  rw [← h3]
  exact h2

variable [FiniteDimensional ℝ E]

/-- The propagator from `s` to `t` as a continuous linear map. -/
def linFlow (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (s t : ℝ) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ => linSol A s ξ t
      map_add' := fun ξ η => by rw [linSol_add hA]; rfl
      map_smul' := fun c ξ => by rw [linSol_smul hA]; rfl }

theorem linFlow_apply (hA : Continuous A) (s t : ℝ) (ξ : E) :
    linFlow A hA s t ξ = linSol A s ξ t := rfl

theorem continuous_linFlow (hA : Continuous A) (s : ℝ) : Continuous (linFlow A hA s) :=
  continuous_clm_apply.2 fun ξ => continuous_linSol hA s ξ

end Propagator

end Morse
