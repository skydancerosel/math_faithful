import Mathlib

/-!
Milnor, *Morse Theory*, §2, p. 10 (infrastructure for the smooth dependence of solutions of
ordinary differential equations on the initial point).

# The Nemytskii operator `γ ↦ Y ∘ γ` on `C([0, 1], E)`

Milnor quotes as "well known" (p. 10) that the solution of `dφ_t(q)/dt = X_{φ_t(q)}`,
`φ_0(q) = q`, "depends smoothly on the initial conditions". The proof given in
`Morse/Flow/Smooth.lean` writes the flow line through `x` as the solution `γ` of the integral
equation `γ(s) = x + ∫₀ˢ X(γ(r)) dr` in the Banach space `C([0, 1], E)` and applies the inverse
function theorem there. The only nonlinear ingredient of that equation is the *Nemytskii* (or
*superposition*) operator `N_Y : γ ↦ Y ∘ γ`, and this file proves that it is as smooth as `Y`:

* `Morse.Flow.hasFDerivAt_nem`: if `Y` is `C¹`, then `N_Y` is differentiable at every `γ`, with
  derivative the pointwise application `η ↦ (s ↦ dY_{γ(s)} (η(s)))` of the curve of operators
  `N_{dY}(γ)`. The remainder estimate is uniform in `s` because `dY` is uniformly continuous near
  the compact set `γ([0, 1])` (Heine–Cantor), combined with the mean value inequality.
* `Morse.Flow.contDiff_nem`: if `Y` is `Cⁿ`, so is `N_Y`. By induction on `n`: the derivative of
  `N_Y` is `N_{dY}` followed by a continuous linear map (`Morse.Flow.pmul`), and `dY` is
  `Cⁿ⁻¹`. The induction runs over the target space, which changes from `F` to `E →L[ℝ] F`, so the
  statement is made for all `F` in the universe of `E`.

Neither fact is in Mathlib (v4.33.1), and Milnor's reference (Graves) proves smooth dependence
by a different route (the variational equation).

The time interval is Mathlib's `unitInterval = [0, 1]`; `C(unitInterval, E)` carries the sup
norm, and is a Banach space when `E` is.
-/

open Set Filter Topology Metric
open scoped ContDiff NNReal

noncomputable section

namespace Morse.Flow

universe u v

section Defs

section Nem

variable {E : Type*} [NormedAddCommGroup E] {F : Type*} [NormedAddCommGroup F]

/-- The Nemytskii operator of a continuous map `Y : E → F`: `nem Y γ = Y ∘ γ`. -/
def nem (Y : C(E, F)) (γ : C(unitInterval, E)) : C(unitInterval, F) :=
  Y.comp γ

@[simp]
theorem nem_apply (Y : C(E, F)) (γ : C(unitInterval, E)) (s : unitInterval) :
    nem Y γ s = Y (γ s) :=
  rfl

theorem continuous_nem (Y : C(E, F)) : Continuous (nem Y) :=
  ContinuousMap.continuous_postcomp Y

/-- A `K`-Lipschitz `Y` gives a `K`-Lipschitz Nemytskii operator (for the sup norm). -/
theorem lipschitzWith_nem {Y : C(E, F)} {K : ℝ≥0} (hY : LipschitzWith K Y) :
    LipschitzWith K (nem Y) :=
  LipschitzWith.of_dist_le_mul fun γ δ =>
    (ContinuousMap.dist_le (by positivity)).2 fun s =>
      (hY.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist s)
        K.2)

theorem norm_nem_le {Y : C(E, F)} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖Y x‖ ≤ C)
    (γ : C(unitInterval, E)) : ‖nem Y γ‖ ≤ C :=
  (ContinuousMap.norm_le _ hC0).2 fun _ => hC _

end Nem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The bilinear map underlying `pmul`. -/
def pmulₗ : C(unitInterval, E →L[ℝ] F) →ₗ[ℝ] C(unitInterval, E) →ₗ[ℝ] C(unitInterval, F) :=
  LinearMap.mk₂ ℝ
    (fun (A : C(unitInterval, E →L[ℝ] F)) (η : C(unitInterval, E)) =>
      (⟨fun s => A s (η s), A.continuous.clm_apply η.continuous⟩ : C(unitInterval, F)))
    (fun A₁ A₂ η => by ext s; simp)
    (fun c A η => by ext s; simp)
    (fun A η₁ η₂ => by ext s; simp)
    (fun c A η => by ext s; simp)

theorem norm_pmulₗ_le (A : C(unitInterval, E →L[ℝ] F)) (η : C(unitInterval, E)) :
    ‖pmulₗ A η‖ ≤ ‖A‖ * ‖η‖ := by
  refine (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg η))).2 fun s => ?_
  exact ((A s).le_opNorm (η s)).trans (mul_le_mul (A.norm_coe_le_norm s)
    (η.norm_coe_le_norm s) (norm_nonneg _) (norm_nonneg _))

/-- Pointwise application of a continuous curve of operators to a continuous curve:
`pmul A η = (s ↦ A(s)(η(s)))`, a continuous bilinear map with norm at most one. -/
def pmul : C(unitInterval, E →L[ℝ] F) →L[ℝ] C(unitInterval, E) →L[ℝ] C(unitInterval, F) :=
  @LinearMap.mkContinuous₂ ℝ ℝ ℝ C(unitInterval, E →L[ℝ] F) C(unitInterval, E) C(unitInterval, F)
    _ _ _ _ _ _ _ _ _ (RingHom.id ℝ) (RingHom.id ℝ) _ pmulₗ 1 fun A η => by
      rw [one_mul]; exact norm_pmulₗ_le A η

@[simp]
theorem pmul_apply (A : C(unitInterval, E →L[ℝ] F)) (η : C(unitInterval, E)) (s : unitInterval) :
    pmul A η s = A s (η s) :=
  rfl

theorem norm_pmul_le (A : C(unitInterval, E →L[ℝ] F)) : ‖pmul A‖ ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun η => norm_pmulₗ_le A η

theorem contDiff_pmul {n : WithTop ℕ∞} : ContDiff ℝ n (pmul (E := E) (F := F)) := by
  exact ContinuousLinearMap.contDiff _

/-- The derivative of `Y`, as a continuous map, when `Y` is `C¹`. -/
def dmap {Y : E → F} (hY : ContDiff ℝ 1 Y) : C(E, E →L[ℝ] F) :=
  ⟨fderiv ℝ Y, hY.continuous_fderiv one_ne_zero⟩

@[simp]
theorem dmap_apply {Y : E → F} (hY : ContDiff ℝ 1 Y) (x : E) : dmap hY x = fderiv ℝ Y x :=
  rfl

/-- **The derivative of the Nemytskii operator.** If `Y` is `C¹`, then `γ ↦ Y ∘ γ` has derivative
`η ↦ (s ↦ dY_{γ(s)}(η(s)))` at `γ`. -/
theorem hasFDerivAt_nem {Y : E → F} (hY : ContDiff ℝ 1 Y) (γ : C(unitInterval, E)) :
    HasFDerivAt (nem ⟨Y, hY.continuous⟩) (pmul (nem (dmap hY) γ)) γ := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  -- `dY` is uniformly continuous near the compact set `γ([0, 1])`
  have hU := (isCompact_range γ.continuous).uniformContinuousAt_of_continuousAt (fderiv ℝ Y)
    (fun a _ => (hY.continuous_fderiv one_ne_zero).continuousAt) (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_uniformity_dist.1 hU
  filter_upwards [Metric.ball_mem_nhds (0 : C(unitInterval, E)) hδ] with η hη
  rw [mem_ball_zero_iff] at hη
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun s => ?_
  simp only [ContinuousMap.sub_apply, nem_apply, ContinuousMap.add_apply, pmul_apply,
    dmap_apply, ContinuousMap.coe_mk]
  have hb : ∀ z ∈ ball (γ s) δ, ‖fderiv ℝ Y z - fderiv ℝ Y (γ s)‖ ≤ ε := fun z hz => by
    have h := hδU (a := γ s) (b := z) (by rw [dist_comm]; exact hz) ⟨s, rfl⟩
    rw [Set.mem_ofPred_eq, dist_eq_norm, norm_sub_rev] at h
    exact h.le
  have hmem : γ s + η s ∈ ball (γ s) δ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (η.norm_coe_le_norm s).trans_lt hη
  have := (convex_ball (γ s) δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := Y) (f' := fderiv ℝ Y) (φ := fderiv ℝ Y (γ s))
    (fun z _ => (hY.differentiable one_ne_zero z).hasFDerivAt.hasFDerivWithinAt) hb
    (mem_ball_self hδ) hmem
  rw [add_sub_cancel_left] at this
  exact this.trans (mul_le_mul_of_nonneg_left (η.norm_coe_le_norm s) hε.le)

/-- The operator norm of the derivative of `N_Y` is at most `sup ‖dY‖`. -/
theorem norm_pmul_nem_dmap_le {Y : E → F} (hY : ContDiff ℝ 1 Y) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖fderiv ℝ Y x‖ ≤ C) (γ : C(unitInterval, E)) :
    ‖pmul (nem (dmap hY) γ)‖ ≤ C :=
  (norm_pmul_le _).trans (norm_nem_le hC0 hC γ)

end Defs

/-- **The Nemytskii operator of a `Cⁿ` map is `Cⁿ`** (finite `n`). The induction is over all
target spaces `F` in the universe of `E`, since the derivative `dY` takes values in
`E →L[ℝ] F`. -/
theorem contDiff_nem_nat {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] (Y : C(E, F)),
      ContDiff ℝ n Y → ContDiff ℝ n (nem Y) := by
  induction n with
  | zero =>
    intro F _ _ Y _
    exact contDiff_zero.2 (continuous_nem Y)
  | succ n ih =>
    intro F _ _ Y hY
    have hY1 : ContDiff ℝ 1 Y := hY.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hDY : ContDiff ℝ n (dmap hY1) := hY.fderiv_right (by push_cast; exact le_rfl)
    have hY' : (⟨Y, hY1.continuous⟩ : C(E, F)) = Y := rfl
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_hasFDerivAt.2
      ⟨pmul ∘ nem (dmap hY1), contDiff_pmul.comp (ih _ hDY), fun γ => ?_⟩
    have := hasFDerivAt_nem hY1 γ
    rwa [hY'] at this

/-- **The Nemytskii operator of a `Cⁿ` map is `Cⁿ`**, for `n ∈ ℕ ∪ {∞}`. -/
theorem contDiff_nem {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞} {Y : C(E, F)}
    (hY : ContDiff ℝ n Y) : ContDiff ℝ n (nem Y) := by
  induction n using ENat.recTopCoe with
  | top => exact contDiff_infty.2 fun m => contDiff_nem_nat m Y (contDiff_infty.1 hY m)
  | coe m => exact contDiff_nem_nat m Y hY

end Morse.Flow
