import Morse.Flow.Nemytskii

/-!
Milnor, *Morse Theory*, §2, p. 10 (infrastructure for the smooth dependence of solutions of
ordinary differential equations on the initial point).

# The integral equation `γ − P(X ∘ γ) = ψ` on `C([0, 1], E)`

A curve `γ : [0, 1] → E` is a solution of `γ' = X(γ)`, `γ(0) = x`, if and only if
`γ(s) = x + ∫₀ˢ X(γ(r)) dr`, that is `Ψ(γ) = x` (the constant curve) for

  `Ψ(γ) = γ − P(X ∘ γ)`,   `(P γ)(s) = ∫₀ˢ γ(r) dr`.

This file studies `Ψ` as a map of the Banach space `C([0, 1], E)` to itself, for a field `X`
which is **Lipschitz with constant `c < 1`**:

* `P` is a continuous linear operator of norm at most one (`Morse.Flow.prim`), so
  `γ ↦ P(X ∘ γ)` is `c`-Lipschitz;
* hence `Ψ` is a bijection (injective by the estimate `‖γ − δ‖ ≤ (1 − c)⁻¹ ‖Ψγ − Ψδ‖`,
  surjective by the contraction principle applied to `γ ↦ ψ + P(X ∘ γ)`) with Lipschitz inverse:
  a homeomorphism `Morse.Flow.voltHomeomorph`;
* `Ψ` is as smooth as `X` (`Morse.Flow.contDiff_nem`), with derivative `1 − P ∘ N_{dX}(γ)`; the
  second term has norm at most `sup ‖dX‖ ≤ c < 1`, so the derivative is invertible (Neumann
  series, Mathlib's `Units.oneSub`);
* therefore `Ψ⁻¹` is as smooth as `X` (`Morse.Flow.contDiff_voltHomeomorph_symm`, by Mathlib's
  `Homeomorph.contDiff_symm`, the "easy half" of the inverse function theorem).

The restriction `c < 1` makes the operator `P ∘ N_{dX}(γ)` a contraction, so that no estimate of
its iterates (`‖Kⁿ‖ ≤ cⁿ/n!`) is needed. It costs nothing: the flow of `X` at time `t` is the
time-one map of `t X`, and `φ_t = (φ_{t/N})^N` (`Morse/Flow/Smooth.lean`).
-/

open Set Filter Topology Metric
open scoped ContDiff NNReal

noncomputable section

namespace Morse.Flow

universe u

section Prim

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The curve `s ↦ ∫₀ˢ γ(r) dr` (with `γ` extended to `ℝ` by `γ(r) = γ(proj_{[0,1]} r)`). -/
def primFun (γ : C(unitInterval, E)) : C(unitInterval, E) where
  toFun s := ∫ r in (0 : ℝ)..(s : ℝ), γ (projIcc 0 1 zero_le_one r)
  continuous_toFun := (intervalIntegral.continuous_primitive
    (fun a b => (γ.continuous.comp continuous_projIcc).intervalIntegrable a b) 0).comp
    continuous_subtype_val

theorem primFun_apply (γ : C(unitInterval, E)) (s : unitInterval) :
    primFun γ s = ∫ r in (0 : ℝ)..(s : ℝ), γ (projIcc 0 1 zero_le_one r) :=
  rfl

theorem norm_primFun_le (γ : C(unitInterval, E)) : ‖primFun γ‖ ≤ ‖γ‖ := by
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun s => ?_
  rw [primFun_apply]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (s : ℝ))
    (C := ‖γ‖) (f := fun r => γ (projIcc 0 1 zero_le_one r)) (fun r _ => γ.norm_coe_le_norm _)
  calc _ ≤ ‖γ‖ * |(s : ℝ) - 0| := h
    _ ≤ ‖γ‖ * 1 := by
        gcongr
        rw [sub_zero, abs_of_nonneg s.2.1]
        exact s.2.2
    _ = ‖γ‖ := mul_one _

/-- The primitive as a linear map. -/
def primₗ : C(unitInterval, E) →ₗ[ℝ] C(unitInterval, E) where
  toFun := primFun
  map_add' γ δ := by
    ext s
    simp only [primFun_apply, ContinuousMap.add_apply]
    exact intervalIntegral.integral_add
      ((γ.continuous.comp continuous_projIcc).intervalIntegrable _ _)
      ((δ.continuous.comp continuous_projIcc).intervalIntegrable _ _)
  map_smul' c γ := by
    ext s
    simp only [primFun_apply, ContinuousMap.smul_apply, RingHom.id_apply]
    exact intervalIntegral.integral_smul c _

/-- **The primitive operator** `P γ = (s ↦ ∫₀ˢ γ)`, of norm at most one. -/
def prim : C(unitInterval, E) →L[ℝ] C(unitInterval, E) :=
  @LinearMap.mkContinuous ℝ ℝ C(unitInterval, E) C(unitInterval, E) _ _ _ _ _ _
    (RingHom.id ℝ) primₗ 1 fun γ => by rw [one_mul]; exact norm_primFun_le γ

theorem prim_apply (γ : C(unitInterval, E)) (s : unitInterval) :
    prim γ s = ∫ r in (0 : ℝ)..(s : ℝ), γ (projIcc 0 1 zero_le_one r) :=
  rfl

theorem norm_prim_le : ‖(prim : C(unitInterval, E) →L[ℝ] C(unitInterval, E))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun γ => by
    rw [one_mul]; exact norm_primFun_le γ

theorem norm_prim_apply_le (γ : C(unitInterval, E)) : ‖prim γ‖ ≤ ‖γ‖ :=
  norm_primFun_le γ

theorem contDiff_prim {n : WithTop ℕ∞} :
    ContDiff ℝ n (prim : C(unitInterval, E) →L[ℝ] C(unitInterval, E)) := by
  exact ContinuousLinearMap.contDiff _

end Prim

section Volt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The map `Ψ_Y γ = γ − P(Y ∘ γ)`, whose zeros-with-right-hand-side `x` are the solutions of
`γ' = Y(γ)`, `γ(0) = x`. -/
def volt (Y : C(E, E)) (γ : C(unitInterval, E)) : C(unitInterval, E) :=
  γ - prim (nem Y γ)

theorem volt_apply (Y : C(E, E)) (γ : C(unitInterval, E)) :
    volt Y γ = γ - prim (nem Y γ) :=
  rfl

theorem dist_prim_nem_le {Y : C(E, E)} {c : ℝ≥0} (hY : LipschitzWith c Y)
    (γ δ : C(unitInterval, E)) : dist (prim (nem Y γ)) (prim (nem Y δ)) ≤ c * dist γ δ := by
  rw [dist_eq_norm, ← map_sub]
  refine (norm_prim_apply_le _).trans ?_
  rw [← dist_eq_norm]
  exact (lipschitzWith_nem hY).dist_le_mul γ δ

/-- The key estimate: `‖γ − δ‖ ≤ (1 − c)⁻¹ ‖Ψγ − Ψδ‖`. -/
theorem dist_le_dist_volt {Y : C(E, E)} {c : ℝ≥0} (hY : LipschitzWith c Y) (hc : c < 1)
    (γ δ : C(unitInterval, E)) : dist γ δ ≤ (1 - (c : ℝ))⁻¹ * dist (volt Y γ) (volt Y δ) := by
  have hc' : (0 : ℝ) < 1 - c := sub_pos.2 (by exact_mod_cast hc)
  rw [le_inv_mul_iff₀ hc']
  have h1 : dist γ δ ≤ dist (volt Y γ) (volt Y δ) + dist (prim (nem Y γ)) (prim (nem Y δ)) := by
    have : γ - δ = (volt Y γ - volt Y δ) + (prim (nem Y γ) - prim (nem Y δ)) := by
      simp only [volt_apply]; abel
    rw [dist_eq_norm, this, dist_eq_norm, dist_eq_norm]
    exact norm_add_le _ _
  have h2 := dist_prim_nem_le hY γ δ
  nlinarith

theorem volt_injective {Y : C(E, E)} {c : ℝ≥0} (hY : LipschitzWith c Y) (hc : c < 1) :
    Function.Injective (volt Y) := fun γ δ h => by
  have := dist_le_dist_volt hY hc γ δ
  rw [h, dist_self, mul_zero] at this
  exact dist_le_zero.1 this

variable [CompleteSpace E]

omit [CompleteSpace E] in
/-- For fixed `ψ`, the map `γ ↦ ψ + P(Y ∘ γ)` is a contraction. -/
theorem contractingWith_volt {Y : C(E, E)} {c : ℝ≥0} (hY : LipschitzWith c Y) (hc : c < 1)
    (ψ : C(unitInterval, E)) : ContractingWith c (fun γ => ψ + prim (nem Y γ)) :=
  ⟨hc, LipschitzWith.of_dist_le_mul fun γ δ => by
    rw [dist_add_left]; exact dist_prim_nem_le hY γ δ⟩

/-- The inverse of `Ψ`: the fixed point of `γ ↦ ψ + P(Y ∘ γ)`. -/
def voltInv {Y : C(E, E)} {c : ℝ≥0} (hY : LipschitzWith c Y) (hc : c < 1)
    (ψ : C(unitInterval, E)) : C(unitInterval, E) :=
  ContractingWith.fixedPoint _ (contractingWith_volt hY hc ψ)

theorem volt_voltInv {Y : C(E, E)} {c : ℝ≥0} (hY : LipschitzWith c Y) (hc : c < 1)
    (ψ : C(unitInterval, E)) : volt Y (voltInv hY hc ψ) = ψ := by
  have h : ψ + prim (nem Y (voltInv hY hc ψ)) = voltInv hY hc ψ :=
    ContractingWith.fixedPoint_isFixedPt (contractingWith_volt hY hc ψ)
  rw [volt_apply]
  nth_rw 1 [← h]
  abel

theorem voltInv_volt {Y : C(E, E)} {c : ℝ≥0} (hY : LipschitzWith c Y) (hc : c < 1)
    (γ : C(unitInterval, E)) : voltInv hY hc (volt Y γ) = γ :=
  volt_injective hY hc (volt_voltInv hY hc _)

/-- `Ψ` is a homeomorphism of `C([0, 1], E)` when `Y` is `c`-Lipschitz with `c < 1`. -/
def voltHomeomorph {Y : C(E, E)} {c : ℝ≥0} (hY : LipschitzWith c Y) (hc : c < 1) :
    C(unitInterval, E) ≃ₜ C(unitInterval, E) where
  toFun := volt Y
  invFun := voltInv hY hc
  left_inv := voltInv_volt hY hc
  right_inv := volt_voltInv hY hc
  continuous_toFun := continuous_id.sub (prim.continuous.comp (continuous_nem Y))
  continuous_invFun := by
    have hc' : (0 : ℝ) < 1 - c := sub_pos.2 (by exact_mod_cast hc)
    refine (LipschitzWith.of_dist_le_mul (K := ⟨(1 - c)⁻¹, (inv_pos.2 hc').le⟩)
      fun ψ₁ ψ₂ => ?_).continuous
    have := dist_le_dist_volt hY hc (voltInv hY hc ψ₁) (voltInv hY hc ψ₂)
    rw [volt_voltInv, volt_voltInv] at this
    exact this

@[simp]
theorem coe_voltHomeomorph {Y : C(E, E)} {c : ℝ≥0} (hY : LipschitzWith c Y) (hc : c < 1) :
    ⇑(voltHomeomorph hY hc) = volt Y :=
  rfl

end Volt

section Smooth

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_volt {n : ℕ∞} {X : E → E} (hX : ContDiff ℝ n X) :
    ContDiff ℝ n (volt ⟨X, hX.continuous⟩) :=
  contDiff_id.sub (contDiff_prim.comp (contDiff_nem (Y := ⟨X, hX.continuous⟩) hX))

/-- The derivative of `Ψ` at `γ` is `1 − P ∘ N_{dX}(γ)`. -/
theorem hasFDerivAt_volt {X : E → E} (hX : ContDiff ℝ 1 X) (γ : C(unitInterval, E)) :
    HasFDerivAt (volt ⟨X, hX.continuous⟩) (1 - prim.comp (pmul (nem (dmap hX) γ))) γ := by
  have h2 : HasFDerivAt (prim : C(unitInterval, E) →L[ℝ] C(unitInterval, E))
      (prim : C(unitInterval, E) →L[ℝ] C(unitInterval, E)) (nem ⟨X, hX.continuous⟩ γ) := by
    exact ContinuousLinearMap.hasFDerivAt _
  exact (hasFDerivAt_id γ).sub (h2.comp γ (hasFDerivAt_nem hX γ))

theorem norm_prim_comp_pmul_lt {X : E → E} (hX : ContDiff ℝ 1 X) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c < 1) (hC : ∀ x, ‖fderiv ℝ X x‖ ≤ c) (γ : C(unitInterval, E)) :
    ‖prim.comp (pmul (nem (dmap hX) γ))‖ < 1 :=
  calc ‖prim.comp (pmul (nem (dmap hX) γ))‖
      ≤ ‖(prim : C(unitInterval, E) →L[ℝ] C(unitInterval, E))‖ * ‖pmul (nem (dmap hX) γ)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * c := mul_le_mul norm_prim_le (norm_pmul_nem_dmap_le hX hc0 hC γ)
        (norm_nonneg (pmul (nem (dmap hX) γ))) zero_le_one
    _ < 1 := by rwa [one_mul]

variable [CompleteSpace E]

/-- The derivative of `Ψ`, as a continuous linear equivalence (Neumann series). -/
def voltDeriv {X : E → E} (hX : ContDiff ℝ 1 X) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1)
    (hC : ∀ x, ‖fderiv ℝ X x‖ ≤ c) (γ : C(unitInterval, E)) :
    C(unitInterval, E) ≃L[ℝ] C(unitInterval, E) :=
  ContinuousLinearEquiv.ofUnit
    (Units.oneSub (prim.comp (pmul (nem (dmap hX) γ))) (norm_prim_comp_pmul_lt hX hc0 hc hC γ))

theorem coe_voltDeriv {X : E → E} (hX : ContDiff ℝ 1 X) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1)
    (hC : ∀ x, ‖fderiv ℝ X x‖ ≤ c) (γ : C(unitInterval, E)) :
    (voltDeriv hX hc0 hc hC γ : C(unitInterval, E) →L[ℝ] C(unitInterval, E)) =
      1 - prim.comp (pmul (nem (dmap hX) γ)) :=
  rfl

/-- **`Ψ⁻¹` is as smooth as `X`**, when `X` is `Cⁿ` (`n ≥ 1`) and `c`-Lipschitz with `c < 1`. -/
theorem contDiff_voltHomeomorph_symm {n : ℕ∞} {X : E → E} (hX : ContDiff ℝ n X) (hn : 1 ≤ n)
    {c : ℝ≥0} (hc : c < 1) (hL : LipschitzWith c X) :
    ContDiff ℝ n (voltHomeomorph (Y := ⟨X, hX.continuous⟩) hL hc).symm := by
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by exact_mod_cast hn)
  have hC : ∀ x, ‖fderiv ℝ X x‖ ≤ c := fun x => norm_fderiv_le_of_lipschitz ℝ hL
  exact Homeomorph.contDiff_symm _
    (f₀' := voltDeriv hX1 (NNReal.coe_nonneg c) (by exact_mod_cast hc) hC)
    (fun γ => hasFDerivAt_volt hX1 γ) (contDiff_volt hX)

end Smooth

end Morse.Flow
