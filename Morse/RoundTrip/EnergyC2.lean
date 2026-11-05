import Morse

/-!
# Parametric interval integrals of `C^n` functions are `C^n`; the energy of a variation is `C^∞`

Milnor's Hessian `E_**` (§13) is the mixed partial `∂²E(ᾱ(u₁, u₂))/∂u₁∂u₂ (0, 0)` of a
2-parameter variation `ᾱ`.  The project computes it as an *iterated* one-variable derivative
(`Morse.second_variation`, `Morse.hasDerivAt_energyHessian`); the blind statements of the audit
read it as a *Fréchet* second derivative of `u ↦ E(ᾱ(u))` on `ℝ²` (`mixedD` in
`RoundTrip/Blind/V8_13.lean` etc.).  The two agree once `u ↦ E(ᾱ(u))` is known to be `C²`, which
is what this file proves, in three steps.

1. **Generic** (`contDiffOn_integral`, `contDiffOn_integral_infty`, `hasFDerivAt_integral`,
   `fderiv_integral`): for `H` finite dimensional, `E` a real Banach space, `U ⊆ H` open and
   `f : H → ℝ → E` with `(x, t) ↦ f x t` of class `C^n` on the closed strip `U ×ˢ Icc a b`
   (Mathlib's `ContDiffOn` on that set, exactly the hypothesis in `Morse.IsVariation.smooth`),
   `x ↦ ∫ t in a..b, f x t` is `C^n` on `U`, with derivative `∫ t in a..b, ∂f/∂x`.
2. **Energy** (`IsVariation.contDiffOn_energy`, `IsVariation.contDiffOn_energy_Icc`): for a
   variation `α` in the project's sense with parameters in an open set of a finite-dimensional
   space, `u ↦ E_a^b(α u)` is `C^∞` on `U` (`0 ≤ a ≤ b ≤ 1`).
3. **Dictionary** (`deriv_deriv_eq_fderiv_fderiv`, `fderiv_fderiv_energy_eq_energyHessian`,
   `fderiv_fderiv_energy_eq_energyHessian'`, `fderiv_fderiv_apply_energy_eq_energyHessian`):
   iterated directional derivatives of a `C²` function are its Fréchet second derivative, in
   either order, so for a 2-parameter variation of a geodesic every reading of
   `∂²E/∂u₁∂u₂ (0, 0)` (iterated, Fréchet in either order, `mixedD`-style) equals the project's
   `Morse.energyHessian`.

Usage in the audit items (V8_13, V8_14, V9_5, V9_15, V9_18–V9_22).  Transport the blind variation
`α : Rn 2 → ℝ → M` to a project variation `α' : P → ℝ → V` (`P = Rn 2` directly, or `ℝ × ℝ`
through `Morse.IsVariation.comp` with a linear isomorphism): the blind `IsVarSub` strips
`U ×ˢ Icc (t i) (t (i+1))` are exactly the closed strips of `Morse.IsVariation.smooth`.  Then
`hα.contDiffOn_energy` gives `C^∞` of `u ↦ E(α' u)`; `fderiv_fderiv_apply_eq_deriv_deriv` (or
`fderiv_fderiv_apply` + `fderiv_fderiv_symm` + `deriv_deriv_eq_fderiv_fderiv`) turns the blind
`mixedD` (`fderiv ℝ (fun u => fderiv ℝ F u e₀) 0 e₁`) into an iterated derivative along two
directions, which is the quantity computed by `Morse.second_variation` (for `P = ℝ × ℝ`,
`fderiv_fderiv_apply_energy_eq_energyHessian` does the whole chain, including the
`DifferentiableAt` clause of the blind `IsHess`).  For `E_0^τ` (`IsHessT`), use
`contDiffOn_energy_Icc`.
-/

namespace RoundTrip.EnergyC2

set_option linter.unusedSectionVars false

open Set Filter Topology Function MeasureTheory Metric intervalIntegral
open scoped ContDiff Interval

noncomputable section

universe u v

/-! ### 1. Parametric interval integrals -/

section Generic

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {U : Set H} {a b : ℝ}

/-- The partial derivative in the parameter `x` of `f : H → ℝ → E`, computed within the closed
strip `U ×ˢ Icc a b`.  For `U` open it is the ordinary derivative of `x ↦ f x t`
(`hasFDerivAt_pderiv`). -/
def pderiv (U : Set H) (a b : ℝ) (f : H → ℝ → E) (x : H) (t : ℝ) : H →L[ℝ] E :=
  (fderivWithin ℝ (fun p : H × ℝ => f p.1 p.2) (U ×ˢ Icc a b) (x, t)).comp
    (ContinuousLinearMap.inl ℝ H ℝ)

theorem uniqueDiffOn_strip (hU : IsOpen U) (hab : a < b) : UniqueDiffOn ℝ (U ×ˢ Icc a b) :=
  hU.uniqueDiffOn.prod (uniqueDiffOn_Icc hab)

theorem continuousOn_param_right {g : H × ℝ → E} (hg : ContinuousOn g (U ×ˢ Icc a b)) {x : H}
    (hx : x ∈ U) : ContinuousOn (fun t => g (x, t)) (Icc a b) :=
  hg.comp (continuousOn_const.prodMk continuousOn_id) fun _ ht => mk_mem_prod hx ht

theorem continuousOn_param_left {g : H × ℝ → E} (hg : ContinuousOn g (U ×ˢ Icc a b)) {t : ℝ}
    (ht : t ∈ Icc a b) : ContinuousOn (fun x => g (x, t)) U :=
  hg.comp (continuousOn_id.prodMk continuousOn_const) fun _ hx => mk_mem_prod hx ht

theorem aestronglyMeasurable_of_continuousOn_Icc {g : ℝ → E} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) : AEStronglyMeasurable g (volume.restrict (Ι a b)) := by
  rw [uIoc_of_le hab]
  exact (hg.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc

/-- `∂f/∂x` is the derivative of `x ↦ f x t` (the `x`-direction is open). -/
theorem hasFDerivAt_pderiv (hU : IsOpen U) {f : H → ℝ → E}
    (hf : DifferentiableOn ℝ (fun p : H × ℝ => f p.1 p.2) (U ×ˢ Icc a b)) {x : H} {t : ℝ}
    (hx : x ∈ U) (ht : t ∈ Icc a b) : HasFDerivAt (fun x => f x t) (pderiv U a b f x t) x := by
  have h1 : HasFDerivWithinAt (fun p : H × ℝ => f p.1 p.2)
      (fderivWithin ℝ (fun p : H × ℝ => f p.1 p.2) (U ×ˢ Icc a b) (x, t)) (U ×ˢ Icc a b) (x, t) :=
    (hf (x, t) (mk_mem_prod hx ht)).hasFDerivWithinAt
  have h2 := h1.comp x (hasFDerivAt_prodMk_left x t).hasFDerivWithinAt
    fun y hy => mk_mem_prod hy ht
  exact h2.hasFDerivAt (hU.mem_nhds hx)

theorem pderiv_eq_fderiv (hU : IsOpen U) {f : H → ℝ → E}
    (hf : DifferentiableOn ℝ (fun p : H × ℝ => f p.1 p.2) (U ×ˢ Icc a b)) {x : H} {t : ℝ}
    (hx : x ∈ U) (ht : t ∈ Icc a b) : pderiv U a b f x t = fderiv ℝ (fun x => f x t) x :=
  (hasFDerivAt_pderiv hU hf hx ht).fderiv.symm

/-- `∂f/∂x` of a `C^{n+1}` function is jointly `C^n` on the closed strip. -/
theorem contDiffOn_pderiv (hU : IsOpen U) (hab : a < b) {n : ℕ∞ω} {f : H → ℝ → E}
    (hf : ContDiffOn ℝ (n + 1) (fun p : H × ℝ => f p.1 p.2) (U ×ˢ Icc a b)) :
    ContDiffOn ℝ n (fun p : H × ℝ => pderiv U a b f p.1 p.2) (U ×ˢ Icc a b) :=
  (hf.fderivWithin (uniqueDiffOn_strip hU hab) le_rfl).clm_comp contDiffOn_const

/-- **Continuity of a parametric integral** of a function continuous on the closed strip. -/
theorem continuousOn_integral (hU : IsOpen U) (hab : a ≤ b) {f : H → ℝ → E}
    (hf : ContinuousOn (fun p : H × ℝ => f p.1 p.2) (U ×ˢ Icc a b)) :
    ContinuousOn (fun x => ∫ t in a..b, f x t) U := by
  intro x₀ hx₀
  obtain ⟨ε, hε, hball⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx₀)
  have hK : IsCompact (closedBall x₀ ε ×ˢ Icc a b) :=
    (isCompact_closedBall x₀ ε).prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hf.mono (prod_mono hball subset_rfl))
  refine (continuousAt_of_dominated_interval (bound := fun _ => M) ?_ ?_ ?_ ?_).continuousWithinAt
  · filter_upwards [hU.mem_nhds hx₀] with x hx
    exact aestronglyMeasurable_of_continuousOn_Icc hab (continuousOn_param_right hf hx)
  · filter_upwards [closedBall_mem_nhds x₀ hε] with x hx
    refine ae_of_all _ fun t ht => hM (x, t) (mk_mem_prod hx ?_)
    rw [uIoc_of_le hab] at ht
    exact Ioc_subset_Icc_self ht
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun t ht => ?_
    rw [uIoc_of_le hab] at ht
    exact (continuousOn_param_left hf (Ioc_subset_Icc_self ht)).continuousAt (hU.mem_nhds hx₀)

/-- **Differentiation under the integral sign** for a function `C¹` on the closed strip. -/
theorem hasFDerivAt_integral (hU : IsOpen U) (hab : a < b) {f : H → ℝ → E}
    (hf : ContDiffOn ℝ 1 (fun p : H × ℝ => f p.1 p.2) (U ×ˢ Icc a b)) {x₀ : H} (hx₀ : x₀ ∈ U) :
    HasFDerivAt (fun x => ∫ t in a..b, f x t) (∫ t in a..b, pderiv U a b f x₀ t) x₀ := by
  obtain ⟨ε, hε, hball⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx₀)
  have hf' : ContinuousOn (fun p : H × ℝ => pderiv U a b f p.1 p.2) (U ×ˢ Icc a b) :=
    (contDiffOn_pderiv hU hab (n := 0) (by rwa [zero_add])).continuousOn
  have hK : IsCompact (closedBall x₀ ε ×ˢ Icc a b) :=
    (isCompact_closedBall x₀ ε).prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hf'.mono (prod_mono hball subset_rfl))
  have hd : DifferentiableOn ℝ (fun p : H × ℝ => f p.1 p.2) (U ×ˢ Icc a b) :=
    hf.differentiableOn one_ne_zero
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := closedBall x₀ ε)
    (bound := fun _ => M) (closedBall_mem_nhds x₀ hε) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [hU.mem_nhds hx₀] with x hx
    exact aestronglyMeasurable_of_continuousOn_Icc hab.le
      (continuousOn_param_right hf.continuousOn hx)
  · exact (continuousOn_param_right hf.continuousOn hx₀).intervalIntegrable_of_Icc hab.le
  · exact aestronglyMeasurable_of_continuousOn_Icc hab.le (continuousOn_param_right hf' hx₀)
  · refine ae_of_all _ fun t ht x hx => hM (x, t) (mk_mem_prod hx ?_)
    rw [uIoc_of_le hab.le] at ht
    exact Ioc_subset_Icc_self ht
  · refine ae_of_all _ fun t ht x hx => hasFDerivAt_pderiv hU hd (hball hx) ?_
    rw [uIoc_of_le hab.le] at ht
    exact Ioc_subset_Icc_self ht

/-- Auxiliary form of `contDiffOn_integral`, with the values in `Type (max u v)` so that the
induction on `n` can pass from `E` to `H →L[ℝ] E`. -/
theorem contDiffOn_integral_aux (hU : IsOpen U) (hab : a < b) (n : ℕ) :
    ∀ (E : Type (max u v)) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (f : H → ℝ → E), ContDiffOn ℝ n (fun p : H × ℝ => f p.1 p.2) (U ×ˢ Icc a b) →
      ContDiffOn ℝ n (fun x => ∫ t in a..b, f x t) U := by
  induction n with
  | zero =>
    intro E _ _ _ f hf
    rw [Nat.cast_zero, contDiffOn_zero] at hf ⊢
    exact continuousOn_integral hU hab.le hf
  | succ n ih =>
    intro E _ _ _ f hf
    rw [Nat.cast_succ] at hf ⊢
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hasFDerivAt_integral hU hab hf.one_of_succ
      hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine (ih (H →L[ℝ] E) (pderiv U a b f) (contDiffOn_pderiv hU hab hf)).congr fun x hx => ?_
    exact (hasFDerivAt_integral hU hab hf.one_of_succ hx).fderiv

/-- **A parametric interval integral of a `C^n` function is `C^n`**: for `U ⊆ H` open (`H`
finite dimensional), `a ≤ b`, and `(x, t) ↦ f x t` of class `C^n` on the closed strip
`U ×ˢ Icc a b`, `x ↦ ∫ t in a..b, f x t` is `C^n` on `U`. -/
theorem contDiffOn_integral (hU : IsOpen U) (hab : a ≤ b) {n : ℕ} {f : H → ℝ → E}
    (hf : ContDiffOn ℝ n (fun p : H × ℝ => f p.1 p.2) (U ×ˢ Icc a b)) :
    ContDiffOn ℝ n (fun x => ∫ t in a..b, f x t) U := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp only [integral_same]
    exact contDiffOn_const
  cases n with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero] at hf ⊢
    exact continuousOn_integral hU hab.le hf
  | succ n =>
    rw [Nat.cast_succ] at hf ⊢
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hasFDerivAt_integral hU hab hf.one_of_succ
      hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine (contDiffOn_integral_aux hU hab n (H →L[ℝ] E) (pderiv U a b f)
      (contDiffOn_pderiv hU hab hf)).congr fun x hx => ?_
    exact (hasFDerivAt_integral hU hab hf.one_of_succ hx).fderiv

/-- The `C^∞` case of `contDiffOn_integral`. -/
theorem contDiffOn_integral_infty (hU : IsOpen U) (hab : a ≤ b) {f : H → ℝ → E}
    (hf : ContDiffOn ℝ ∞ (fun p : H × ℝ => f p.1 p.2) (U ×ˢ Icc a b)) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in a..b, f x t) U :=
  contDiffOn_infty.2 fun n => contDiffOn_integral hU hab (contDiffOn_infty.1 hf n)

/-- **Differentiation under the integral sign**, as a formula for `fderiv`. -/
theorem fderiv_integral (hU : IsOpen U) (hab : a < b) {f : H → ℝ → E}
    (hf : ContDiffOn ℝ 1 (fun p : H × ℝ => f p.1 p.2) (U ×ˢ Icc a b)) {x : H} (hx : x ∈ U) :
    fderiv ℝ (fun x => ∫ t in a..b, f x t) x = ∫ t in a..b, fderiv ℝ (fun x => f x t) x := by
  rw [(hasFDerivAt_integral hU hab hf hx).fderiv]
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le hab.le] at ht
  exact pderiv_eq_fderiv hU (hf.differentiableOn one_ne_zero) hx ht

end Generic

/-! ### 2. The energy of a variation is `C^∞` in the parameter -/

section Energy

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {U : Set P} {a b : ℝ}

/-- On a closed strip where `(u, t) ↦ α u t` is `C^∞`, `u ↦ ∫ₐᵇ ‖∂α/∂t‖²` is `C^∞`. -/
theorem contDiffOn_integral_norm_deriv_sq (hU : IsOpen U) (hab : a < b) {α : P → ℝ → V}
    (hα : ContDiffOn ℝ ∞ (fun p : P × ℝ => α p.1 p.2) (U ×ˢ Icc a b)) :
    ContDiffOn ℝ ∞ (fun u => ∫ t in a..b, ‖deriv (α u) t‖ ^ 2) U := by
  set S := U ×ˢ Icc a b with hS
  set F : P × ℝ → V := fun p => α p.1 p.2 with hF
  have hg : ContDiffOn ℝ ∞ (fun p : P × ℝ => ‖fderivWithin ℝ F S p (0, 1)‖ ^ 2) S :=
    ((hα.fderivWithin (uniqueDiffOn_strip hU hab) (m := ∞) (by simp)).clm_apply
      contDiffOn_const).norm_sq ℝ
  refine (contDiffOn_integral_infty hU hab.le
    (f := fun u t => ‖fderivWithin ℝ F S (u, t) (0, 1)‖ ^ 2) hg).congr fun u hu => ?_
  refine integral_congr_Ioo_of_le hab.le fun t ht => ?_
  have h1 : HasFDerivWithinAt F (fderivWithin ℝ F S (u, t)) S (u, t) :=
    ((hα.differentiableOn (by simp)) (u, t)
      (mk_mem_prod hu (Ioo_subset_Icc_self ht))).hasFDerivWithinAt
  have h2 := h1.comp t (hasFDerivAt_prodMk_right u t).hasFDerivWithinAt
    fun s hs => mk_mem_prod hu hs
  have h3 := ((h2.hasFDerivAt (Icc_mem_nhds ht.1 ht.2)).hasDerivAt).deriv
  simp only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply] at h3
  rw [← h3]

/-- **The energy `E_a^b` of a variation is `C^∞` in the parameter** (`0 ≤ a ≤ b ≤ 1`), for
parameters in an open set of a finite-dimensional space. -/
theorem _root_.Morse.IsVariation.contDiffOn_energy_Icc [FiniteDimensional ℝ V] {N : Set V}
    {α : P → ℝ → V} {B : Finset ℝ} (hα : Morse.IsVariation N U α B) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) : ContDiffOn ℝ ∞ (fun u => Morse.energy (α u) a b) U := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp only [Morse.energy, integral_same]
    exact contDiffOn_const
  refine Morse.piecewise_induction (B := B) (lo := 0) (hi := 1)
    (P := fun a b => ContDiffOn ℝ ∞ (fun u => Morse.energy (α u) a b) U) ?_ ?_ a b ha hab hb
  · intro s t hs hst ht hB
    exact contDiffOn_integral_norm_deriv_sq hα.isOpen hst (hα.smooth s t hs hst ht hB)
  · intro a x b ha hax hxb hb _ h₁ h₂
    refine (h₁.add h₂).congr fun u hu => ?_
    have hint := (hα.isPiecewiseSmooth hu).intervalIntegrable_norm_deriv_sq
    have hsub : ∀ c d, 0 ≤ c → c ≤ d → d ≤ 1 → [[c, d]] ⊆ [[(0 : ℝ), 1]] := fun c d hc hcd hd => by
      rw [uIcc_of_le hcd, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hc hd
    exact (integral_add_adjacent_intervals
      (hint.mono_set (hsub a x ha hax.le (hxb.le.trans hb)))
      (hint.mono_set (hsub x b (ha.trans hax.le) hxb.le hb))).symm

/-- **Milnor's `E(ᾱ(u))` is `C^∞` in `u`** for every variation `ᾱ` of the project
(`Morse.IsVariation`) with parameters in an open set of a finite-dimensional space. -/
theorem _root_.Morse.IsVariation.contDiffOn_energy [FiniteDimensional ℝ V] {N : Set V}
    {α : P → ℝ → V} {B : Finset ℝ} (hα : Morse.IsVariation N U α B) :
    ContDiffOn ℝ ∞ (fun u => Morse.energy (α u) 0 1) U :=
  hα.contDiffOn_energy_Icc le_rfl zero_le_one le_rfl

theorem _root_.Morse.IsVariation.contDiffAt_energy [FiniteDimensional ℝ V] {N : Set V}
    {α : P → ℝ → V} {B : Finset ℝ} (hα : Morse.IsVariation N U α B) :
    ContDiffAt ℝ ∞ (fun u => Morse.energy (α u) 0 1) 0 :=
  hα.contDiffOn_energy.contDiffAt (hα.isOpen.mem_nhds hα.zero_mem)

end Energy

/-! ### 3. Iterated partial derivatives versus the Fréchet second derivative -/

section Dictionary

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative along the line `r ↦ y + r • w` at `r = 0` is the directional derivative. -/
theorem hasDerivAt_line {F : H → E} {y : H} (hF : DifferentiableAt ℝ F y) (w : H) :
    HasDerivAt (fun r : ℝ => F (y + r • w)) (fderiv ℝ F y w) 0 := by
  have hl : HasDerivAt (fun r : ℝ => y + r • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add y
  have hF' : HasFDerivAt F (fderiv ℝ F y) ((fun r : ℝ => y + r • w) 0) := by
    simpa using hF.hasFDerivAt
  exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hF' hl

variable {F : H → ℝ} {U : Set H}

/-- **Iterated directional derivatives of a `C²` function are its second Fréchet derivative**:
`∂/∂s ∂/∂r F(x + s v + r w) (0, 0) = D²F(x)(v, w)` (Mathlib's `fderiv ℝ (fderiv ℝ F) x v w`;
the outer derivative is in the direction `v`, the inner one in the direction `w`). -/
theorem deriv_deriv_eq_fderiv_fderiv (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U) {x : H}
    (hx : x ∈ U) (v w : H) :
    deriv (fun s : ℝ => deriv (fun r : ℝ => F (x + s • v + r • w)) 0) 0 =
      fderiv ℝ (fderiv ℝ F) x v w := by
  have hG : ContDiffOn ℝ 1 (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by norm_num)
  have hFd : DifferentiableOn ℝ F U := hF.differentiableOn (by norm_num)
  have hGd : DifferentiableOn ℝ (fderiv ℝ F) U := hG.differentiableOn one_ne_zero
  have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), x + s • v ∈ U := by
    have hc : ContinuousAt (fun s : ℝ => x + s • v) 0 := by fun_prop
    exact hc.preimage_mem_nhds (by simpa using hU.mem_nhds hx)
  have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ F (x + s • v) w) (fderiv ℝ (fderiv ℝ F) x v w)
      0 := by
    have := (hasDerivAt_line (hGd.differentiableAt (hU.mem_nhds hx)) v).clm_apply
      (hasDerivAt_const (0 : ℝ) w)
    simpa using this
  refine (h1.congr_of_eventuallyEq ?_).deriv
  filter_upwards [hmem] with s hs
  exact (hasDerivAt_line (hFd.differentiableAt (hU.mem_nhds hs)) w).deriv

/-- Symmetry of the second derivative of a `C²` function (Mathlib's
`ContDiffAt.isSymmSndFDerivAt`). -/
theorem fderiv_fderiv_symm (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U) {x : H} (hx : x ∈ U)
    (v w : H) : fderiv ℝ (fderiv ℝ F) x v w = fderiv ℝ (fderiv ℝ F) x w v :=
  ((hF.contDiffAt (hU.mem_nhds hx)).isSymmSndFDerivAt (by simp)).eq v w

theorem differentiableAt_fderiv_apply (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U) {x : H}
    (hx : x ∈ U) (v : H) : DifferentiableAt ℝ (fun y => fderiv ℝ F y v) x :=
  ((hF.fderiv_of_isOpen hU (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableOn
    one_ne_zero).differentiableAt (hU.mem_nhds hx) |>.clm_apply (differentiableAt_const v)

/-- The derivative of `y ↦ DF(y) v` in the direction `w` is `D²F(x)(w, v)`. -/
theorem fderiv_fderiv_apply (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U) {x : H} (hx : x ∈ U)
    (v w : H) : fderiv ℝ (fun y => fderiv ℝ F y v) x w = fderiv ℝ (fderiv ℝ F) x w v := by
  have hGd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hF.fderiv_of_isOpen hU (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableOn
      one_ne_zero).differentiableAt (hU.mem_nhds hx)
  rw [fderiv_clm_apply hGd (differentiableAt_const v)]
  simp

/-- The blind `mixedD`-style reading `D(y ↦ DF(y) v)(x) w` of `∂²F/∂v∂w` equals the iterated
derivative `∂/∂s ∂/∂r F(x + s v + r w)`, outer in `v`, inner in `w` (by symmetry). -/
theorem fderiv_fderiv_apply_eq_deriv_deriv (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U) {x : H}
    (hx : x ∈ U) (v w : H) :
    fderiv ℝ (fun y => fderiv ℝ F y v) x w =
      deriv (fun s : ℝ => deriv (fun r : ℝ => F (x + s • v + r • w)) 0) 0 := by
  rw [fderiv_fderiv_apply hU hF hx, fderiv_fderiv_symm hU hF hx,
    deriv_deriv_eq_fderiv_fderiv hU hF hx]

/-- The project's iterated derivative `∂/∂u₁ ∂/∂u₂ F(u₁, u₂)` at `(0, 0)` on `ℝ × ℝ` is
`D²F(0)((1, 0), (0, 1))`. -/
theorem deriv_deriv_eq_fderiv_fderiv_prod {U : Set (ℝ × ℝ)} (hU : IsOpen U) {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 2 F U) (h0 : (0 : ℝ × ℝ) ∈ U) :
    deriv (fun u₁ => deriv (fun u₂ => F (u₁, u₂)) 0) 0 =
      fderiv ℝ (fderiv ℝ F) 0 (1, 0) (0, 1) := by
  have key : ∀ u₁ u₂ : ℝ,
      (0 : ℝ × ℝ) + u₁ • ((1 : ℝ), (0 : ℝ)) + u₂ • ((0 : ℝ), (1 : ℝ)) = (u₁, u₂) := by
    intro u₁ u₂
    ext <;> simp
  have := deriv_deriv_eq_fderiv_fderiv hU hF h0 ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))
  simpa only [key] using this

end Dictionary

/-! ### Milnor's `E_**` as a Fréchet second derivative equals the project's `energyHessian` -/

section Hessian

open scoped Manifold

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
  {γ : ℝ → V} {p q : V} {U : Set (ℝ × ℝ)} {α : ℝ × ℝ → ℝ → V} {B : Finset ℝ}

/-- **Theorem 13.1 with `E_**` read as a Fréchet second derivative**: for a 2-parameter
variation `α` of a geodesic `γ ∈ Ω`, `D²(u ↦ E(α u))(0)((1, 0), (0, 1)) = E_**(W₁, W₂)`,
`Wᵢ = ∂α/∂uᵢ (0, ·)`.  (From `Morse.hasDerivAt_energyHessian` and
`deriv_deriv_eq_fderiv_fderiv_prod`.) -/
theorem fderiv_fderiv_energy_eq_energyHessian (hγ : γ ∈ Morse.pathSpace N p q)
    (hgeo : Morse.IsUnbrokenGeodesic hN γ) (hα : Morse.IsVariation N U α B)
    (hαγ : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) :
    fderiv ℝ (fderiv ℝ (fun u => Morse.energy (α u) 0 1)) 0 (1, 0) (0, 1) =
      Morse.energyHessian hN hγ ⟨_, hα.partial₁_mem hN hαγ⟩ ⟨_, hα.partial₂_mem hN hαγ⟩ := by
  rw [← deriv_deriv_eq_fderiv_fderiv_prod hα.isOpen (hα.contDiffOn_energy.of_le ENat.LEInfty.out)
    hα.zero_mem]
  exact (Morse.hasDerivAt_energyHessian hN hγ hgeo hα hαγ).deriv

/-- The other order of the second derivative (symmetry). -/
theorem fderiv_fderiv_energy_eq_energyHessian' (hγ : γ ∈ Morse.pathSpace N p q)
    (hgeo : Morse.IsUnbrokenGeodesic hN γ) (hα : Morse.IsVariation N U α B)
    (hαγ : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) :
    fderiv ℝ (fderiv ℝ (fun u => Morse.energy (α u) 0 1)) 0 (0, 1) (1, 0) =
      Morse.energyHessian hN hγ ⟨_, hα.partial₁_mem hN hαγ⟩ ⟨_, hα.partial₂_mem hN hαγ⟩ := by
  rw [← fderiv_fderiv_energy_eq_energyHessian hN hγ hgeo hα hαγ]
  exact fderiv_fderiv_symm hα.isOpen (hα.contDiffOn_energy.of_le ENat.LEInfty.out) hα.zero_mem _ _

/-- The `mixedD`-style reading `D(u ↦ D(E ∘ α)(u) e₁)(0) e₂` (inner derivative in `e₁ = (1, 0)`,
outer in `e₂ = (0, 1)`) equals `E_**(W₁, W₂)`, and the inner derivative is differentiable. -/
theorem fderiv_fderiv_apply_energy_eq_energyHessian (hγ : γ ∈ Morse.pathSpace N p q)
    (hgeo : Morse.IsUnbrokenGeodesic hN γ) (hα : Morse.IsVariation N U α B)
    (hαγ : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) :
    DifferentiableAt ℝ (fun u => fderiv ℝ (fun v => Morse.energy (α v) 0 1) u (1, 0)) 0 ∧
    fderiv ℝ (fun u => fderiv ℝ (fun v => Morse.energy (α v) 0 1) u (1, 0)) 0 (0, 1) =
      Morse.energyHessian hN hγ ⟨_, hα.partial₁_mem hN hαγ⟩ ⟨_, hα.partial₂_mem hN hαγ⟩ := by
  have hF : ContDiffOn ℝ 2 (fun u => Morse.energy (α u) 0 1) U :=
    hα.contDiffOn_energy.of_le ENat.LEInfty.out
  refine ⟨differentiableAt_fderiv_apply hα.isOpen hF hα.zero_mem _, ?_⟩
  rw [fderiv_fderiv_apply hα.isOpen hF hα.zero_mem]
  exact fderiv_fderiv_energy_eq_energyHessian' hN hγ hgeo hα hαγ

end Hessian

end

end RoundTrip.EnergyC2
