import Morse.Chapter9.JacobiSpace

/-!
Milnor, *Morse Theory*, §15, pp. 83–85: the tools for the proof of the index theorem — the
second variation formula for broken Jacobi fields, and why `E_**` is positive definite on fields
vanishing at the points of a fine subdivision — for a submanifold `N ⊆ ℝᴷ` with the induced
metric.

# The Hessian on broken Jacobi fields; positivity on short pieces

## Milnor's text, paraphrased

(pp. 83–85) Choose a subdivision `0 = t₀ < ⋯ < t_k = 1` so fine that each `γ|[t_{i−1}, t_i]` lies
in an open set `U` as in Lemma 10.3 / 14.5 and is minimal.  Then (Remark 14.5) Jacobi fields
along each segment are determined by their values at its ends, and these can be prescribed; and
(Lemma 15.3) for `W ∈ TΩ_γ` vanishing at all `t_i`, `E_**(W, W) ≥ 0` because each segment is
minimal, `E(ᾱ(u)) ≥ E(γ)`; equality forces `W` into the null space, i.e. `W` is a Jacobi field
(Theorem 14.1), hence `0` (Remark 14.5).  For a broken Jacobi field `W₁` and any `W₂`, the second
variation formula reads `½ E_**(W₁, W₂) = −Σ_t ⟨W₂(t), Δ_t DW₁/dt⟩`.

## In the embedded setting

* `Morse.energyHessian_eq_jumps`: **the second variation formula for broken Jacobi fields**: if
  `W` agrees near every `t ∈ (0, 1)` off a finite set `B` with a Jacobi field (for instance with
  `0`), then `E_**(W, Y) = −2 Σ_{b ∈ B ∩ (0, 1)} ⟨Y(b), Δ_b DW/dt⟩` (from Theorem 13.1, the
  integral term vanishing).
* `Morse.hessForm_ge`: **positivity on fields vanishing at nearby points**, by an analytic
  estimate.  There is a constant `h₀ = Morse.fineMesh hc > 0`, depending only on `γ` (through
  bounds for `P'` and the curvature along `γ`), such that if every `t ∈ [0, 1]` has a zero of `W`
  in `[t − h₀, t]`, then `½ E_**(W, W) ≥ ∫₀¹ ‖W‖²`: on each piece `‖W(t)‖² ≤ h₀ ∫ ‖W'‖²`
  (Schwarz, Lemma 12.A), while `‖DW/dt‖² ≥ ‖W'‖² − ‖P'‖²‖W‖²` and
  `⟨R(V, W)V, W⟩ ≤ ‖R(V, ·)V‖ ‖W‖²`.
* `Morse.eq_zero_of_short`: **no two parameters closer than `h₀` are conjugate** (Remark 14.5 in
  the form needed for Theorem 15.1): a Jacobi field vanishing at `a < b`, `b − a ≤ h₀`, is the
  restriction of a field `W` with `E_**(W, W) = 0` by the formula above, hence `0`.
* `Morse.jacEvalEnds_bijective`, `Morse.exists_jacobi_ends`: so along a segment of length `≤ h₀`
  a Jacobi field is determined by its values at the ends, which can be prescribed (dimension
  count, as in Milnor's proof of Lemma 14.4).

## Relation with Milnor's proof

Milnor gets the two properties of a fine subdivision from Lemma 10.3 (minimal geodesics in a
convex neighbourhood, with the variations of Lemma 14.4) and Theorem 10.4 (short geodesics are
minimal).  Here both come from the single estimate `Morse.hessForm_ge`, which needs neither the
exponential map nor minimality, and gives the strict positivity on `T'` directly, without passing
through Theorem 14.1.  (Remark 14.5 itself, with Milnor's neighbourhoods `U`, is
`Morse.remark_14_5` in `Morse/Chapter9/JacobiVariation.lean`.)
-/

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace Interval

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {γ : ℝ → V}

/-! ### Jacobi fields and the second variation formula -/

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem jacobiExpr_congr {X X' : ℝ → V} {t : ℝ} (hev : X =ᶠ[𝓝 t] X') :
    jacobiExpr hN γ X t = jacobiExpr hN γ X' t := by
  have hev' : covD hN γ X =ᶠ[𝓝 t] covD hN γ X' := by
    filter_upwards [eventually_eventually_nhds.2 hev] with x hx
    rw [covD, covD, (show X =ᶠ[𝓝 x] X' from hx).deriv_eq]
  rw [jacobiExpr, jacobiExpr, covD, covD, hev'.deriv_eq, hev.eq_of_nhds]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The zero field is a Jacobi field. -/
theorem isJacobiField_zero : IsJacobiField hN γ 0 where
  contDiffOn := contDiffOn_const
  tangent _ _ := map_zero _
  eq t _ := by
    have h0 : covD hN γ (0 : ℝ → V) = 0 := funext fun s => by simp [covD]
    rw [jacobiExpr, h0]
    by_cases hN' : γ t ∈ N
    · simp [covD, curvR_of_mem hN hN', curvOp]
    · simp [covD, curvR, hN']

/-- **The second variation formula for broken Jacobi fields** (Milnor pp. 84, 87): if `W ∈ TΩ_γ`
agrees near every point of `(0, 1)` off a finite set `B` with a Jacobi field, then
`E_**(W, Y) = −2 Σ_{b ∈ B ∩ (0, 1)} ⟨Y(b), Δ_b DW/dt⟩`. -/
theorem energyHessian_eq_jumps {p q : V} (hγ : γ ∈ pathSpace N p q) (X Y : pathTangent hN γ)
    {B : Finset ℝ} (hX : ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ B →
      ∃ J, IsJacobiField hN γ J ∧ (X : ℝ → V) =ᶠ[𝓝 t] J) :
    energyHessian hN hγ X Y = -2 * ∑ b ∈ B with b ∈ Ioo (0 : ℝ) 1,
      ⟪(Y : ℝ → V) b, prj hN (γ b) (jump X b)⟫ := by
  rw [energyHessian_apply, secondVariation]
  have hint : ∫ t in (0 : ℝ)..1, ⟪(Y : ℝ → V) t, covD hN γ (covD hN γ X) t +
      curvR hN (γ t) (deriv γ t) ((X : ℝ → V) t) (deriv γ t)⟫ = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
    · simp
    have hfin : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ insert (1 : ℝ) (B : Set ℝ) :=
      (B.finite_toSet.insert 1).countable.ae_notMem _
    filter_upwards [hfin] with t htB ht
    rw [uIoc_of_le zero_le_one] at ht
    rw [mem_insert_iff, not_or] at htB
    have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_le_of_ne ht.2 htB.1⟩
    obtain ⟨J, hJ, hev⟩ := hX t ht' htB.2
    have h1 := jacobiExpr_congr (hN := hN) (γ := γ) hev
    rw [hJ.eq t ht'] at h1
    rw [jacobiExpr] at h1
    rw [h1, inner_zero_right]
  have hsum : ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪(Y : ℝ → V) t, prj hN (γ t) (jump X t)⟫ =
      ∑ b ∈ B with b ∈ Ioo (0 : ℝ) 1, ⟪(Y : ℝ → V) b, prj hN (γ b) (jump X b)⟫ :=
    finsum_mem_Ioo_eq_sum fun t ht htB => by
      obtain ⟨J, hJ, hev⟩ := hX t ht htB
      have hd : DifferentiableAt ℝ (X : ℝ → V) t :=
        ((hJ.contDiffOn.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt
          (by simp)).congr_of_eventuallyEq hev
      rw [jump_eq_zero hd, map_zero, inner_zero_right]
  rw [hsum, hint]
  ring

/-! ### Positivity on fields vanishing at nearby points -/

section Positivity

variable (hc : IsSmoothCurveIn hN γ)
include hc

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem IsSmoothCurveIn.mem_pathSpace : γ ∈ pathSpace N (γ 0) (γ 1) :=
  ⟨IsPiecewiseSmooth.of_contDiffOn hc.contDiffOn zero_le_one subset_rfl, hc.mem, rfl, rfl⟩

theorem exists_jacBound : ∃ C, 0 ≤ C ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ‖dpAlong hN γ t‖ ^ 2 + ‖curvAlong hN γ t‖ ≤ C := by
  have hcont : ContinuousOn (fun t => ‖dpAlong hN γ t‖ ^ 2 + ‖curvAlong hN γ t‖) (Icc 0 1) :=
    (hc.contDiffOn_dpAlong.continuousOn.norm.pow 2).add hc.contDiffOn_curvAlong.continuousOn.norm
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun t ht => ?_⟩
  have := hC t ht
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

variable (hN γ) in
/-- A bound for `‖P'‖² + ‖R(V, P ·)V‖` along `γ`. -/
def jacBound (hc : IsSmoothCurveIn hN γ) : ℝ := Classical.choose (exists_jacBound hc)

theorem jacBound_nonneg : 0 ≤ jacBound hN γ hc := (Classical.choose_spec (exists_jacBound hc)).1

theorem le_jacBound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖dpAlong hN γ t‖ ^ 2 + ‖curvAlong hN γ t‖ ≤ jacBound hN γ hc :=
  (Classical.choose_spec (exists_jacBound hc)).2 t ht

variable (hN γ) in
/-- **The mesh of a fine subdivision**: pieces of length `≤ h₀ = 1 / (jacBound + 1)`. -/
def fineMesh (hc : IsSmoothCurveIn hN γ) : ℝ := 1 / (jacBound hN γ hc + 1)

theorem fineMesh_pos : 0 < fineMesh hN γ hc := by
  have := jacBound_nonneg hc
  rw [fineMesh]
  positivity

/-- The integrand of `E_**(X, X)` is at least `‖X'‖² − C‖X‖²`. -/
theorem integrand_ge {X : ℝ → V} (hXT : ∀ t ∈ Icc (0 : ℝ) 1, prj hN (γ t) (X t) = X t)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hd : DifferentiableAt ℝ X t) :
    ‖deriv X t‖ ^ 2 - jacBound hN γ hc * ‖X t‖ ^ 2 ≤
      ⟪covD hN γ X t, covD hN γ X t⟫ -
        ⟪curvR hN (γ t) (deriv γ t) (X t) (deriv γ t), X t⟫ := by
  have ht' := Ioo_subset_Icc_self ht
  -- `X' = P'X + PX'`
  have hX' : deriv X t = dpAlong hN γ t (X t) + prj hN (γ t) (deriv X t) := by
    have hev : X =ᶠ[𝓝 t] fun x => prj hN (γ x) (X x) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
      exact (hXT x (Ioo_subset_Icc_self hx)).symm
    conv_lhs => rw [hev.deriv_eq]
    exact ((hc.hasDerivAt_prj ht).clm_apply hd.hasDerivAt).deriv
  -- Pythagoras: `‖X'‖² = ‖PX'‖² + ‖X' − PX'‖²`
  have h1 : ⟪prj hN (γ t) (deriv X t), prj hN (γ t) (deriv X t)⟫ =
      ⟪prj hN (γ t) (deriv X t), deriv X t⟫ := by
    rw [inner_prj_left, prj_prj, real_inner_comm]
  have horth : ⟪prj hN (γ t) (deriv X t), deriv X t - prj hN (γ t) (deriv X t)⟫ = 0 := by
    rw [inner_sub_right, h1, sub_self]
  have hpyth : ‖deriv X t‖ ^ 2 = ‖prj hN (γ t) (deriv X t)‖ ^ 2 +
      ‖deriv X t - prj hN (γ t) (deriv X t)‖ ^ 2 := by
    have := norm_add_sq_real (prj hN (γ t) (deriv X t)) (deriv X t - prj hN (γ t) (deriv X t))
    rw [horth, mul_zero, add_zero, add_sub_cancel] at this
    exact this
  have hnormal : deriv X t - prj hN (γ t) (deriv X t) = dpAlong hN γ t (X t) := by
    linear_combination (norm := module) hX'
  have hD : ‖dpAlong hN γ t (X t)‖ ^ 2 ≤ ‖dpAlong hN γ t‖ ^ 2 * ‖X t‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((dpAlong hN γ t).le_opNorm _) 2
  -- the curvature term
  have hK : curvR hN (γ t) (deriv γ t) (X t) (deriv γ t) = curvAlong hN γ t (X t) := by
    rw [curvAlong_apply (hc.mem t ht'), hXT t ht', hc.velAlong_eq ht]
  have hKb : ⟪curvAlong hN γ t (X t), X t⟫ ≤ ‖curvAlong hN γ t‖ * ‖X t‖ ^ 2 := by
    calc ⟪curvAlong hN γ t (X t), X t⟫ ≤ ‖curvAlong hN γ t (X t)‖ * ‖X t‖ :=
          real_inner_le_norm _ _
      _ ≤ ‖curvAlong hN γ t‖ * ‖X t‖ * ‖X t‖ :=
          mul_le_mul_of_nonneg_right ((curvAlong hN γ t).le_opNorm _) (norm_nonneg _)
      _ = ‖curvAlong hN γ t‖ * ‖X t‖ ^ 2 := by ring
  have hC := le_jacBound hc ht'
  have hcov : ⟪covD hN γ X t, covD hN γ X t⟫ = ‖prj hN (γ t) (deriv X t)‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq]; rfl
  rw [hcov, hK]
  rw [hnormal] at hpyth
  nlinarith [sq_nonneg ‖X t‖, norm_nonneg (dpAlong hN γ t), norm_nonneg (curvAlong hN γ t)]

omit hc in
/-- **Poincaré's inequality on short pieces**: if every `t ∈ [0, 1]` has a zero of `X` in
`[t − h, t]`, then `∫₀¹ ‖X‖² ≤ h ∫₀¹ ‖X'‖²` (from `‖X(t)‖ ≤ L_s^t(X)` and Lemma 12.A). -/
theorem integral_norm_sq_le {X : ℝ → V} (hX : IsPiecewiseSmooth X 0 1) {h : ℝ} (hh : 0 ≤ h)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc 0 t, t - s ≤ h ∧ X s = 0) :
    ∫ t in (0 : ℝ)..1, ‖X t‖ ^ 2 ≤ h * ∫ t in (0 : ℝ)..1, ‖deriv X t‖ ^ 2 := by
  have hE := hX.intervalIntegrable_norm_deriv_sq
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, ‖X t‖ ^ 2 ≤ h * energy X 0 1 := by
    intro t ht
    obtain ⟨s, hs, hts, hXs⟩ := hzero t ht
    rcases eq_or_lt_of_le hs.2 with hst | hst
    · rw [← hst, hXs, norm_zero]
      have : 0 ≤ energy X 0 1 :=
        intervalIntegral.integral_nonneg zero_le_one fun _ _ => by positivity
      nlinarith
    have hXst : IsPiecewiseSmooth X s t := hX.mono hs.1 hst.le ht.2
    have h1 : ‖X t‖ ≤ pathLength X s t := by
      have := hXst.isAdmissible.norm_sub_le_pathLength
      rwa [hXs, sub_zero] at this
    have h2 := pathLength_sq_le_energy hXst
    have h3 : energy X s t ≤ energy X 0 1 :=
      intervalIntegral.integral_mono_interval hs.1 hst.le ht.2
        (Eventually.of_forall fun _ => by positivity) hE
    have h4 : 0 ≤ energy X s t := intervalIntegral.integral_nonneg hst.le fun _ _ => by positivity
    have h5 := hXst.isAdmissible.pathLength_nonneg
    calc ‖X t‖ ^ 2 ≤ pathLength X s t ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (t - s) * energy X s t := h2
      _ ≤ h * energy X 0 1 := mul_le_mul hts h3 h4 hh
  have hcont : ContinuousOn (fun t => ‖X t‖ ^ 2) (Icc 0 1) := hX.2.1.norm.pow 2
  calc ∫ t in (0 : ℝ)..1, ‖X t‖ ^ 2 ≤ ∫ _ in (0 : ℝ)..1, h * energy X 0 1 :=
        intervalIntegral.integral_mono_on zero_le_one (hcont.intervalIntegrable_of_Icc zero_le_one)
          intervalIntegrable_const hpt
    _ = h * ∫ t in (0 : ℝ)..1, ‖deriv X t‖ ^ 2 := by simp [energy]

/-- **Positivity on fields vanishing at nearby points**: if every `t ∈ [0, 1]` has a zero of
`X ∈ TΩ_γ` in `[t − h₀, t]`, `h₀ = Morse.fineMesh`, then `½ E_**(X, X) ≥ ∫₀¹ ‖X‖²`. -/
theorem hessForm_ge {p q : V} (hγ : γ ∈ pathSpace N p q) {X : ℝ → V} (hX : X ∈ pathTangent hN γ)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc 0 t, t - s ≤ fineMesh hN γ hc ∧ X s = 0) :
    ∫ t in (0 : ℝ)..1, ‖X t‖ ^ 2 ≤ hessForm hN γ X X := by
  have hC := jacBound_nonneg hc
  have hP := integral_norm_sq_le hX.1 (fineMesh_pos hc).le hzero
  have hE := hX.1.intervalIntegrable_norm_deriv_sq
  have hcont : ContinuousOn (fun t => ‖X t‖ ^ 2) (Icc 0 1) := hX.1.2.1.norm.pow 2
  have hI2 : IntervalIntegrable (fun t => ‖X t‖ ^ 2) volume 0 1 :=
    hcont.intervalIntegrable_of_Icc zero_le_one
  have hmono : ∫ t in (0 : ℝ)..1, (‖deriv X t‖ ^ 2 - jacBound hN γ hc * ‖X t‖ ^ 2) ≤
      hessForm hN γ X X := by
    rw [hessForm]
    refine intervalIntegral.integral_mono_ae_restrict zero_le_one
      (hE.sub (hI2.const_mul (jacBound hN γ hc))) (intervalIntegrable_hessIntegrand hN hγ hX hX) ?_
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hX.1.ae_differentiableAt, (countable_singleton (0 : ℝ)).ae_notMem _,
      (countable_singleton (1 : ℝ)).ae_notMem _] with t hd h0 h1 ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
    exact integrand_ge hc hX.2.1 ht' (hd (by rw [uIoc_of_le zero_le_one]; exact ⟨ht'.1, ht.2⟩))
  rw [intervalIntegral.integral_sub hE (hI2.const_mul _), intervalIntegral.integral_const_mul]
    at hmono
  set C := jacBound hN γ hc with hCdef
  have hfm : fineMesh hN γ hc * (C + 1) = 1 := by
    rw [fineMesh, ← hCdef]; field_simp
  have hI0 : 0 ≤ ∫ t in (0 : ℝ)..1, ‖X t‖ ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun _ _ => by positivity
  have hE' : (C + 1) * ∫ t in (0 : ℝ)..1, ‖X t‖ ^ 2 ≤ ∫ t in (0 : ℝ)..1, ‖deriv X t‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hP (show 0 ≤ C + 1 by linarith)
    calc (C + 1) * ∫ t in (0 : ℝ)..1, ‖X t‖ ^ 2
        ≤ (C + 1) * (fineMesh hN γ hc * ∫ t in (0 : ℝ)..1, ‖deriv X t‖ ^ 2) := this
      _ = ∫ t in (0 : ℝ)..1, ‖deriv X t‖ ^ 2 := by rw [← mul_assoc, mul_comm (C + 1), hfm, one_mul]
  linarith

/-- **`E_**` is positive definite on fields vanishing at nearby points**: under the hypothesis of
`Morse.hessForm_ge`, `E_**(X, X) = 0` forces `X = 0` on `[0, 1]`. -/
theorem eqOn_zero_of_hessForm {p q : V} (hγ : γ ∈ pathSpace N p q) {X : ℝ → V}
    (hX : X ∈ pathTangent hN γ)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc 0 t, t - s ≤ fineMesh hN γ hc ∧ X s = 0)
    (h0 : hessForm hN γ X X ≤ 0) : EqOn X 0 (Icc 0 1) := by
  have h1 := (hessForm_ge hc hγ hX hzero).trans h0
  have hcont : Continuous (fun t => ‖X (projIcc (0 : ℝ) 1 zero_le_one t)‖ ^ 2) :=
    (hX.1.2.1.norm.pow 2).comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun t => (projIcc (0 : ℝ) 1 zero_le_one t).2
  have hI0 : ∫ t in (0 : ℝ)..1, ‖X t‖ ^ 2 = 0 :=
    le_antisymm h1 (intervalIntegral.integral_nonneg zero_le_one fun _ _ => by positivity)
  have hcongr : ∫ t in (0 : ℝ)..1, ‖X (projIcc (0 : ℝ) 1 zero_le_one t)‖ ^ 2 =
      ∫ t in (0 : ℝ)..1, ‖X t‖ ^ 2 :=
    intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le zero_le_one] at ht
      simp [projIcc_of_mem _ ht]
  have hI0' : ∫ t in (0 : ℝ)..1, ‖X (projIcc (0 : ℝ) 1 zero_le_one t)‖ ^ 2 = 0 :=
    hcongr.trans hI0
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
    (.of_forall fun _ => by positivity) (hcont.intervalIntegrable 0 1)).1 hI0'
  have hopen := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset
    Ioo_subset_Ioc_self hae) isOpen_Ioo hcont.continuousOn continuousOn_const
  have hIoo : ∀ t ∈ Ioo (0 : ℝ) 1, X t = 0 := fun t ht => by
    have := hopen ht
    simp only [Pi.zero_apply, projIcc_of_mem _ (Ioo_subset_Icc_self ht),
      pow_eq_zero_iff two_ne_zero, norm_eq_zero] at this
    exact this
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h]; exact hX.2.2.1
  rcases eq_or_lt_of_le ht.2 with h' | h'
  · rw [h']; exact hX.2.2.2
  exact hIoo t ⟨h, h'⟩

/-! ### No conjugate points closer than `h₀` -/

omit [FiniteDimensional ℝ V] hc in
/-- The field equal to `J` on `[a, b]` and to `0` elsewhere is piecewise smooth if `J` vanishes
at `a` and `b`. -/
theorem isPiecewiseSmooth_indicator {J : ℝ → V} (hJ : ContDiffOn ℝ ∞ J (Icc 0 1)) {a b : ℝ}
    (_ha : 0 ≤ a) (_hab : a ≤ b) (_hb : b ≤ 1) (hJa : J a = 0) (hJb : J b = 0) :
    IsPiecewiseSmooth ((Icc a b).indicator J) 0 1 := by
  classical
  have hpiece : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ ({a, b} : Finset ℝ), x ∉ Ioo s t) →
      ContDiffOn ℝ ∞ ((Icc a b).indicator J) (Icc s t) := by
    intro s t hs hst ht hB
    have hna : a ∉ Ioo s t := hB a (by simp)
    have hnb : b ∉ Ioo s t := hB b (by simp)
    by_cases h1 : t ≤ a
    · refine contDiffOn_const (c := (0 : V)).congr fun x hx => ?_
      by_cases hx' : x ∈ Icc a b
      · have : x = a := le_antisymm (hx.2.trans h1) hx'.1
        rw [indicator_of_mem hx', this, hJa]
      · rw [indicator_of_notMem hx']
    by_cases h2 : b ≤ s
    · refine contDiffOn_const (c := (0 : V)).congr fun x hx => ?_
      by_cases hx' : x ∈ Icc a b
      · have : x = b := le_antisymm hx'.2 (h2.trans hx.1)
        rw [indicator_of_mem hx', this, hJb]
      · rw [indicator_of_notMem hx']
    push Not at h1 h2
    have has : a ≤ s := by
      by_contra h
      exact hna ⟨lt_of_not_ge h, h1⟩
    have htb : t ≤ b := by
      by_contra h
      exact hnb ⟨h2, lt_of_not_ge h⟩
    refine (hJ.mono (Icc_subset_Icc hs ht)).congr fun x hx => ?_
    rw [indicator_of_mem (show x ∈ Icc a b from ⟨has.trans hx.1, hx.2.trans htb⟩)]
  exact ⟨zero_le_one, continuousOn_of_piecewise (B := ({a, b} : Finset ℝ))
    fun s t hs hst ht hB => (hpiece s t hs hst ht hB).continuousOn, ({a, b} : Finset ℝ), hpiece⟩

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] hc in
/-- `J` cut off to `[a, b]` lies in `TΩ_γ` if `J` is a Jacobi field vanishing at `a` and `b`. -/
theorem indicator_mem_pathTangent {J : ℝ → V} (hJ : IsJacobiField hN γ J) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hJa : J a = 0) (hJb : J b = 0) :
    (Icc a b).indicator J ∈ pathTangent hN γ := by
  refine ⟨isPiecewiseSmooth_indicator hJ.contDiffOn ha hab hb hJa hJb, fun t ht => ?_, ?_, ?_⟩
  · by_cases h : t ∈ Icc a b
    · rw [indicator_of_mem h]; exact hJ.tangent t ht
    · rw [indicator_of_notMem h, map_zero]
  · by_cases h : (0 : ℝ) ∈ Icc a b
    · rw [indicator_of_mem h, show (0 : ℝ) = a from le_antisymm ha h.1, hJa]
    · rw [indicator_of_notMem h]
  · by_cases h : (1 : ℝ) ∈ Icc a b
    · rw [indicator_of_mem h, show (1 : ℝ) = b from le_antisymm h.2 hb, hJb]
    · rw [indicator_of_notMem h]

/-- **No two parameters closer than `h₀` are conjugate** (the form of Remark 14.5 used in the
proof of Theorem 15.1): a Jacobi field vanishing at `a < b`, `b − a ≤ h₀`, vanishes. -/
theorem eq_zero_of_short {J : ℝ → V} (hJ : J ∈ jacobiSpace hN γ hc) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ 1) (hh : b - a ≤ fineMesh hN γ hc) (hJa : J a = 0)
    (hJb : J b = 0) : J = 0 := by
  classical
  have hγ := hc.mem_pathSpace
  set X : ℝ → V := (Icc a b).indicator J
  have hX : X ∈ pathTangent hN γ := indicator_mem_pathTangent hJ.1 ha hab.le hb hJa hJb
  -- `X` is locally a Jacobi field (`J` or `0`) off `{a, b}`
  have hloc : ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ ({a, b} : Finset ℝ) →
      ∃ J', IsJacobiField hN γ J' ∧ X =ᶠ[𝓝 t] J' := by
    intro t _ htB
    have hta : t ≠ a := fun h => htB (by simp [h])
    have htb : t ≠ b := fun h => htB (by simp [h])
    rcases lt_or_gt_of_ne hta with h1 | h1
    · refine ⟨0, isJacobiField_zero, ?_⟩
      filter_upwards [Iio_mem_nhds h1] with x hx
      exact indicator_of_notMem (fun h => absurd h.1 (not_le.2 hx)) _
    rcases lt_or_gt_of_ne htb with h2 | h2
    · refine ⟨J, hJ.1, ?_⟩
      filter_upwards [Ioo_mem_nhds h1 h2] with x hx
      exact indicator_of_mem (Ioo_subset_Icc_self hx) _
    · refine ⟨0, isJacobiField_zero, ?_⟩
      filter_upwards [Ioi_mem_nhds h2] with x hx
      exact indicator_of_notMem (fun h => absurd h.2 (not_le.2 hx)) _
  have hE := energyHessian_eq_jumps hγ (⟨X, hX⟩ : pathTangent hN γ)
    (⟨X, hX⟩ : pathTangent hN γ) hloc
  have hXa : X a = 0 := by simp [X, hJa]
  have hXb : X b = 0 := by simp [X, hJb]
  have hsum : ∑ x ∈ ({a, b} : Finset ℝ) with x ∈ Ioo (0 : ℝ) 1,
      ⟪X x, prj hN (γ x) (jump X x)⟫ = 0 :=
    Finset.sum_eq_zero fun x hx => by
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx.1 with rfl | rfl
      · rw [hXa, inner_zero_left]
      · rw [hXb, inner_zero_left]
  change energyHessian hN hγ ⟨X, hX⟩ ⟨X, hX⟩ = _ at hE
  rw [hsum, mul_zero, energyHessian_apply, secondVariation_eq_hessForm hN hγ hX hX] at hE
  have hzero : ∀ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc 0 t, t - s ≤ fineMesh hN γ hc ∧ X s = 0 := by
    intro t ht
    by_cases h : t ∈ Icc a b
    · exact ⟨a, ⟨ha, h.1⟩, by linarith [h.2], hXa⟩
    · exact ⟨t, ⟨ht.1, le_rfl⟩, by rw [sub_self]; exact (fineMesh_pos hc).le,
        indicator_of_notMem h _⟩
  have hX0 := eqOn_zero_of_hessForm hc hγ hX hzero (by linarith)
  -- `J` vanishes near the midpoint, so `J = 0`
  set m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  have hm01 : m ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hm.1], by linarith [hm.2]⟩
  have hev : J =ᶠ[𝓝 m] 0 := by
    filter_upwards [Ioo_mem_nhds hm.1 hm.2] with x hx
    have h1 : X x = 0 := hX0 (show x ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    change (Icc a b).indicator J x = 0 at h1
    rwa [indicator_of_mem (Ioo_subset_Icc_self hx)] at h1
  have hJm : J m = 0 := hev.eq_of_nhds
  have hcovm : covAlong hN γ J m = 0 := by
    have hd : HasDerivAt J 0 m := (hasDerivAt_const m (0 : V)).congr_of_eventuallyEq hev
    rw [covAlong, hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one m hm01), map_zero]
  exact jacobiSpace_eq_zero hc hJ (hJ.1.eqOn_zero hc hm01 hJm hcovm)

/-- `J ↦ (J(a), J(b))`. -/
def jacEvalEnds {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    jacobiSpace hN γ hc →ₗ[ℝ] tanAt hN (γ a) × tanAt hN (γ b) where
  toFun J := (⟨(J : ℝ → V) a, (mem_tanAt hN (hc.mem a ha)).2 (J.2.1.tangent a ha)⟩,
    ⟨(J : ℝ → V) b, (mem_tanAt hN (hc.mem b hb)).2 (J.2.1.tangent b hb)⟩)
  map_add' J J' := by ext <;> simp
  map_smul' c J := by ext <;> simp

/-- **Along a segment of length `≤ h₀`, Jacobi fields are determined by their values at the
ends, and these can be prescribed** (Milnor's proof of Lemma 14.4 and Remark 14.5: an injective
linear map between spaces of the same dimension `2n`). -/
theorem jacEvalEnds_bijective {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a < b) (hh : b - a ≤ fineMesh hN γ hc) : Bijective (jacEvalEnds hc ha hb) := by
  have hinj : Injective (jacEvalEnds hc ha hb) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro J hJ
    rw [LinearMap.mem_ker] at hJ
    have h1 : (J : ℝ → V) a = 0 := congrArg (fun z => (z.1 : V)) hJ
    have h2 : (J : ℝ → V) b = 0 := congrArg (fun z => (z.2 : V)) hJ
    exact (Submodule.mem_bot ℝ).2 (Subtype.ext (eq_zero_of_short hc J.2 ha.1 hab hb.2 hh h1 h2))
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [finrank_jacobiSpace hc, Module.finrank_prod, finrank_tanAt hN (hc.mem a ha),
    finrank_tanAt hN (hc.mem b hb)]
  ring

theorem exists_jacobi_ends {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a < b) (hh : b - a ≤ fineMesh hN γ hc) {u v : V} (hu : prj hN (γ a) u = u)
    (hv : prj hN (γ b) v = v) : ∃ J ∈ jacobiSpace hN γ hc, J a = u ∧ J b = v := by
  obtain ⟨J, hJ⟩ := (jacEvalEnds_bijective hc ha hb hab hh).2
    (⟨u, (mem_tanAt hN (hc.mem a ha)).2 hu⟩, ⟨v, (mem_tanAt hN (hc.mem b hb)).2 hv⟩)
  exact ⟨J, J.2, congrArg (fun z => (z.1 : V)) hJ, congrArg (fun z => (z.2 : V)) hJ⟩

end Positivity

end Morse
