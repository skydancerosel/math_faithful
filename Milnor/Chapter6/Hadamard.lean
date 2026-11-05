import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Hadamard's lemma, and the smooth extension of `f (t x) / t`

Milnor proves (§6, Lemma 2, p. 33) that any orientation preserving diffeomorphism of `ℝᵐ` is
smoothly isotopic to the identity.  After reducing to a diffeomorphism `f` with `f 0 = 0` he uses
the isotopy `F (x, t) = f (t x) / t` for `0 < t ≤ 1` and `F (x, 0) = d f₀ (x)`, and the crux of the
argument is that `F` is *smooth*, including at `t = 0`.

This is **Hadamard's lemma**: a smooth `f` with `f 0 = 0` factors as `f x = L x (x)` where
`L x = ∫₀¹ d f_{t x} dt` is a smooth family of linear maps.  Then `f (t x) / t = L (t x) (x)`,
which manifestly extends smoothly across `t = 0` with value `d f₀ (x)`.

Everything is done for a smooth map between real normed spaces, the target assumed complete (so
that the Bochner integrals exist); Milnor only needs `E = F = ℝᵐ`.

## Main results

* `Milnor.contDiff_intervalIntegral` and `Milnor.contDiff_intervalIntegral_infty`: if
  `h : E × ℝ → F` is `Cⁿ` (resp. `C^∞`) then so is `x ↦ ∫ t in 0..1, h (x, t)`.  This is not in
  Mathlib; it is proved by induction on `n`, differentiating under the integral sign, the bound
  needed for the domination hypothesis coming from compactness of the segment `{x} × [0, 1]`.
* `Milnor.exists_hadamard`: Hadamard's lemma, `f x = L x (x)` with `L` smooth and `L 0 = d f₀`.
* `Milnor.exists_contDiff_extension`: there is a smooth `G : E × ℝ → F` with
  `G (x, t) = t⁻¹ • f (t • x)` for `t ≠ 0` and `G (x, 0) = d f₀ (x)`.
* `Milnor.contDiff_ite_smul_inv`: the same statement for the explicit `if t = 0 then … else …`
  formula, which is the form Milnor's isotopy is written in.
-/

open Set Filter MeasureTheory
open scoped ContDiff Interval Topology

noncomputable section

namespace Milnor

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Smoothness of the parametric integral `x ↦ ∫ t in 0..1, h (x, t)`, in the shape in which it
can be proved by induction on `n`: the target space is confined to the universe `max u v`, because
each step of the induction replaces the target `G` by `E →L[ℝ] G`, which again lives in
`Type (max u v)`.  The unrestricted statement is `Milnor.contDiff_intervalIntegral`, deduced from
this one by lifting the target with `ULift`.

The induction step differentiates under the integral sign
(`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`); the integrable bound demanded
there is produced from the continuity of `d h` on a "tube" `s × w ⊇ {x₀} × [0, 1]` around the
compact segment `{x₀} × [0, 1]`. -/
private theorem contDiff_intervalIntegral_aux (n : ℕ) :
    ∀ {G : Type max u v} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      {h : E × ℝ → G}, ContDiff ℝ n h → ContDiff ℝ n fun x => ∫ t in (0 : ℝ)..1, h (x, t) := by
  induction n with
  | zero =>
      intro G _ _ _ h hh
      simp only [Nat.cast_zero, contDiff_zero] at hh ⊢
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun (x : E) (t : ℝ) => h (x, t)) hh 0 1
  | succ n ih =>
      intro G _ _ _ h hh
      push_cast at hh ⊢
      have hc : Continuous h := hh.continuous
      have hdf : Differentiable ℝ h := hh.differentiable (by simp)
      have hfd : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ h) := (contDiff_succ_iff_fderiv.1 hh).2.2
      have hD : ContDiff ℝ (n : WithTop ℕ∞)
          (fun p : E × ℝ => (fderiv ℝ h p).comp (ContinuousLinearMap.inl ℝ E ℝ)) :=
        hfd.clm_comp contDiff_const
      have hDc : Continuous
          (fun p : E × ℝ => (fderiv ℝ h p).comp (ContinuousLinearMap.inl ℝ E ℝ)) := hD.continuous
      -- differentiation under the integral sign
      have key : ∀ x₀ : E, HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, h (x, t))
          (∫ t in (0 : ℝ)..1, (fderiv ℝ h (x₀, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x₀ := by
        intro x₀
        -- a bound for `d h` on the compact segment `{x₀} × [0, 1]` …
        obtain ⟨M, hM⟩ := (isCompact_singleton.prod
          (isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_bound_of_continuousOn hDc.continuousOn
        -- … extends to a tube `s × w` around it
        obtain ⟨s, w, hs, -, hx₀s, hIcc, hsw⟩ :=
          generalized_tube_lemma (isCompact_singleton (x := x₀))
            (isCompact_Icc (a := (0 : ℝ)) (b := 1)) (isOpen_lt hDc.norm continuous_const)
            (fun p hp => lt_of_le_of_lt (hM p hp) (lt_add_one M))
        refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
          (F := fun (x : E) (t : ℝ) => h (x, t))
          (F' := fun (x : E) (t : ℝ) => (fderiv ℝ h (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ))
          (bound := fun _ => M + 1) (s := s) (hs.mem_nhds (singleton_subset_iff.1 hx₀s))
          (.of_forall fun x =>
            (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
          ((hc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)
          ((hDc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
          (.of_forall fun t ht x hx => ?_) intervalIntegrable_const
          (.of_forall fun t _ x _ => (hdf (x, t)).hasFDerivAt.comp x
            ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)))
        have ht' : t ∈ Icc (0 : ℝ) 1 :=
          Ioc_subset_Icc_self (by rwa [uIoc_of_le zero_le_one] at ht)
        exact (hsw (mk_mem_prod hx (hIcc ht'))).le
      rw [contDiff_succ_iff_fderiv]
      refine ⟨fun x₀ => (key x₀).differentiableAt, by simp, ?_⟩
      have hfe : fderiv ℝ (fun x => ∫ t in (0 : ℝ)..1, h (x, t))
          = fun x₀ =>
            ∫ t in (0 : ℝ)..1, (fderiv ℝ h (x₀, t)).comp (ContinuousLinearMap.inl ℝ E ℝ) :=
        funext fun x₀ => (key x₀).fderiv
      rw [hfe]
      exact ih hD

/-- **Smoothness of an integral over a fixed interval with a parameter.**  If `h : E × ℝ → F` is
`n` times continuously differentiable (`E`, `F` real normed spaces, `F` complete) then so is
`x ↦ ∫ t in 0..1, h (x, t)`.  (Not in Mathlib.) -/
theorem contDiff_intervalIntegral (n : ℕ) {h : E × ℝ → F} (hh : ContDiff ℝ n h) :
    ContDiff ℝ n fun x => ∫ t in (0 : ℝ)..1, h (x, t) := by
  -- move the target up to the universe `max u v`, where the induction of
  -- `contDiff_intervalIntegral_aux` lives
  have e : F ≃L[ℝ] ULift.{u} F := ContinuousLinearEquiv.ulift.symm
  have hup : ContDiff ℝ (n : WithTop ℕ∞)
      fun p : E × ℝ => (e : F →L[ℝ] ULift.{u} F) (h p) :=
    (e : F →L[ℝ] ULift.{u} F).contDiff.comp hh
  have key := contDiff_intervalIntegral_aux (E := E) n hup
  have hdown : ContDiff ℝ (n : WithTop ℕ∞) fun x =>
      (e.symm : ULift.{u} F →L[ℝ] F) (∫ t in (0 : ℝ)..1, (e : F →L[ℝ] ULift.{u} F) (h (x, t))) :=
    (e.symm : ULift.{u} F →L[ℝ] F).contDiff.comp key
  have hfix : ∀ x : E, (e.symm : ULift.{u} F →L[ℝ] F)
      (∫ t in (0 : ℝ)..1, (e : F →L[ℝ] ULift.{u} F) (h (x, t)))
      = ∫ t in (0 : ℝ)..1, h (x, t) := by
    intro x
    have hint : IntervalIntegrable (fun t : ℝ => h (x, t)) volume 0 1 :=
      (hh.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
    rw [ContinuousLinearMap.intervalIntegral_comp_comm (e : F →L[ℝ] ULift.{u} F) hint]
    simp
  simpa only [hfix] using hdown

/-- **Smoothness of an integral over a fixed interval with a parameter**, `C^∞` version: if
`h : E × ℝ → F` is smooth then so is `x ↦ ∫ t in 0..1, h (x, t)`. -/
theorem contDiff_intervalIntegral_infty {h : E × ℝ → F} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ fun x => ∫ t in (0 : ℝ)..1, h (x, t) :=
  contDiff_infty.2 fun n => contDiff_intervalIntegral n (contDiff_infty.1 hh n)

/-- **Hadamard's lemma**, coordinate free.  A smooth map `f` between real normed spaces (the
target complete) with `f 0 = 0` factors as `f x = L x (x)` for a smooth family `L` of continuous
linear maps, namely `L x = ∫₀¹ d f_{t x} dt`; moreover `L 0 = d f₀`.

This is what Milnor uses on p. 33 to see that `f (t x) / t` extends smoothly over `t = 0`. -/
theorem exists_hadamard {f : E → F} (hf : ContDiff ℝ ∞ f) (hf0 : f 0 = 0) :
    ∃ L : E → (E →L[ℝ] F), ContDiff ℝ ∞ L ∧ (∀ x, f x = L x x) ∧ L 0 = fderiv ℝ f 0 := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2
  refine ⟨fun x => ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x), ?_, ?_, ?_⟩
  · exact contDiff_intervalIntegral_infty (h := fun p : E × ℝ => fderiv ℝ f (p.2 • p.1))
      (hfd.comp (contDiff_snd.smul contDiff_fst))
  · intro x
    -- the fundamental theorem of calculus along the segment from `0` to `x`
    have taylor := map_add_eq_sum_add_integral_iteratedFDeriv (n := 0) (f := f) (x := 0) (y := x)
      fun t _ => hf.contDiffAt.of_le (by simp)
    have hint : IntervalIntegrable (fun t : ℝ => fderiv ℝ f (t • x)) volume 0 1 :=
      (hfd.continuous.comp (continuous_id.smul continuous_const)).intervalIntegrable 0 1
    have hpull : (∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x)) x
        = ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x) x :=
      ((ContinuousLinearMap.apply ℝ F x).intervalIntegral_comp_comm hint).symm
    rw [hpull]
    simpa [hf0, iteratedFDeriv_one_apply] using taylor
  · simp

/-- **The consequence Milnor uses** (§6, Lemma 2, p. 33).  For `f` smooth with `f 0 = 0` the map
`(x, t) ↦ f (t x) / t` extends to a smooth map `G` on all of `E × ℝ`, with value `d f₀ (x)` at
`t = 0`. -/
theorem exists_contDiff_extension {f : E → F} (hf : ContDiff ℝ ∞ f) (hf0 : f 0 = 0) :
    ∃ G : E × ℝ → F, ContDiff ℝ ∞ G ∧ (∀ (x : E) (t : ℝ), t ≠ 0 → G (x, t) = t⁻¹ • f (t • x)) ∧
      (∀ x : E, G (x, 0) = fderiv ℝ f 0 x) := by
  obtain ⟨L, hL, hfL, hL0⟩ := exists_hadamard hf hf0
  refine ⟨fun p => L (p.2 • p.1) p.1, (hL.comp (contDiff_snd.smul contDiff_fst)).clm_apply
    contDiff_fst, ?_, ?_⟩
  · intro x t ht
    change L (t • x) x = t⁻¹ • f (t • x)
    rw [hfL (t • x), map_smul, smul_smul, inv_mul_cancel₀ ht, one_smul]
  · intro x
    change L ((0 : ℝ) • x) x = fderiv ℝ f 0 x
    rw [zero_smul, hL0]

/-- The extension of `Milnor.exists_contDiff_extension` written out: the isotopy
`(x, t) ↦ f (t x) / t`, given the value `d f₀ (x)` at `t = 0`, is smooth on `E × ℝ`. -/
theorem contDiff_ite_smul_inv {f : E → F} (hf : ContDiff ℝ ∞ f) (hf0 : f 0 = 0) :
    ContDiff ℝ ∞ fun p : E × ℝ =>
      if p.2 = 0 then fderiv ℝ f 0 p.1 else p.2⁻¹ • f (p.2 • p.1) := by
  obtain ⟨G, hG, hGne, hG0⟩ := exists_contDiff_extension hf hf0
  have heq : (fun p : E × ℝ =>
      if p.2 = 0 then fderiv ℝ f 0 p.1 else p.2⁻¹ • f (p.2 • p.1)) = G := by
    funext p
    obtain ⟨x, t⟩ := p
    by_cases ht : t = 0
    · subst ht; simpa using (hG0 x).symm
    · simpa [ht] using (hGne x t ht).symm
  rw [heq]
  exact hG

end Milnor
