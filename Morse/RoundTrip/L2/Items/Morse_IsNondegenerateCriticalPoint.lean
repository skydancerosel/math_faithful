import Morse
import RoundTrip.L2.Blind.Morse_IsNondegenerateCriticalPoint

/-! Layer-2 check of `Morse.IsNondegenerateCriticalPoint` against the blind textbook definition.
Both use the Hessian `fderiv ℝ (fderiv ℝ f) p` and the trivial-null-space non-degeneracy; they
differ only in "critical": the project asks `HasFDerivAt f 0 p`, the blind definition
`fderiv ℝ f p = 0`. So they agree wherever `f` is differentiable at `p` (the textbook's smooth
`f`). At a non-differentiable point the blind notion can hold through junk values: for
`f x = if x = 0 then 1 else x²` on `ℝ`, `f` is discontinuous at `0`, so `fderiv f 0 = 0` (junk)
and `fderiv f = fderiv (x ↦ x²)` everywhere, whose derivative at `0` is the non-degenerate
`(v, w) ↦ 2 v w`. -/

namespace RoundTrip.L2.Morse_IsNondegenerateCriticalPoint

theorem P_imp_T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (p : E) :
    Morse.IsNondegenerateCriticalPoint f p → T f p := by
  rintro ⟨h1, h2⟩
  exact ⟨h1.fderiv_eq, Morse.isNondegenerate_iff.1 h2⟩

theorem agree_of {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (p : E)
    (hf : DifferentiableAt ℝ f p) : Morse.IsNondegenerateCriticalPoint f p ↔ T f p := by
  unfold Morse.IsNondegenerateCriticalPoint T IsCrit
  rw [Morse.isCriticalPoint_iff hf, Morse.isNondegenerate_iff]
  rfl

/-- The counterexample: `x²` with the value at `0` moved to `1`. -/
noncomputable def f₀ : ℝ → ℝ := fun x => if x = 0 then 1 else x * x

theorem f₀_eventuallyEq : f₀ =ᶠ[nhdsWithin (0 : ℝ) {0}ᶜ]
    (fun x => ContinuousLinearMap.mul ℝ ℝ x x) := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp [f₀, show x ≠ 0 from hx]

theorem f₀_not_differentiableAt : ¬ DifferentiableAt ℝ f₀ 0 := by
  intro h
  have h1 : Filter.Tendsto f₀ (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 1) := by
    have := h.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
    simpa [f₀] using this
  have h2 : Filter.Tendsto f₀ (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 0) := by
    have hc : Continuous (fun x : ℝ => ContinuousLinearMap.mul ℝ ℝ x x) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
    simp only [map_zero] at this
    exact this.congr' f₀_eventuallyEq.symm
  exact one_ne_zero (tendsto_nhds_unique h1 h2)

theorem fderiv_f₀ : fderiv ℝ f₀ = fderiv ℝ (fun x => ContinuousLinearMap.mul ℝ ℝ x x) := by
  funext x
  by_cases hx : x = 0
  · subst hx
    rw [fderiv_zero_of_not_differentiableAt f₀_not_differentiableAt]
    have : HasFDerivAt (fun x : ℝ => ContinuousLinearMap.mul ℝ ℝ x x) _ 0 :=
      (ContinuousLinearMap.mul ℝ ℝ).hasFDerivAt_of_bilinear (hasFDerivAt_id (0 : ℝ))
        (hasFDerivAt_id (0 : ℝ))
    rw [this.fderiv]
    ext
    simp
  · apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [f₀, hy]

theorem differ : ¬ (Morse.IsNondegenerateCriticalPoint f₀ 0 ↔ T f₀ 0) := by
  have hT : T f₀ 0 := by
    refine ⟨?_, ?_⟩
    · exact fderiv_zero_of_not_differentiableAt f₀_not_differentiableAt
    · intro v hv
      have h := hv 1
      have hH : hess f₀ 0 = Morse.hessian (fun x => ContinuousLinearMap.mul ℝ ℝ x x) 0 := by
        simp only [hess, Morse.hessian, fderiv_f₀]
      rw [hH, Morse.hessian_bilinear] at h
      simp at h
      linarith
  intro h
  exact f₀_not_differentiableAt (h.2 hT).1.differentiableAt

end RoundTrip.L2.Morse_IsNondegenerateCriticalPoint
