import Morse
import RoundTrip.Check
import RoundTrip.Blind.V5_6

open Filter Topology

namespace RoundTrip.V5_6

/-- The project's statement (universes instantiated at 0): the real Hessian of
`z ↦ ‖w z − p‖²` at `q`, for `w` complex-`C²` at `q`, is `2(Re⟨dw v, dw v'⟩ + Re⟨w q − p, d²w(v, v')⟩)`. -/
def A : Prop := type_of% @Morse.hessian_normSq_sub_holomorphic.{0,0}

theorem A_holds : A := @Morse.hessian_normSq_sub_holomorphic

/-- B ⇒ A holds only because A is provable outright (the project's computation re-done); B,
about analytic immersions `ℂᵏ → ℂⁿ` and a unit normal `v`, does not give the Hessian formula for
arbitrary `C²` maps between arbitrary complex spaces and arbitrary `p`. -/
theorem B_to_A : B → A := by
  intro _ V _ _ F _ _ w q hw p v v'
  have hf : (fun z => ‖w z - p‖ ^ 2) = fun z => Morse.reInner (w z - p) (w z - p) := by
    funext z
    rw [Morse.reInner_self]
  rw [hf]
  have hdiff : ∀ᶠ z in 𝓝 q, DifferentiableAt ℂ w z :=
    (hw.eventually (by simp)).mono fun z hz => hz.differentiableAt (by simp)
  have h1 : ∀ᶠ z in 𝓝 q, HasFDerivAt (fun z => Morse.reInner (w z - p) (w z - p))
      ((2 : ℝ) • (Morse.reInner (w z - p)).comp ((fderiv ℂ w z).restrictScalars ℝ)) z := by
    filter_upwards [hdiff] with z hz
    have hu : HasFDerivAt (fun z => w z - p) ((fderiv ℂ w z).restrictScalars ℝ) z :=
      (hz.hasFDerivAt.restrictScalars ℝ).sub_const p
    refine ((Morse.reInner : F →L[ℝ] F →L[ℝ] ℝ).hasFDerivAt_of_bilinear hu hu).congr_fderiv ?_
    ext v
    simp [Morse.reInner_comm (fderiv ℂ w z v)]
    ring
  have h2 : fderiv ℝ (fun z => Morse.reInner (w z - p) (w z - p)) =ᶠ[𝓝 q]
      fun z => (2 : ℝ) • (Morse.reInner (w z - p)).comp ((fderiv ℂ w z).restrictScalars ℝ) :=
    h1.mono fun z hz => hz.fderiv
  have hwq : HasFDerivAt (fun z => w z - p) ((fderiv ℂ w q).restrictScalars ℝ) q :=
    ((hw.differentiableAt (by simp)).hasFDerivAt.restrictScalars ℝ).sub_const p
  have hc : HasFDerivAt (fun z => Morse.reInner (w z - p))
      ((Morse.reInner : F →L[ℝ] F →L[ℝ] ℝ).comp ((fderiv ℂ w q).restrictScalars ℝ)) q :=
    (Morse.reInner : F →L[ℝ] F →L[ℝ] ℝ).hasFDerivAt.comp q hwq
  have hD : HasFDerivAt (fderiv ℂ w) (fderiv ℂ (fderiv ℂ w) q) q :=
    ((hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hd : HasFDerivAt (fun z => (fderiv ℂ w z).restrictScalars ℝ)
      ((ContinuousLinearMap.restrictScalarsL ℂ V F ℝ ℝ).comp
        ((fderiv ℂ (fderiv ℂ w) q).restrictScalars ℝ)) q :=
    (ContinuousLinearMap.restrictScalarsL ℂ V F ℝ ℝ).hasFDerivAt.comp q (hD.restrictScalars ℝ)
  have h3 : HasFDerivAt (fun z => (2 : ℝ) • (Morse.reInner (w z - p)).comp
      ((fderiv ℂ w z).restrictScalars ℝ)) _ q := (hc.clm_comp hd).const_smul (2 : ℝ)
  rw [Morse.hessian, h2.fderiv_eq, h3.fderiv]
  simp
  ring

#rt_check RoundTrip.V5_6.B_to_A [Morse.hessian_normSq_sub_holomorphic]
#rt_overlap RoundTrip.V5_6.B_to_A [Morse.hessian_normSq_sub_holomorphic]

end RoundTrip.V5_6
