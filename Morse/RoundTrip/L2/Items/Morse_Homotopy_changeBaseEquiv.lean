import Morse
import RoundTrip.L2.Blind.Morse_Homotopy_changeBaseEquiv
namespace RoundTrip.L2.Morse_Homotopy_changeBaseEquiv

open scoped unitInterval Topology Topology.Homotopy

variable {N : Type*} [Fintype N] {Y : Type*} [TopologicalSpace Y] {y₀ y₁ : Y}

/-- The blind radius `maxᵢ |2tᵢ - 1|` is twice the project's sup-distance `maxᵢ |tᵢ - 1/2|`. -/
theorem rad_eq (t : I^N) : rad t = 2 * Morse.Homotopy.cubeDist t := by
  have : ctr t = (2 : ℝ) • fun i => (t i : ℝ) - 1 / 2 := by
    funext i; simp only [ctr, Pi.smul_apply, smul_eq_mul]; ring
  rw [rad, this, norm_smul, Real.norm_two, Morse.Homotopy.cubeDist]

omit [Fintype N] in
/-- The blind rescaling by `2` is the project's rescaling of the cube of radius `1/4`. -/
theorem sh_eq (t : I^N) : sh ((1 : ℝ) / 2)⁻¹ t = Morse.Homotopy.cubeScale (1 / 4) t := by
  funext i
  simp only [sh, Morse.Homotopy.cubeScale]
  congr 1
  ring

/-- The two change-of-base-point loops are equal pointwise: `f` on the inner cube of sup-radius
`1/4` (blind radius `1/2`), rescaled by `2`, and `γ(4d - 1) = γ(2r - 1)` on the collar. -/
theorem changeBase_eq_chg (γ : Path y₀ y₁) (f : Ω^ N Y y₀) :
    Morse.Homotopy.changeBase γ f = chg γ f := by
  apply Subtype.ext
  ext t
  change Morse.Homotopy.changeBase γ f t = chgFun γ f t
  rw [Morse.Homotopy.changeBase_apply]
  simp only [chgFun, collar, rad_eq, sh_eq]
  by_cases h : Morse.Homotopy.cubeDist t ≤ 1 / 4
  · rw [if_pos h, if_pos (by linarith)]
  · rw [if_neg h, if_neg (by linarith)]
    congr 1
    ring

/-- **Agreement**: the project's change-of-base-point bijection along `γ` is the blind one
(same direction: `π_N(Y, y₀) ≃ π_N(Y, y₁)`, `γ` running from the inner cube to `∂I^N`). -/
theorem agree (γ : Path y₀ y₁) :
    Morse.Homotopy.changeBaseEquiv (N := N) γ = T γ := by
  refine Equiv.ext fun c => ?_
  induction c using Quotient.inductionOn with
  | h f => exact congrArg (Quotient.mk _) (changeBase_eq_chg γ f)

end RoundTrip.L2.Morse_Homotopy_changeBaseEquiv
