import Morse
import RoundTrip.L2.Blind.Morse_IsCompatible

/-! Layer-2 check of `Morse.IsCompatible` (Milnor's Corollary 8.4 pointwise:
`X_x⟨Y, Y'⟩ = ⟨∇_{X_x} Y, Y'_x⟩ + ⟨Y_x, ∇_{X_x} Y'⟩` at every `x`, for all fields `X, Y, Y'`
merely differentiable at `x`) against the blind textbook definition (the same identity for every
tangent vector `v` at every `x`, but only for globally `C^∞` fields `Y, Y'`).

* `imp`: the project's condition implies the blind one, with no hypothesis (a smooth field is
  differentiable at `x`, and `v` extends to a field differentiable at `x`, `FiberBundle.extend`).
* `agree_of`: equivalent when the model `E` is finite-dimensional, `M` is Hausdorff and the metric
  is `C¹` (`IsContMDiffRiemannianBundle I 1`) — the textbook setting. Then both are Mathlib's
  `CovariantDerivative.IsMetricCompatible` (`Morse.isCompatible_iff_isMetricCompatible`), the
  vanishing of the tensor `derivMetricTensor`, whose value at `x` only depends on the values of
  the fields at `x` (tensoriality); every tangent vector is the value of a globally smooth field
  (a smooth bump function times `FiberBundle.extend`), so the blind condition already forces the
  tensor to vanish.
Outside these hypotheses (non-Hausdorff or infinite-dimensional models, non-`C¹` metrics, where
globally smooth fields need not realize every value) the blind condition may be weaker; no
counterexample is attempted. -/

namespace RoundTrip.L2.Morse_IsCompatible

open Bundle Set Filter
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (↑(⊤ : ℕ∞)) M] [Bundle.RiemannianBundle fun x : M => TangentSpace I x]

/-- The project's (pointwise) compatibility implies the blind one, with no hypothesis: a tangent
vector `v` at `x` extends to a field differentiable at `x` (`FiberBundle.extend`). -/
theorem imp (cov : CovariantDerivative I E (TangentSpace I (M := M))) :
    Morse.IsCompatible cov → T cov := by
  intro h Y Y' hY hY' x v
  have hX := FiberBundle.mdifferentiableAt_extend I E (V := TangentSpace I) (x := x) v
  have := h (FiberBundle.extend E v) Y Y' x hX (hY.mdifferentiableAt (by simp))
    (hY'.mdifferentiableAt (by simp))
  simp only [FiberBundle.extend_apply_self] at this
  exact this

omit [Bundle.RiemannianBundle fun x : M => TangentSpace I x] in
/-- On a Hausdorff manifold with finite-dimensional model, every tangent vector is the value of a
globally smooth vector field: a smooth bump function times `FiberBundle.extend`. -/
theorem exists_smooth_field [FiniteDimensional ℝ E] [T2Space M] (x : M) (v : TangentSpace I x) :
    ∃ Y : (y : M) → TangentSpace I y,
      ContMDiff I I.tangent ∞ (fun y => (⟨y, Y y⟩ : TangentBundle I M)) ∧ Y x = v := by
  obtain ⟨s, hs, hsm⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞) I E
    (V := TangentSpace I) v
  obtain ⟨ψ, -, hψ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.1 (interior_mem_nhds.2 hs)
  refine ⟨(ψ : M → ℝ) • FiberBundle.extend E v, ?_, ?_⟩
  · exact ContMDiffOn.smul_section_of_tsupport ψ.contMDiff.contMDiffOn isOpen_interior hψ
      (hsm.mono interior_subset)
  · simp

/-- **Agreement under hypotheses**: for a `C¹` metric on a Hausdorff manifold modelled on a
finite-dimensional space, the blind compatibility (for globally smooth fields) implies the
project's pointwise one (for fields differentiable at the point). -/
theorem agree_of [FiniteDimensional ℝ E] [T2Space M]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) :
    Morse.IsCompatible cov ↔ T cov := by
  refine ⟨imp cov, fun hT => ?_⟩
  rw [Morse.isCompatible_iff_isMetricCompatible]
  unfold CovariantDerivative.IsMetricCompatible
  ext x σ₀ τ₀ X₀
  obtain ⟨σ, hσ, rfl⟩ := exists_smooth_field x σ₀
  obtain ⟨τ, hτ, rfl⟩ := exists_smooth_field x τ₀
  have h := CovariantDerivative.derivMetricTensor_apply (F := E)
    (V := fun x : M ↦ TangentSpace I x) (cov := cov) (X := fun _ => X₀) x
    (hσ.mdifferentiableAt (by simp)) (hτ.mdifferentiableAt (by simp))
  simp only at h
  rw [h]
  change _ = (0 : ℝ)
  have h2 : (d% fun x => inner ℝ (σ x) (τ x)) x X₀ =
      inner ℝ (cov σ x X₀) (τ x) + inner ℝ (σ x) (cov τ x X₀) := hT σ τ hσ hτ x X₀
  rw [h2]
  ring

end RoundTrip.L2.Morse_IsCompatible
