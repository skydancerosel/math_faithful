import Milnor.Chapter7.Pontryagin

/-!
# The adjoint and pseudo-inverse in `ℝᵏ × ℝ`

`ℝᵏ × ℝ` with the product norm is not an inner product space in Mathlib, so the adjoint of a
linear map `A : ℝᵏ × ℝ → ℝᵖ` with respect to the inner product
`ipXR (a, s) (b, t) = ⟪a, b⟫ + s t` is written down by hand: `adjXR A c = (A₁^* c, A₂^* c)` with
`A₁ = A ∘ inl`, `A₂ = A ∘ inr`.  The pseudo-inverse `pinvXR A = adjXR A ∘ (A ∘ adjXR A)⁻¹` then
has the same properties as `pinv` in the Euclidean case.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Framed

variable {k p : ℕ}

theorem real_inner_mul (x y : ℝ) : ⟪x, y⟫ = x * y := by simp [inner, mul_comm]

/-- The adjoint with respect to `ipXR`. -/
def adjXR (A : EuclideanSpace ℝ (Fin k) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin k) × ℝ :=
  (ContinuousLinearMap.adjoint (A.comp (ContinuousLinearMap.inl ℝ _ _))).prod
    (ContinuousLinearMap.adjoint (A.comp (ContinuousLinearMap.inr ℝ _ _)))

theorem ipXR_adjXR (A : EuclideanSpace ℝ (Fin k) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin p))
    (c : EuclideanSpace ℝ (Fin p)) (v : EuclideanSpace ℝ (Fin k) × ℝ) :
    ipXR (adjXR A c) v = ⟪c, A v⟫ := by
  unfold ipXR adjXR
  simp only [ContinuousLinearMap.prod_apply]
  have hv : v = (v.1, 0) + (0, v.2) := by simp
  have h1 : ⟪ContinuousLinearMap.adjoint (A.comp (ContinuousLinearMap.inl ℝ _ _)) c, v.1⟫ =
      ⟪c, A (v.1, 0)⟫ := by
    rw [ContinuousLinearMap.adjoint_inner_left]; rfl
  have h2 : ContinuousLinearMap.adjoint (A.comp (ContinuousLinearMap.inr ℝ _ _)) c * v.2 =
      ⟪c, A (0, v.2)⟫ := by
    rw [← real_inner_mul, ContinuousLinearMap.adjoint_inner_left]; rfl
  rw [h1, h2, ← inner_add_right, ← map_add, ← hv]

/-- `adjXR` as a linear map in `A`. -/
def adjXRLin : (EuclideanSpace ℝ (Fin k) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin p)) →ₗ[ℝ]
    (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin k) × ℝ) where
  toFun := adjXR
  map_add' A B := by
    unfold adjXR
    simp only [ContinuousLinearMap.add_comp, map_add]
    ext c <;> simp
  map_smul' r A := by
    unfold adjXR
    simp only [ContinuousLinearMap.smul_comp, RingHom.id_apply]
    have h1 : ContinuousLinearMap.adjoint (r • A.comp (ContinuousLinearMap.inl ℝ _ _)) =
        r • ContinuousLinearMap.adjoint (A.comp (ContinuousLinearMap.inl ℝ _ _)) := by
      simpa using map_smulₛₗ ContinuousLinearMap.adjoint r (A.comp (ContinuousLinearMap.inl ℝ _ _))
    have h2 : ContinuousLinearMap.adjoint (r • A.comp (ContinuousLinearMap.inr ℝ _ _)) =
        r • ContinuousLinearMap.adjoint (A.comp (ContinuousLinearMap.inr ℝ _ _)) := by
      simpa using map_smulₛₗ ContinuousLinearMap.adjoint r (A.comp (ContinuousLinearMap.inr ℝ _ _))
    rw [h1, h2]
    ext c <;> simp

/-- `adjXR` is a continuous linear map in `A`. -/
def adjXRL : (EuclideanSpace ℝ (Fin k) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin p)) →L[ℝ]
    (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin k) × ℝ) :=
  (adjXRLin (k := k) (p := p)).toContinuousLinearMap

@[simp] theorem adjXRL_apply (A : EuclideanSpace ℝ (Fin k) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin p)) :
    adjXRL A = adjXR A := rfl

/-! ### The pseudo-inverse -/

theorem ipXR_self_nonneg (v : EuclideanSpace ℝ (Fin k) × ℝ) : 0 ≤ ipXR v v := by
  unfold ipXR
  exact add_nonneg real_inner_self_nonneg (mul_self_nonneg _)

theorem ipXR_self_eq_zero {v : EuclideanSpace ℝ (Fin k) × ℝ} (h : ipXR v v = 0) : v = 0 := by
  unfold ipXR at h
  have h1 : ⟪v.1, v.1⟫ = 0 := by nlinarith [real_inner_self_nonneg (x := v.1), mul_self_nonneg v.2]
  have h2 : v.2 * v.2 = 0 := by nlinarith [real_inner_self_nonneg (x := v.1), mul_self_nonneg v.2]
  have h3 : v.1 = 0 := inner_self_eq_zero.1 h1
  have h4 : v.2 = 0 := mul_self_eq_zero.1 h2
  exact Prod.ext h3 h4

/-- `A ∘ adjXR A` is a unit when `A` is surjective. -/
theorem isUnit_comp_adjXR {A : EuclideanSpace ℝ (Fin k) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin p)}
    (hA : Surjective A) : IsUnit (A.comp (adjXR A)) := by
  have hinj : Injective (A.comp (adjXR A)) := by
    refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
    have h1 : ipXR (adjXR A c) (adjXR A c) = 0 := by
      rw [ipXR_adjXR]
      simp only [ContinuousLinearMap.comp_apply] at hc
      rw [hc, inner_zero_right]
    have h2 : adjXR A c = 0 := ipXR_self_eq_zero h1
    obtain ⟨v, rfl⟩ := hA c
    have h3 : ⟪A v, A v⟫ = 0 := by
      rw [← ipXR_adjXR, h2]
      simp [ipXR]
    exact inner_self_eq_zero.1 h3
  have hsurj : Surjective (A.comp (adjXR A)) :=
    LinearMap.injective_iff_surjective (f := (A.comp (adjXR A)).toLinearMap) |>.1 hinj
  exact ⟨(ContinuousLinearEquiv.ofBijective (A.comp (adjXR A))
    (LinearMap.ker_eq_bot.2 hinj) (LinearMap.range_eq_top.2 hsurj)).toUnit, rfl⟩

/-- The pseudo-inverse `adjXR A ∘ (A ∘ adjXR A)⁻¹`. -/
def pinvXR (A : EuclideanSpace ℝ (Fin k) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin k) × ℝ :=
  (adjXR A).comp (Ring.inverse (A.comp (adjXR A)))

theorem comp_pinvXR {A : EuclideanSpace ℝ (Fin k) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin p)}
    (hA : Surjective A) (c : EuclideanSpace ℝ (Fin p)) : A (pinvXR A c) = c := by
  obtain ⟨u, hu⟩ := isUnit_comp_adjXR hA
  have : A (pinvXR A c) = (A.comp (adjXR A)) (Ring.inverse (A.comp (adjXR A)) c) := rfl
  rw [this, ← hu, Ring.inverse_unit, ← ContinuousLinearMap.mul_apply, u.mul_inv,
    ContinuousLinearMap.one_apply]

theorem ipXR_pinvXR_eq_zero (A : EuclideanSpace ℝ (Fin k) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin p))
    (c : EuclideanSpace ℝ (Fin p)) {v : EuclideanSpace ℝ (Fin k) × ℝ} (hv : A v = 0) :
    ipXR (pinvXR A c) v = 0 := by
  unfold pinvXR
  rw [ContinuousLinearMap.comp_apply, ipXR_adjXR, hv, inner_zero_right]

/-- When `A` does not involve the `ℝ`-direction, the pseudo-inverse is the Euclidean one. -/
theorem pinvXR_comp_fst (B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (c : EuclideanSpace ℝ (Fin p)) :
    pinvXR (B.comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) ℝ)) c = (pinv B c, 0) := by
  have h1 : adjXR (B.comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) ℝ)) =
      (ContinuousLinearMap.adjoint B).prod (0 : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ) := by
    unfold adjXR
    have e1 : (B.comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) ℝ)).comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin k)) ℝ) = B := by
      ext v; simp
    have e2 : (B.comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) ℝ)).comp (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) ℝ) = 0 := by
      ext v; simp
    rw [e1, e2, map_zero]
  have h2 : (B.comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) ℝ)).comp (adjXR (B.comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) ℝ))) =
      B.comp (ContinuousLinearMap.adjoint B) := by
    rw [h1]; ext c; simp
  unfold pinvXR pinv
  rw [h2, h1]
  ext <;> simp

end Framed

end Milnor
