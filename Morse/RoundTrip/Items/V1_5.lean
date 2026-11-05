import Morse
import RoundTrip.Check
import RoundTrip.Blind.V1_5

open scoped ContDiff Manifold Matrix

namespace RoundTrip.V1_5

/-- The project's statement: the types of the listed theorems (`IsSmoothCoord` is vocabulary),
universes instantiated at `0`. -/
def A : Prop :=
  (type_of% @Morse.hessian_comp.{0, 0}) ∧
  (type_of% @Morse.isSmoothCoord_iff_mem_maximalAtlas.{0, 0}) ∧
  (type_of% @Morse.IsSmoothCoord.isCriticalPointM_iff_forall_partial.{0, 0}) ∧
  (type_of% @Morse.IsSmoothCoord.hessian_comp_symm.{0, 0, 0}) ∧
  (type_of% @Morse.IsSmoothCoord.isNondegenerate_iff.{0, 0, 0}) ∧
  (type_of% @Morse.IsSmoothCoord.index_eq.{0, 0, 0}) ∧
  (type_of% @Morse.IsSmoothCoord.nullity_eq.{0, 0, 0}) ∧
  (type_of% @Morse.IsSmoothCoord.isNondegenerate_iff_det_ne_zero.{0, 0})

theorem A_holds : A :=
  ⟨@Morse.hessian_comp.{0, 0}, @Morse.isSmoothCoord_iff_mem_maximalAtlas.{0, 0},
    @Morse.IsSmoothCoord.isCriticalPointM_iff_forall_partial.{0, 0},
    @Morse.IsSmoothCoord.hessian_comp_symm.{0, 0, 0}, @Morse.IsSmoothCoord.isNondegenerate_iff.{0, 0, 0},
    @Morse.IsSmoothCoord.index_eq.{0, 0, 0}, @Morse.IsSmoothCoord.nullity_eq.{0, 0, 0},
    @Morse.IsSmoothCoord.isNondegenerate_iff_det_ne_zero.{0, 0}⟩

section Glue

variable {n : ℕ}

theorem eq_sum_basis (v : Fin n → ℝ) : v = ∑ i, v i • (Pi.single i 1 : Fin n → ℝ) := by
  conv_lhs => rw [← (Pi.basisFun ℝ (Fin n)).sum_repr v]
  simp

/-- The bilinear form of the matrix `H(eᵢ, eⱼ)` is `H`. -/
theorem dot_mulVec_eq (H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (v w : Fin n → ℝ) :
    v ⬝ᵥ ((Matrix.of fun i j => H (Pi.single i 1) (Pi.single j 1)).mulVec w) = H v w := by
  conv_rhs => rw [eq_sum_basis v, eq_sum_basis w]
  simp [map_sum, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm]
  exact Finset.sum_comm

/-- The blind Hessian matrix is the matrix of the project's Hessian (for `f` of class `C²` near
the point). -/
theorem hmat_eq {f : (Fin n → ℝ) → ℝ} {p : Fin n → ℝ} (hf : ContDiffAt ℝ 2 f p) :
    hmat f p = Matrix.of fun i j => Morse.hessian f p (Pi.single i 1) (Pi.single j 1) := by
  ext i j
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  simp only [hmat, Matrix.of_apply]
  show fderiv ℝ (fun x => fderiv ℝ f x (Pi.single j 1)) p (Pi.single i 1) = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp [Morse.hessian]

/-- Non-degeneracy is invariant under pulling back by a linear bijection. -/
theorem isNondegenerate_comp_iff {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (H : E₂ →L[ℝ] E₂ →L[ℝ] ℝ)
    (H' : E₁ →L[ℝ] E₁ →L[ℝ] ℝ) (L : E₁ →L[ℝ] E₂) (hL : Function.Bijective L)
    (hH : ∀ v w, H' v w = H (L v) (L w)) :
    Morse.IsNondegenerate H' ↔ Morse.IsNondegenerate H := by
  rw [Morse.isNondegenerate_iff, Morse.isNondegenerate_iff]
  constructor
  · intro h u hu
    obtain ⟨v, rfl⟩ := hL.2 u
    rw [h v fun w => by rw [hH]; exact hu _, map_zero]
  · intro h v hv
    have : L v = 0 := h (L v) fun w' => by
      obtain ⟨w, rfl⟩ := hL.2 w'
      rw [← hH]; exact hv w
    exact hL.1 (this.trans (map_zero L).symm)

end Glue

theorem A_to_B : A → B := by
  intro hA
  refine ⟨fun n f φ q hf hφ hL hcrit => ?_, fun n M _ _ _ _ f p hf hcrit v w => ?_⟩
  · -- (1) coordinate independence of non-degeneracy
    have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_cast)
    have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
    rw [hmat_eq (hf2.comp hφ2).contDiffAt, hmat_eq hf2.contDiffAt,
      ← Morse.isNondegenerate_hessian_iff_det_ne_zero (hf2.comp hφ2).contDiffAt,
      ← Morse.isNondegenerate_hessian_iff_det_ne_zero hf2.contDiffAt]
    exact isNondegenerate_comp_iff _ _ (fderiv ℝ φ q) hL
      (hA.1 hf2.contDiffAt hφ2.contDiffAt hcrit)
  · -- (2) the coordinate Hessian matrix represents `f_**`
    have hy : Morse.IsSmoothCoord (Fin n → ℝ) (chartAt (Fin n → ℝ) p) :=
      (hA.2.1 _).2 (IsManifold.chart_mem_maximalAtlas p)
    have hp := mem_chart_source (Fin n → ℝ) p
    -- the derivative of the preferred chart at `p` is the identity
    have hD : ∀ u, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (chartAt (Fin n → ℝ) p) p u = u := by
      intro u
      rw [hy.mfderiv_eq hp]
      have hev : (chartAt (Fin n → ℝ) p ∘ (chartAt (Fin n → ℝ) p).symm) =ᶠ[nhds
          (chartAt (Fin n → ℝ) p p)] id :=
        (chartAt (Fin n → ℝ) p).eventually_right_inverse
          ((chartAt (Fin n → ℝ) p).map_source hp)
      rw [hev.fderiv_eq, fderiv_id]
      rfl
    have h2 := Morse.contDiffAt_comp_chartAt_symm (hf.contMDiffAt.of_le (by norm_cast)) (p := p)
    have h3 := dot_mulVec_eq (Morse.hessian (f ∘ (chartAt (Fin n → ℝ) p).symm)
      (chartAt (Fin n → ℝ) p p)) v w
    rw [← hmat_eq h2, ← Morse.hessianM_eq_chartAt] at h3
    rw [← h3]
    have key : ∀ g : M → (Fin n → ℝ), g = ⇑(chartAt (Fin n → ℝ) p) →
        ∀ u : Fin n → ℝ, (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) g p u : Fin n → ℝ) = u := by
      rintro g rfl
      exact hD
    have hv := key _ (Morse.extChartAt_self_coe p)
    rw [hv v, hv w, Morse.extChartAt_self_coe_symm, Morse.extChartAt_self_coe]

#rt_check RoundTrip.V1_5.A_to_B [Morse.hessian_comp, Morse.isSmoothCoord_iff_mem_maximalAtlas,
  Morse.IsSmoothCoord.isCriticalPointM_iff_forall_partial, Morse.IsSmoothCoord.hessian_comp_symm,
  Morse.IsSmoothCoord.isNondegenerate_iff, Morse.IsSmoothCoord.index_eq,
  Morse.IsSmoothCoord.nullity_eq, Morse.IsSmoothCoord.isNondegenerate_iff_det_ne_zero]

end RoundTrip.V1_5
