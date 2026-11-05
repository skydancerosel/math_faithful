import Milnor.Chapter7.Compose

/-!
# Identifying the Pontryagin framing

For a regular value `y` of `f : M → Sᵖ` and `x ∈ f⁻¹(y)`, the kernel of the derivative
`A = dF̃_x` of the extension is `T_xN ⊕ (T_xM)ᗮ` (by a dimension count), so a vector `v`
tangent to `M`, orthogonal to `N = f⁻¹(y)` and with `A v = bᵢ` is exactly the framing vector
`f^*bᵢ(x) = A^*(A A^*)⁻¹ bᵢ`.  This is what makes the map constructed in the product
neighbourhood theorem have the prescribed framing.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

/-- `range A^* = (ker A)ᗮ`. -/
theorem range_adjoint_eq {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →L[ℝ] F) :
    LinearMap.range (ContinuousLinearMap.adjoint A : F →ₗ[ℝ] E) =
      (LinearMap.ker (A : E →ₗ[ℝ] F))ᗮ := by
  have h : (LinearMap.range (ContinuousLinearMap.adjoint A : F →ₗ[ℝ] E))ᗮ =
      LinearMap.ker (A : E →ₗ[ℝ] F) := by
    ext w
    rw [Submodule.mem_orthogonal, LinearMap.mem_ker]
    constructor
    · intro hw
      have := hw (ContinuousLinearMap.adjoint A (A w)) ⟨A w, rfl⟩
      rw [ContinuousLinearMap.adjoint_inner_left] at this
      show A w = 0
      exact inner_self_eq_zero.1 this
    · rintro hw _ ⟨c, rfl⟩
      show ⟪ContinuousLinearMap.adjoint A c, w⟫ = 0
      rw [ContinuousLinearMap.adjoint_inner_left]
      have hw' : A w = 0 := hw
      rw [hw', inner_zero_right]
  rw [← h, Submodule.orthogonal_orthogonal]

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) (hMc : IsCompact M) (hne : M.Nonempty)
  {p n : ℕ} {f : M → Sph p}
  (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
  {y : Sph p}
  (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
  (hnp : n + p = m)

/-- The tangent space of `M` has dimension `m`. -/
theorem finrank_tangentM (x : M) : finrank ℝ (tangentM hM x) = m := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  unfold tangentM
  have hinj : Injective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x) := injective_mfderiv_val hM x
  rw [LinearMap.finrank_range_of_inj hinj]
  simp

include hf hy in
/-- The tangent space of `f⁻¹(y)` has dimension `n`. -/
theorem finrank_tangentN_level (q : f ⁻¹' {y}) :
    finrank ℝ (tangentN hM (isSliceSubmanifold_level hM hf hy hnp) q) = n := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hN := isSliceSubmanifold_level hM hf hy hnp
  letI := hN.chartedSpace
  haveI := hN.isManifold
  unfold tangentN
  have h1 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))) (hM.contMDiff_val.mdifferentiableAt (by simp) :
      MDifferentiableAt _ _ (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) q.1)
  have h2 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (hN.contMDiff_val.mdifferentiableAt (by simp) :
      MDifferentiableAt _ _ (Subtype.val : f ⁻¹' {y} → M) q)
  have h3 := HasMFDerivAt.mfd_eq (h1.comp q h2)
  have h4 : ((Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) ∘ (Subtype.val : f ⁻¹' {y} → M)) =
      fun r : f ⁻¹' {y} => (r.1.1 : EuclideanSpace ℝ (Fin (K + 1))) := rfl
  rw [h4] at h3
  have h3' : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (fun r : f ⁻¹' {y} => (r.1.1 : EuclideanSpace ℝ (Fin (K + 1)))) q =
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) q.1).comp
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (Subtype.val : f ⁻¹' {y} → M) q) := h3
  rw [h3']
  have hinj : Injective ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) q.1).comp
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (Subtype.val : f ⁻¹' {y} → M) q)) :=
    (injective_mfderiv_val hM q.1).comp (injective_mfderiv_val hN q)
  rw [LinearMap.finrank_range_of_inj hinj]
  simp

include hf hy in
/-- **The kernel of `dF̃_x`** at `x ∈ f⁻¹(y)` is `T_xN ⊕ (T_xM)ᗮ`. -/
theorem ker_At_eq (q : f ⁻¹' {y}) :
    LinearMap.ker (At hM hMc hne f y q.1.1 :
      EuclideanSpace ℝ (Fin (K + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) =
      tangentN hM (isSliceSubmanifold_level hM hf hy hnp) q ⊔ (tangentM hM q.1)ᗮ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hsrc : f ⟨q.1.1, q.1.2⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source := by
    rw [Subtype.coe_eta]
    have : f q.1 = y := q.2
    rw [this]; exact mem_extChartAt_source y
  -- `⊇`
  have hle : tangentN hM (isSliceSubmanifold_level hM hf hy hnp) q ⊔ (tangentM hM q.1)ᗮ ≤
      LinearMap.ker (At hM hMc hne f y q.1.1 :
        EuclideanSpace ℝ (Fin (K + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) := by
    refine sup_le ?_ ?_
    · intro w hw
      rw [LinearMap.mem_ker]
      exact At_tangentN_eq_zero hM hMc hne hf hy hnp q hw
    · intro w hw
      rw [LinearMap.mem_ker]
      exact At_normal_eq_zero hM hMc hne hf q.1.2 hsrc
        (fun v hv => (Submodule.mem_orthogonal' _ _).1 hw v hv)
  -- dimension count
  have hsurj := surjective_At hM hMc hne hf hy q.1.2 q.2
  have hrank := LinearMap.finrank_range_add_finrank_ker (At hM hMc hne f y q.1.1 :
    EuclideanSpace ℝ (Fin (K + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, finrank_euclideanSpace_fin,
    finrank_euclideanSpace_fin] at hrank
  have hTN : tangentN hM (isSliceSubmanifold_level hM hf hy hnp) q ≤ tangentM hM q.1 := by
    -- the range of `d(val_M ∘ val_N)` is contained in the range of `d(val_M)`
    have hN := isSliceSubmanifold_level hM hf hy hnp
    letI := hN.chartedSpace
    haveI := hN.isManifold
    have h1 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))) (hM.contMDiff_val.mdifferentiableAt (by simp) :
        MDifferentiableAt _ _ (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) q.1)
    have h2 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (hN.contMDiff_val.mdifferentiableAt (by simp) :
        MDifferentiableAt _ _ (Subtype.val : f ⁻¹' {y} → M) q)
    have h3 := HasMFDerivAt.mfd_eq (h1.comp q h2)
    have h4 : ((Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) ∘ (Subtype.val : f ⁻¹' {y} → M)) =
        fun r : f ⁻¹' {y} => (r.1.1 : EuclideanSpace ℝ (Fin (K + 1))) := rfl
    rw [h4] at h3
    have h3' : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (fun r : f ⁻¹' {y} => (r.1.1 : EuclideanSpace ℝ (Fin (K + 1)))) q =
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
          (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) q.1).comp
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
          (Subtype.val : f ⁻¹' {y} → M) q) := h3
    unfold tangentN tangentM
    rw [h3', ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]
    exact LinearMap.map_le_range
  have hinf : tangentN hM (isSliceSubmanifold_level hM hf hy hnp) q ⊓ (tangentM hM q.1)ᗮ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have h1 : v ∈ tangentM hM q.1 := hTN hv.1
    have h2 : v ∈ (tangentM hM q.1)ᗮ := hv.2
    exact (Submodule.inf_orthogonal_eq_bot (tangentM hM q.1)).le ⟨h1, h2⟩
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (tangentN hM (isSliceSubmanifold_level hM hf hy hnp) q) (tangentM hM q.1)ᗮ
  rw [hinf, finrank_bot, add_zero, finrank_tangentN_level hM hf hy hnp q] at hsup
  have horth := Submodule.finrank_add_finrank_orthogonal (tangentM hM q.1)
  rw [finrank_tangentM hM, finrank_euclideanSpace_fin] at horth
  symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  omega

include hf hy in
/-- **The framing vector is determined**: a vector tangent to `M`, orthogonal to `f⁻¹(y)`, with
`dF̃_x v = bᵢ` is the Pontryagin framing vector `f^*bᵢ(x)`. -/
theorem pontV_eq_of (q : f ⁻¹' {y}) {v : EuclideanSpace ℝ (Fin (K + 1))}
    (hvT : v ∈ tangentM hM q.1)
    (hvN : ∀ w ∈ tangentN hM (isSliceSubmanifold_level hM hf hy hnp) q, ⟪v, w⟫ = 0)
    (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p)
    (hAv : At hM hMc hne f y q.1.1 v = b i) :
    pontV hM hMc hne f y b i q = v := by
  symm
  apply pinv_unique (surjective_At hM hMc hne hf hy q.1.2 q.2) _ hAv
  rw [range_adjoint_eq, ker_At_eq hM hMc hne hf hy hnp q, Submodule.mem_orthogonal]
  intro u hu
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hu
  rw [inner_add_left]
  have h1 : ⟪u₁, v⟫ = 0 := by rw [real_inner_comm]; exact hvN u₁ hu₁
  have h2 : ⟪u₂, v⟫ = 0 := Submodule.inner_left_of_mem_orthogonal hvT hu₂
  rw [h1, h2, add_zero]

end Framed

end Milnor
