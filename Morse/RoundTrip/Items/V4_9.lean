import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V4_9

open Module Set Function Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V4_9

/-- The project's statement: the two listed theorems; no universe parameters. -/
def A : Prop :=
  type_of% @Morse.isFocalPointMult_add_smul_iff ∧
  type_of% @Morse.not_isFocalPoint_self

theorem A_holds : A := ⟨@Morse.isFocalPointMult_add_smul_iff, @Morse.not_isFocalPoint_self⟩

/-! ### B's focal multiplicity is the project's (structure independence) -/

section Bridge

variable {K d m : ℕ} {M : Set (Rn (K + 1))}
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)

include hM in
theorem hkw_of (q : M) : d + 1 + m = K + 1 :=
  Morse.slice_dim_add_eq_of_nonempty hM ⟨q.1, q.2⟩

noncomputable def cplx (h : d + 1 + m = K + 1) : Rn (K + 1) ≃L[ℝ] (Rn m × Rn (d + 1)) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [finrank_prod]; omega)

theorem nullE_eq_focalMult
    (hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) (Rn (K + 1)) (Rn (K + 1))
      (NSet hM)) (q : M) (e : Rn (K + 1)) :
    nullE hNN (q.1, e - q.1) = Morse.focalMult hM (hkw_of hM q) q e := by
  unfold nullE Morse.focalMult
  by_cases h : ((q : Rn (K + 1)), e - q) ∈ NSet hM
  · rw [dif_pos h, dif_pos (show ((q : Rn (K + 1)), e - q) ∈ Milnor.Problems.normalBundleSet hM
      from h)]
    exact (Glue.endpointNullity_eq_of_slice hM (hkw_of hM q) hNN (cplx (hkw_of hM q)) _).symm
  · rw [dif_neg h, dif_neg (show ((q : Rn (K + 1)), e - q) ∉ Milnor.Problems.normalBundleSet hM
      from h)]

theorem isFocalOfMult_iff
    (hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) (Rn (K + 1)) (Rn (K + 1))
      (NSet hM)) (q : M) (e : Rn (K + 1)) (μ : ℕ) :
    IsFocalOfMult hNN q.1 e μ ↔ Morse.IsFocalPointMult hM (hkw_of hM q) q e μ := by
  rw [Morse.isFocalPointMult_iff_focalMult, IsFocalOfMult, nullE_eq_focalMult]
  exact and_comm

theorem canonical (h : d + 1 + m = K + 1) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) (Rn (K + 1)) (Rn (K + 1)) (NSet hM) :=
  Glue.isSliceSubmanifold_congr_complement
    (Milnor.Problems.isSliceSubmanifold_normalBundle hM h) (cplx h).symm

end Bridge

/-! ### Matrix nullity = nullity of the bilinear form -/

section Matrix

variable {k : ℕ}

theorem apply_eq_sum (H : Rn k →L[ℝ] Rn k →L[ℝ] ℝ) (ξ η : Rn k) :
    H ξ η = ∑ i, ∑ j, ξ i * η j * H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr ξ,
    ← (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr η]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply,
    EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- **The nullity of a bilinear form on `ℝᵏ` is the nullity of its matrix.** -/
theorem nullity_eq_matNullity (H : Rn k →L[ℝ] Rn k →L[ℝ] ℝ) :
    Morse.nullity H =
      matNullity (Matrix.of fun i j => H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
  set A : Matrix (Fin k) (Fin k) ℝ :=
    Matrix.of fun i j => H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) with hA
  have key : Morse.nullSpace H =
      (LinearMap.ker A.transpose.mulVecLin).comap (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap := by
    ext ξ
    simp only [Morse.mem_nullSpace, Submodule.mem_comap, LinearMap.mem_ker,
      Matrix.mulVecLin_apply, LinearEquiv.coe_coe]
    constructor
    · intro h
      funext j
      have := h (EuclideanSpace.single j 1)
      rw [apply_eq_sum] at this
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hA, Matrix.of_apply,
        Pi.zero_apply]
      rw [← this]
      simp only [PiLp.single_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp [Finset.sum_ite_eq', mul_comm]
    · intro h η
      rw [apply_eq_sum, Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      have := congrFun h j
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hA, Matrix.of_apply,
        Pi.zero_apply] at this
      rw [show ∑ i, ξ i * η j * H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        η j * ∑ i, H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * ξ i by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ ↦ ?_; ring]
      convert mul_zero (η j) using 2
      exact this
  have h1 : Morse.nullity H = finrank ℝ (LinearMap.ker A.transpose.mulVecLin) := by
    rw [Morse.nullity, key, Submodule.comap_equiv_eq_map_symm]
    exact LinearEquiv.finrank_map_eq _ _
  rw [h1, matNullity]
  have r1 := LinearMap.finrank_range_add_finrank_ker A.transpose.mulVecLin
  have r2 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hr : A.transpose.rank = A.rank := Matrix.rank_transpose A
  rw [Matrix.rank] at hr
  rw [Matrix.rank] at hr
  omega

end Matrix

/-! ### The project's parametrization is a coordinate patch in B's sense -/

section Patch

variable {N k w : ℕ} {M : Set (Rn N)} (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn N) (Rn k) (Rn w) M)

theorem tangentSubspace_eq_range_dParam (q : M) :
    Morse.tangentSubspace hM q = LinearMap.range (Morse.dParam hM q : Rn k →ₗ[ℝ] Rn N) :=
  Morse.tangentSubspace_eq_range_fderiv_sliceParam hM _ (Milnor.Tub.mem_source hM q)

theorem tangSp_eq_range (q : M) :
    tangSp (Morse.xParam hM q) (Morse.uParam hM q) =
      LinearMap.range (Morse.dParam hM q : Rn k →ₗ[ℝ] Rn N) := by
  unfold tangSp
  rw [LinearMap.range_eq_map, ← (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.span_eq,
    Submodule.map_span, ← Set.range_comp]
  congr 1
  ext i
  simp [dx, Morse.dParam]

lemma d2x_eq {x : Rn k → Rn N} {u : Rn k} (hx : DifferentiableAt ℝ (fderiv ℝ x) u) (i j : Fin k) :
    d2x x u i j = fderiv ℝ (fderiv ℝ x) u (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  unfold d2x dx
  rw [fderiv_clm_apply hx (differentiableAt_const _)]
  simp

theorem sff_eq_secondFF (q : M) {v : Rn N}
    (hv : v ∈ (LinearMap.range (Morse.dParam hM q : Rn k →ₗ[ℝ] Rn N))ᗮ) (i j : Fin k) :
    sff (Morse.xParam hM q) (Morse.uParam hM q) v i j =
      Morse.secondFF hM q v (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (Morse.xParam hM q)) (Morse.uParam hM q) :=
    (Morse.hasFDerivAt_fderiv_xParam hM q).differentiableAt
  rw [← tangSp_eq_range] at hv
  simp only [sff, ell, Matrix.of_apply, Morse.secondFF_apply]
  rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 hv,
    d2x_eq hd]
  rfl

theorem gmat_eq_firstFF (q : M) (i j : Fin k) :
    gmat (Morse.xParam hM q) (Morse.uParam hM q) i j =
      Morse.firstFF hM q (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := rfl

/-- `xParam hM q` on `Ω` is a coordinate patch of `M` around `q`. -/
theorem isPatch_xParam {K d m : ℕ} {M : Set (Rn (K + 1))}
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M) (q : M) :
    IsPatch hM (Morse.xParam hM q) (Milnor.Tub.Ω hM q) := by
  refine ⟨Milnor.Tub.isOpen_Ω hM q, Milnor.Tub.contDiffOn_φ hM q, fun u hu ↦ ?_, ?_,
    fun _ ⟨u, hu, he⟩ ↦ he ▸ Milnor.Tub.φ_mem hM q hu, ?_⟩
  · have hinj := Milnor.Tub.injective_fderiv_φ hM q hu
    have := (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis.linearIndependent.map'
      (fderiv ℝ (Milnor.Tub.φ hM q) u : Rn (d + 1) →ₗ[ℝ] Rn (K + 1))
      (LinearMap.ker_eq_bot.2 hinj)
    have heq : dx (Morse.xParam hM q) u =
        ⇑(fderiv ℝ (Milnor.Tub.φ hM q) u : Rn (d + 1) →ₗ[ℝ] Rn (K + 1)) ∘
          ⇑(EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis := by
      funext i
      simp [dx]
    rw [heq]
    exact this
  · intro u hu u' hu' h
    have h1 := Milnor.Tub.c_φ hM q hu
    have h2 := Milnor.Tub.c_φ hM q hu'
    change Milnor.Tub.φ hM q u = Milnor.Tub.φ hM q u' at h
    rw [← h1, ← h2, h]
  · have : (Subtype.val : M → Rn (K + 1)) ⁻¹' (Morse.xParam hM q '' Milnor.Tub.Ω hM q) =
        (Subtype.val : M → Rn (K + 1)) ⁻¹' (Milnor.Tub.σ hM q).φ.source := by
      ext q'
      simp only [mem_preimage, mem_image]
      constructor
      · rintro ⟨u, hu, he⟩
        rw [← he]
        exact Milnor.Tub.φ_mem_source hM q hu
      · intro h
        exact ⟨_, Milnor.Tub.c_mem_Ω hM q h, Milnor.Tub.φ_c hM q h⟩
    rw [this]
    exact (Milnor.Tub.σ hM q).φ.open_source.preimage continuous_subtype_val

end Patch

/-! ### B ⇒ A -/

/-- `not_isFocalPoint_self`, re-proved from the project's `endpointNullity_eq_nullity` (V4_8) and
`nullity_firstFF_sub_zero_smul_secondFF` (B gives nothing here when `M` has codimension `0`: there
is no unit normal). -/
theorem not_self : type_of% @Morse.not_isFocalPoint_self := by
  rintro n k w M hM hkw q ⟨μ, h, hμ, hpos⟩
  rw [Morse.endpointNullity_eq_nullity] at hμ
  have hf : Morse.footPoint hM ⟨_, h⟩ = q := Subtype.ext rfl
  have h0 : Morse.firstFF hM (Morse.footPoint hM ⟨_, h⟩) -
      Morse.secondFF hM (Morse.footPoint hM ⟨_, h⟩) ((q : Rn n) - q) =
      Morse.firstFF hM q - (0 : ℝ) • Morse.secondFF hM q 0 := by
    rw [hf, sub_self]
    ext ξ η
    simp
  rw [h0, Morse.nullity_firstFF_sub_zero_smul_secondFF] at hμ
  omega

/-- **B ⇒ A.** For `dim M ≥ 1` and `v ≠ 0`: apply B to the project's parametrization `xParam`
(a coordinate patch, `isPatch_xParam`), the unit normal `v/‖v‖`, the parameter `t‖v‖`, and the
canonical structure on `N`; B's matrix is the project's `firstFF − t secondFF v`
(`gmat_eq_firstFF`, `sff_eq_secondFF`) and B's multiplicity the project's
(`Glue.endpointNullity_eq_of_slice`). `v = 0`, `dim M = 0` and `not_isFocalPoint_self` are
separate (no unit normal / nothing in B). -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, not_self⟩
  intro n k w M hM hkw q v hv t μ
  rcases k with _ | d
  · have h0 : Morse.nullity (Morse.firstFF hM q - t • Morse.secondFF hM q v) = 0 :=
      Submodule.finrank_eq_zero.2 (Subsingleton.elim _ _)
    rw [h0]
    constructor
    · rintro ⟨h, hμ, hpos⟩
      rw [Morse.endpointNullity_eq_nullity, Morse.nullity,
        Submodule.finrank_eq_zero.2 (Subsingleton.elim _ _)] at hμ
      omega
    · rintro ⟨h1, h2⟩
      omega
  obtain ⟨K, rfl⟩ : ∃ K, n = K + 1 := ⟨d + w, by omega⟩
  by_cases hv0 : v = 0
  · subst hv0
    rw [smul_zero, add_zero]
    have h0 : Morse.nullity (Morse.firstFF hM q - t • Morse.secondFF hM q 0) = 0 := by
      have : Morse.firstFF hM q - t • Morse.secondFF hM q 0 =
          Morse.firstFF hM q - (0 : ℝ) • Morse.secondFF hM q 0 := by
        ext ξ η
        simp
      rw [this, Morse.nullity_firstFF_sub_zero_smul_secondFF]
    rw [h0]
    exact ⟨fun h ↦ (not_self hM hkw q ⟨μ, h⟩).elim, fun ⟨h1, h2⟩ ↦ by omega⟩
  have hcpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  set v' : Rn (K + 1) := ‖v‖⁻¹ • v with hv'def
  have hv'1 : ‖v'‖ = 1 := by
    rw [hv'def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hcpos.ne']
  have hv'N : v' ∈ (Morse.tangentSubspace hM q)ᗮ := Submodule.smul_mem _ _ hv
  have hmem : (Morse.xParam hM q (Morse.uParam hM q), v') ∈ NSet hM := by
    rw [Morse.xParam_uParam]
    exact ⟨q.2, fun w hw ↦ (Submodule.mem_orthogonal' _ _).1 hv'N w hw⟩
  have hb := hB K d w M hM (canonical hM hkw) (Morse.xParam hM q) (Milnor.Tub.Ω hM q)
    (isPatch_xParam hM q) (Morse.uParam hM q) (Milnor.Tub.z₀_mem hM q) v' hv'1 hmem
    (t * ‖v‖) μ
  rw [Morse.xParam_uParam] at hb
  have he : (q : Rn (K + 1)) + (t * ‖v‖) • v' = q + t • v := by
    rw [hv'def, smul_smul, mul_assoc, mul_inv_cancel₀ hcpos.ne', mul_one]
  rw [he, isFocalOfMult_iff hM _ q] at hb
  have hv'r : v' ∈ (LinearMap.range (Morse.dParam hM q : Rn (d + 1) →ₗ[ℝ] Rn (K + 1)))ᗮ := by
    rw [← tangentSubspace_eq_range_dParam]
    exact hv'N
  have hmat : matNullity (gmat (Morse.xParam hM q) (Morse.uParam hM q) -
      (t * ‖v‖) • sff (Morse.xParam hM q) (Morse.uParam hM q) v') =
      Morse.nullity (Morse.firstFF hM q - t • Morse.secondFF hM q v) := by
    rw [nullity_eq_matNullity]
    congr 1
    ext i j
    rw [Matrix.sub_apply, Matrix.smul_apply, sff_eq_secondFF hM q hv'r, gmat_eq_firstFF]
    simp only [smul_eq_mul, Matrix.of_apply, sub_apply, FunLike.coe_smul, Pi.smul_apply,
      Morse.secondFF_apply, hv'def, inner_smul_left, RCLike.conj_to_real]
    field_simp
  rw [hmat] at hb
  exact hb.trans and_comm

/-! ### A ⇒ B: independence of the parametrization -/

theorem nullity_smul {k : ℕ} (H : Rn k →L[ℝ] Rn k →L[ℝ] ℝ) {c : ℝ} (hc : c ≠ 0) :
    Morse.nullity (c • H) = Morse.nullity H := by
  have : Morse.nullSpace (c • H) = Morse.nullSpace H := by
    ext ξ
    simp only [Morse.mem_nullSpace, smul_apply, smul_eq_mul, mul_eq_zero, hc,
      false_or]
  unfold Morse.nullity
  rw [this]

/-- **Milnor's matrix `(g_ij − t v·ℓ_ij)` has the same nullity in every coordinate patch**: in an
arbitrary patch `x` it has the nullity of the project's `firstFF − t secondFF v` (computed in
`xParam`). Both are half the Hessian of `L_p`, `p = q + t v`, at a critical point, in two
coordinate systems; the transition map `ψ = (σ.φ ∘ x).1` has invertible derivative, and at a
critical point the Hessian transforms by congruence (`Morse.hessian_comp`). -/
theorem matNullity_eq {K d m : ℕ} {M : Set (Rn (K + 1))}
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)
    {x : Rn (d + 1) → Rn (K + 1)} {U : Set (Rn (d + 1))} (hpatch : IsPatch hM x U)
    {u₀ : Rn (d + 1)} (hu₀ : u₀ ∈ U) (q : M) (hq : x u₀ = q) {v : Rn (K + 1)}
    (hv : v ∈ (Morse.tangentSubspace hM q)ᗮ) (t : ℝ) :
    matNullity (gmat x u₀ - t • sff x u₀ v) =
      Morse.nullity (Morse.firstFF hM q - t • Morse.secondFF hM q v) := by
  obtain ⟨hUo, hxs, hli, -, himg, -⟩ := hpatch
  set σ := Milnor.Tub.σ hM q
  set y := Morse.xParam hM q
  set u₁ := Morse.uParam hM q
  set p : Rn (K + 1) := q + t • v with hp
  set ψ : Rn (d + 1) → Rn (d + 1) := fun u => (σ.φ (x u)).1 with hψ
  have hxc : ContDiffAt ℝ ∞ x u₀ := hxs.contDiffAt (hUo.mem_nhds hu₀)
  have hsrc : x u₀ ∈ σ.φ.source := hq ▸ Milnor.Tub.mem_source hM q
  have hφc : ContDiffAt ℝ ∞ σ.φ (x u₀) :=
    (Milnor.Tub.contDiffOn_σφ hM q).contDiffAt (σ.φ.open_source.mem_nhds hsrc)
  have hψc : ContDiffAt ℝ ∞ ψ u₀ := contDiffAt_fst.comp _ (hφc.comp u₀ hxc)
  have hψu₀ : ψ u₀ = u₁ := by
    simp only [hψ, hq]
    rfl
  have hyc : ContDiffAt ℝ ∞ y (ψ u₀) := hψu₀ ▸ Morse.contDiffAt_xParam hM q
  -- `x = y ∘ ψ` near `u₀`
  have heq : y ∘ ψ =ᶠ[𝓝 u₀] x := by
    filter_upwards [hUo.mem_nhds hu₀,
      hxc.continuousAt.preimage_mem_nhds (σ.φ.open_source.mem_nhds hsrc)] with u hu hs
    exact Milnor.Tub.φ_c hM q (q := ⟨x u, himg ⟨u, hu, rfl⟩⟩) hs
  have hDx : fderiv ℝ x u₀ = (Morse.dParam hM q).comp (fderiv ℝ ψ u₀) := by
    rw [← heq.fderiv_eq, fderiv_comp u₀ (hyc.differentiableAt (by simp))
      (hψc.differentiableAt (by simp)), hψu₀]
    rfl
  -- `dx` is injective, hence so is `dψ`, which is then invertible
  have hinjx : Injective (fderiv ℝ x u₀) := by
    refine (injective_iff_map_eq_zero _).2 fun ξ hξ ↦ ?_
    have hξ' : ∑ i, ξ i • dx x u₀ i = 0 := by
      have := congrArg (fderiv ℝ x u₀)
        ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).sum_repr ξ)
      rw [map_sum] at this
      simp only [map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at this
      rw [← hξ, ← this]
      rfl
    have h0 := Fintype.linearIndependent_iff.1 (hli u₀ hu₀) _ hξ'
    ext i
    simp [h0 i]
  have hinjψ : Injective (fderiv ℝ ψ u₀) := by
    intro a b hab
    apply hinjx
    rw [hDx, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hab]
  let L : Rn (d + 1) ≃L[ℝ] Rn (d + 1) :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ ψ u₀ : Rn (d + 1) →ₗ[ℝ] Rn (d + 1))
      hinjψ).toContinuousLinearEquiv
  have hL : ∀ a, L a = fderiv ℝ ψ u₀ a := fun _ ↦ rfl
  -- `v` is normal to the `∂x/∂uⁱ`
  have hvr : v ∈ (LinearMap.range (Morse.dParam hM q : Rn (d + 1) →ₗ[ℝ] Rn (K + 1)))ᗮ := by
    rw [← tangentSubspace_eq_range_dParam]; exact hv
  have hvt : v ∈ (tangSp x u₀)ᗮ := by
    rw [tangSp, Submodule.mem_orthogonal]
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨l, rfl⟩ := hw
      have : dx x u₀ l ∈ LinearMap.range (Morse.dParam hM q : Rn (d + 1) →ₗ[ℝ] Rn (K + 1)) :=
        ⟨fderiv ℝ ψ u₀ (EuclideanSpace.single l 1), by
          simp only [dx, hDx]; rfl⟩
      exact (Submodule.mem_orthogonal _ _).1 hvr _ this
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  -- the Hessians
  have hfy : ContDiffAt ℝ 2 (fun z => ‖y z - p‖ ^ 2) (ψ u₀) :=
    ((Morse.contDiff_normSq_sub p).contDiffAt.of_le (by norm_cast)).comp _
      (hyc.of_le (by norm_cast))
  have hcrit : fderiv ℝ (fun z => ‖y z - p‖ ^ 2) (ψ u₀) = 0 := by
    ext ξ
    have hc : (fun z => ‖y z - p‖ ^ 2) = (fun w : Rn (K + 1) => ‖w - p‖ ^ 2) ∘ y := rfl
    rw [hc, fderiv_comp _ ((Morse.contDiff_normSq_sub p).differentiable (by simp) _)
      (hyc.differentiableAt (by simp)), ContinuousLinearMap.comp_apply,
      Morse.fderiv_normSq_sub_apply, hψu₀, show y u₁ = q from Morse.xParam_uParam hM q]
    have h1 : (q : Rn (K + 1)) - p = -(t • v) := by rw [hp]; abel
    have h2 : ⟪v, fderiv ℝ y u₁ ξ⟫ = 0 :=
      (Submodule.mem_orthogonal' _ _).1 hvr _ ⟨ξ, rfl⟩
    rw [h1, inner_neg_left, inner_smul_left, h2]
    simp
  have hHx : Morse.hessian (fun z => ‖x z - p‖ ^ 2) u₀ =
      (Morse.hessian (fun z => ‖y z - p‖ ^ 2) u₁).bilinearComp (L : Rn (d + 1) →L[ℝ] Rn (d + 1))
        (L : Rn (d + 1) →L[ℝ] Rn (d + 1)) := by
    have hev : (fun z => ‖x z - p‖ ^ 2) =ᶠ[𝓝 u₀] (fun z => ‖y z - p‖ ^ 2) ∘ ψ := by
      filter_upwards [heq] with u hu
      simp only [Function.comp_apply] at hu ⊢
      rw [hu]
    rw [Morse.hessian_congr hev]
    ext a b
    rw [Morse.hessian_comp hfy (hψc.of_le (by norm_cast)) hcrit, hψu₀]
    rfl
  have hHy : Morse.hessian (fun z => ‖y z - p‖ ^ 2) u₁ =
      (2 : ℝ) • (Morse.firstFF hM q - t • Morse.secondFF hM q v) := by
    rw [Morse.hessian_normSq_sub_xParam, hp, add_sub_cancel_left]
    congr 2
    ext ξ η
    simp [inner_smul_left]
  -- matrix entries of half the Hessian in `x`
  have hxc2 : ContDiffAt ℝ 2 x u₀ := hxc.of_le (by norm_cast)
  have hdd : DifferentiableAt ℝ (fderiv ℝ x) u₀ :=
    (hxc2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hmat : gmat x u₀ - t • sff x u₀ v = Matrix.of fun i j =>
      ((1 / 2 : ℝ) • Morse.hessian (fun z => ‖x z - p‖ ^ 2) u₀)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    ext i j
    have hsff : sff x u₀ v i j = ⟪v, d2x x u₀ i j⟫ := by
      simp only [sff, ell, Matrix.of_apply]
      rw [← Submodule.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.2 hvt]
    rw [Matrix.sub_apply, Matrix.smul_apply, hsff, Matrix.of_apply,
      smul_apply, smul_apply,
      Morse.hessian_normSq_sub_comp hxc2 p, d2x_eq hdd, hq]
    have h1 : (q : Rn (K + 1)) - p = -(t • v) := by rw [hp]; abel
    rw [h1, inner_neg_right, inner_smul_right, real_inner_comm]
    simp only [gmat, Matrix.of_apply, dx, smul_eq_mul]
    ring
  rw [hmat, ← nullity_eq_matNullity, nullity_smul _ (by norm_num), hHx,
    Morse.nullity_bilinearComp, hHy, nullity_smul _ (by norm_num)]

/-- **A ⇒ B.** B's multiplicity is the project's (`Glue.endpointNullity_eq_of_slice`); then A's
`isFocalPointMult_add_smul_iff` computes it as the nullity of `firstFF − t secondFF v` in the
project's parametrization, which is B's matrix nullity in the arbitrary patch `x`
(`matNullity_eq`). -/
theorem A_to_B : A → B := by
  intro hA K d m M hM hNN x U hpatch u₀ hu₀ v _ hmem t μ
  let q : M := ⟨x u₀, hpatch.2.2.2.2.1 ⟨u₀, hu₀, rfl⟩⟩
  obtain ⟨hq', hvN⟩ := hmem
  have hv : v ∈ (Morse.tangentSubspace hM q)ᗮ :=
    (Submodule.mem_orthogonal' _ _).2 fun w hw ↦ hvN w hw
  have h1 := isFocalOfMult_iff hM hNN q (q.1 + t • v) μ
  have h2 := hA.1 hM (hkw_of hM q) q hv t μ
  change IsFocalOfMult hNN q.1 (q.1 + t • v) μ ↔ _
  rw [h1, h2, matNullity_eq hM hpatch hu₀ q rfl hv t]
  exact and_comm

#rt_check RoundTrip.V4_9.A_to_B [Morse.isFocalPointMult_add_smul_iff, Morse.not_isFocalPoint_self]
#rt_check RoundTrip.V4_9.B_to_A [Morse.isFocalPointMult_add_smul_iff, Morse.not_isFocalPoint_self]
#rt_overlap RoundTrip.V4_9.B_to_A [Morse.isFocalPointMult_add_smul_iff,
  Morse.not_isFocalPoint_self]

end RoundTrip.V4_9
