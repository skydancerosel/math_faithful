import Morse
import RoundTrip.Check
import RoundTrip.Blind.V4_6

open Module Function Polynomial
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V4_6

/-- The project's statement: the two listed theorems (`tanSpace`, `shapeOp`,
`principalCurvatures` are definitions); no universe parameters. -/
def A : Prop :=
  type_of% @Morse.isSymmetric_shapeOp ∧
  type_of% @Morse.finrank_eigenspace_shapeOp

theorem A_holds : A := ⟨@Morse.isSymmetric_shapeOp, @Morse.finrank_eigenspace_shapeOp⟩

/-- `A` with the proof `isSymmetric_shapeOp hM p v` hidden in `principalCurvatures` replaced by an
arbitrary proof `h` (same statement by proof irrelevance, `A_iff_A'`); `#rt_check` follows the
bodies of definitions, so B ⇒ A is checked on `A'`. -/
def A' : Prop :=
  type_of% @Morse.isSymmetric_shapeOp ∧
  ∀ {n k w : ℕ} {M : Set (Rn n)} (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn n) (Rn k) (Rn w) M)
    (p : M) (v : Rn n)
    (h : (Morse.shapeOp hM p v : Morse.tanSpace hM p →ₗ[ℝ] Morse.tanSpace hM p).IsSymmetric)
    (K : ℝ),
    finrank ℝ (Module.End.eigenspace (Morse.shapeOp hM p v : Module.End ℝ (Morse.tanSpace hM p)) K) =
      (Finset.univ.filter fun i => h.eigenvalues (Morse.finrank_tanSpace hM p) i = K).card

theorem A_iff_A' : A ↔ A' :=
  ⟨fun h ↦ ⟨h.1, fun hM p v _ K ↦ h.2 hM p v K⟩,
    fun h ↦ ⟨h.1, fun hM p v K ↦ h.2 hM p v (h.1 hM p v) K⟩⟩

section Calc

variable {k n : ℕ}

lemma d2x_eq {x : Rn k → Rn n} {u : Rn k} (hx : DifferentiableAt ℝ (fderiv ℝ x) u) (i j : Fin k) :
    d2x x u i j = fderiv ℝ (fderiv ℝ x) u (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  unfold d2x dx
  rw [fderiv_clm_apply hx (differentiableAt_const _)]
  simp

/-- B's `(v · ℓ_ij)` is a symmetric matrix for a `C²` map (symmetry of second derivatives). -/
lemma sff_isHermitian {x : Rn k → Rn n} {U : Set (Rn k)} (hU : IsOpen U) (hx : ContDiffOn ℝ 2 x U)
    {u : Rn k} (hu : u ∈ U) (v : Rn n) : (sff x u v).IsHermitian := by
  have hxu : ContDiffAt ℝ 2 x u := hx.contDiffAt (hU.mem_nhds hu)
  have hd : DifferentiableAt ℝ (fderiv ℝ x) u :=
    (hxu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym := hxu.isSymmSndFDerivAt (by simp)
  ext i j
  simp only [Matrix.conjTranspose_apply, sff, ell, Matrix.of_apply, star_trivial]
  rw [d2x_eq hd, d2x_eq hd, hsym]

end Calc

/-- **B holds outright** (Mathlib's spectral theorem for the symmetric matrix `(v · ℓ_ij)`; the
normalization `g = 1` and `‖v‖ = 1` are not needed): the eigenvalue list exists, and two lists
with the same characteristic polynomial agree as multisets (its roots). -/
theorem B_holds : B := by
  intro k n x U hU hx u hu _ _ v _ _
  have hH := sff_isHermitian hU hx hu v
  refine ⟨⟨hH.eigenvalues, ?_⟩, fun K K' hK hK' ↦ ?_, fun r ↦ Iff.rfl⟩
  · unfold IsPrincCurv
    rw [hH.charpoly_eq]
    simp
  · have h1 : (Multiset.map K Finset.univ.val).map (fun a ↦ X - C a) =
        Multiset.map (fun i ↦ X - C (K i)) Finset.univ.val := by rw [Multiset.map_map]; rfl
    have h2 : (Multiset.map K' Finset.univ.val).map (fun a ↦ X - C a) =
        Multiset.map (fun i ↦ X - C (K' i)) Finset.univ.val := by rw [Multiset.map_map]; rfl
    rw [← roots_multiset_prod_X_sub_C (Multiset.map K Finset.univ.val),
      ← roots_multiset_prod_X_sub_C (Multiset.map K' Finset.univ.val), h1, h2]
    unfold IsPrincCurv at hK hK'
    simp only [Finset.prod_eq_multiset_prod] at hK hK'
    rw [← hK, ← hK']

theorem A'_to_B : A' → B := fun _ ↦ B_holds

theorem A_to_B : A → B := fun h ↦ A'_to_B (A_iff_A'.1 h)

/-- B ⇒ A, by re-proving `A'` (B, about an arbitrary parametrization with `g = 1`, has no
statement about the project's shape operator): symmetry from the project's `d2Param_symm`, the
multiplicities from Mathlib's `card_filter_eigenvalues_eq`. -/
theorem B_to_A' : B → A' := by
  intro _
  have hsym : type_of% @Morse.isSymmetric_shapeOp := by
    intro n k w M hM p v a b
    obtain ⟨ξ, rfl⟩ := (Morse.dParamEquiv hM p).surjective a
    obtain ⟨η, rfl⟩ := (Morse.dParamEquiv hM p).surjective b
    change ⟪Morse.shapeOp hM p v (Morse.dParamEquiv hM p ξ), Morse.dParamEquiv hM p η⟫ =
      ⟪Morse.dParamEquiv hM p ξ, Morse.shapeOp hM p v (Morse.dParamEquiv hM p η)⟫
    rw [Morse.inner_shapeOp_dParamEquiv, real_inner_comm, Morse.inner_shapeOp_dParamEquiv,
      Morse.secondFF_apply, Morse.secondFF_apply, Morse.d2Param_symm]
  exact ⟨hsym, fun hM p v h K ↦ (h.card_filter_eigenvalues_eq (Morse.finrank_tanSpace hM p) K).symm⟩

theorem B_to_A : B → A := fun h ↦ A_iff_A'.2 (B_to_A' h)

/-! ### Vocabulary check (not part of `A`): in the project's parametrization, if `g = 1` at `q`
and `v ⊥ T_qM`, the project's `principalCurvatures hM q v` are principal curvatures in B's sense
(eigenvalues with multiplicity of B's matrix `(v · ℓ_ij)`). -/

section Vocab

variable {N k w : ℕ} {M : Set (Rn N)} (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn N) (Rn k) (Rn w) M)

theorem tangSp_eq_range (q : M) :
    tangSp (Morse.xParam hM q) (Morse.uParam hM q) =
      LinearMap.range (Morse.dParam hM q : Rn k →ₗ[ℝ] Rn N) := by
  unfold tangSp
  rw [LinearMap.range_eq_map, ← (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.span_eq,
    Submodule.map_span, ← Set.range_comp]
  congr 1
  ext i
  simp [dx, Morse.dParam]

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

theorem isPrincCurv_principalCurvatures (q : M)
    (hg : gmat (Morse.xParam hM q) (Morse.uParam hM q) = 1) {v : Rn N}
    (hv : v ∈ (LinearMap.range (Morse.dParam hM q : Rn k →ₗ[ℝ] Rn N))ᗮ) :
    IsPrincCurv (Morse.xParam hM q) (Morse.uParam hM q) v (Morse.principalCurvatures hM q v) := by
  classical
  -- the basis `dx(eᵢ)` of `T_qM` is orthonormal when `g = 1`
  let e : Fin k → Morse.tanSpace hM q := fun i ↦ Morse.dParamEquiv hM q (EuclideanSpace.single i 1)
  have hon : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    have := congrFun (congrFun hg i) j
    simp only [gmat, Matrix.of_apply, Matrix.one_apply] at this
    rw [← this]
    rfl
  let b0 : Basis (Fin k) ℝ (Morse.tanSpace hM q) :=
    (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.map (Morse.dParamEquiv hM q)
  have hb0 : ⇑b0 = e := by
    ext i
    simp [b0, e]
  let b : OrthonormalBasis (Fin k) ℝ (Morse.tanSpace hM q) :=
    OrthonormalBasis.mk (hb0 ▸ hon) (by rw [b0.span_eq])
  have hb : ∀ i, b i = e i := fun i ↦ by simp [b, hb0]
  let S := (Morse.shapeOp hM q v : Module.End ℝ (Morse.tanSpace hM q))
  have hmat : sff (Morse.xParam hM q) (Morse.uParam hM q) v = LinearMap.toMatrix b.toBasis b.toBasis S := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, hb, hb, real_inner_comm]
    change _ = ⟪Morse.shapeOp hM q v (Morse.dParamEquiv hM q _), Morse.dParamEquiv hM q _⟫
    rw [Morse.inner_shapeOp_dParamEquiv, sff_eq_secondFF hM q hv, Morse.secondFF_apply,
      Morse.secondFF_apply, Morse.d2Param_symm]
  unfold IsPrincCurv
  rw [hmat, LinearMap.charpoly_toMatrix, (Morse.isSymmetric_shapeOp hM q v).charpoly_eq
    (Morse.finrank_tanSpace hM q)]
  rfl

end Vocab

#rt_check RoundTrip.V4_6.A'_to_B [Morse.isSymmetric_shapeOp, Morse.finrank_eigenspace_shapeOp]
#rt_check RoundTrip.V4_6.B_to_A' [Morse.isSymmetric_shapeOp, Morse.finrank_eigenspace_shapeOp]
#rt_overlap RoundTrip.V4_6.B_to_A' [Morse.isSymmetric_shapeOp, Morse.finrank_eigenspace_shapeOp]

end RoundTrip.V4_6
