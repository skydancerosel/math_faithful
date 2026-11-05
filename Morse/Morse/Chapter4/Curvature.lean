import Morse.Chapter4.Focal

/-!
Milnor, *Morse Theory*, §6, pp. 33–35 and 37–38.

# Principal curvatures: Lemma 6.3 and the index theorem for `L_p` (Lemma 6.9)

Setting and notation as in `Morse/Chapter4/NormalBundle.lean` and `Morse/Chapter4/Focal.lean`:
`M ⊆ ℝⁿ` is a slice submanifold of dimension `k`, `x = Morse.xParam hM q` Milnor's coordinates
near `q`, `g = Morse.firstFF hM q` and `ℓ_v = Morse.secondFF hM q v` the first and second
fundamental forms at `q`.

## Milnor's statements (paraphrased)

* (p. 34) Choose the coordinates so that `(g_ij)` is the identity at `q`; the eigenvalues
  `K₁, …, K_k` of `(v · ℓ_ij)` are the *principal curvatures* of `M` at `q` in the normal
  direction `v`, and the reciprocals of the nonzero ones the *principal radii of curvature*.
* **Lemma 6.3** (p. 34): the focal points of `(M, q)` along the normal line `q + tv` (`v` a unit
  normal) are the points `q + K_i⁻¹ v` with `K_i ≠ 0`; there are at most `k` of them, each
  counted with its multiplicity.  (Proof via Assertion 6.4: for `t ≠ 0`, `(g_ij − t v · ℓ_ij)` is
  singular iff `1/t` is an eigenvalue of `(v · ℓ_ij)`, with the same multiplicity.)
* **Lemma 6.9** (index theorem for `L_p`, p. 37): the index of `L_p` at a non-degenerate critical
  point `q` equals the number of focal points of `(M, q)` on the segment from `q` to `p`, each
  counted with its multiplicity.  (Proof, p. 38: the index of `2(g_ij − t v · ℓ_ij)` is its number
  of negative eigenvalues, which for `(g_ij)` the identity is the number of eigenvalues of
  `(v · ℓ_ij)` that are at least `1/t`; compare with Lemma 6.3.)

## How it is formalized

Instead of normalizing the coordinates we work on the tangent space `T_qM = range dx ⊆ ℝⁿ`
(`Morse.tanSpace hM q`), an inner product space isometric to `(ℝᵏ, g)` through `dx`
(`Morse.dParamEquiv`).  The second fundamental form transported to `T_qM` is represented by the
**shape operator** `S_v` (`Morse.shapeOp`, `⟪S_v a, b⟫ = ℓ_v(dx⁻¹ a, dx⁻¹ b)`), which is
self-adjoint (`Morse.isSymmetric_shapeOp`, from the symmetry of `∂²x/∂uⁱ∂uʲ`).  Its eigenvalues
are the **principal curvatures** (`Morse.principalCurvatures`, sorted, with multiplicities, from
Mathlib's spectral theorem); in coordinates with `g = I` at `q` they are Milnor's `K_i`, and in
general they are the eigenvalues of `g⁻¹(v · ℓ)`.

* `Morse.map_nullSpace_firstFF_sub_eq_eigenspace`: for `t ≠ 0`, `dx` maps the null space of
  `g − t ℓ_v` onto the eigenspace of `S_v` for the eigenvalue `1/t`;
* `Morse.focalMult` (the multiplicity of a point as a focal point, `0` if it is not one),
  `Morse.focalMult_add_smul`, `Morse.isFocalPoint_add_smul_iff`, `Morse.focalMult_add_inv_smul`
  (**Lemma 6.3**: the focal points on the normal line through `q` in the direction `v ⊥ T_qM` are
  the `q + K⁻¹ v`, `K ≠ 0` a principal curvature, with the multiplicity of `K`), and
  `Morse.sum_focalMult_add_smul_le` (at most `k` of them, counted with multiplicity);
* `Morse.index_firstFF_sub_secondFF`: the index of `g − ℓ_v` is the number of principal
  curvatures `> 1` (Sylvester's law of inertia in an orthonormal eigenbasis of `S_v`);
* `Morse.indexM_normSq_sub_eq_card` and `Morse.indexM_normSq_sub_eq_finsum_focalMult`
  (**Lemma 6.9**): the index of `L_p` at a critical point `q` is the number of principal
  curvatures `> 1` in the direction `p − q`; at a non-degenerate critical point it is the sum of
  the multiplicities of the points `q + t(p − q)`, `0 ≤ t ≤ 1`, as focal points of `(M, q)`.

## Gaps in Milnor's text

* **Principal curvatures are defined in special coordinates** (`g_ij(q) = δ_ij`), with no proof
  that such coordinates exist (a linear change of variables does it) or that the eigenvalues do
  not depend on them.  Here they are the eigenvalues of an operator on `T_qM`, which needs no
  normalization; that this operator does not depend on the parametrization is not needed and is
  not proved.
* **Multiplicities.**  "The multiplicity of `1/t` as an eigenvalue" is its multiplicity as a root
  of the characteristic polynomial; it equals the dimension of the eigenspace, which is what
  Assertion 6.4 produces, because the matrix is symmetric.  The formal statements use the
  dimension of the eigenspace.
* **"Eigenvalues which are `≥ 1/t`"** (p. 38): the index counts the eigenvalues `> 1/t`.
  Equality would make `p` a focal point of `(M, q)`, i.e. `q` degenerate (Lemma 6.5); this is
  where the non-degeneracy hypothesis of Lemma 6.9 enters, and with it `≥` and `>` agree.  The
  point `q` itself (`t = 0`) is never a focal point of `(M, q)`.
* **The case `p = q`** (`t = 0`, no unit normal): the index is `0` and the segment `{q}` contains
  no focal point; the formal statements cover it, with `v = p − q = 0`.
-/

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

namespace Morse

open Milnor.Problems (normalBundleSet normalSum isSliceSubmanifold_normalBundle)

variable {n k w : ℕ} {M : Set (𝔼 n)}
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M)

section Shape

/-- The tangent space `T_pM`, as the range of `dx` at `u_p`. -/
abbrev tanSpace (p : M) : Submodule ℝ (𝔼 n) := LinearMap.range (dParam hM p : 𝔼 k →ₗ[ℝ] 𝔼 n)

/-- `dx` as a linear isomorphism `ℝᵏ ≃ T_pM`. -/
def dParamEquiv (p : M) : 𝔼 k ≃ₗ[ℝ] tanSpace hM p :=
  LinearEquiv.ofInjective _ (injective_dParam hM p)

@[simp] theorem dParamEquiv_apply (p : M) (ξ : 𝔼 k) :
    (dParamEquiv hM p ξ : 𝔼 n) = dParam hM p ξ := rfl

theorem finrank_tanSpace (p : M) : finrank ℝ (tanSpace hM p) = k := by
  rw [← (dParamEquiv hM p).finrank_eq, finrank_euclideanSpace_fin]

theorem d2Param_symm (p : M) (ξ η : 𝔼 k) : d2Param hM p ξ η = d2Param hM p η ξ :=
  (((contDiffAt_xParam hM p).of_le (by norm_cast) : ContDiffAt ℝ 2 (xParam hM p)
    (uParam hM p)).isSymmSndFDerivAt (by simp)) ξ η

/-- The second fundamental form in the direction `v`, transported to `T_pM`:
`(a, b) ↦ ℓ_v(dx⁻¹ a, dx⁻¹ b)`. -/
def secondFFTan (p : M) (v : 𝔼 n) : tanSpace hM p →L[ℝ] tanSpace hM p →L[ℝ] ℝ :=
  (secondFF hM p v).bilinearComp
    ((dParamEquiv hM p).symm.toContinuousLinearEquiv : tanSpace hM p →L[ℝ] 𝔼 k)
    ((dParamEquiv hM p).symm.toContinuousLinearEquiv : tanSpace hM p →L[ℝ] 𝔼 k)

theorem secondFFTan_apply (p : M) (v : 𝔼 n) (ξ η : 𝔼 k) :
    secondFFTan hM p v (dParamEquiv hM p ξ) (dParamEquiv hM p η) = secondFF hM p v ξ η := by
  simp [secondFFTan]

/-- **The shape operator** (Weingarten map) of `M` at `p` in the direction `v`: the self-adjoint
endomorphism `S_v` of `T_pM` with `⟪S_v a, b⟫ = ℓ_v(a, b)`.  Its eigenvalues are the *principal
curvatures* of `M` at `p` in the direction `v` (Milnor, p. 34). -/
def shapeOp (p : M) (v : 𝔼 n) : tanSpace hM p →L[ℝ] tanSpace hM p :=
  InnerProductSpace.continuousLinearMapOfBilin (secondFFTan hM p v)

theorem inner_shapeOp (p : M) (v : 𝔼 n) (a b : tanSpace hM p) :
    ⟪shapeOp hM p v a, b⟫ = secondFFTan hM p v a b :=
  InnerProductSpace.continuousLinearMapOfBilin_apply _ a b

theorem inner_shapeOp_dParamEquiv (p : M) (v : 𝔼 n) (ξ η : 𝔼 k) :
    ⟪shapeOp hM p v (dParamEquiv hM p ξ), dParamEquiv hM p η⟫ = secondFF hM p v ξ η := by
  rw [inner_shapeOp, secondFFTan_apply]

theorem isSymmetric_shapeOp (p : M) (v : 𝔼 n) :
    (shapeOp hM p v : tanSpace hM p →ₗ[ℝ] tanSpace hM p).IsSymmetric := by
  intro a b
  obtain ⟨ξ, rfl⟩ := (dParamEquiv hM p).surjective a
  obtain ⟨η, rfl⟩ := (dParamEquiv hM p).surjective b
  change ⟪shapeOp hM p v (dParamEquiv hM p ξ), dParamEquiv hM p η⟫ =
    ⟪dParamEquiv hM p ξ, shapeOp hM p v (dParamEquiv hM p η)⟫
  rw [inner_shapeOp_dParamEquiv, real_inner_comm, inner_shapeOp_dParamEquiv, secondFF_apply,
    secondFF_apply, d2Param_symm]

end Shape

/-! ### Lemma 6.3 -/

section Lemma63

theorem inner_dParamEquiv (p : M) (ξ η : 𝔼 k) :
    ⟪dParamEquiv hM p ξ, dParamEquiv hM p η⟫ = firstFF hM p ξ η := rfl

theorem inner_smul_left_tanSpace (p : M) (t : ℝ) (a b : tanSpace hM p) :
    ⟪t • a, b⟫ = t * ⟪a, b⟫ := by
  rw [Submodule.coe_inner, Submodule.coe_smul, real_inner_smul_left, ← Submodule.coe_inner]

/-- `ξ` is in the null space of `g − t ℓ_v` iff `(1 − t S_v)(dx ξ) = 0`. -/
theorem mem_nullSpace_firstFF_sub_iff (p : M) (v : 𝔼 n) (t : ℝ) (ξ : 𝔼 k) :
    ξ ∈ nullSpace (firstFF hM p - t • secondFF hM p v) ↔
      dParamEquiv hM p ξ - t • shapeOp hM p v (dParamEquiv hM p ξ) = 0 := by
  have hinner : ∀ η, ⟪dParamEquiv hM p ξ - t • shapeOp hM p v (dParamEquiv hM p ξ),
      dParamEquiv hM p η⟫ = (firstFF hM p - t • secondFF hM p v) ξ η := fun η => by
    rw [inner_sub_left, inner_smul_left_tanSpace, inner_shapeOp_dParamEquiv, inner_dParamEquiv]
    simp only [FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [mem_nullSpace]
  constructor
  · intro h
    obtain ⟨η, hη⟩ := (dParamEquiv hM p).surjective
      (dParamEquiv hM p ξ - t • shapeOp hM p v (dParamEquiv hM p ξ))
    have := hinner η
    rw [h η, hη] at this
    exact inner_self_eq_zero.1 this
  · intro h η
    rw [← hinner, h, inner_zero_left]

/-- **The null space of `g − t ℓ_v` is the eigenspace of the shape operator for the eigenvalue
`1/t`** (Milnor, p. 35, for `t ≠ 0`), transported by `dx`. -/
theorem map_nullSpace_firstFF_sub_eq_eigenspace (p : M) (v : 𝔼 n) {t : ℝ} (ht : t ≠ 0) :
    (nullSpace (firstFF hM p - t • secondFF hM p v)).map
        (dParamEquiv hM p : 𝔼 k →ₗ[ℝ] tanSpace hM p) =
      Module.End.eigenspace (shapeOp hM p v : Module.End ℝ (tanSpace hM p)) t⁻¹ := by
  ext a
  obtain ⟨ξ, rfl⟩ := (dParamEquiv hM p).surjective a
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_nullSpace_firstFF_sub_iff,
    Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, sub_eq_zero]
  constructor
  · intro h
    calc shapeOp hM p v (dParamEquiv hM p ξ)
        = t⁻¹ • (t • shapeOp hM p v (dParamEquiv hM p ξ)) := by
          rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = t⁻¹ • dParamEquiv hM p ξ := by rw [← h]
  · intro h
    rw [h, smul_smul, mul_inv_cancel₀ ht, one_smul]

theorem nullity_firstFF_sub_smul_secondFF (p : M) (v : 𝔼 n) {t : ℝ} (ht : t ≠ 0) :
    nullity (firstFF hM p - t • secondFF hM p v) =
      finrank ℝ (Module.End.eigenspace (shapeOp hM p v : Module.End ℝ (tanSpace hM p)) t⁻¹) := by
  rw [← map_nullSpace_firstFF_sub_eq_eigenspace hM p v ht, nullity,
    LinearEquiv.finrank_map_eq]

theorem nullity_firstFF_sub_zero_smul_secondFF (p : M) (v : 𝔼 n) :
    nullity (firstFF hM p - (0 : ℝ) • secondFF hM p v) = 0 := by
  have h : nullSpace (firstFF hM p - (0 : ℝ) • secondFF hM p v) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro ξ hξ
    rw [mem_nullSpace_firstFF_sub_iff, zero_smul, sub_zero] at hξ
    exact (dParamEquiv hM p).map_eq_zero_iff.1 hξ
  rw [nullity, h, finrank_bot]

variable (hkw : k + w = n)

open Classical in
/-- **The multiplicity of `e` as a focal point of `(M, q)`**: the nullity of `dE` at
`(q, e − q)` if this point lies in `N`, and `0` otherwise.  So `e` is a focal point of `(M, q)`
iff its multiplicity is positive (`Morse.isFocalPoint_iff_focalMult_pos`). -/
def focalMult (q : M) (e : 𝔼 n) : ℕ :=
  if h : ((q : 𝔼 n), e - q) ∈ normalBundleSet hM then endpointNullity hM hkw ⟨_, h⟩ else 0

theorem isFocalPointMult_iff_focalMult (q : M) (e : 𝔼 n) (μ : ℕ) :
    IsFocalPointMult hM hkw q e μ ↔ focalMult hM hkw q e = μ ∧ 0 < μ := by
  unfold IsFocalPointMult focalMult
  constructor
  · rintro ⟨h, hμ, hpos⟩
    rw [dif_pos h]
    exact ⟨hμ, hpos⟩
  · rintro ⟨hμ, hpos⟩
    by_cases h : ((q : 𝔼 n), e - q) ∈ normalBundleSet hM
    · rw [dif_pos h] at hμ
      exact ⟨h, hμ, hpos⟩
    · rw [dif_neg h] at hμ
      omega

theorem isFocalPoint_iff_focalMult_pos (q : M) (e : 𝔼 n) :
    IsFocalPoint hM hkw q e ↔ 0 < focalMult hM hkw q e := by
  constructor
  · rintro ⟨μ, hμ⟩
    obtain ⟨h1, h2⟩ := (isFocalPointMult_iff_focalMult hM hkw q e μ).1 hμ
    omega
  · intro h
    exact ⟨_, (isFocalPointMult_iff_focalMult hM hkw q e _).2 ⟨rfl, h⟩⟩

/-- **Lemma 6.3** (Milnor, p. 34), multiplicity form: for `v` normal to `M` at `q`, the
multiplicity of `q + tv` as a focal point of `(M, q)` is `0` for `t = 0`, and for `t ≠ 0` it is
the multiplicity of `1/t` as an eigenvalue of the shape operator `S_v` (that is, as a principal
curvature of `M` at `q` in the direction `v`). -/
theorem focalMult_add_smul (q : M) {v : 𝔼 n} (hv : v ∈ (tangentSubspace hM q)ᗮ) (t : ℝ) :
    focalMult hM hkw q (q + t • v) = if t = 0 then 0 else
      finrank ℝ (Module.End.eigenspace (shapeOp hM q v : Module.End ℝ (tanSpace hM q)) t⁻¹) := by
  have hmem : ((q : 𝔼 n), ((q : 𝔼 n) + t • v) - q) ∈ normalBundleSet hM := by
    rw [add_sub_cancel_left, mem_normalBundleSet_iff]
    exact ⟨q.2, Submodule.smul_mem _ t hv⟩
  have hnull : endpointNullity hM hkw ⟨_, hmem⟩ =
      nullity (firstFF hM q - t • secondFF hM q v) := by
    rw [endpointNullity_eq_nullity]
    change nullity (firstFF hM q - secondFF hM q ((q : 𝔼 n) + t • v - q)) = _
    rw [add_sub_cancel_left, secondFF_smul]
  rw [focalMult, dif_pos hmem, hnull]
  split_ifs with ht
  · subst ht
    exact nullity_firstFF_sub_zero_smul_secondFF hM q v
  · exact nullity_firstFF_sub_smul_secondFF hM q v ht

/-- **Lemma 6.3** (Milnor, p. 34): *the focal points of `(M, q)` along the normal line
`{q + tv}` are precisely the points `q + K⁻¹ v`, `K ≠ 0` a principal curvature of `M` at `q` in
the direction `v`*; and the multiplicity of `q + K⁻¹ v` is the multiplicity of `K`
(`Morse.focalMult_add_inv_smul`). -/
theorem isFocalPoint_add_smul_iff (q : M) {v : 𝔼 n} (hv : v ∈ (tangentSubspace hM q)ᗮ)
    (t : ℝ) :
    IsFocalPoint hM hkw q (q + t • v) ↔ ∃ K : ℝ, K ≠ 0 ∧
      Module.End.HasEigenvalue (shapeOp hM q v : Module.End ℝ (tanSpace hM q)) K ∧ t = K⁻¹ := by
  rw [isFocalPoint_iff_focalMult_pos, focalMult_add_smul hM hkw q hv]
  constructor
  · intro h
    split_ifs at h with ht
    · omega
    · refine ⟨t⁻¹, inv_ne_zero ht, ?_, (inv_inv t).symm⟩
      rw [Module.End.hasEigenvalue_iff, ne_eq,
        ← Submodule.finrank_eq_zero]
      exact Nat.pos_iff_ne_zero.1 h
  · rintro ⟨K, hK, hKe, rfl⟩
    rw [if_neg (inv_ne_zero hK), inv_inv]
    rw [Module.End.hasEigenvalue_iff, ne_eq,
      ← Submodule.finrank_eq_zero] at hKe
    exact Nat.pos_of_ne_zero hKe

theorem focalMult_add_inv_smul (q : M) {v : 𝔼 n} (hv : v ∈ (tangentSubspace hM q)ᗮ) {K : ℝ}
    (hK : K ≠ 0) :
    focalMult hM hkw q (q + K⁻¹ • v) =
      finrank ℝ (Module.End.eigenspace (shapeOp hM q v : Module.End ℝ (tanSpace hM q)) K) := by
  rw [focalMult_add_smul hM hkw q hv, if_neg (inv_ne_zero hK), inv_inv]

end Lemma63

/-! ### Principal curvatures; at most `k` focal points on a normal line -/

section Principal

/-- **The principal curvatures** of `M` at `p` in the direction `v` (Milnor, p. 34), with
multiplicities and in decreasing order: the eigenvalues of the self-adjoint shape operator
`S_v` of `T_pM`. -/
def principalCurvatures (p : M) (v : 𝔼 n) : Fin k → ℝ :=
  (isSymmetric_shapeOp hM p v).eigenvalues (finrank_tanSpace hM p)

/-- The multiplicity of `K` as a principal curvature is the dimension of the eigenspace. -/
theorem finrank_eigenspace_shapeOp (p : M) (v : 𝔼 n) (K : ℝ) :
    finrank ℝ (Module.End.eigenspace (shapeOp hM p v : Module.End ℝ (tanSpace hM p)) K) =
      (Finset.univ.filter fun i => principalCurvatures hM p v i = K).card :=
  ((isSymmetric_shapeOp hM p v).card_filter_eigenvalues_eq (finrank_tanSpace hM p) K).symm

variable (hkw : k + w = n)

theorem focalMult_add_smul_eq_card (q : M) {v : 𝔼 n} (hv : v ∈ (tangentSubspace hM q)ᗮ)
    (t : ℝ) :
    focalMult hM hkw q (q + t • v) =
      (Finset.univ.filter fun i => t ≠ 0 ∧ principalCurvatures hM q v i = t⁻¹).card := by
  rw [focalMult_add_smul hM hkw q hv]
  split_ifs with ht
  · simp [ht]
  · rw [finrank_eigenspace_shapeOp]
    simp [ht]

/-- **Lemma 6.3** (Milnor, p. 34), second sentence: *there are at most `k` focal points of
`(M, q)` along the normal line `{q + tv}`, each counted with its multiplicity*: for any finite set
of parameters `t`, the multiplicities of the points `q + tv` add up to at most `k`. -/
theorem sum_focalMult_add_smul_le (q : M) {v : 𝔼 n} (hv : v ∈ (tangentSubspace hM q)ᗮ)
    (T : Finset ℝ) :
    ∑ t ∈ T, focalMult hM hkw q (q + t • v) ≤ k := by
  classical
  simp_rw [focalMult_add_smul_eq_card hM hkw q hv]
  rw [← Finset.card_biUnion]
  · exact (Finset.card_le_univ _).trans (by simp)
  · intro s _ t _ hst
    rw [Function.onFun, Finset.disjoint_filter]
    rintro i - ⟨hs, hsi⟩ ⟨ht, hti⟩
    exact hst (inv_injective (hsi.symm.trans hti))

end Principal

/-! ### Lemma 6.9 -/

section Index

/-- **The index of `g − ℓ_v`** is the number of principal curvatures (with multiplicity) in the
direction `v` which are `> 1`: in an orthonormal eigenbasis of the shape operator the quadratic
form `g − ℓ_v` is `Σ (1 − κᵢ) cᵢ²`, and Sylvester's law of inertia counts its negative
coefficients. -/
theorem index_firstFF_sub_secondFF (p : M) (v : 𝔼 n) :
    index (firstFF hM p - secondFF hM p v) =
      (Finset.univ.filter fun i => 1 < principalCurvatures hM p v i).card := by
  set hT := isSymmetric_shapeOp hM p v
  set hn := finrank_tanSpace hM p
  set e := hT.eigenvectorBasis hn
  set κ := principalCurvatures hM p v with hκ
  let Φ : 𝔼 k ≃ₗ[ℝ] (Fin k → ℝ) := (dParamEquiv hM p).trans
    (e.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)))
  have hΦ : ∀ ξ, Φ ξ = fun i => e.repr (dParamEquiv hM p ξ) i := fun ξ => rfl
  have hS : ∀ (a : tanSpace hM p) (i : Fin k),
      e.repr (shapeOp hM p v a) i = κ i * e.repr a i := fun a i =>
    hT.eigenvectorBasis_apply_self_apply hn a i
  have hQ : ∀ ξ, QuadraticMap.weightedSumSquares ℝ (fun i => 1 - κ i) (Φ ξ) =
      quadForm (firstFF hM p - secondFF hM p v) ξ := by
    intro ξ
    rw [QuadraticMap.weightedSumSquares_apply, quadForm_apply]
    have h1 : firstFF hM p ξ ξ = ∑ i, e.repr (dParamEquiv hM p ξ) i *
        e.repr (dParamEquiv hM p ξ) i := by
      rw [← inner_dParamEquiv, ← e.repr.inner_map_map, PiLp.inner_apply]
      simp [sq]
    have h2 : secondFF hM p v ξ ξ = ∑ i, κ i * (e.repr (dParamEquiv hM p ξ) i *
        e.repr (dParamEquiv hM p ξ) i) := by
      rw [← inner_shapeOp_dParamEquiv, ← e.repr.inner_map_map, PiLp.inner_apply]
      simp only [hS]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    simp only [FunLike.coe_sub, Pi.sub_apply, h1, h2, hΦ, smul_eq_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hequiv : (quadForm (firstFF hM p - secondFF hM p v)).Equivalent
      (QuadraticMap.weightedSumSquares ℝ (fun i => 1 - κ i)) :=
    ⟨{ Φ with map_app' := hQ }⟩
  rw [index, QuadraticForm.sigNeg_of_equiv_weightedSumSquares hequiv, Set.ncard_eq_toFinset_card',
    Set.toFinset_ofPred]
  congr 1
  ext i
  simp

/-- The index of `L_p` at a critical point `q` is the number of principal curvatures of `M` at `q`
in the direction `p − q` which are `> 1` (Milnor, p. 38, with `p = q + tv`: the number of
eigenvalues of `(v · ℓ_ij)` greater than `1/t`). -/
theorem indexM_normSq_sub_eq_card (p : 𝔼 n) (q : M)
    (hcrit : letI := hM.chartedSpace;
      IsCriticalPointM (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) q) :
    letI := hM.chartedSpace
    indexM (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) q =
      (Finset.univ.filter fun i => 1 < principalCurvatures hM q (p - q) i).card := by
  let := hM.chartedSpace
  rw [indexM_normSq_sub_eq hM (Milnor.Tub.σ hM q) p (Milnor.Tub.mem_source hM q) hcrit]
  change index (hessian (fun z => ‖xParam hM q z - p‖ ^ 2) (uParam hM q)) = _
  rw [hessian_normSq_sub_xParam, index_smul two_pos, index_firstFF_sub_secondFF]

variable (hkw : k + w = n)

/-- **Lemma 6.9** (index theorem for `L_p`, Milnor, p. 37): *the index of `L_p` at a
non-degenerate critical point `q ∈ M` equals the number of focal points of `(M, q)` on the segment
from `q` to `p`, each counted with its multiplicity*: the sum, over `t ∈ [0, 1]`, of the
multiplicities of the points `q + t(p − q)` as focal points of `(M, q)` (all but finitely many of
which are `0`). -/
theorem indexM_normSq_sub_eq_finsum_focalMult (p : 𝔼 n) (q : M)
    (hq : letI := hM.chartedSpace;
      IsNondegenerateCriticalPointM (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) q) :
    letI := hM.chartedSpace
    indexM (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) q =
      ∑ᶠ t ∈ Icc (0 : ℝ) 1, focalMult hM hkw q (q + t • (p - q)) := by
  classical
  let := hM.chartedSpace
  have hmem := (isCriticalPointM_normSq_sub_iff_mem_normalBundleSet p q).1 hq.1
  have hv : p - q ∈ (tangentSubspace hM q)ᗮ := ((mem_normalBundleSet_iff hM).1 hmem).2
  set κ := principalCurvatures hM q (p - q) with hκ
  -- no principal curvature in the direction `p − q` equals `1`: `p` is not a focal point
  have h1 : ∀ i, κ i ≠ 1 := by
    intro i hi
    have hnull : nullityM (𝔼 k) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) q = 0 :=
      isNondegenerate_hessianM_iff_nullityM_eq_zero.1 hq.2
    rw [nullityM_normSq_sub_eq_endpointNullity hkw p q hmem] at hnull
    have hfm : focalMult hM hkw q (q + (1 : ℝ) • (p - q)) = 0 := by
      rw [one_smul, add_sub_cancel]
      rw [focalMult, dif_pos hmem]
      exact hnull
    rw [focalMult_add_smul_eq_card hM hkw q hv, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff] at hfm
    exact hfm (Finset.mem_univ i) ⟨one_ne_zero, by rw [inv_one]; exact hi⟩
  rw [indexM_normSq_sub_eq_card hM p q hq.1]
  simp_rw [focalMult_add_smul_eq_card hM hkw q hv]
  rw [← hκ]
  set s := Finset.univ.filter fun i => 1 < κ i with hs
  rw [finsum_mem_eq_sum_of_subset _ (t := s.image fun i => (κ i)⁻¹)]
  · rw [Finset.card_eq_sum_card_image (fun i => (κ i)⁻¹) s]
    refine Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ht
    have hj1 : 1 < κ j := (Finset.mem_filter.1 hj).2
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs]
    constructor
    · rintro ⟨hi1, hi⟩
      refine ⟨inv_ne_zero (by linarith), ?_⟩
      rw [inv_inv]
      exact inv_injective hi
    · rintro ⟨-, hi⟩
      rw [inv_inv] at hi
      exact ⟨hi ▸ hj1, by rw [hi]⟩
  · rintro t ⟨⟨ht0, ht1⟩, ht⟩
    rw [Function.mem_support, ne_eq, Finset.card_eq_zero, ← ne_eq,
      ← Finset.nonempty_iff_ne_empty] at ht
    obtain ⟨i, hi⟩ := ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨htne, hi⟩ := hi
    have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htne)
    have hge : 1 ≤ κ i := by rw [hi]; exact one_le_inv₀ htpos |>.2 ht1
    have hgt : 1 < κ i := lt_of_le_of_ne hge (Ne.symm (h1 i))
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, ?_, ?_⟩)
    · simp [hs, hgt]
    · rw [hi, inv_inv]
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
    have hj1 : 1 < κ j := (Finset.mem_filter.1 hj).2
    exact ⟨(inv_pos.2 (by linarith)).le, inv_le_one_of_one_le₀ hj1.le⟩

end Index

end Morse
