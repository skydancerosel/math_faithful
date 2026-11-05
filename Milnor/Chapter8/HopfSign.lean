import Milnor.Chapter8.LinkDegree
import Milnor.Chapter8.HopfMap
import Milnor.Chapter8.LinkAlg

/-!
# The linking number of two Hopf fibres (Milnor §8, Problem 15)

The computation behind Milnor's claim `H(π) = 1` for the Hopf fibration `π = hopfMap : S³ → S²`.
We compute the linking number of the fibres over `y = (1, 0, 0)` and `z = (−1, 0, 0)`, oriented as
preimages (`preimOr`, for positive bases of `T_y S²`, `T_z S²`), after the identity rotation and
stereographic projection from the north pole `(0, 0, 0, 1)`:

* `linkingNumberRot_hopfMap`: **the linking number is `−1`** (with the book's conventions taken
  literally: `sphOrStd` is "outward normal first", preimages carry the frame orientation, and the
  linking number is the degree of `(x, x') ↦ (x − x')/‖x − x'‖` for the product orientation);
* `isRegularValue_linkMap_hopfE`: `e = (0, −1, 0)` is a regular value of the linking map;
* `stN_eq_stereoTop`: `stN = stereoTop` on `ℝ⁴`.

**Method.**  By `degAt_phiR_eq_linkingNumberRot` the linking number is the local degree of
`Φ = phiR π π id ∘ val` on `D_R ⊆ S³ × S³` at `((y, z), e)`.

1. *The preimage* (`HopfSign.preimage_phiR`) is the single point `(a, a')`,
   `a = (0, −1, 0, −1)/√2`, `a' = (0, 1, 0, −1)/√2`: `stN x − stN x'` must be a positive multiple of
   `e`, and `hopf_link_pair_iff` applies.
2. *The sign of `Φ` at `(a, a')`* (`HopfSign.signAt_q₀`).  The block lemma
   `LinkDeg.orSign_pair_preimage₂` (sign factor `(−1)^(1·2) = 1`) reduces it to the sign of
   `dλ ∘ (ι × ι') : ℝ × ℝ → T_e S²`, where `ι, ι'` span the fibre directions (chart vectors with
   images `t = (1, 0, 1, 0)/√2` at `a`, `t' = (−1, 0, 1, 0)/√2` at `a'`, both in `ker dπ`), and the
   fibres carry the frame orientations for lifts `u₁ = (1, 0, −1, 0)`, `u₂ = (0, −1, 0, 1)` at `a`
   (`dπ u₁ = 2√2 e₁`, `dπ u₂ = 2√2 e₂`) and `w₁ = (0, 1, 0, 1)`, `w₂ = (1, 0, 1, 0)` at `a'`
   (`dπ w₁ = 2√2 e₂`, `dπ w₂ = 2√2 e₁`).  All orientation signs are ambient determinants
   (`HopfSign.orientation_eq_sphOrStd_iff`: a chart basis `ζ` of `T_q Sⁿ` is positive for
   `sphOrStd n` iff `det(q, dι ζ) > 0`):
   * the lifts are positive bases at `y` and `z`: `det(y, 2√2 e₁, 2√2 e₂) = det(z, 2√2 e₂, 2√2 e₁) = 8`;
   * the fibre directions are **negative**: `det(a, u₁, u₂, t) = det(a', w₁, w₂, t') = −2`;
   * `dλ(t, 0) = c (1, 0, 1)` and `dλ(0, t') = c (1, 0, −1)` with `c = (√2 − 1)/‖stN a − stN a'‖ > 0`
     (in fact `c = 1/2`), computed by the chain rule through `stereoTop` and `normalize`; this pair
     is a **negative** basis at `e`: `det(e, c (1, 0, 1), c (1, 0, −1)) = −2c²`.

   Hence the sign is `sgn((−1)(−1)(−1)) = −1`, the local degree is `−1`, and so is the linking
   number.  Since the only preimage point is regular, `e` is a regular value of the linking map
   (`LinkDeg.signAt_phiR_eq`).

Auxiliary definitions and lemmas live in the namespace `Milnor.Problems.HopfSign`.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Problems

open Sphere

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

/-- The point `(1, 0, 0)` of `S²`. -/
def hopfY : Sph 2 := ⟨!₂[1, 0, 0], by
  rw [mem_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp⟩

/-- The point `(−1, 0, 0)` of `S²`. -/
def hopfZ : Sph 2 := ⟨!₂[-1, 0, 0], by
  rw [mem_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp⟩

/-- The direction `(0, −1, 0)` of `S²`. -/
def hopfE : Sph 2 := ⟨!₂[0, -1, 0], by
  rw [mem_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp⟩

/-- The stereographic projection `stN` from the north pole of `S³` is `stereoTop`. -/
theorem stN_eq_stereoTop :
    (stN : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 3)) = stereoTop := by
  funext x
  ext i
  fin_cases i <;> simp [stN, stereoTop, dropLast_apply]

/-- The identity rotation of `ℝ⁴`. -/
local notation "R₀" => LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 4))

namespace HopfSign

theorem hopfY_val : hopfY.1 = !₂[1, 0, 0] := rfl

theorem hopfZ_val : hopfZ.1 = !₂[-1, 0, 0] := rfl

theorem hopfE_val : hopfE.1 = !₂[0, -1, 0] := rfl

theorem hopfY_ne_hopfZ : hopfY ≠ hopfZ := by
  intro h
  have h1 := congrArg (fun q : Sph 2 => q.1 0) h
  simp [hopfY, hopfZ] at h1
  norm_num at h1

/-! ### Signs of chart bases of the sphere -/

/-- A chart basis `ζ` of `T_q Sⁿ` is positive for `sphOrStd n` iff
`det(q, dι ζ₀, …, dι ζ_{n-1}) > 0` in the standard basis of `ℝⁿ⁺¹`. -/
theorem orientation_eq_sphOrStd_iff {n : ℕ} (q : Sph n) (ζ : Basis (Fin n) ℝ (𝔼 n)) :
    ζ.orientation = (sphOrStd n).or q ↔
      0 < (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det
        (Matrix.vecCons q.1 fun i => mfd 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 (n + 1))
          (Subtype.val : Sph n → 𝔼 (n + 1)) q (ζ i)) := by
  rw [sphOrStd_or, frameOr_eq_someVector hZ (stdOrE n) (sph_frameForm_ne_zero q),
    LinkAlg.orientation_eq_rayOfNeZero_iff ζ, frameForm_apply, frameTuple_one]
  obtain ⟨r, hr, hrdet⟩ : ∃ r : ℝ, 0 < r ∧
      r • (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det = (stdOrE n).someVector := by
    have h1 : rayOfNeZero ℝ _ (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det_ne_zero =
        rayOfNeZero ℝ _ (stdOrE n).someVector_ne_zero := by
      rw [Module.Ray.someVector_ray]; rfl
    exact ((ray_eq_iff _ _).1 h1).exists_pos_left (Basis.det_ne_zero _)
      (stdOrE n).someVector_ne_zero
  rw [← hrdet, AlternatingMap.smul_apply, smul_eq_mul]
  exact ⟨fun h => pos_of_mul_pos_right h hr.le, fun h => mul_pos hr h⟩

/-- Tangent vectors whose frame determinant does not vanish are linearly independent. -/
theorem linearIndependent_of_det_ne_zero {n : ℕ} (q : Sph n) (w : Fin n → 𝔼 n)
    (h : (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det
        (Matrix.vecCons q.1 fun i => mfd 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 (n + 1))
          (Subtype.val : Sph n → 𝔼 (n + 1)) q (w i)) ≠ 0) :
    LinearIndependent ℝ w := by
  have h1 := ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.is_basis_iff_det.2
    (isUnit_iff_ne_zero.2 h)).1
  have h2 : LinearIndependent ℝ fun i => mfd 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 (n + 1))
      (Subtype.val : Sph n → 𝔼 (n + 1)) q (w i) :=
    h1.comp Fin.succ (Fin.succ_injective _)
  exact LinearIndependent.of_comp (mfd 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 (n + 1))
    (Subtype.val : Sph n → 𝔼 (n + 1)) q : 𝔼 n →ₗ[ℝ] 𝔼 (n + 1)) h2

/-- The derivative of `normalize` on vectors orthogonal to the base point. -/
theorem exists_hasFDerivAt_normalize {n : ℕ} {y₀ : 𝔼 (n + 1)} (hy₀ : y₀ ≠ 0) :
    ∃ D : 𝔼 (n + 1) →L[ℝ] 𝔼 (n + 1), HasFDerivAt (Sphere.normalize (n := n)) D y₀ ∧
      ∀ h, ⟪y₀, h⟫ = 0 → D h = ‖y₀‖⁻¹ • h := by
  have hr : ‖y₀‖ ^ 2 ≠ 0 := by positivity
  have hs : √(‖y₀‖ ^ 2) ≠ 0 := by
    rw [Real.sqrt_sq (norm_nonneg _)]; exact norm_ne_zero_iff.2 hy₀
  have h1 := (Real.hasDerivAt_sqrt hr).fun_inv hs
  have h2 := h1.comp_hasFDerivAt y₀ (hasStrictFDerivAt_norm_sq y₀).hasFDerivAt
  have h3 := h2.smul (hasFDerivAt_id y₀)
  refine ⟨_, h3.congr_of_eventuallyEq ?_, fun h hh => ?_⟩
  · filter_upwards with y
    simp [Sphere.normalize, Real.sqrt_sq (norm_nonneg _)]
  · simp [hh, Real.sqrt_sq (norm_nonneg _)]

/-! ### Real numbers -/

theorem sqrt2_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

theorem inv_sqrt2_mul_self : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
  rw [← mul_inv, sqrt2_mul_self, one_div]

theorem inv_sqrt2_pos : 0 < (Real.sqrt 2)⁻¹ := by positivity

theorem one_lt_sqrt2 : 1 < Real.sqrt 2 := by
  have h : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_one] at h

/-! ### The two points of the fibres -/

/-- `a = (0, −1, 0, −1)/√2`, in the fibre over `(1, 0, 0)`. -/
def ptA : Sph 3 := ⟨(Real.sqrt 2)⁻¹ • !₂[0, -1, 0, -1], mem_sph_hopfA⟩

/-- `a' = (0, 1, 0, −1)/√2`, in the fibre over `(−1, 0, 0)`. -/
def ptA' : Sph 3 := ⟨(Real.sqrt 2)⁻¹ • !₂[0, 1, 0, -1], mem_sph_hopfA'⟩

theorem ptA_val : ptA.1 = (Real.sqrt 2)⁻¹ • !₂[0, -1, 0, -1] := rfl

theorem ptA'_val : ptA'.1 = (Real.sqrt 2)⁻¹ • !₂[0, 1, 0, -1] := rfl

theorem hopfMap_ptA : hopfMap ptA = hopfY := Subtype.ext hopfPoly_hopfA

theorem hopfMap_ptA' : hopfMap ptA' = hopfZ := Subtype.ext hopfPoly_hopfA'

theorem ptA_ne_north : ptA.1 ≠ (north : Sph (1 + 1 + 1)).1 := by
  intro h
  have h3 := congrArg (fun v : 𝔼 4 => v 3) h
  simp [ptA, north, northV] at h3
  linarith [inv_sqrt2_pos]

theorem ptA'_ne_north : ptA'.1 ≠ (north : Sph (1 + 1 + 1)).1 := by
  intro h
  have h3 := congrArg (fun v : 𝔼 4 => v 3) h
  simp [ptA', north, northV] at h3
  linarith [inv_sqrt2_pos]

theorem ptA_ne_ptA' : ptA ≠ ptA' := by
  intro h
  have h1 := congrArg (fun q : Sph 3 => q.1 1) h
  simp [ptA, ptA'] at h1
  linarith [inv_sqrt2_pos]

theorem mem_domR_ptA : ((ptA, ptA') : Sph 3 × Sph 3) ∈ domR (d := 1) R₀ :=
  mem_domR.2 ⟨ptA_ne_north, ptA'_ne_north, ptA_ne_ptA'⟩

/-- The pair `(a, a') ∈ D_R`. -/
def q₀ : domR (d := 1) R₀ := ⟨(ptA, ptA'), mem_domR_ptA⟩

/-! ### Chart vectors at `a` and `a'` -/

/-- The chart vector at `a` with image `t = (1, 0, 1, 0)/√2`. -/
def vt : 𝔼 3 := (exists_mfd_val_eq (x := ptA) hopfA_inner_t).choose

/-- The chart vector at `a` with image `u₁ = (1, 0, −1, 0)`. -/
def vu₁ : 𝔼 3 := (exists_mfd_val_eq (x := ptA) hopfA_inner_u₁).choose

/-- The chart vector at `a` with image `u₂ = (0, −1, 0, 1)`. -/
def vu₂ : 𝔼 3 := (exists_mfd_val_eq (x := ptA) hopfA_inner_u₂).choose

/-- The chart vector at `a'` with image `t' = (−1, 0, 1, 0)/√2`. -/
def vt' : 𝔼 3 := (exists_mfd_val_eq (x := ptA') hopfA'_inner_t').choose

/-- The chart vector at `a'` with image `w₁ = (0, 1, 0, 1)`. -/
def vw₁ : 𝔼 3 := (exists_mfd_val_eq (x := ptA') hopfA'_inner_w₁).choose

/-- The chart vector at `a'` with image `w₂ = (1, 0, 1, 0)`. -/
def vw₂ : 𝔼 3 := (exists_mfd_val_eq (x := ptA') hopfA'_inner_w₂).choose

theorem mfd_vt : mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA vt =
    (Real.sqrt 2)⁻¹ • !₂[1, 0, 1, 0] :=
  (exists_mfd_val_eq (x := ptA) hopfA_inner_t).choose_spec

theorem mfd_vu₁ : mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA vu₁ =
    !₂[1, 0, -1, 0] :=
  (exists_mfd_val_eq (x := ptA) hopfA_inner_u₁).choose_spec

theorem mfd_vu₂ : mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA vu₂ =
    !₂[0, -1, 0, 1] :=
  (exists_mfd_val_eq (x := ptA) hopfA_inner_u₂).choose_spec

theorem mfd_vt' : mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA' vt' =
    (Real.sqrt 2)⁻¹ • !₂[-1, 0, 1, 0] :=
  (exists_mfd_val_eq (x := ptA') hopfA'_inner_t').choose_spec

theorem mfd_vw₁ : mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA' vw₁ =
    !₂[0, 1, 0, 1] :=
  (exists_mfd_val_eq (x := ptA') hopfA'_inner_w₁).choose_spec

theorem mfd_vw₂ : mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA' vw₂ =
    !₂[1, 0, 1, 0] :=
  (exists_mfd_val_eq (x := ptA') hopfA'_inner_w₂).choose_spec

/-! ### The derivative of the Hopf map at `a` and `a'` -/

theorem mfd_val_hopfMap_apply (x : Sph 3) (v : 𝔼 3) :
    mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1)) (hopfMap x)
      (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap x v) =
    fderiv ℝ hopfPoly x.1
      (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) x v) :=
  DFunLike.congr_fun (mfd_val_comp_hopfMap x) v

theorem D_vt : mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA vt = 0 := by
  refine injective_mfderiv_val (sphS 2) (hopfMap ptA) ?_
  have h := mfd_val_hopfMap_apply ptA vt
  rw [mfd_vt] at h
  exact h.trans (hopfA_fderiv_t.trans (map_zero _).symm)

theorem D_vt' : mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA' vt' = 0 := by
  refine injective_mfderiv_val (sphS 2) (hopfMap ptA') ?_
  have h := mfd_val_hopfMap_apply ptA' vt'
  rw [mfd_vt'] at h
  exact h.trans (hopfA'_fderiv_t'.trans (map_zero _).symm)

theorem vt_ne_zero : vt ≠ 0 := by
  intro h
  have h1 := mfd_vt
  rw [h, map_zero] at h1
  have h2 := congrArg (fun v : 𝔼 4 => v 0) h1
  simp at h2
  linarith [one_lt_sqrt2]

theorem vt'_ne_zero : vt' ≠ 0 := by
  intro h
  have h1 := mfd_vt'
  rw [h, map_zero] at h1
  have h2 := congrArg (fun v : 𝔼 4 => v 0) h1
  simp at h2

theorem injective_toSpanSingleton {v : 𝔼 3} (hv : v ≠ 0) :
    Injective (ContinuousLinearMap.toSpanSingleton ℝ v) := fun s s' h => by
  simp only [ContinuousLinearMap.toSpanSingleton_apply] at h
  exact smul_left_injective ℝ hv h

/-- The fibre direction spans the kernel of `dπ`. -/
theorem range_toSpanSingleton_eq_ker {x : Sph 3} {v : 𝔼 3} (hv : v ≠ 0)
    (hD : mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap x v = 0) :
    LinearMap.range (ContinuousLinearMap.toSpanSingleton ℝ v : ℝ →ₗ[ℝ] 𝔼 3) =
      LinearMap.ker (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap x : 𝔼 3 →ₗ[ℝ] 𝔼 2) := by
  have hsurj : Surjective (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap x) :=
    isRegularValue_hopfMap _ x rfl
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨s, rfl⟩
    simp [hD]
  · have h1 := LinearMap.finrank_range_add_finrank_ker
      (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap x : 𝔼 3 →ₗ[ℝ] 𝔼 2)
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin] at h1
    rw [LinearMap.finrank_range_of_inj (injective_toSpanSingleton hv), finrank_self]
    omega

/-- The inclusion of the fibre direction at `a`. -/
def ιA : ℝ →L[ℝ] 𝔼 3 := ContinuousLinearMap.toSpanSingleton ℝ vt

/-- The inclusion of the fibre direction at `a'`. -/
def ιA' : ℝ →L[ℝ] 𝔼 3 := ContinuousLinearMap.toSpanSingleton ℝ vt'

theorem hιA : Injective ιA := injective_toSpanSingleton vt_ne_zero

theorem hιA' : Injective ιA' := injective_toSpanSingleton vt'_ne_zero

theorem hkerA : LinearMap.range (ιA : ℝ →ₗ[ℝ] 𝔼 3) =
    LinearMap.ker (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA : 𝔼 3 →ₗ[ℝ] 𝔼 2) :=
  range_toSpanSingleton_eq_ker vt_ne_zero D_vt

theorem hkerA' : LinearMap.range (ιA' : ℝ →ₗ[ℝ] 𝔼 3) =
    LinearMap.ker (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA' : 𝔼 3 →ₗ[ℝ] 𝔼 2) :=
  range_toSpanSingleton_eq_ker vt'_ne_zero D_vt'

/-! ### The frames `u` (lifts of positive bases at `y` and `z`) -/

/-- Lifts at `a`: `dπ(u₁) = 2√2 e₁`, `dπ(u₂) = 2√2 e₂`. -/
def uA : Fin 2 → 𝔼 3 := ![vu₁, vu₂]

/-- Lifts at `a'`: `dπ(w₁) = 2√2 e₂`, `dπ(w₂) = 2√2 e₁`. -/
def uA' : Fin 2 → 𝔼 3 := ![vw₁, vw₂]

theorem mfd_val_D_uA : (fun i => mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1))
    (hopfMap ptA) (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA (uA i))) =
    ![(2 * Real.sqrt 2) • !₂[0, 1, 0], (2 * Real.sqrt 2) • !₂[0, 0, 1]] := by
  funext i
  fin_cases i
  · show mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1))
      (hopfMap ptA) (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA vu₁) = _
    rw [mfd_val_hopfMap_apply, mfd_vu₁]
    exact hopfA_fderiv_u₁
  · show mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1))
      (hopfMap ptA) (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA vu₂) = _
    rw [mfd_val_hopfMap_apply, mfd_vu₂]
    exact hopfA_fderiv_u₂

theorem mfd_val_D_uA' : (fun i => mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1))
    (hopfMap ptA') (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA' (uA' i))) =
    ![(2 * Real.sqrt 2) • !₂[0, 0, 1], (2 * Real.sqrt 2) • !₂[0, 1, 0]] := by
  funext i
  fin_cases i
  · show mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1))
      (hopfMap ptA') (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA' vw₁) = _
    rw [mfd_val_hopfMap_apply, mfd_vw₁]
    exact hopfA'_fderiv_w₁
  · show mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1))
      (hopfMap ptA') (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA' vw₂) = _
    rw [mfd_val_hopfMap_apply, mfd_vw₂]
    exact hopfA'_fderiv_w₂

/-- `det(y, 2√2 e₁, 2√2 e₂) = 8`. -/
theorem det_D_uA : (EuclideanSpace.basisFun (Fin (2 + 1)) ℝ).toBasis.det
    (Matrix.vecCons (hopfMap ptA).1 fun i => mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1))
      (Subtype.val : Sph 2 → 𝔼 (2 + 1)) (hopfMap ptA)
      (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA (uA i))) = 8 := by
  rw [mfd_val_D_uA, hopfMap_ptA, hopfY_val, Basis.det_apply, Matrix.det_fin_three]
  simp [Basis.toMatrix_apply]
  linear_combination 4 * sqrt2_mul_self

/-- `det(z, 2√2 e₂, 2√2 e₁) = 8`. -/
theorem det_D_uA' : (EuclideanSpace.basisFun (Fin (2 + 1)) ℝ).toBasis.det
    (Matrix.vecCons (hopfMap ptA').1 fun i => mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1))
      (Subtype.val : Sph 2 → 𝔼 (2 + 1)) (hopfMap ptA')
      (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA' (uA' i))) = 8 := by
  rw [mfd_val_D_uA', hopfMap_ptA', hopfZ_val, Basis.det_apply, Matrix.det_fin_three]
  simp [Basis.toMatrix_apply]
  linear_combination 4 * sqrt2_mul_self

theorem linearIndependent_D_uA :
    LinearIndependent ℝ fun i => mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA (uA i) :=
  linearIndependent_of_det_ne_zero (hopfMap ptA) _ (ne_of_eq_of_ne det_D_uA (by norm_num))

theorem linearIndependent_D_uA' :
    LinearIndependent ℝ fun i => mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA' (uA' i) :=
  linearIndependent_of_det_ne_zero (hopfMap ptA') _ (ne_of_eq_of_ne det_D_uA' (by norm_num))

theorem orientation_D_uA :
    (basisOfLinearIndependentOfCardEqFinrank' _ linearIndependent_D_uA (by simp)).orientation =
      (sphOrStd 2).or (hopfMap ptA) := by
  rw [orientation_eq_sphOrStd_iff]
  simp only [coe_basisOfLinearIndependentOfCardEqFinrank']
  rw [det_D_uA]
  norm_num

theorem orientation_D_uA' :
    (basisOfLinearIndependentOfCardEqFinrank' _ linearIndependent_D_uA' (by simp)).orientation =
      (sphOrStd 2).or (hopfMap ptA') := by
  rw [orientation_eq_sphOrStd_iff]
  simp only [coe_basisOfLinearIndependentOfCardEqFinrank']
  rw [det_D_uA']
  norm_num

/-! ### The frame orientations of the fibres at `a` and `a'` -/

/-- The basis `(u₁, u₂, t)` of the chart space at `a`. -/
def eVA : Basis (Fin (1 + 2)) ℝ (𝔼 3) :=
  basisOfLinearIndependentOfCardEqFinrank' _
    (LinkAlg.linearIndependent_frameTuple hιA hkerA linearIndependent_D_uA
      (Basis.singleton (Fin 1) ℝ)) (by simp)

/-- The basis `(w₁, w₂, t')` of the chart space at `a'`. -/
def eVA' : Basis (Fin (1 + 2)) ℝ (𝔼 3) :=
  basisOfLinearIndependentOfCardEqFinrank' _
    (LinkAlg.linearIndependent_frameTuple hιA' hkerA' linearIndependent_D_uA'
      (Basis.singleton (Fin 1) ℝ)) (by simp)

theorem coe_eVA : ⇑eVA = frameTuple uA fun i => ιA (Basis.singleton (Fin 1) ℝ i) := by
  simp [eVA]

theorem coe_eVA' : ⇑eVA' = frameTuple uA' fun i => ιA' (Basis.singleton (Fin 1) ℝ i) := by
  simp [eVA']

theorem mfd_val_eVA : (fun i => mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1))
    ptA (eVA i)) = ![!₂[1, 0, -1, 0], !₂[0, -1, 0, 1], (Real.sqrt 2)⁻¹ • !₂[1, 0, 1, 0]] := by
  rw [coe_eVA]
  funext i
  fin_cases i
  · exact (congrArg (fun v => mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA v)
      (LinkAlg.frameTuple_apply_left uA (fun i => ιA (Basis.singleton (Fin 1) ℝ i))
        (i := ⟨0, by norm_num⟩) (j := 0) rfl)).trans mfd_vu₁
  · exact (congrArg (fun v => mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA v)
      (LinkAlg.frameTuple_apply_left uA (fun i => ιA (Basis.singleton (Fin 1) ℝ i))
        (i := ⟨1, by norm_num⟩) (j := 1) rfl)).trans mfd_vu₂
  · have h3 : frameTuple uA (fun i => ιA (Basis.singleton (Fin 1) ℝ i))
        (⟨2, by norm_num⟩ : Fin (1 + 2)) = vt := by
      rw [LinkAlg.frameTuple_apply_right uA _ (i := ⟨2, by norm_num⟩) (j := 0) rfl]
      simp [ιA]
    exact (congrArg (fun v => mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1))
      ptA v) h3).trans mfd_vt

theorem mfd_val_eVA' : (fun i => mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1))
    ptA' (eVA' i)) = ![!₂[0, 1, 0, 1], !₂[1, 0, 1, 0], (Real.sqrt 2)⁻¹ • !₂[-1, 0, 1, 0]] := by
  rw [coe_eVA']
  funext i
  fin_cases i
  · exact (congrArg (fun v => mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA' v)
      (LinkAlg.frameTuple_apply_left uA' (fun i => ιA' (Basis.singleton (Fin 1) ℝ i))
        (i := ⟨0, by norm_num⟩) (j := 0) rfl)).trans mfd_vw₁
  · exact (congrArg (fun v => mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA' v)
      (LinkAlg.frameTuple_apply_left uA' (fun i => ιA' (Basis.singleton (Fin 1) ℝ i))
        (i := ⟨1, by norm_num⟩) (j := 1) rfl)).trans mfd_vw₂
  · have h3 : frameTuple uA' (fun i => ιA' (Basis.singleton (Fin 1) ℝ i))
        (⟨2, by norm_num⟩ : Fin (1 + 2)) = vt' := by
      rw [LinkAlg.frameTuple_apply_right uA' _ (i := ⟨2, by norm_num⟩) (j := 0) rfl]
      simp [ιA']
    exact (congrArg (fun v => mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1))
      ptA' v) h3).trans mfd_vt'

/-- `det(a, u₁, u₂, t) = −2`. -/
theorem det_eVA : (EuclideanSpace.basisFun (Fin (3 + 1)) ℝ).toBasis.det
    (Matrix.vecCons ptA.1 fun i => mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1))
      (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA (eVA i)) = -2 := by
  rw [mfd_val_eVA, ptA_val, Basis.det_apply, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Basis.toMatrix_apply, Matrix.det_fin_three, Fin.succAbove]
  linear_combination (-4) * inv_sqrt2_mul_self

/-- `det(a', w₁, w₂, t') = −2`. -/
theorem det_eVA' : (EuclideanSpace.basisFun (Fin (3 + 1)) ℝ).toBasis.det
    (Matrix.vecCons ptA'.1 fun i => mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1))
      (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA' (eVA' i)) = -2 := by
  rw [mfd_val_eVA', ptA'_val, Basis.det_apply, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Basis.toMatrix_apply, Matrix.det_fin_three, Fin.succAbove]
  linear_combination (-4) * inv_sqrt2_mul_self

/-- The fibre over `y` is negatively oriented along `t` in the chart at `a`. -/
theorem orEpsB_frameOr_A : orEpsB (Basis.singleton (Fin 1) ℝ)
    (frameOr (finrank_self ℝ) ((sphOrStd 3).or ptA) uA ιA) = -1 := by
  rw [LinkAlg.orEpsB_congr (frameOr_basis_iff (finrank_self ℝ) ((sphOrStd 3).or ptA) uA ιA
    (Basis.singleton (Fin 1) ℝ) eVA coe_eVA).symm]
  refine LinkAlg.orEpsB_eq_neg_one' fun h => ?_
  have h2 := (orientation_eq_sphOrStd_iff ptA eVA).1 h
  rw [det_eVA] at h2
  norm_num at h2

/-- The fibre over `z` is negatively oriented along `t'` in the chart at `a'`. -/
theorem orEpsB_frameOr_A' : orEpsB (Basis.singleton (Fin 1) ℝ)
    (frameOr (finrank_self ℝ) ((sphOrStd 3).or ptA') uA' ιA') = -1 := by
  rw [LinkAlg.orEpsB_congr (frameOr_basis_iff (finrank_self ℝ) ((sphOrStd 3).or ptA') uA' ιA'
    (Basis.singleton (Fin 1) ℝ) eVA' coe_eVA').symm]
  refine LinkAlg.orEpsB_eq_neg_one' fun h => ?_
  have h2 := (orientation_eq_sphOrStd_iff ptA' eVA').1 h
  rw [det_eVA'] at h2
  norm_num at h2

/-! ### The direction map at `(a, a')` -/

theorem inner3 (x y : 𝔼 3) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

/-- `w₀ = stN a − stN a'`. -/
def w₀ : 𝔼 3 := stereoTop ptA.1 - stereoTop ptA'.1

theorem w₀_eq : w₀ = (2 * (Real.sqrt 2 - 1)) • !₂[0, -1, 0] := by
  rw [w₀, ptA_val, ptA'_val, stereoTop_hopfA, stereoTop_hopfA']
  ext i
  fin_cases i <;> simp
  ring

theorem w₀_ne_zero : w₀ ≠ 0 := by
  rw [w₀_eq]
  refine smul_ne_zero (by nlinarith [one_lt_sqrt2] : (0 : ℝ) < 2 * (Real.sqrt 2 - 1)).ne' ?_
  intro h
  have h1 := congrArg (fun v : 𝔼 3 => v 1) h
  simp at h1

theorem lamR_ptA : LinkDeg.lamR (d := 1) R₀ (ptA, ptA') = hopfE := by
  show nv0 (stN (ptA.1 : 𝔼 4) - stN (ptA'.1 : 𝔼 4) : 𝔼 3) = hopfE
  rw [stN_eq_stereoTop]
  show nv0 w₀ = hopfE
  rw [w₀_eq, nv0_smul (by nlinarith [one_lt_sqrt2])]
  exact nv0_of_mem hopfE

/-- The derivative of `λ` at `(a, a')`, read in `ℝ³ ⊇ S²`: `dλ(v, v') = N(dst(dι v) − dst(dι v'))`
where `N` is the derivative of `normalize` at `w₀`. -/
theorem exists_mfd_lamR :
    ∃ Dn : 𝔼 3 →L[ℝ] 𝔼 3, (∀ h, ⟪w₀, h⟫ = 0 → Dn h = ‖w₀‖⁻¹ • h) ∧
    ∀ v v' : 𝔼 3,
      mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1))
        (LinkDeg.lamR (d := 1) R₀ (ptA, ptA'))
        (mfd ((𝓘(ℝ, 𝔼 3)).prod 𝓘(ℝ, 𝔼 3)) 𝓘(ℝ, 𝔼 2) (LinkDeg.lamR (d := 1) R₀) (ptA, ptA')
          (v, v')) =
      Dn (fderiv ℝ stereoTop ptA.1
          (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA v) -
        fderiv ℝ stereoTop ptA'.1
          (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA' v')) := by
  obtain ⟨Dn, hDn, hDn'⟩ := exists_hasFDerivAt_normalize w₀_ne_zero
  refine ⟨Dn, hDn', fun v v' => ?_⟩
  have ha3 : (ptA.1 : 𝔼 4) 3 ≠ 1 := by
    rw [ptA_val]; simp; linarith [inv_sqrt2_pos]
  have ha3' : (ptA'.1 : 𝔼 4) 3 ≠ 1 := by
    rw [ptA'_val]; simp; linarith [inv_sqrt2_pos]
  have hsA : HasFDerivAt stereoTop (fderiv ℝ stereoTop ptA.1) ptA.1 :=
    ((contDiffAt_stereoTop ha3).differentiableAt (by simp)).hasFDerivAt
  have hsA' : HasFDerivAt stereoTop (fderiv ℝ stereoTop ptA'.1) ptA'.1 :=
    ((contDiffAt_stereoTop ha3').differentiableAt (by simp)).hasFDerivAt
  have hvA : HasMFDerivAt 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA
      (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA) :=
    hasMFDerivAt_mfd (contMDiff_val.mdifferentiableAt (by simp))
  have hvA' : HasMFDerivAt 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA'
      (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) ptA') :=
    hasMFDerivAt_mfd (contMDiff_val.mdifferentiableAt (by simp))
  have h1 := (hsA.hasMFDerivAt.comp ptA hvA).comp (ptA, ptA')
    (hasMFDerivAt_fst (I := 𝓘(ℝ, 𝔼 3)) (I' := 𝓘(ℝ, 𝔼 3)) (ptA, ptA'))
  have h2 := (hsA'.hasMFDerivAt.comp ptA' hvA').comp (ptA, ptA')
    (hasMFDerivAt_snd (I := 𝓘(ℝ, 𝔼 3)) (I' := 𝓘(ℝ, 𝔼 3)) (ptA, ptA'))
  have hW := h1.sub h2
  have hNW := hDn.hasMFDerivAt.comp (ptA, ptA') hW
  have hlam : MDifferentiableAt ((𝓘(ℝ, 𝔼 3)).prod 𝓘(ℝ, 𝔼 3)) 𝓘(ℝ, 𝔼 2)
      (LinkDeg.lamR (d := 1) R₀) (ptA, ptA') :=
    (LinkDeg.contMDiffAt_lamR mem_domR_ptA).mdifferentiableAt (by simp)
  have hvE : MDifferentiableAt 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1))
      (LinkDeg.lamR (d := 1) R₀ (ptA, ptA')) :=
    contMDiff_val.mdifferentiableAt (by simp)
  have hL := (hasMFDerivAt_mfd hvE).comp (ptA, ptA') (hasMFDerivAt_mfd hlam)
  have hev : (Subtype.val ∘ LinkDeg.lamR (d := 1) R₀) =ᶠ[𝓝 (ptA, ptA')]
      (Sphere.normalize ∘ ((stereoTop ∘ Subtype.val) ∘ Prod.fst -
        (stereoTop ∘ Subtype.val) ∘ Prod.snd)) := by
    filter_upwards [hW.continuousAt.eventually_ne w₀_ne_zero] with q hq
    show (nv0 (stN (q.1.1 : 𝔼 4) - stN (q.2.1 : 𝔼 4) : 𝔼 3)).1 =
      Sphere.normalize (stereoTop q.1.1 - stereoTop q.2.1)
    rw [stN_eq_stereoTop]
    exact nv0_val hq
  have huniq := hasMFDerivAt_unique hL (hNW.congr_of_eventuallyEq hev)
  exact DFunLike.congr_fun huniq (v, v')

/-- `c = (√2 − 1)/‖w₀‖ > 0`. -/
def cl : ℝ := ‖w₀‖⁻¹ * (Real.sqrt 2 - 1)

theorem cl_pos : 0 < cl :=
  mul_pos (inv_pos.2 (norm_pos_iff.2 w₀_ne_zero)) (by linarith [one_lt_sqrt2])

/-- `dλ(t, 0) = c (1, 0, 1)`. -/
theorem mfd_lamR_t :
    mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1))
      (LinkDeg.lamR (d := 1) R₀ (ptA, ptA'))
      (mfd ((𝓘(ℝ, 𝔼 3)).prod 𝓘(ℝ, 𝔼 3)) 𝓘(ℝ, 𝔼 2) (LinkDeg.lamR (d := 1) R₀) (ptA, ptA')
        (vt, 0)) = cl • !₂[1, 0, 1] := by
  obtain ⟨Dn, hDn, hmfd⟩ := exists_mfd_lamR
  have h1 : fderiv ℝ stereoTop ptA.1 ((Real.sqrt 2)⁻¹ • !₂[1, 0, 1, 0]) =
      (Real.sqrt 2 - 1) • !₂[1, 0, 1] := stereoTop_fderiv_hopfA_t
  rw [hmfd, mfd_vt, map_zero, map_zero, sub_zero, h1, hDn, smul_smul]
  · rfl
  · rw [w₀_eq, inner3]
    simp

/-- `dλ(0, t') = c (1, 0, −1)`. -/
theorem mfd_lamR_t' :
    mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1))
      (LinkDeg.lamR (d := 1) R₀ (ptA, ptA'))
      (mfd ((𝓘(ℝ, 𝔼 3)).prod 𝓘(ℝ, 𝔼 3)) 𝓘(ℝ, 𝔼 2) (LinkDeg.lamR (d := 1) R₀) (ptA, ptA')
        (0, vt')) = cl • !₂[1, 0, -1] := by
  obtain ⟨Dn, hDn, hmfd⟩ := exists_mfd_lamR
  have h1 : fderiv ℝ stereoTop ptA'.1 ((Real.sqrt 2)⁻¹ • !₂[-1, 0, 1, 0]) =
      (Real.sqrt 2 - 1) • !₂[-1, 0, 1] := stereoTop_fderiv_hopfA'_t'
  have h2 : (0 : 𝔼 3) - (Real.sqrt 2 - 1) • !₂[-1, 0, 1] = (Real.sqrt 2 - 1) • !₂[1, 0, -1] := by
    ext i
    fin_cases i <;> simp
  rw [hmfd, mfd_vt', map_zero, map_zero, h1, h2, hDn, smul_smul]
  · rfl
  · rw [w₀_eq, inner3]
    simp

/-- The images `dλ(t, 0)`, `dλ(0, t')` in the chart space at `e`. -/
def βl : Fin 2 → 𝔼 2 :=
  ![mfd ((𝓘(ℝ, 𝔼 3)).prod 𝓘(ℝ, 𝔼 3)) 𝓘(ℝ, 𝔼 2) (LinkDeg.lamR (d := 1) R₀) (ptA, ptA') (vt, 0),
    mfd ((𝓘(ℝ, 𝔼 3)).prod 𝓘(ℝ, 𝔼 3)) 𝓘(ℝ, 𝔼 2) (LinkDeg.lamR (d := 1) R₀) (ptA, ptA') (0, vt')]

theorem mfd_val_βl : (fun i => mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1))
    (LinkDeg.lamR (d := 1) R₀ (ptA, ptA')) (βl i)) = ![cl • !₂[1, 0, 1], cl • !₂[1, 0, -1]] := by
  funext i
  fin_cases i
  · exact mfd_lamR_t
  · exact mfd_lamR_t'

/-- `det(e, c (1, 0, 1), c (1, 0, −1)) = −2 c²`. -/
theorem det_βl : (EuclideanSpace.basisFun (Fin (2 + 1)) ℝ).toBasis.det
    (Matrix.vecCons (LinkDeg.lamR (d := 1) R₀ (ptA, ptA')).1 fun i =>
      mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1))
        (LinkDeg.lamR (d := 1) R₀ (ptA, ptA')) (βl i)) = -2 * cl ^ 2 := by
  rw [mfd_val_βl, lamR_ptA, hopfE_val, Basis.det_apply, Matrix.det_fin_three]
  simp [Basis.toMatrix_apply]
  ring

theorem linearIndependent_βl : LinearIndependent ℝ βl :=
  linearIndependent_of_det_ne_zero (n := 2) (LinkDeg.lamR (d := 1) R₀ (ptA, ptA')) βl
    (ne_of_eq_of_ne det_βl (mul_ne_zero (by norm_num) (pow_ne_zero 2 cl_pos.ne')))

/-- The basis `(dλ(t, 0), dλ(0, t'))` of the chart space at `e`. -/
def ξe : Basis (Fin 2) ℝ (𝔼 2) :=
  basisOfLinearIndependentOfCardEqFinrank' βl linearIndependent_βl (by simp)

theorem orEpsB_ξe : orEpsB ξe ((sphOrStd 2).or (LinkDeg.lamR (d := 1) R₀ (ptA, ptA'))) = -1 := by
  refine LinkAlg.orEpsB_eq_neg_one' fun h => ?_
  have h2 := (orientation_eq_sphOrStd_iff (n := 2) _ ξe).1 h
  simp only [ξe, coe_basisOfLinearIndependentOfCardEqFinrank'] at h2
  rw [det_βl] at h2
  nlinarith [cl_pos]

/-! ### The sign of `Φ` at `(a, a')` -/

/-- The reduced `2 × 2` sign: `sgn((−1)(−1)(−1)) = −1`. -/
theorem orSign_lam :
    orSign (Orientation.reindex ℝ (ℝ × ℝ) (finCongr (rfl : 1 + 1 = 1 + 1))
        (orProdGen (finrank_self ℝ) (finrank_self ℝ)
          (frameOr (finrank_self ℝ) ((sphOrStd 3).or ptA) uA ιA)
          (frameOr (finrank_self ℝ) ((sphOrStd 3).or ptA') uA' ιA')))
      ((sphOrStd 2).or (LinkDeg.lamR (d := 1) R₀ (ptA, ptA')))
      ((mfd ((𝓘(ℝ, 𝔼 3)).prod 𝓘(ℝ, 𝔼 3)) 𝓘(ℝ, 𝔼 2) (LinkDeg.lamR (d := 1) R₀) (ptA, ptA')).comp
        (ιA.prodMap ιA')) = -1 := by
  rw [LinkAlg.orSign_eq_sgn_det (finrank_prod_eq (finrank_self ℝ) (finrank_self ℝ)) _ _
      ((prodBasis (Basis.singleton (Fin 1) ℝ) (Basis.singleton (Fin 1) ℝ)).reindex
        (finCongr (rfl : 1 + 1 = 1 + 1))) ξe,
    LinkAlg.orEpsB_reindex, LinkAlg.orEpsB_prodBasis, orEpsB_frameOr_A, orEpsB_frameOr_A',
    orEpsB_ξe]
  have hfam : (fun i => ((mfd ((𝓘(ℝ, 𝔼 3)).prod 𝓘(ℝ, 𝔼 3)) 𝓘(ℝ, 𝔼 2)
      (LinkDeg.lamR (d := 1) R₀) (ptA, ptA')).comp (ιA.prodMap ιA'))
        (((prodBasis (Basis.singleton (Fin 1) ℝ) (Basis.singleton (Fin 1) ℝ)).reindex
          (finCongr (rfl : 1 + 1 = 1 + 1))) i)) = ⇑ξe := by
    funext i
    fin_cases i
    · show ((mfd ((𝓘(ℝ, 𝔼 3)).prod 𝓘(ℝ, 𝔼 3)) 𝓘(ℝ, 𝔼 2)
          (LinkDeg.lamR (d := 1) R₀) (ptA, ptA')).comp (ιA.prodMap ιA'))
          (((prodBasis (Basis.singleton (Fin 1) ℝ) (Basis.singleton (Fin 1) ℝ)).reindex
            (finCongr (rfl : 1 + 1 = 1 + 1))) ⟨0, by norm_num⟩) = ξe ⟨0, by norm_num⟩
      rw [Basis.reindex_apply, finCongr_refl, Equiv.refl_symm, Equiv.refl_apply,
        LinkAlg.prodBasis_apply_left _ _ (i := ⟨0, by norm_num⟩) (j := 0) rfl]
      simp [ξe, βl, ιA, ιA']
    · show ((mfd ((𝓘(ℝ, 𝔼 3)).prod 𝓘(ℝ, 𝔼 3)) 𝓘(ℝ, 𝔼 2)
          (LinkDeg.lamR (d := 1) R₀) (ptA, ptA')).comp (ιA.prodMap ιA'))
          (((prodBasis (Basis.singleton (Fin 1) ℝ) (Basis.singleton (Fin 1) ℝ)).reindex
            (finCongr (rfl : 1 + 1 = 1 + 1))) ⟨1, by norm_num⟩) = ξe ⟨1, by norm_num⟩
      rw [Basis.reindex_apply, finCongr_refl, Equiv.refl_symm, Equiv.refl_apply,
        LinkAlg.prodBasis_apply_right _ _ (i := ⟨1, by norm_num⟩) (j := 0) rfl]
      simp [ξe, βl, ιA, ιA']
  rw [hfam, Basis.det_self]
  norm_num [sgn_neg]

/-- **The sign of `Φ = phiR π π id ∘ val` at `(a, a')` is `−1`.** -/
theorem signAt_q₀ : signAt (orDomR (d := 1) R₀) orTarget
    (phiR (d := 1) hopfMap hopfMap R₀ ∘ Subtype.val) q₀ = -1 := by
  have hlam : MDifferentiableAt ((𝓘(ℝ, 𝔼 3)).prod 𝓘(ℝ, 𝔼 3)) 𝓘(ℝ, 𝔼 2)
      (LinkDeg.lamR (d := 1) R₀) (ptA, ptA') :=
    (LinkDeg.contMDiffAt_lamR mem_domR_ptA).mdifferentiableAt (by simp)
  have hgd : MDifferentiableAt 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA :=
    contMDiff_hopfMap.mdifferentiableAt (by simp)
  have hfd : MDifferentiableAt 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA' :=
    contMDiff_hopfMap.mdifferentiableAt (by simp)
  have hΦ : HasMFDerivAt ((𝓘(ℝ, 𝔼 3)).prod 𝓘(ℝ, 𝔼 3))
      ((𝓘(ℝ, 𝔼 2).prod 𝓘(ℝ, 𝔼 2)).prod 𝓘(ℝ, 𝔼 2))
      (phiR (d := 1) hopfMap hopfMap R₀) (ptA, ptA')
      ((((mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA).prodMap
        (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA')).prod
        (mfd ((𝓘(ℝ, 𝔼 3)).prod 𝓘(ℝ, 𝔼 3)) 𝓘(ℝ, 𝔼 2) (LinkDeg.lamR (d := 1) R₀)
          (ptA, ptA')) :)) :=
    ((hasMFDerivAt_mfd hgd).prodMap (hasMFDerivAt_mfd hfd)).prodMk (hasMFDerivAt_mfd hlam)
  have hmfd := (mfd_comp_subtype_val (domR (d := 1) R₀) (y := q₀) hΦ.mdifferentiableAt).trans
    (HasMFDerivAt.mfd_eq hΦ)
  have key := LinkDeg.orSign_pair_preimage₂ (d := 1) (p := 2) (k := 2) rfl rfl
    hZ hZ (finrank_self ℝ) (finrank_self ℝ) hZ
    ((sphOrStd 3).or ptA) ((sphOrStd 3).or ptA')
    ((sphOrStd 2).or (hopfMap ptA)) ((sphOrStd 2).or (hopfMap ptA'))
    ((sphOrStd 2).or (LinkDeg.lamR (d := 1) R₀ (ptA, ptA')))
    ιA (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA) hιA hkerA uA linearIndependent_D_uA
    orientation_D_uA
    ιA' (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap ptA') hιA' hkerA' uA' linearIndependent_D_uA'
    orientation_D_uA'
    (mfd ((𝓘(ℝ, 𝔼 3)).prod 𝓘(ℝ, 𝔼 3)) 𝓘(ℝ, 𝔼 2) (LinkDeg.lamR (d := 1) R₀) (ptA, ptA'))
  exact (congrArg (orSign _ _) hmfd).trans (key.trans
    ((congrArg (fun s => (-1 : ℤ) ^ (1 * 2) * s) orSign_lam).trans (by norm_num)))

/-! ### The preimage of `((y, z), e)` -/

theorem eq_q₀_of_phiR (q : domR (d := 1) R₀)
    (hq : phiR (d := 1) hopfMap hopfMap R₀ q.1 = ((hopfY, hopfZ), hopfE)) : q = q₀ := by
  obtain ⟨⟨x, x'⟩, hmem⟩ := q
  have h1 : hopfMap x = hopfY := congrArg (fun w => w.1.1) hq
  have h2 : hopfMap x' = hopfZ := congrArg (fun w => w.1.2) hq
  have h3 : (nv0 (stN (x.1 : 𝔼 4) - stN (x'.1 : 𝔼 4) : 𝔼 3) : Sph 2) = hopfE :=
    congrArg Prod.snd hq
  obtain ⟨hx, hx', hxx'⟩ := mem_domR.1 hmem
  have hu : (x : Sph (2 + 1)) ≠ north := fun h => hx (congrArg Subtype.val h)
  have hv : (x' : Sph (2 + 1)) ≠ north := fun h => hx' (congrArg Subtype.val h)
  have hw : stN (x.1 : 𝔼 4) - stN (x'.1 : 𝔼 4) ≠ 0 := stN_sub_ne_zero hu hv hxx'
  have h4 := congrArg Subtype.val h3
  rw [nv0_val hw, Sphere.normalize, hopfE_val] at h4
  have h5 : stN (x.1 : 𝔼 4) - stN (x'.1 : 𝔼 4) =
      ‖stN (x.1 : 𝔼 4) - stN (x'.1 : 𝔼 4)‖ • !₂[0, -1, 0] := by
    rw [← h4, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hw), one_smul]
  rw [stN_eq_stereoTop] at h5 hw
  have hpair := (hopf_link_pair_iff x x' (congrArg Subtype.val h1) (congrArg Subtype.val h2)).1
    ⟨_, norm_pos_iff.2 hw, h5⟩
  exact Subtype.ext (Prod.ext (Subtype.ext hpair.1) (Subtype.ext hpair.2))

theorem preimage_phiR : (phiR (d := 1) hopfMap hopfMap R₀ ∘ Subtype.val) ⁻¹'
    {((hopfY, hopfZ), hopfE)} = {q₀} := by
  ext q
  simp only [mem_preimage, mem_singleton_iff, Function.comp_apply]
  refine ⟨eq_q₀_of_phiR q, ?_⟩
  rintro rfl
  show ((hopfMap ptA, hopfMap ptA'), LinkDeg.lamR (d := 1) R₀ (ptA, ptA')) =
    ((hopfY, hopfZ), hopfE)
  rw [hopfMap_ptA, hopfMap_ptA', lamR_ptA]

/-- **The local degree of `Φ` at `((y, z), e)` is `−1`.** -/
theorem degAt_hopf : degAt (orDomR (d := 1) R₀) orTarget
    (phiR (d := 1) hopfMap hopfMap R₀ ∘ Subtype.val) ((hopfY, hopfZ), hopfE) = -1 := by
  unfold degAt
  rw [preimage_phiR, finsum_mem_singleton, signAt_q₀]

/-! ### Admissibility of the identity rotation -/

theorem hopf_disj : ∀ x x' : Sph 3, hopfMap x = hopfY → hopfMap x' = hopfZ → x ≠ x' := by
  rintro x x' hx hx' rfl
  have h := congrArg (fun q : Sph 2 => q.1 0) (hx.symm.trans hx')
  simp [hopfY, hopfZ] at h
  norm_num at h

theorem isRotation_refl : IsRotation (LinearIsometryEquiv.refl ℝ (𝔼 4)) := by
  unfold IsRotation
  simp

theorem hopf_north_y : ∀ x : Sph 3, hopfMap x = hopfY →
    (LinearIsometryEquiv.refl ℝ (𝔼 4)) x.1 ≠ (north : Sph (2 + 1)).1 := by
  intro x hx hn
  have h := (hopfMap_eq_e0_iff x).1 (congrArg Subtype.val hx)
  have h1 := congrArg (fun v : 𝔼 4 => v 1) hn
  have h3 := congrArg (fun v : 𝔼 4 => v 3) hn
  simp [north, northV] at h1 h3
  linarith [h.2]

theorem hopf_north_z : ∀ x : Sph 3, hopfMap x = hopfZ →
    (LinearIsometryEquiv.refl ℝ (𝔼 4)) x.1 ≠ (north : Sph (2 + 1)).1 := by
  intro x hx hn
  have h := (hopfMap_eq_neg_e0_iff x).1 (congrArg Subtype.val hx)
  have h1 := congrArg (fun v : 𝔼 4 => v 1) hn
  have h3 := congrArg (fun v : 𝔼 4 => v 3) hn
  simp [north, northV] at h1 h3
  linarith [h.2]

end HopfSign

open HopfSign

/-- **The direction `e = (0, −1, 0)` is a regular value of the linking map** of the fibres
`π⁻¹(1, 0, 0)` and `π⁻¹(−1, 0, 0)` (projected from the north pole). -/
theorem isRegularValue_linkMap_hopfE :
    letI := (isSliceSubmanifold_preim (d := 1) (p := 2) contMDiff_hopfMap
      (isRegularValue_hopfMap hopfY)).chartedSpace
    letI := (isSliceSubmanifold_preim (d := 1) (p := 2) contMDiff_hopfMap
      (isRegularValue_hopfMap hopfZ)).chartedSpace
    IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin 1)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      (linkMap (fun x : hopfMap ⁻¹' {hopfY} =>
          stN (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 4)) x.1.1))
        (fun x : hopfMap ⁻¹' {hopfZ} =>
          stN (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 4)) x.1.1))) hopfE := by
  let _ := (isSliceSubmanifold_preim (d := 1) (p := 2) contMDiff_hopfMap
    (isRegularValue_hopfMap hopfY)).chartedSpace
  have _ := (isSliceSubmanifold_preim (d := 1) (p := 2) contMDiff_hopfMap
    (isRegularValue_hopfMap hopfY)).isManifold
  let _ := (isSliceSubmanifold_preim (d := 1) (p := 2) contMDiff_hopfMap
    (isRegularValue_hopfMap hopfZ)).chartedSpace
  have _ := (isSliceSubmanifold_preim (d := 1) (p := 2) contMDiff_hopfMap
    (isRegularValue_hopfMap hopfZ)).isManifold
  obtain ⟨ey, hey⟩ := exists_basis_orientation_sphOrStd (p := 2) (by norm_num) hopfY
  obtain ⟨ez, hez⟩ := exists_basis_orientation_sphOrStd (p := 2) (by norm_num) hopfZ
  intro p hp
  have hp1 : hopfMap p.1.1 = hopfY := p.1.2
  have hp2 : hopfMap p.2.1 = hopfZ := p.2.2
  have hmem : ((p.1.1, p.2.1) : Sph 3 × Sph 3) ∈ domR (d := 1) R₀ :=
    mem_domR.2 ⟨hopf_north_y _ hp1, hopf_north_z _ hp2, hopf_disj _ _ hp1 hp2⟩
  have hphi : phiR (d := 1) hopfMap hopfMap R₀ (p.1.1, p.2.1) = ((hopfY, hopfZ), hopfE) :=
    Prod.ext (Prod.ext hp1 hp2) hp
  have hq : (⟨(p.1.1, p.2.1), hmem⟩ : domR (d := 1) R₀) = q₀ := eq_q₀_of_phiR _ hphi
  have h1 : signAt (orDomR (d := 1) R₀) orTarget (phiR (d := 1) hopfMap hopfMap R₀ ∘ Subtype.val)
      ⟨(p.1.1, p.2.1), hmem⟩ = -1 := by
    rw [hq]; exact signAt_q₀
  have hsign := LinkDeg.signAt_phiR_eq (d := 1) contMDiff_hopfMap contMDiff_hopfMap
    (isRegularValue_hopfMap hopfY) (isRegularValue_hopfMap hopfZ) ey hey ez hez R₀ p
    ⟨(p.1.1, p.2.1), hmem⟩ rfl
  have hne := ne_of_eq_of_ne (hsign.symm.trans h1) (by norm_num : (-1 : ℤ) ≠ 0)
  exact ((signAt_ne_zero_iff (finrank_prod_eq hZ hZ) hZ _ _ _ _).1 hne).2

/-- **The linking number of the fibres of the Hopf fibration over `(1, 0, 0)` and `(−1, 0, 0)`**
(oriented as preimages, computed after the identity rotation) is `−1`. -/
theorem linkingNumberRot_hopfMap (ey : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hey : ey.orientation = (sphOrStd 2).or hopfY)
    (ez : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hez : ez.orientation = (sphOrStd 2).or hopfZ) :
    letI := (isSliceSubmanifold_preim (d := 1) (p := 2) contMDiff_hopfMap
      (isRegularValue_hopfMap hopfY)).chartedSpace
    haveI := (isSliceSubmanifold_preim (d := 1) (p := 2) contMDiff_hopfMap
      (isRegularValue_hopfMap hopfY)).isManifold
    letI := (isSliceSubmanifold_preim (d := 1) (p := 2) contMDiff_hopfMap
      (isRegularValue_hopfMap hopfZ)).chartedSpace
    haveI := (isSliceSubmanifold_preim (d := 1) (p := 2) contMDiff_hopfMap
      (isRegularValue_hopfMap hopfZ)).isManifold
    linkingNumberRot rfl (preimOr (d := 1) (p := 2) contMDiff_hopfMap
        (isRegularValue_hopfMap hopfY) ey hey)
      (preimOr (d := 1) (p := 2) contMDiff_hopfMap (isRegularValue_hopfMap hopfZ) ez hez)
      Subtype.val Subtype.val (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 4))) = -1 := by
  let _ := (isSliceSubmanifold_preim (d := 1) (p := 2) contMDiff_hopfMap
    (isRegularValue_hopfMap hopfY)).chartedSpace
  have _ := (isSliceSubmanifold_preim (d := 1) (p := 2) contMDiff_hopfMap
    (isRegularValue_hopfMap hopfY)).isManifold
  let _ := (isSliceSubmanifold_preim (d := 1) (p := 2) contMDiff_hopfMap
    (isRegularValue_hopfMap hopfZ)).chartedSpace
  have _ := (isSliceSubmanifold_preim (d := 1) (p := 2) contMDiff_hopfMap
    (isRegularValue_hopfMap hopfZ)).isManifold
  have h := degAt_phiR_eq_linkingNumberRot (d := 1) le_rfl contMDiff_hopfMap contMDiff_hopfMap
    (isRegularValue_hopfMap hopfY) (isRegularValue_hopfMap hopfZ) ey hey ez hez
    hopf_disj isRotation_refl hopf_north_y hopf_north_z isRegularValue_linkMap_hopfE
  exact h.symm.trans degAt_hopf

end Problems

end Milnor
