import Morse.Chapter6.Submanifold
import Milnor.Chapter6.EulerSphere

/-!
Milnor, *Morse Theory*, §9 (the curvature tensor, pp. 51–54) and the definition of sectional
curvature (p. 100), for the round sphere `Sⁿ ⊆ ℝⁿ⁺¹`.

# The second fundamental form and the curvature of the unit sphere

`Sⁿ = {x ∈ ℝⁿ⁺¹ | ‖x‖ = 1}` is the companion project's `Milnor.Sphere.Sph n`, a slice submanifold
of `ℝⁿ⁺¹` (`Milnor.Sphere.sphSub n`), with tangent space `T_qSⁿ = q^⊥`
(`Milnor.Sphere.mem_range_mfd_val_iff`).  With the metric induced from `ℝⁿ⁺¹`:

* `Morse.tanProj_sph`: `P_q v = v − ⟪q, v⟫ q`;
* `Morse.secondFundForm_sph`: **the second fundamental form is `II_q(v, w) = −⟪v, w⟫ q`**;
* `Morse.curvOp_sph`, `Morse.curvTensor_sph`: by the Gauss equation, **the curvature tensor is
  `R(x, y)z = ⟪x, z⟫ y − ⟪y, z⟫ x`** (with Milnor's sign), i.e. `Morse.curvatureOne` of
  `Morse/Chapter6/CurvatureAlgebra.lean`;
* `Morse.sectionalCurvature_sph`, `Morse.inner_curvTensor_sph_orthonormal`: **`Sⁿ` has constant
  sectional curvature `1`**, both in the form `K(x, y) = 1` for linearly independent tangent
  vectors and in Milnor's form `⟨R(A, B)A, B⟩ = 1` for orthonormal `A, B` (p. 100).

Milnor uses the constant curvature of the sphere in §19–§20 without computing it; the exposition
(Chapter 6, §8) computes it in latitude–longitude coordinates.  Here the computation is
coordinate-free: `P_y = 1 − y yᵀ` near the sphere, so `D_v w = −⟪v, w⟫ q − ⟪q, w⟫ v`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

open Milnor.Sphere

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (n + 1))

theorem mem_tangentSubspace_sph_iff (q : Sph n) (w : 𝔼) :
    w ∈ tangentSubspace (sphSub n) q ↔ ⟪(q : 𝔼), w⟫ = 0 :=
  mem_range_mfd_val_iff q w

theorem inner_self_sph (q : Sph n) : ⟪(q : 𝔼), (q : 𝔼)⟫ = 1 :=
  inner_self_eq_one_of_mem q.2

/-- **The tangent projection of the sphere**: `P_q v = v − ⟪q, v⟫ q`. -/
theorem tanProj_sph (q : Sph n) (v : 𝔼) :
    tanProj (sphSub n) q v = v - ⟪(q : 𝔼), v⟫ • (q : 𝔼) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [mem_tangentSubspace_sph_iff, inner_sub_right, real_inner_smul_right, inner_self_sph,
      mul_one, sub_self]
  · intro w hw
    rw [mem_tangentSubspace_sph_iff] at hw
    rw [sub_sub_cancel, real_inner_smul_left, hw, mul_zero]

theorem tanProj_sph_self (q : Sph n) : tanProj (sphSub n) q q = 0 := by
  rw [tanProj_sph, inner_self_sph, one_smul, sub_self]

/-- **The second fundamental form of the unit sphere**: `II_q(v, w) = −⟪v, w⟫ q` for tangent
vectors `v, w` (the outward normal is `q`). -/
theorem secondFundForm_sph {q : Sph n} {v w : 𝔼} (hv : v ∈ tangentSubspace (sphSub n) q)
    (hw : w ∈ tangentSubspace (sphSub n) q) :
    secondFundForm (sphSub n) q v w = -⟪v, w⟫ • (q : 𝔼) := by
  let _ := (sphSub n).chartedSpace
  have hW := contMDiff_projField (sphSub n) w
  have h := secondFundForm_eq_sub_tanProj (sphSub n) (isTangentField_projField (sphSub n) w)
    (hW.mdifferentiableAt (by simp)) hv
  rw [projField_apply_of_mem (sphSub n) hw] at h
  -- the ambient representative `G y = w − ⟪w, y⟫ y` of the field `x ↦ P_x w`
  set G : 𝔼 → 𝔼 := fun y => w - (innerSL ℝ w y) • y with hG
  have hGd : HasFDerivAt G (0 - ((innerSL ℝ w (q : 𝔼)) • ContinuousLinearMap.id ℝ 𝔼 +
      (innerSL ℝ w).smulRight (q : 𝔼))) (q : 𝔼) :=
    (hasFDerivAt_const w (q : 𝔼)).sub ((innerSL ℝ w).hasFDerivAt.smul (hasFDerivAt_id _))
  have hev : ∀ᶠ x : Sph n in 𝓝 q, projField (sphSub n) w x = G x :=
    Eventually.of_forall fun x => by
      rw [projField, tanProj_sph]
      change w - ⟪(x : 𝔼), w⟫ • (x : 𝔼) = w - (innerSL ℝ w (x : 𝔼)) • (x : 𝔼)
      rw [innerSL_apply_apply, real_inner_comm]
  have hq : ⟪w, (q : 𝔼)⟫ = 0 := by
    rw [real_inner_comm]
    exact (mem_tangentSubspace_sph_iff q w).1 hw
  rw [dN_eq_fderiv (sphSub n) hGd.differentiableAt hev hv, hGd.fderiv] at h
  simp only [zero_sub, neg_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hq,
    zero_smul, zero_add] at h
  rw [h, map_neg, map_smul, tanProj_sph_self, smul_zero, neg_zero, sub_zero,
    real_inner_comm, neg_smul]

/-- **The curvature of the unit sphere**: `R(x, y)z = ⟪x, z⟫ y − ⟪y, z⟫ x` (Milnor's sign) for
tangent vectors, from the Gauss equation. -/
theorem curvOp_sph {q : Sph n} {x y z : 𝔼} (hx : x ∈ tangentSubspace (sphSub n) q)
    (hy : y ∈ tangentSubspace (sphSub n) q) (hz : z ∈ tangentSubspace (sphSub n) q) :
    curvOp (sphSub n) q x y z = ⟪x, z⟫ • y - ⟪y, z⟫ • x := by
  have hm : curvOp (sphSub n) q x y z - (⟪x, z⟫ • y - ⟪y, z⟫ • x) ∈
      tangentSubspace (sphSub n) q :=
    Submodule.sub_mem _ (curvOp_mem (sphSub n) hx hy hz)
      (Submodule.sub_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx))
  refine sub_eq_zero.1 ?_
  refine eq_zero_of_mem_of_mem_orthogonal (sphSub n) hm ?_
  rw [Submodule.mem_orthogonal]
  intro w hw
  rw [real_inner_comm, inner_sub_left, inner_curvOp, secondFundForm_sph hx hz,
    secondFundForm_sph hy hw, secondFundForm_sph hx hw, secondFundForm_sph hy hz]
  simp only [real_inner_smul_left, real_inner_smul_right, inner_self_sph, inner_sub_left,
    mul_one]
  ring

/-- **The curvature tensor of `Sⁿ` is that of constant curvature `1`**: on `T_qSⁿ`,
`R = Morse.curvatureOne`, `R(x, y)z = ⟪x, z⟫ y − ⟪y, z⟫ x`. -/
theorem curvTensor_sph (q : Sph n) : curvTensor (sphSub n) q = curvatureOne := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => LinearMap.ext fun z => Subtype.ext ?_
  simp only [coe_curvTensor_apply, curvatureOne_apply, Submodule.coe_sub, Submodule.coe_smul,
    Submodule.coe_inner]
  exact curvOp_sph x.2 y.2 z.2

/-- **`Sⁿ` has constant sectional curvature `1`.** -/
theorem sectionalCurvature_sph (q : Sph n) {x y : tangentSubspace (sphSub n) q}
    (h : LinearIndependent ℝ ![x, y]) : sectionalCurvature (curvTensor (sphSub n) q) x y = 1 := by
  rw [curvTensor_sph, ← one_smul ℝ (curvatureOne : tangentSubspace (sphSub n) q →ₗ[ℝ] _)]
  exact sectionalCurvature_smul_curvatureOne 1 h

/-- **`Sⁿ` has sectional curvature `1` in Milnor's form** (p. 100): `⟨R(A, B)A, B⟩ = 1` for an
orthonormal pair of tangent vectors. -/
theorem inner_curvTensor_sph_orthonormal (q : Sph n) {A B : tangentSubspace (sphSub n) q}
    (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hAB : ⟪A, B⟫ = 0) :
    ⟪curvTensor (sphSub n) q A B A, B⟫ = 1 := by
  rw [curvTensor_sph, inner_curvatureOne_self, hA, hB, hAB]
  norm_num

end Morse
