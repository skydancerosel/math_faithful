import Milnor.Chapter8.Linking
import Milnor.Chapter7.StdMap
import Milnor.Chapter7.Stereo

/-!
# Linking numbers in the sphere: the definitions

Milnor §8, Problem 13, last sentence: "Define the linking number for disjoint manifolds in the
sphere `S^{m+n+1}`."  The linking number of two maps into `S^{k+1}` is defined after a rotation
`R` of the sphere that moves both images away from the north pole: project stereographically
from the north pole to `ℝᵏ⁺¹` and take the Euclidean linking number of `Linking.lean`.

This file contains only the definitions and the elementary facts about the projection, so that
the independence of the rotation (`LinkingSphere.lean`) and the local-degree description used for
the Hopf invariant (`LinkDegree.lean`) can be developed in parallel.

* `stN x = (x₀, …, x_k) / (1 − x_{k+1})`, stereographic projection from `north = e_{k+1}`;
* `ι (stN x) = stereo north x` (Chapter 7's projection into the equatorial hyperplane);
* `stN` is injective on `S^{k+1} ∖ {north}` and smooth near every point with `x_{k+1} ≠ 1`;
* `IsRotation R`: `R` is a linear isometry of `ℝᵏ⁺²` of positive determinant;
* `linkingNumberRot hk oA oB α β R`: the linking number of `stN ∘ R ∘ α` and `stN ∘ R ∘ β`.
-/

open Set Function
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Problems

open Sphere

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

variable {k : ℕ}

/-! ### Stereographic projection from the north pole -/

/-- Forgetting the last coordinate, `ℝᵏ⁺² → ℝᵏ⁺¹`. -/
def dropLastₗ : 𝔼 (k + 2) →ₗ[ℝ] 𝔼 (k + 1) where
  toFun x := WithLp.toLp 2 (fun i : Fin (k + 1) => x (Fin.castSucc i))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

/-- Forgetting the last coordinate, as a continuous linear map. -/
def dropLast : 𝔼 (k + 2) →L[ℝ] 𝔼 (k + 1) := LinearMap.toContinuousLinearMap dropLastₗ

theorem dropLast_apply (x : 𝔼 (k + 2)) (i : Fin (k + 1)) :
    dropLast x i = x (Fin.castSucc i) := by
  show (WithLp.toLp 2 (fun i : Fin (k + 1) => x (Fin.castSucc i)) : 𝔼 (k + 1)) i = _
  simp

/-- **Stereographic projection from the north pole** `e_{k+1}` of `ℝᵏ⁺²` onto `ℝᵏ⁺¹`. -/
def stN (x : 𝔼 (k + 2)) : 𝔼 (k + 1) := (1 - x (Fin.last (k + 1)))⁻¹ • dropLast x

/-- The north pole of `S^{k+1}` (Chapter 7's `north`). -/
abbrev northPt : Sph (k + 1) := north

theorem inner_northV_right (x : 𝔼 (k + 2)) : ⟪x, (northV : 𝔼 (k + 2))⟫ = x (Fin.last (k + 1)) := by
  rw [northV, EuclideanSpace.inner_single_right]
  simp

theorem sub_smul_northV (x : 𝔼 (k + 2)) :
    x - x (Fin.last (k + 1)) • (northV : 𝔼 (k + 2)) = ι (dropLast x) := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [ι_apply_last]
    simp [northV]
  · rw [ι_apply_castSucc, dropLast_apply]
    simp [northV, EuclideanSpace.single_apply, Fin.castSucc_ne_last]

/-- `stN` is Chapter 7's projection from the north pole, read in the first coordinates. -/
theorem ι_stN (x : 𝔼 (k + 2)) : ι (stN x) = stereo north x := by
  rw [stereo, north_val, inner_northV_right, sub_smul_northV, stN, map_smul]

/-- A point of `S^{k+1}` other than the north pole has last coordinate `< 1`. -/
theorem last_lt_one_of_ne_north {q : Sph (k + 1)} (hq : q ≠ north) :
    q.1 (Fin.last (k + 1)) < 1 := by
  have h := inner_lt_one_of_ne hq
  rwa [north_val, inner_northV_right] at h

theorem last_lt_one_of_mem_of_ne {x : 𝔼 (k + 2)} (hx : x ∈ Sph (k + 1))
    (hxn : x ≠ (north : Sph (k + 1)).1) : x (Fin.last (k + 1)) < 1 :=
  last_lt_one_of_ne_north (q := ⟨x, hx⟩) fun h => hxn (congrArg Subtype.val h)

/-- **`stN` is injective on `S^{k+1} ∖ {north}`.** -/
theorem stN_injOn {u v : Sph (k + 1)} (hu : u ≠ north) (hv : v ≠ north)
    (h : stN u.1 = stN v.1) : u = v := by
  have h1 : stereo north u.1 = stereo north v.1 := by rw [← ι_stN, ← ι_stN, h]
  apply Subtype.ext
  rw [← stereoInv_stereo hu, ← stereoInv_stereo hv, h1]

theorem stN_sub_ne_zero {u v : Sph (k + 1)} (hu : u ≠ north) (hv : v ≠ north) (huv : u ≠ v) :
    stN u.1 - stN v.1 ≠ 0 := fun h => huv (stN_injOn hu hv (sub_eq_zero.1 h))

/-- `stN` is smooth near every point whose last coordinate is not `1`. -/
theorem contDiffAt_stN {x : 𝔼 (k + 2)} (hx : x (Fin.last (k + 1)) ≠ 1) :
    ContDiffAt ℝ ∞ stN x := by
  have hlast : ContDiff ℝ ∞ (fun y : 𝔼 (k + 2) => y (Fin.last (k + 1))) :=
    (EuclideanSpace.proj (Fin.last (k + 1)) : 𝔼 (k + 2) →L[ℝ] ℝ).contDiff
  have hden : ContDiffAt ℝ ∞ (fun y : 𝔼 (k + 2) => (1 - y (Fin.last (k + 1)))⁻¹) x :=
    ((contDiff_const.sub hlast).contDiffAt).inv (sub_ne_zero.2 (Ne.symm hx))
  exact hden.smul dropLast.contDiff.contDiffAt

/-! ### Rotations and the linking number after a rotation -/

/-- A **rotation** of `ℝᵏ⁺²`: a linear isometry with positive determinant. -/
def IsRotation (R : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2)) : Prop :=
  0 < LinearMap.det (R.toLinearEquiv : 𝔼 (k + 2) →ₗ[ℝ] 𝔼 (k + 2))

theorem rotation_mem_sph (R : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2)) (q : Sph (k + 1)) :
    R q.1 ∈ Sph (k + 1) := by
  rw [mem_iff_norm, LinearIsometryEquiv.norm_map]
  exact mem_iff_norm.1 q.2

section Manifold

variable {a : ℕ} {A : Type*} [TopologicalSpace A] [ChartedSpace (𝔼 a) A]

/-- **Smoothness of `stN ∘ R ∘ α`** when `R ∘ α` avoids the north pole. -/
theorem contMDiff_stN_comp {α : A → Sph (k + 1)}
    (hα : ContMDiff 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (k + 1)) ∞ α) (R : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2))
    (hRN : ∀ x, R (α x).1 ≠ (north : Sph (k + 1)).1) :
    ContMDiff 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (k + 1)) ∞ (fun x => stN (R (α x).1)) := by
  have hRα : ContMDiff 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (k + 2)) ∞ (fun x => R (α x).1) :=
    (R.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contMDiff).comp
      (contMDiff_val.comp hα)
  intro x
  have hx : (R (α x).1) (Fin.last (k + 1)) ≠ 1 :=
    (last_lt_one_of_mem_of_ne (rotation_mem_sph R (α x)) (hRN x)).ne
  exact ContMDiffAt.comp (g := stN) (f := fun x => R (α x).1) x (contDiffAt_stN hx).contMDiffAt
    (hRα x)

end Manifold

/-- The projected maps are disjoint when the maps are disjoint and avoid the north pole after
`R`. -/
theorem stN_comp_disjoint {A B : Type*} {α : A → Sph (k + 1)} {β : B → Sph (k + 1)}
    (hdisj : ∀ x y, α x ≠ β y) (R : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2))
    (hRα : ∀ x, R (α x).1 ≠ (north : Sph (k + 1)).1)
    (hRβ : ∀ y, R (β y).1 ≠ (north : Sph (k + 1)).1) (x : A) (y : B) :
    stN (R (α x).1) ≠ stN (R (β y).1) := by
  intro h
  have hu : (⟨R (α x).1, rotation_mem_sph R (α x)⟩ : Sph (k + 1)) ≠ north :=
    fun h' => hRα x (congrArg Subtype.val h')
  have hv : (⟨R (β y).1, rotation_mem_sph R (β y)⟩ : Sph (k + 1)) ≠ north :=
    fun h' => hRβ y (congrArg Subtype.val h')
  have := congrArg Subtype.val (stN_injOn hu hv h)
  exact hdisj x y (Subtype.ext (R.injective this))


variable {a b : ℕ} {A : Type*} [TopologicalSpace A] [ChartedSpace (𝔼 a) A]
  [IsManifold 𝓘(ℝ, 𝔼 a) ∞ A] {B : Type*} [TopologicalSpace B] [ChartedSpace (𝔼 b) B]
  [IsManifold 𝓘(ℝ, 𝔼 b) ∞ B]

/-- **The linking number of `α` and `β` in `S^{k+1}` after the rotation `R`**: project from the
north pole and take the Euclidean linking number. -/
def linkingNumberRot (hk : a + b = k) (oA : Orient 𝓘(ℝ, 𝔼 a) A a) (oB : Orient 𝓘(ℝ, 𝔼 b) B b)
    (α : A → Sph (k + 1)) (β : B → Sph (k + 1)) (R : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2)) : ℤ :=
  linkingNumber hk oA oB (fun x => stN (R (α x).1)) (fun y => stN (R (β y).1))

end Problems

end Milnor
