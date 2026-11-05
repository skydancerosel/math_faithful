import Milnor.Chapter8.LinkingDefs
import Milnor.Chapter8.Generic
import Milnor.Chapter7.Rotation
import Milnor.Chapter8.SphereMaps

/-!
# Linking numbers in the sphere

Milnor, *Topology from the Differentiable Viewpoint*, §8, Problem 13, last sentence: "Define the
linking number for disjoint manifolds in the sphere `S^{m+n+1}`."

Let `A`, `B` be compact oriented boundaryless manifolds of dimensions `a, b ≥ 1`, `k = a + b`, and
let `α : A → S^{k+1}`, `β : B → S^{k+1}` be smooth maps with disjoint images.  A rotation `R` of
`ℝᵏ⁺²` is *admissible* if `R ∘ α` and `R ∘ β` avoid the north pole; then
`linkingNumberRot hk oA oB α β R` (`LinkingDefs.lean`) is the Euclidean linking number of the
stereographic projections `stN ∘ R ∘ α` and `stN ∘ R ∘ β` in `ℝᵏ⁺¹`.

* `exists_admissible_rotation`: admissible rotations exist (the images are meagre, so a point `q`
  avoids them, and a planar rotation moves `q` to the north pole);
* `linkingNumberSph`: the linking number in the sphere, computed with an admissible rotation
  (`0` if there is none);
* `linkingNumberSph_eq` (**Problem 13, sphere part**): `linkingNumberRot` is the same for all
  admissible rotations, hence equal to `linkingNumberSph`.

The hypothesis `a, b ≥ 1` is needed: for a point and a great sphere the Euclidean linking number is
`±1` or `0` depending on the side of the great sphere on which the projection point lies.

## Proof of the independence (namespace `LinkSph`)

1. `linkingNumber_comp_linear`: for `det T > 0`, `λ_{Tα,Tβ} = (u ↦ Tu/|Tu|) ∘ λ_{α,β}`, and
   `u ↦ Tu/|Tu|` is a bijection of `Sᵏ` of constant sign `+1` (`signAt_nv0_linear`).
2. `linkingNumberRot_trans_of_fix`: a rotation `Q` fixing the north pole satisfies
   `stN ∘ Q = T_Q ∘ stN` for its block `T_Q` on the first `k + 1` coordinates, and
   `det T_Q = det Q > 0` (Laplace expansion along the last column).
3. `linkingNumberRot_eq_of_family`: along a smooth family of rotations keeping both images off the
   north pole for `t ∈ [0, 1]`, the linking maps (with time reparametrized by
   `Real.smoothTransition`) form a smooth homotopy on `A × B`.
4. For `q, q'` in the sphere there is `w ≠ -q, -q'` such that the minor arcs `q → w` and `q' → w`
   avoid the images: a point `c ≠ q` on the arc from `q` to `w` gives `w = (c − r q)/|c − r q|`
   for some `r ∈ ℝ`, and the "cones" `(x, r) ↦ (α x − r q)/|α x − r q|` are smooth maps from
   manifolds of dimension `a + 1, b + 1 ≤ k` into the `(k+1)`-sphere, so their images are meagre
   (`isMeagre_image_of_finrank_lt`), and the sphere is a Baire space.
5. `linkingNumberRot_eq_of_admissible`: for admissible `R, R'`, follow the arcs from `R⁻¹(north)`
   and `R'⁻¹(north)` to `w` by planar rotations (step 3); the resulting rotations `S, S'` both send
   `w` to the north pole, and `S = (S ∘ S'⁻¹) ∘ S'` with `S ∘ S'⁻¹` fixing it (step 2).
-/

open Set Function Module Real
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Problems

open Sphere

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

namespace LinkSph

/-! ### Elementary facts -/

private theorem sph_ne_zero {n : ℕ} (u : Sph n) : u.1 ≠ 0 := fun h => by
  have hu := mem_iff_norm.1 u.2
  rw [h, norm_zero] at hu
  exact zero_ne_one hu

private theorem nv0_smul_pos {n : ℕ} {c : ℝ} (hc : 0 < c) (y : 𝔼 (n + 1)) :
    nv0 (c • y) = nv0 y := by
  by_cases hy : y = 0
  · simp [hy]
  · have hcy : c • y ≠ 0 := smul_ne_zero hc.ne' hy
    apply Subtype.ext
    rw [nv0_val hcy, nv0_val hy]
    simp only [Sphere.normalize, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_inv, smul_smul]
    congr 1
    field_simp

private theorem nv0_val_sph {n : ℕ} (u : Sph n) : nv0 u.1 = u := by
  apply Subtype.ext
  rw [nv0_val (sph_ne_zero u), Sphere.normalize, mem_iff_norm.1 u.2, inv_one, one_smul]

private theorem bijective_of_det_pos {n : ℕ} {T : 𝔼 n →L[ℝ] 𝔼 n}
    (h : 0 < LinearMap.det (T : 𝔼 n →ₗ[ℝ] 𝔼 n)) : Bijective T := by
  have hu : IsUnit (LinearMap.det (T : 𝔼 n →ₗ[ℝ] 𝔼 n)) := isUnit_iff_ne_zero.2 h.ne'
  have heq : ⇑(LinearMap.equivOfIsUnitDet hu) = T :=
    funext fun x => LinearMap.equivOfIsUnitDet_apply hu x
  rw [← heq]
  exact (LinearMap.equivOfIsUnitDet hu).bijective

/-! ### Step 1: a linear change of the target -/

section linear

variable {k : ℕ}

/-- `u ↦ T u/|T u|` is a bijection of `Sᵏ` when `T` is invertible. -/
private theorem bijective_nv0_linear {T : 𝔼 (k + 1) →L[ℝ] 𝔼 (k + 1)} (hT : Bijective T) :
    Bijective (fun u : Sph k => nv0 (T u.1)) := by
  obtain ⟨Te, hTe⟩ : ∃ Te : 𝔼 (k + 1) ≃ₗ[ℝ] 𝔼 (k + 1), ∀ x, Te x = T x :=
    ⟨LinearEquiv.ofBijective (T : 𝔼 (k + 1) →ₗ[ℝ] 𝔼 (k + 1)) hT, fun x => rfl⟩
  have hTeT : ∀ x, Te.symm (T x) = x := fun x => by rw [← hTe]; exact Te.symm_apply_apply x
  have hTTe : ∀ y, T (Te.symm y) = y := fun y => by rw [← hTe]; exact Te.apply_symm_apply y
  refine bijective_iff_has_inverse.2 ⟨fun u => nv0 (Te.symm u.1), fun u => ?_, fun u => ?_⟩
  · have hne : T u.1 ≠ 0 := A_ne_zero hT (sph_ne_zero u)
    change nv0 (Te.symm (nv0 (T u.1)).1) = u
    rw [nv0_val hne, Sphere.normalize, map_smul, hTeT,
      nv0_smul_pos (inv_pos.2 (norm_pos_iff.2 hne)), nv0_val_sph]
  · have hne : Te.symm u.1 ≠ 0 := fun h0 => sph_ne_zero u (by
      have := congrArg Te h0
      rwa [Te.apply_symm_apply, map_zero] at this)
    change nv0 (T (nv0 (Te.symm u.1)).1) = u
    rw [nv0_val hne, Sphere.normalize, map_smul, hTTe,
      nv0_smul_pos (inv_pos.2 (norm_pos_iff.2 hne)), nv0_val_sph]

/-- For `det T > 0`, `u ↦ T u/|T u|` has sign `+1` for Milnor's orientation of `Sᵏ`. -/
private theorem signAt_nv0_linear_std (hk0 : 0 < k) {T : 𝔼 (k + 1) →L[ℝ] 𝔼 (k + 1)}
    (hT : Bijective T) (hdet : 0 < LinearMap.det (T : 𝔼 (k + 1) →ₗ[ℝ] 𝔼 (k + 1))) (u : Sph k) :
    signAt (sphOrStd k) (sphOrStd k) (fun u : Sph k => nv0 (T u.1)) u = 1 := by
  have h := (signAt_nv0_linear hT u).trans (sgn_pos hdet)
  rcases sphOrStd_eq_or_neg hk0 with hs | hs
  · rw [hs]; exact h
  · rw [hs, signAt_neg_left hZ, signAt_neg_right hZ hZ, neg_neg]; exact h

end linear

variable {a b k : ℕ} {A : Type*} [TopologicalSpace A] [ChartedSpace (𝔼 a) A]
  [IsManifold 𝓘(ℝ, 𝔼 a) ∞ A] {B : Type*} [TopologicalSpace B] [ChartedSpace (𝔼 b) B]
  [IsManifold 𝓘(ℝ, 𝔼 b) ∞ B]

/-- **Step 1.** Composing both maps with a linear map `T` of positive determinant does not change
the linking number: `λ_{Tα,Tβ} = (u ↦ Tu/|Tu|) ∘ λ_{α,β}`, and `u ↦ Tu/|Tu|` is a bijection of
`Sᵏ` of constant sign `+1`. -/
theorem linkingNumber_comp_linear [CompactSpace A] [T2Space A] [SecondCountableTopology A]
    [CompactSpace B] [T2Space B] [SecondCountableTopology B] (hk : a + b = k) (hk0 : 0 < k)
    {oA : Orient 𝓘(ℝ, 𝔼 a) A a} {oB : Orient 𝓘(ℝ, 𝔼 b) B b} {α : A → 𝔼 (k + 1)}
    {β : B → 𝔼 (k + 1)} (hα : ContMDiff 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (k + 1)) ∞ α)
    (hβ : ContMDiff 𝓘(ℝ, 𝔼 b) 𝓘(ℝ, 𝔼 (k + 1)) ∞ β) (hdisj : ∀ x y, α x ≠ β y)
    {T : 𝔼 (k + 1) →L[ℝ] 𝔼 (k + 1)} (hdet : 0 < LinearMap.det (T : 𝔼 (k + 1) →ₗ[ℝ] 𝔼 (k + 1))) :
    linkingNumber hk oA oB (fun x => T (α x)) (fun y => T (β y)) = linkingNumber hk oA oB α β := by
  have := preconnectedSpace hk0
  have hT := bijective_of_det_pos hdet
  have hfin : finrank ℝ (𝔼 a × 𝔼 b) = k := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin, hk]
  obtain ⟨oAB, hoAB⟩ : ∃ o, (oA.prod finrank_euclideanSpace_fin finrank_euclideanSpace_fin oB).cast
      hk = o := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : Sph k → Sph k, h = fun u => nv0 (T u.1) := ⟨_, rfl⟩
  have hf := contMDiff_linkMap hα hβ hdisj
  have hhs : ContMDiff 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k) ∞ h := by
    rw [hh]
    exact contMDiff_nv0_comp (T.contDiff.contMDiff.comp contMDiff_val)
      (fun u => A_ne_zero hT (sph_ne_zero u))
  have hhb : Bijective h := by rw [hh]; exact bijective_nv0_linear hT
  have hsign : ∀ u, signAt (sphOrStd k) (sphOrStd k) h u = 1 := fun u => by
    rw [hh]; exact signAt_nv0_linear_std hk0 hT hdet u
  have heq : linkMap (fun x => T (α x)) (fun y => T (β y)) = fun p => h (linkMap α β p) := by
    funext p
    have hne : α p.1 - β p.2 ≠ 0 := sub_ne_zero.2 (hdisj p.1 p.2)
    rw [hh]
    change nv0 (T (α p.1) - T (β p.2)) = nv0 (T (nv0 (α p.1 - β p.2)).1)
    rw [← map_sub, nv0_val hne, Sphere.normalize, map_smul,
      nv0_smul_pos (inv_pos.2 (norm_pos_iff.2 hne))]
  have hfd : ∀ p, MDifferentiableAt (𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)) 𝓘(ℝ, 𝔼 k) (linkMap α β) p :=
    fun p => hf.mdifferentiableAt (by simp)
  have hhd : ∀ u, MDifferentiableAt 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k) h u :=
    fun u => hhs.mdifferentiableAt (by simp)
  have hhf : ContMDiff (𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)) 𝓘(ℝ, 𝔼 k) ∞ (fun p => h (linkMap α β p)) :=
    hhs.comp hf
  obtain ⟨z, hz⟩ := (dense_regularValues hf).nonempty
  have hz' : IsRegularValue (𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)) 𝓘(ℝ, 𝔼 k)
      (fun p => h (linkMap α β p)) (h z) := by
    intro p hp
    have hpz : linkMap α β p = z := hhb.1 hp
    rw [← signAt_ne_zero_iff_isRegularPoint hfin finrank_euclideanSpace_fin oAB (sphOrStd k),
      signAt_comp' hfin finrank_euclideanSpace_fin oAB (sphOrStd k) (sphOrStd k) (hfd p) (hhd _),
      hsign, one_mul]
    exact IsRegularPoint.signAt_ne_zero hfin finrank_euclideanSpace_fin oAB (sphOrStd k) (hz _ hpz)
  unfold linkingNumber
  rw [hoAB, heq, deg_eq hfin finrank_euclideanSpace_fin oAB (sphOrStd k) hhf hz',
    deg_eq hfin finrank_euclideanSpace_fin oAB (sphOrStd k) hf hz,
    degAt_comp_bij_left hfin finrank_euclideanSpace_fin oAB (sphOrStd k) (sphOrStd k) hhb hhd
      (Or.inl rfl) hsign hfd rfl, one_mul]

/-! ### Step 2: rotations fixing the north pole -/

section fix

variable {k : ℕ}

/-- The block of a linear map of `ℝᵏ⁺²` on the first `k + 1` coordinates. -/
private def restrictN (Q : 𝔼 (k + 2) →L[ℝ] 𝔼 (k + 2)) : 𝔼 (k + 1) →L[ℝ] 𝔼 (k + 1) :=
  dropLast.comp (Q.comp ι)

private theorem restrictN_apply (Q : 𝔼 (k + 2) →L[ℝ] 𝔼 (k + 2)) (x : 𝔼 (k + 1)) :
    restrictN Q x = dropLast (Q (ι x)) := rfl

private theorem dropLast_northV : dropLast (northV : 𝔼 (k + 2)) = 0 := by
  ext i
  rw [dropLast_apply]
  simp [northV, Fin.castSucc_ne_last]

private theorem ι_single (j : Fin (k + 1)) :
    (ι (EuclideanSpace.single j (1 : ℝ)) : 𝔼 (k + 2)) =
      EuclideanSpace.single (Fin.castSucc j) 1 := by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [ι_apply_last]
    simp [(Fin.castSucc_ne_last j).symm]
  · rw [ι_apply_castSucc]
    simp

/-- A rotation fixing the north pole commutes with the projection `stN` up to its block on the
first `k + 1` coordinates. -/
private theorem stN_map_of_fix (Q : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2)) (hQN : Q northV = northV)
    (x : 𝔼 (k + 2)) :
    stN (Q x) = restrictN (Q.toContinuousLinearEquiv : 𝔼 (k + 2) →L[ℝ] 𝔼 (k + 2)) (stN x) := by
  have hlast : (Q x) (Fin.last (k + 1)) = x (Fin.last (k + 1)) := by
    have h := Q.inner_map_map x northV
    rw [hQN, inner_northV_right, inner_northV_right] at h
    exact h
  have hx : x = ι (dropLast x) + x (Fin.last (k + 1)) • northV := by
    rw [← sub_smul_northV]; abel
  have hdrop : dropLast (Q x) =
      restrictN (Q.toContinuousLinearEquiv : 𝔼 (k + 2) →L[ℝ] 𝔼 (k + 2)) (dropLast x) := by
    conv_lhs => rw [hx]
    rw [map_add, map_smul, hQN, map_add, map_smul, dropLast_northV, smul_zero, add_zero]
    rfl
  unfold stN
  rw [hlast, hdrop, map_smul]

private theorem toMatrix_basisFun_apply {n : ℕ} (L : 𝔼 n →L[ℝ] 𝔼 n) (i j : Fin n) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (L : 𝔼 n →ₗ[ℝ] 𝔼 n) i j =
      L (EuclideanSpace.single j 1) i := by
  simp [LinearMap.toMatrix_apply]

/-- The block of a linear map fixing `e_{k+1}` has the same determinant (Laplace expansion along
the last column). -/
private theorem det_restrictN (Q : 𝔼 (k + 2) →L[ℝ] 𝔼 (k + 2)) (hQN : Q northV = northV) :
    LinearMap.det (restrictN Q : 𝔼 (k + 1) →ₗ[ℝ] 𝔼 (k + 1)) =
      LinearMap.det (Q : 𝔼 (k + 2) →ₗ[ℝ] 𝔼 (k + 2)) := by
  classical
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis,
    ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin (k + 2)) ℝ).toBasis]
  have hQN' : Q (EuclideanSpace.single (Fin.last (k + 1)) 1) =
      EuclideanSpace.single (Fin.last (k + 1)) 1 := hQN
  have hM : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis (restrictN Q : 𝔼 (k + 1) →ₗ[ℝ] 𝔼 (k + 1)) =
      (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (k + 2)) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin (k + 2)) ℝ).toBasis
        (Q : 𝔼 (k + 2) →ₗ[ℝ] 𝔼 (k + 2))).submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    rw [Matrix.submatrix_apply, toMatrix_basisFun_apply, toMatrix_basisFun_apply, restrictN_apply,
      dropLast_apply, ι_single]
  rw [hM, Matrix.det_succ_column _ (Fin.last (k + 1)), Finset.sum_eq_single (Fin.last (k + 1))]
  · rw [toMatrix_basisFun_apply, hQN', Fin.succAbove_last, Fin.val_last,
      Even.neg_one_pow (⟨k + 1, rfl⟩ : Even (k + 1 + (k + 1)))]
    simp
  · intro i _ hi
    rw [toMatrix_basisFun_apply, hQN']
    simp [hi]
  · simp

end fix

/-- **Step 2.** A rotation `Q` fixing the north pole does not change the linking number:
`stN ∘ Q = T_Q ∘ stN` for the block `T_Q` of `Q`, with `det T_Q = det Q > 0`. -/
theorem linkingNumberRot_trans_of_fix [CompactSpace A] [T2Space A] [SecondCountableTopology A]
    [CompactSpace B] [T2Space B] [SecondCountableTopology B] (hk : a + b = k) (hk0 : 0 < k)
    {oA : Orient 𝓘(ℝ, 𝔼 a) A a} {oB : Orient 𝓘(ℝ, 𝔼 b) B b} {α : A → Sph (k + 1)}
    {β : B → Sph (k + 1)} (hα : ContMDiff 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (k + 1)) ∞ α)
    (hβ : ContMDiff 𝓘(ℝ, 𝔼 b) 𝓘(ℝ, 𝔼 (k + 1)) ∞ β) (hdisj : ∀ x y, α x ≠ β y)
    {R Q : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2)} (hQ : IsRotation Q) (hQN : Q northPt.1 = northPt.1)
    (hRα : ∀ x, R (α x).1 ≠ northPt.1) (hRβ : ∀ y, R (β y).1 ≠ northPt.1) :
    linkingNumberRot hk oA oB α β (R.trans Q) = linkingNumberRot hk oA oB α β R := by
  have hQN' : Q northV = northV := hQN
  obtain ⟨T, hT⟩ : ∃ T, restrictN (Q.toContinuousLinearEquiv : 𝔼 (k + 2) →L[ℝ] 𝔼 (k + 2)) = T :=
    ⟨_, rfl⟩
  have hdet : 0 < LinearMap.det (T : 𝔼 (k + 1) →ₗ[ℝ] 𝔼 (k + 1)) := by
    rw [← hT, det_restrictN _ hQN']
    exact hQ
  have h1 : (fun x => stN ((R.trans Q) (α x).1)) = fun x => T (stN (R (α x).1)) :=
    funext fun x => by rw [← hT]; exact stN_map_of_fix Q hQN' _
  have h2 : (fun y => stN ((R.trans Q) (β y).1)) = fun y => T (stN (R (β y).1)) :=
    funext fun y => by rw [← hT]; exact stN_map_of_fix Q hQN' _
  unfold linkingNumberRot
  rw [h1, h2]
  exact linkingNumber_comp_linear hk hk0 (contMDiff_stN_comp hα R hRα) (contMDiff_stN_comp hβ R hRβ)
    (stN_comp_disjoint hdisj R hRα hRβ) hdet

/-! ### Step 3: smooth families of rotations -/

/-- **Step 3.** Along a smooth family of rotations `S t` which keeps both images away from the
north pole for `t ∈ [0, 1]`, the linking number does not change: after reparametrizing time by
`Real.smoothTransition`, the linking maps form a smooth homotopy. -/
theorem linkingNumberRot_eq_of_family [CompactSpace A] [T2Space A] [SecondCountableTopology A]
    [CompactSpace B] [T2Space B] [SecondCountableTopology B] (hk : a + b = k) (hk0 : 0 < k)
    {oA : Orient 𝓘(ℝ, 𝔼 a) A a} {oB : Orient 𝓘(ℝ, 𝔼 b) B b} {α : A → Sph (k + 1)}
    {β : B → Sph (k + 1)} (hα : ContMDiff 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (k + 1)) ∞ α)
    (hβ : ContMDiff 𝓘(ℝ, 𝔼 b) 𝓘(ℝ, 𝔼 (k + 1)) ∞ β) (hdisj : ∀ x y, α x ≠ β y)
    {S : ℝ → 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2)} {F : ℝ → 𝔼 (k + 2) →L[ℝ] 𝔼 (k + 2)}
    (hF : ContDiff ℝ ∞ F) (hSF : ∀ t v, S t v = F t v)
    (hSα : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, S t (α x).1 ≠ northPt.1)
    (hSβ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, S t (β y).1 ≠ northPt.1) :
    linkingNumberRot hk oA oB α β (S 0) = linkingNumberRot hk oA oB α β (S 1) := by
  have := preconnectedSpace hk0
  have hfin : finrank ℝ (𝔼 a × 𝔼 b) = k := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin, hk]
  have hρs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hρI : ∀ t, Real.smoothTransition t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  -- the moving points `S_{ρ t} (α x)` and `S_{ρ t} (β y)`
  obtain ⟨u, hu⟩ : ∃ u : (A × B) × ℝ → 𝔼 (k + 2),
      u = fun q => F (Real.smoothTransition q.2) (α q.1.1).1 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : (A × B) × ℝ → 𝔼 (k + 2),
      v = fun q => F (Real.smoothTransition q.2) (β q.1.2).1 := ⟨_, rfl⟩
  have hus : ContMDiff ((𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼 (k + 2)) ∞ u := by
    rw [hu]
    exact ContMDiff.clm_apply ((hF.comp hρs).contMDiff.comp contMDiff_snd)
      (contMDiff_val.comp (hα.comp (contMDiff_fst.comp contMDiff_fst)))
  have hvs : ContMDiff ((𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼 (k + 2)) ∞ v := by
    rw [hv]
    exact ContMDiff.clm_apply ((hF.comp hρs).contMDiff.comp contMDiff_snd)
      (contMDiff_val.comp (hβ.comp (contMDiff_snd.comp contMDiff_fst)))
  have hueq : ∀ q, u q = S (Real.smoothTransition q.2) (α q.1.1).1 := fun q => by
    rw [hu, hSF]
  have hveq : ∀ q, v q = S (Real.smoothTransition q.2) (β q.1.2).1 := fun q => by
    rw [hv, hSF]
  have huS : ∀ q, u q ∈ Sph (k + 1) := fun q => by rw [hueq]; exact rotation_mem_sph _ _
  have hvS : ∀ q, v q ∈ Sph (k + 1) := fun q => by rw [hveq]; exact rotation_mem_sph _ _
  have huN : ∀ q, u q ≠ northPt.1 := fun q => by rw [hueq]; exact hSα _ (hρI q.2) _
  have hvN : ∀ q, v q ≠ northPt.1 := fun q => by rw [hveq]; exact hSβ _ (hρI q.2) _
  have huv : ∀ q, u q ≠ v q := fun q h => by
    rw [hueq, hveq] at h
    exact hdisj q.1.1 q.1.2 (Subtype.ext ((S _).injective h))
  have hstu : ContMDiff ((𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼 (k + 1)) ∞
      (fun q => stN (u q)) := fun q =>
    ContMDiffAt.comp (g := stN) (f := u) q
      (contDiffAt_stN (last_lt_one_of_mem_of_ne (huS q) (huN q)).ne).contMDiffAt (hus q)
  have hstv : ContMDiff ((𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼 (k + 1)) ∞
      (fun q => stN (v q)) := fun q =>
    ContMDiffAt.comp (g := stN) (f := v) q
      (contDiffAt_stN (last_lt_one_of_mem_of_ne (hvS q) (hvN q)).ne).contMDiffAt (hvs q)
  have hne : ∀ q, stN (u q) - stN (v q) ≠ 0 := fun q =>
    stN_sub_ne_zero (u := ⟨u q, huS q⟩) (v := ⟨v q, hvS q⟩)
      (fun h => huN q (congrArg Subtype.val h)) (fun h => hvN q (congrArg Subtype.val h))
      (fun h => huv q (congrArg Subtype.val h))
  have hdeg := deg_eq_of_homotopy hfin finrank_euclideanSpace_fin
    ((oA.prod finrank_euclideanSpace_fin finrank_euclideanSpace_fin oB).cast hk) (sphOrStd k)
    (contMDiff_nv0_comp (hstu.sub hstv) hne)
  have e0 : (fun p : A × B => nv0 (stN (u (p, 0)) - stN (v (p, 0)))) =
      linkMap (fun x => stN ((S 0) (α x).1)) (fun y => stN ((S 0) (β y).1)) := by
    funext p
    rw [hueq, hveq]
    simp only [Real.smoothTransition.zero]
    rfl
  have e1 : (fun p : A × B => nv0 (stN (u (p, 1)) - stN (v (p, 1)))) =
      linkMap (fun x => stN ((S 1) (α x).1)) (fun y => stN ((S 1) (β y).1)) := by
    funext p
    rw [hueq, hveq]
    simp only [Real.smoothTransition.one]
    rfl
  unfold linkingNumberRot linkingNumber
  rw [← e0, ← e1]
  exact hdeg

/-! ### Rotations -/

section rotations

variable {k : ℕ}

/-- The planar rotation `rotCLM u v θ` (for an orthonormal pair `u, v`) as a linear isometry
equivalence. -/
def rotLIE {u v : 𝔼 (k + 2)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0) (θ : ℝ) :
    𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2) :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (rotCLM u v θ : 𝔼 (k + 2) →ₗ[ℝ] 𝔼 (k + 2))
      norm_map' := norm_rotCLM hu hv huv θ }
    (rotCLM_bijective hu hv huv θ).2

theorem rotLIE_apply {u v : 𝔼 (k + 2)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0)
    (θ : ℝ) (x : 𝔼 (k + 2)) : rotLIE hu hv huv θ x = rotCLM u v θ x := rfl

theorem isRotation_rotLIE {u v : 𝔼 (k + 2)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0)
    (θ : ℝ) : IsRotation (rotLIE hu hv huv θ) := by
  unfold IsRotation
  have h : ((rotLIE hu hv huv θ).toLinearEquiv : 𝔼 (k + 2) →ₗ[ℝ] 𝔼 (k + 2)) =
      (rotCLM u v θ : 𝔼 (k + 2) →ₗ[ℝ] 𝔼 (k + 2)) := LinearMap.ext fun x => rfl
  rw [h]
  exact det_rotCLM_pos hu hv huv θ

theorem isRotation_trans {R Q : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2)} (hR : IsRotation R)
    (hQ : IsRotation Q) : IsRotation (R.trans Q) := by
  unfold IsRotation at *
  have h : ((R.trans Q).toLinearEquiv : 𝔼 (k + 2) →ₗ[ℝ] 𝔼 (k + 2)) =
      (Q.toLinearEquiv : 𝔼 (k + 2) →ₗ[ℝ] 𝔼 (k + 2)).comp
        (R.toLinearEquiv : 𝔼 (k + 2) →ₗ[ℝ] 𝔼 (k + 2)) := LinearMap.ext fun x => rfl
  rw [h, LinearMap.det_comp]
  exact mul_pos hQ hR

theorem isRotation_symm {R : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2)} (hR : IsRotation R) :
    IsRotation R.symm := by
  unfold IsRotation at *
  have h : (R.symm.toLinearEquiv : 𝔼 (k + 2) →ₗ[ℝ] 𝔼 (k + 2)) =
      (R.toLinearEquiv.symm : 𝔼 (k + 2) →ₗ[ℝ] 𝔼 (k + 2)) := LinearMap.ext fun x => rfl
  rw [h, LinearEquiv.det_coe_symm]
  exact inv_pos.2 hR

end rotations

/-! ### Step 4: two great-circle arcs avoiding the images -/

section arcs

variable {k : ℕ}

/-- A great-circle arc from `q` to `w ≠ -q`: `w = cos θ q + sin θ v` with `v ⊥ q` a unit vector
and `0 ≤ θ < π`. -/
private theorem exists_arc {n : ℕ} (hn : 1 ≤ n) {q w : 𝔼 (n + 1)} (hq : ‖q‖ = 1) (hw : ‖w‖ = 1)
    (hwq : w ≠ -q) : ∃ v : 𝔼 (n + 1), ∃ θ : ℝ, ‖v‖ = 1 ∧ ⟪q, v⟫ = 0 ∧ 0 ≤ θ ∧ θ < π ∧
      Real.cos θ • q + Real.sin θ • v = w := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ⟪q, w⟫ := ⟨_, rfl⟩
  have hc1 : |c| ≤ 1 := by
    have := abs_real_inner_le_norm q w
    rwa [hq, hw, one_mul, ← hc] at this
  obtain ⟨hlo, hhi⟩ := abs_le.1 hc1
  have hcne : c ≠ -1 := by
    intro h
    apply hwq
    have h1 : ⟪-q, w⟫ = 1 := by rw [inner_neg_left, ← hc, h, neg_neg]
    exact ((inner_eq_one_iff_of_norm_eq_one (by rwa [norm_neg]) hw).1 h1).symm
  obtain ⟨d, hd⟩ : ∃ d : 𝔼 (n + 1), d = w - c • q := ⟨_, rfl⟩
  have hqd : ⟪q, d⟫ = 0 := by
    rw [hd, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hq, ← hc]; ring
  have hdsq : ‖d‖ ^ 2 = 1 - c ^ 2 := by
    rw [hd, norm_sub_sq_real, real_inner_smul_right, real_inner_comm, ← hc, norm_smul, hq, hw,
      Real.norm_eq_abs, mul_one, sq_abs]
    ring
  obtain ⟨v, hv, hqv, hdv⟩ : ∃ v : 𝔼 (n + 1), ‖v‖ = 1 ∧ ⟪q, v⟫ = 0 ∧ ‖d‖ • v = d := by
    by_cases hd0 : d = 0
    · obtain ⟨v, hv, hqv⟩ := exists_unit_orthogonal hn hq
      exact ⟨v, hv, hqv, by rw [hd0, norm_zero, zero_smul]⟩
    · have hdn : ‖d‖ ≠ 0 := norm_ne_zero_iff.2 hd0
      refine ⟨‖d‖⁻¹ • d, ?_, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hdn]
      · rw [real_inner_smul_right, hqd, mul_zero]
      · rw [smul_smul, mul_inv_cancel₀ hdn, one_smul]
  refine ⟨v, Real.arccos c, hv, hqv, Real.arccos_nonneg c,
    Real.arccos_lt_pi.2 (lt_of_le_of_ne hlo (Ne.symm hcne)), ?_⟩
  rw [Real.cos_arccos hlo hhi, Real.sin_arccos, ← hdsq, Real.sqrt_sq (norm_nonneg _), hdv, hd]
  abel

/-- If `c ≠ q` lies on the arc `s ↦ cos s q + sin s v` (`0 ≤ s ≤ θ < π`) from `q` to
`w = cos θ q + sin θ v`, then `w = (c − r q)/|c − r q|` for some `r`. -/
private theorem arc_avoid {n : ℕ} {q v c : 𝔼 (n + 1)} {w : Sph n} {θ : ℝ} (hθπ : θ < π)
    (hw : Real.cos θ • q + Real.sin θ • v = w.1) (hcq : c ≠ q)
    (hbad : ∀ r : ℝ, c - r • q ≠ 0 → nv0 (c - r • q) ≠ w) {s : ℝ} (hs0 : 0 ≤ s) (hsθ : s ≤ θ) :
    Real.cos s • q + Real.sin s • v ≠ c := by
  intro hc
  rcases hs0.eq_or_lt with hs | hs
  · subst hs
    rw [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero] at hc
    exact hcq hc.symm
  · have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi (hs.trans_le hsθ) hθπ
    have hsins : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs (hsθ.trans_lt hθπ)
    obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = Real.sin s / Real.sin θ := ⟨_, rfl⟩
    have hμpos : 0 < μ := by rw [hμ]; exact div_pos hsins hsinθ
    have hμs : μ * Real.sin θ = Real.sin s := by rw [hμ]; exact div_mul_cancel₀ _ hsinθ.ne'
    have key : c - (Real.cos s - μ * Real.cos θ) • q = μ • w.1 := by
      rw [← hw, ← hc, ← hμs]
      module
    have hne : c - (Real.cos s - μ * Real.cos θ) • q ≠ 0 := by
      rw [key]; exact smul_ne_zero hμpos.ne' (sph_ne_zero w)
    refine hbad _ hne ?_
    rw [key, nv0_smul_pos hμpos, nv0_val_sph]

/-- The "cone" of `γ` seen from `q`, i.e. the set of points `(γ x − r q)/|γ x − r q|`, is meagre
when `dim X + 1 < dim S^{k+1}`. -/
private theorem isMeagre_cone {d : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (𝔼 d) X]
    [IsManifold 𝓘(ℝ, 𝔼 d) ∞ X] [SecondCountableTopology X] (hd : d < k) {γ : X → Sph (k + 1)}
    (hγ : ContMDiff 𝓘(ℝ, 𝔼 d) 𝓘(ℝ, 𝔼 (k + 1)) ∞ γ) (q : 𝔼 (k + 2)) :
    IsMeagre ((fun p : X × ℝ => (nv0 ((γ p.1).1 - p.2 • q) : Sph (k + 1))) ''
      {p : X × ℝ | (γ p.1).1 - p.2 • q ≠ 0}) := by
  have hw : ContMDiff (𝓘(ℝ, 𝔼 d).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼 (k + 2)) ∞
      (fun p : X × ℝ => (γ p.1).1 - p.2 • q) :=
    (contMDiff_val.comp (hγ.comp contMDiff_fst)).sub (contMDiff_snd.smul contMDiff_const)
  have hU : IsOpen {p : X × ℝ | (γ p.1).1 - p.2 • q ≠ 0} :=
    isOpen_ne_fun hw.continuous continuous_const
  refine isMeagre_image_of_finrank_lt (I := 𝓘(ℝ, 𝔼 d).prod 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, 𝔼 (k + 1))) ?_ hU ?_
  · rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
      Module.finrank_self]
    omega
  · intro p hp
    exact (contMDiffAt_nv0_comp ⟨_, hU⟩ (fun p _ => hw.contMDiffAt) (fun p hp => hp)
      hp).contMDiffWithinAt

private theorem isMeagre_singleton_sph (hk0 : 0 < k) (p : Sph (k + 1)) :
    IsMeagre ({p} : Set (Sph (k + 1))) := by
  have h := isMeagre_image_of_finrank_lt (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, 𝔼 (k + 1)))
    (g := fun _ : ℝ => p) (U := univ)
    (by rw [Module.finrank_self, finrank_euclideanSpace_fin]; omega) isOpen_univ contMDiffOn_const
  rwa [univ_nonempty.image_const] at h

end arcs

/-- **Step 4.** For `q, q'` in `S^{k+1}` there is `w ≠ -q, -q'` outside the cones of `α` and `β`
seen from `q` and from `q'` (these cones are meagre since `a + 1, b + 1 ≤ k`, and the sphere is a
Baire space). -/
private theorem exists_good_point [SecondCountableTopology A] [SecondCountableTopology B]
    (hk : a + b = k) (ha : 1 ≤ a) (hb : 1 ≤ b) {α : A → Sph (k + 1)} {β : B → Sph (k + 1)}
    (hα : ContMDiff 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (k + 1)) ∞ α)
    (hβ : ContMDiff 𝓘(ℝ, 𝔼 b) 𝓘(ℝ, 𝔼 (k + 1)) ∞ β) (q q' : Sph (k + 1)) :
    ∃ w : Sph (k + 1), w ≠ antip q ∧ w ≠ antip q' ∧
      (∀ x (r : ℝ), (α x).1 - r • q.1 ≠ 0 → nv0 ((α x).1 - r • q.1) ≠ w) ∧
      (∀ y (r : ℝ), (β y).1 - r • q.1 ≠ 0 → nv0 ((β y).1 - r • q.1) ≠ w) ∧
      (∀ x (r : ℝ), (α x).1 - r • q'.1 ≠ 0 → nv0 ((α x).1 - r • q'.1) ≠ w) ∧
      (∀ y (r : ℝ), (β y).1 - r • q'.1 ≠ 0 → nv0 ((β y).1 - r • q'.1) ≠ w) := by
  have hk0 : 0 < k := by omega
  have hq := (isMeagre_singleton_sph hk0 (antip q)).union (isMeagre_singleton_sph hk0 (antip q'))
  have hα' := (isMeagre_cone (by omega : a < k) hα q.1).union
    (isMeagre_cone (by omega : b < k) hβ q.1)
  have hβ' := (isMeagre_cone (by omega : a < k) hα q'.1).union
    (isMeagre_cone (by omega : b < k) hβ q'.1)
  obtain ⟨w, -, hw⟩ :=
    exists_mem_open_not_mem_of_isMeagre isOpen_univ univ_nonempty ((hq.union hα').union hβ')
  simp only [mem_union, mem_singleton_iff, not_or] at hw
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩ := hw
  exact ⟨w, h1, h2, fun x r hxr hw => h3 ⟨(x, r), hxr, hw⟩, fun y r hyr hw => h4 ⟨(y, r), hyr, hw⟩,
    fun x r hxr hw => h5 ⟨(x, r), hxr, hw⟩, fun y r hyr hw => h6 ⟨(y, r), hyr, hw⟩⟩

/-- **One leg of step 5.** If `R` is admissible, `q = R⁻¹(north)`, and `w ≠ -q` is not in the
cones of `α, β` seen from `q`, then following the arc from `q` to `w` gives an admissible rotation
`S` with `S w = north` and the same linking number. -/
private theorem exists_leg [CompactSpace A] [T2Space A] [SecondCountableTopology A]
    [CompactSpace B] [T2Space B] [SecondCountableTopology B] (hk : a + b = k) (hk0 : 0 < k)
    {oA : Orient 𝓘(ℝ, 𝔼 a) A a} {oB : Orient 𝓘(ℝ, 𝔼 b) B b} {α : A → Sph (k + 1)}
    {β : B → Sph (k + 1)} (hα : ContMDiff 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (k + 1)) ∞ α)
    (hβ : ContMDiff 𝓘(ℝ, 𝔼 b) 𝓘(ℝ, 𝔼 (k + 1)) ∞ β) (hdisj : ∀ x y, α x ≠ β y)
    {R : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2)} (hR : IsRotation R)
    (hRα : ∀ x, R (α x).1 ≠ northPt.1) (hRβ : ∀ y, R (β y).1 ≠ northPt.1) {w : Sph (k + 1)}
    (hw : w.1 ≠ -R.symm northPt.1)
    (hwα : ∀ x (r : ℝ), (α x).1 - r • R.symm northPt.1 ≠ 0 →
      nv0 ((α x).1 - r • R.symm northPt.1) ≠ w)
    (hwβ : ∀ y (r : ℝ), (β y).1 - r • R.symm northPt.1 ≠ 0 →
      nv0 ((β y).1 - r • R.symm northPt.1) ≠ w) :
    ∃ S : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2), IsRotation S ∧ (∀ x, S (α x).1 ≠ northPt.1) ∧
      (∀ y, S (β y).1 ≠ northPt.1) ∧ S w.1 = northPt.1 ∧
      linkingNumberRot hk oA oB α β R = linkingNumberRot hk oA oB α β S := by
  obtain ⟨q, hq⟩ : ∃ q : 𝔼 (k + 2), q = R.symm northPt.1 := ⟨_, rfl⟩
  rw [← hq] at hw hwα hwβ
  have hq1 : ‖q‖ = 1 := by
    rw [hq, LinearIsometryEquiv.norm_map]; exact mem_iff_norm.1 northPt.2
  have hRq : R q = northPt.1 := by rw [hq]; exact R.apply_symm_apply _
  obtain ⟨v, θ, hv, hqv, hθ0, hθπ, hwθ⟩ :=
    exists_arc (by omega : 1 ≤ k + 1) hq1 (mem_iff_norm.1 w.2) hw
  -- the arc from `q` to `w` avoids both images
  have harc : ∀ t ∈ Icc (0 : ℝ) 1, ∀ c : Sph (k + 1),
      (∀ r : ℝ, c.1 - r • q ≠ 0 → nv0 (c.1 - r • q) ≠ w) → R c.1 ≠ northPt.1 →
      rotCLM q v (t * θ) q ≠ c.1 := by
    intro t ht c hc hRc
    rw [rotCLM_apply_u hq1 hv hqv]
    exact arc_avoid hθπ hwθ (fun h => hRc (by rw [h, hRq])) hc (mul_nonneg ht.1 hθ0)
      (mul_le_of_le_one_left hθ0 ht.2)
  -- the family `S t = R ∘ rot(-tθ)`
  obtain ⟨S, hS⟩ : ∃ S : ℝ → 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2),
      ∀ t, S t = (rotLIE hq1 hv hqv (-(t * θ))).trans R := ⟨_, fun _ => rfl⟩
  have hSapp : ∀ t x, S t x = R (rotCLM q v (-(t * θ)) x) := fun t x => by rw [hS]; rfl
  have hSN : ∀ t ∈ Icc (0 : ℝ) 1, ∀ c : Sph (k + 1),
      (∀ r : ℝ, c.1 - r • q ≠ 0 → nv0 (c.1 - r • q) ≠ w) → R c.1 ≠ northPt.1 →
      S t c.1 ≠ northPt.1 := by
    intro t ht c hc hRc h
    rw [hSapp, ← hRq] at h
    have h1 := R.injective h
    apply harc t ht c hc hRc
    calc rotCLM q v (t * θ) q = rotCLM q v (t * θ) (rotCLM q v (-(t * θ)) c.1) := by rw [h1]
      _ = c.1 := rotCLM_rotCLM_neg hq1 hv hqv _ _
  have hF : ContDiff ℝ ∞ (fun t : ℝ =>
      (R.toContinuousLinearEquiv : 𝔼 (k + 2) →L[ℝ] 𝔼 (k + 2)).comp (rotCLM q v (-(t * θ)))) :=
    contDiff_const.clm_comp ((contDiff_rotCLM_clm q v).comp (contDiff_id.mul contDiff_const).neg)
  have hfam := linkingNumberRot_eq_of_family hk hk0 (oA := oA) (oB := oB) hα hβ hdisj hF
    (S := S) (fun t x => hSapp t x) (fun t ht x => hSN t ht (α x) (hwα x) (hRα x))
    (fun t ht y => hSN t ht (β y) (hwβ y) (hRβ y))
  have hS0 : S 0 = R := LinearIsometryEquiv.ext fun x => by
    rw [hSapp, zero_mul, neg_zero, rotCLM_zero]; rfl
  refine ⟨S 1, ?_, fun x => hSN 1 ⟨zero_le_one, le_rfl⟩ (α x) (hwα x) (hRα x),
    fun y => hSN 1 ⟨zero_le_one, le_rfl⟩ (β y) (hwβ y) (hRβ y), ?_, ?_⟩
  · rw [hS]; exact isRotation_trans (isRotation_rotLIE hq1 hv hqv _) hR
  · rw [hSapp, one_mul, ← hwθ, ← rotCLM_apply_u hq1 hv hqv, rotCLM_neg_rotCLM hq1 hv hqv, hRq]
  · rw [← hfam, hS0]

/-- **Step 5: independence of the admissible rotation.** -/
theorem linkingNumberRot_eq_of_admissible [CompactSpace A] [T2Space A] [SecondCountableTopology A]
    [CompactSpace B] [T2Space B] [SecondCountableTopology B] (hk : a + b = k) (ha : 1 ≤ a)
    (hb : 1 ≤ b) {oA : Orient 𝓘(ℝ, 𝔼 a) A a} {oB : Orient 𝓘(ℝ, 𝔼 b) B b} {α : A → Sph (k + 1)}
    {β : B → Sph (k + 1)} (hα : ContMDiff 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (k + 1)) ∞ α)
    (hβ : ContMDiff 𝓘(ℝ, 𝔼 b) 𝓘(ℝ, 𝔼 (k + 1)) ∞ β) (hdisj : ∀ x y, α x ≠ β y)
    {R R' : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2)} (hR : IsRotation R) (hR' : IsRotation R')
    (hRα : ∀ x, R (α x).1 ≠ northPt.1) (hRβ : ∀ y, R (β y).1 ≠ northPt.1)
    (hR'α : ∀ x, R' (α x).1 ≠ northPt.1) (hR'β : ∀ y, R' (β y).1 ≠ northPt.1) :
    linkingNumberRot hk oA oB α β R = linkingNumberRot hk oA oB α β R' := by
  have hk0 : 0 < k := by omega
  obtain ⟨w, hw1, hw2, hw3, hw4, hw5, hw6⟩ := exists_good_point hk ha hb hα hβ
    ⟨R.symm northPt.1, rotation_mem_sph R.symm northPt⟩
    ⟨R'.symm northPt.1, rotation_mem_sph R'.symm northPt⟩
  obtain ⟨S, hS, -, -, hSw, hRS⟩ := exists_leg hk hk0 (oA := oA) (oB := oB) hα hβ hdisj hR hRα hRβ
    (w := w) (fun h => hw1 (Subtype.ext h)) hw3 hw4
  obtain ⟨S', hS', hS'α, hS'β, hS'w, hRS'⟩ := exists_leg hk hk0 (oA := oA) (oB := oB) hα hβ hdisj
    hR' hR'α hR'β (w := w) (fun h => hw2 (Subtype.ext h)) hw5 hw6
  -- `S = Q ∘ S'` with `Q = S ∘ S'⁻¹` fixing the north pole
  have hQN : (S'.symm.trans S) northPt.1 = northPt.1 := by
    change S (S'.symm northPt.1) = northPt.1
    rw [S'.symm_apply_eq.2 hS'w.symm, hSw]
  have hSS' : S'.trans (S'.symm.trans S) = S := LinearIsometryEquiv.ext fun x => by
    change S (S'.symm (S' x)) = S x
    rw [S'.symm_apply_apply]
  rw [hRS, hRS', ← hSS', linkingNumberRot_trans_of_fix hk hk0 hα hβ hdisj
    (isRotation_trans (isRotation_symm hS') hS) hQN hS'α hS'β]

private theorem linkingNumber_of_isEmpty (hk : a + b = k) [IsEmpty (A × B)]
    (oA : Orient 𝓘(ℝ, 𝔼 a) A a) (oB : Orient 𝓘(ℝ, 𝔼 b) B b) (α : A → 𝔼 (k + 1))
    (β : B → 𝔼 (k + 1)) : linkingNumber hk oA oB α β = 0 := by
  unfold linkingNumber deg
  split_ifs with h
  · unfold degAt
    exact finsum_of_isEmpty _
  · rfl

end LinkSph

variable {a b k : ℕ} {A : Type*} [TopologicalSpace A] [ChartedSpace (𝔼 a) A]
  [IsManifold 𝓘(ℝ, 𝔼 a) ∞ A] {B : Type*} [TopologicalSpace B] [ChartedSpace (𝔼 b) B]
  [IsManifold 𝓘(ℝ, 𝔼 b) ∞ B]

open Classical in
/-- **The linking number in the sphere** (defined with an admissible rotation, `0` if none
exists). -/
def linkingNumberSph (hk : a + b = k) (oA : Orient 𝓘(ℝ, 𝔼 a) A a) (oB : Orient 𝓘(ℝ, 𝔼 b) B b)
    (α : A → Sph (k + 1)) (β : B → Sph (k + 1)) : ℤ :=
  if h : ∃ R : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2), IsRotation R ∧
      ∀ x y, R (α x).1 ≠ northPt.1 ∧ R (β y).1 ≠ northPt.1 then
    linkingNumberRot hk oA oB α β h.choose
  else 0

/-- Admissible rotations exist: a point `q` outside the images (which are meagre, since
`a, b < k + 1`) is moved to the north pole by a planar rotation. -/
theorem exists_admissible_rotation [SecondCountableTopology A] [SecondCountableTopology B]
    (hk : a + b = k) (ha : 1 ≤ a) (hb : 1 ≤ b) {α : A → Sph (k + 1)} {β : B → Sph (k + 1)}
    (hα : ContMDiff 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (k + 1)) ∞ α)
    (hβ : ContMDiff 𝓘(ℝ, 𝔼 b) 𝓘(ℝ, 𝔼 (k + 1)) ∞ β) :
    ∃ R : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2), IsRotation R ∧
      ∀ x y, R (α x).1 ≠ northPt.1 ∧ R (β y).1 ≠ northPt.1 := by
  have hm := (isMeagre_image_of_finrank_lt (I := 𝓘(ℝ, 𝔼 a)) (J := 𝓘(ℝ, 𝔼 (k + 1)))
    (by rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]; omega) isOpen_univ
    hα.contMDiffOn).union
    (isMeagre_image_of_finrank_lt (I := 𝓘(ℝ, 𝔼 b)) (J := 𝓘(ℝ, 𝔼 (k + 1)))
    (by rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]; omega) isOpen_univ
    hβ.contMDiffOn)
  obtain ⟨q, -, hq⟩ := exists_mem_open_not_mem_of_isMeagre isOpen_univ univ_nonempty hm
  simp only [mem_union, not_or, mem_image, mem_univ, true_and, not_exists] at hq
  obtain ⟨hqα, hqβ⟩ := hq
  obtain ⟨u, v, θ₀, hu, hv, huv, -, -, hrot, -⟩ :=
    exists_rotation_path (by omega : 1 ≤ k + 1) q northPt
  refine ⟨LinkSph.rotLIE hu hv huv θ₀, LinkSph.isRotation_rotLIE hu hv huv θ₀,
    fun x y => ⟨?_, ?_⟩⟩
  · intro h
    apply hqα x
    apply Subtype.ext
    apply (LinkSph.rotLIE hu hv huv θ₀).injective
    rw [h, LinkSph.rotLIE_apply, hrot]
  · intro h
    apply hqβ y
    apply Subtype.ext
    apply (LinkSph.rotLIE hu hv huv θ₀).injective
    rw [h, LinkSph.rotLIE_apply, hrot]

/-- **Problem 13, sphere part**: independence of the rotation. -/
theorem linkingNumberSph_eq [CompactSpace A] [T2Space A] [SecondCountableTopology A]
    [CompactSpace B] [T2Space B] [SecondCountableTopology B]
    (hk : a + b = k) (ha : 1 ≤ a) (hb : 1 ≤ b) {oA : Orient 𝓘(ℝ, 𝔼 a) A a}
    {oB : Orient 𝓘(ℝ, 𝔼 b) B b} {α : A → Sph (k + 1)} {β : B → Sph (k + 1)}
    (hα : ContMDiff 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (k + 1)) ∞ α)
    (hβ : ContMDiff 𝓘(ℝ, 𝔼 b) 𝓘(ℝ, 𝔼 (k + 1)) ∞ β) (hdisj : ∀ x y, α x ≠ β y)
    {R : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2)} (hR : IsRotation R)
    (hRN : ∀ x y, R (α x).1 ≠ northPt.1 ∧ R (β y).1 ≠ northPt.1) :
    linkingNumberSph hk oA oB α β = linkingNumberRot hk oA oB α β R := by
  rcases isEmpty_or_nonempty (A × B) with hAB | ⟨⟨x₀, y₀⟩⟩
  · -- `A × B` is empty: both linking numbers vanish
    have h0 : ∀ R', linkingNumberRot hk oA oB α β R' = 0 := fun R' =>
      LinkSph.linkingNumber_of_isEmpty hk _ _ _ _
    unfold linkingNumberSph
    split_ifs with h
    · rw [h0, h0]
    · rw [h0]
  · have hex : ∃ R' : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2), IsRotation R' ∧
        ∀ x y, R' (α x).1 ≠ northPt.1 ∧ R' (β y).1 ≠ northPt.1 := ⟨R, hR, hRN⟩
    rw [linkingNumberSph, dif_pos hex]
    obtain ⟨hR₀, hR₀N⟩ := hex.choose_spec
    exact LinkSph.linkingNumberRot_eq_of_admissible hk ha hb hα hβ hdisj hR₀ hR
      (fun x => (hR₀N x y₀).1) (fun y => (hR₀N x₀ y).2) (fun x => (hRN x y₀).1)
      (fun y => (hRN x₀ y).2)

end Problems

end Milnor
