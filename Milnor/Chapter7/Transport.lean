import Milnor.Chapter7.Lemma1

/-!
# Transporting and gluing submanifolds of `M × ℝ`

Infrastructure for showing that framed cobordism is an equivalence relation (Milnor §7, p. 43):

* the preimage of a slice submanifold under a diffeomorphism is a slice submanifold;
* the affine time changes `(x, t) ↦ (x, a t + c)` of `M × ℝ` are diffeomorphisms, and the
  tangent spaces of `S ⊆ M × ℝ` are carried to those of the preimage by `(v, s) ↦ (v, a s)`;
* the tangent space of `S` at `q` only depends on `S` near `q`;
* two submanifolds agreeing on a strip `c' < t < c` glue to a submanifold.
-/

open Set Filter Topology Function Module Metric TopologicalSpace
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

section general

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The preimage of a slice submanifold under a diffeomorphism is a slice submanifold. -/
theorem isSliceSubmanifold_preimage_diffeomorph {S : Set M} (hS : IsSliceSubmanifold I Z W S)
    (τ : M ≃ₘ^∞⟮I, I⟯ M) : IsSliceSubmanifold I Z W (τ ⁻¹' S) := by
  intro p hp
  obtain ⟨σ, hpσ⟩ := hS (τ p) hp
  have hsrc : (τ.toPartialDiffeomorph.trans σ.φ).source = τ ⁻¹' σ.φ.source := by
    show (univ ∩ (τ ⁻¹' σ.φ.source)) = _
    exact univ_inter _
  have happ : ∀ q, (τ.toPartialDiffeomorph.trans σ.φ) q = σ.φ (τ q) := fun q => rfl
  refine ⟨{ φ := τ.toPartialDiffeomorph.trans σ.φ
            x₀ := p
            x₀_mem := hp
            x₀_source := by rw [hsrc]; exact hpσ
            slice := fun q hq => by
              rw [hsrc] at hq
              rw [happ]
              exact σ.slice (τ q) hq }, ?_⟩
  show p ∈ (τ.toPartialDiffeomorph.trans σ.φ).source
  rw [hsrc]; exact hpσ

/-- The affine time change `(x, t) ↦ (x, a t + c)` as a plain function. -/
def affFun {X : Type*} (a c : ℝ) (q : X × ℝ) : X × ℝ := (q.1, a * q.2 + c)

/-- Its inverse `(x, t) ↦ (x, (t - c) / a)`. -/
def affInv {X : Type*} (a c : ℝ) (q : X × ℝ) : X × ℝ := (q.1, (q.2 - c) / a)

theorem affInv_affFun {X : Type*} {a : ℝ} (c : ℝ) (ha : a ≠ 0) (q : X × ℝ) :
    affInv a c (affFun a c q) = q := by
  unfold affFun affInv
  ext
  · rfl
  · show (a * q.2 + c - c) / a = q.2
    rw [add_sub_cancel_right, mul_comm, mul_div_assoc, div_self ha, mul_one]

theorem affFun_affInv {X : Type*} {a : ℝ} (c : ℝ) (ha : a ≠ 0) (q : X × ℝ) :
    affFun a c (affInv a c q) = q := by
  unfold affFun affInv
  ext
  · rfl
  · show a * ((q.2 - c) / a) + c = q.2
    rw [mul_comm, div_mul_cancel₀ _ ha, sub_add_cancel]

theorem contMDiff_affFun (a c : ℝ) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ (affFun (X := M) a c) := by
  have h : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => a * t + c) :=
    contMDiff_iff_contDiff.2 ((contDiff_const.mul contDiff_id).add contDiff_const)
  exact (contMDiff_fst (I := I) (J := 𝓘(ℝ, ℝ)) (M := M) (N := ℝ)).prodMk
    (h.comp (contMDiff_snd (I := I) (J := 𝓘(ℝ, ℝ)) (M := M) (N := ℝ)))

theorem contMDiff_affInv (a c : ℝ) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ (affInv (X := M) a c) := by
  have h : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => (t - c) / a) :=
    contMDiff_iff_contDiff.2 ((contDiff_id.sub contDiff_const).div_const a)
  exact (contMDiff_fst (I := I) (J := 𝓘(ℝ, ℝ)) (M := M) (N := ℝ)).prodMk
    (h.comp (contMDiff_snd (I := I) (J := 𝓘(ℝ, ℝ)) (M := M) (N := ℝ)))

/-- The affine time change `(x, t) ↦ (x, a t + c)` of `M × ℝ`, `a ≠ 0`, as a diffeomorphism. -/
def affineXR (a c : ℝ) (ha : a ≠ 0) :
    (M × ℝ) ≃ₘ^∞⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ) where
  toFun := affFun a c
  invFun := affInv a c
  left_inv q := affInv_affFun c ha q
  right_inv q := affFun_affInv c ha q
  contMDiff_toFun := contMDiff_affFun a c
  contMDiff_invFun := contMDiff_affInv a c

end general

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) {n p : ℕ}

/-- The derivative `(v, s) ↦ (v, a s)` of the ambient affine time change. -/
def dtXR (a : ℝ) : EuclideanSpace ℝ (Fin (K + 1)) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin (K + 1)) × ℝ :=
  (ContinuousLinearMap.fst ℝ _ _).prod (a • ContinuousLinearMap.snd ℝ _ _)

@[simp] theorem dtXR_apply (a : ℝ) (v : EuclideanSpace ℝ (Fin (K + 1)) × ℝ) :
    dtXR a v = (v.1, a * v.2) := rfl

theorem hasFDerivAt_affine_amb (a c : ℝ) (v : EuclideanSpace ℝ (Fin (K + 1)) × ℝ) :
    HasFDerivAt (affFun (X := EuclideanSpace ℝ (Fin (K + 1))) a c) (dtXR a) v :=
  hasFDerivAt_fst.prodMk ((hasFDerivAt_snd.const_mul a).add_const c)

section transport

variable {S : Set (M × ℝ)}
  (hS : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)) S)
  (a c : ℝ) (ha : a ≠ 0)

include hS ha in
/-- The preimage `τ⁻¹(S)` of `S` under the affine time change is a submanifold. -/
theorem isSliceSubmanifold_preimage_affine :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)) (affFun a c ⁻¹' S) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  exact isSliceSubmanifold_preimage_diffeomorph hS
    (affineXR (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) a c ha)

/-- The map `τ⁻¹(S) → S`. -/
def ιaff (q : affFun a c ⁻¹' S) : S := ⟨affFun a c q.1, q.2⟩

/-- The map `S → τ⁻¹(S)`. -/
def ιaff' (q : S) : affFun a c ⁻¹' S :=
  ⟨affInv a c q.1, by show affFun a c (affInv a c q.1) ∈ S; rw [affFun_affInv c ha]; exact q.2⟩

theorem ιaff'_ιaff (q) : ιaff' (S := S) a c ha (ιaff (S := S) a c q) = q := by
  apply Subtype.ext
  show affInv a c (affFun a c q.1) = q.1
  rw [affInv_affFun c ha]

include hS in
theorem contMDiff_ιaff :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    letI := (isSliceSubmanifold_preimage_affine hM hS a c ha).chartedSpace;
    letI := hS.chartedSpace;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      (ιaff (S := S) a c) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hS' := isSliceSubmanifold_preimage_affine hM hS a c ha
  letI := hS'.chartedSpace
  haveI := hS'.isManifold
  letI := hS.chartedSpace
  exact hS.contMDiff_codRestrict
    (F := fun q : affFun a c ⁻¹' S => affFun a c q.1)
    ((contMDiff_affFun (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) a c).comp hS'.contMDiff_val)
    (fun q => q.2)

include hS in
theorem contMDiff_ιaff' :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    letI := (isSliceSubmanifold_preimage_affine hM hS a c ha).chartedSpace;
    letI := hS.chartedSpace;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      (ιaff' (S := S) a c ha) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hS' := isSliceSubmanifold_preimage_affine hM hS a c ha
  letI := hS'.chartedSpace
  haveI := hS'.isManifold
  letI := hS.chartedSpace
  haveI := hS.isManifold
  exact hS'.contMDiff_codRestrict
    (F := fun q : S => affInv a c q.1)
    ((contMDiff_affInv (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) a c).comp hS.contMDiff_val)
    (fun q => (ιaff' (S := S) a c ha q).2)

include hS in
/-- `dι` is surjective (it has a left inverse). -/
theorem surjective_mfd_ιaff (q) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    letI := (isSliceSubmanifold_preimage_affine hM hS a c ha).chartedSpace;
    letI := hS.chartedSpace;
    Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (ιaff (S := S) a c) q) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hS' := isSliceSubmanifold_preimage_affine hM hS a c ha
  letI := hS'.chartedSpace
  haveI := hS'.isManifold
  letI := hS.chartedSpace
  haveI := hS.isManifold
  have h1 := (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
    ((contMDiff_ιaff' hM hS a c ha).mdifferentiableAt (x := ιaff (S := S) a c q) (by simp))).comp q
    (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
      ((contMDiff_ιaff hM hS a c ha).mdifferentiableAt (x := q) (by simp)))
  have hcomp : (ιaff' (S := S) a c ha ∘ ιaff (S := S) a c) = id := funext (ιaff'_ιaff (S := S) a c ha)
  rw [hcomp] at h1
  have h2 := hasMFDerivAt_unique h1 (hasMFDerivAt_id (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) q)
  have hinj : Injective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (ιaff (S := S) a c) q) := by
    have h3 : (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (ιaff' (S := S) a c ha) (ιaff (S := S) a c q)).comp
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
          (ιaff (S := S) a c) q) = ContinuousLinearMap.id ℝ _ := h2
    intro x y hxy
    have := congrArg (fun L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) =>
      L x - L y) h3
    simp only [ContinuousLinearMap.comp_apply, hxy, sub_self, ContinuousLinearMap.id_apply] at this
    exact (sub_eq_zero.1 this.symm)
  exact LinearMap.injective_iff_surjective (f := (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (ιaff (S := S) a c) q).toLinearMap) |>.1 hinj

include hS in
/-- **Transport of tangent spaces**: `T_{τ q} S = dτ (T_q τ⁻¹(S))`. -/
theorem tangentS_affine (q) :
    tangentS hM hS (ιaff (S := S) a c q) =
      (tangentS hM (isSliceSubmanifold_preimage_affine hM hS a c ha) q).map
        (dtXR (K := K) a : EuclideanSpace ℝ (Fin (K + 1)) × ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin (K + 1)) × ℝ) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hS' := isSliceSubmanifold_preimage_affine hM hS a c ha
  letI := hS'.chartedSpace
  haveI := hS'.isManifold
  letI := hS.chartedSpace
  haveI := hS.isManifold
  set ι := ιaff (S := S) a c with hι
  -- the chain rule for `embXR ∘ ι = τ_amb ∘ embXR`
  have hA : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
      (fun r : S => embXR r.1) (ι q) (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (fun r : S => embXR r.1) (ι q)) :=
    hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ))
      (((contMDiff_embXR hM).comp hS.contMDiff_val).mdifferentiableAt (x := ι q) (by simp))
  have hB := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
    ((contMDiff_ιaff hM hS a c ha).mdifferentiableAt (x := q) (by simp))
  have hC : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
      (fun r : affFun a c ⁻¹' S => embXR r.1) q (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (fun r : affFun a c ⁻¹' S => embXR r.1) q) :=
    hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ))
      (((contMDiff_embXR hM).comp hS'.contMDiff_val).mdifferentiableAt (x := q) (by simp))
  have hD := (hasFDerivAt_affine_amb (K := K) a c (embXR q.1)).hasMFDerivAt
  have h1 := hA.comp q hB
  have h2 := hD.comp q hC
  have heq : ((fun r : S => embXR r.1) ∘ ι) =
      (affFun (X := EuclideanSpace ℝ (Fin (K + 1))) a c ∘ fun r : affFun a c ⁻¹' S => embXR r.1) := by
    funext r; rfl
  rw [heq] at h1
  have h3 := hasMFDerivAt_unique h1 h2
  -- ranges
  have hsurj := surjective_mfd_ιaff hM hS a c ha q
  have h3' : (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
      (fun r : S => embXR r.1) (ι q)).comp (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ι q) =
      (dtXR (K := K) a).comp (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (fun r : affFun a c ⁻¹' S => embXR r.1) q) := h3
  unfold tangentS
  rw [← LinearMap.range_comp, ← ContinuousLinearMap.toLinearMap_comp, ← h3',
    ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.2 hsurj

end transport

section local_

variable {S T : Set (M × ℝ)}
  (hS : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)) S)
  (hT : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)) T)

include hS hT in
/-- If `S` and `T` agree on an open set `U`, their tangent spaces agree at points of `U`
(one inclusion). -/
theorem tangentS_le_of_inter_eq {U : Set (M × ℝ)} (hU : IsOpen U) (hST : S ∩ U = T ∩ U)
    (q : S) (hq : q.1 ∈ U) (hqT : q.1 ∈ T) :
    tangentS hM hS q ≤ tangentS hM hT ⟨q.1, hqT⟩ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := hS.chartedSpace
  haveI := hS.isManifold
  letI := hT.chartedSpace
  haveI := hT.isManifold
  set US : Opens S := ⟨{r | r.1 ∈ U}, hU.preimage continuous_subtype_val⟩ with hUS
  have hmem : ∀ r : US, r.1.1 ∈ T := fun r => by
    have : r.1.1 ∈ S ∩ U := ⟨r.1.2, r.2⟩
    rw [hST] at this; exact this.1
  set κ : US → T := fun r => ⟨r.1.1, hmem r⟩ with hκ
  have hκs : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ κ :=
    hT.contMDiff_codRestrict (F := fun r : US => r.1.1)
      (hS.contMDiff_val.comp (contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))))
      hmem
  set r : US := ⟨q, hq⟩ with hr
  have hA : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
      (fun s : T => embXR s.1) (κ r) (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (fun s : T => embXR s.1) (κ r)) :=
    hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ))
      (((contMDiff_embXR hM).comp hT.contMDiff_val).mdifferentiableAt (x := κ r) (by simp))
  have hB := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) (hκs.mdifferentiableAt (x := r) (by simp))
  have h1 := hA.comp r hB
  have heq : ((fun s : T => embXR s.1) ∘ κ) = (fun s : S => embXR s.1) ∘ (Subtype.val : US → S) := by
    funext s; rfl
  rw [heq] at h1
  have h2 := HasMFDerivAt.mfd_eq h1
  have hmd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (fun s : S => embXR s.1) q :=
    ((contMDiff_embXR hM).comp hS.contMDiff_val).mdifferentiableAt (by simp)
  rw [mfd_comp_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) US hmd] at h2
  have h2' : (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
      (fun s : S => embXR s.1) q) = (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (fun s : T => embXR s.1) (κ r)).comp
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) κ r) := h2
  unfold tangentS
  show LinearMap.range _ ≤ LinearMap.range _
  have hκr : κ r = ⟨q.1, hqT⟩ := rfl
  rw [← hκr, h2', ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]
  exact LinearMap.map_le_range

include hS hT in
theorem tangentS_eq_of_inter_eq {U : Set (M × ℝ)} (hU : IsOpen U) (hST : S ∩ U = T ∩ U)
    (q : S) (hq : q.1 ∈ U) (hqT : q.1 ∈ T) :
    tangentS hM hS q = tangentS hM hT ⟨q.1, hqT⟩ :=
  le_antisymm (tangentS_le_of_inter_eq hM hS hT hU hST q hq hqT)
    (tangentS_le_of_inter_eq hM hT hS hU hST.symm ⟨q.1, hqT⟩ hq q.2)

end local_

section glue

variable {S₁ S₂ : Set (M × ℝ)}
  (hS₁ : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)) S₁)
  (hS₂ : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)) S₂)
  {c' c : ℝ}

/-- The glued set `S₁ ∩ {t < c} ∪ S₂ ∩ {c' < t}`. -/
def glueS (S₁ S₂ : Set (M × ℝ)) (c' c : ℝ) : Set (M × ℝ) :=
  {q ∈ S₁ | q.2 < c} ∪ {q ∈ S₂ | c' < q.2}

variable (hov : ∀ q : M × ℝ, c' < q.2 → q.2 < c → (q ∈ S₁ ↔ q ∈ S₂))

include hov in
theorem glueS_inter_left : glueS S₁ S₂ c' c ∩ {q | q.2 < c} = S₁ ∩ {q | q.2 < c} := by
  ext q
  simp only [glueS, mem_inter_iff, mem_union, mem_ofPred_eq]
  constructor
  · rintro ⟨h | h, hc⟩
    · exact ⟨h.1, hc⟩
    · exact ⟨(hov q h.2 hc).2 h.1, hc⟩
  · rintro ⟨h1, hc⟩
    exact ⟨Or.inl ⟨h1, hc⟩, hc⟩

include hov in
theorem glueS_inter_right : glueS S₁ S₂ c' c ∩ {q | c' < q.2} = S₂ ∩ {q | c' < q.2} := by
  ext q
  simp only [glueS, mem_inter_iff, mem_union, mem_ofPred_eq]
  constructor
  · rintro ⟨h | h, hc⟩
    · exact ⟨(hov q hc h.2).1 h.1, hc⟩
    · exact ⟨h.1, hc⟩
  · rintro ⟨h1, hc⟩
    exact ⟨Or.inr ⟨h1, hc⟩, hc⟩

include hS₁ hS₂ hov in
/-- **Gluing.** -/
theorem isSliceSubmanifold_glueS :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)) (glueS S₁ S₂ c' c) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  intro q hq
  have hl := glueS_inter_left (S₁ := S₁) (S₂ := S₂) hov
  have hr := glueS_inter_right (S₁ := S₁) (S₂ := S₂) hov
  by_cases hqc : q.2 < c
  · have hq1 : q ∈ S₁ := by
      have : q ∈ glueS S₁ S₂ c' c ∩ {q | q.2 < c} := ⟨hq, hqc⟩
      rw [hl] at this; exact this.1
    obtain ⟨σ, hqσ⟩ := hS₁ q hq1
    have hopen : IsOpen {r : M × ℝ | r.2 < c} := isOpen_lt continuous_snd continuous_const
    refine ⟨{ φ := σ.φ.restrOpen {r | r.2 < c} hopen
              x₀ := q
              x₀_mem := hq
              x₀_source := ⟨hqσ, hqc⟩
              slice := fun r hr => by
                rw [PartialDiffeomorph.restrOpen_apply]
                have hrc : r.2 < c := hr.2
                rw [← σ.slice r hr.1]
                constructor
                · intro h
                  have : r ∈ glueS S₁ S₂ c' c ∩ {q | q.2 < c} := ⟨h, hrc⟩
                  rw [hl] at this; exact this.1
                · intro h
                  have : r ∈ S₁ ∩ {q | q.2 < c} := ⟨h, hrc⟩
                  rw [← hl] at this; exact this.1 }, ⟨hqσ, hqc⟩⟩
  · have hqc' : c' < q.2 := by
      rcases hq with h | h
      · exact absurd h.2 hqc
      · exact h.2
    have hq2 : q ∈ S₂ := by
      have : q ∈ glueS S₁ S₂ c' c ∩ {q | c' < q.2} := ⟨hq, hqc'⟩
      rw [hr] at this; exact this.1
    obtain ⟨σ, hqσ⟩ := hS₂ q hq2
    have hopen : IsOpen {r : M × ℝ | c' < r.2} := isOpen_lt continuous_const continuous_snd
    refine ⟨{ φ := σ.φ.restrOpen {r | c' < r.2} hopen
              x₀ := q
              x₀_mem := hq
              x₀_source := ⟨hqσ, hqc'⟩
              slice := fun r hrs => by
                rw [PartialDiffeomorph.restrOpen_apply]
                have hrc : c' < r.2 := hrs.2
                rw [← σ.slice r hrs.1]
                constructor
                · intro h
                  have : r ∈ glueS S₁ S₂ c' c ∩ {q | c' < q.2} := ⟨h, hrc⟩
                  rw [hr] at this; exact this.1
                · intro h
                  have : r ∈ S₂ ∩ {q | c' < q.2} := ⟨h, hrc⟩
                  rw [← hr] at this; exact this.1 }, ⟨hqσ, hqc'⟩⟩

end glue

end Framed

end Milnor
