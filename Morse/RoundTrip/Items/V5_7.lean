import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V5_7

open Module
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V5_7

/-- The project's statement (universes instantiated at 0): in a holomorphic chart `w : V → F`,
the Hessians at `q` of `‖w(·) − (w q ± t n)‖²` have the same nullity. -/
def A : Prop := type_of% @Morse.nullity_hessian_normSq_sub_add_eq_sub.{0,0}

theorem A_holds : A := @Morse.nullity_hessian_normSq_sub_add_eq_sub

section Geometric

variable {K d m : ℕ} {M : Set (Rn (K + 1))}
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)

/-- **Assertion 2 in Milnor's form, from project lemmas outside the item**: on a submanifold
with `J`-invariant tangent spaces, `g − ℓ_w` and `g + ℓ_w` have the same nullity for `w` normal.
The complex structure `J' = Jc` read in the parametrization `xParam` preserves `g` and reverses
`ℓ_w` (`Morse.inner_fderiv_fderiv_sliceParam_Jc`, the project's derivation of the
anti-invariance of the second fundamental form from `J`-invariance of nearby tangent spaces). -/
theorem nullity_firstFF_sub_secondFF_neg {J : Rn (K + 1) →L[ℝ] Rn (K + 1)}
    (hJ : Morse.IsOrthComplexStructure J) (hc : Morse.IsComplexSubmanifold hM J) (q : M)
    {w : Rn (K + 1)} (hw : w ∈ (Morse.tangentSubspace hM q)ᗮ) :
    Morse.nullity (Morse.firstFF hM q - Morse.secondFF hM q w) =
      Morse.nullity (Morse.firstFF hM q - Morse.secondFF hM q (-w)) := by
  set σ := Milnor.Tub.σ hM q
  have hu : Morse.uParam hM q ∈ σ.toChart.target :=
    Morse.toChart_apply_mem_target σ (Milnor.Tub.mem_source hM q)
  set J' := Morse.Jc σ J (Morse.uParam hM q) with hJ'
  have hD : ∀ ξ, Morse.dParam hM q (J' ξ) = J (Morse.dParam hM q ξ) :=
    Morse.fderiv_sliceParam_Jc σ hc hu
  have hJJ : ∀ ξ, J' (J' ξ) = -ξ := fun ξ =>
    Morse.injective_dParam hM q (by rw [hD, hD, hJ.sq, map_neg])
  let L : Rn (d + 1) ≃L[ℝ] Rn (d + 1) :=
    ContinuousLinearEquiv.equivOfInverse J' (-J') (fun ξ => by simp [hJJ])
      (fun ξ => by simp [hJJ])
  have hrange : Morse.tangentSubspace hM q =
      LinearMap.range (Morse.dParam hM q : Rn (d + 1) →ₗ[ℝ] Rn (K + 1)) :=
    Milnor.Tub.range_mfd_val hM q q (Milnor.Tub.mem_source hM q)
  have hν : ∀ t ∈ LinearMap.range (fderiv ℝ (Morse.sliceParam σ) (Morse.uParam hM q) :
      Rn (d + 1) →ₗ[ℝ] Rn (K + 1)), ⟪w, t⟫ = 0 := by
    intro t ht
    have : t ∈ Morse.tangentSubspace hM q := by rw [hrange]; exact ht
    exact (Submodule.mem_orthogonal' _ _).1 hw t this
  have hνJ : ∀ t ∈ LinearMap.range (fderiv ℝ (Morse.sliceParam σ) (Morse.uParam hM q) :
      Rn (d + 1) →ₗ[ℝ] Rn (K + 1)), ⟪J w, t⟫ = 0 := by
    intro t ht
    have : t ∈ Morse.tangentSubspace hM q := by rw [hrange]; exact ht
    exact hc.inner_J_eq_zero hJ (fun s hs => (Submodule.mem_orthogonal' _ _).1 hw s hs) this
  have hlem := Morse.inner_fderiv_fderiv_sliceParam_Jc σ hc hu hν
  have hlemJ := Morse.inner_fderiv_fderiv_sliceParam_Jc σ hc hu hνJ
  have hsym := Morse.d2Param_symm hM q
  have hsec : ∀ ξ η, Morse.secondFF hM q w (J' ξ) (J' η) = -Morse.secondFF hM q w ξ η := by
    intro ξ η
    simp only [Morse.secondFF_apply]
    have e1 : ⟪w, Morse.d2Param hM q (J' ξ) (J' η)⟫ = ⟪w, J (Morse.d2Param hM q (J' ξ) η)⟫ :=
      hlem (J' ξ) η
    have e2 := hJ.inner_left w (Morse.d2Param hM q (J' ξ) η)
    have e3 : ⟪J w, Morse.d2Param hM q η (J' ξ)⟫ = ⟪J w, J (Morse.d2Param hM q η ξ)⟫ :=
      hlemJ η ξ
    have e4 := hJ.inner w (Morse.d2Param hM q η ξ)
    rw [hsym (J' ξ) η] at e1 e2
    rw [hsym η ξ] at e3 e4
    linarith
  have hfirst : ∀ ξ η, Morse.firstFF hM q (J' ξ) (J' η) = Morse.firstFF hM q ξ η := by
    intro ξ η
    simp only [Morse.firstFF_apply, hD, hJ.inner]
  rw [← Morse.nullity_bilinearComp _ L]
  congr 1
  ext ξ η
  simp only [ContinuousLinearMap.bilinearComp_apply, sub_apply]
  change Morse.firstFF hM q (J' ξ) (J' η) - Morse.secondFF hM q w (J' ξ) (J' η) = _
  rw [hfirst, hsec]
  have : Morse.secondFF hM q (-w) = -Morse.secondFF hM q w := by
    ext a b; simp [Morse.secondFF_apply, inner_neg_left]
  rw [this]
  simp

/-- B's nullity of `dE` at `(q, x)` in the normal bundle (any slice structure `hNN` on `N`) is the
nullity of `g − ℓ_x` (`Glue.endpointNullity_eq_of_slice` and the project's
`endpointNullity_eq_nullity`, Assertion 6.4). -/
theorem nullE_eq_nullity
    (hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) (Rn (K + 1)) (Rn (K + 1))
      (NSet hM)) (q : M) {x : Rn (K + 1)} (hx : ((q : Rn (K + 1)), x) ∈ NSet hM) :
    nullE hNN (q.1, x) = Morse.nullity (Morse.firstFF hM q - Morse.secondFF hM q x) := by
  have hkw : d + 1 + m = K + 1 := Morse.slice_dim_add_eq_of_nonempty hM ⟨q.1, q.2⟩
  let L : Rn (K + 1) ≃L[ℝ] (Rn m × Rn (d + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [finrank_prod]; omega)
  unfold nullE
  rw [dif_pos hx]
  have hx' : ((q : Rn (K + 1)), x) ∈ Milnor.Problems.normalBundleSet hM := hx
  refine (Glue.endpointNullity_eq_of_slice hM hkw hNN L ⟨_, hx'⟩).symm.trans ?_
  rw [Morse.endpointNullity_eq_nullity]
  rfl

end Geometric

/-- **B holds**, from project theorems outside the item: focal multiplicities are nullities of
`g − ℓ_{tv}` (Assertion 6.4 + structure independence), and `g ∓ ℓ_{tv}` are conjugate under the
complex structure (`nullity_firstFF_sub_secondFF_neg`).  A (the holomorphic-chart statement) is
not used: the project has no bridge from `J`-invariant tangent spaces to holomorphic charts. -/
theorem A_to_B : A → B := by
  intro _ K d m M hM hNN J hJ hc q v hqv t μ
  have hJ' : Morse.IsOrthComplexStructure
      (J.toContinuousLinearEquiv : Rn (K + 1) →L[ℝ] Rn (K + 1)) :=
    ⟨fun v => hJ v, fun v w => J.inner_map_map v w⟩
  have hc' : Morse.IsComplexSubmanifold hM
      (J.toContinuousLinearEquiv : Rn (K + 1) →L[ℝ] Rn (K + 1)) := fun q v hv => hc q v hv
  obtain ⟨hq, hperp⟩ := hqv
  have hw : t • v ∈ (Morse.tangentSubspace hM q)ᗮ :=
    Submodule.smul_mem _ t ((Submodule.mem_orthogonal' _ _).2 hperp)
  have hmem : ∀ x ∈ (Morse.tangentSubspace hM q)ᗮ, ((q : Rn (K + 1)), x) ∈ NSet hM :=
    fun x hx => ⟨q.2, (Submodule.mem_orthogonal' _ _).1 hx⟩
  unfold IsFocalOfMult
  rw [add_sub_cancel_left, sub_sub_cancel_left,
    nullE_eq_nullity hM hNN q (hmem _ hw), nullE_eq_nullity hM hNN q (hmem _ (Submodule.neg_mem _ hw)),
    nullity_firstFF_sub_secondFF_neg hM hJ' hc' q hw]

/-- B ⇒ A holds only because A is provable outright (the project's short computation re-done
from `Morse.hessian_normSq_sub_holomorphic`); B, about focal points of submanifolds, does not
give statements about arbitrary holomorphic maps (non-immersions, arbitrary `n`). -/
theorem B_to_A : B → A := by
  intro _ V _ _ F _ _ w q hw n t
  open Complex in
  have h : (Morse.hessian (fun z => ‖w z - (w q + t • n)‖ ^ 2) q).bilinearComp
      ((Morse.complexStructureEquiv (Morse.realMulI : V →L[ℝ] V) Morse.realMulI_realMulI :
        V ≃L[ℝ] V) : V →L[ℝ] V)
      ((Morse.complexStructureEquiv (Morse.realMulI : V →L[ℝ] V) Morse.realMulI_realMulI :
        V ≃L[ℝ] V) : V →L[ℝ] V) = Morse.hessian (fun z => ‖w z - (w q - t • n)‖ ^ 2) q := by
    ext v v'
    simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe,
      Morse.complexStructureEquiv_apply, Morse.realMulI_apply]
    rw [Morse.hessian_normSq_sub_holomorphic hw, Morse.hessian_normSq_sub_holomorphic hw]
    simp only [map_smul, smul_apply, smul_smul, I_mul_I, neg_one_smul, map_neg,
      Morse.reInner_I_smul, sub_add_cancel_left, sub_sub_cancel, neg_apply,
      neg_neg]
  rw [← h, Morse.nullity_bilinearComp]

#rt_check RoundTrip.V5_7.B_to_A [Morse.nullity_hessian_normSq_sub_add_eq_sub]
#rt_overlap RoundTrip.V5_7.B_to_A [Morse.nullity_hessian_normSq_sub_add_eq_sub]
#rt_check RoundTrip.V5_7.A_to_B [Morse.nullity_hessian_normSq_sub_add_eq_sub]

end RoundTrip.V5_7
