import Morse
import RoundTrip.Check
import RoundTrip.Blind.V5_13

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V5_13

/-- The project's statement (universes instantiated at 0): (1) on a slice submanifold `N` of a
finite-dimensional real inner product space `V` with `J`-invariant tangent spaces, every critical
point (degenerate or not) of `L_p` has `2 · index ≤ dim N`; (2) for `V = 𝔼 n` and `dim N = 2k`,
`index ≤ k`. -/
def A : Prop :=
  type_of% @Morse.two_mul_indexM_normSq_sub_le.{0,0,0} ∧ type_of% @Morse.indexM_normSq_sub_le

theorem A_holds : A := ⟨@Morse.two_mul_indexM_normSq_sub_le, @Morse.indexM_normSq_sub_le⟩

/-- A ⇒ B: specialize the second conjunct of A (`index ≤ k`) to `n = K + 1`, model `ℝ^{d+1}`
with `d + 1 = 2k`, after turning B's linear isometry `J` into a continuous linear map; B's
non-degeneracy hypothesis is not needed. -/
theorem A_to_B : A → B := by
  intro hA K d m k M hM J hJ hc hdk p
  obtain ⟨-, h2⟩ := hA
  have key : ∀ {D : ℕ} (hM' : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn D) (Rn m) M),
      Morse.IsComplexSubmanifold hM' (J.toContinuousLinearEquiv : Rn (K + 1) →L[ℝ] Rn (K + 1)) →
      D = 2 * k →
      letI := hM'.chartedSpace
      ∀ q : M, Morse.IsCriticalPointM (Rn D) (fun y : M => Lp p y.1) q →
        Morse.indexM (Rn D) (fun y : M => Lp p y.1) q ≤ k := by
    intro D hM' hc' hD
    subst hD
    intro q hq
    exact h2 hM' ⟨fun v => hJ v, fun v w => J.inner_map_map v w⟩ hc' p q hq
  intro q hq _
  exact key hM (fun q v hv => hc q v hv) hdk q hq

/-- B ⇒ A holds only vacuously: A is re-proved outright by the project's own argument (the
"shorter route": `Morse.indexM_normSq_sub_eq`, `Morse.fderiv_sliceParam_Jc`,
`Morse.inner_fderiv_fderiv_sliceParam_Jc`, `Morse.two_mul_index_le_finrank`). B, restricted to
non-degenerate critical points and to Euclidean models with `dim N = 2k`, is not used. -/
theorem two_mul_le {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {J : V →L[ℝ] V}
    (hJ : Morse.IsOrthComplexStructure J) (hc : Morse.IsComplexSubmanifold hN J)
    (p : V) (q : N)
    (hcrit : letI := hN.chartedSpace; Morse.IsCriticalPointM Z (fun x : N => ‖(x : V) - p‖ ^ 2) q) :
    letI := hN.chartedSpace
    2 * Morse.indexM Z (fun x : N => ‖(x : V) - p‖ ^ 2) q ≤ finrank ℝ Z := by
  let _ := hN.chartedSpace
  obtain ⟨σ, hqσ⟩ := hN q q.2
  rw [Morse.indexM_normSq_sub_eq hN σ p hqσ hcrit]
  have hu : (σ.φ q).1 ∈ σ.toChart.target := Morse.toChart_apply_mem_target σ hqσ
  set u := (σ.φ q).1 with hu_def
  have hx : ContDiffAt ℝ ∞ (Morse.sliceParam σ) u := Morse.contDiffAt_sliceParam σ hu
  set D := fderiv ℝ (Morse.sliceParam σ) u with hD_def
  set D2 := fderiv ℝ (fderiv ℝ (Morse.sliceParam σ)) u with hD2_def
  set ν := Morse.sliceParam σ u - p with hν_def
  have hcp : Morse.IsCriticalPoint ((fun y : V => ‖y - p‖ ^ 2) ∘ Morse.sliceParam σ) u :=
    (Morse.isCriticalPointM_comp_val_iff_sliceParam hN σ hqσ
      ((Morse.contDiff_normSq_sub p).differentiable (by simp) _)).1 hcrit
  have hν : ∀ t ∈ LinearMap.range (D : Z →ₗ[ℝ] V), ⟪ν, t⟫ = 0 := by
    rintro _ ⟨ξ, rfl⟩
    have h1 := hcp.fderiv
    have h2 : fderiv ℝ ((fun y : V => ‖y - p‖ ^ 2) ∘ Morse.sliceParam σ) u ξ = 2 * ⟪ν, D ξ⟫ := by
      rw [fderiv_comp u ((Morse.contDiff_normSq_sub p).differentiable (by simp) _)
        (hx.differentiableAt (by simp)), ContinuousLinearMap.comp_apply,
        Morse.fderiv_normSq_sub_apply]
    rw [h1] at h2
    simp only [ContinuousLinearMap.zero_apply] at h2
    change ⟪ν, D ξ⟫ = 0
    linarith
  have hJD : ∀ ξ, J (D ξ) = D (Morse.Jc σ J u ξ) := fun ξ =>
    (Morse.fderiv_sliceParam_Jc σ hc hu ξ).symm
  have hJν : ∀ t ∈ LinearMap.range (D : Z →ₗ[ℝ] V), ⟪J ν, t⟫ = 0 := by
    rintro _ ⟨ξ, rfl⟩
    change ⟪J ν, D ξ⟫ = 0
    rw [hJ.inner_left, hJD, hν (D (Morse.Jc σ J u ξ)) ⟨_, rfl⟩, neg_zero]
  have hx2 : ContDiffAt ℝ 2 (Morse.sliceParam σ) u := hx.of_le (WithTop.coe_le_coe.2 le_top)
  have hsymm : ∀ v w, D2 v w = D2 w v := fun v w => (hx2.isSymmSndFDerivAt (by simp)) v w
  have hF2 : ∀ η ξ, ⟪ν, D2 η (Morse.Jc σ J u ξ)⟫ = ⟪ν, J (D2 η ξ)⟫ :=
    Morse.inner_fderiv_fderiv_sliceParam_Jc σ hc hu hν
  have hF2' : ∀ η ξ, ⟪J ν, D2 η (Morse.Jc σ J u ξ)⟫ = ⟪J ν, J (D2 η ξ)⟫ :=
    Morse.inner_fderiv_fderiv_sliceParam_Jc σ hc hu hJν
  have hHess : ∀ v w, Morse.hessian (fun z => ‖Morse.sliceParam σ z - p‖ ^ 2) u v w =
      2 * (⟪D v, D w⟫ + ⟪ν, D2 v w⟫) := fun v w => by
    rw [Morse.hessian_normSq_sub_comp hx2 p v w, real_inner_comm ν]
  refine Morse.two_mul_index_le_finrank _ (Morse.Jc σ J u : Z →ₗ[ℝ] Z) ?_ fun ξ => ?_
  · intro ξ ξ' h
    have h1 : D (Morse.Jc σ J u ξ) = D (Morse.Jc σ J u ξ') := congrArg D h
    rw [← hJD, ← hJD] at h1
    have h2 : D ξ = D ξ' := by
      have := congrArg J h1
      rwa [hJ.sq, hJ.sq, neg_inj] at this
    have h3 := congrArg (fun v => (fderiv ℝ σ.φ (Morse.sliceParam σ u) v).1) h2
    rwa [Morse.fst_fderiv_sliceChart_fderiv_sliceParam σ hu,
      Morse.fst_fderiv_sliceChart_fderiv_sliceParam σ hu] at h3
  · change 0 ≤ Morse.hessian _ u ξ ξ + Morse.hessian _ u (Morse.Jc σ J u ξ) (Morse.Jc σ J u ξ)
    rw [hHess, hHess, ← hJD, hJ.inner]
    have key : ⟪ν, D2 (Morse.Jc σ J u ξ) (Morse.Jc σ J u ξ)⟫ = -⟪ν, D2 ξ ξ⟫ := by
      rw [hF2, show ⟪ν, J (D2 (Morse.Jc σ J u ξ) ξ)⟫ = -⟪J ν, D2 (Morse.Jc σ J u ξ) ξ⟫ by
        rw [hJ.inner_left, neg_neg], hsymm, hF2', hJ.inner]
    rw [key]
    nlinarith [real_inner_self_nonneg (x := D ξ)]

theorem B_to_A : B → A := by
  intro _
  refine ⟨fun hJ hc p q hcrit => two_mul_le hJ hc p q hcrit, ?_⟩
  intro n k w M hM J hJ hc p q hcrit
  have h := two_mul_le hJ hc p q hcrit
  rw [finrank_euclideanSpace_fin] at h
  omega

#rt_check RoundTrip.V5_13.A_to_B [Morse.two_mul_indexM_normSq_sub_le, Morse.indexM_normSq_sub_le]
#rt_check RoundTrip.V5_13.B_to_A [Morse.two_mul_indexM_normSq_sub_le, Morse.indexM_normSq_sub_le]
#rt_overlap RoundTrip.V5_13.B_to_A [Morse.two_mul_indexM_normSq_sub_le, Morse.indexM_normSq_sub_le]

end RoundTrip.V5_13
