import Morse
import RoundTrip.L2.Blind.Morse_IsJacobiField
namespace RoundTrip.L2.Morse_IsJacobiField

open Set Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace

/-! ### Dictionary: the blind `T_xN`, `P`, `II`, `R` are the project's -/

section Dictionary

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}

/-- Every vector of the project tangent space is a velocity (copied from the layer-2 check of
`Morse.tangentSubspace`). -/
theorem exists_curve (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) {q : N} (hq : q.1 ∈ σ.φ.source)
    (a : Z) : IsVelocity N q (fderiv ℝ (Morse.sliceParam σ) (σ.φ q).1 a) := by
  set z₀ : Z := (σ.φ q).1 with hz₀
  have hz₀mem : z₀ ∈ σ.toChart.target := Morse.toChart_apply_mem_target σ hq
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (Morse.isOpen_toChart_target σ) z₀ hz₀mem
  set ε : ℝ := r / (‖a‖ + 1) with hε
  have hε0 : 0 < ε := div_pos hr (by positivity)
  have hmaps : Set.MapsTo (fun t : ℝ => z₀ + t • a) (Set.Ioo (-ε) ε) σ.toChart.target := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have ht' : |t| < ε := abs_lt.2 ht
    have h1 : |t| * (‖a‖ + 1) < r := by
      rw [hε, lt_div_iff₀ (by positivity)] at ht'
      exact ht'
    nlinarith [abs_nonneg t, norm_nonneg a]
  refine ⟨ε, hε0, fun t => Morse.sliceParam σ (z₀ + t • a), ?_, ?_, ?_, ?_⟩
  · exact (Morse.contDiffOn_sliceParam σ).comp
      (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn hmaps
  · exact fun t ht => Morse.sliceParam_mem σ (hmaps ht)
  · simpa using Morse.sliceParam_toChart σ hq
  · have hd : HasDerivAt (fun t : ℝ => z₀ + t • a) a 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add z₀
    have hx : HasFDerivAt (Morse.sliceParam σ) (fderiv ℝ (Morse.sliceParam σ) z₀)
        (z₀ + (0:ℝ) • a) := by
      rw [zero_smul, add_zero]
      exact ((Morse.contDiffAt_sliceParam σ hz₀mem).differentiableAt (by simp)).hasFDerivAt
    exact hx.comp_hasDerivAt 0 hd

/-- Every velocity lies in the project tangent space (copied from the layer-2 check of
`Morse.tangentSubspace`). -/
theorem mem_of_velocity (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (q : N) {v : V}
    (hv : IsVelocity N q v) : v ∈ Morse.tangentSubspace hN q := by
  obtain ⟨ε, hε, γ, -, hγN, hγ0, hγv⟩ := hv
  obtain ⟨σ, hσ⟩ := hN q.1 q.2
  rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ]
  have hφ : DifferentiableAt ℝ σ.φ q := by
    have h1 := σ.φ.contMDiffOn_toFun
    rw [contMDiffOn_iff_contDiffOn] at h1
    exact (h1.contDiffAt (σ.φ.open_source.mem_nhds hσ)).differentiableAt (by simp)
  set c : ℝ → Z := fun t => (σ.φ (γ t)).1 with hc_def
  have hc : HasDerivAt c (fderiv ℝ (fun x => (σ.φ x).1) q v) 0 := by
    have hfst : DifferentiableAt ℝ (fun x => (σ.φ x).1) (γ 0) := by
      rw [hγ0]
      exact differentiableAt_fst.comp _ hφ
    exact hγ0 ▸ hfst.hasFDerivAt.comp_hasDerivAt 0 hγv
  have hc0 : c 0 = (σ.φ q).1 := by simp [hc_def, hγ0]
  have hev : γ =ᶠ[𝓝 0] Morse.sliceParam σ ∘ c := by
    have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ σ.φ.source :=
      hγv.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact σ.φ.open_source.mem_nhds hσ)
    have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Set.Ioo (-ε) ε :=
      Ioo_mem_nhds (by linarith) hε
    filter_upwards [h1, h2] with t ht1 ht2
    have hs : (σ.φ (γ t)).2 = 0 := (σ.slice _ ht1).1 (hγN ht2)
    have : ((σ.φ (γ t)).1, (0 : W)) = σ.φ (γ t) := Prod.ext rfl hs.symm
    simp only [Function.comp_apply, hc_def, Morse.sliceParam]
    rw [this, σ.φ.invFun_apply ht1]
  have hx : HasFDerivAt (Morse.sliceParam σ) (fderiv ℝ (Morse.sliceParam σ) (σ.φ q).1) (c 0) := by
    rw [hc0]
    exact ((Morse.contDiffAt_sliceParam σ (Morse.toChart_apply_mem_target σ hσ)).differentiableAt
      (by simp)).hasFDerivAt
  have hγ' := (hx.comp_hasDerivAt 0 hc).congr_of_eventuallyEq hev
  exact ⟨_, (hγv.unique hγ').symm⟩

/-- **The blind tangent space is the project's** (at points of `N`). -/
theorem tan_eq (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {x : V} (hx : x ∈ N) :
    tan N x = Morse.tangentSubspace hN ⟨x, hx⟩ := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun v hv => mem_of_velocity hN ⟨x, hx⟩ hv
  · obtain ⟨σ, hσ⟩ := hN x hx
    rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ]
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span (exists_curve σ (q := ⟨x, hx⟩) hσ a)

/-- Off `N` the blind tangent space is `0` (no curve in `N` passes through `x`). -/
theorem tan_eq_bot {x : V} (hx : x ∉ N) : tan N x = ⊥ := by
  rw [tan, Submodule.span_eq_bot]
  rintro v ⟨ε, hε, c, -, hcN, hc0, -⟩
  exact absurd (hc0 ▸ hcN ⟨by linarith, hε⟩) hx

variable [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
theorem starProjection_congr {K K' : Submodule ℝ V} [K.HasOrthogonalProjection]
    [K'.HasOrthogonalProjection] (h : K = K') : K.starProjection = K'.starProjection := by
  subst h; rfl

/-- **The blind projection is the project's `prj`** (everywhere: both are `0` off `N`). -/
theorem P_eq (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (x : V) : P N x = Morse.prj hN x := by
  by_cases hx : x ∈ N
  · rw [Morse.prj_of_mem hN hx, Morse.tanProj, P, starProjection_congr (tan_eq hN hx)]
  · rw [Morse.prj_of_notMem hN hx, P, starProjection_congr (tan_eq_bot hx),
      Submodule.starProjection_bot]

theorem P_fun_eq (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) : P N = Morse.prj hN :=
  funext (P_eq hN)

theorem mem_tan_iff (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (x v : V) :
    v ∈ tan N x ↔ Morse.prj hN x v = v := by
  by_cases hx : x ∈ N
  · rw [tan_eq hN hx, Morse.prj_eq_self_iff hN hx]
  · rw [tan_eq_bot hx, Morse.prj_of_notMem hN hx, Submodule.mem_bot]
    simp [eq_comm]

variable [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ W] in
/-- **The derivative within `N` of the blind `P`, on tangent vectors, is the project's
`dN P`.** -/
theorem fderivWithin_P_apply (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {x : V} (hx : x ∈ N)
    {v : V} (hv : v ∈ Morse.tangentSubspace hN ⟨x, hx⟩) :
    fderivWithin ℝ (P N) N x v = Morse.dN hN (Morse.tanProj hN) ⟨x, hx⟩ v := by
  set q : N := ⟨x, hx⟩
  set σ := Morse.sliceAt hN q
  have hq : x ∈ σ.φ.source := Morse.mem_sliceAt_source hN q
  have hd : HasFDerivAt (Morse.projRep σ) (fderiv ℝ (Morse.projRep σ) x) x :=
    ((Morse.contDiffAt_projRep σ (q := q) hq).differentiableAt (by simp)).hasFDerivAt
  have hev : P N =ᶠ[𝓝[N] x] Morse.projRep σ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (σ.φ.open_source.mem_nhds hq)] with
      y hyN hys
    rw [P_eq hN, Morse.prj_of_mem hN hyN, Morse.projRep_eq hN σ (x := ⟨y, hyN⟩) hys]
  have hW : HasFDerivWithinAt (P N) (fderiv ℝ (Morse.projRep σ) x) N x :=
    hd.hasFDerivWithinAt.congr_of_eventuallyEq hev (by
      rw [P_eq hN, Morse.prj_of_mem hN hx, Morse.projRep_eq hN σ (x := q) hq])
  have key : ∀ w, IsVelocity N x w → fderivWithin ℝ (P N) N x w =
      fderiv ℝ (Morse.projRep σ) x w := by
    rintro w ⟨ε, hε, c, -, hcN, hc0, hcv⟩
    have hn : Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hε
    have h1 := ((hc0 ▸ hW.differentiableWithinAt.hasFDerivWithinAt :
      HasFDerivWithinAt (P N) (fderivWithin ℝ (P N) N x) N (c 0)).comp_hasDerivWithinAt 0
        hcv.hasDerivWithinAt hcN).hasDerivAt hn
    have h2 := ((hc0 ▸ hW : HasFDerivWithinAt (P N) (fderiv ℝ (Morse.projRep σ) x) N
      (c 0)).comp_hasDerivWithinAt 0 hcv.hasDerivWithinAt hcN).hasDerivAt hn
    exact h1.unique h2
  have hspan : tan N x ≤ LinearMap.ker ((fderivWithin ℝ (P N) N x -
      fderiv ℝ (Morse.projRep σ) x : V →L[ℝ] V →L[ℝ] V) : V →ₗ[ℝ] V →L[ℝ] V) :=
    Submodule.span_le.2 fun w hw => by
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        sub_apply, key w hw, sub_self]
  have hv' : v ∈ tan N x := by rw [tan_eq hN hx]; exact hv
  have := hspan hv'
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply,
    sub_eq_zero] at this
  rw [this, Morse.dN_tanProj_eq_fderiv hN σ (q := q) hq hv]

omit [FiniteDimensional ℝ W] in
/-- **The blind curvature is the project's `curvR`** at tangent arguments. -/
theorem R_eq (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {x : V} (hx : x ∈ N) {X Y Z' : V}
    (hX : X ∈ Morse.tangentSubspace hN ⟨x, hx⟩) (hY : Y ∈ Morse.tangentSubspace hN ⟨x, hx⟩)
    (hZ : Z' ∈ Morse.tangentSubspace hN ⟨x, hx⟩) :
    R N x X Y Z' = Morse.curvR hN x X Y Z' := by
  set q : N := ⟨x, hx⟩
  set D := Morse.dN hN (Morse.tanProj hN) q
  have hPx : P N x = Morse.tanProj hN q := by rw [P_eq hN, Morse.prj_of_mem hN hx]
  -- `II(v, w) = D_v w` for tangent `v, w`
  have hII : ∀ {v w : V}, v ∈ Morse.tangentSubspace hN q → w ∈ Morse.tangentSubspace hN q →
      II N x v w = D v w := by
    intro v w hv hw
    simp only [II, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      sub_apply, one_apply_eq_self]
    rw [fderivWithin_P_apply hN hx hv, hPx, Morse.tanProj_dN_tanProj_of_mem hN hv hw, sub_zero]
  -- `P(II(Y, ·)* n) = D_Y n` for normal `n`
  have hadj : ∀ {v n : V}, v ∈ Morse.tangentSubspace hN q →
      n ∈ (Morse.tangentSubspace hN q)ᗮ →
      P N x (ContinuousLinearMap.adjoint (II N x v) n) = D v n := by
    intro v n hv hn
    have hPn : Morse.tanProj hN q n = 0 := (Morse.tanProj_eq_zero_iff hN).2 hn
    have hDn : D v n ∈ Morse.tangentSubspace hN q :=
      Morse.dN_tanProj_mem_of_mem_orthogonal hN hv hn
    refine ext_inner_right ℝ fun u => ?_
    rw [hPx, Morse.inner_tanProj_left, ContinuousLinearMap.adjoint_inner_left]
    simp only [II, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      sub_apply, one_apply_eq_self]
    rw [fderivWithin_P_apply hN hx hv, hPx, inner_sub_right, ← Morse.inner_tanProj_left hN q n,
      hPn, inner_zero_left, sub_zero, ← Morse.inner_dN_tanProj_comm, ← Morse.inner_tanProj_left,
      Morse.tanProj_eq_self hN hDn]
  have hXZ := Morse.dN_tanProj_mem_orthogonal_of_mem hN hX hZ
  have hYZ := Morse.dN_tanProj_mem_orthogonal_of_mem hN hY hZ
  rw [R, hII hX hZ, hII hY hZ, map_sub, hadj hY hXZ, hadj hX hYZ, Morse.curvR_of_mem hN hx,
    Morse.curvOp_apply]
  rfl

end Dictionary

/-! ### Jacobi fields -/

section Jacobi

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {N : Set V}

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The blind covariant derivative within `[0, 1]` is the project's `covAlong`. -/
theorem covD_eq (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (γ X : ℝ → V) :
    covD N (Icc 0 1) γ X = Morse.covAlong hN γ X := by
  funext t
  simp only [covD, Morse.covAlong, P_eq hN]

/-- The blind Jacobi expression on `[0, 1]`, in project terms. -/
theorem blindExpr_eq (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ J : ℝ → V}
    (hc : Morse.IsSmoothCurveIn hN γ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hJt : Morse.prj hN (γ t) (J t) = J t) :
    covD N (Icc 0 1) γ (covD N (Icc 0 1) γ J) t +
        R N (γ t) (derivWithin γ (Icc 0 1) t) (J t) (derivWithin γ (Icc 0 1) t) =
      Morse.covAlong hN γ (Morse.covAlong hN γ J) t +
        Morse.curvR hN (γ t) (Morse.velAlong γ t) (J t) (Morse.velAlong γ t) := by
  have hx := hc.mem t ht
  have hv : Morse.velAlong γ t ∈ Morse.tangentSubspace hN ⟨γ t, hx⟩ :=
    (Morse.prj_eq_self_iff hN hx).1 (hc.velAlong_mem ht)
  rw [covD_eq hN, covD_eq hN]
  congr 1
  exact R_eq hN hx hv ((Morse.prj_eq_self_iff hN hx).1 hJt) hv

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The project's Jacobi expression at an interior point, in terms of `covAlong`. -/
theorem jacobiExpr_eq (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ J : ℝ → V}
    (hc : Morse.IsSmoothCurveIn hN γ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Morse.jacobiExpr hN γ J t = Morse.covAlong hN γ (Morse.covAlong hN γ J) t +
      Morse.curvR hN (γ t) (Morse.velAlong γ t) (J t) (Morse.velAlong γ t) := by
  have hev : Morse.covD hN γ J =ᶠ[𝓝 t] Morse.covAlong hN γ J := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    rw [Morse.covD, Morse.covAlong, derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  rw [Morse.jacobiExpr, Morse.covD, hev.deriv_eq, Morse.covAlong,
    derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), hc.velAlong_eq ht]

/-- The blind Jacobi expression is continuous on `[0, 1]` for a smooth tangent field. -/
theorem continuousOn_expr (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ J : ℝ → V}
    (hc : Morse.IsSmoothCurveIn hN γ) (hJ : ContDiffOn ℝ ∞ J (Icc 0 1))
    (hJt : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN (γ t) (J t) = J t) :
    ContinuousOn (fun t => Morse.covAlong hN γ (Morse.covAlong hN γ J) t +
      Morse.curvR hN (γ t) (Morse.velAlong γ t) (J t) (Morse.velAlong γ t)) (Icc 0 1) := by
  have hu := uniqueDiffOn_Icc (zero_lt_one' ℝ)
  have hcov : ContDiffOn ℝ ∞ (Morse.covAlong hN γ J) (Icc 0 1) :=
    hc.contDiffOn_prj.clm_apply (hJ.derivWithin hu (by simp))
  have h1 : ContinuousOn (Morse.covAlong hN γ (Morse.covAlong hN γ J)) (Icc 0 1) :=
    hc.contDiffOn_prj.continuousOn.clm_apply
      (hcov.derivWithin (m := ∞) hu (by simp)).continuousOn
  refine h1.add fun t ht => ?_
  have hV := hc.contDiffOn_velAlong.continuousOn
  exact Morse.continuousWithinAt_curvR hN ht (hc.contDiffOn.continuousOn t ht) hc.mem (hV t ht)
    (hJ.continuousOn t ht) (hV t ht) (fun τ hτ => hc.velAlong_mem hτ) hJt

/-- **The project's Jacobi fields along a smooth curve `γ` in `N`** (equation on `(0, 1)`) are
the blind ones (equation on `[0, 1]`, derivatives within `[0, 1]`). -/
theorem isJacobiField_iff (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ J : ℝ → V}
    (hc : Morse.IsSmoothCurveIn hN γ) :
    Morse.IsJacobiField hN γ J ↔ IsJacobiOn N γ (Icc 0 1) J := by
  constructor
  · intro hJ
    refine ⟨hJ.contDiffOn, fun t ht => (mem_tan_iff hN _ _).2 (hJ.tangent t ht), ?_⟩
    have h0 : EqOn (fun t => Morse.covAlong hN γ (Morse.covAlong hN γ J) t +
        Morse.curvR hN (γ t) (Morse.velAlong γ t) (J t) (Morse.velAlong γ t)) 0 (Icc 0 1) := by
      refine EqOn.of_subset_closure (s := Ioo 0 1) (fun t ht => ?_)
        (continuousOn_expr hN hc hJ.contDiffOn hJ.tangent) continuousOn_const Ioo_subset_Icc_self
        (by rw [closure_Ioo zero_ne_one])
      rw [← jacobiExpr_eq hN hc ht]
      exact hJ.eq t ht
    intro t ht
    rw [blindExpr_eq hN hc ht (hJ.tangent t ht)]
    exact h0 ht
  · rintro ⟨hJs, hJt, hJe⟩
    have hJt' : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN (γ t) (J t) = J t := fun t ht =>
      (mem_tan_iff hN _ _).1 (hJt t ht)
    refine ⟨hJs, hJt', fun t ht => ?_⟩
    have := hJe t (Ioo_subset_Icc_self ht)
    rw [blindExpr_eq hN hc (Ioo_subset_Icc_self ht) (hJt' t (Ioo_subset_Icc_self ht))] at this
    rw [jacobiExpr_eq hN hc ht, this]

end Jacobi

/-- **Agreement for a smooth curve `γ` in `N`** (in particular for a geodesic, Milnor's
hypothesis). -/
theorem agree_of {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    {γ J : ℝ → V} (hc : Morse.IsSmoothCurveIn hN γ) : Morse.IsJacobiField hN γ J ↔ T hN γ J :=
  isJacobiField_iff hN hc

end RoundTrip.L2.Morse_IsJacobiField
