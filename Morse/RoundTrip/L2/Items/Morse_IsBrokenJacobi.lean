import Morse
import RoundTrip.L2.Blind.Morse_IsBrokenJacobi
namespace RoundTrip.L2.Morse_IsBrokenJacobi

open Set Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace

/-! The dictionary between the blind geometry (span of velocities, `P`, `II`, Gauss-equation `R`)
and the project's is the same as in the layer-2 check of `Morse.IsJacobiField`
(`RoundTrip/L2/Items/Morse_IsJacobiField.lean`), repeated here; then its local version on a
subinterval `[u, v] ⊆ [0, 1]`, with the uniqueness of solutions of the Jacobi system on `[u, v]`
(adapted from `Morse.IsJacobiField.eqOn_jacSol`). -/

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

/-! ### Jacobi fields on a subinterval -/

section Local

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {N : Set V}

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The project's Jacobi expression only depends on the germ of the field. -/
theorem jacobiExpr_congr (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ X J : ℝ → V} {t : ℝ}
    (h : X =ᶠ[𝓝 t] J) : Morse.jacobiExpr hN γ X t = Morse.jacobiExpr hN γ J t := by
  have h1 : Morse.covD hN γ X =ᶠ[𝓝 t] Morse.covD hN γ J := by
    filter_upwards [h.deriv] with s hs
    simp only [Morse.covD, hs]
  unfold Morse.jacobiExpr
  congr 1
  · show Morse.prj hN (γ t) (deriv (Morse.covD hN γ X) t) =
      Morse.prj hN (γ t) (deriv (Morse.covD hN γ J) t)
    rw [h1.deriv_eq]
  · rw [h.eq_of_nhds]

/-- **The blind Jacobi equation on `[u, v] ⊆ [0, 1]`** (one-sided derivatives at the ends) is the
project's on `(u, v)`, for a smooth tangent field along a smooth curve in `N`. -/
theorem isJacobiOn_iff (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ X : ℝ → V}
    (hc : Morse.IsSmoothCurveIn hN γ) {u v : ℝ} (hu0 : 0 ≤ u) (huv : u < v) (hv1 : v ≤ 1)
    (hX : ContDiffOn ℝ ∞ X (Icc u v)) (hXt : ∀ t ∈ Icc u v, Morse.prj hN (γ t) (X t) = X t) :
    IsJacobiOn N γ (Icc u v) X ↔ ∀ t ∈ Ioo u v, Morse.jacobiExpr hN γ X t = 0 := by
  have h : Morse.PieceData hN γ X X u v := ⟨huv, hc.contDiffOn.mono (Icc_subset_Icc hu0 hv1),
    hX, hX, fun τ hτ => hc.mem τ ⟨hu0.trans hτ.1, hτ.2.trans hv1⟩, hXt, hXt⟩
  have hcov : ∀ Y : ℝ → V, covD N (Icc u v) γ Y = h.D Y := fun Y => by
    funext t
    simp only [covD, Morse.PieceData.D, P_eq hN]
  -- the blind expression in project terms, on `[u, v]`
  have hexpr : ∀ t ∈ Icc u v, covD N (Icc u v) γ (covD N (Icc u v) γ X) t +
      R N (γ t) (derivWithin γ (Icc u v) t) (X t) (derivWithin γ (Icc u v) t) =
      Morse.prj hN (γ t) (derivWithin (h.D X) (Icc u v) t) +
        Morse.curvR hN (γ t) (derivWithin γ (Icc u v) t) (X t) (derivWithin γ (Icc u v) t) := by
    intro t ht
    have hx := h.mem t ht
    have hv : derivWithin γ (Icc u v) t ∈ Morse.tangentSubspace hN ⟨γ t, hx⟩ :=
      (Morse.prj_eq_self_iff hN hx).1 (h.prj_derivWithin ht)
    rw [hcov, hcov, R_eq hN hx hv ((Morse.prj_eq_self_iff hN hx).1 (hXt t ht)) hv]
    simp only [Morse.PieceData.D]
  have hint : ∀ t ∈ Ioo u v, Morse.jacobiExpr hN γ X t =
      Morse.prj hN (γ t) (derivWithin (h.D X) (Icc u v) t) +
        Morse.curvR hN (γ t) (derivWithin γ (Icc u v) t) (X t) (derivWithin γ (Icc u v) t) :=
    fun t ht => by rw [Morse.jacobiExpr, h.covD_covD_eq hX ht, h.curv_eq ht]
  constructor
  · rintro ⟨-, -, he⟩ t ht
    rw [hint t ht, ← hexpr t (Ioo_subset_Icc_self ht)]
    exact he t (Ioo_subset_Icc_self ht)
  · intro he
    refine ⟨hX, fun t ht => (mem_tan_iff hN _ _).2 (hXt t ht), ?_⟩
    have hcont : ContinuousOn (fun t => Morse.prj hN (γ t) (derivWithin (h.D X) (Icc u v) t) +
        Morse.curvR hN (γ t) (derivWithin γ (Icc u v) t) (X t) (derivWithin γ (Icc u v) t))
        (Icc u v) :=
      (h.contDiffOn_prj.continuousOn.clm_apply ((h.contDiffOn_D hX).continuousOn_derivWithin
        (uniqueDiffOn_Icc huv) (by simp))).add h.continuousOn_curv
    have h0 := EqOn.of_subset_closure (s := Ioo u v) (g := fun _ => (0 : V))
      (fun t ht => by rw [← hint t ht]; exact he t ht) hcont continuousOn_const
      Ioo_subset_Icc_self (by rw [closure_Ioo huv.ne])
    intro t ht
    rw [hexpr t ht]
    exact h0 ht

/-- **Uniqueness on `[u, v]`**: a smooth tangent field on `[u, v] ⊆ [0, 1]` satisfying the Jacobi
equation on `(u, v)` agrees on `[u, v]` with an element of the project's `𝒥(γ)` (the solution of
the Jacobi system with the same initial data at `u`). -/
theorem exists_jacobi_eqOn (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ X : ℝ → V}
    (hc : Morse.IsSmoothCurveIn hN γ) {u v : ℝ} (hu0 : 0 ≤ u) (huv : u < v) (hv1 : v ≤ 1)
    (hX : ContDiffOn ℝ ∞ X (Icc u v)) (hXt : ∀ t ∈ Icc u v, Morse.prj hN (γ t) (X t) = X t)
    (hXe : ∀ t ∈ Ioo u v, Morse.jacobiExpr hN γ X t = 0) :
    ∃ J ∈ Morse.jacobiSpace hN γ hc, EqOn X J (Icc u v) := by
  set c : ℝ → V := fun t => Morse.prj hN (γ t) (derivWithin X (Icc u v) t) with hc_def
  set f : ℝ → V × V := fun t => (X t, c t) with hf_def
  have huI : u ∈ Icc (0 : ℝ) 1 := ⟨hu0, huv.le.trans hv1⟩
  have hζ1 : Morse.prj hN (γ u) (f u).1 = (f u).1 := hXt u ⟨le_rfl, huv.le⟩
  have hζ2 : Morse.prj hN (γ u) (f u).2 = (f u).2 := Morse.prj_prj hN _ _
  obtain ⟨hJ, -⟩ := Morse.isJacobiField_jacSol hc huI hζ1 hζ2
  have hu := uniqueDiffOn_Icc huv
  have hfc : ContinuousOn f (Icc u v) :=
    hX.continuousOn.prodMk ((hc.contDiffOn_prj.continuousOn.mono (Icc_subset_Icc hu0 hv1)).clm_apply
      (hX.continuousOn_derivWithin hu (by simp)))
  have hfd : ∀ t ∈ Ioo u v, HasDerivAt f (Morse.jacA hN γ t (f t)) t := by
    intro t ht
    have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨hu0.trans_lt ht.1, ht.2.trans_le hv1⟩
    have ht' := Ioo_subset_Icc_self htI
    have hn : Icc u v ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hXd : ContDiffOn ℝ ∞ (derivWithin X (Icc u v)) (Icc u v) := hX.derivWithin hu (by simp)
    have hJt : HasDerivAt X (deriv X t) t :=
      ((hX.contDiffAt hn).differentiableAt (by simp)).hasDerivAt
    have hev : derivWithin X (Icc u v) =ᶠ[𝓝 t] deriv X := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
      exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
    have hJ't : HasDerivAt (deriv X) (deriv (deriv X) t) t := by
      have := ((hXd.contDiffAt hn).differentiableAt (by simp)).hasDerivAt
      rw [hev.deriv_eq] at this
      exact this.congr_of_eventuallyEq hev.symm
    have hPd := hc.hasDerivAt_prj htI
    have hcov_ev : c =ᶠ[𝓝 t] fun x => Morse.prj hN (γ x) (deriv X x) := by
      filter_upwards [hev] with x hx
      simp only [hc_def, hx]
    have hcovd : HasDerivAt c
        (Morse.dpAlong hN γ t (deriv X t) + Morse.prj hN (γ t) (deriv (deriv X) t)) t :=
      (hPd.clm_apply hJ't).congr_of_eventuallyEq hcov_ev
    have hJP : X =ᶠ[𝓝 t] fun x => Morse.prj hN (γ x) (X x) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
      exact (hXt x (Ioo_subset_Icc_self hx)).symm
    have hJ'eq : deriv X t = Morse.dpAlong hN γ t (X t) + Morse.prj hN (γ t) (deriv X t) := by
      conv_lhs => rw [hJP.deriv_eq]
      exact (hPd.clm_apply hJt).deriv
    have hjac := hXe t ht
    have hcovD : Morse.covD hN γ X =ᶠ[𝓝 t] c := by
      filter_upwards [hev] with x hx
      simp only [Morse.covD, hc_def, hx]
    rw [Morse.jacobiExpr, Morse.covD, hcovD.deriv_eq, hcovd.deriv, ← hc.velAlong_eq htI] at hjac
    have hR : Morse.curvR hN (γ t) (Morse.velAlong γ t) (X t) (Morse.velAlong γ t) =
        Morse.curvAlong hN γ t (X t) := by
      rw [Morse.curvAlong_apply (hc.mem t ht'), hXt t (Ioo_subset_Icc_self ht)]
    rw [hR] at hjac
    have hJtan := hXt t (Ioo_subset_Icc_self ht)
    have hcovt : c t = Morse.prj hN (γ t) (deriv X t) := by simp only [hc_def, hev.eq_of_nhds]
    refine (hJt.prodMk hcovd).congr_deriv ?_
    have e2 := hc.prj_dp_prj ht' (X t)
    have e3 := hc.dp_eq ht' (deriv X t)
    have e4 := hc.prj_dp_prj ht' (deriv X t)
    rw [hJtan] at e2
    rw [Morse.jacA_of_mem ht', Morse.jacSys_apply]
    simp only [hf_def, hcovt]
    simp only [map_add, Morse.prj_prj] at hjac
    refine Prod.ext ?_ ?_
    · simp only [Morse.jacS, sub_apply, ContinuousLinearMap.comp_apply, hJtan]
      linear_combination (norm := module) hJ'eq + e2
    · simp only [Morse.jacS, sub_apply, ContinuousLinearMap.comp_apply, Morse.prj_prj]
      linear_combination (norm := module) e3 + hjac + e4
  have key := Morse.eqOn_Icc_linSol hc.continuous_jacA huv hfc hfd (s := u) ⟨le_rfl, huv.le⟩
  refine ⟨_, hJ.comp_projIcc_mem hc, fun t ht => ?_⟩
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨hu0.trans ht.1, ht.2.trans hv1⟩
  simp only [projIcc_of_mem _ htI]
  exact congrArg Prod.fst (key ht)

/-- **Local agreement**: a field is a blind Jacobi field on `[u, v] ⊆ [0, 1]` iff it agrees on
`[u, v]` with a Jacobi field of the project's `𝒥(γ)`. -/
theorem isJacobiOn_iff_exists (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ : ℝ → V}
    (hc : Morse.IsSmoothCurveIn hN γ) {u v : ℝ} (hu0 : 0 ≤ u) (huv : u < v) (hv1 : v ≤ 1)
    (X : ℝ → V) :
    IsJacobiOn N γ (Icc u v) X ↔ ∃ J ∈ Morse.jacobiSpace hN γ hc, EqOn X J (Icc u v) := by
  constructor
  · intro h
    have hXt : ∀ t ∈ Icc u v, Morse.prj hN (γ t) (X t) = X t := fun t ht =>
      (mem_tan_iff hN _ _).1 (h.2.1 t ht)
    exact exists_jacobi_eqOn hN hc hu0 huv hv1 h.1 hXt
      ((isJacobiOn_iff hN hc hu0 huv hv1 h.1 hXt).1 h)
  · rintro ⟨J, hJ, hEq⟩
    have hsub : Icc u v ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hu0 hv1
    have hX : ContDiffOn ℝ ∞ X (Icc u v) := (hJ.1.contDiffOn.mono hsub).congr hEq
    have hXt : ∀ t ∈ Icc u v, Morse.prj hN (γ t) (X t) = X t := fun t ht => by
      rw [hEq ht]; exact hJ.1.tangent t (hsub ht)
    refine (isJacobiOn_iff hN hc hu0 huv hv1 hX hXt).2 fun t ht => ?_
    have hev : X =ᶠ[𝓝 t] J := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact hEq (Ioo_subset_Icc_self hs)
    rw [jacobiExpr_congr hN hev]
    exact hJ.1.eq t ⟨hu0.trans_lt ht.1, ht.2.trans_le hv1⟩

end Local

/-! ### Broken Jacobi fields -/

section Broken

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {N : Set V}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem mem_pts {B : Finset ℝ} {τ w : ℝ} :
    w ∈ pts B τ ↔ w = 0 ∨ w = τ ∨ (w ∈ B ∧ 0 < w ∧ w < τ) := by
  simp [pts, or_assoc]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem pts_mem_Icc {B : Finset ℝ} {τ w : ℝ} (hτ : 0 ≤ τ) (hw : w ∈ pts B τ) :
    w ∈ Icc 0 τ := by
  rcases mem_pts.1 hw with rfl | rfl | ⟨-, h1, h2⟩
  exacts [⟨le_rfl, hτ⟩, ⟨hτ, le_rfl⟩, ⟨h1.le, h2.le⟩]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- Consecutive subdivision points around an interval `[s, s']` free of division points. -/
theorem exists_consecutive (B : Finset ℝ) {τ s s' : ℝ} (hs : 0 ≤ s) (hss' : s < s')
    (hs'τ : s' ≤ τ) (hB : ∀ b ∈ B, b ∉ Ioo s s') :
    ∃ u ∈ pts B τ, ∃ v ∈ pts B τ, u ≤ s ∧ s' ≤ v ∧ u < v ∧ ∀ w ∈ pts B τ, w ∉ Ioo u v := by
  classical
  set F : Finset ℝ := insert 0 (insert τ (B.filter fun t => 0 < t ∧ t < τ))
  have hF : ∀ w, w ∈ F ↔ w ∈ pts B τ := fun w => by
    rw [mem_pts]; simp [F]
  have hL : (F.filter (· ≤ s)).Nonempty := ⟨0, by simp [F, hs]⟩
  have hR : (F.filter (s' ≤ ·)).Nonempty := ⟨τ, by simp [F, hs'τ]⟩
  set u := (F.filter (· ≤ s)).max' hL
  set v := (F.filter (s' ≤ ·)).min' hR
  have hu := Finset.mem_filter.1 ((F.filter (· ≤ s)).max'_mem hL)
  have hv := Finset.mem_filter.1 ((F.filter (s' ≤ ·)).min'_mem hR)
  refine ⟨u, (hF u).1 hu.1, v, (hF v).1 hv.1, hu.2, hv.2, by linarith [hu.2, hv.2], ?_⟩
  rintro w hw ⟨hwu, hwv⟩
  have hwF := (hF w).2 hw
  rcases le_or_gt w s with h | h
  · exact absurd ((F.filter (· ≤ s)).le_max' w (Finset.mem_filter.2 ⟨hwF, h⟩)) (not_le.2 hwu)
  rcases le_or_gt s' w with h' | h'
  · exact absurd ((F.filter (s' ≤ ·)).min'_le w (Finset.mem_filter.2 ⟨hwF, h'⟩)) (not_le.2 hwv)
  rcases mem_pts.1 hw with rfl | rfl | ⟨hwB, -, -⟩
  · linarith
  · linarith
  · exact hB w hwB ⟨h, h'⟩

/-- **Agreement for `0 < τ ≤ 1`** (Milnor's setting; `γ` smooth in `N` is the signature's `hc`):
the project's broken Jacobi fields on `[0, τ]` for the division points `B` (on every interval
`[s, s'] ⊆ [0, τ]` free of division points, the field agrees with a Jacobi field along `γ`) are the
blind ones (continuous on `[0, τ]`, a Jacobi field on each segment between consecutive
subdivision points, derivatives within the segment). -/
theorem agree_of (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ : ℝ → V}
    (hc : Morse.IsSmoothCurveIn hN γ) (B : Finset ℝ) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (X : ℝ → V) : Morse.IsBrokenJacobi hN γ hc B τ X ↔ T hN γ hc B τ X := by
  constructor
  · intro hP
    refine ⟨Morse.continuousOn_of_piecewise (B := B) fun s t hs hst ht hB => ?_,
      fun u hu v hv huv hcons => ?_⟩
    · obtain ⟨J, hJ, hEq⟩ := hP s t hs hst ht hB
      exact (hJ.1.contDiffOn.continuousOn.mono (Icc_subset_Icc hs (ht.trans hτ1))).congr hEq
    · have hu' := pts_mem_Icc hτ0.le hu
      have hv' := pts_mem_Icc hτ0.le hv
      refine (isJacobiOn_iff_exists hN hc hu'.1 huv (hv'.2.trans hτ1) X).2
        (hP u v hu'.1 huv hv'.2 fun b hb hbI => hcons b ?_ hbI)
      exact mem_pts.2 (Or.inr (Or.inr ⟨hb, hu'.1.trans_lt hbI.1, hbI.2.trans_le hv'.2⟩))
  · rintro ⟨-, hT⟩ s s' hs hss' hs'τ hB
    obtain ⟨u, hu, v, hv, hus, hs'v, huv, hcons⟩ := exists_consecutive B hs hss' hs'τ hB
    have hu' := pts_mem_Icc hτ0.le hu
    have hv' := pts_mem_Icc hτ0.le hv
    obtain ⟨J, hJ, hEq⟩ := (isJacobiOn_iff_exists hN hc hu'.1 huv (hv'.2.trans hτ1) X).1
      (hT u hu v hv huv hcons)
    exact ⟨J, hJ, hEq.mono (Icc_subset_Icc hus hs'v)⟩

/-- **They differ for `τ < 0`** (outside Milnor's `0 < τ ≤ 1`): the project's condition is vacuous
(there is no `[s, s'] ⊆ [0, τ]`), while the blind one asks for a Jacobi field on the segment
`[τ, 0]` between the subdivision points `τ` and `0`. -/
theorem differ [Nontrivial V] (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ : ℝ → V}
    (hc : Morse.IsSmoothCurveIn hN γ) (B : Finset ℝ) :
    ∃ X : ℝ → V, Morse.IsBrokenJacobi hN γ hc B (-1) X ∧ ¬ T hN γ hc B (-1) X := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨fun t => if t = -1 / 2 then v else 0, fun s s' hs hss' hs' _ => by linarith, ?_⟩
  rintro ⟨-, hT⟩
  have hm1 : (-1 : ℝ) ∈ pts B (-1) := mem_pts.2 (Or.inr (Or.inl rfl))
  have h0 : (0 : ℝ) ∈ pts B (-1) := mem_pts.2 (Or.inl rfl)
  have hJ := hT (-1) hm1 0 h0 (by norm_num) fun w hw hwI => by
    rcases mem_pts.1 hw with rfl | rfl | ⟨-, h1, h2⟩
    · exact lt_irrefl _ hwI.2
    · exact lt_irrefl _ hwI.1
    · linarith
  have hcont : ContinuousOn (fun t : ℝ => if t = -1 / 2 then v else 0) (Icc (-1 / 2) 0) :=
    hJ.1.continuousOn.mono (Icc_subset_Icc (by norm_num) le_rfl)
  have heq := EqOn.of_subset_closure (s := Ioo (-1 / 2 : ℝ) 0) (g := fun _ => (0 : V))
    (fun t ht => by simp [ht.1.ne']) hcont continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo (by norm_num)])
  exact hv (by simpa using heq (show (-1 / 2 : ℝ) ∈ Icc (-1 / 2) 0 by norm_num))

end Broken

end RoundTrip.L2.Morse_IsBrokenJacobi
