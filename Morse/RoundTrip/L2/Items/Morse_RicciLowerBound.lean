import Morse
import RoundTrip.L2.Blind.Morse_RicciLowerBound

/-! Layer-2 check of `Morse.RicciLowerBound` (`K(U, U) ≥ (n − 1)/r²` for unit `U ∈ T_qN`, all
`q ∈ N`, `n = finrank Z`, `K = Morse.ricci`) against the blind textbook definition (the same
inequality, with the blind tangent space — span of velocities of curves in `N` — and the Ricci
form the trace of `W ↦ R(U, W)U`, `R` given by the Gauss equation in Milnor's sign via
`LinearMap.adjoint`, `II = (1 − P_q) ∘ dP_q` computed by `fderivWithin`).

Equivalent outright, for every `r` (`agree`): the tangent spaces agree (so do the unit vectors),
the Gauss-equation curvature on `T_qN` is `Morse.curvTensor` (compare inner products, as in the
layer-2 item `Morse_curvTensor`), and the trace over the blind tangent space is transported to the
trace over `Morse.tangentSubspace` by `subst` of the equality of submodules. Both leave `r`
unconstrained (`r = 0` gives the bound `K(U, U) ≥ 0` by `x / 0 = 0`), and both take `n = finrank Z`. -/

namespace RoundTrip.L2.Morse_RicciLowerBound

open Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}

/-- Every vector of the project tangent space is a velocity. -/
theorem exists_curve (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) {q : N} (hq : q.1 ∈ σ.φ.source)
    (a : Z) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V, ContDiffOn ℝ ∞ γ (Set.Ioo (-ε) ε) ∧
      Set.MapsTo γ (Set.Ioo (-ε) ε) N ∧ γ 0 = q ∧
      HasDerivAt γ (fderiv ℝ (Morse.sliceParam σ) (σ.φ q).1 a) 0 := by
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
    have hx : HasFDerivAt (Morse.sliceParam σ) (fderiv ℝ (Morse.sliceParam σ) z₀) (z₀ + (0:ℝ) • a) := by
      rw [zero_smul, add_zero]
      exact ((Morse.contDiffAt_sliceParam σ hz₀mem).differentiableAt (by simp)).hasFDerivAt
    exact hx.comp_hasDerivAt 0 hd

/-- Every velocity lies in the project tangent space. -/
theorem mem_of_velocity (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (q : N) {v : V}
    (hv : ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V, ContDiffOn ℝ ∞ γ (Set.Ioo (-ε) ε) ∧
      Set.MapsTo γ (Set.Ioo (-ε) ε) N ∧ γ 0 = q ∧ HasDerivAt γ v 0) :
    v ∈ Morse.tangentSubspace hN q := by
  obtain ⟨ε, hε, γ, -, hγN, hγ0, hγv⟩ := hv
  obtain ⟨σ, hσ⟩ := hN q.1 q.2
  rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ]
  -- `φ` is differentiable at `q`
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
  -- near `0`, `γ = x ∘ c`
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


/-- The project tangent space is the blind one (span of the velocities). -/
theorem tangentSubspace_eq (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    (q : ↑N) : Morse.tangentSubspace hN q = tangentSpace N (q : V) := by
  apply le_antisymm
  · obtain ⟨σ, hσ⟩ := hN q.1 q.2
    rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ]
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span (exists_curve σ hσ a)
  · exact Submodule.span_le.2 fun v hv => mem_of_velocity hN q hv

theorem starProjection_congr {K₁ K₂ : Submodule ℝ V} [K₁.HasOrthogonalProjection]
    [K₂.HasOrthogonalProjection] (h : K₁ = K₂) : K₁.starProjection = K₂.starProjection := by
  subst h; rfl

section Deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two derivatives of `f` within `N` at `q` agree on `T_qN` (compose with a slice
parametrization, which maps a neighbourhood into `N`). -/
theorem eq_of_hasFDerivWithinAt (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    {q : ↑N} {f : V → E} {f₁ f₂ : V →L[ℝ] E} (h₁ : HasFDerivWithinAt f f₁ N q)
    (h₂ : HasFDerivWithinAt f f₂ N q) {v : V} (hv : v ∈ Morse.tangentSubspace hN q) :
    f₁ v = f₂ v := by
  obtain ⟨σ, hσ⟩ := hN q.1 q.2
  rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ] at hv
  obtain ⟨a, rfl⟩ := hv
  have hz := Morse.toChart_apply_mem_target σ hσ
  have hx : HasFDerivAt (Morse.sliceParam σ) (fderiv ℝ (Morse.sliceParam σ) (σ.φ q).1)
      (σ.φ q).1 :=
    ((Morse.contDiffAt_sliceParam σ hz).differentiableAt (by simp)).hasFDerivAt
  have hmaps : ∀ᶠ z in 𝓝 (σ.φ q).1, Morse.sliceParam σ z ∈ N :=
    Filter.mem_of_superset ((Morse.isOpen_toChart_target σ).mem_nhds hz)
      fun z hz => Morse.sliceParam_mem σ hz
  have hq : (q : V) = Morse.sliceParam σ (σ.φ q).1 := (Morse.sliceParam_toChart σ hσ).symm
  have e₁ := h₁.comp_hasFDerivAt_of_eq _ hx hmaps hq
  have e₂ := h₂.comp_hasFDerivAt_of_eq _ hx hmaps hq
  exact DFunLike.congr_fun (e₁.unique e₂) a

/-- **The derivative within `N` is `dN` on tangent vectors**: if `f : V → E` restricts to
`F : N → E`, then `fderivWithin f N q v = dN F q v` for `v ∈ T_qN` (both are `0` when `F` is
not differentiable at `q`). -/
theorem fderivWithin_eq_dN (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    {F : ↑N → E} {f : V → E} (hfF : ∀ x : ↑N, f x = F x) {q : ↑N} {v : V}
    (hv : v ∈ Morse.tangentSubspace hN q) :
    fderivWithin ℝ f N q v = Morse.dN hN F q v := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  by_cases hF : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) F q
  · obtain ⟨G, hG, hFG⟩ := Morse.exists_differentiableAt_rep hN hF
    rw [Morse.dN_eq_fderiv hN hG hFG hv]
    have hev : f =ᶠ[𝓝[N] (q : V)] G := by
      have := (eventually_nhds_subtype_iff N q (fun y => ∀ h : y ∈ N, F ⟨y, h⟩ = G y)).1
        (hFG.mono fun x hx _ => hx)
      filter_upwards [this, self_mem_nhdsWithin] with y hy hyN
      rw [hfF ⟨y, hyN⟩]
      exact hy hyN
    have h1 : HasFDerivWithinAt f (fderiv ℝ G q) N q :=
      hG.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq hev
        (by rw [hfF q]; exact hFG.self_of_nhds)
    exact eq_of_hasFDerivWithinAt hN h1.differentiableWithinAt.hasFDerivWithinAt h1 hv
  · have h0 : Morse.dN hN F q = 0 := by
      ext w
      rw [Morse.dN_apply, mfderiv_zero_of_not_mdifferentiableAt hF]
      rfl
    have hnd : ¬ DifferentiableWithinAt ℝ f N q := by
      intro hd
      apply hF
      have hFf : F = f ∘ Subtype.val := funext fun x => (hfF x).symm
      have hval : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : ↑N → V) q :=
        hN.contMDiff_val.mdifferentiableAt (by simp)
      rw [hFf, ← mdifferentiableWithinAt_univ]
      exact (mdifferentiableWithinAt_iff_differentiableWithinAt.2 hd).comp q
        hval.mdifferentiableWithinAt (fun x _ => x.2)
    rw [fderivWithin_zero_of_not_differentiableWithinAt hnd, h0]

end Deriv

/-- A slice submanifold through some point has a finite-dimensional model `Z` (`Z` embeds in `V`
by the derivative of a slice parametrization). -/
theorem finiteDimensional_of_mem [FiniteDimensional ℝ V]
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (q : ↑N) :
    FiniteDimensional ℝ Z := by
  obtain ⟨σ, hσ⟩ := hN q.1 q.2
  exact Module.Finite.of_injective
    ((fderiv ℝ (Morse.sliceParam σ) (σ.φ q).1 : Z →L[ℝ] V) : Z →ₗ[ℝ] V)
    (Morse.injective_fderiv_sliceParam σ (Morse.toChart_apply_mem_target σ hσ))

/-- The blind `P_p` is the project's `P_p` at points of `N`. -/
theorem proj_eq [FiniteDimensional ℝ V]
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (x : ↑N) :
    proj N x = Morse.tanProj hN x :=
  (starProjection_congr (tangentSubspace_eq hN x)).symm

/-- The derivative within `N` of the blind `p ↦ P_p` is the project's `D_v = dN P q v`. -/
theorem fderivWithin_proj [FiniteDimensional ℝ V]
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (q : ↑N) {v : V}
    (hv : v ∈ Morse.tangentSubspace hN q) :
    fderivWithin ℝ (fun p => proj N p) N q v = Morse.dN hN (Morse.tanProj hN) q v :=
  fderivWithin_eq_dN hN (fun x => proj_eq hN x) hv

/-- The blind Gauss-equation curvature, paired with a fourth vector:
`⟪R(X, Y)Z, U⟫ = ⟪b(X, Z), b(Y, U)⟫ − ⟪b(Y, Z), b(X, U)⟫`. -/
theorem inner_gaussCurv [FiniteDimensional ℝ V] (K : Submodule ℝ V) (b : V →L[ℝ] V →L[ℝ] V)
    (X Y Z' U : K) :
    ⟪(gaussCurv K b X Y Z' : V), (U : V)⟫ = ⟪b X Z', b Y U⟫ - ⟪b Y Z', b X U⟫ := by
  rw [← Submodule.coe_inner]
  change ⟪LinearMap.adjoint _ _ - LinearMap.adjoint _ _, U⟫ = _
  rw [inner_sub_left, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
  rfl

/-- The blind second fundamental form is the project's on tangent vectors. -/
theorem II_apply [FiniteDimensional ℝ V]
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (q : ↑N) {a c : V}
    (ha : a ∈ Morse.tangentSubspace hN q) (hc : c ∈ Morse.tangentSubspace hN q) :
    II N q a c = Morse.secondFundForm hN q a c := by
  have := finiteDimensional_of_mem hN q
  change (1 - proj N q) (fderivWithin ℝ (fun p => proj N p) N q a c) = _
  rw [fderivWithin_proj hN q ha, sub_apply, one_apply_eq_self, proj_eq hN q]
  change Morse.secondFundForm hN q a c - Morse.tanProj hN q (Morse.secondFundForm hN q a c) = _
  rw [Morse.tanProj_secondFundForm hN ha hc, sub_zero]

/-- On the project's tangent space, the Gauss-equation curvature is `Morse.curvTensor`. -/
theorem curv_eq [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z]
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (q : ↑N) :
    Morse.curvTensor hN q = gaussCurv (Morse.tangentSubspace hN q) (II N q) := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => LinearMap.ext fun z => ?_
  refine ext_inner_right ℝ fun u => ?_
  rw [Submodule.coe_inner, Submodule.coe_inner, Morse.coe_curvTensor_apply, Morse.inner_curvOp,
    inner_gaussCurv]
  rw [II_apply hN q x.2 z.2, II_apply hN q y.2 u.2, II_apply hN q y.2 z.2, II_apply hN q x.2 u.2,
    real_inner_comm (Morse.secondFundForm hN q x u)]

/-- The blind Ricci form is the project's. -/
theorem ricci_eq [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z]
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (q : ↑N)
    (U : tangentSpace N (q : V)) (hU : (U : V) ∈ Morse.tangentSubspace hN q) :
    ricci N q U U = Morse.ricci hN q ⟨U, hU⟩ ⟨U, hU⟩ := by
  have key : ∀ (K : Submodule ℝ V) (hK : K = Morse.tangentSubspace hN q) (U : K),
      LinearMap.trace ℝ K ((gaussCurv K (II N q) U).flip U) =
        Morse.ricci hN q ⟨U, hK ▸ U.2⟩ ⟨U, hK ▸ U.2⟩ := by
    intro K hK U
    subst hK
    rw [Morse.ricci, curv_eq hN q]
  exact key _ (tangentSubspace_eq hN q).symm U

/-- **Agreement**, outright (for every `r`). -/
theorem agree [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z]
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (r : ℝ) :
    Morse.RicciLowerBound hN r ↔ T hN r := by
  constructor
  · intro h q hq U hU1
    have hU : (U : V) ∈ Morse.tangentSubspace hN ⟨q, hq⟩ := by
      rw [tangentSubspace_eq]; exact U.2
    rw [ricci_eq hN ⟨q, hq⟩ U hU]
    exact h ⟨q, hq⟩ ⟨U, hU⟩ hU1
  · intro h q U hU1
    have hU' : (U : V) ∈ tangentSpace N (q : V) := by rw [← tangentSubspace_eq hN q]; exact U.2
    have := h q q.2 ⟨U, hU'⟩ hU1
    rwa [ricci_eq hN q ⟨U, hU'⟩ U.2] at this

end RoundTrip.L2.Morse_RicciLowerBound
