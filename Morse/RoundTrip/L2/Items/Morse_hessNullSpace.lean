import Morse
import RoundTrip.L2.Blind.Morse_hessNullSpace
namespace RoundTrip.L2.Morse_hessNullSpace

open Set Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace

/-! The dictionary between the blind geometry (span of velocities, `P`, `II`, Gauss-equation `R`)
and the project's is the same as in the layer-2 check of `Morse.IsJacobiField`
(`RoundTrip/L2/Items/Morse_IsJacobiField.lean`); the Hessian part as in the check of
`Morse.energyHessian`. Both are repeated here. -/

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

/-! ### The Hessian: the blind formula is the project's `2 · secondVariation` -/

section Hessian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {N : Set V}

/-- **The blind `E_**` formula is twice the project's second variation** on `TΩ_γ`, for every
`γ ∈ Ω` (Proposition 13.A of the project, `Morse.secondVariation_eq_hessForm`, is the
integration by parts; the integrands agree a.e. by the dictionary). -/
theorem hessVal_eq (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ X Y : ℝ → V} {p q : V}
    (hγ : γ ∈ Morse.pathSpace N p q) (hX : X ∈ Morse.pathTangent hN γ)
    (hY : Y ∈ Morse.pathTangent hN γ) :
    hessVal N γ X Y = 2 * Morse.secondVariation hN γ X Y := by
  rw [Morse.secondVariation_eq_hessForm hN hγ hX hY, hessVal, Morse.hessForm]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ τ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), τ ≠ 1 :=
    (countable_singleton 1).ae_notMem _
  filter_upwards [hγ.1.ae_differentiableAt, hne] with τ hd h1 hτ
  have hτ' : τ ∈ Ioo (0 : ℝ) 1 := by
    rw [uIoc_of_le zero_le_one] at hτ
    exact ⟨hτ.1, lt_of_le_of_ne hτ.2 h1⟩
  have hτN : γ τ ∈ N := hγ.2.1 τ (Ioo_subset_Icc_self hτ')
  have hV : deriv γ τ ∈ Morse.tangentSubspace hN ⟨γ τ, hτN⟩ :=
    Morse.hasDerivAt_mem_tangentSubspace hN (hd hτ).hasDerivAt
      (eventually_of_mem (Ioo_mem_nhds hτ'.1 hτ'.2) fun x hx =>
        hγ.2.1 x (Ioo_subset_Icc_self hx))
  have hXt : X τ ∈ Morse.tangentSubspace hN ⟨γ τ, hτN⟩ :=
    (Morse.prj_eq_self_iff hN hτN).1 (hX.2.1 τ (Ioo_subset_Icc_self hτ'))
  simp only [Morse.covD, P_eq hN, R_eq hN hτN hV hXt hV]

omit [FiniteDimensional ℝ V] in
/-- `bilinOf f` is `B` when `f` is the bilinear form `B`. -/
theorem bilinOf_eq {M : Type*} [AddCommGroup M] [Module ℝ M] (f : M → M → ℝ)
    (B : LinearMap.BilinForm ℝ M) (h : ∀ x y, f x y = B x y) : bilinOf f = B := by
  have hb : (∀ x x' y, f (x + x') y = f x y + f x' y) ∧ (∀ (c : ℝ) x y, f (c • x) y = c • f x y) ∧
      (∀ x y y', f x (y + y') = f x y + f x y') ∧ (∀ (c : ℝ) x y, f x (c • y) = c • f x y) :=
    ⟨fun x x' y => by simp only [h, map_add, LinearMap.add_apply],
      fun c x y => by simp only [h, map_smul, LinearMap.smul_apply],
      fun x y y' => by simp only [h, map_add],
      fun c x y => by simp only [h, map_smul]⟩
  unfold bilinOf
  rw [dif_pos hb]
  ext x y
  simp [h]

/-- On `TΩ_γ`, `bilinOf` of the blind formula is the project's `energyHessian`. -/
theorem bilinOf_hessVal (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ : ℝ → V} {p q : V}
    (hγ : γ ∈ Morse.pathSpace N p q) :
    bilinOf (fun W₁ W₂ : Morse.pathTangent hN γ => hessVal N γ W₁ W₂) =
      Morse.energyHessian hN hγ :=
  bilinOf_eq _ _ fun W₁ W₂ => by rw [Morse.energyHessian_apply, hessVal_eq hN hγ W₁.2 W₂.2]

end Hessian

/-! ### The blind `TΩ_γ` and `E_**` are the project's -/

section TOm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {N : Set V}

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **The blind `TΩ_γ` is the project's `pathTangent`** (for every `γ`; continuity on `[0, 1]`
follows from smoothness on the pieces). -/
theorem TOm_eq (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (γ : ℝ → V) :
    TOm N γ = Morse.pathTangent hN γ := by
  ext X
  change (IsPWS X ∧ (∀ t ∈ Icc (0 : ℝ) 1, X t ∈ tan N (γ t)) ∧ X 0 = 0 ∧ X 1 = 0) ↔ _
  rw [Morse.mem_pathTangent]
  constructor
  · rintro ⟨⟨S, hS⟩, ht, h0, h1⟩
    exact ⟨⟨zero_le_one, Morse.continuousOn_of_piecewise fun s t hs hst ht' hB =>
      (hS s t hs hst ht' hB).continuousOn, S, hS⟩, fun t htI => (mem_tan_iff hN _ _).1 (ht t htI),
      h0, h1⟩
  · rintro ⟨⟨-, -, S, hS⟩, ht, h0, h1⟩
    exact ⟨⟨S, hS⟩, fun t htI => (mem_tan_iff hN _ _).2 (ht t htI), h0, h1⟩

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem mem_TOm_iff (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (γ X : ℝ → V) :
    X ∈ TOm N γ ↔ X ∈ Morse.pathTangent hN γ := by
  rw [TOm_eq hN γ]

/-- The identification `TΩ_γ (project) ≃ TΩ_γ (blind)`. -/
noncomputable def eTOm (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (γ : ℝ → V) :
    Morse.pathTangent hN γ ≃ₗ[ℝ] TOm N γ :=
  LinearEquiv.ofEq _ _ (TOm_eq hN γ).symm

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
@[simp] theorem coe_eTOm (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (γ : ℝ → V)
    (X : Morse.pathTangent hN γ) : ((eTOm hN γ X : TOm N γ) : ℝ → V) = X := rfl

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
@[simp] theorem coe_eTOm_symm (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (γ : ℝ → V)
    (X : TOm N γ) : (((eTOm hN γ).symm X : Morse.pathTangent hN γ) : ℝ → V) = X := rfl

/-- **The blind `E_**` is the project's**, transported along `TΩ_γ (blind) = TΩ_γ (project)`. -/
theorem Ess_eq (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ : ℝ → V} {p q : V}
    (hγ : γ ∈ Morse.pathSpace N p q) :
    Ess N γ = (Morse.energyHessian hN hγ).compl₁₂ ((eTOm hN γ).symm : TOm N γ →ₗ[ℝ] _)
      ((eTOm hN γ).symm : TOm N γ →ₗ[ℝ] _) :=
  bilinOf_eq _ _ fun X Y => by
    rw [LinearMap.compl₁₂_apply, Morse.energyHessian_apply, LinearEquiv.coe_coe,
      coe_eTOm_symm, coe_eTOm_symm,
      hessVal_eq hN hγ ((mem_TOm_iff hN γ X).1 X.2) ((mem_TOm_iff hN γ Y).1 Y.2)]

/-- The blind null space of `E_**`, as functions on `ℝ`, is the project's kernel (as functions). -/
theorem map_ker_Ess (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ : ℝ → V} {p q : V}
    (hγ : γ ∈ Morse.pathSpace N p q) :
    (LinearMap.ker (Ess N γ)).map (TOm N γ).subtype =
      (LinearMap.ker (Morse.energyHessian hN hγ)).map (Morse.pathTangent hN γ).subtype := by
  ext X
  simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.subtype_apply]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    refine ⟨(eTOm hN γ).symm Y, ?_, rfl⟩
    ext Y'
    have := congrArg (fun L => L (eTOm hN γ Y')) hY
    simpa [Ess_eq hN hγ] using this
  · rintro ⟨Y, hY, rfl⟩
    refine ⟨eTOm hN γ Y, ?_, rfl⟩
    ext Y'
    rw [Ess_eq hN hγ]
    simp [hY]

end TOm

section Main

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {N : Set V}

/-- **Agreement up to the values off `[0, 1]`** (for every `γ ∈ Ω`, the signature's hypothesis):
the project's null space is the blind one normalised by `X ↦ X ∘ projIcc` (`Morse.restrictIcc`).
The blind null space is the kernel of `E_**` itself, as a set of functions `ℝ → V`. -/
theorem agree_restrict (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ : ℝ → V} {p q : V}
    (hγ : γ ∈ Morse.pathSpace N p q) :
    Morse.hessNullSpace hN hγ = (T hN hγ).map (Morse.restrictIcc V) := by
  rw [Morse.hessNullSpace, T, map_ker_Ess hN hγ, Submodule.map_comp]

/-- The two agree on `[0, 1]`: restricted to `[0, 1]`, they are the same space of fields. -/
theorem agree_on_Icc (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ : ℝ → V} {p q : V}
    (hγ : γ ∈ Morse.pathSpace N p q) :
    (Morse.hessNullSpace hN hγ).map
        (LinearMap.funLeft ℝ V (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) =
      (T hN hγ).map (LinearMap.funLeft ℝ V (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) := by
  rw [agree_restrict hN hγ, ← Submodule.map_comp]
  congr 1
  ext X t
  simp [Morse.restrictIcc, LinearMap.funLeft, projIcc_of_mem _ t.2]

open Classical in
/-- **They differ as spaces of functions on `ℝ`** (as soon as `V ≠ 0`, for every `γ ∈ Ω`): the
blind null space contains every field of `TΩ_γ` vanishing on `[0, 1]`, e.g. `v` at `t = 2` and
`0` elsewhere, which is not of the project's normalised form `X ∘ projIcc` (whose value at `2` is
`X 1 = 0`). -/
theorem differ [Nontrivial V] (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ : ℝ → V}
    {p q : V} (hγ : γ ∈ Morse.pathSpace N p q) : Morse.hessNullSpace hN hγ ≠ T hN hγ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  set X : ℝ → V := fun t => if t = 2 then v else 0 with hXdef
  have hX : ∀ t, t < 2 → X t = 0 := fun t ht => by simp [X, ht.ne]
  have hXev : ∀ t, t < 2 → X =ᶠ[𝓝 t] 0 := fun t ht => by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact hX s hs
  have hXmem : X ∈ TOm N γ := by
    refine ⟨⟨∅, fun a b ha hab hb _ => (contDiffOn_const (c := (0 : V))).congr fun t ht =>
      hX t (by linarith [ht.2])⟩, fun t ht => ?_, hX 0 (by norm_num), hX 1 (by norm_num)⟩
    rw [hX t (by linarith [ht.2])]
    exact Submodule.zero_mem _
  have hval : ∀ Y : ℝ → V, hessVal N γ X Y = 0 := fun Y => by
    rw [hessVal]
    have : ∫ t in (0 : ℝ)..1, (⟪P N (γ t) (deriv X t), P N (γ t) (deriv Y t)⟫ -
        ⟪R N (γ t) (deriv γ t) (X t) (deriv γ t), Y t⟫) = ∫ _ in (0 : ℝ)..1, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le zero_le_one] at ht
      have ht2 : t < 2 := by linarith [ht.2]
      simp only [(hXev t ht2).deriv_eq, hX t ht2, map_zero, inner_zero_left, R,
        II, zero_apply, sub_zero]
      simp
    rw [this]
    simp
  have hker : (⟨X, hXmem⟩ : TOm N γ) ∈ LinearMap.ker (Ess N γ) := by
    rw [LinearMap.mem_ker]
    ext Y
    rw [Ess_eq hN hγ, LinearMap.compl₁₂_apply, Morse.energyHessian_apply, LinearEquiv.coe_coe,
      coe_eTOm_symm, coe_eTOm_symm, ← hessVal_eq hN hγ ((mem_TOm_iff hN γ _).1 hXmem)
      ((mem_TOm_iff hN γ _).1 Y.2), hval]
    rfl
  have hXT : X ∈ T hN hγ := ⟨⟨X, hXmem⟩, hker, rfl⟩
  intro h
  rw [← h] at hXT
  obtain ⟨Y, -, hY⟩ := hXT
  have h2 := congrFun hY 2
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, Morse.restrictIcc,
    LinearMap.coe_mk, AddHom.coe_mk] at h2
  rw [projIcc_of_right_le _ (by norm_num : (1 : ℝ) ≤ 2)] at h2
  have hY1 : (Y : ℝ → V) 1 = 0 := Y.2.2.2.2
  rw [hY1] at h2
  exact hv (by simpa [X] using h2.symm)

end Main

end RoundTrip.L2.Morse_hessNullSpace
