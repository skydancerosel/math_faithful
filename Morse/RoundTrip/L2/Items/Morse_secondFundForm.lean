import Morse
import RoundTrip.L2.Blind.Morse_secondFundForm

/-! Layer-2 check of `Morse.secondFundForm` (`II_q(v, w) = D_v w`, `D_v = dN P q v` the derivative
along `N` of `p ↦ P_p`, a bilinear map on all of `V`) against the blind textbook definition
(`(1 − P_q)(D_{P_q v} W)` for the tangent field `W(p) = P_p w`, derivative within `N`).

* `agree_of`: equal for tangent `v, w ∈ T_qN` (the textbook's domain): the two tangent spaces
  and projections agree, `fderivWithin (p ↦ P_p w) N q v = (dN P q v) w`, and `D_v w` is already
  normal for tangent `w`.
* `differ`: they differ for a normal second argument. The project extends `II` by the shape
  operator: `D_v ν` is tangent for `ν ⊥ T_qN` (used in `Morse.curvOp`,
  `R(x, y)z = II(y, II(x, z)) − II(x, II(y, z))`), whereas the blind value is the normal part of
  `D_{P v}(P_· ν)` (`= 0`). On the unit circle `S¹ ⊆ ℝ²` at `q = e₀`, with `v = e₁`:
  `⟪II(v, q), v⟫ = ⟪q, II(v, v)⟫ = −1`, while the blind value is normal, so its inner product
  with `v` is `0`. Harmless: outside the textbook's domain (and a deliberate convention). -/

namespace RoundTrip.L2.Morse_secondFundForm

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

/-- **Agreement on tangent vectors** (the textbook's domain). -/
theorem agree_of [FiniteDimensional ℝ V]
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (q : ↑N) {v w : V}
    (hv : v ∈ Morse.tangentSubspace hN q) (hw : w ∈ Morse.tangentSubspace hN q) :
    Morse.secondFundForm hN q v w = T hN q v w := by
  have := finiteDimensional_of_mem hN q
  have hd : fderivWithin ℝ (fun p => proj N p w) N q v = Morse.secondFundForm hN q v w := by
    rw [fderivWithin_eq_dN hN (F := fun x => Morse.tanProj hN x w)
      (fun x => by rw [proj_eq hN x]) hv]
    have h := Morse.dN_clm_comp hN (ContinuousLinearMap.apply ℝ V w)
      (Morse.mdifferentiableAt_tanProj hN q)
    exact DFunLike.congr_fun h v
  simp only [T]
  rw [proj_eq hN q, Morse.tanProj_eq_self hN hv, ← proj_eq hN q, hd, proj_eq hN q,
    Morse.tanProj_secondFundForm hN hv hw, sub_zero]

/-- **They differ for a normal second argument**: on the unit circle `S¹ ⊆ ℝ²` at `q = e₀`,
`II(e₁, q)` (project) is the tangent vector `−e₁`, the blind value is normal. -/
theorem differ : ∃ q : ↑(Milnor.Sphere.Sph 1), ∃ v w : EuclideanSpace ℝ (Fin 2),
    Morse.secondFundForm (Milnor.Sphere.sphSub 1) q v w ≠ T (Milnor.Sphere.sphSub 1) q v w := by
  set e₀ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  set e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1
  have h00 : ⟪e₀, e₀⟫ = 1 := by simp [e₀]
  have h01 : ⟪e₀, e₁⟫ = 0 := by
    simp [e₀, e₁, EuclideanSpace.inner_single_left]
  have h11 : ⟪e₁, e₁⟫ = 1 := by simp [e₁]
  have hq : e₀ ∈ Milnor.Sphere.Sph 1 := by
    rw [Set.mem_preimage, Set.mem_singleton_iff, Milnor.Sphere.sphG, h00, sub_self]
  set q : ↑(Milnor.Sphere.Sph 1) := ⟨e₀, hq⟩
  have hv : e₁ ∈ Morse.tangentSubspace (Milnor.Sphere.sphSub 1) q :=
    (Morse.mem_tangentSubspace_sph_iff q e₁).2 h01
  refine ⟨q, e₁, e₀, fun h => ?_⟩
  -- the project's value has inner product `−1` with `e₁`
  have h1 : ⟪Morse.secondFundForm (Milnor.Sphere.sphSub 1) q e₁ e₀, e₁⟫ = -1 := by
    rw [Morse.inner_secondFundForm_comm, Morse.secondFundForm_sph hv hv]
    change ⟪e₀, -⟪e₁, e₁⟫ • e₀⟫ = -1
    rw [real_inner_smul_right, h11, h00]
    ring
  -- the blind value is normal to the (blind) tangent space, which contains `e₁`
  have h2 : ⟪T (Milnor.Sphere.sphSub 1) q e₁ e₀, e₁⟫ = 0 := by
    have hK : e₁ ∈ tangentSpace (Milnor.Sphere.Sph 1) (q : EuclideanSpace ℝ (Fin 2)) := by
      rw [← tangentSubspace_eq (Milnor.Sphere.sphSub 1) q]
      exact hv
    exact Submodule.inner_left_of_mem_orthogonal hK (Submodule.sub_starProjection_mem_orthogonal _)
  rw [h] at h1
  rw [h1] at h2
  norm_num at h2

end RoundTrip.L2.Morse_secondFundForm
