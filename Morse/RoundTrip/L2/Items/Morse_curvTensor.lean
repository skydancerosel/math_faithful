import Morse
import RoundTrip.L2.Blind.Morse_curvTensor

/-! Layer-2 check of `Morse.curvTensor` (`R(x, y)z = II(y, II(x, z)) − II(x, II(y, z))` on
`T_qN`, the project's `II(v, ·) = D_v` extended to normal vectors by the shape operator) against
the blind textbook definition (Milnor's sign; the vector of `T_qN` determined by the Gauss
equation `⟨R(X, Y)Z, U⟩ = ⟨II(X, Z), II(Y, U)⟩ − ⟨II(Y, Z), II(X, U)⟩`, via `LinearMap.adjoint`,
with `II = (1 − P_q) ∘ dP_q` computed by `fderivWithin`).

Equal outright, for every slice submanifold and every `q` (`agree`): both are trilinear maps of
`T_qN` (the same subspace, `Morse.tangentSubspace`), so it suffices to compare inner products with
every `U ∈ T_qN`; the project side is `Morse.inner_curvOp` (the Gauss equation, from the
self-adjointness of `D_v`), the blind side is the defining property of the adjoint, and the two
second fundamental forms agree on tangent vectors (the derivative within `N` of `p ↦ P_p` is the
project's `dN P q` on `T_qN`; `D_v w` is normal for tangent `w`). -/

namespace RoundTrip.L2.Morse_curvTensor

open Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}

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
theorem II_apply [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z]
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (q : ↑N) {a c : V}
    (ha : a ∈ Morse.tangentSubspace hN q) (hc : c ∈ Morse.tangentSubspace hN q) :
    II hN q a c = Morse.secondFundForm hN q a c := by
  have hd : fderivWithin ℝ (fun p => (tan hN p).starProjection) N q a =
      Morse.dN hN (Morse.tanProj hN) q a := by
    refine fderivWithin_eq_dN hN (fun x => ?_) ha
    have h : tan hN x = Morse.tangentSubspace hN x := by simp [tan, x.2]
    exact starProjection_congr h
  change (1 - (Morse.tangentSubspace hN q).starProjection)
    (fderivWithin ℝ (fun p => (tan hN p).starProjection) N q a c) = _
  rw [hd, sub_apply, one_apply_eq_self]
  change Morse.secondFundForm hN q a c - Morse.tanProj hN q (Morse.secondFundForm hN q a c) = _
  rw [Morse.tanProj_secondFundForm hN ha hc, sub_zero]

/-- **Agreement**: the project's curvature tensor is the blind Gauss-equation one, outright. -/
theorem agree [FiniteDimensional ℝ V]
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) [FiniteDimensional ℝ Z]
    (q : ↑N) : Morse.curvTensor hN q = T hN q := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => LinearMap.ext fun z => ?_
  refine ext_inner_right ℝ fun u => ?_
  rw [Submodule.coe_inner, Submodule.coe_inner, Morse.coe_curvTensor_apply, Morse.inner_curvOp]
  change _ = ⟪(gaussCurv _ (II hN q) x y z : V), (u : V)⟫
  rw [inner_gaussCurv]
  rw [II_apply hN q x.2 z.2, II_apply hN q y.2 u.2, II_apply hN q y.2 z.2, II_apply hN q x.2 u.2,
    real_inner_comm (Morse.secondFundForm hN q x u)]

end RoundTrip.L2.Morse_curvTensor
