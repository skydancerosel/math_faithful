import Morse
import RoundTrip.Check
import RoundTrip.Blind.V11_8
import RoundTrip.Bridge
import RoundTrip.EnergyC2

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V11_8

/-- The project's statement (universes instantiated at `0`): for a slice submanifold `N ⊆ V` with
the induced metric and `⟨R(A,B)A,B⟩ ≤ 0` (`Morse.NonposCurvature`): every geodesic
`γ ∈ Ω(N; p, q)` has index `0` and nullity `0` for the formula-defined Hessian
`Morse.energyHessian` (`formIndex`, `hessNullity`); `E_**` is positive definite (`E_**(X, X) > 0`
for `X ∈ TΩ_γ` not identically `0` on `[0,1]`); and `exp_p` is non-critical (injective
`d(exp_p)_v`) on its whole domain. No completeness. -/
def A : Prop :=
  type_of% @Morse.formIndex_eq_zero_of_nonpos.{0,0,0} ∧
    type_of% @Morse.energyHessian_pos_of_nonpos.{0,0,0} ∧
    type_of% @Morse.injective_dExpAt_of_nonpos.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.formIndex_eq_zero_of_nonpos, @Morse.energyHessian_pos_of_nonpos,
    @Morse.injective_dExpAt_of_nonpos⟩

/-! Neither `A → B` nor `B → A` is proved: B quantifies over abstract connected Hausdorff
`ℝⁿ`-manifolds with an arbitrary smooth metric and an arbitrary Levi-Civita connection, A only
over slice submanifolds `N ⊆ V` with the induced metric (see `V11_8.json`). Below: the embedded
special case `B_emb` (B for `M = ↥N`, `cov = Bridge.conn`) and its comparison with A. -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

theorem prj_incl (x : Bridge.Sub hN) : Morse.prj hN (incl hN x) = P hN x :=
  Morse.prj_of_mem hN x.2

theorem isIntv_Icc : RoundTrip.BridgePrelude.IsIntv (Icc (0 : ℝ) 1) :=
  ⟨ordConnected_Icc, uniqueDiffOn_Icc zero_lt_one⟩

/-- On the interior, `derivWithin [0,1]` of a function smooth on `[0, 1]` is `deriv`, near `t`. -/
theorem derivWithin_eventuallyEq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} (hF : ContDiffOn ℝ ∞ F (Icc 0 1)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    derivWithin F (Icc 0 1) =ᶠ[𝓝 t] deriv F := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
  exact ((hF.contDiffAt (Icc_mem_nhds hx.1 hx.2)).differentiableAt (by simp)).hasDerivAt
    |>.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one x (Ioo_subset_Icc_self hx))

/-- Project side: for a project Jacobi field, the Jacobi equation read with derivatives within
`[0, 1]` holds on all of `[0, 1]` (it is stated on `(0, 1)`; continuity). -/
theorem jacobi_Icc {c X : ℝ → V} (hc : Morse.IsSmoothCurveIn hN c)
    (hX : Morse.IsJacobiField hN c X) :
    ∀ t ∈ Icc (0 : ℝ) 1, Morse.covAlong hN c (Morse.covAlong hN c X) t +
      Morse.curvR hN (c t) (Morse.velAlong c t) (X t) (Morse.velAlong c t) = 0 := by
  have hu := uniqueDiffOn_Icc (zero_lt_one' ℝ)
  have hcov : ContDiffOn ℝ ∞ (Morse.covAlong hN c X) (Icc 0 1) :=
    hc.contDiffOn_prj.clm_apply (hX.contDiffOn.derivWithin hu (by simp))
  have hf : ContinuousOn (fun t => Morse.covAlong hN c (Morse.covAlong hN c X) t +
      Morse.curvR hN (c t) (Morse.velAlong c t) (X t) (Morse.velAlong c t)) (Icc 0 1) := by
    have h1 : ContinuousOn (Morse.covAlong hN c (Morse.covAlong hN c X)) (Icc 0 1) :=
      hc.contDiffOn_prj.continuousOn.clm_apply
        (hcov.derivWithin hu (m := 0) (by simp)).continuousOn
    have h2 : ContinuousOn (fun t => Morse.curvAlong hN c t (X t)) (Icc 0 1) :=
      hc.contDiffOn_curvAlong.continuousOn.clm_apply hX.contDiffOn.continuousOn
    refine h1.add (h2.congr fun t ht => ?_)
    show _ = Morse.curvAlong hN c t (X t)
    rw [Morse.curvAlong_apply (hc.mem t ht), hX.tangent t ht]
  refine EqOn.of_subset_closure (g := fun _ => (0 : V)) ?_ hf continuousOn_const
    Ioo_subset_Icc_self (by rw [closure_Ioo zero_ne_one])
  intro t ht
  have e1 : Morse.covAlong hN c X =ᶠ[𝓝 t] Morse.covD hN c X := by
    filter_upwards [derivWithin_eventuallyEq hX.contDiffOn ht] with x hx
    rw [Morse.covAlong, Morse.covD, hx]
  have e2 : Morse.covAlong hN c (Morse.covAlong hN c X) t =
      Morse.covD hN c (Morse.covD hN c X) t := by
    rw [Morse.covAlong, Morse.covD, (derivWithin_eventuallyEq hcov ht).eq_of_nhds, e1.deriv_eq]
  have := hX.eq t ht
  rw [Morse.jacobiExpr, ← hc.velAlong_eq ht, ← e2] at this
  exact this

/-- **Dictionary, blind ⇒ project**: a blind Jacobi field of the induced connection along `γ` on
`[0, 1]` is, read in `V`, a project Jacobi field along `incl ∘ γ`. -/
theorem isJacobiField_of_isJacobi {γ : ℝ → Bridge.Sub hN} {J : FA n γ}
    (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) (hJ : IsJacobi (conn (hN := hN)) γ (Icc 0 1) J) :
    Morse.IsJacobiField hN (incl hN ∘ γ) (ambA γ J) := by
  obtain ⟨J', J'', h1, h2, h3⟩ := hJ
  have hγ' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Icc 0 1) := hγ
  obtain ⟨h1s, h1e⟩ := (hasCovDeriv_iff' isIntv_Icc hγ').1 h1
  obtain ⟨h2s, h2e⟩ := (hasCovDeriv_iff' isIntv_Icc hγ').1 h2
  have hX := (isSmoothAlong_iff.1 h1s).2
  have hX' := (isSmoothAlong_iff.1 h2s).2
  have hu := uniqueDiffOn_Icc (zero_lt_one' ℝ)
  refine ⟨hX, fun t _ => ?_, fun t ht => ?_⟩
  · show Morse.prj hN (incl hN (γ t)) (D hN (γ t) (J t)) = D hN (γ t) (J t)
    rw [prj_incl]
    exact P_D _ _
  · have htI := Ioo_subset_Icc_self ht
    have e1 : Morse.covD hN (incl hN ∘ γ) (ambA γ J) =ᶠ[𝓝 t] ambA γ J' := by
      filter_upwards [derivWithin_eventuallyEq hX ht, Ioo_mem_nhds ht.1 ht.2] with x hx hx'
      rw [Morse.covD, ← hx, h1e x (Ioo_subset_Icc_self hx')]
      show Morse.prj hN (incl hN (γ x)) _ = _
      rw [prj_incl]
    have e2 : Morse.covD hN (incl hN ∘ γ) (Morse.covD hN (incl hN ∘ γ) (ambA γ J)) t =
        ambA γ J'' t := by
      rw [Morse.covD, e1.deriv_eq, ← (derivWithin_eventuallyEq hX' ht).eq_of_nhds, h2e t htI]
      show Morse.prj hN (incl hN (γ t)) _ = _
      rw [prj_incl]
    obtain ⟨r, hr, hr0⟩ := h3 t htI
    have hr' := (isCurvVal_iff (γ t) _ _ _ r).1 hr
    have hvel : D hN (γ t) (vel (n := n) γ (Icc 0 1) t) = deriv (incl hN ∘ γ) t := by
      have h := D_vel hγ' hu htI
      exact h.trans (derivWithin_eventuallyEq (isSmoothCurve_iff.1 hγ') ht).eq_of_nhds
    rw [hvel] at hr'
    rw [Morse.jacobiExpr, e2]
    show D hN (γ t) (J'' t) + Morse.curvR hN (incl hN (γ t)) _ (D hN (γ t) (J t)) _ = 0
    rw [← hr']
    exact (map_add (D hN (γ t)) (J'' t) r).symm.trans
      ((congrArg (D hN (γ t)) hr0).trans (map_zero _))

/-- **Dictionary, project ⇒ blind**: a field along `γ` whose ambient image is a project Jacobi
field along `incl ∘ γ` is a blind Jacobi field of the induced connection on `[0, 1]`. -/
theorem isJacobi_of_isJacobiField {γ : ℝ → Bridge.Sub hN} {J : FA n γ}
    (hγ : IsSmoothCurve (n := n) γ (Icc 0 1))
    (hX : Morse.IsJacobiField hN (incl hN ∘ γ) (ambA γ J)) :
    IsJacobi (conn (hN := hN)) γ (Icc 0 1) J := by
  have hγ' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Icc 0 1) := hγ
  have hc : Morse.IsSmoothCurveIn hN (incl hN ∘ γ) :=
    ⟨isSmoothCurve_iff.1 hγ', fun t _ => (γ t).2⟩
  have hu := uniqueDiffOn_Icc (zero_lt_one' ℝ)
  have hamb : ∀ U : FA n γ, ambA γ (covA γ (Icc 0 1) U) =
      Morse.covAlong hN (incl hN ∘ γ) (ambA γ U) := fun U => funext fun t => by
    refine (D_covA γ (Icc 0 1) U t).trans ?_
    show _ = Morse.prj hN (incl hN (γ t)) _
    rw [prj_incl]
  have hcov : ContDiffOn ℝ ∞ (ambA γ (covA γ (Icc 0 1) J)) (Icc 0 1) := by
    rw [hamb]
    exact hc.contDiffOn_prj.clm_apply (hX.contDiffOn.derivWithin hu (by simp))
  have hJs : RoundTrip.BridgePrelude.IsSmoothAlong γ (Icc 0 1) J :=
    isSmoothAlong_iff.2 ⟨hγ', hX.contDiffOn⟩
  have hJ's : RoundTrip.BridgePrelude.IsSmoothAlong γ (Icc 0 1) (covA γ (Icc 0 1) J) :=
    isSmoothAlong_iff.2 ⟨hγ', hcov⟩
  refine ⟨covA γ (Icc 0 1) J, covA γ (Icc 0 1) (covA γ (Icc 0 1) J),
    (hasCovDeriv_iff isIntv_Icc hγ').2 ⟨hJs, fun _ _ => rfl⟩,
    (hasCovDeriv_iff isIntv_Icc hγ').2 ⟨hJ's, fun _ _ => rfl⟩,
    fun t ht => ⟨-(covA γ (Icc 0 1) (covA γ (Icc 0 1) J) t), ?_, add_neg_cancel _⟩⟩
  refine (isCurvVal_iff (γ t) _ _ _ _).2 ?_
  have hvel : D hN (γ t) (vel (n := n) γ (Icc 0 1) t) = Morse.velAlong (incl hN ∘ γ) t :=
    D_vel hγ' hu ht
  have h1 : D hN (γ t) (covA γ (Icc 0 1) (covA γ (Icc 0 1) J) t) =
      Morse.covAlong hN (incl hN ∘ γ) (Morse.covAlong hN (incl hN ∘ γ) (ambA γ J)) t := by
    have := congrFun (hamb (covA γ (Icc 0 1) J)) t
    rw [hamb J] at this
    exact this
  rw [hvel]
  refine (map_neg (D hN (γ t)) (covA γ (Icc 0 1) (covA γ (Icc 0 1) J) t)).trans ?_
  refine (congrArg Neg.neg h1).trans ?_
  exact neg_eq_of_add_eq_zero_left ((add_comm _ _).trans (jacobi_Icc hc hX t ht))

/-- **Dictionary: conjugate parameters.** For `a, b ∈ [0, 1]`, blind conjugacy along `γ` for the
induced connection is the project's `Morse.IsConjugate` along `incl ∘ γ`. -/
theorem isConj_iff {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    IsConj (conn (hN := hN)) γ a b ↔ Morse.IsConjugate hN (incl hN ∘ γ) a b := by
  constructor
  · rintro ⟨hab, J, ⟨hJ, hJo⟩, hne, hJa, hJb⟩
    obtain ⟨t, ht⟩ := Function.ne_iff.1 hne
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      by_contra h
      exact ht (hJo t h)
    refine ⟨ha, hb, hab, ambA γ J, isJacobiField_of_isJacobi hγ hJ, ?_, ?_, t, htI, ?_⟩
    · show D hN (γ a) (J a) = 0
      rw [hJa]
      exact map_zero _
    · show D hN (γ b) (J b) = 0
      rw [hJb]
      exact map_zero _
    · intro h
      exact ht (D_injective (γ t) (h.trans (map_zero _).symm))
  · rintro ⟨-, -, hab, X, hX, hXa, hXb, t, ht, hXt⟩
    classical
    let J : FA n γ := fun s => if s ∈ Icc (0 : ℝ) 1 then L hN (γ s) (X s) else 0
    have hJX : EqOn (ambA γ J) X (Icc 0 1) := fun s hs => by
      show D hN (γ s) (if s ∈ Icc (0 : ℝ) 1 then L hN (γ s) (X s) else 0) = X s
      rw [if_pos hs]
      exact D_L ((Morse.prj_eq_self_iff hN (γ s).2).1 (hX.tangent s hs))
    refine ⟨hab, J, ⟨isJacobi_of_isJacobiField hγ (hX.congr fun s hs => (hJX hs).symm),
      fun s hs => by
        show (if s ∈ Icc (0 : ℝ) 1 then L hN (γ s) (X s) else 0) = 0
        rw [if_neg hs]⟩, fun h => hXt ?_, ?_, ?_⟩
    · rw [← hJX ht]
      show D hN (γ t) (J t) = 0
      rw [show J t = 0 from congrFun h t]
      exact map_zero _
    · show (if a ∈ Icc (0 : ℝ) 1 then L hN (γ a) (X a) else 0) = 0
      rw [if_pos ha, hXa, map_zero]
    · show (if b ∈ Icc (0 : ℝ) 1 then L hN (γ b) (X b) else 0) = 0
      rw [if_pos hb, hXb, map_zero]

/-- A smooth curve in `N` on `[0, 1]` which is a geodesic on `(0, 1)` lifts to a blind geodesic of
the induced connection on the closed interval `[0, 1]` (endpoint condition by continuity). -/
theorem isGeodesic_lift {γ : ℝ → V} (hc : Morse.IsSmoothCurveIn hN γ)
    (hg : Morse.IsGeodesicOn hN γ (Ioo 0 1)) (q : Bridge.Sub hN) :
    IsGeodesic (conn (hN := hN)) (lift γ q) (Icc 0 1) ∧
      EqOn (incl hN ∘ lift γ q) γ (Icc 0 1) := by
  have hu := uniqueDiffOn_Icc (zero_lt_one' ℝ)
  have heq : EqOn (incl hN ∘ lift γ q) γ (Icc 0 1) := fun t ht => incl_lift q (hc.mem t ht)
  refine ⟨?_, heq⟩
  have h : RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hN)) (lift γ q) (Icc 0 1) := by
    refine isGeodesic_iff.2 ⟨isIntv_Icc, hc.contDiffOn.congr heq, fun t ht => ?_⟩
    have hd1 : EqOn (derivWithin (incl hN ∘ lift γ q) (Icc 0 1)) (derivWithin γ (Icc 0 1))
        (Icc 0 1) := fun s hs => derivWithin_congr heq (heq hs)
    rw [derivWithin_congr hd1 (hd1 ht)]
    have hP : P hN (lift γ q t) = Morse.prj hN (γ t) := by
      rw [← prj_incl]
      exact congrArg (Morse.prj hN) (heq ht)
    rw [hP]
    -- the normal condition, extended from `(0, 1)` to `[0, 1]` by continuity
    have hf : ContinuousOn (fun s => Morse.prj hN (γ s)
        (derivWithin (derivWithin γ (Icc 0 1)) (Icc 0 1) s)) (Icc 0 1) :=
      hc.contDiffOn_prj.continuousOn.clm_apply
        ((hc.contDiffOn_velAlong.derivWithin hu (m := 0) (by simp)).continuousOn)
    refine EqOn.of_subset_closure (g := fun _ => (0 : V)) (fun s hs => ?_) hf continuousOn_const
      Ioo_subset_Icc_self (by rw [closure_Ioo zero_ne_one]) ht
    show Morse.prj hN (γ s) (derivWithin (derivWithin γ (Icc 0 1)) (Icc 0 1) s) = 0
    have hv : ContDiffOn ℝ ∞ (derivWithin γ (Icc 0 1)) (Icc 0 1) := hc.contDiffOn_velAlong
    rw [(derivWithin_eventuallyEq hv hs).eq_of_nhds,
      (derivWithin_eventuallyEq hc.contDiffOn hs).deriv_eq,
      Morse.prj_of_mem hN (hc.mem s (Ioo_subset_Icc_self hs))]
    exact (Morse.tanProj_eq_zero_iff hN).2 (hg.normal s hs)
  exact h

theorem isConjugate_congr {γ γ' : ℝ → V} (heq : EqOn γ γ' (Icc 0 1)) {a b : ℝ}
    (h : Morse.IsConjugate hN γ a b) : Morse.IsConjugate hN γ' a b := by
  obtain ⟨ha, hb, hab, J, hJ, hJa, hJb, t, ht, hJt⟩ := h
  exact ⟨ha, hb, hab, J, hJ.congr_curve heq, hJa, hJb, t, ht, hJt⟩

end Emb

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

theorem riemDist_eq_ofReal_rho (hpre : IsPreconnected N) (p q : Bridge.Sub hN) :
    Morse.riemDist (N := N) (incl hN p) (incl hN q) = ENNReal.ofReal (rho (n := n) p q) := by
  have e : rho (n := n) p q = RoundTrip.BridgePrelude.rho (n := n) p q := rfl
  rw [e, rho_eq]
  exact (ENNReal.ofReal_toReal (Morse.riemDist_ne_top hN hpre p.2 q.2)).symm

theorem rho_nonneg (p q : Bridge.Sub hN) : 0 ≤ rho (n := n) p q := by
  have e : rho (n := n) p q = RoundTrip.BridgePrelude.rho (n := n) p q := rfl
  rw [e, rho_eq]
  exact ENNReal.toReal_nonneg

theorem rho_lt_iff (hpre : IsPreconnected N) (p q : Bridge.Sub hN) {ε : ℝ} (hε : 0 < ε) :
    rho (n := n) p q < ε ↔ Morse.riemDist (N := N) (incl hN p) (incl hN q) < ENNReal.ofReal ε := by
  rw [riemDist_eq_ofReal_rho hpre, ENNReal.ofReal_lt_ofReal_iff hε]

theorem metricComplete_iff (hpre : IsPreconnected N) :
    MetricComplete n (Bridge.Sub hN) ↔ Morse.IsRiemComplete N := by
  constructor
  · intro h x hx hcau
    let x' : ℕ → Bridge.Sub hN := fun k => ⟨x k, hx k⟩
    obtain ⟨p, hp⟩ := h x' fun ε hε => by
      obtain ⟨n₀, hn₀⟩ := hcau ε hε
      exact ⟨n₀, fun m hm k hk => (rho_lt_iff hpre _ _ hε).2 (hn₀ m hm k hk)⟩
    refine ⟨incl hN p, p.2, ?_⟩
    have ht : Tendsto (fun k => rho (n := n) (x' k) p) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨n₀, hn₀⟩ := hp ε hε
      refine ⟨n₀, fun m hm => ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (rho_nonneg _ _)]
      exact hn₀ m hm
    have := ENNReal.tendsto_ofReal ht
    rw [ENNReal.ofReal_zero] at this
    refine this.congr fun k => ?_
    exact (riemDist_eq_ofReal_rho hpre (x' k) p).symm
  · intro h x hcau
    obtain ⟨y, hy, hlim⟩ := h (fun k => incl hN (x k)) (fun k => (x k).2) fun ε hε => by
      obtain ⟨n₀, hn₀⟩ := hcau ε hε
      exact ⟨n₀, fun m hm k hk => (rho_lt_iff hpre _ _ hε).1 (hn₀ m hm k hk)⟩
    refine ⟨⟨y, hy⟩, fun ε hε => ?_⟩
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
      (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε)))
    exact ⟨n₀, fun m hm => (rho_lt_iff hpre _ _ hε).2 (hn₀ m hm)⟩

theorem isPreconnected_of [ConnectedSpace (Bridge.Sub hN)] : IsPreconnected N :=
  isPreconnected_iff_preconnectedSpace.2 (inferInstance : PreconnectedSpace (Bridge.Sub hN))

/-- Milnor's completeness of `(↥N, ρ)` gives the project's geodesic completeness (Hopf–Rinow). -/
theorem complete_of_metricComplete [ConnectedSpace (Bridge.Sub hN)]
    (h : MetricComplete n (Bridge.Sub hN)) : Morse.IsGeodesicallyComplete hN :=
  Morse.isGeodesicallyComplete_of_isRiemComplete
    ((metricComplete_iff (isPreconnected_of (hN := hN))).1 h)

/-- Conversely (Hopf–Rinow). -/
theorem metricComplete_of_complete [ConnectedSpace (Bridge.Sub hN)]
    (h : Morse.IsGeodesicallyComplete hN) : MetricComplete n (Bridge.Sub hN) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty (Bridge.Sub hN))
  refine (metricComplete_iff (isPreconnected_of (hN := hN))).2 ?_
  exact ((Morse.hopf_rinow (hN := hN) (isPreconnected_of (hN := hN)) ⟨incl hN x, x.2⟩).out 0 1).2 h

theorem mem_expDom (hc : Morse.IsGeodesicallyComplete hN) (q : Bridge.Sub hN) (w : Rn n) :
    (incl hN q, D hN q w) ∈ Morse.expDom hN := hc q (D hN q w) (D_mem q w)

/-- The blind `exp` of the induced connection is the project's `exp` (complete `N`). -/
theorem incl_expMap (hc : Morse.IsGeodesicallyComplete hN) (q : Bridge.Sub hN) (w : Rn n) :
    incl hN (expMap (conn (hN := hN)) q w) = Morse.exp hN (incl hN q) (D hN q w) :=
  expMap_eq (mem_expDom hc q w)

/-- `D_q : ℝⁿ → T_qN`, with values in the tangent subspace. -/
noncomputable def Dt (q : Bridge.Sub hN) : Rn n →L[ℝ] Morse.tangentSubspace hN q :=
  (D hN q).codRestrict _ (D_mem q)

theorem coe_Dt (q : Bridge.Sub hN) (w : Rn n) : ((Dt q w : Morse.tangentSubspace hN q) : V) =
    D hN q w := rfl

theorem Dt_injective (q : Bridge.Sub hN) : Injective (Dt (hN := hN) q) := fun a b h =>
  D_injective q (congrArg Subtype.val h)

theorem Dt_L (q : Bridge.Sub hN) (v : Morse.tangentSubspace hN q) : Dt q (L hN q v) = v :=
  Subtype.ext (D_L v.2)

theorem Dt_surjective (q : Bridge.Sub hN) : Surjective (Dt (hN := hN) q) := fun v =>
  ⟨L hN q v, Dt_L q v⟩

/-- Precomposition with the bijection `Dt q` does not change injectivity. -/
theorem injective_comp_Dt_iff {X : Type*} (q : Bridge.Sub hN)
    (g : Morse.tangentSubspace hN q → X) : Injective (g ∘ Dt q) ↔ Injective g := by
  constructor
  · intro h x y hxy
    obtain ⟨a, rfl⟩ := Dt_surjective q x
    obtain ⟨b, rfl⟩ := Dt_surjective q y
    exact congrArg _ (h hxy)
  · intro h
    exact h.comp (Dt_injective q)

/-- A map from a normed space into `N` is smooth (into the manifold `N`) iff it is smooth in `V`. -/
theorem contMDiffAt_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {x : E} :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f x ↔ ContDiffAt ℝ ∞ (incl hN ∘ f) x := by
  constructor
  · intro h
    exact contMDiffAt_iff_contDiffAt.1 ((contMDiff_incl (f x)).comp x h)
  · intro h
    have hcont : ContinuousAt f x :=
      (Topology.IsInducing.subtypeVal.continuousAt_iff (f := f)).2 h.continuousAt
    rw [contMDiffAt_iff_target]
    refine ⟨hcont, ?_⟩
    set σ := Morse.sliceAt hN (f x)
    have hφ : ContDiffAt ℝ ∞ (fun y => (σ.φ y).1) (incl hN (f x)) :=
      contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt
        (σ.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (f x))))
    have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) = (fun y => (σ.φ y).1) ∘ (incl hN ∘ f) := rfl
    rw [e]
    exact contMDiffAt_iff_contDiffAt.2 (hφ.comp x h)

theorem contMDiff_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f ↔ ContDiff ℝ ∞ (incl hN ∘ f) := by
  rw [contDiff_iff_contDiffAt]
  exact forall_congr' fun _ => contMDiffAt_map_iff

/-- The differential of a map into `N`, read in `V`. -/
theorem D_mfderiv_map {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x)
    (v : E) :
    D hN (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x v) = fderiv ℝ (incl hN ∘ f) x v := by
  have hi : MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (incl hN) (f x) :=
    (contMDiff_incl (f x)).mdifferentiableAt (by simp)
  have h := (hi.hasMFDerivAt.comp x hf.hasMFDerivAt).mfderiv
  rw [mfderiv_eq_fderiv] at h
  rw [h]
  rfl

/-- `f` is critical at `x` (non-injective differential into `N`) iff `incl ∘ f` has a
non-injective derivative in `V`. -/
theorem injective_mfderiv_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x) :
    Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x) ↔ Injective (fderiv ℝ (incl hN ∘ f) x) := by
  constructor
  · intro h a b hab
    rw [← D_mfderiv_map hf, ← D_mfderiv_map hf] at hab
    exact h (D_injective _ hab)
  · intro h a b hab
    apply h
    have e1 := D_mfderiv_map hf a
    have e2 := D_mfderiv_map hf b
    rw [hab] at e1
    exact e1.symm.trans e2

/-- The exponential map `w ↦ exp_q(D_q w)` on `ℝⁿ` is `exp_q ∘ Dt q`. -/
theorem incl_comp_expMap (hc : Morse.IsGeodesicallyComplete hN) (q : Bridge.Sub hN) :
    incl hN ∘ (fun w : Rn n => expMap (conn (hN := hN)) q w) =
      (fun y : Morse.tangentSubspace hN q => Morse.exp hN (incl hN q) y) ∘ Dt q :=
  funext fun w => incl_expMap hc q w

end Emb

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- **Dictionary: Milnor's curvature hypothesis.** For the induced connection, the blind
`⟨R(A,B)A,B⟩ ≤ 0` is the project's `Morse.NonposCurvature`. -/
theorem nonPosCurv_iff : NonPosCurv n (conn (hN := hN)) ↔ Morse.NonposCurvature hN := by
  constructor
  · intro h q A hA B hB
    let p : Bridge.Sub hN := q
    have hR : Morse.curvOp hN q A B A ∈ Morse.tangentSubspace hN q := Morse.curvOp_mem hN hA hB hA
    have hcv : RoundTrip.V8_13.IsCurvVal (conn (hN := hN)) p (L hN p A) (L hN p B) (L hN p A)
        (L hN p (Morse.curvOp hN q A B A)) := by
      refine (isCurvVal_iff p _ _ _ _).2 ?_
      rw [D_L hR, D_L hA, D_L hB]
      exact (Morse.curvR_of_mem hN q.2 A B A).symm
    have := h p _ _ _ hcv
    change ⟪D hN p (L hN p (Morse.curvOp hN q A B A)), D hN p (L hN p B)⟫ ≤ 0 at this
    rw [D_L hR, D_L hB] at this
    exact this
  · intro h p x y r hr
    have hr' := (isCurvVal_iff p x y x r).1 hr
    change ⟪D hN p r, D hN p y⟫ ≤ 0
    rw [hr']
    show ⟪Morse.curvR hN (incl hN p) _ _ _, _⟫ ≤ 0
    have hp : incl hN p ∈ N := p.2
    rw [Morse.curvR_of_mem hN hp]
    exact h ⟨incl hN p, hp⟩ _ (D_mem p x) _ (D_mem p y)

end Emb

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- **Dictionary: geodesics from `p` to `q`, blind ⇒ project.** -/
theorem unbroken_of_geodPQ {p q : Bridge.Sub hN} {γ : ℝ → Bridge.Sub hN}
    (h : IsGeodPQ n (conn (hN := hN)) p q γ) :
    incl hN ∘ γ ∈ Morse.pathSpace N (incl hN p) (incl hN q) ∧
      Morse.IsUnbrokenGeodesic hN (incl hN ∘ γ) := by
  obtain ⟨hγ, hγ0, hγ1⟩ := h
  have hγ' : RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hN)) γ (Icc 0 1) := hγ
  have hcd := (isGeodesic_iff.1 hγ').2.1
  refine ⟨⟨Morse.IsPiecewiseSmooth.of_contDiffOn hcd zero_le_one subset_rfl,
    fun t _ => (γ t).2, ?_, ?_⟩, hcd, isGeodesicOn_Ioo hγ'⟩
  · show incl hN (γ 0) = incl hN p
    rw [hγ0]
  · show incl hN (γ 1) = incl hN q
    rw [hγ1]

/-- **Dictionary: geodesics from `p` to `q`, project ⇒ blind** (the lift `Bridge.lift`). -/
theorem geodPQ_of_unbroken {p q : Bridge.Sub hN} {γ : ℝ → V}
    (hγ : γ ∈ Morse.pathSpace N (incl hN p) (incl hN q)) (hg : Morse.IsUnbrokenGeodesic hN γ) :
    IsGeodPQ n (conn (hN := hN)) p q (lift γ p) ∧ EqOn (incl hN ∘ lift γ p) γ (Icc 0 1) := by
  obtain ⟨hgeo, heqc⟩ := isGeodesic_lift (hg.isSmoothCurveIn hN hγ) hg.2 p
  refine ⟨⟨hgeo, Subtype.ext ?_, Subtype.ext ?_⟩, heqc⟩
  · exact (heqc ⟨le_rfl, zero_le_one⟩).trans hγ.2.2.1
  · exact (heqc ⟨zero_le_one, le_rfl⟩).trans hγ.2.2.2

end Emb

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- The dictionary for Theorem 18.1 on a complete `↥N`: blind conjugacy along `γ_v` and blind
criticality of `exp_p` at `v` are the project's conjugacy along `t ↦ exp_p(t D_p v)` and
non-injectivity of `d(exp_p)_{D_p v}`. -/
theorem conj_crit_iff (hc : Morse.IsGeodesicallyComplete hN) (p : Bridge.Sub hN)
    (v : Rn n) :
    (IsConj (conn (hN := hN)) (fun t : ℝ => expMap (conn (hN := hN)) p (t • v)) 0 1 ↔
      Morse.IsConjugate hN (fun t => Morse.exp hN (incl hN p) (t • ((Dt p v : _) : V))) 0 1) ∧
    (IsCritMap n (fun w : Rn n => expMap (conn (hN := hN)) p w) v ↔
      ¬ Injective (Morse.dExpAt hN p (Dt p v))) := by
  set f := fun w : Rn n => expMap (conn (hN := hN)) p w with hf
  set E := fun y : Morse.tangentSubspace hN p => Morse.exp hN (incl hN p) y with hE
  have hEs : ContDiff ℝ ∞ E := by
    have h := Morse.contDiffOn_expAt (hN := hN) p
    rw [Morse.expDomAt_eq_univ hc p] at h
    exact contDiffOn_univ.1 h
  have hfE : incl hN ∘ f = E ∘ Dt p := incl_comp_expMap hc p
  have hfs : ContDiff ℝ ∞ (incl hN ∘ f) := by rw [hfE]; exact hEs.comp (Dt p).contDiff
  have hfm : ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) ∞ f := contMDiff_map_iff.2 hfs
  have hγ : incl hN ∘ (fun t : ℝ => expMap (conn (hN := hN)) p (t • v)) =
      fun t => Morse.exp hN (incl hN p) (t • ((Dt p v : _) : V)) := by
    funext t
    show incl hN (expMap (conn (hN := hN)) p (t • v)) = _
    rw [incl_expMap hc p (t • v)]
    show _ = Morse.exp hN (incl hN p) (t • D hN p v)
    exact congrArg _ ((D hN p).map_smul t v)
  have hvD : Dt p v ∈ Morse.expDomAt hN p := by rw [Morse.expDomAt_eq_univ hc p]; trivial
  have hγs : IsSmoothCurve (n := n) (fun t : ℝ => expMap (conn (hN := hN)) p (t • v)) (Icc 0 1) := by
    refine isSmoothCurve_iff.2 ?_
    rw [hγ]
    exact (Morse.isSmoothCurveIn_ray hvD).1
  refine ⟨?_, ?_⟩
  · rw [isConj_iff hγs ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩, hγ]
  · have hd : fderiv ℝ (incl hN ∘ f) v = (fderiv ℝ E (Dt p v)).comp (Dt p : Rn n →L[ℝ] _) := by
      rw [hfE, fderiv_comp v (hEs.differentiable (by simp) _) (Dt p).differentiableAt,
        (Dt p).fderiv]
    show ¬ Injective (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) f v) ↔ _
    rw [injective_mfderiv_iff (hfm.mdifferentiableAt (by simp)), hd, ContinuousLinearMap.coe_comp,
      injective_comp_Dt_iff]
    rfl

end Emb

/-! ### The Hessian dictionary: blind `IsHessT 1` ⇒ the project's `energyHessian` -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- `Bridge.contMDiffWithinAt_curve_iff` for maps from any normed space. -/
theorem contMDiffWithinAt_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} {x : E} :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s x ↔ ContDiffWithinAt ℝ ∞ (incl hN ∘ f) s x := by
  constructor
  · intro h
    exact contMDiffWithinAt_iff_contDiffWithinAt.1
      ((contMDiff_incl (f x)).comp_contMDiffWithinAt x h)
  · intro h
    have hcont : ContinuousWithinAt f s x :=
      (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := f)).2 h.continuousWithinAt
    rw [contMDiffWithinAt_iff_target]
    refine ⟨hcont, ?_⟩
    set σ := Morse.sliceAt hN (f x)
    have hφ : ContDiffAt ℝ ∞ (fun y => (σ.φ y).1) (incl hN (f x)) :=
      contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt
        (σ.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (f x))))
    have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) = (fun y => (σ.φ y).1) ∘ (incl hN ∘ f) := rfl
    rw [e]
    exact contMDiffWithinAt_iff_contDiffWithinAt.2 (hφ.comp_contDiffWithinAt x h)

theorem contMDiffOn_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s ↔ ContDiffOn ℝ ∞ (incl hN ∘ f) s :=
  forall₂_congr fun _ _ => contMDiffWithinAt_map_iff

/-- A map into `N` that is differentiable in `V` is differentiable into the manifold `N`. -/
theorem mdifferentiableAt_of_differentiableAt {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → Bridge.Sub hN} {x : E}
    (h : DifferentiableAt ℝ (incl hN ∘ f) x) : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x := by
  have hcont : ContinuousAt f x :=
    (Topology.IsInducing.subtypeVal.continuousAt_iff (f := f)).2 h.continuousAt
  rw [mdifferentiableAt_iff_target]
  refine ⟨hcont, ?_⟩
  set σ := Morse.sliceAt hN (f x)
  have hφ : DifferentiableAt ℝ (fun y => (σ.φ y).1) (incl hN (f x)) :=
    (Milnor.Problems.sliceChart_differentiableAt σ (Morse.mem_sliceAt_source hN (f x))).fst
  have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) = (fun y => (σ.φ y).1) ∘ (incl hN ∘ f) := rfl
  rw [e]
  exact mdifferentiableAt_iff_differentiableAt.2 (hφ.comp x h)

/-- An interval `[s, s']` of `[0, 1]` whose interior avoids the subdivision points lies in one
strip `[t i, t (i+1)]`. -/
theorem exists_strip {t : ℕ → ℝ} {k : ℕ} (h0 : t 0 = 0) (hk : t k = 1)
    (hlt : ∀ i < k, t i < t (i + 1)) {s s' : ℝ} (hs : 0 ≤ s) (hss' : s < s') (hs' : s' ≤ 1)
    (hB : ∀ x ∈ (Finset.range (k + 1)).image t, x ∉ Ioo s s') :
    ∃ i < k, t i ≤ s ∧ s' ≤ t (i + 1) := by
  classical
  have hP : ∃ j, s < t j ∧ j ≤ k := ⟨k, by rw [hk]; linarith, le_rfl⟩
  set m := Nat.find hP
  have hm : s < t m ∧ m ≤ k := Nat.find_spec hP
  have hm0 : m ≠ 0 := by
    intro h; have := hm.1; rw [h, h0] at this; linarith
  have hi : t (m - 1) ≤ s := by
    by_contra hcon
    exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
      ⟨lt_of_not_ge hcon, by omega⟩
  have hu : s' ≤ t m := by
    by_contra hcon
    exact hB (t m) (Finset.mem_image.2 ⟨m, Finset.mem_range.2 (by omega), rfl⟩)
      ⟨hm.1, lt_of_not_ge hcon⟩
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)
  exact ⟨m - 1, by omega, hi, by rw [hm1]; exact hu⟩

/-- **Dictionary: 2-parameter variations.** A blind variation `α : ℝ² → ℝ → ↥N` (strips
`U × [t i, t (i+1)]`) is, read in `V`, a project variation (`Morse.IsVariation`, parameters in
`ℝ²`, break points the `t i`). -/
theorem isVariation_of_isVarSubT {U : Set (Rn 2)} {α : Rn 2 → ℝ → Bridge.Sub hN} {k : ℕ}
    {t : ℕ → ℝ} (h : IsVarSubT (n := n) 1 U α k t) :
    Morse.IsVariation N U (fun u s => incl hN (α u s)) ((Finset.range (k + 1)).image t) := by
  obtain ⟨hU, h0U, ht0, htk, hlt, hpaths, hsm⟩ := h
  refine ⟨hU, h0U, fun u _ s _ => (α u s).2, fun u hu => ?_, fun u hu => ?_, ?_⟩
  · show incl hN (α u 0) = incl hN (α 0 0)
    rw [(hpaths u hu).2.1]
  · show incl hN (α u 1) = incl hN (α 0 1)
    rw [(hpaths u hu).2.2]
  · intro s s' hs hss' hs' hB
    obtain ⟨i, hi, his, his'⟩ := exists_strip ht0 htk hlt hs hss' hs' hB
    exact contMDiffOn_map_iff.1 ((hsm i hi).mono (prod_mono subset_rfl (Icc_subset_Icc his his')))

/-- **Dictionary: variation fields.** For `s ∈ [0, 1]`, the derivative of `r ↦ α(r w, s)` read
in `V` is `D` of the blind (manifold) derivative of `u ↦ α(u, s)` in the direction `w`. -/
theorem deriv_line_eq {U : Set (Rn 2)} {α : Rn 2 → ℝ → Bridge.Sub hN} {B : Finset ℝ}
    (hα : Morse.IsVariation N U (fun u s => incl hN (α u s)) B) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (w : Rn 2) :
    deriv (fun r : ℝ => incl hN (α (r • w) s)) 0 =
      D hN (α 0 s) (mfderiv 𝓘(ℝ, Rn 2) 𝓘(ℝ, Rn n) (fun u => α u s) 0 w) := by
  obtain ⟨a, b, ha, hab, hb, hsab, hB⟩ := Morse.exists_piece_mem B zero_lt_one hs
  have hF := hα.smooth a b ha hab hb hB
  have hd := RoundTrip.EnergyC2.hasFDerivAt_pderiv hα.isOpen
    (f := fun u s => incl hN (α u s)) (hF.differentiableOn (by simp)) hα.zero_mem hsab
  have hmd : MDifferentiableAt 𝓘(ℝ, Rn 2) 𝓘(ℝ, Rn n) (fun u => α u s) 0 :=
    mdifferentiableAt_of_differentiableAt hd.differentiableAt
  rw [D_mfderiv_map hmd w]
  have hl := RoundTrip.EnergyC2.hasDerivAt_line hd.differentiableAt w
  simp only [zero_add] at hl
  exact hl.deriv

/-- **Dictionary: Milnor's `E_**` on `↥N`.** If `r = E_**(W₁, W₂)` in the blind sense (`IsHessT`:
`r` is the mixed partial of the energy of some 2-parameter blind variation of the blind geodesic
`γ` with variation fields `W₁, W₂`), then `r` is the project's `energyHessian` of two elements of
`TΩ` which agree on `[0, 1]` with `W₁, W₂` read in `V`. (Theorem 13.1 `hasDerivAt_energyHessian`
and the C² regularity of `RoundTrip/EnergyC2.lean`.) -/
theorem isHessT_eq {γ : ℝ → Bridge.Sub hN} (hγ : IsGeodesic (conn (hN := hN)) γ (Icc 0 1))
    {W₁ W₂ : FA n γ} {r : ℝ} (h : IsHessT (n := n) 1 γ W₁ W₂ r) :
    ∃ X₁ X₂ : Morse.pathTangent hN (incl hN ∘ γ),
      (∀ s ∈ Icc (0 : ℝ) 1, (X₁ : ℝ → V) s = ambA γ W₁ s) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, (X₂ : ℝ → V) s = ambA γ W₂ s) ∧
      r = Morse.energyHessian hN
        (unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (conn (hN := hN)) (γ 0) (γ 1) γ)).1
        X₁ X₂ := by
  obtain ⟨hpath, hgeo⟩ :=
    unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (conn (hN := hN)) (γ 0) (γ 1) γ)
  obtain ⟨U, α, k, t, hvar, hα0, hW₁, hW₂, -, hr⟩ := h
  have hα' := isVariation_of_isVarSubT hvar
  set α' : Rn 2 → ℝ → V := fun u s => incl hN (α u s) with hα'def
  set e₀ : Rn 2 := EuclideanSpace.single 0 (1 : ℝ)
  set e₁ : Rn 2 := EuclideanSpace.single 1 (1 : ℝ)
  set φ : ℝ × ℝ → Rn 2 := fun u => u.1 • e₀ + u.2 • e₁ with hφdef
  have hφ : ContDiff ℝ ∞ φ :=
    (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)
  have hφ0 : φ 0 ∈ U := by
    have : φ 0 = 0 := by simp [hφdef]
    rw [this]; exact hvar.2.1
  have hα'' := hα'.comp hφ hφ0
  have hα''γ : ∀ s ∈ Icc (0 : ℝ) 1, α' (φ 0) s = (incl hN ∘ γ) s := by
    intro s _
    have : φ 0 = 0 := by simp [hφdef]
    rw [this, ← hα0]
    rfl
  have hHD := Morse.hasDerivAt_energyHessian hN hpath hgeo hα'' hα''γ
  refine ⟨⟨_, hα''.partial₁_mem hN hα''γ⟩, ⟨_, hα''.partial₂_mem hN hα''γ⟩, ?_, ?_, ?_⟩
  · intro s hs
    show deriv (fun u₁ => α' (φ (u₁, 0)) s) 0 = D hN (γ s) (W₁ s)
    have e : (fun u₁ : ℝ => α' (φ (u₁, 0)) s) = fun u₁ => incl hN (α (u₁ • e₀) s) := by
      funext u₁; simp [hφdef, hα'def]
    rw [e, deriv_line_eq hα' hs e₀]
    have hv : (W₁ s : Rn n) = (varField (n := n) α 0 s : Rn n) := eq_of_heq (hW₁ s)
    subst hα0
    rw [hv]
    rfl
  · intro s hs
    show deriv (fun u₂ => α' (φ (0, u₂)) s) 0 = D hN (γ s) (W₂ s)
    have e : (fun u₂ : ℝ => α' (φ (0, u₂)) s) = fun u₂ => incl hN (α (u₂ • e₁) s) := by
      funext u₂; simp [hφdef, hα'def]
    rw [e, deriv_line_eq hα' hs e₁]
    have hv : (W₂ s : Rn n) = (varField (n := n) α 1 s : Rn n) := eq_of_heq (hW₂ s)
    subst hα0
    rw [hv]
    rfl
  · rw [← hr, ← hHD.deriv]
    have hF : ContDiffOn ℝ 2 (fun v => Morse.energy (α' v) 0 1) U :=
      hα'.contDiffOn_energy.of_le ENat.LEInfty.out
    have hmix := RoundTrip.EnergyC2.fderiv_fderiv_apply_eq_deriv_deriv hvar.1 hF hvar.2.1 e₀ e₁
    have hEF : (fun v : Rn 2 => energy (n := n) (α v) 0 1) =
        fun v => Morse.energy (α' v) 0 1 := funext fun v => Bridge.energy_eq (α v) 0 1
    show fderiv ℝ (fun u : Rn 2 => fderiv ℝ (fun v : Rn 2 => energy (n := n) (α v) 0 1) u e₀) 0 e₁
      = _
    rw [hEF, hmix]
    simp only [zero_add, hφdef]

/-- **Under `E_** > 0` on `TΩ`, the blind index `λ(1)` of a geodesic of `↥N` is `0`.** -/
theorem lam_eq_zero {γ : ℝ → Bridge.Sub hN} (hγ : IsGeodesic (conn (hN := hN)) γ (Icc 0 1))
    (hpos : ∀ X : Morse.pathTangent hN (incl hN ∘ γ), (∃ s ∈ Icc (0 : ℝ) 1, (X : ℝ → V) s ≠ 0) →
      0 < Morse.energyHessian hN
        (unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (conn (hN := hN)) (γ 0) (γ 1) γ)).1 X X) :
    lam (n := n) 1 γ = 0 := by
  have hpath :=
    (unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (conn (hN := hN)) (γ 0) (γ 1) γ)).1
  have key : ∀ w ∈ TOm (n := n) 1 γ, w ≠ 0 → ¬ HessT (n := n) 1 γ w w < 0 := by
    intro w hw hne hlt
    obtain ⟨s, hs, hws⟩ : ∃ s ∈ Icc (0 : ℝ) 1, w s ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hne
      funext s
      by_cases hs : s ∈ Icc (0 : ℝ) 1
      · exact hcon s hs
      · exact hw.2.2.2 s hs
    unfold HessT at hlt
    split_ifs at hlt with h
    · obtain ⟨X₁, X₂, h1, h2, hr⟩ := isHessT_eq hγ h.choose_spec
      have hX₁ : ∃ s ∈ Icc (0 : ℝ) 1, (X₁ : ℝ → V) s ≠ 0 := by
        refine ⟨s, hs, fun h0 => hws (D_injective (γ s) ?_)⟩
        exact ((h1 s hs).symm.trans h0).trans (map_zero (D hN (γ s))).symm
      have hp := hpos X₁ hX₁
      have heq : Morse.energyHessian hN hpath X₁ X₂ = Morse.energyHessian hN hpath X₁ X₁ := by
        rw [Morse.energyHessian_apply, Morse.energyHessian_apply,
          Morse.secondVariation_congr hN (fun _ _ => rfl)
            (fun s hs => (h2 s hs).trans (h1 s hs).symm)]
      rw [hr, heq] at hlt
      linarith
    · exact lt_irrefl 0 hlt
  unfold lam bIndex
  refine nonpos_iff_eq_zero.1 (iSup₂_le fun S hS => ?_)
  obtain ⟨hSA, hSfin, hSneg⟩ := hS
  by_contra hne
  have hS0 : S ≠ ⊥ := by
    intro hbot
    apply hne
    rw [hbot, finrank_bot]
    rfl
  obtain ⟨w, hwS, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  exact key w (hSA hwS) hw0 (hSneg w hwS hw0)

end Emb

/-! ### The converse Hessian dictionary: every field of `TΩ` is realized by a blind variation -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- A subdivision `0 = t 0 < … < t k = 1` whose open pieces avoid a finite set (as in
`Bridge.isPW_lift`). -/
theorem exists_subdiv (B : Finset ℝ) : ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧ t k = 1 ∧
    (∀ i < k, t i < t (i + 1)) ∧
    ∀ i < k, 0 ≤ t i ∧ t (i + 1) ≤ 1 ∧ ∀ x ∈ B, x ∉ Ioo (t i) (t (i + 1)) := by
  classical
  have hlt : (0 : ℝ) < 1 := zero_lt_one
  set S : Finset ℝ := insert 0 (insert 1 (B.filter (· ∈ Ioo (0 : ℝ) 1)))
  have hS : ∀ x ∈ S, 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨-, hx⟩
    · exact ⟨le_rfl, hlt.le⟩
    · exact ⟨hlt.le, le_rfl⟩
    · exact ⟨hx.1.le, hx.2.le⟩
  have haS : (0 : ℝ) ∈ S := Finset.mem_insert_self _ _
  have hbS : (1 : ℝ) ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  set m := S.card
  have hm : 1 < m := Finset.one_lt_card.2 ⟨0, haS, 1, hbS, hlt.ne⟩
  set e := S.orderEmbOfFin rfl
  set t : ℕ → ℝ := fun j => if h : j < m then e ⟨j, h⟩ else 1
  have ht : ∀ j (h : j < m), t j = e ⟨j, h⟩ := fun j h => dif_pos h
  refine ⟨m - 1, t, ?_, ?_, ?_, ?_⟩
  · rw [ht 0 (by omega), Finset.orderEmbOfFin_zero rfl (by omega)]
    exact le_antisymm (Finset.min'_le _ _ haS) ((hS _ (Finset.min'_mem _ _)).1)
  · rw [ht (m - 1) (by omega), Finset.orderEmbOfFin_last rfl (by omega)]
    exact le_antisymm ((hS _ (Finset.max'_mem _ _)).2) (Finset.le_max' _ _ hbS)
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    refine ⟨(hS _ (Finset.orderEmbOfFin_mem _ _ _)).1, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2,
      fun x hx hxi => ?_⟩
    have hxS : x ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.2 ⟨hx, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).1.trans_lt hxi.1,
        hxi.2.trans_le (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2⟩))
    obtain ⟨j, rfl⟩ : x ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]; exact hxS
    have h1 := e.lt_iff_lt.1 hxi.1
    have h2 := e.lt_iff_lt.1 hxi.2
    rw [Fin.lt_def] at h1 h2
    simp only at h1 h2
    omega

/-- Gluing continuity over the pieces of a subdivision of `[0, 1]`. -/
theorem continuousOn_of_pieces {X : Type*} [TopologicalSpace X] {f : ℝ → X} {k : ℕ}
    {t : ℕ → ℝ} (h0 : t 0 = 0) (hk : t k = 1) (hlt : ∀ i < k, t i < t (i + 1))
    (hf : ∀ i < k, ContinuousOn f (Icc (t i) (t (i + 1)))) : ContinuousOn f (Icc 0 1) := by
  have key : ∀ j ≤ k, ContinuousOn f (Icc (t 0) (t j)) := by
    intro j
    induction j with
    | zero => intro _; rw [Icc_self]; exact continuousOn_singleton _ _
    | succ j ih =>
      intro hj
      rw [← Icc_union_Icc_eq_Icc (Bridge.le_of_strictSeq hlt (Nat.zero_le j) (by omega))
        (hlt j (by omega)).le]
      exact (ih (by omega)).union_of_isClosed (hf j (by omega)) isClosed_Icc isClosed_Icc
  rw [← h0, ← hk]
  exact key k le_rfl

/-- The blind field along `γ` of an ambient field `X` (zero off `[0, 1]`). -/
noncomputable def toW (γ : ℝ → Bridge.Sub hN) (X : ℝ → V) : FA n γ :=
  fun t => if t ∈ Icc (0 : ℝ) 1 then L hN (γ t) (X t) else 0

theorem ambA_toW {γ : ℝ → Bridge.Sub hN} {X : ℝ → V}
    (hX : X ∈ Morse.pathTangent hN (incl hN ∘ γ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ambA γ (toW γ X) t = X t := by
  show D hN (γ t) (if t ∈ Icc (0 : ℝ) 1 then L hN (γ t) (X t) else 0) = X t
  rw [if_pos ht]
  exact D_L ((Morse.prj_eq_self_iff hN (γ t).2).1 (hX.2.1 t ht))

theorem toW_of_notMem {γ : ℝ → Bridge.Sub hN} {X : ℝ → V} {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) :
    toW γ X t = 0 := if_neg ht

/-- `X ↦ toW γ X` on `TΩ`, as a linear map. -/
noncomputable def toWₗ (γ : ℝ → Bridge.Sub hN) :
    Morse.pathTangent hN (incl hN ∘ γ) →ₗ[ℝ] FA n γ where
  toFun X := toW γ X
  map_add' X Y := funext fun t => by
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · simp [toW, ht, map_add]
      rfl
    · simp [toW, ht]
  map_smul' c X := funext fun t => by
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · simp [toW, ht, map_smul]
      rfl
    · simp [toW, ht]

/-- **Dictionary: `TΩ`, project ⇒ blind.** -/
theorem toW_mem {γ : ℝ → Bridge.Sub hN} (hγs : IsSmoothCurve (n := n) γ (Icc 0 1)) {X : ℝ → V}
    (hX : X ∈ Morse.pathTangent hN (incl hN ∘ γ)) : toW γ X ∈ TOm (n := n) 1 γ := by
  have hX' := hX
  obtain ⟨⟨-, -, B, hB⟩, -, hX0, hX1⟩ := hX'
  obtain ⟨k, t, h0, hk, hlt, hgood⟩ := exists_subdiv B
  have hpiece : ∀ i < k, IsSmoothAlong γ (Icc (t i) (t (i + 1))) (toW γ X) := by
    intro i hi
    obtain ⟨hti, hti1, hBi⟩ := hgood i hi
    have hsub : Icc (t i) (t (i + 1)) ⊆ Icc 0 1 := Icc_subset_Icc hti hti1
    have hγs' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Icc (t i) (t (i + 1))) :=
      hγs.mono hsub
    exact isSmoothAlong_iff.2 ⟨hγs', (hB _ _ hti (hlt i hi) hti1 hBi).congr fun s hs =>
      ambA_toW hX (hsub hs)⟩
  refine ⟨⟨k, t, h0, hk, hlt, continuousOn_of_pieces h0 hk hlt fun i hi =>
    (hpiece i hi).continuousOn, hpiece⟩, ?_, ?_, fun s hs => toW_of_notMem hs⟩
  · show (if (0 : ℝ) ∈ Icc (0 : ℝ) 1 then L hN (γ 0) (X 0) else 0) = 0
    rw [if_pos ⟨le_rfl, zero_le_one⟩, hX0, map_zero]
  · show (if (1 : ℝ) ∈ Icc (0 : ℝ) 1 then L hN (γ 1) (X 1) else 0) = 0
    rw [if_pos ⟨zero_le_one, le_rfl⟩, hX1, map_zero]

/-- **Every pair of `TΩ` is realized by a blind 2-parameter variation** (Lemma 11.A of the project,
`Morse.exists_variation_two`, lifted to `↥N` and frozen off `[0, 1]`). -/
theorem exists_isHessT {γ : ℝ → Bridge.Sub hN} (hγ : IsGeodesic (conn (hN := hN)) γ (Icc 0 1))
    {X₁ X₂ : ℝ → V} (hX₁ : X₁ ∈ Morse.pathTangent hN (incl hN ∘ γ))
    (hX₂ : X₂ ∈ Morse.pathTangent hN (incl hN ∘ γ)) :
    ∃ r, IsHessT (n := n) 1 γ (toW γ X₁) (toW γ X₂) r := by
  classical
  obtain ⟨hpath, -⟩ :=
    unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (conn (hN := hN)) (γ 0) (γ 1) γ)
  obtain ⟨ε, hε, B, hα, h0, hd1, hd2⟩ := Morse.exists_variation_two hN hpath hX₁ hX₂
  set α' : ℝ × ℝ → ℝ → V := fun u t =>
    Morse.exp hN ((incl hN ∘ γ) t) (u.1 • X₁ t + u.2 • X₂ t) with hα'def
  set ψ : Rn 2 →L[ℝ] ℝ × ℝ := (EuclideanSpace.proj (0 : Fin 2)).prod (EuclideanSpace.proj 1)
    with hψdef
  have hψ0 : ψ 0 ∈ Metric.ball (0 : ℝ × ℝ) ε := by simp [hε]
  have hβ := hα.comp ψ.contDiff hψ0
  set U := ψ ⁻¹' Metric.ball (0 : ℝ × ℝ) ε with hUdef
  have h0U : (0 : Rn 2) ∈ U := hβ.zero_mem
  let αb : Rn 2 → ℝ → Bridge.Sub hN := fun u t =>
    if h : u ∈ U ∧ t ∈ Icc (0 : ℝ) 1 then ((⟨α' (ψ u) t, hβ.mem u h.1 t h.2⟩ : N) : Bridge.Sub hN)
    else γ t
  have hincl : ∀ u ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, incl hN (αb u t) = α' (ψ u) t := by
    intro u hu t ht
    have e : αb u t = ((⟨α' (ψ u) t, hβ.mem u hu t ht⟩ : N) : Bridge.Sub hN) := dif_pos ⟨hu, ht⟩
    rw [e]
    rfl
  have hout : ∀ u, ∀ t ∉ Icc (0 : ℝ) 1, αb u t = γ t := fun u t ht =>
    dif_neg (fun h : u ∈ U ∧ t ∈ Icc (0 : ℝ) 1 => ht h.2)
  have hα0 : αb 0 = γ := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · apply Subtype.ext
      show incl hN (αb 0 t) = incl hN (γ t)
      rw [hincl 0 h0U t ht]
      have := h0 t ht
      simpa [hα'def] using this
    · exact hout 0 t ht
  have hvarV : Morse.IsVariation N U (fun u s => incl hN (αb u s)) B := by
    refine ⟨hβ.isOpen, h0U, fun u _ t _ => (αb u t).2, fun u hu => ?_, fun u hu => ?_, ?_⟩
    · rw [hincl u hu 0 ⟨le_rfl, zero_le_one⟩, hincl 0 h0U 0 ⟨le_rfl, zero_le_one⟩]
      exact hβ.start u hu
    · rw [hincl u hu 1 ⟨zero_le_one, le_rfl⟩, hincl 0 h0U 1 ⟨zero_le_one, le_rfl⟩]
      exact hβ.finish u hu
    · intro s s' hs hss' hs' hB
      exact (hβ.smooth s s' hs hss' hs' hB).congr fun x hx =>
        hincl x.1 hx.1 x.2 ⟨hs.trans hx.2.1, hx.2.2.trans hs'⟩
  obtain ⟨k, t, ht0, htk, hlt, hgood⟩ := exists_subdiv B
  have hstrip : ∀ i < k, ContMDiffOn 𝓘(ℝ, Rn 2 × ℝ) 𝓘(ℝ, Rn n) ∞
      (fun x : Rn 2 × ℝ => αb x.1 x.2) (U ×ˢ Icc (t i) (t (i + 1))) := fun i hi => by
    obtain ⟨h1, h2, h3⟩ := hgood i hi
    exact contMDiffOn_map_iff.2 (hvarV.smooth _ _ h1 (hlt i hi) h2 h3)
  have hvarB : IsVarSubT (n := n) 1 U αb k t := by
    refine ⟨hβ.isOpen, h0U, ht0, htk, hlt, fun u hu => ⟨⟨k, t, ht0, htk, hlt, fun i hi => ?_⟩,
      ?_, ?_⟩, hstrip⟩
    · have hg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn 2 × ℝ) ∞ (fun s : ℝ => (u, s)) :=
        (contDiff_const.prodMk contDiff_id).contMDiff
      exact (hstrip i hi).comp hg.contMDiffOn fun s hs => mk_mem_prod hu hs
    · apply Subtype.ext
      show incl hN (αb u 0) = incl hN (αb 0 0)
      rw [hincl u hu 0 ⟨le_rfl, zero_le_one⟩, hincl 0 h0U 0 ⟨le_rfl, zero_le_one⟩]
      exact hβ.start u hu
    · apply Subtype.ext
      show incl hN (αb u 1) = incl hN (αb 0 1)
      rw [hincl u hu 1 ⟨zero_le_one, le_rfl⟩, hincl 0 h0U 1 ⟨zero_le_one, le_rfl⟩]
      exact hβ.finish u hu
  -- the variation fields
  have hfield : ∀ (i : Fin 2) (X : ℝ → V), X ∈ Morse.pathTangent hN (incl hN ∘ γ) →
      (∀ s ∈ Icc (0 : ℝ) 1,
        deriv (fun r : ℝ => α' (ψ (r • EuclideanSpace.single i (1 : ℝ))) s) 0 = X s) →
      ∀ s, HEq (toW γ X s) (varField (n := n) αb i s) := by
    intro i X hX hd s
    apply heq_of_eq
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · have h1 := deriv_line_eq hvarV hs (EuclideanSpace.single i (1 : ℝ))
      have hev : (fun r : ℝ => incl hN (αb (r • EuclideanSpace.single i (1 : ℝ)) s)) =ᶠ[𝓝 0]
          fun r : ℝ => α' (ψ (r • EuclideanSpace.single i (1 : ℝ))) s := by
        have hc : Continuous fun r : ℝ => r • EuclideanSpace.single i (1 : ℝ) :=
          continuous_id.smul continuous_const
        have hmem : ∀ᶠ r in 𝓝 (0 : ℝ), r • EuclideanSpace.single i (1 : ℝ) ∈ U :=
          hc.continuousAt.preimage_mem_nhds (by rw [zero_smul]; exact hβ.isOpen.mem_nhds h0U)
        filter_upwards [hmem] with r hr
        exact hincl _ hr s hs
      rw [hev.deriv_eq, hd s hs] at h1
      have e : αb 0 s = γ s := congrFun hα0 s
      rw [e] at h1
      apply D_injective (γ s)
      refine (ambA_toW hX hs).trans ?_
      exact h1
    · rw [toW_of_notMem hs]
      have hc : (fun u => αb u s) = fun _ => γ s := funext fun u => hout u s hs
      show (0 : Rn n) = mfderiv 𝓘(ℝ, Rn 2) 𝓘(ℝ, Rn n) (fun u => αb u s) 0 _
      rw [hc, mfderiv_const]
      rfl
  have hF2 : ContDiffOn ℝ 2 (fun v => Morse.energy ((fun u s => incl hN (αb u s)) v) 0 1) U :=
    hvarV.contDiffOn_energy.of_le ENat.LEInfty.out
  have hEF : (fun v : Rn 2 => energy (n := n) (αb v) 0 1) =
      fun v => Morse.energy ((fun u s => incl hN (αb u s)) v) 0 1 :=
    funext fun v => Bridge.energy_eq (αb v) 0 1
  refine ⟨_, U, αb, k, t, hvarB, hα0, hfield 0 X₁ hX₁ fun s hs => ?_, hfield 1 X₂ hX₂ fun s hs => ?_,
    ?_, rfl⟩
  · have e : (fun r : ℝ => α' (ψ (r • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) s) =
        fun u₁ : ℝ => Morse.exp hN ((incl hN ∘ γ) s) (u₁ • X₁ s + (0 : ℝ) • X₂ s) := by
      funext r; simp [hα'def, hψdef]
    rw [e]; exact hd1 s hs
  · have e : (fun r : ℝ => α' (ψ (r • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) s) =
        fun u₂ : ℝ => Morse.exp hN ((incl hN ∘ γ) s) ((0 : ℝ) • X₁ s + u₂ • X₂ s) := by
      funext r; simp [hα'def, hψdef]
    rw [e]; exact hd2 s hs
  · rw [hEF]
    exact RoundTrip.EnergyC2.differentiableAt_fderiv_apply hβ.isOpen hF2 h0U _

/-- **The blind `E_**` on `toW`-fields is the project's `energyHessian`.** -/
theorem hessT_toW {γ : ℝ → Bridge.Sub hN} (hγ : IsGeodesic (conn (hN := hN)) γ (Icc 0 1))
    {X : ℝ → V} (hX : X ∈ Morse.pathTangent hN (incl hN ∘ γ)) :
    HessT (n := n) 1 γ (toW γ X) (toW γ X) = Morse.energyHessian hN
      (unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (conn (hN := hN)) (γ 0) (γ 1) γ)).1
      ⟨X, hX⟩ ⟨X, hX⟩ := by
  have h := exists_isHessT hγ hX hX
  unfold HessT
  rw [dif_pos h]
  obtain ⟨X₁, X₂, h1, h2, hr⟩ := isHessT_eq hγ h.choose_spec
  rw [hr, Morse.energyHessian_apply, Morse.energyHessian_apply,
    Morse.secondVariation_congr hN (fun s hs => (h1 s hs).trans (ambA_toW hX hs))
      (fun s hs => (h2 s hs).trans (ambA_toW hX hs))]

/-- **The project's index is at most the blind index** `λ(1)` (on embedded manifolds). -/
theorem formIndex_le_lam {γ : ℝ → Bridge.Sub hN} (hγ : IsGeodesic (conn (hN := hN)) γ (Icc 0 1)) :
    Morse.formIndex (Morse.energyHessian hN
      (unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (conn (hN := hN)) (γ 0) (γ 1) γ)).1) ≤
      lam (n := n) 1 γ := by
  set hpath :=
    (unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (conn (hN := hN)) (γ 0) (γ 1) γ)).1
  have hγs : IsSmoothCurve (n := n) γ (Icc 0 1) := hγ.2.1
  refine Morse.formIndex_le fun S hS hneg => ?_
  set Φ := toWₗ (hN := hN) (n := n) γ
  have hinj : ∀ x ∈ S, Φ x = 0 → x = 0 := by
    intro x hx h0
    by_contra hne
    have hlt := hneg x hx hne
    have hx0 : ∀ s ∈ Icc (0 : ℝ) 1, (x : ℝ → V) s = ((0 : Morse.pathTangent hN (incl hN ∘ γ)) :
        ℝ → V) s := fun s hs => by
      rw [← ambA_toW x.2 hs]
      show D hN (γ s) (toW γ x s) = 0
      rw [show toW γ x s = 0 from congrFun h0 s]
      exact map_zero _
    have : Morse.energyHessian hN hpath x x = Morse.energyHessian hN hpath 0 0 := by
      rw [Morse.energyHessian_apply, Morse.energyHessian_apply,
        Morse.secondVariation_congr hN hx0 hx0]
    rw [this] at hlt
    simp at hlt
  have hfin := Morse.finrank_map_of_injOn Φ S hinj
  have hmem : ((S.map Φ : Submodule ℝ (FA n γ)) : Set (FA n γ)) ⊆ TOm (n := n) 1 γ := by
    rintro _ ⟨x, -, rfl⟩
    exact toW_mem hγs x.2
  have hneg' : IsNegDefSub (HessT (n := n) 1 γ) (S.map Φ) := by
    rintro _ ⟨x, hx, rfl⟩ hne
    have hx0 : x ≠ 0 := fun h => hne (by rw [h, map_zero])
    show HessT (n := n) 1 γ (toW γ x) (toW γ x) < 0
    rw [hessT_toW hγ x.2]
    exact hneg x hx hx0
  unfold lam bIndex
  rw [← hfin]
  exact le_iSup₂_of_le (f := fun (S' : Submodule ℝ (FA n γ)) (_ : (S' : Set (FA n γ)) ⊆
    TOm (n := n) 1 γ ∧ FiniteDimensional ℝ S' ∧ IsNegDefSub (HessT (n := n) 1 γ) S') =>
      (finrank ℝ S' : ℕ∞)) (S.map Φ) ⟨hmem, inferInstance, hneg'⟩ le_rfl

end Emb

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- `secondVariation` only depends on the curve on `[0, 1]`. -/
theorem secondVariation_congr_curve {γ γ' X₁ X₂ : ℝ → V} (h : ∀ t ∈ Icc (0 : ℝ) 1, γ t = γ' t) :
    Morse.secondVariation hN γ X₁ X₂ = Morse.secondVariation hN γ' X₁ X₂ := by
  have hev : ∀ t ∈ Ioo (0 : ℝ) 1, γ =ᶠ[𝓝 t] γ' := fun t ht => by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact h s (Ioo_subset_Icc_self hs)
  unfold Morse.secondVariation
  congr 1
  · congr 1
    exact finsum_mem_congr rfl fun t ht => by rw [h t (Ioo_subset_Icc_self ht)]
  · refine intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht => ?_
    have hcov : Morse.covD hN γ X₁ =ᶠ[𝓝 t] Morse.covD hN γ' X₁ := by
      filter_upwards [hev t ht] with s hs
      simp only [Morse.covD, hs]
    simp only [Morse.covD]
    rw [hcov.deriv_eq, h t (Ioo_subset_Icc_self ht), (hev t ht).deriv_eq]

/-- `formIndex` of `E_**` only depends on the curve on `[0, 1]` (one inequality). -/
theorem formIndex_le_of_eqOn {γ γ' : ℝ → V} {p q p' q' : V} (hγ : γ ∈ Morse.pathSpace N p q)
    (hγ' : γ' ∈ Morse.pathSpace N p' q') (h : ∀ t ∈ Icc (0 : ℝ) 1, γ t = γ' t) :
    Morse.formIndex (Morse.energyHessian hN hγ) ≤ Morse.formIndex (Morse.energyHessian hN hγ') := by
  let Lm : Morse.pathTangent hN γ →ₗ[ℝ] Morse.pathTangent hN γ' :=
    { toFun := fun x => ⟨x, Morse.mem_pathTangent_congr hN h x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Morse.formIndex_le_of_map Lm fun x y => ?_
  rw [Morse.energyHessian_apply, Morse.energyHessian_apply]
  exact congrArg (2 * ·) (secondVariation_congr_curve h).symm

end Emb

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric) with the induced Levi-Civita
connection `Bridge.conn` (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    NonPosCurv n (Bridge.conn (hN := hN)) →
      (∀ (p q : Bridge.Sub hN) (γ : ℝ → Bridge.Sub hN),
        IsGeodPQ n (Bridge.conn (hN := hN)) p q γ → lam (n := n) 1 γ = 0) ∧
      (MetricComplete n (Bridge.Sub hN) → ∀ (p : Bridge.Sub hN) (v : TangentSpace 𝓘(ℝ, Rn n) p),
        ¬ IsCritMap n (fun w : Rn n => expMap (Bridge.conn (hN := hN)) p w) v)

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds.** Index `0`: a negative definite subspace of the blind
`TΩ` for the blind `E_**` (`HessT`, a choice among values realized by 2-parameter variations)
would contain `w ≠ 0` whose realized value is the project's `E_**(X, X)` with `X = w` on `[0,1]`
(`Emb.isHessT_eq`, through the variation dictionary and `RoundTrip/EnergyC2.lean`), which A's
`energyHessian_pos_of_nonpos` makes positive (`Emb.lam_eq_zero`). Non-criticality: A's
`injective_dExpAt_of_nonpos` through `Emb.conj_crit_iff`. -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ hK
  have hK' := Emb.nonPosCurv_iff.1 hK
  refine ⟨fun p q γ hγ => ?_, fun hmc p v => ?_⟩
  · obtain ⟨hγg, -, -⟩ := hγ
    exact Emb.lam_eq_zero hγg fun X hX =>
      hA.2.1 hK' _ (Emb.unbroken_of_geodPQ ⟨hγg, rfl, rfl⟩).2 X hX
  · have hc := Emb.complete_of_metricComplete hmc
    have hvD : Emb.Dt p v ∈ Morse.expDomAt hN p := by rw [Morse.expDomAt_eq_univ hc p]; trivial
    exact fun h => (Emb.conj_crit_iff hc p v).2.1 h (hA.2.2 hK' hvD)

/-- The part of A that B covers on embedded manifolds (beyond the index, see the JSON): `exp_p`
is non-critical on all of `T_pN` for complete connected `N` (model `ℝⁿ`). -/
def A_cplt : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    Morse.IsGeodesicallyComplete hN → Morse.NonposCurvature hN →
      ∀ (p : N) (v : Morse.tangentSubspace hN p), Injective (Morse.dExpAt hN p v)

theorem A_to_A_cplt : A → A_cplt := fun hA _ _ _ _ _ _ _ _ _ _ hN _ hc hK p v =>
  hA.2.2 hK (Morse.expDomAt_eq_univ hc p ▸ mem_univ v)

/-- **B on embedded manifolds implies non-criticality of `exp_p`** (complete connected `N`). -/
theorem B_emb_to_A_cplt : B_emb → A_cplt := by
  intro hB V _ _ _ W _ _ _ n N hN _ hc hK p v
  let p' : Bridge.Sub hN := p
  have h := (hB V W n N hN (Emb.nonPosCurv_iff.2 hK)).2 (Emb.metricComplete_of_complete hc) p'
    (Bridge.L hN p' v)
  have h2 := (Emb.conj_crit_iff hc p' (Bridge.L hN p' v)).2
  rw [Emb.Dt_L] at h2
  by_contra hni
  exact h (h2.2 hni)

/-- The index half of A's `formIndex_eq_zero_of_nonpos` (model `ℝⁿ`, connected `↥N`): every
geodesic of `Ω(N; p, q)` has index `0` for the project's `energyHessian`. -/
def A_idx : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    Morse.NonposCurvature hN → ∀ {p q : V} {γ : ℝ → V} (hγ : γ ∈ Morse.pathSpace N p q),
      Morse.IsUnbrokenGeodesic hN γ → Morse.formIndex (Morse.energyHessian hN hγ) = 0

theorem A_to_A_idx : A → A_idx := fun hA _ _ _ _ _ _ _ _ _ _ _ _ hK _ _ _ hγ hg =>
  (hA.1 hK hγ hg).1

/-- **B on embedded manifolds implies index `0` for the project's `E_**`**: lift the geodesic to
`↥N`, where B gives blind index `0`, and the converse Hessian dictionary
(`Emb.formIndex_le_lam`: every negative definite subspace of `TΩ` for `energyHessian` maps to one
of the blind `TΩ` for `HessT`, each `TΩ` pair being realized by a blind variation lifted from
`Morse.exists_variation_two`) bounds the project's index by the blind one. -/
theorem B_emb_to_A_idx : B_emb → A_idx := by
  intro hB V _ _ _ W _ _ _ n N hN _ hK p q γ hγ hg
  have hp : γ 0 ∈ N := hγ.2.1 0 ⟨le_rfl, zero_le_one⟩
  have hq : γ 1 ∈ N := hγ.2.1 1 ⟨zero_le_one, le_rfl⟩
  let p' : Bridge.Sub hN := (⟨γ 0, hp⟩ : N)
  let q' : Bridge.Sub hN := (⟨γ 1, hq⟩ : N)
  have hγ' : γ ∈ Morse.pathSpace N (Bridge.incl hN p') (Bridge.incl hN q') :=
    ⟨hγ.1, hγ.2.1, rfl, rfl⟩
  obtain ⟨hpq, heq⟩ := Emb.geodPQ_of_unbroken (p := p') (q := q') hγ' hg
  have hlam := (hB V W n N hN (Emb.nonPosCurv_iff.2 hK)).1 p' q' _ hpq
  have h1 := Emb.formIndex_le_lam hpq.1
  rw [hlam] at h1
  have h2 := Emb.formIndex_le_of_eqOn (hN := hN) hγ
    (Emb.unbroken_of_geodPQ ⟨hpq.1, rfl, rfl⟩).1 fun t ht => (heq ht).symm
  exact nonpos_iff_eq_zero.1 (h2.trans h1)

#rt_check RoundTrip.V11_8.B_emb_to_A_idx [Morse.formIndex_eq_zero_of_nonpos,
  Morse.energyHessian_pos_of_nonpos, Morse.injective_dExpAt_of_nonpos]
#rt_overlap RoundTrip.V11_8.B_emb_to_A_idx [Morse.formIndex_eq_zero_of_nonpos,
  Morse.energyHessian_pos_of_nonpos, Morse.injective_dExpAt_of_nonpos]

#rt_check RoundTrip.V11_8.A_to_B_emb [Morse.formIndex_eq_zero_of_nonpos,
  Morse.energyHessian_pos_of_nonpos, Morse.injective_dExpAt_of_nonpos]
#rt_check RoundTrip.V11_8.B_emb_to_A_cplt [Morse.formIndex_eq_zero_of_nonpos,
  Morse.energyHessian_pos_of_nonpos, Morse.injective_dExpAt_of_nonpos]
#rt_overlap RoundTrip.V11_8.B_emb_to_A_cplt [Morse.formIndex_eq_zero_of_nonpos,
  Morse.energyHessian_pos_of_nonpos, Morse.injective_dExpAt_of_nonpos]
#rt_overlap RoundTrip.V11_8.A_to_B_emb [Morse.formIndex_eq_zero_of_nonpos,
  Morse.energyHessian_pos_of_nonpos, Morse.injective_dExpAt_of_nonpos]

end RoundTrip.V11_8
