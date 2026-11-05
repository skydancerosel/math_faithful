import Morse
import RoundTrip.Check
import RoundTrip.Blind.V11_17
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V11_17

/-- The project's statement (universes instantiated at `0`; `Morse.expDiffeomorph` is
vocabulary): for a slice submanifold `N ⊆ V` with the induced metric: closed `N` is geodesically
complete; if `exp_p : T_pN → N` is a covering map and `N` is simply connected, `exp_p` is
injective; for complete connected `N`, `exp_p` is onto; and **Theorem 19.2**: if `N` is complete,
simply connected and `⟨R(A,B)A,B⟩ ≤ 0`, any two points are joined by a geodesic `γ ∈ Ω(N; p, q)`,
unique on `[0,1]` among unbroken geodesics of `Ω(N; p, q)`, and `N` is diffeomorphic to `ℝᵏ`,
`k = dim N` (Mathlib `Diffeomorph`, for the manifold structure of `N`). -/
def A : Prop :=
  type_of% @Morse.isGeodesicallyComplete_of_isClosed.{0,0,0} ∧
    type_of% @Morse.injective_expToN_of_simplyConnected.{0,0,0} ∧
    type_of% @Morse.surjective_expToN.{0,0,0} ∧
    type_of% @Morse.theorem_19_2.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.isGeodesicallyComplete_of_isClosed, @Morse.injective_expToN_of_simplyConnected,
    @Morse.surjective_expToN, @Morse.theorem_19_2⟩

/-! Neither `A → B` nor `B → A` is proved: B quantifies over abstract connected Hausdorff
`ℝⁿ`-manifolds with an arbitrary smooth metric and an arbitrary Levi-Civita connection, A only
over slice submanifolds `N ⊆ V` with the induced metric (see `V11_17.json`). Below: the embedded
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

/-- `ℝᵏ ≅ ℝⁿ` for `k = finrank ℝ ℝⁿ`. -/
noncomputable def eucl (n : ℕ) :
    Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ (Rn n)))) 𝓘(ℝ, Rn n)
      (EuclideanSpace ℝ (Fin (finrank ℝ (Rn n)))) (Rn n) ∞ :=
  let e : EuclideanSpace ℝ (Fin (finrank ℝ (Rn n))) ≃L[ℝ] Rn n :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_euclideanSpace_fin])
  { toEquiv := e.toEquiv
    contMDiff_toFun := e.contDiff.contMDiff
    contMDiff_invFun := e.symm.contDiff.contMDiff }

end Emb

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric) with the induced Levi-Civita
connection `Bridge.conn` (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    MetricComplete n (Bridge.Sub hN) → SimplyConnectedSpace (Bridge.Sub hN) →
    NonPosCurv n (Bridge.conn (hN := hN)) →
      (∀ p q : Bridge.Sub hN, ∃ γ, IsGeodPQ n (Bridge.conn (hN := hN)) p q γ ∧
        ∀ γ', IsGeodPQ n (Bridge.conn (hN := hN)) p q γ' → Set.EqOn γ γ' (Set.Icc 0 1)) ∧
      Nonempty (Diffeomorph 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (Bridge.Sub hN) (Rn n) ∞)

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- The part of A that B covers on embedded manifolds: Theorem 19.2 (A's `theorem_19_2`) for model
`ℝⁿ`. -/
def A_cplt : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
    Morse.IsGeodesicallyComplete hN → SimplyConnectedSpace N → Morse.NonposCurvature hN →
    (∀ p q : N, ∃ γ : ℝ → V, γ ∈ Morse.pathSpace N p q ∧ Morse.IsUnbrokenGeodesic hN γ ∧
      ∀ γ' ∈ Morse.pathSpace N p q, Morse.IsUnbrokenGeodesic hN γ' → EqOn γ' γ (Icc 0 1)) ∧
    (letI := hN.chartedSpace
     Nonempty (Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ (Rn n)))) 𝓘(ℝ, Rn n)
       (EuclideanSpace ℝ (Fin (finrank ℝ (Rn n)))) N ∞))

theorem A_to_A_cplt : A → A_cplt := fun hA _ _ _ _ _ _ _ _ _ _ _ hc hsc hK => hA.2.2.2 hc hsc hK

/-- **A implies B on embedded manifolds** (A's `theorem_19_2`, through the geodesic dictionary
`Emb.unbroken_of_geodPQ` / `Emb.geodPQ_of_unbroken`, the curvature dictionary
`Emb.nonPosCurv_iff`, Hopf–Rinow for completeness, and `ℝᵏ ≅ ℝⁿ`). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ hmc hsc hK
  have hc := Emb.complete_of_metricComplete hmc
  have hsc' : SimplyConnectedSpace N := hsc
  obtain ⟨h1, h2⟩ := hA.2.2.2 hc hsc' (Emb.nonPosCurv_iff.1 hK)
  refine ⟨fun p q => ?_, ?_⟩
  · obtain ⟨γ, hγ, hg, huniq⟩ := h1 p q
    obtain ⟨hpq, heq⟩ := Emb.geodPQ_of_unbroken (p := p) (q := q) hγ hg
    refine ⟨_, hpq, fun γ' hγ' t ht => Subtype.ext ?_⟩
    obtain ⟨hm', hg'⟩ := Emb.unbroken_of_geodPQ hγ'
    exact (heq ht).trans (huniq _ hm' hg' ht).symm
  · letI := hN.chartedSpace
    obtain ⟨D⟩ := h2
    exact ⟨D.symm.trans (Emb.eucl n)⟩

/-- **B on embedded manifolds implies Theorem 19.2 for model `ℝⁿ`.** -/
theorem B_emb_to_A_cplt : B_emb → A_cplt := by
  intro hB V _ _ _ W _ _ _ n N hN hc hsc hK
  have : ConnectedSpace (Bridge.Sub hN) := (inferInstance : ConnectedSpace N)
  obtain ⟨h1, h2⟩ := hB V W n N hN (Emb.metricComplete_of_complete hc) hsc
    (Emb.nonPosCurv_iff.2 hK)
  refine ⟨fun p q => ?_, ?_⟩
  · obtain ⟨γ, hγ, huniq⟩ := h1 p q
    obtain ⟨hm, hg⟩ := Emb.unbroken_of_geodPQ hγ
    refine ⟨_, hm, hg, fun γ' hγ' hg' t ht => ?_⟩
    obtain ⟨hpq', heq'⟩ := Emb.geodPQ_of_unbroken (p := p) (q := q) hγ' hg'
    rw [← heq' ht]
    exact congrArg (Bridge.incl hN) (huniq _ hpq' ht).symm
  · letI := hN.chartedSpace
    obtain ⟨D⟩ := h2
    exact ⟨(Emb.eucl n).trans D.symm⟩

#rt_check RoundTrip.V11_17.A_to_B_emb [Morse.isGeodesicallyComplete_of_isClosed,
  Morse.injective_expToN_of_simplyConnected, Morse.surjective_expToN, Morse.theorem_19_2]
#rt_check RoundTrip.V11_17.B_emb_to_A_cplt [Morse.isGeodesicallyComplete_of_isClosed,
  Morse.injective_expToN_of_simplyConnected, Morse.surjective_expToN, Morse.theorem_19_2]
#rt_overlap RoundTrip.V11_17.B_emb_to_A_cplt [Morse.isGeodesicallyComplete_of_isClosed,
  Morse.injective_expToN_of_simplyConnected, Morse.surjective_expToN, Morse.theorem_19_2]

end RoundTrip.V11_17
