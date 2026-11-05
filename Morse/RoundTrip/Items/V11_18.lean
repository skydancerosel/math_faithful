import Morse
import RoundTrip.Check
import RoundTrip.Blind.V11_18
import RoundTrip.Bridge
import RoundTrip.EnergyC2

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal unitInterval RealInnerProductSpace

namespace RoundTrip.V11_18

/-- The project's statement (universes instantiated at `0`): for a slice submanifold `N ⊆ V` with
the induced metric and `⟨R(A,B)A,B⟩ ≤ 0`: for closed `N`, `Ω(N; p, q)` has the homotopy type of a
countable cell complex (`Morse.IsCountableCellComplexType`, the project's notion) with only
`0`-cells, one for each geodesic (Theorem 17.3 with all indices `0`); for complete `N` the
geodesics from `p` to `q` are the points of the fibre `exp_p⁻¹(q)`, `Ω* ≃ₕ` that fibre, the fibre
is discrete and countable and `Ω ≃ₕ` the fibre; for complete simply connected `N`, `Ω(N; p, q)`
is contractible; and for closed simply connected `N` it has the homotopy type of a cell complex
with exactly one cell, a `0`-cell. -/
def A : Prop :=
  type_of% @Morse.omega_cells_of_nonpos.{0,0,0} ∧
    type_of% @Morse.geodesic_iff_mem_fiber.{0,0,0} ∧
    type_of% @Morse.nonempty_homotopyEquiv_pathC_fiber.{0,0,0} ∧
    type_of% @Morse.omega_homotopyEquiv_fiber.{0,0,0} ∧
    type_of% @Morse.contractibleSpace_pathSp.{0,0,0} ∧
    type_of% @Morse.omega_single_cell.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.omega_cells_of_nonpos, @Morse.geodesic_iff_mem_fiber,
    @Morse.nonempty_homotopyEquiv_pathC_fiber, @Morse.omega_homotopyEquiv_fiber,
    @Morse.contractibleSpace_pathSp, @Morse.omega_single_cell⟩

/-! Neither `A → B` nor `B → A` is proved: B quantifies over abstract connected Hausdorff
`ℝⁿ`-manifolds with an arbitrary smooth metric and an arbitrary Levi-Civita connection, A only
over slice submanifolds `N ⊆ V` with the induced metric (see `V11_18.json`). Below: the embedded
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
    set sc := Morse.sliceAt hN (f x)
    have hφ : ContDiffAt ℝ ∞ (fun y => (sc.φ y).1) (incl hN (f x)) :=
      contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn sc).contDiffAt
        (sc.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (f x))))
    have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) = (fun y => (sc.φ y).1) ∘ (incl hN ∘ f) := rfl
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
    set sc := Morse.sliceAt hN (f x)
    have hφ : ContDiffAt ℝ ∞ (fun y => (sc.φ y).1) (incl hN (f x)) :=
      contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn sc).contDiffAt
        (sc.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (f x))))
    have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) = (fun y => (sc.φ y).1) ∘ (incl hN ∘ f) := rfl
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
  set sc := Morse.sliceAt hN (f x)
  have hφ : DifferentiableAt ℝ (fun y => (sc.φ y).1) (incl hN (f x)) :=
    (Milnor.Problems.sliceChart_differentiableAt sc (Morse.mem_sliceAt_source hN (f x))).fst
  have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) = (fun y => (sc.φ y).1) ∘ (incl hN ∘ f) := rfl
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

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- The arc length `s(t) = ∫₀ᵗ ‖γ'‖` of a piecewise smooth path has derivative `‖γ'(t)‖` off a
finite set of `(0, 1)`. -/
theorem hasDerivAt_pathLength {c : ℝ → V} (hc : Morse.IsPiecewiseSmooth c 0 1) :
    ∃ B : Finset ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ B →
      HasDerivAt (fun x => Morse.pathLength c 0 x) ‖deriv c t‖ t := by
  obtain ⟨B, hB⟩ := hc.exists_deriv_piece
  refine ⟨B, fun t ht htB => ?_⟩
  have hopen : IsOpen (Ioo (0 : ℝ) 1 \ (B : Set ℝ)) := isOpen_Ioo.sdiff B.finite_toSet.isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen t ⟨ht, htB⟩
  have hsm : t - ε / 2 ∈ Metric.ball t ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_of_neg (by linarith)]; linarith
  have hup : t + ε / 2 ∈ Metric.ball t ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_of_pos (by linarith)]; linarith
  have hs0 : 0 ≤ t - ε / 2 := (hball hsm).1.1.le
  have hu1 : t + ε / 2 ≤ 1 := (hball hup).1.2.le
  have hsu : t - ε / 2 < t + ε / 2 := by linarith
  have hfree : ∀ x ∈ B, x ∉ Ioo (t - ε / 2) (t + ε / 2) := by
    intro x hx hx'
    have : x ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx'.1, hx'.2]
    exact (hball this).2 hx
  obtain ⟨K, hK, hKeq⟩ := hB _ _ hs0 hsu hu1 hfree
  have htI : t ∈ Ioo (t - ε / 2) (t + ε / 2) := ⟨by linarith, by linarith⟩
  have hev : deriv c =ᶠ[𝓝 t] K := by
    filter_upwards [Ioo_mem_nhds htI.1 htI.2] with x hx
    exact hKeq hx
  have hKt : ContinuousAt K t := hK.continuousAt (Icc_mem_nhds htI.1 htI.2)
  have hcont : ContinuousAt (fun x => ‖deriv c x‖) t :=
    (hKt.norm).congr (hev.fun_comp (‖·‖)).symm
  have hcontOn : ContinuousOn (fun x => ‖deriv c x‖) (Ioo (t - ε / 2) (t + ε / 2)) := by
    intro x hx
    have hev' : deriv c =ᶠ[𝓝 x] K := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hKeq hy
    exact ((hK.continuousAt (Icc_mem_nhds hx.1 hx.2)).norm.congr
      (hev'.fun_comp (‖·‖)).symm).continuousWithinAt
  have hmeas : StronglyMeasurableAtFilter (fun x => ‖deriv c x‖) (𝓝 t) volume :=
    hcontOn.stronglyMeasurableAtFilter isOpen_Ioo t htI
  have hint : IntervalIntegrable (fun x => ‖deriv c x‖) volume 0 t :=
    hc.isAdmissible.integrable.mono_set (by
      rw [uIcc_of_le zero_le_one, uIcc_of_le ht.1.le]
      exact Icc_subset_Icc le_rfl ht.2.le)
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont

/-- **Dictionary: `ds/dt`.** The blind `ds/dt` (derivative of the blind arc length) of a path in
`N` is the project's speed `‖(incl ∘ w)'‖`, off a finite subset of `(0, 1)`. -/
theorem dsdt_eq {w : ℝ → Bridge.Sub hN} (hw : IsPW (n := n) w 0 1) :
    ∃ B : Finset ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ B →
      dsdt (n := n) w t = Morse.PathSp.speed (incl hN ∘ w) t := by
  obtain ⟨B, hB⟩ := hasDerivAt_pathLength (isPiecewiseSmooth_of_isPW hw)
  refine ⟨B, fun t ht htB => ?_⟩
  have e : (fun x => arcLen (n := n) w 0 x) = fun x => Morse.pathLength (incl hN ∘ w) 0 x :=
    funext fun x => arcLen_eq w 0 x
  show deriv (fun x => arcLen (n := n) w 0 x) t = _
  rw [e]
  exact (hB t ht htB).deriv

/-- **Dictionary: the `L²` part.** -/
theorem integral_dsdt_eq {w w' : ℝ → Bridge.Sub hN} (hw : IsPW (n := n) w 0 1)
    (hw' : IsPW (n := n) w' 0 1) :
    ∫ t in (0 : ℝ)..1, (dsdt (n := n) w t - dsdt (n := n) w' t) ^ 2 =
      ∫ t in (0 : ℝ)..1, (Morse.PathSp.speed (incl hN ∘ w) t -
        Morse.PathSp.speed (incl hN ∘ w') t) ^ 2 := by
  classical
  obtain ⟨B, hB⟩ := dsdt_eq hw
  obtain ⟨B', hB'⟩ := dsdt_eq hw'
  refine intervalIntegral.integral_congr_ae ?_
  have hfin : ((B ∪ B' ∪ {1} : Finset ℝ) : Set ℝ).Finite := Finset.finite_toSet _
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hfin.measure_zero volume)] with t htB ht
  rw [uIoc_of_le zero_le_one] at ht
  simp only [Finset.coe_union, Finset.coe_singleton, mem_union, mem_singleton_iff,
    Finset.mem_coe, not_or] at htB
  have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_le_of_ne ht.2 htB.2⟩
  rw [hB t ht' htB.1.1, hB' t ht' htB.1.2]

/-- Two paths of `Ω(N; p, q)` are at finite uniform distance (both stay within their lengths of
`p`). -/
theorem supDist_ne_top {c c' : ℝ → V} {p q : V} (hc : c ∈ Morse.pathSpace N p q)
    (hc' : c' ∈ Morse.pathSpace N p q) : Morse.PathSp.supDist N c c' ≠ ⊤ := by
  have key : ∀ {c : ℝ → V}, c ∈ Morse.pathSpace N p q → ∀ t ∈ Icc (0 : ℝ) 1,
      Morse.riemDist (N := N) p (c t) ≤ ENNReal.ofReal (Morse.pathLength c 0 1) := by
    intro c hc t ht
    have h1 := Morse.riemDist_le_pathLength (N := N) (hc.1.mono le_rfl ht.1 ht.2)
      (fun s hs => hc.2.1 s ⟨hs.1, hs.2.trans ht.2⟩)
    rw [hc.2.2.1] at h1
    exact h1.trans (ENNReal.ofReal_le_ofReal (hc.1.isAdmissible.pathLength_le le_rfl ht.1 ht.2))
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (Morse.pathLength c 0 1) +
    ENNReal.ofReal (Morse.pathLength c' 0 1)) (by simp) ?_
  refine iSup₂_le fun t ht => ?_
  calc Morse.riemDist (N := N) (c t) (c' t)
      ≤ Morse.riemDist (N := N) (c t) p + Morse.riemDist (N := N) p (c' t) :=
        Morse.riemDist_triangle _ _ _
    _ ≤ _ := add_le_add ((Morse.riemDist_comm _ _).trans_le (key hc t ht)) (key hc' t ht)

/-- A blind path of `Ω(↥N; p, q)` is, in `V`, a project path of `Ω(N; p, q)`. -/
theorem mem_pathSpace {p q : Bridge.Sub hN} {w : ℝ → Bridge.Sub hN}
    (hw : InOmega (n := n) p q w) :
    incl hN ∘ w ∈ Morse.pathSpace N (incl hN p) (incl hN q) :=
  ⟨isPiecewiseSmooth_of_isPW hw.1, fun t _ => (w t).2, congrArg (incl hN) hw.2.1,
    congrArg (incl hN) hw.2.2⟩

/-- The project path `incl ∘ w` of a blind path, as an element of `Morse.PathSp N p q`. -/
def pt {p q : Bridge.Sub hN} {w : ℝ → Bridge.Sub hN} (hw : InOmega (n := n) p q w) :
    Morse.PathSp N (incl hN p) (incl hN q) :=
  ⟨incl hN ∘ w, mem_pathSpace hw⟩

/-- **Dictionary: the uniform part.** -/
theorem iSup_rho_eq {p q : Bridge.Sub hN} {w w' : ℝ → Bridge.Sub hN}
    (hw : InOmega (n := n) p q w) (hw' : InOmega (n := n) p q w') :
    (⨆ t : Icc (0 : ℝ) 1, rho (n := n) (w t) (w' t)) =
      (Morse.PathSp.supDist N (incl hN ∘ w) (incl hN ∘ w')).toReal := by
  have hne := supDist_ne_top (mem_pathSpace hw) (mem_pathSpace hw')
  rw [Morse.PathSp.supDist, iSup_subtype', ENNReal.toReal_iSup ?_]
  · exact iSup_congr fun t => rho_eq _ _
  · intro t
    exact ne_top_of_le_ne_top hne (Morse.PathSp.riemDist_le_supDist t.2)

/-- **Dictionary: Milnor's metric.** For blind paths `w, w'` of `Ω(↥N; p, q)`, the blind `d(w, w')`
is the project's `edist` of `incl ∘ w, incl ∘ w'` in `Morse.PathSp N p q`. -/
theorem edist_eq {p q : Bridge.Sub hN} {w w' : ℝ → Bridge.Sub hN}
    (hw : InOmega (n := n) p q w) (hw' : InOmega (n := n) p q w') :
    edist (pt hw) (pt hw') = ENNReal.ofReal (dOm (n := n) w w') := by
  rw [Morse.PathSp.edist_def]
  show _ = ENNReal.ofReal ((⨆ t : Icc (0 : ℝ) 1, rho (n := n) (w t) (w' t)) +
    Real.sqrt (∫ t in (0 : ℝ)..1, (dsdt (n := n) w t - dsdt (n := n) w' t) ^ 2))
  rw [iSup_rho_eq hw hw', integral_dsdt_eq hw.1 hw'.1,
    ENNReal.ofReal_add ENNReal.toReal_nonneg (Real.sqrt_nonneg _),
    ENNReal.ofReal_toReal (supDist_ne_top (mem_pathSpace hw) (mem_pathSpace hw'))]
  rfl

theorem dOm_nonneg {p q : Bridge.Sub hN} {w w' : ℝ → Bridge.Sub hN}
    (hw : InOmega (n := n) p q w) (hw' : InOmega (n := n) p q w') : 0 ≤ dOm (n := n) w w' := by
  show 0 ≤ (⨆ t : Icc (0 : ℝ) 1, rho (n := n) (w t) (w' t)) +
    Real.sqrt (∫ t in (0 : ℝ)..1, (dsdt (n := n) w t - dsdt (n := n) w' t) ^ 2)
  rw [iSup_rho_eq hw hw']
  exact add_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _)


/-- The blind energy of a path in `N` is the project's energy of `incl ∘ w`. -/
theorem efun_eq (w : ℝ → Bridge.Sub hN) : Efun (n := n) w = Morse.energy (incl hN ∘ w) 0 1 :=
  energy_eq w 0 1

/-- A project path of `Ω(N; p, q)` lifts to a blind path of `Ω(↥N; p', q')` agreeing with it on
`[0, 1]`. -/
theorem inOmega_lift {p' q' : Bridge.Sub hN} {c : ℝ → V}
    (hc : c ∈ Morse.pathSpace N (incl hN p') (incl hN q')) :
    InOmega (n := n) p' q' (lift c p') ∧ EqOn (incl hN ∘ lift c p') c (Icc 0 1) := by
  have heq : EqOn (incl hN ∘ lift c p') c (Icc 0 1) := fun t ht => incl_lift p' (hc.2.1 t ht)
  refine ⟨⟨isPW_lift hc.1 hc.2.1 p', ?_, ?_⟩, heq⟩
  · apply Subtype.ext
    exact (heq ⟨le_rfl, zero_le_one⟩).trans hc.2.2.1
  · apply Subtype.ext
    exact (heq ⟨zero_le_one, le_rfl⟩).trans hc.2.2.2


/-! ### Topological dictionary for `Ω` and `Ω*` (new; as in Items/V10_15.lean) -/

section Omega

variable {p q : Bridge.Sub hN}

/-- The blind `Ω(↥N; p, q)` maps to the project's `Ω(N; p, q)` by `w ↦ incl ∘ w`. -/
def tau (w : Om n p q) : Morse.PathSp N (incl hN p) (incl hN q) := pt w.2

theorem dOm_self (w : Om n p q) : dOm (n := n) w.1 w.1 = 0 := by
  have h := edist_eq w.2 w.2
  rw [edist_self] at h
  have h0 := dOm_nonneg w.2 w.2
  have := ENNReal.ofReal_eq_zero.1 h.symm
  linarith

/-- **The blind topology of `Ω` (generated by Milnor's `d`-balls) is induced by `τ`** from the
project's pseudo-emetric topology on `Ω(N; p, q)`. -/
theorem omTopology_eq :
    omTopology n p q = TopologicalSpace.induced (tau (n := n)) inferInstance := by
  apply le_antisymm
  · intro s hs
    obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.1 hs
    rw [isOpen_iff_forall_mem_open]
    intro w hw
    obtain ⟨ε, hε, hball⟩ := EMetric.isOpen_iff.1 hU _ hw
    obtain ⟨r, -, hr0, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have hr : 0 < r := ENNReal.ofReal_pos.1 hr0
    refine ⟨{w' | dOm (n := n) w.1 w'.1 < r}, fun w' hw' => hball ?_,
      TopologicalSpace.isOpen_generateFrom_of_mem ⟨w, r, rfl⟩, ?_⟩
    · rw [Metric.mem_eball, edist_comm]
      show edist (pt w.2) (pt w'.2) < ε
      rw [edist_eq w.2 w'.2]
      exact ((ENNReal.ofReal_lt_ofReal_iff hr).2 hw').trans hrε
    · show dOm (n := n) w.1 w.1 < r
      rw [dOm_self]; exact hr
  · refine le_generateFrom fun s ⟨w, ε, hs⟩ => ?_
    subst hs
    rcases le_or_gt ε 0 with hε | hε
    · convert @isOpen_empty _ (TopologicalSpace.induced (tau (n := n)) inferInstance)
      ext w'
      show dOm (n := n) w.1 w'.1 < ε ↔ False
      simp only [iff_false, not_lt]
      exact hε.trans (dOm_nonneg w.2 w'.2)
    · refine isOpen_induced_iff.2
        ⟨Metric.eball (tau w) (ENNReal.ofReal ε), Metric.isOpen_eball, ?_⟩
      ext w'
      show edist (tau w') (tau w) < ENNReal.ofReal ε ↔ dOm (n := n) w.1 w'.1 < ε
      rw [edist_comm]
      show edist (pt w.2) (pt w'.2) < _ ↔ _
      rw [edist_eq w.2 w'.2, ENNReal.ofReal_lt_ofReal_iff hε]

theorem isInducing_tau : IsInducing (tau (n := n) (p := p) (q := q)) := ⟨omTopology_eq⟩

/-- **The blind `Ω*` (continuous maps `I → ↥N`) is homeomorphic to the project's `PathC`**
(continuous maps `I → V` with values in `N`), both with the compact-open topology. -/
def sigma : OmStar p q ≃ₜ Morse.PathC N (incl hN p) (incl hN q) where
  toFun w := ⟨(⟨incl hN, continuous_subtype_val⟩ : C(Bridge.Sub hN, V)).comp w.1,
    fun t => (w.1 t).2, congrArg (incl hN) w.2.1, congrArg (incl hN) w.2.2⟩
  invFun γ := ⟨⟨fun t => (⟨(γ.1 : C(I, V)) t, γ.2.1 t⟩ : N), by fun_prop⟩,
    Subtype.ext γ.2.2.1, Subtype.ext γ.2.2.2⟩
  left_inv w := rfl
  right_inv γ := rfl
  continuous_toFun :=
    ((ContinuousMap.continuous_postcomp _).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine (ContinuousMap.isInducing_postcomp
      (⟨incl hN, continuous_subtype_val⟩ : C(Bridge.Sub hN, V))
      IsInducing.subtypeVal).continuous_iff.2 ?_
    exact continuous_subtype_val

theorem isInducing_sigma_val :
    IsInducing (fun w : OmStar p q => ((sigma w : Morse.PathC N _ _) : C(I, V))) :=
  IsInducing.subtypeVal.comp sigma.isInducing

end Omega

/-! ### Homotopy equivalence `Ω ≃ PathSp` (new) -/

/-- Two maps whose values are pointwise inseparable are homotopic. -/
theorem homotopic_of_inseparable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) (h : ∀ x, Inseparable (f x) (g x)) : f.Homotopic g := by
  classical
  refine ⟨{ toFun := fun z => if (z.1 : ℝ) = 0 then f z.2 else g z.2
            continuous_toFun := ?_
            map_zero_left := fun x => by simp
            map_one_left := fun x => by simp }⟩
  refine (continuous_congr_of_inseparable (g := fun z : I × X => g z.2) fun z => ?_).2
    (g.continuous.comp continuous_snd)
  split_ifs
  · exact h z.2
  · exact Inseparable.refl _

section HE

variable {p q : Bridge.Sub hN}

/-- `τ` as a continuous map. -/
def tauC : C(Om n p q, Morse.PathSp N (incl hN p) (incl hN q)) :=
  ⟨tau, isInducing_tau.continuous⟩

/-- Lifting a project path to a blind one (`Bridge.lift`). -/
noncomputable def lamP (γ : Morse.PathSp N (incl hN p) (incl hN q)) : Om n p q :=
  ⟨lift (γ : ℝ → V) p, (inOmega_lift γ.2).1⟩

theorem tau_lam_insep (γ : Morse.PathSp N (incl hN p) (incl hN q)) :
    Inseparable (tau (lamP (n := n) γ)) γ :=
  EMetric.inseparable_iff.2 (Morse.PathSp.edist_eq_zero_of_eqOn (inOmega_lift γ.2).2)

theorem lam_tau_insep (w : Om n p q) : Inseparable (lamP (n := n) (tau w)) w :=
  isInducing_tau.inseparable_iff.1 (EMetric.inseparable_iff.2
    (Morse.PathSp.edist_eq_zero_of_eqOn (inOmega_lift (tau w).2).2))

theorem continuous_lam : Continuous (lamP (n := n) (p := p) (q := q)) := by
  refine isInducing_tau.continuous_iff.2 ?_
  exact (continuous_congr_of_inseparable tau_lam_insep).2 continuous_id

noncomputable def lamPC : C(Morse.PathSp N (incl hN p) (incl hN q), Om n p q) := ⟨lamP, continuous_lam⟩

theorem lam_tau_homotopic : ((lamPC (n := n) (p := p) (q := q)).comp tauC).Homotopic
    (ContinuousMap.id _) :=
  homotopic_of_inseparable _ _ lam_tau_insep

theorem tau_lam_homotopic : ((tauC (n := n) (p := p) (q := q)).comp lamPC).Homotopic
    (ContinuousMap.id _) :=
  homotopic_of_inseparable _ _ tau_lam_insep

/-- **The blind `Ω` and the project's `Ω(N; p, q)` are homotopy equivalent** via `τ`. -/
theorem isHomotopyEquiv_tau : Morse.IsHomotopyEquiv (tauC (n := n) (p := p) (q := q)) :=
  ⟨lamPC, lam_tau_homotopic, tau_lam_homotopic⟩

theorem isHomotopyEquiv_lam : Morse.IsHomotopyEquiv (lamPC (n := n) (p := p) (q := q)) :=
  Morse.IsHomotopyEquiv.of_inverse lam_tau_homotopic tau_lam_homotopic

end HE
end Emb

/-! ### Zero-dimensional CW complexes (pure topology) -/

namespace CW0

/-- The cells of the one-point CW complex: one `0`-cell. -/
def ptCell (l : ℕ) : Type := {_u : Unit // l = 0}

/-- Its characteristic maps. -/
noncomputable def ptMap (l : ℕ) (i : ptCell l) : PartialEquiv (Fin l → ℝ) Unit where
  toFun _ := ()
  invFun _ := 0
  source := Metric.ball 0 1
  target := univ
  map_source' _ _ := trivial
  map_target' _ _ := Metric.mem_ball_self one_pos
  left_inv' x _ := by
    obtain ⟨_, rfl⟩ := i
    exact Subsingleton.elim _ _
  right_inv' _ _ := rfl

/-- **The one-point CW complex** (Mathlib's `Topology.CWComplex` on `Unit`). -/
noncomputable instance ptCW : Topology.CWComplex (univ : Set Unit) where
  cell := ptCell
  map := ptMap
  source_eq _ _ := rfl
  continuousOn _ _ := continuousOn_const
  continuousOn_symm _ _ := continuousOn_const
  pairwiseDisjoint' := by
    rintro ⟨l, ⟨u, hl⟩⟩ - ⟨l', ⟨u', hl'⟩⟩ - hne
    subst hl
    subst hl'
    exact absurd rfl hne
  mapsTo' l i := by
    refine ⟨fun _ => ∅, ?_⟩
    obtain ⟨_, rfl⟩ := i
    intro x hx
    rw [Metric.sphere_eq_empty_of_subsingleton one_ne_zero] at hx
    exact absurd hx (notMem_empty x)
  closed' A _ _ := (Set.subsingleton_of_subsingleton (s := A)).isClosed
  union' := by
    refine eq_univ_of_forall fun x => mem_iUnion₂.2 ⟨0, ⟨(), rfl⟩, ?_⟩
    exact ⟨0, Metric.mem_closedBall_self zero_le_one, rfl⟩

theorem isEmpty_ptCell {l : ℕ} (hl : 0 < l) :
    IsEmpty (Topology.CWComplex.cell (univ : Set Unit) l) :=
  ⟨fun i => by have := i.2; omega⟩

/-- **A connected Hausdorff CW complex with no cells of positive dimension is a point** (every
subset is closed: its trace on each closed `0`-cell, a point, is closed). -/
theorem subsingleton_of_cw0 (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (univ : Set Y)]
    (h : ∀ l : ℕ, 0 < l → IsEmpty (Topology.CWComplex.cell (univ : Set Y) l)) [ConnectedSpace Y] :
    Subsingleton Y := by
  have hcl : ∀ A : Set Y, IsClosed A := by
    intro A
    refine (Topology.CWComplex.closed (univ : Set Y) A (subset_univ A)).2 fun l j => ?_
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · rw [Topology.CWComplex.closedCell_zero_eq_singleton]
      exact (Set.subsingleton_singleton.anti inter_subset_right).isClosed
    · exact ((h l hl).false j).elim
  constructor
  intro x y
  have hclopen : IsClopen ({x} : Set Y) := ⟨hcl _, by rw [← isClosed_compl_iff]; exact hcl _⟩
  rcases isClopen_iff.1 hclopen with h0 | h1
  · exact absurd h0 (singleton_ne_empty x)
  · have : y ∈ ({x} : Set Y) := by rw [h1]; trivial
    exact (mem_singleton_iff.1 this).symm

/-- A space homotopy equivalent to a connected space is connected. -/
theorem connectedSpace_of_hequiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ConnectedSpace X] (e : ContinuousMap.HomotopyEquiv X Y) : ConnectedSpace Y := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  refine connectedSpace_iff_connectedComponent.2 ⟨e.toFun x₀, eq_univ_of_forall fun y => ?_⟩
  have h1 : e.toFun (e.invFun y) ∈ connectedComponent (e.toFun x₀) :=
    (isPreconnected_range e.toFun.continuous).subset_connectedComponent ⟨x₀, rfl⟩ ⟨_, rfl⟩
  obtain ⟨F⟩ := e.right_inv
  have hc : Continuous fun t : I => F (t, y) := F.continuous.comp (continuous_id.prodMk continuous_const)
  have h2 : y ∈ connectedComponent (e.toFun (e.invFun y)) := by
    have hy : y ∈ range fun t : I => F (t, y) := ⟨1, by simp⟩
    have h0 : e.toFun (e.invFun y) ∈ range fun t : I => F (t, y) := ⟨0, by simp⟩
    exact (isPreconnected_range hc).subset_connectedComponent h0 hy
  rw [connectedComponent_eq h1]
  exact h2

end CW0

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- The blind `Ω(↥N; p, q)` is homotopy equivalent to the project's `Ω(N; p, q)`. -/
noncomputable def omHE (p q : Bridge.Sub hN) :
    ContinuousMap.HomotopyEquiv (Om n p q) (Morse.PathSp N (incl hN p) (incl hN q)) :=
  ⟨tauC, lamPC, lam_tau_homotopic, tau_lam_homotopic⟩

/-- The blind index of every blind geodesic of `↥N` is `0` in non-positive curvature. -/
theorem lam_geod_eq_zero (hK : Morse.NonposCurvature hN) {g : ℝ → Bridge.Sub hN}
    (hg : IsGeodesic (conn (hN := hN)) g (Icc 0 1)) : lam (n := n) 1 g = 0 :=
  lam_eq_zero hg fun X hX =>
    Morse.energyHessian_pos_of_nonpos hK _ (unbroken_of_geodPQ ⟨hg, rfl, rfl⟩).2 X hX

/-- The unique geodesic (Theorem 19.2 through the geodesic dictionary). -/
theorem unique_geod (hc : Morse.IsGeodesicallyComplete hN) (hsc : SimplyConnectedSpace N)
    (hK : Morse.NonposCurvature hN) (p q : Bridge.Sub hN) :
    ∃ γ, IsGeodPQ n (conn (hN := hN)) p q γ ∧
      ∀ γ', IsGeodPQ n (conn (hN := hN)) p q γ' → Set.EqOn γ γ' (Set.Icc 0 1) := by
  obtain ⟨γ, hγ, hg, huniq⟩ := (Morse.theorem_19_2 hc hsc hK).1 p q
  obtain ⟨hpq, heq⟩ := geodPQ_of_unbroken (p := p) (q := q) hγ hg
  refine ⟨_, hpq, fun γ' hγ' t ht => Subtype.ext ?_⟩
  obtain ⟨hm', hg'⟩ := unbroken_of_geodPQ hγ'
  exact (heq ht).trans (huniq _ hm' hg' ht).symm

end Emb

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric) with the induced Levi-Civita
connection `Bridge.conn` (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    MetricComplete n (Bridge.Sub hN) → SimplyConnectedSpace (Bridge.Sub hN) →
    NonPosCurv n (Bridge.conn (hN := hN)) → ∀ p q : Bridge.Sub hN,
      ConnectedSpace (Om n p q) ∧
      (∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (_ : CWComplex (Set.univ : Set Y)),
        (∀ l : ℕ, 0 < l → IsEmpty (Topology.CWComplex.cell (Set.univ : Set Y) l)) ∧
        Nonempty (ContinuousMap.HomotopyEquiv (Om n p q) Y) ∧
        ∀ l : ℕ, Nonempty (Topology.CWComplex.cell (Set.univ : Set Y) l ≃
          GeodIdx n (Bridge.conn (hN := hN)) p q l Set.univ)) ∧
      (∀ (Y : Type) [TopologicalSpace Y] [T2Space Y] [CWComplex (Set.univ : Set Y)],
        (∀ l : ℕ, 0 < l → IsEmpty (Topology.CWComplex.cell (Set.univ : Set Y) l)) →
          ConnectedSpace Y → Subsingleton Y)

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds.** Connectedness and the homotopy type of a point: A's
`contractibleSpace_pathSp` through `Ω ≃ₕ PathSp` (`Emb.omHE`, from Items/V10_19.lean). The
one-point CW complex `CW0.ptCW` on `Unit`; its single `0`-cell ↔ the unique geodesic in `Ω*`
(Theorem 19.2, `Emb.unique_geod`), which has blind index `0` (`Emb.lam_geod_eq_zero`, the Hessian
dictionary with `energyHessian_pos_of_nonpos`), and no geodesic has positive index. The last
conjunct is pure topology (`CW0.subsingleton_of_cw0`). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ hmc hsc hK p q
  have hc := Emb.complete_of_metricComplete hmc
  have hsc' : SimplyConnectedSpace N := hsc
  have hK' := Emb.nonPosCurv_iff.1 hK
  have hcon : ContractibleSpace (Morse.PathSp N (Bridge.incl hN p) (Bridge.incl hN q)) :=
    hA.2.2.2.2.1 hc hsc' hK' p q
  have hOm : ContractibleSpace (Om n p q) := (Emb.omHE p q).contractibleSpace
  obtain ⟨eU⟩ := ContractibleSpace.hequiv_unit (Om n p q)
  obtain ⟨γ, ⟨hγ, hγ0, hγ1⟩, huniq⟩ := Emb.unique_geod hc hsc' hK' p q
  -- the unique geodesic as a point of `Ω*`
  let γs : OmStar p q :=
    ⟨⟨(Icc (0 : ℝ) 1).restrict γ, (hγ.2.1.continuousOn).restrict⟩, hγ0, hγ1⟩
  have hγs : γs ∈ GeodIdx n (Bridge.conn (hN := hN)) p q 0 Set.univ :=
    ⟨γ, ⟨hγ, fun _ => rfl⟩, Emb.lam_geod_eq_zero hK' hγ, trivial⟩
  have hsub : ∀ x ∈ GeodIdx n (Bridge.conn (hN := hN)) p q 0 Set.univ, x = γs := by
    rintro x ⟨g, ⟨hg, hgx⟩, -, -⟩
    have hg0 : g 0 = p := by rw [← x.2.1]; exact (hgx 0).symm
    have hg1 : g 1 = q := by rw [← x.2.2]; exact (hgx 1).symm
    have heq := huniq g ⟨hg, hg0, hg1⟩
    exact Subtype.ext (ContinuousMap.ext fun t => (hgx t).trans (heq t.2).symm)
  have hpos : ∀ l : ℕ, 0 < l → GeodIdx n (Bridge.conn (hN := hN)) p q l Set.univ = ∅ := by
    intro l hl
    refine eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨g, ⟨hg, -⟩, hlam, -⟩ := hx
    rw [Emb.lam_geod_eq_zero hK' hg] at hlam
    have : (l : ℕ∞) = 0 := hlam.symm
    exact absurd (by exact_mod_cast this) hl.ne'
  refine ⟨inferInstance, ⟨Unit, inferInstance, inferInstance, CW0.ptCW,
    fun l hl => CW0.isEmpty_ptCell hl, ⟨eU⟩, fun l => ?_⟩, fun Y _ _ _ h _ =>
    CW0.subsingleton_of_cw0 Y h⟩
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · exact ⟨{ toFun := fun _ => ⟨γs, hγs⟩
             invFun := fun _ => ⟨(), rfl⟩
             left_inv := fun x => by obtain ⟨u, hu⟩ := x; rfl
             right_inv := fun y => Subtype.ext (hsub y.1 y.2).symm }⟩
  · haveI := CW0.isEmpty_ptCell hl
    haveI : IsEmpty (GeodIdx n (Bridge.conn (hN := hN)) p q l Set.univ) := by
      rw [hpos l hl]; infer_instance
    exact ⟨Equiv.equivOfIsEmpty _ _⟩

/-- The part of A that B covers on embedded manifolds: A's `contractibleSpace_pathSp` (Milnor's
"`Ω(M; p, q)` has the homotopy type of a point") for model `ℝⁿ`. -/
def A_cplt : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
    Morse.IsGeodesicallyComplete hN → SimplyConnectedSpace N → Morse.NonposCurvature hN →
      ∀ p q : N, ContractibleSpace (Morse.PathSp N p q)

theorem A_to_A_cplt : A → A_cplt := fun hA _ _ _ _ _ _ _ _ _ _ _ hc hsc hK p q =>
  hA.2.2.2.2.1 hc hsc hK p q

/-- **B on embedded manifolds implies the contractibility of `Ω(N; p, q)`**: `Ω` is connected and
homotopy equivalent to a `0`-dimensional CW complex `Y`, which is then connected, hence a point by
B's last conjunct. -/
theorem B_emb_to_A_cplt : B_emb → A_cplt := by
  intro hB V _ _ _ W _ _ _ n N hN hc hsc hK p q
  have : ConnectedSpace (Bridge.Sub hN) := (inferInstance : ConnectedSpace N)
  let p' : Bridge.Sub hN := p
  let q' : Bridge.Sub hN := q
  obtain ⟨hconn, ⟨Y, _, _, _, hcells, ⟨e⟩, -⟩, hsub⟩ :=
    hB V W n N hN (Emb.metricComplete_of_complete hc) hsc (Emb.nonPosCurv_iff.2 hK) p' q'
  have hYc : ConnectedSpace Y := CW0.connectedSpace_of_hequiv e
  have hYs : Subsingleton Y := hsub Y hcells hYc
  have hYn : Nonempty Y := hYc.toNonempty
  have hYcon : ContractibleSpace Y := inferInstance
  have hOm : ContractibleSpace (Om n p' q') := e.contractibleSpace
  exact (Emb.omHE p' q').symm.contractibleSpace

#rt_check RoundTrip.V11_18.A_to_B_emb [Morse.omega_cells_of_nonpos, Morse.geodesic_iff_mem_fiber,
  Morse.nonempty_homotopyEquiv_pathC_fiber, Morse.omega_homotopyEquiv_fiber,
  Morse.contractibleSpace_pathSp, Morse.omega_single_cell]
#rt_check RoundTrip.V11_18.B_emb_to_A_cplt [Morse.omega_cells_of_nonpos,
  Morse.geodesic_iff_mem_fiber, Morse.nonempty_homotopyEquiv_pathC_fiber,
  Morse.omega_homotopyEquiv_fiber, Morse.contractibleSpace_pathSp, Morse.omega_single_cell]
#rt_overlap RoundTrip.V11_18.B_emb_to_A_cplt [Morse.omega_cells_of_nonpos,
  Morse.geodesic_iff_mem_fiber, Morse.nonempty_homotopyEquiv_pathC_fiber,
  Morse.omega_homotopyEquiv_fiber, Morse.contractibleSpace_pathSp, Morse.omega_single_cell]

end RoundTrip.V11_18
