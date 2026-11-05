import Morse
import RoundTrip.Check
import RoundTrip.Blind.V11_13
import RoundTrip.Bridge

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal unitInterval RealInnerProductSpace

namespace RoundTrip.V11_13

/-- The project's statement (universes instantiated at `0`; `Morse.RicciLowerBound` is
vocabulary): a minimal geodesic in Milnor's sense on `[0, 1]` (`Morse.IsMinimalGeodesic`) is an
unbroken geodesic of `Ω(N; γ(0), γ(1))` of minimal length; and **Corollary 19.5** for slice
submanifolds `N ⊆ V` (model `Z`): `N` preconnected and complete (`riemDist`), `r > 0`,
`(n − 1)/r² > 0` and `K(U, U) ≥ (n − 1)/r²` ⇒ `ρ(p, q) ≤ πr` for all `p, q ∈ N`, and `N` is
compact. -/
def A : Prop :=
  type_of% @Morse.IsMinimalGeodesic.isMinimalPath.{0,0,0} ∧ type_of% @Morse.corollary_19_5.{0,0,0}

theorem A_holds : A := ⟨@Morse.IsMinimalGeodesic.isMinimalPath, @Morse.corollary_19_5⟩

/-! ## Dictionary (copied from `Items/V11_12.lean`, `Items/V7_29.lean`, `Items/V9_10.lean`) -/

namespace Emb

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

theorem isIntv_Icc : RoundTrip.BridgePrelude.IsIntv (Icc (0 : ℝ) 1) :=
  ⟨ordConnected_Icc, uniqueDiffOn_Icc zero_lt_one⟩

theorem isSmoothCurveIn {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) :
    Morse.IsSmoothCurveIn hN (incl hN ∘ γ) :=
  ⟨isSmoothCurve_iff.1 hγ, fun t _ => (γ t).2⟩

theorem prj_incl (x : Bridge.Sub hN) : Morse.prj hN (incl hN x) = P hN x :=
  Morse.prj_of_mem hN x.2

/-- On the interior, `derivWithin [0,1]` of a function smooth on `[0, 1]` is `deriv`, near `t`. -/
theorem derivWithin_eventuallyEq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} (hF : ContDiffOn ℝ ∞ F (Icc 0 1)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    derivWithin F (Icc 0 1) =ᶠ[𝓝 t] deriv F := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
  exact ((hF.contDiffAt (Icc_mem_nhds hx.1 hx.2)).differentiableAt (by simp)).hasDerivAt
    |>.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one x (Ioo_subset_Icc_self hx))

/-- A smooth curve in `N` on `[0, 1]` which is a geodesic on `(0, 1)` lifts to a blind geodesic of
the induced connection on `[0, 1]` (from `Items/V9_10.lean`). -/
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

/-! ### The Ricci tensor (from `Items/V11_24.lean`) -/

/-- The coordinate isomorphism `ℝⁿ ≃ T_xN`, `z ↦ D_x z`. -/
noncomputable def eT (x : Bridge.Sub hN) : Bridge.Rn n ≃ₗ[ℝ] Morse.tangentSubspace hN x :=
  LinearEquiv.ofBijective
    ((D hN x : Bridge.Rn n →ₗ[ℝ] V).codRestrict (Morse.tangentSubspace hN x) (D_mem x))
    ⟨fun _ _ h => D_injective x (congrArg Subtype.val h),
      fun v => ⟨L hN x v, Subtype.ext (D_L v.2)⟩⟩

/-- **Dictionary: curvature values.** -/
theorem curvR_eq (x : Bridge.Sub hN) (a b c : TangentSpace 𝓘(ℝ, Bridge.Rn n) x) :
    curvR (Bridge.conn (hN := hN)) x a b c =
      L hN x (Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c)) := by
  have hr : ∀ r, IsCurvVal (Bridge.conn (hN := hN)) x a b c r ↔
      D hN x r = Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c) := fun r => by
    have h := Bridge.isCurvVal_iff x a b c r
    have e : Morse.curvR hN (incl hN x) (D hN x a) (D hN x b) (D hN x c) =
        Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c) := Morse.curvR_of_mem hN x.2 _ _ _
    rw [e] at h
    exact h
  have hmem : Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c) ∈ Morse.tangentSubspace hN x :=
    Morse.curvOp_mem hN (D_mem x a) (D_mem x b) (D_mem x c)
  have hex : ∃ r, IsCurvVal (Bridge.conn (hN := hN)) x a b c r :=
    ⟨L hN x _, (hr _).2 (D_L hmem)⟩
  unfold curvR
  rw [dif_pos hex]
  apply D_injective x
  rw [(hr _).1 hex.choose_spec, D_L hmem]

/-- **Dictionary: the Ricci tensor** (diagonal). -/
theorem ricci_eq (x : Bridge.Sub hN) (U : TangentSpace 𝓘(ℝ, Bridge.Rn n) x) :
    ricci (Bridge.conn (hN := hN)) x U U =
      Morse.ricci hN x ⟨D hN x U, D_mem x U⟩ ⟨D hN x U, D_mem x U⟩ := by
  set U' : Morse.tangentSubspace hN x := ⟨D hN x U, D_mem x U⟩
  set T := (Morse.curvTensor hN x U').flip U'
  have hT : ∀ W : Bridge.Rn n, ((eT x).symm.conj T) W = curvR (Bridge.conn (hN := hN)) x U W U := by
    intro W
    have hmem : Morse.curvOp hN x (D hN x U) (D hN x W) (D hN x U) ∈
        Morse.tangentSubspace hN x :=
      Morse.curvOp_mem hN (D_mem x U) (D_mem x W) (D_mem x U)
    have h1 : ((eT x).symm.conj T) W = (eT x).symm (T (eT x W)) := rfl
    have h2 : (eT x).symm (T (eT x W)) =
        L hN x (Morse.curvOp hN x (D hN x U) (D hN x W) (D hN x U)) := by
      apply (eT x).injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      show Morse.curvOp hN x (D hN x U) (D hN x W) (D hN x U) = D hN x (L hN x _)
      exact (D_L hmem).symm
    exact h1.trans (h2.trans (curvR_eq x U W U).symm)
  have hex : ∃ L' : Bridge.Rn n →ₗ[ℝ] Bridge.Rn n, ∀ W : Bridge.Rn n,
      L' W = curvR (Bridge.conn (hN := hN)) x U W U := ⟨_, hT⟩
  have hch : hex.choose = (eT x).symm.conj T :=
    LinearMap.ext fun W => (hex.choose_spec W).trans (hT W).symm
  unfold ricci
  rw [dif_pos hex, hch, LinearMap.trace_conj']
  rfl


/-- A blind geodesic on `[0, 1]` of `↥N` from `p` to `q` is, in `V`, a project geodesic of
`Ω(N; p, q)` (from `Items/V10_23.lean`). -/
theorem mem_pathSpace_of_isGeodesic {γ : ℝ → Bridge.Sub hN} {p q : Bridge.Sub hN}
    (h : IsGeodesic (conn (hN := hN)) γ (Icc 0 1)) (h0 : γ 0 = p) (h1 : γ 1 = q) :
    incl hN ∘ γ ∈ Morse.pathSpace N (incl hN p) (incl hN q) ∧
      Morse.IsUnbrokenGeodesic hN (incl hN ∘ γ) := by
  have h' : RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hN)) γ (Icc 0 1) := h
  obtain ⟨-, hc, -⟩ := isGeodesic_iff.1 h'
  exact ⟨⟨Morse.IsPiecewiseSmooth.of_contDiffOn hc zero_le_one subset_rfl, fun t _ => (γ t).2,
    congrArg (incl hN) h0, congrArg (incl hN) h1⟩, hc, isGeodesicOn_Ioo h'⟩

/-- A project path of `Ω(N; p, q)` lifts to a blind piecewise smooth path in `↥N` agreeing with it
on `[0, 1]` (from `Items/V8_6.lean`). -/
theorem lift_mem {c : ℝ → V} {p q : Bridge.Sub hN}
    (hc : c ∈ Morse.pathSpace N (incl hN p) (incl hN q)) :
    InOmega (n := n) p q (lift c p) ∧ EqOn (incl hN ∘ lift c p) c (Icc 0 1) := by
  obtain ⟨hps, hmem, h0, h1⟩ := hc
  refine ⟨⟨isPW_lift hps hmem p, ?_, ?_⟩, fun t ht => incl_lift p (hmem t ht)⟩
  · rw [lift_of_mem p (hmem 0 ⟨le_rfl, zero_le_one⟩)]
    exact Subtype.ext h0
  · rw [lift_of_mem p (hmem 1 ⟨zero_le_one, le_rfl⟩)]
    exact Subtype.ext h1

/-- A blind minimal geodesic (arc length `≤` that of every blind piecewise smooth path) is, in `V`,
a project minimal path. -/
theorem isMinimalPath_of_isMinimal {γ : ℝ → Bridge.Sub hN}
    (h : IsMinimal (conn (hN := hN)) γ 0 1) :
    Morse.IsMinimalPath N (incl hN ∘ γ) (incl hN (γ 0)) (incl hN (γ 1)) := by
  obtain ⟨hmem, -⟩ := mem_pathSpace_of_isGeodesic h.1 rfl rfl
  refine ⟨hmem, fun c' hc' => ?_⟩
  obtain ⟨hpw', heq'⟩ := lift_mem (n := n) hc'
  have := h.2 (lift c' (γ 0)) 0 1 zero_le_one hpw'.1 hpw'.2.1 hpw'.2.2
  have e1 : arcLen (n := n) γ 0 1 = Morse.pathLength (incl hN ∘ γ) 0 1 := arcLen_eq γ 0 1
  have e2 : arcLen (n := n) (lift c' (γ 0)) 0 1 =
      Morse.pathLength (incl hN ∘ lift c' (γ 0)) 0 1 := arcLen_eq _ 0 1
  rw [e1, e2] at this
  rwa [pathLength_congr zero_le_one heq'] at this

theorem finrank_tangent (x : Bridge.Sub hN) : finrank ℝ (Morse.tangentSubspace hN x) = n := by
  have := Morse.finrank_tanAt hN x.2
  rwa [Morse.tanAt_of_mem hN x.2, finrank_euclideanSpace_fin] at this

open Bundle in
/-- Blind Ricci lower bound (induced connection) ⇒ the project's `RicciLowerBound`. -/
theorem ricciLowerBound_of {r : ℝ}
    (h : RicciGE (Bridge.conn (hN := hN)) (((n : ℝ) - 1) / r ^ 2)) :
    Morse.RicciLowerBound hN r := by
  intro q U hU
  let x : Bridge.Sub hN := q
  have e : (⟨D hN x (L hN x U), D_mem x _⟩ : Morse.tangentSubspace hN q) = U :=
    Subtype.ext (D_L U.2)
  have h1 := (h x (L hN x U) ((Bridge.norm_eq x (L hN x U)).trans (by rw [D_L U.2]; exact hU))).trans_eq
    (ricci_eq x (L hN x U))
  rw [e] at h1
  rwa [finrank_euclideanSpace_fin]


open Bundle in
/-- The project's `RicciLowerBound` ⇒ the blind Ricci lower bound (induced connection). -/
theorem ricciGE_of {r : ℝ} (h : Morse.RicciLowerBound hN r) :
    RicciGE (Bridge.conn (hN := hN)) (((n : ℝ) - 1) / r ^ 2) := by
  intro x U hU
  rw [ricci_eq]
  have h1 := h x ⟨D hN x U, D_mem x U⟩ (by
    show ‖D hN x U‖ = 1
    rw [← Bridge.norm_eq]
    exact hU)
  rwa [finrank_euclideanSpace_fin] at h1

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

end Emb

open Bundle in
/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric, connected), `cov = Bridge.conn`. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], MetricComplete n (Bridge.Sub hN) → ∀ r : ℝ, 0 < r →
    0 < ((n : ℝ) - 1) / r ^ 2 → RicciGE (Bridge.conn (hN := hN)) (((n : ℝ) - 1) / r ^ 2) →
      CompactSpace (Bridge.Sub hN) ∧ (∀ p q : Bridge.Sub hN, rho (n := n) p q ≤ Real.pi * r) ∧
      ∀ p q : Bridge.Sub hN, ∃ γ : ℝ → Bridge.Sub hN, IsMinimal (Bridge.conn (hN := hN)) γ 0 1 ∧
        γ 0 = p ∧ γ 1 = q ∧ arcLen (n := n) γ 0 1 ≤ Real.pi * r

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ hMC r hr hpos hRic =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC hMC r hr hpos hRic

/-- A for slice submanifolds modelled on `ℝⁿ`. -/
def A_Rn : Prop :=
  type_of% @Morse.IsMinimalGeodesic.isMinimalPath.{0,0,0} ∧
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
    IsPreconnected N → Morse.IsRiemComplete N → ∀ {r : ℝ}, 0 < r →
    0 < ((finrank ℝ (Rn n) : ℝ) - 1) / r ^ 2 → Morse.RicciLowerBound hN r →
      (∀ p q : N, Morse.riemDist (N := N) p q ≤ ENNReal.ofReal (Real.pi * r)) ∧ IsCompact N

theorem A_to_A_Rn : A → A_Rn := fun hA => ⟨hA.1, fun _ _ _ _ _ _ _ _ _ _ _ hpre hc _ hr hpos hRic =>
  hA.2 hpre hc hr hpos hRic⟩

open Emb Bridge in
/-- **A implies B on embedded manifolds.** Uses A's `corollary_19_5` (diameter `≤ πr`,
compactness) and `IsMinimalGeodesic.isMinimalPath`; the existence of a minimal geodesic of length
`ρ(p, q)` (Hopf–Rinow, `Morse.hopf_rinow_of_isRiemComplete`) is a project theorem outside A. -/
theorem A_Rn_to_B_emb : A_Rn → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ hMC r hr hpos hRic
  have hpre : IsPreconnected N :=
    isPreconnected_iff_preconnectedSpace.2 (inferInstance : PreconnectedSpace (Bridge.Sub hN))
  have hcomplete : Morse.IsRiemComplete N := (metricComplete_iff hpre).1 hMC
  have hpos' : 0 < ((finrank ℝ (Rn n) : ℝ) - 1) / r ^ 2 := by rwa [finrank_euclideanSpace_fin]
  obtain ⟨hdist, hcpt⟩ := hA.2 V W n N hN hpre hcomplete hr hpos' (ricciLowerBound_of hRic)
  have hπr : 0 ≤ Real.pi * r := by positivity
  refine ⟨isCompact_iff_compactSpace.1 hcpt, fun p q => ?_, fun p q => ?_⟩
  · have e : rho (n := n) p q = RoundTrip.BridgePrelude.rho (n := n) p q := rfl
    rw [e, rho_eq]
    exact ENNReal.toReal_le_of_le_ofReal hπr (hdist p q)
  · -- a minimal geodesic of length `ρ(p, q)` (Hopf–Rinow), lifted to `↥N`
    obtain ⟨γ, hγmin, hγ0, hγ1, hρ⟩ := (Morse.hopf_rinow_of_isRiemComplete hN hpre hcomplete).2.2.1 p q
    obtain ⟨hγp, hunb, -⟩ := hA.1 hγmin
    have hc : Morse.IsSmoothCurveIn hN γ := ⟨hunb.1, fun t ht => hγp.2.1 t ht⟩
    obtain ⟨hgeo, heq⟩ := isGeodesic_lift hc hunb.2 p
    have h0 : lift γ p 0 = p := Subtype.ext ((heq ⟨le_rfl, zero_le_one⟩).trans hγ0)
    have h1 : lift γ p 1 = q := Subtype.ext ((heq ⟨zero_le_one, le_rfl⟩).trans hγ1)
    have hlen : arcLen (n := n) (lift γ p) 0 1 = Morse.pathLength γ 0 1 :=
      (arcLen_eq (lift γ p) 0 1).trans (pathLength_congr zero_le_one heq)
    refine ⟨lift γ p, ⟨hgeo, fun pw a' b' hab hpw hpa hpb => ?_⟩, h0, h1, ?_⟩
    · rw [hlen]
      have e : arcLen (n := n) pw a' b' = Morse.pathLength (incl hN ∘ pw) a' b' := arcLen_eq pw a' b'
      rw [e]
      refine hγmin.2.2 (incl hN ∘ pw) a' b' (isPiecewiseSmooth_of_isPW hpw) (fun t _ => (pw t).2)
        ?_ ?_
      · show incl hN (pw a') = γ 0
        rw [hpa, h0, hγ0]; rfl
      · show incl hN (pw b') = γ 1
        rw [hpb, h1, hγ1]; rfl
    · rw [hlen]
      have := hρ.symm.trans_le (hdist p q)
      exact (ENNReal.ofReal_le_ofReal_iff hπr).1 this

/-- **A implies B on embedded manifolds** (through A's `ℝⁿ`-model part). -/
theorem A_to_B_emb : A → B_emb := fun hA => A_Rn_to_B_emb (A_to_A_Rn hA)

#rt_check RoundTrip.V11_13.A_to_B_emb [Morse.IsMinimalGeodesic.isMinimalPath, Morse.corollary_19_5]
#rt_overlap RoundTrip.V11_13.A_to_B_emb [Morse.IsMinimalGeodesic.isMinimalPath, Morse.corollary_19_5]

/-! ## `B ⇒ A` for the model `ℝⁿ`

`A_Rn`: A with the model `Z = ℝⁿ`.  Its first clause (`IsMinimalGeodesic.isMinimalPath`) is
vocabulary and is re-proved outright; its second clause (Corollary 19.5) follows from `B_emb`
through the dictionary (empty `N` separately).  For a general model `Z`, transporting
`Morse.RicciLowerBound` along `Z ≃ ℝᵐ` (`isSliceRn` of Items/V7_28.lean) would need the
chart-independence of `Morse.dN`/`Morse.curvOp` (not available); no new mathematics. -/

/-- The project's `IsMinimalGeodesic.isMinimalPath`, re-proved outright (vocabulary glue). -/
theorem isMinimalPath_outright {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {γ : ℝ → V}
    (h : Morse.IsMinimalGeodesic hN γ 0 1) :
    γ ∈ Morse.pathSpace N (γ 0) (γ 1) ∧ Morse.IsUnbrokenGeodesic hN γ ∧
      Morse.IsMinimalPath N γ (γ 0) (γ 1) := by
  obtain ⟨-, ⟨s, hsub, hgeo⟩, hmin⟩ := h
  have hγ : γ ∈ Morse.pathSpace N (γ 0) (γ 1) :=
    ⟨Morse.IsPiecewiseSmooth.of_contDiffOn hgeo.contDiffOn zero_le_one hsub,
      fun t ht => hgeo.mem t (hsub ht), rfl, rfl⟩
  exact ⟨hγ, ⟨hgeo.contDiffOn.mono hsub, hgeo.mono isOpen_Ioo (Ioo_subset_Icc_self.trans hsub)⟩,
    hγ, fun c hc => hmin c 0 1 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2⟩

open Emb Bridge in
/-- **B on embedded manifolds implies A for the model `ℝⁿ`** (B_emb used for Corollary 19.5). -/
theorem B_emb_to_A_Rn : B_emb → A_Rn := by
  intro hB
  refine ⟨@isMinimalPath_outright, ?_⟩
  intro V _ _ _ W _ _ _ n N hN hpre hcomplete r hr hpos hRic
  rcases N.eq_empty_or_nonempty with hN0 | ⟨x₀, hx₀⟩
  · subst hN0
    exact ⟨fun p => absurd p.2 (Set.notMem_empty _), isCompact_empty⟩
  have : ConnectedSpace (Bridge.Sub hN) :=
    isConnected_iff_connectedSpace.1 ⟨⟨x₀, hx₀⟩, hpre⟩
  have hpos' : 0 < ((n : ℝ) - 1) / r ^ 2 := by rwa [finrank_euclideanSpace_fin] at hpos
  obtain ⟨hcpt, hdist, -⟩ := hB V W n N hN ((metricComplete_iff hpre).2 hcomplete) r hr
    hpos' (ricciGE_of hRic)
  refine ⟨fun p q => ?_, isCompact_iff_compactSpace.2 hcpt⟩
  have h := riemDist_eq_ofReal_rho (hN := hN) hpre p q
  exact h.trans_le (ENNReal.ofReal_le_ofReal (hdist p q))

/-- **B implies A for the model `ℝⁿ`**. -/
theorem B_to_A_Rn : B → A_Rn := fun hB => B_emb_to_A_Rn (B_to_B_emb hB)

#rt_check RoundTrip.V11_13.B_to_A_Rn [Morse.IsMinimalGeodesic.isMinimalPath, Morse.corollary_19_5]
#rt_overlap RoundTrip.V11_13.B_to_A_Rn [Morse.IsMinimalGeodesic.isMinimalPath, Morse.corollary_19_5]

/-- On embedded manifolds (model `ℝⁿ`), B and A coincide. -/
theorem B_emb_iff_A_Rn : B_emb ↔ A_Rn := ⟨B_emb_to_A_Rn, A_Rn_to_B_emb⟩

end RoundTrip.V11_13
