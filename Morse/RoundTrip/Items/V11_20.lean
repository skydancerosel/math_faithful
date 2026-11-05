import Morse
import RoundTrip.Check
import RoundTrip.Blind.V11_20
import RoundTrip.Bridge

/-! # Round trip for V11_20 (Milnor §19, p. 103: each homotopy class contains one geodesic)

`A` (universes `0`; `Morse.pathOfMem` is vocabulary): `Morse.homotopy_class_unique_geodesic`: for
a slice submanifold `N ⊆ V` with the induced metric, geodesically complete with
`⟨R(A,B)A,B⟩ ≤ 0`, and any `p, q ∈ N`, every path `c` from `p` to `q` is homotopic (rel end points)
to an unbroken geodesic of `Ω(N; p, q)`, and two such geodesics agree on `[0, 1]`.

`B`: the same on every abstract connected Hausdorff Riemannian `ℝⁿ`-manifold with a Levi-Civita
connection, Milnor-complete, `⟨R(A,B)A,B⟩ ≤ 0`, and NOT simply connected (Milnor's hypothesis).

Neither direction (setting). Embedded special case: `A_to_B_emb` and `B_emb_to_A_nsc` (A for
connected, non-simply-connected `N` with model `ℝⁿ`). -/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace unitInterval

namespace RoundTrip.V11_20

def A : Prop := type_of% @Morse.homotopy_class_unique_geodesic.{0,0,0}

theorem A_holds : A := @Morse.homotopy_class_unique_geodesic

/-! ### Glue (copied from Items/V11_17.lean) -/

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

/-! ### Dictionary: the homotopy class of a blind geodesic -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- A blind geodesic `g` (read in `V`) lies in the class of `c` iff the project's path
`pathOfMem` of `incl ∘ g` is homotopic to `c`. -/
theorem inClass_iff {p q : Bridge.Sub hN} {g : ℝ → Bridge.Sub hN}
    (hg : incl hN ∘ g ∈ Morse.pathSpace N (incl hN p) (incl hN q)) (c : Path p q) :
    InClass g c ↔ (Morse.pathOfMem (p := p) (q := q) hg).Homotopic c := by
  constructor
  · rintro ⟨h, hh, hc⟩
    have : Morse.pathOfMem (p := p) (q := q) hg = h := by
      ext t
      exact congrArg Subtype.val (hh t).symm
    rw [this]
    exact hc
  · intro hc
    exact ⟨Morse.pathOfMem (p := p) (q := q) hg, fun t => rfl, hc⟩

/-- For a project path `γ` and a blind `g` agreeing with it on `[0, 1]`, the two project paths are
equal. -/
theorem pathOfMem_congr {p q : N} {γ γ' : ℝ → V} (hγ : γ ∈ Morse.pathSpace N p q)
    (hγ' : γ' ∈ Morse.pathSpace N p q) (h : EqOn γ γ' (Icc 0 1)) :
    Morse.pathOfMem hγ = Morse.pathOfMem hγ' := by
  ext t
  exact h t.2

end Emb

/-! ### The embedded special case -/

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric), `cov = Bridge.conn`. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    MetricComplete n (Bridge.Sub hN) → NonPosCurv n (Bridge.conn (hN := hN)) →
    ¬ SimplyConnectedSpace (Bridge.Sub hN) →
    ∀ p q : Bridge.Sub hN, ∀ c : Path p q, ∃ g : ℝ → Bridge.Sub hN,
      IsGeodPQ n (Bridge.conn (hN := hN)) p q g ∧ InClass g c ∧
      ∀ g' : ℝ → Bridge.Sub hN, IsGeodPQ n (Bridge.conn (hN := hN)) p q g' → InClass g' c →
        Set.EqOn g g' (Set.Icc 0 1)

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds** (without using `¬ SimplyConnectedSpace`). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ hmc hK _ p q c
  have hc := Emb.complete_of_metricComplete hmc
  obtain ⟨⟨γ, hγ, hgeo, hhom⟩, huniq⟩ := hA hc (Emb.nonPosCurv_iff.1 hK) (p := p) (q := q) c
  obtain ⟨hpq, heq⟩ := Emb.geodPQ_of_unbroken (p := p) (q := q) hγ hgeo
  obtain ⟨hmem, -⟩ := Emb.unbroken_of_geodPQ hpq
  refine ⟨_, hpq, ?_, fun g' hg' hcl' t ht => ?_⟩
  · rw [Emb.inClass_iff hmem]
    rw [Emb.pathOfMem_congr hmem hγ heq]
    exact hhom
  · obtain ⟨hmem', hgeo'⟩ := Emb.unbroken_of_geodPQ hg'
    have h1 := (Emb.inClass_iff hmem' c).1 hcl'
    have h2 := huniq _ _ hγ hmem' hgeo hgeo' hhom h1
    exact Subtype.ext ((heq ht).trans (h2 ht))

/-- The part of A that `B_emb` covers: connected, NOT simply connected `N` with model `ℝⁿ`. -/
def A_nsc : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
    ConnectedSpace N → ¬ SimplyConnectedSpace N →
    Morse.IsGeodesicallyComplete hN → Morse.NonposCurvature hN → ∀ {p q : N} (c : Path p q),
    (∃ γ : ℝ → V, ∃ hγ : γ ∈ Morse.pathSpace N p q, Morse.IsUnbrokenGeodesic hN γ ∧
      (Morse.pathOfMem hγ).Homotopic c) ∧
    ∀ (γ γ' : ℝ → V) (hγ : γ ∈ Morse.pathSpace N p q) (hγ' : γ' ∈ Morse.pathSpace N p q),
      Morse.IsUnbrokenGeodesic hN γ → Morse.IsUnbrokenGeodesic hN γ' →
      (Morse.pathOfMem hγ).Homotopic c → (Morse.pathOfMem hγ').Homotopic c → EqOn γ γ' (Icc 0 1)

theorem A_to_A_nsc : A → A_nsc := fun hA _ _ _ _ _ _ _ _ _ _ _ _ _ hc hK _ _ c => hA hc hK c

/-- **B on embedded manifolds implies A for connected, non-simply-connected `N`.** -/
theorem B_emb_to_A_nsc : B_emb → A_nsc := by
  intro hB V _ _ _ W _ _ _ n N hN hconn hnsc hc hK p q c
  have : ConnectedSpace (Bridge.Sub hN) := hconn
  have h := hB V W n N hN (Emb.metricComplete_of_complete hc) (Emb.nonPosCurv_iff.2 hK) hnsc
    (p := p) (q := q) c
  obtain ⟨g, hg, hcl, huniq⟩ := h
  obtain ⟨hmem, hgeo⟩ := Emb.unbroken_of_geodPQ hg
  refine ⟨⟨_, hmem, hgeo, (Emb.inClass_iff hmem c).1 hcl⟩, ?_⟩
  intro γ γ' hγ hγ' hgeo₁ hgeo₂ hc₁ hc₂ t ht
  obtain ⟨hpq₁, heq₁⟩ := Emb.geodPQ_of_unbroken (p := p) (q := q) hγ hgeo₁
  obtain ⟨hpq₂, heq₂⟩ := Emb.geodPQ_of_unbroken (p := p) (q := q) hγ' hgeo₂
  have hm₁ := (Emb.unbroken_of_geodPQ hpq₁).1
  have hm₂ := (Emb.unbroken_of_geodPQ hpq₂).1
  have hcl₁ : InClass (Bridge.lift (hN := hN) γ (p : Bridge.Sub hN)) c := by
    refine (Emb.inClass_iff hm₁ c).2 ?_
    rw [Emb.pathOfMem_congr hm₁ hγ heq₁]; exact hc₁
  have hcl₂ : InClass (Bridge.lift (hN := hN) γ' (p : Bridge.Sub hN)) c := by
    refine (Emb.inClass_iff hm₂ c).2 ?_
    rw [Emb.pathOfMem_congr hm₂ hγ' heq₂]; exact hc₂
  have e1 := huniq _ hpq₁ hcl₁ ht
  have e2 := huniq _ hpq₂ hcl₂ ht
  rw [← heq₁ ht, ← heq₂ ht]
  show Bridge.incl hN _ = Bridge.incl hN _
  rw [← e1, ← e2]

#rt_check RoundTrip.V11_20.A_to_B_emb [Morse.homotopy_class_unique_geodesic]
#rt_check RoundTrip.V11_20.B_emb_to_A_nsc [Morse.homotopy_class_unique_geodesic]
#rt_overlap RoundTrip.V11_20.B_emb_to_A_nsc [Morse.homotopy_class_unique_geodesic]

end RoundTrip.V11_20
