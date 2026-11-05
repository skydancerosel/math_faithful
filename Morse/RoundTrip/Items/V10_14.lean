import Morse
import RoundTrip.Check
import RoundTrip.Blind.V10_14
import RoundTrip.Bridge

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V10_14

/-- The project's statement (universes instantiated at `0`), for `B : Morse.BrokenSetup hN p q c m`
(Milnor's choices of §16 for a slice submanifold `N ⊆ V` with the induced metric; `nodes`,
`nodeVal`, `energy'`, `path` are vocabulary):
* `nodeVal_mem_nodes_of_energy_lt`: a path `γ ∈ Ω(N; p, q)` with `E(γ) < c` has its break points
  `B.nodeVal γ` in `B.nodes` (the domain `U` of `E'`), with `E'(nodeVal γ) ≤ E(γ)`;
* `exists_energy_minimizing` (Milnor's Remark p. 92): if some `γ₀ ∈ Ω(N; p, q)` has `E(γ₀) < c`,
  there are break points `y ∈ B.nodes` whose broken geodesic `B.path y` is an unbroken geodesic
  minimizing `E` over all of `Ω(N; p, q)`. -/
def A : Prop :=
  type_of% @Morse.BrokenSetup.nodeVal_mem_nodes_of_energy_lt.{0, 0, 0} ∧
    type_of% @Morse.BrokenSetup.exists_energy_minimizing.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.BrokenSetup.nodeVal_mem_nodes_of_energy_lt, @Morse.BrokenSetup.exists_energy_minimizing⟩

/-! Neither `A → B` nor `B → A` is proved: B quantifies over abstract connected Hausdorff
`ℝⁿ`-manifolds with any smooth metric and any Levi-Civita connection, A only over slice
submanifolds `N ⊆ V` with the induced metric; see `V10_14.json`.

## The embedded special case

`B_emb` is B for `M = ↥N` (model `ℝⁿ`, induced metric) and the induced connection. We prove
`A → B_emb_nc`, where `B_emb_nc` is `B_emb` without the compactness of `B^a`: A's minimizer (for a
`BrokenSetup` of ANY fine subdivision, which exists by `Morse.exists_brokenSetup_uniform`) is an
unbroken geodesic, hence lies in `B^a` for B's subdivision as well; it minimizes `E` over all of
`Ω`, so over `B^a`; and it is a minimal geodesic (length-minimizing) because a minimal geodesic of
Hopf–Rinow (project, outside the item) has energy `L² = ρ²`, so `L(γ)² = E(γ) ≤ ρ²`.
The compactness of `B^a` (for B's `Setup16` subdivision) is not in A. -/

namespace Emb

set_option linter.unusedSectionVars false

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-! Distances and completeness on `↥N` (copied from `Items/V10_4.lean` / `V7_29.lean`). -/

theorem riemDist_eq_ofReal_rho (hpre : IsPreconnected N) (p q : Bridge.Sub hN) :
    Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q) =
      ENNReal.ofReal (rho (n := n) p q) := by
  have e : rho (n := n) p q = RoundTrip.BridgePrelude.rho (n := n) p q := rfl
  rw [e, Bridge.rho_eq]
  exact (ENNReal.ofReal_toReal (Morse.riemDist_ne_top hN hpre p.2 q.2)).symm

theorem rho_nonneg (p q : Bridge.Sub hN) : 0 ≤ rho (n := n) p q := by
  have e : rho (n := n) p q = RoundTrip.BridgePrelude.rho (n := n) p q := rfl
  rw [e, Bridge.rho_eq]
  exact ENNReal.toReal_nonneg

theorem rho_lt_iff (hpre : IsPreconnected N) (p q : Bridge.Sub hN) {ε : ℝ} (hε : 0 < ε) :
    rho (n := n) p q < ε ↔
      Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q) < ENNReal.ofReal ε := by
  rw [riemDist_eq_ofReal_rho hpre, ENNReal.ofReal_lt_ofReal_iff hε]

theorem metricComplete_iff (hpre : IsPreconnected N) :
    MetricComplete n (Bridge.Sub hN) ↔ Morse.IsRiemComplete N := by
  constructor
  · intro h x hx hcau
    let x' : ℕ → Bridge.Sub hN := fun k => ⟨x k, hx k⟩
    obtain ⟨p, hp⟩ := h x' fun ε hε => by
      obtain ⟨n₀, hn₀⟩ := hcau ε hε
      exact ⟨n₀, fun m hm k hk => (rho_lt_iff hpre _ _ hε).2 (hn₀ m hm k hk)⟩
    refine ⟨Bridge.incl hN p, p.2, ?_⟩
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
    obtain ⟨y, hy, hlim⟩ := h (fun k => Bridge.incl hN (x k)) (fun k => (x k).2) fun ε hε => by
      obtain ⟨n₀, hn₀⟩ := hcau ε hε
      exact ⟨n₀, fun m hm k hk => (rho_lt_iff hpre _ _ hε).1 (hn₀ m hm k hk)⟩
    refine ⟨⟨y, hy⟩, fun ε hε => ?_⟩
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
      (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε)))
    exact ⟨n₀, fun m hm => (rho_lt_iff hpre _ _ hε).2 (hn₀ m hm)⟩

/-- A blind path of `Ω(↥N; p, q)` is, in `V`, a project path of `Ω(N; p, q)`. -/
theorem mem_pathSpace {p q : Bridge.Sub hN} {w : ℝ → Bridge.Sub hN}
    (hw : InOmega (n := n) p q w) :
    Bridge.incl hN ∘ w ∈ Morse.pathSpace N (Bridge.incl hN p) (Bridge.incl hN q) :=
  ⟨Bridge.isPiecewiseSmooth_of_isPW hw.1, fun t _ => (w t).2, congrArg (Bridge.incl hN) hw.2.1,
    congrArg (Bridge.incl hN) hw.2.2⟩

/-! Geodesics (copied from `Items/V9_10.lean`). -/

theorem prj_incl (x : Bridge.Sub hN) : Morse.prj hN (Bridge.incl hN x) = Bridge.P hN x :=
  Morse.prj_of_mem hN x.2

theorem isIntv_Icc : RoundTrip.BridgePrelude.IsIntv (Icc (0 : ℝ) 1) :=
  ⟨ordConnected_Icc, uniqueDiffOn_Icc zero_lt_one⟩

theorem derivWithin_eventuallyEq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} (hF : ContDiffOn ℝ ∞ F (Icc 0 1)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    derivWithin F (Icc 0 1) =ᶠ[𝓝 t] deriv F := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
  exact ((hF.contDiffAt (Icc_mem_nhds hx.1 hx.2)).differentiableAt (by simp)).hasDerivAt
    |>.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one x (Ioo_subset_Icc_self hx))

/-- A smooth curve in `N` on `[0, 1]` which is a geodesic on `(0, 1)` lifts to a blind geodesic of
the induced connection on the closed interval `[0, 1]`. -/
theorem isGeodesic_lift {γ : ℝ → V} (hc : Morse.IsSmoothCurveIn hN γ)
    (hg : Morse.IsGeodesicOn hN γ (Ioo 0 1)) (q : Bridge.Sub hN) :
    IsGeodesic (Bridge.conn (hN := hN)) (Bridge.lift γ q) (Icc 0 1) ∧
      EqOn (Bridge.incl hN ∘ Bridge.lift γ q) γ (Icc 0 1) := by
  have hu := uniqueDiffOn_Icc (zero_lt_one' ℝ)
  have heq : EqOn (Bridge.incl hN ∘ Bridge.lift γ q) γ (Icc 0 1) :=
    fun t ht => Bridge.incl_lift q (hc.mem t ht)
  refine ⟨?_, heq⟩
  have h : RoundTrip.BridgePrelude.IsGeodesic (Bridge.conn (hN := hN)) (Bridge.lift γ q)
      (Icc 0 1) := by
    refine Bridge.isGeodesic_iff.2 ⟨isIntv_Icc, hc.contDiffOn.congr heq, fun t ht => ?_⟩
    have hd1 : EqOn (derivWithin (Bridge.incl hN ∘ Bridge.lift γ q) (Icc 0 1))
        (derivWithin γ (Icc 0 1)) (Icc 0 1) := fun s hs => derivWithin_congr heq (heq hs)
    rw [derivWithin_congr hd1 (hd1 ht)]
    have hP : Bridge.P hN (Bridge.lift γ q t) = Morse.prj hN (γ t) := by
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

/-- A blind geodesic on `[0, 1]` is a blind geodesic on every `[a, b] ⊆ [0, 1]`, `a < b`. -/
theorem isGeodesic_mono {γ : ℝ → Bridge.Sub hN}
    (h : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {a b : ℝ} (hab : a < b) (ha : 0 ≤ a)
    (hb : b ≤ 1) : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc a b) := by
  have h' : RoundTrip.BridgePrelude.IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1) := h
  obtain ⟨-, hc, hP⟩ := Bridge.isGeodesic_iff.1 h'
  have hsub : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha hb
  have hu := uniqueDiffOn_Icc hab
  have hu01 := uniqueDiffOn_Icc (zero_lt_one' ℝ)
  have hd1 : EqOn (derivWithin (Bridge.incl hN ∘ γ) (Icc a b))
      (derivWithin (Bridge.incl hN ∘ γ) (Icc 0 1)) (Icc a b) := fun x hx =>
    derivWithin_subset hsub (hu x hx) (((hc.of_le (by simp)).differentiableOn one_ne_zero) x (hsub hx))
  have hc' : ContDiffOn ℝ 1 (derivWithin (Bridge.incl hN ∘ γ) (Icc 0 1)) (Icc 0 1) :=
    hc.derivWithin hu01 (WithTop.coe_le_coe.2 le_top)
  have g : RoundTrip.BridgePrelude.IsGeodesic (Bridge.conn (hN := hN)) γ (Icc a b) := by
    refine Bridge.isGeodesic_iff.2 ⟨⟨ordConnected_Icc, hu⟩, hc.mono hsub, fun s hs => ?_⟩
    rw [derivWithin_congr hd1 (hd1 hs),
      derivWithin_subset hsub (hu s hs) ((hc'.differentiableOn one_ne_zero) s (hsub hs))]
    exact hP s (hsub hs)
  exact g

/-- A blind geodesic on `[0, 1]` is a blind piecewise smooth path on `[0, 1]`. -/
theorem isPW_of_isGeodesic {γ : ℝ → Bridge.Sub hN}
    (h : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) : IsPW (n := n) γ 0 1 := by
  refine ⟨1, fun i => (i : ℝ), by simp, by simp, fun i _ => by push_cast; linarith,
    fun i hi => ?_⟩
  have hi0 : i = 0 := by omega
  subst hi0
  have h2 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) ∞ γ (Icc 0 1) := h.2.1
  simpa using h2

/-- On `↥N`, a blind geodesic on `[0, 1]` is (in `V`) a project unbroken geodesic. -/
theorem isUnbrokenGeodesic_of_isGeodesic {γ : ℝ → Bridge.Sub hN}
    (h : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) :
    Morse.IsUnbrokenGeodesic hN (Bridge.incl hN ∘ γ) := by
  have h' : RoundTrip.BridgePrelude.IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1) := h
  exact ⟨(Bridge.isGeodesic_iff.1 h').2.1, Bridge.isGeodesicOn_Ioo h'⟩

end Emb

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric), the induced Levi-Civita
connection `Bridge.conn`. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], MetricComplete n (Bridge.Sub hN) →
  ∀ (p q : Bridge.Sub hN) (c ε : ℝ) (k : ℕ) (t : ℕ → ℝ),
    Setup16 n (Bridge.conn (hN := hN)) p q c ε k t →
    ∀ a : ℝ, a < c → (∃ w, w ∈ OmLe n p q a) →
      (BsetA n (Bridge.conn (hN := hN)) p q c k t a).Nonempty ∧
      IsCompact (BsetA n (Bridge.conn (hN := hN)) p q c k t a) ∧
      ∃ γ ∈ BsetA n (Bridge.conn (hN := hN)) p q c k t a,
        (∀ w ∈ BsetA n (Bridge.conn (hN := hN)) p q c k t a, Efun (n := n) γ.1 ≤ Efun (n := n) w.1) ∧
        IsMinimal (Bridge.conn (hN := hN)) γ.1 0 1 ∧ γ.1 0 = p ∧ γ.1 1 = q

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- `B_emb` without the compactness of `B^a`. -/
def B_emb_nc : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], MetricComplete n (Bridge.Sub hN) →
  ∀ (p q : Bridge.Sub hN) (c ε : ℝ) (k : ℕ) (t : ℕ → ℝ),
    Setup16 n (Bridge.conn (hN := hN)) p q c ε k t →
    ∀ a : ℝ, a < c → (∃ w, w ∈ OmLe n p q a) →
      (BsetA n (Bridge.conn (hN := hN)) p q c k t a).Nonempty ∧
      ∃ γ ∈ BsetA n (Bridge.conn (hN := hN)) p q c k t a,
        (∀ w ∈ BsetA n (Bridge.conn (hN := hN)) p q c k t a, Efun (n := n) γ.1 ≤ Efun (n := n) w.1) ∧
        IsMinimal (Bridge.conn (hN := hN)) γ.1 0 1 ∧ γ.1 0 = p ∧ γ.1 1 = q

theorem B_emb_to_B_emb_nc : B_emb → B_emb_nc := fun h V _ _ _ W _ _ _ n N hN _ hmc p q c ε k t hS
    a ha hw => ⟨(h V W n N hN hmc p q c ε k t hS a ha hw).1, (h V W n N hN hmc p q c ε k t hS a ha hw).2.2⟩

/-- The common core: an energy-minimizing unbroken geodesic `σ` of `Ω(N; p, q)` gives B's minimizer
in `B^a` (for B's subdivision), a minimal geodesic. The length minimality uses the project's
Hopf–Rinow theorem (outside the item). -/
theorem conclusion_of_minimizer {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {n : ℕ} {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}
    (hpre : IsPreconnected N) (hRC : Morse.IsRiemComplete N)
    {p q : Bridge.Sub hN} {c ε : ℝ} {k : ℕ} {t : ℕ → ℝ}
    (hS16 : Setup16 n (Bridge.conn (hN := hN)) p q c ε k t) {a : ℝ} (ha : a < c)
    (w₀ : Om n p q) (hw₀a : Efun (n := n) w₀.1 ≤ a) {σ : ℝ → V}
    (hσ : σ ∈ Morse.pathSpace N (Bridge.incl hN p) (Bridge.incl hN q))
    (hgeo : Morse.IsUnbrokenGeodesic hN σ)
    (hmin : ∀ γ ∈ Morse.pathSpace N (Bridge.incl hN p) (Bridge.incl hN q),
      Morse.energy σ 0 1 ≤ Morse.energy γ 0 1) :
    (BsetA n (Bridge.conn (hN := hN)) p q c k t a).Nonempty ∧
      ∃ γ ∈ BsetA n (Bridge.conn (hN := hN)) p q c k t a,
        (∀ w ∈ BsetA n (Bridge.conn (hN := hN)) p q c k t a, Efun (n := n) γ.1 ≤ Efun (n := n) w.1) ∧
        IsMinimal (Bridge.conn (hN := hN)) γ.1 0 1 ∧ γ.1 0 = p ∧ γ.1 1 = q := by
  obtain ⟨-, -, -, ht0, htk, hlt, -⟩ := hS16
  have hγ₀ := Emb.mem_pathSpace w₀.2
  have hEw : ∀ w : ℝ → Bridge.Sub hN,
      Morse.energy (Bridge.incl hN ∘ w) 0 1 = Efun (n := n) w := fun w =>
    (Bridge.energy_eq w 0 1).symm
  obtain ⟨hg, heq⟩ := Emb.isGeodesic_lift (Morse.IsUnbrokenGeodesic.isSmoothCurveIn hN hσ hgeo)
    hgeo.2 p
  set γ := Bridge.lift σ p with hγdef
  have hγ0 : γ 0 = p := Subtype.ext ((heq ⟨le_rfl, zero_le_one⟩).trans hσ.2.2.1)
  have hγ1 : γ 1 = q := Subtype.ext ((heq ⟨zero_le_one, le_rfl⟩).trans hσ.2.2.2)
  have hΩ : InOmega (n := n) p q γ := ⟨Emb.isPW_of_isGeodesic hg, hγ0, hγ1⟩
  have hEγ : Efun (n := n) γ = Morse.energy σ 0 1 := by
    rw [← hEw]; exact Morse.energy_congr heq
  have hEγa : Efun (n := n) γ ≤ a := by
    rw [hEγ]; exact (hmin _ hγ₀).trans (by rw [hEw]; exact hw₀a)
  have hti : ∀ i < k, 0 ≤ t i ∧ t (i + 1) ≤ 1 := fun i hi =>
    ⟨ht0 ▸ Bridge.le_of_strictSeq hlt (Nat.zero_le i) hi.le,
      htk ▸ Bridge.le_of_strictSeq hlt hi le_rfl⟩
  let γΩ : Om n p q := ⟨γ, hΩ⟩
  have hmem : γΩ ∈ BsetA n (Bridge.conn (hN := hN)) p q c k t a :=
    ⟨⟨⟨hΩ, fun i hi => Emb.isGeodesic_mono hg (hlt i hi) (hti i hi).1 (hti i hi).2⟩,
      lt_of_le_of_lt hEγa ha⟩, hEγa⟩
  refine ⟨⟨γΩ, hmem⟩, γΩ, hmem, fun w _ => ?_, ⟨hg, ?_⟩, hγ0, hγ1⟩
  · show Efun (n := n) γ ≤ Efun (n := n) w.1
    rw [hEγ, ← hEw]
    exact hmin _ (Emb.mem_pathSpace w.2)
  · -- minimality of length
    intro pw a' b' _ hpw hpa hpb
    obtain ⟨σ', hσ'm, hσ'0, hσ'1, -⟩ := (Morse.hopf_rinow_of_isRiemComplete hN hpre hRC).2.2.1 p q
    obtain ⟨hσ'mem, hσ'geo, -⟩ := hσ'm.isMinimalPath
    rw [hσ'0, hσ'1] at hσ'mem
    have hγmem := Emb.mem_pathSpace hΩ
    have hγgeo := Emb.isUnbrokenGeodesic_of_isGeodesic hg
    have h1 : Morse.energy (Bridge.incl hN ∘ γ) 0 1 ≤ Morse.energy σ' 0 1 := by
      rw [hEw, hEγ]; exact hmin _ hσ'mem
    rw [Morse.energy_eq_pathLength_sq_of_geodesic hγmem hγgeo,
      Morse.energy_eq_pathLength_sq_of_geodesic hσ'mem hσ'geo] at h1
    have h2 : Morse.pathLength (Bridge.incl hN ∘ γ) 0 1 ≤ Morse.pathLength σ' 0 1 :=
      (pow_le_pow_iff_left₀ hγmem.1.isAdmissible.pathLength_nonneg
        hσ'mem.1.isAdmissible.pathLength_nonneg two_ne_zero).1 h1
    have h3 : Morse.pathLength σ' 0 1 ≤ Morse.pathLength (Bridge.incl hN ∘ pw) a' b' :=
      hσ'm.2.2 _ a' b' (Bridge.isPiecewiseSmooth_of_isPW hpw) (fun s _ => (pw s).2)
        (by rw [hσ'0]; exact congrArg (Bridge.incl hN) (hpa.trans hγ0))
        (by rw [hσ'1]; exact congrArg (Bridge.incl hN) (hpb.trans hγ1))
    have e1 : arcLen (n := n) γ 0 1 = Morse.pathLength (Bridge.incl hN ∘ γ) 0 1 :=
      Bridge.arcLen_eq γ 0 1
    have e2 : arcLen (n := n) pw a' b' = Morse.pathLength (Bridge.incl hN ∘ pw) a' b' :=
      Bridge.arcLen_eq pw a' b'
    show arcLen (n := n) γ 0 1 ≤ arcLen (n := n) pw a' b'
    rw [e1, e2]
    exact h2.trans h3

/-- **A gives B on `↥N`, except the compactness of `B^a`.** The minimizer is A's
`exists_energy_minimizing` (for a `BrokenSetup` of some uniform subdivision, which exists by
`Morse.exists_brokenSetup_uniform`). -/
theorem A_to_B_emb_nc : A → B_emb_nc := by
  intro hA V _ _ _ W _ _ _ n N hN _ hmc p q c ε k t hS16 a ha hw0
  have hpre : IsPreconnected N :=
    isPreconnected_iff_preconnectedSpace.2 (inferInstance : PreconnectedSpace (Bridge.Sub hN))
  have hRC : Morse.IsRiemComplete N := (Emb.metricComplete_iff hpre).1 hmc
  have hc : 0 < c := hS16.1
  have hS : IsCompact (Morse.closedRiemBall N (Bridge.incl hN p) (Real.sqrt c)) :=
    Morse.isCompact_closedRiemBall_of_isRiemComplete hN hpre hRC _ _
  obtain ⟨m, ⟨Bs⟩⟩ := Morse.exists_brokenSetup_uniform hN (q := Bridge.incl hN q) p.2 q.2 hc hS
  obtain ⟨w₀, hw₀⟩ := hw0
  have hw₀a : Efun (n := n) w₀.1 ≤ a := hw₀
  have hE : Morse.energy (Bridge.incl hN ∘ w₀.1) 0 1 < c := by
    have e : Morse.energy (Bridge.incl hN ∘ w₀.1) 0 1 = Efun (n := n) w₀.1 :=
      (Bridge.energy_eq w₀.1 0 1).symm
    rw [e]; exact lt_of_le_of_lt hw₀a ha
  obtain ⟨y, hy, hgeo, hmin⟩ := hA.2 Bs (Emb.mem_pathSpace w₀.2) hE
  exact conclusion_of_minimizer hpre hRC hS16 ha w₀ hw₀a (Bs.path_mem_pathSpace hy) hgeo hmin

/-- **`B_emb_nc` is provable outright** (without A): the minimal geodesic of Hopf–Rinow minimizes
the energy (`Morse.energy_le_of_isMinimalPath`), so it serves as the minimizer. Hence on `↥N`
the only part of the Remark that is not already a consequence of Hopf–Rinow is the compactness of
`B^a`, which A does not give. -/
theorem B_emb_nc_outright : B_emb_nc := by
  intro V _ _ _ W _ _ _ n N hN _ hmc p q c ε k t hS16 a ha hw0
  have hpre : IsPreconnected N :=
    isPreconnected_iff_preconnectedSpace.2 (inferInstance : PreconnectedSpace (Bridge.Sub hN))
  have hRC : Morse.IsRiemComplete N := (Emb.metricComplete_iff hpre).1 hmc
  obtain ⟨w₀, hw₀⟩ := hw0
  obtain ⟨σ', hσ'm, hσ'0, hσ'1, -⟩ := (Morse.hopf_rinow_of_isRiemComplete hN hpre hRC).2.2.1 p q
  obtain ⟨hσ'mem, hσ'geo, hσ'min⟩ := hσ'm.isMinimalPath
  rw [hσ'0, hσ'1] at hσ'mem hσ'min
  exact conclusion_of_minimizer hpre hRC hS16 ha w₀ hw₀ hσ'mem hσ'geo
    fun γ hγ => Morse.energy_le_of_isMinimalPath hN hσ'min hσ'geo hγ

#rt_check RoundTrip.V10_14.A_to_B_emb_nc [Morse.BrokenSetup.nodeVal_mem_nodes_of_energy_lt,
  Morse.BrokenSetup.exists_energy_minimizing]
#rt_overlap RoundTrip.V10_14.A_to_B_emb_nc [Morse.BrokenSetup.nodeVal_mem_nodes_of_energy_lt,
  Morse.BrokenSetup.exists_energy_minimizing]
#rt_check RoundTrip.V10_14.B_emb_nc_outright [Morse.BrokenSetup.nodeVal_mem_nodes_of_energy_lt,
  Morse.BrokenSetup.exists_energy_minimizing]

end RoundTrip.V10_14
