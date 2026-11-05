import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_29
import RoundTrip.Bridge

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V7_29

/-- The project's statement (universes instantiated at 0): for a slice submanifold `N ⊆ V` with the
induced metric, connected (`IsPreconnected`) and nonempty, the TFAE of (1) `(N, riemDist)` complete
(`IsRiemComplete`, ℝ≥0∞-valued `ρ`), (2) geodesically complete (`exp_q` defined on all of `T_qN`
for every `q`), (3) `exp_p` defined on all of `T_pN` for one `p`, (4) every `ρ`-bounded set has
compact closure contained in `N`; for complete connected `N`: geodesic completeness, extension of
every geodesic to `ℝ`, a minimal geodesic of length `ρ(p, q)` joining any two points, closed
bounded subsets compact; and the Heine–Borel step "(4) ⇒ closed bounded subsets of `N` are
compact" (for any `N ⊆ V`). -/
def A : Prop :=
  type_of% @Morse.hopf_rinow.{0,0,0} ∧
    type_of% @Morse.hopf_rinow_of_isRiemComplete.{0,0,0} ∧
    type_of% @Morse.isCompact_of_isClosed_of_isRiemBounded.{0}

theorem A_holds : A :=
  ⟨@Morse.hopf_rinow, @Morse.hopf_rinow_of_isRiemComplete,
    @Morse.isCompact_of_isClosed_of_isRiemBounded⟩

/-! Neither `A → B` nor `B → A` is proved; see `V7_29.json`. B quantifies over abstract connected
Hausdorff `ℝⁿ`-manifolds with an arbitrary smooth Mathlib `RiemannianBundle` metric and an
arbitrary Levi-Civita `CovariantDerivative` (in Milnor's sense), while A only concerns slice
submanifolds of an inner product space with the induced metric; conversely A contains Theorem 10.9
(minimal geodesics), the bounded-sets-have-compact-closure property and the one-point criterion,
none of which is in B's two-way implication.

## The embedded special case

Below, B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold
`N ⊆ V` with model `ℝⁿ`, carrying the induced metric and the induced Levi-Civita connection
`Bridge.conn` of `RoundTrip/Bridge.lean` (`B_emb`). Through the Bridge's dictionary (geodesics,
`exp`, `ρ = riemDist`), B_emb is exactly the `(1) ⇔ (2)` clause of the project's `hopf_rinow`
(`A12`), and follows from A. -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

theorem geodComplete_iff :
    GeodComplete (n := n) (M := Bridge.Sub hN) (conn (hN := hN)) ↔ Morse.IsGeodesicallyComplete hN := by
  constructor
  · intro h q v hv
    let q' : Bridge.Sub hN := q
    obtain ⟨γ, hγ, hinit⟩ := h q' (L hN q' v)
    have hγ' : RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hN)) γ (Icc 0 1) := hγ
    obtain ⟨-, hcd, -⟩ := isGeodesic_iff.1 hγ'
    have hc : Morse.IsSmoothCurveIn hN (incl hN ∘ γ) := ⟨hcd, fun t _ => (γ t).2⟩
    obtain ⟨η, hη, hray, heq⟩ := Morse.exists_initial_ray (hN := hN) hc (isGeodesicOn_Ioo hγ')
    set g : ℝ → V := fun t => Morse.exp hN ((incl hN ∘ γ) 0)
      (t • Morse.velAlong (incl hN ∘ γ) 0) with hg
    have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have h0J : (0 : ℝ) ∈ Ioo (-η) (1 + η) := ⟨by linarith, by linarith⟩
    have hγ0 : γ 0 = q' := hinit.1
    have hinit' : RoundTrip.BridgePrelude.InitData (n := n) γ (Icc 0 1) q' (L hN q' v) := hinit
    have hD := (initData_iff hγ0).1 hinit'
    rw [D_L hv] at hD
    have hderiv : deriv g 0 = v := by
      have h1 : HasDerivWithinAt (incl hN ∘ γ) (deriv g 0) (Icc 0 1) 0 :=
        (hray.hasDerivAt h0J).hasDerivWithinAt.congr (fun t ht => (heq t ht).symm)
          (heq 0 h0I).symm
      rw [← hD, D_vel (isSmoothCurve_iff.2 hcd) (uniqueDiffOn_Icc zero_lt_one) h0I]
      exact (uniqueDiffOn_Icc zero_lt_one 0 h0I).eq_deriv _ h1
        (h1.differentiableWithinAt.hasDerivWithinAt)
    refine ⟨g, η, hη, hray, ?_, hderiv⟩
    show g 0 = (q : V)
    refine (heq 0 h0I).trans ?_
    show incl hN (γ 0) = incl hN q'
    rw [hγ0]
  · intro h q w
    exact expDefined_of_mem_expDom (h q (D hN q w) (D_mem q w))

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

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    GeodComplete (n := n) (M := Bridge.Sub hN) (Bridge.conn (hN := hN)) ↔
      MetricComplete n (Bridge.Sub hN)

/-- The `(1) ⇔ (2)` clause of A's `hopf_rinow`, for slice submanifolds modelled on `ℝⁿ`. -/
def A12 : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
    IsPreconnected N → N.Nonempty → (Morse.IsRiemComplete N ↔ Morse.IsGeodesicallyComplete hN)

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

theorem A_to_A12 : A → A12 := fun hA _ _ _ _ _ _ _ _ _ _ hN hpre hne =>
  (hA.1 hN hpre hne).out 0 1

/-- **B on embedded manifolds is the `(1) ⇔ (2)` clause of A**, through the Bridge dictionary
(`Emb.geodComplete_iff`, `Emb.metricComplete_iff`). -/
theorem B_emb_iff_A12 : B_emb ↔ A12 := by
  constructor
  · intro h V _ _ _ W _ _ _ n N hN hpre hne
    have : ConnectedSpace (Bridge.Sub hN) :=
      isConnected_iff_connectedSpace.1 ⟨hne, hpre⟩
    rw [← Emb.geodComplete_iff (hN := hN), ← Emb.metricComplete_iff (hN := hN) hpre]
    exact (h V W n N hN).symm
  · intro h V _ _ _ W _ _ _ n N hN hconn
    have hpre : IsPreconnected N :=
      isPreconnected_iff_preconnectedSpace.2 (inferInstance : PreconnectedSpace (Bridge.Sub hN))
    obtain ⟨x⟩ := hconn.toNonempty
    rw [Emb.geodComplete_iff (hN := hN), Emb.metricComplete_iff (hN := hN) hpre]
    exact (h V W n N hN hpre ⟨Bridge.incl hN x, x.2⟩).symm

/-- **A implies B on embedded manifolds** (uses A's `hopf_rinow`). -/
theorem A_to_B_emb : A → B_emb := fun hA => B_emb_iff_A12.2 (A_to_A12 hA)

/-- **B implies A's `(1) ⇔ (2)` clause** (for model `ℝⁿ`), by specializing B to `↥N`. -/
theorem B_to_A12 : B → A12 := fun hB => B_emb_iff_A12.1 (B_to_B_emb hB)

#rt_check RoundTrip.V7_29.A_to_B_emb [Morse.hopf_rinow, Morse.hopf_rinow_of_isRiemComplete,
  Morse.isCompact_of_isClosed_of_isRiemBounded]
#rt_check RoundTrip.V7_29.B_to_A12 [Morse.hopf_rinow, Morse.hopf_rinow_of_isRiemComplete,
  Morse.isCompact_of_isClosed_of_isRiemBounded]
#rt_overlap RoundTrip.V7_29.B_to_A12 [Morse.hopf_rinow, Morse.hopf_rinow_of_isRiemComplete,
  Morse.isCompact_of_isClosed_of_isRiemBounded]

end RoundTrip.V7_29
