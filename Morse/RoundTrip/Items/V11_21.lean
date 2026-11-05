import Morse
import RoundTrip.Check
import RoundTrip.Blind.V11_21
import RoundTrip.Bridge

/-! # Round trip for V11_21 (Milnor §19, Corollary 19.3)

`A` (universes `0`): `Morse.contractibleSpace_cube`, `Morse.isPreconnected_cube_face`,
`Morse.genLoop_homotopic_const` and `Morse.corollary_19_3`: for a slice submanifold `N ⊆ V`
(induced metric), geodesically complete, with `⟨R(A,B)A,B⟩ ≤ 0`: `πᵢ(N, x) = 0` for `i > 1`
(at every base point), via null-homotopy of generalized loops; plus two topological facts about the
cube. The project does NOT formalize the second half of Corollary 19.3 (`π₁` torsion-free).

`B`: on every abstract connected Hausdorff Riemannian `ℝⁿ`-manifold with a Levi-Civita
connection, Milnor-complete, `⟨R(A,B)A,B⟩ ≤ 0`: `πᵢ(M, x) = 0` for `i ≥ 2` AND `π₁(M, x)` has no
non-trivial element of finite order.

Neither `A → B` nor `B → A`: setting (abstract vs embedded), and `A` lacks the `π₁` half.
Embedded special case below: `B_emb` (B for `M = ↥N`, `cov = Bridge.conn`);
`A_to_B_emb_pi` (A ⇒ the `πᵢ` half of `B_emb`) and `B_emb_to_A_conn` (B_emb ⇒ A for connected
`N` with model `ℝⁿ`). -/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace unitInterval

namespace RoundTrip.V11_21

def A : Prop :=
  type_of% @Morse.contractibleSpace_cube ∧
    type_of% @Morse.isPreconnected_cube_face ∧
    type_of% @Morse.genLoop_homotopic_const.{0,0,0} ∧
    type_of% @Morse.corollary_19_3.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.contractibleSpace_cube, @Morse.isPreconnected_cube_face,
    @Morse.genLoop_homotopic_const, @Morse.corollary_19_3⟩

/-! ### Glue (copied from Items/V11_17.lean: completeness via Hopf–Rinow, curvature) -/

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

/-! ### The embedded special case -/

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric), `cov = Bridge.conn`. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    MetricComplete n (Bridge.Sub hN) → NonPosCurv n (Bridge.conn (hN := hN)) →
      (∀ (i : ℕ), 2 ≤ i → ∀ x : Bridge.Sub hN, Subsingleton (HomotopyGroup.Pi i (Bridge.Sub hN) x)) ∧
      (∀ x : Bridge.Sub hN, ∀ g : FundamentalGroup (Bridge.Sub hN) x, IsOfFinOrder g → g = 1)

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- The `πᵢ` half of `B_emb` (the part `A` can reach). -/
def B_emb_pi : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    MetricComplete n (Bridge.Sub hN) → NonPosCurv n (Bridge.conn (hN := hN)) →
      ∀ (i : ℕ), 2 ≤ i → ∀ x : Bridge.Sub hN, Subsingleton (HomotopyGroup.Pi i (Bridge.Sub hN) x)

/-- **A gives the `πᵢ` half of B on embedded manifolds** (A's `corollary_19_3` with the
completeness and curvature dictionaries). -/
theorem A_to_B_emb_pi : A → B_emb_pi := by
  intro hA V _ _ _ W _ _ _ n N hN _ hmc hK i hi x
  exact hA.2.2.2 (Emb.complete_of_metricComplete hmc) (Emb.nonPosCurv_iff.1 hK) hi x

/-- The part of `A` that `B_emb` covers: connected `N` with model `ℝⁿ`. -/
def A_conn : Prop :=
  (∀ n : ℕ, ContractibleSpace (Fin n → I)) ∧
  (∀ {n : ℕ} (i : Fin n) (a : I), IsPreconnected {y : Fin n → I | y i = a}) ∧
  (∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N), ConnectedSpace N →
    Morse.IsGeodesicallyComplete hN → Morse.NonposCurvature hN →
    (∀ {m : ℕ}, 2 ≤ m → ∀ (x : N) (γ : GenLoop (Fin m) N x), GenLoop.Homotopic γ GenLoop.const) ∧
    (∀ {i : ℕ}, 1 < i → ∀ x : N, Subsingleton (HomotopyGroup.Pi i N x)))

theorem A_to_A_conn : A → A_conn := fun hA =>
  ⟨hA.1, hA.2.1, fun _ _ _ _ _ _ _ _ _ _ _ _ hc hK =>
    ⟨fun hm x γ => hA.2.2.1 hc hK hm x γ, fun hi x => hA.2.2.2 hc hK hi x⟩⟩

/-- **B on embedded manifolds gives A for connected `N` with model `ℝⁿ`.** The cube facts are
elementary topology, proved outright (as in the project). -/
theorem B_emb_to_A_conn : B_emb → A_conn := by
  intro hB
  refine ⟨fun n => ?_, fun {n} i a => ?_, ?_⟩
  · rw [contractible_iff_id_nullhomotopic]
    refine ⟨fun _ => 0, ⟨?_⟩⟩
    exact
      { toFun := fun x i => unitInterval.symm x.1 * x.2 i
        continuous_toFun := by fun_prop
        map_zero_left := fun y => by funext i; simp
        map_one_left := fun y => by funext i; simp }
  · have e : {y : Fin n → I | y i = a} = Set.pi univ (fun k => if k = i then {a} else univ) := by
      ext y
      constructor
      · intro h k _
        by_cases hk : k = i
        · subst hk
          simpa using h
        · simp [hk]
      · intro h
        simpa using h i (mem_univ i)
    rw [e]
    exact isPreconnected_univ_pi fun k => by
      split_ifs
      exacts [isPreconnected_singleton, isPreconnected_univ]
  · intro V _ _ _ W _ _ _ n N hN hconn hc hK
    have : ConnectedSpace (Bridge.Sub hN) := hconn
    have hpi := (hB V W n N hN (Emb.metricComplete_of_complete hc) (Emb.nonPosCurv_iff.2 hK)).1
    refine ⟨fun {m} hm x γ => ?_, fun {i} hi x => hpi i hi x⟩
    have h := (hpi m hm x).elim (Quotient.mk _ γ) (Quotient.mk _ GenLoop.const)
    exact Quotient.exact h

#rt_check RoundTrip.V11_21.A_to_B_emb_pi [Morse.contractibleSpace_cube,
  Morse.isPreconnected_cube_face, Morse.genLoop_homotopic_const, Morse.corollary_19_3]
#rt_check RoundTrip.V11_21.B_emb_to_A_conn [Morse.contractibleSpace_cube,
  Morse.isPreconnected_cube_face, Morse.genLoop_homotopic_const, Morse.corollary_19_3]
#rt_overlap RoundTrip.V11_21.B_emb_to_A_conn [Morse.contractibleSpace_cube,
  Morse.isPreconnected_cube_face, Morse.genLoop_homotopic_const, Morse.corollary_19_3]

end RoundTrip.V11_21
