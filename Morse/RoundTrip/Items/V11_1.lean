import Morse
import RoundTrip.Check
import RoundTrip.Blind.V11_1
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V11_1

/-- The project's statement (universes instantiated at `0`; `Morse.RaysGoodE` is vocabulary): for
a slice submanifold `N ⊆ V` with the induced metric (no completeness): smooth dependence of the
radial geodesics `t ↦ exp_{c(u)}(t w(u))` on parameters `u` in a normed space over a compact time
interval; a smooth local retraction onto `N`; a geodesic `t ↦ exp_y(tw)` on an open interval
containing `[0,1]` puts `(y, w)` in the domain of `exp`; **`exp` is smooth on its whole domain**
(near each `(p, v) ∈ expDom` it is the restriction to `TN` of a smooth map on an open set of
`V × V`), the domain is open in `TN`, and `exp` is `C^∞` on its domain for the manifold structure
of `TN`. -/
def A : Prop :=
  type_of% @Morse.raysGoodE_of_isGeodesicOn.{0,0,0,0} ∧
    type_of% @Morse.exists_retraction.{0,0,0} ∧
    type_of% @Morse.mem_expDom_of_isGeodesicOn.{0,0,0} ∧
    type_of% @Morse.exists_contDiffOn_exp.{0,0,0} ∧
    type_of% @Morse.exists_isOpen_expDom.{0,0,0} ∧
    type_of% @Morse.contMDiffOn_exp_expDom.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.raysGoodE_of_isGeodesicOn, @Morse.exists_retraction, @Morse.mem_expDom_of_isGeodesicOn,
    @Morse.exists_contDiffOn_exp, @Morse.exists_isOpen_expDom, @Morse.contMDiffOn_exp_expDom⟩

/-! Neither `A → B` nor `B → A` is proved: B quantifies over abstract connected Hausdorff
`ℝⁿ`-manifolds with an arbitrary smooth metric and an arbitrary Levi-Civita connection, A only
over slice submanifolds `N ⊆ V` with the induced metric (see `V11_1.json`). Below: the embedded
special case `B_emb` (B for `M = ↥N`, `cov = Bridge.conn`) and its comparison with A. -/

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

/-- `Dt q` as a continuous linear equivalence `ℝⁿ ≃ T_qN`. -/
noncomputable def DtE (q : Bridge.Sub hN) : Rn n ≃L[ℝ] Morse.tangentSubspace hN q :=
  (LinearEquiv.ofBijective (Dt q : Rn n →ₗ[ℝ] Morse.tangentSubspace hN q)
    ⟨Dt_injective q, Dt_surjective q⟩).toContinuousLinearEquiv

theorem DtE_apply (q : Bridge.Sub hN) (w : Rn n) : DtE q w = Dt q w := rfl

end Emb

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric) with the induced Levi-Civita
connection `Bridge.conn` (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    MetricComplete n (Bridge.Sub hN) →
    ∀ p : Bridge.Sub hN, (∀ v : TangentSpace 𝓘(ℝ, Rn n) p, ExpDefined (Bridge.conn (hN := hN)) p v) ∧
      ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) ∞ (fun w : Rn n => expMap (Bridge.conn (hN := hN)) p w)

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- What B says on embedded manifolds, in the project's terms: for complete connected `N` (model
`ℝⁿ`), `exp_q` is `C^∞` on all of `T_qN`. (Not one of A's conjuncts: a consequence of A's
`exists_contDiffOn_exp`, see `A_to_A_pt`.) -/
def A_pt : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    Morse.IsGeodesicallyComplete hN → ∀ q : N,
      ContDiff ℝ ∞ (fun y : Morse.tangentSubspace hN q => Morse.exp hN q y)

/-- A gives the per-point smoothness of `exp_q` (from `exists_contDiffOn_exp`). -/
theorem A_to_A_pt : A → A_pt := by
  intro hA V _ _ _ W _ _ _ n N hN _ hc q
  rw [contDiff_iff_contDiffAt]
  intro y
  obtain ⟨O, hO, hyO, F, hF, hFeq⟩ := hA.2.2.2.1 (hc q y y.2)
  set ι : Morse.tangentSubspace hN q → V × V := fun y' => ((q : V), (y' : V)) with hι
  have hιc : ContDiff ℝ ∞ ι := contDiff_const.prodMk (Morse.tangentSubspace hN q).subtypeL.contDiff
  have h1 : ContDiffAt ℝ ∞ (F ∘ ι) y :=
    (hF.contDiffAt (hO.mem_nhds hyO)).comp y hιc.contDiffAt
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hιc.continuous.continuousAt.preimage_mem_nhds (hO.mem_nhds hyO)] with y' hy'
  exact (hFeq (ι y') hy' ⟨q.2, y'.2⟩).2

/-- On a complete `↥N`, B_emb's two claims are equivalent to `A_pt` (blind `exp` = project `exp`,
`contMDiff_map_iff`, and `D_q : ℝⁿ ≃ T_qN`). -/
theorem B_emb_iff_A_pt : B_emb ↔ A_pt := by
  constructor
  · intro hB V _ _ _ W _ _ _ n N hN _ hc q
    let p : Bridge.Sub hN := q
    have h := (hB V W n N hN (Emb.metricComplete_of_complete hc) p).2
    have h1 := Emb.contMDiff_map_iff.1 h
    rw [Emb.incl_comp_expMap hc p] at h1
    have h2 := h1.comp (Emb.DtE p).symm.contDiff
    convert h2 using 1
    funext y
    show _ = Morse.exp hN (Bridge.incl hN p) (Emb.Dt p ((Emb.DtE p).symm y) : V)
    rw [← Emb.DtE_apply, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · intro hA V _ _ _ W _ _ _ n N hN _ hmc p
    have hc := Emb.complete_of_metricComplete hmc
    refine ⟨fun v => Bridge.expDefined_of_mem_expDom (Emb.mem_expDom hc p v), ?_⟩
    refine Emb.contMDiff_map_iff.2 ?_
    rw [Emb.incl_comp_expMap hc p]
    exact (hA V W n N hN hc p).comp (Emb.Dt p).contDiff

/-- **A implies B on embedded manifolds** (through `A_pt`). -/
theorem A_to_B_emb : A → B_emb := fun hA => B_emb_iff_A_pt.2 (A_to_A_pt hA)

/-- **B on embedded manifolds gives the per-point smoothness of `exp_q`** (complete `N`). -/
theorem B_emb_to_A_pt : B_emb → A_pt := fun h => B_emb_iff_A_pt.1 h

#rt_check RoundTrip.V11_1.A_to_B_emb [Morse.raysGoodE_of_isGeodesicOn, Morse.exists_retraction,
  Morse.mem_expDom_of_isGeodesicOn, Morse.exists_contDiffOn_exp, Morse.exists_isOpen_expDom,
  Morse.contMDiffOn_exp_expDom]
#rt_check RoundTrip.V11_1.B_emb_to_A_pt [Morse.raysGoodE_of_isGeodesicOn, Morse.exists_retraction,
  Morse.mem_expDom_of_isGeodesicOn, Morse.exists_contDiffOn_exp, Morse.exists_isOpen_expDom,
  Morse.contMDiffOn_exp_expDom]
#rt_overlap RoundTrip.V11_1.B_emb_to_A_pt [Morse.raysGoodE_of_isGeodesicOn,
  Morse.exists_retraction, Morse.mem_expDom_of_isGeodesicOn, Morse.exists_contDiffOn_exp,
  Morse.exists_isOpen_expDom, Morse.contMDiffOn_exp_expDom]

end RoundTrip.V11_1
