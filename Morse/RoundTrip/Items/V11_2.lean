import Morse
import RoundTrip.Check
import RoundTrip.Blind.V11_2
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V11_2

/-- The project's statement (universes instantiated at `0`; `Morse.expDomAt` — the domain of
`exp_q` in `T_qN` — and `Morse.dExpAt` — the derivative of `exp_q` at `v`, Milnor's `exp_*` — are
vocabulary): for a slice submanifold `N ⊆ V` with the induced metric (no completeness), the domain
of `exp_q` is open, `exp_q` is `C^∞` on it, for `v` in it `γ_v(t) = exp_q(tv)` is a geodesic on an
open interval containing `[0,1]` and a smooth curve in `N` on `[0,1]`, and for complete `N` the
domain is all of `T_qN`. -/
def A : Prop :=
  type_of% @Morse.isOpen_expDomAt.{0,0,0} ∧
    type_of% @Morse.contDiffOn_expAt.{0,0,0} ∧
    type_of% @Morse.isGeodesicOn_ray.{0,0,0} ∧
    type_of% @Morse.isSmoothCurveIn_ray.{0,0,0} ∧
    type_of% @Morse.expDomAt_eq_univ.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.isOpen_expDomAt, @Morse.contDiffOn_expAt, @Morse.isGeodesicOn_ray,
    @Morse.isSmoothCurveIn_ray, @Morse.expDomAt_eq_univ⟩

/-! Neither `A → B` nor `B → A` is proved: B quantifies over abstract connected Hausdorff
`ℝⁿ`-manifolds with an arbitrary smooth metric and an arbitrary Levi-Civita connection, A only
over slice submanifolds `N ⊆ V` with the induced metric (see `V11_2.json`). Below: the embedded
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

/-- The blind radial curve `t ↦ exp_p(tv)` of a complete `↥N`, read in `V`. -/
theorem incl_ray (hc : Morse.IsGeodesicallyComplete hN) (p : Bridge.Sub hN) (v : Rn n) (t : ℝ) :
    incl hN (expMap (conn (hN := hN)) p (t • v)) = Morse.exp hN (incl hN p) (t • D hN p v) := by
  rw [incl_expMap hc p (t • v)]
  exact congrArg _ ((D hN p).map_smul t v)

/-- **The radial curve, given that the project's ray is a geodesic near `[0, 1]`** (this is where
A's `isGeodesicOn_ray` enters): the blind `γ_v` is a blind geodesic on `[0, 1]` with
`γ_v(0) = p`, `γ_v(1) = exp_p(v)` and initial velocity `v`. -/
theorem ray_props (hc : Morse.IsGeodesicallyComplete hN) (p : Bridge.Sub hN) (v : Rn n)
    (hray : ∃ δ > 0, Morse.IsGeodesicOn hN (fun t => Morse.exp hN (incl hN p) (t • D hN p v))
      (Ioo (-δ) (1 + δ))) :
    IsGeodesic (conn (hN := hN)) (fun t : ℝ => expMap (conn (hN := hN)) p (t • v)) (Icc 0 1) ∧
      (fun t : ℝ => expMap (conn (hN := hN)) p (t • v)) 0 = p ∧
      (fun t : ℝ => expMap (conn (hN := hN)) p (t • v)) 1 = expMap (conn (hN := hN)) p v ∧
      InitData (fun t : ℝ => expMap (conn (hN := hN)) p (t • v)) (Icc 0 1) p v := by
  obtain ⟨δ, hδ, hgeo⟩ := hray
  set γV : ℝ → V := fun t => Morse.exp hN (incl hN p) (t • D hN p v) with hγV
  have hfrom : Morse.IsGeodesicFrom hN γV (incl hN p) (D hN p v) := by
    refine ⟨δ, hδ, hgeo, ?_, ?_⟩
    · simp only [hγV, zero_smul]
      exact Morse.exp_zero p.2
    · exact (Morse.hasDerivAt_exp_smul_zero (hN := hN) p (D_mem p v)).deriv
  obtain ⟨h1, h2, -⟩ := isGeodesic_lift_of_isGeodesicFrom (w := v) hfrom
  have heq : (fun t : ℝ => expMap (conn (hN := hN)) p (t • v)) = lift γV p := by
    funext t
    have hmem : γV t ∈ N := by
      show Morse.exp hN (incl hN p) (t • D hN p v) ∈ N
      rw [← incl_ray hc p v t]
      exact (expMap _ p (t • v)).2
    apply Subtype.ext
    show incl hN (expMap (conn (hN := hN)) p (t • v)) = incl hN (lift γV p t)
    rw [incl_lift p hmem, incl_ray hc p v t]
  rw [heq]
  refine ⟨h1, h2.1, ?_, h2⟩
  rw [← heq]
  simp only [one_smul]

end Emb

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric) with the induced Levi-Civita
connection `Bridge.conn` (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    MetricComplete n (Bridge.Sub hN) →
    ∀ (p : Bridge.Sub hN) (v : TangentSpace 𝓘(ℝ, Rn n) p),
      IsGeodesic (Bridge.conn (hN := hN)) (fun t : ℝ => expMap (Bridge.conn (hN := hN)) p (t • v))
          (Set.Icc 0 1) ∧
        (fun t : ℝ => expMap (Bridge.conn (hN := hN)) p (t • v)) 0 = p ∧
        (fun t : ℝ => expMap (Bridge.conn (hN := hN)) p (t • v)) 1 =
          expMap (Bridge.conn (hN := hN)) p v ∧
        InitData (fun t : ℝ => expMap (Bridge.conn (hN := hN)) p (t • v)) (Set.Icc 0 1) p v

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds** (A's `expDomAt_eq_univ` and `isGeodesicOn_ray`, then the
lift of `Bridge.isGeodesic_lift_of_isGeodesicFrom`). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ hmc p v
  have hc := Emb.complete_of_metricComplete hmc
  have hvD : Emb.Dt p v ∈ Morse.expDomAt hN p := by rw [hA.2.2.2.2 hc p]; trivial
  exact Emb.ray_props hc p v (hA.2.2.1 hvD)

/-- **B_emb holds outright**: the same proof with the ray taken from the definition of `expDom`
(`Morse.IsGeodesicFrom.isGeodesicOn_exp_smul`, Chapter 7) instead of A. -/
theorem B_emb_holds : B_emb := by
  intro V _ _ _ W _ _ _ n N hN _ hmc p v
  have hc := Emb.complete_of_metricComplete hmc
  obtain ⟨γ, hγ⟩ := Emb.mem_expDom hc p v
  obtain ⟨δ, hδ, hgeo, -⟩ := hγ.isGeodesicOn_exp_smul
  exact Emb.ray_props hc p v ⟨δ, hδ, hgeo⟩

/-- The part of A that B covers on embedded manifolds: for complete, connected `N` (model `ℝⁿ`),
`γ_v` is a smooth curve in `N` on `[0, 1]` and a geodesic on `(0, 1)`. -/
def A_cplt : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    Morse.IsGeodesicallyComplete hN → ∀ (q : N) (v : Morse.tangentSubspace hN q),
      Morse.IsSmoothCurveIn hN (fun t => Morse.exp hN q (t • (v : V))) ∧
        Morse.IsGeodesicOn hN (fun t => Morse.exp hN q (t • (v : V))) (Ioo 0 1)

theorem A_to_A_cplt : A → A_cplt := by
  intro hA V _ _ _ W _ _ _ n N hN _ hc q v
  have hv : v ∈ Morse.expDomAt hN q := by rw [hA.2.2.2.2 hc q]; trivial
  obtain ⟨δ, hδ, hgeo⟩ := hA.2.2.1 hv
  exact ⟨hA.2.2.2.1 hv, hgeo.mono isOpen_Ioo (Ioo_subset_Ioo (by linarith) (by linarith))⟩

/-- **B on embedded manifolds implies the covered part of A** (`Bridge.isGeodesicOn_Ioo`,
`Bridge.isSmoothCurve_iff`). -/
theorem B_emb_to_A_cplt : B_emb → A_cplt := by
  intro hB V _ _ _ W _ _ _ n N hN _ hc q v
  let p : Bridge.Sub hN := q
  obtain ⟨hgeo, -, -, -⟩ := hB V W n N hN (Emb.metricComplete_of_complete hc) p (Bridge.L hN p v)
  have hγ : Bridge.incl hN ∘ (fun t : ℝ => expMap (Bridge.conn (hN := hN)) p (t • Bridge.L hN p v)) =
      fun t => Morse.exp hN q (t • (v : V)) := by
    funext t
    rw [Function.comp_apply, Emb.incl_ray hc p _ t, Bridge.D_L v.2]
    rfl
  have hgeo' : RoundTrip.BridgePrelude.IsGeodesic (Bridge.conn (hN := hN))
      (fun t : ℝ => expMap (Bridge.conn (hN := hN)) p (t • Bridge.L hN p v)) (Icc 0 1) := hgeo
  have h1 := Bridge.isGeodesicOn_Ioo hgeo'
  have h2 := (Bridge.isGeodesic_iff.1 hgeo').2.1
  rw [hγ] at h1 h2
  exact ⟨⟨h2, fun t _ => by rw [← congrFun hγ t]; exact (expMap _ p _).2⟩, h1⟩

#rt_check RoundTrip.V11_2.A_to_B_emb [Morse.isOpen_expDomAt, Morse.contDiffOn_expAt,
  Morse.isGeodesicOn_ray, Morse.isSmoothCurveIn_ray, Morse.expDomAt_eq_univ]
#rt_check RoundTrip.V11_2.B_emb_holds [Morse.isOpen_expDomAt, Morse.contDiffOn_expAt,
  Morse.isGeodesicOn_ray, Morse.isSmoothCurveIn_ray, Morse.expDomAt_eq_univ]
#rt_check RoundTrip.V11_2.B_emb_to_A_cplt [Morse.isOpen_expDomAt, Morse.contDiffOn_expAt,
  Morse.isGeodesicOn_ray, Morse.isSmoothCurveIn_ray, Morse.expDomAt_eq_univ]
#rt_overlap RoundTrip.V11_2.B_emb_to_A_cplt [Morse.isOpen_expDomAt, Morse.contDiffOn_expAt,
  Morse.isGeodesicOn_ray, Morse.isSmoothCurveIn_ray, Morse.expDomAt_eq_univ]

end RoundTrip.V11_2
