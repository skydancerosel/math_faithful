import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.V7_29

namespace RoundTrip.V7_29

/-- The project's statement (universes instantiated at 0): for a connected nonempty slice
submanifold `N ⊆ V`, the Hopf–Rinow TFAE (`(N, ρ)` complete ↔ geodesically complete ↔ `exp_p`
total for some `p` ↔ `ρ`-bounded sets have compact closure in `N`); for complete `N` geodesics
extend to `ℝ`, any two points are joined by a minimal geodesic of length `ρ`, and closed
`ρ`-bounded sets are compact; and the Heine–Borel statement for any `N` with the
compact-closure property. -/
def A : Prop :=
  type_of% @Morse.hopf_rinow.{0,0,0} ∧
    type_of% @Morse.hopf_rinow_of_isRiemComplete.{0,0,0} ∧
    type_of% @Morse.isCompact_of_isClosed_of_isRiemBounded.{0}

theorem A_holds : A :=
  ⟨@Morse.hopf_rinow, @Morse.hopf_rinow_of_isRiemComplete,
    @Morse.isCompact_of_isClosed_of_isRiemBounded⟩

/-! Neither direction is proved (see `V7_29.json`): `B` is about an abstract Riemannian manifold
with an arbitrary Levi-Civita connection, `A` about slice submanifolds of a Euclidean space, and
`A` contains Theorem 10.9 (minimal geodesics) and the Heine–Borel statements, which `B` lacks.

### Embedded special case

What *can* be checked: on a slice submanifold `N ⊆ V` modelled on `ℝⁿ`, Milnor's equivalence `B`
specialises (through `RoundTrip.Bridge`: the induced metric and connection are Levi-Civita in the
blind sense) to the equivalence `1 ↔ 2` of the project's `hopf_rinow`. The only missing piece of
the dictionary was that a blind geodesic on `[0, 1]` yields a point of the project's `expDom`
(a geodesic on an open interval containing `[0, 1]`), which is `Morse.exists_initial_ray`. -/

section Embedded

open Set Filter Topology Bundle
open scoped ContDiff Manifold
open RoundTrip.Bridge RoundTrip.BridgePrelude

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- A blind geodesic `[0, 1] → N` from `q` with velocity `w` extends to a project geodesic on an
open interval containing `[0, 1]`, so `(q, w) ∈ expDom`. -/
theorem mem_expDom_of_expDefined [FiniteDimensional ℝ W] {q : Sub hN}
    {w : TangentSpace 𝓘(ℝ, Rn n) q} (h : RoundTrip.V7_29.ExpDefined (conn (hN := hN)) q w) :
    (incl hN q, D hN q w) ∈ Morse.expDom hN := by
  obtain ⟨c, hc, hinit⟩ := h
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hsm : Morse.IsSmoothCurveIn hN (incl hN ∘ c) :=
    ⟨(isGeodesic_iff.1 hc).2.1, fun t _ => (c t).2⟩
  obtain ⟨η, hη, hray, heq⟩ := Morse.exists_initial_ray hsm (isGeodesicOn_Ioo hc)
  set g : ℝ → V := fun t => Morse.exp hN ((incl hN ∘ c) 0) (t • Morse.velAlong (incl hN ∘ c) 0)
  have hc0 : c 0 = q := hinit.1
  have hg0 : g 0 = incl hN q := by
    show Morse.exp hN ((incl hN ∘ c) 0) ((0 : ℝ) • Morse.velAlong (incl hN ∘ c) 0) = incl hN q
    rw [heq 0 h0I]
    exact congrArg (incl hN) hc0
  refine ⟨g, η, hη, hray, hg0, ?_⟩
  have hd : DifferentiableAt ℝ g 0 :=
    (hray.contDiffOn.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  have uI : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have e1 : deriv g 0 = derivWithin g (Icc 0 1) 0 := (hd.derivWithin (uI 0 h0I)).symm
  have e2 : derivWithin g (Icc 0 1) 0 = derivWithin (incl hN ∘ c) (Icc 0 1) 0 :=
    derivWithin_congr (fun t ht => heq t ht) (heq 0 h0I)
  rw [e1, e2, ← D_vel (isSmoothCurve_iff.2 (isGeodesic_iff.1 hc).2.1) uI h0I]
  exact (initData_iff hc0).1 hinit

/-- Dictionary: geodesic completeness. -/
theorem isGeodesicallyComplete_iff_geodComplete [FiniteDimensional ℝ W] :
    Morse.IsGeodesicallyComplete hN ↔ RoundTrip.V7_29.GeodComplete (conn (hN := hN)) := by
  constructor
  · intro h q w
    exact expDefined_of_mem_expDom (h q _ (D_mem q w))
  · intro h q v hv
    have := mem_expDom_of_expDefined (h q (L hN q v))
    rwa [D_L hv] at this

/-- The blind `ρ` of `V7_29` is the project's `riemDist` (as a real number): `Bridge.rho_eq`,
the two blind definitions being syntactically identical. -/
theorem rho_eq' [FiniteDimensional ℝ W] (p q : Sub hN) :
    RoundTrip.V7_29.rho (n := n) p q =
      (Morse.riemDist (N := N) (incl hN p) (incl hN q)).toReal :=
  rho_eq p q

/-- Dictionary: metric completeness (for connected `N`, where `ρ < ∞`). -/
theorem isRiemComplete_iff_metricComplete [FiniteDimensional ℝ W] (hconn : IsPreconnected N) :
    Morse.IsRiemComplete N ↔ RoundTrip.V7_29.MetricComplete n (Sub hN) := by
  have hne : ∀ p q : Sub hN, Morse.riemDist (N := N) (incl hN p) (incl hN q) ≠ ⊤ :=
    fun p q => Morse.riemDist_ne_top hN hconn p.2 q.2
  constructor
  · intro h x hx
    obtain ⟨y, hyN, hlim⟩ := h (fun k => incl hN (x k)) (fun k => (x k).2) (fun ε hε => by
      obtain ⟨n₀, hn₀⟩ := hx ε hε
      refine ⟨n₀, fun m hm k hk => ?_⟩
      have := hn₀ m hm k hk
      rw [rho_eq'] at this
      exact (ENNReal.lt_ofReal_iff_toReal_lt (hne _ _)).2 this)
    refine ⟨(⟨y, hyN⟩ : Sub hN), fun ε hε => ?_⟩
    have := ENNReal.tendsto_nhds_zero.1 hlim (ENNReal.ofReal (ε / 2)) (by simpa using hε)
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 this
    refine ⟨n₀, fun m hm => (rho_eq' (x m) (⟨y, hyN⟩ : Sub hN)).trans_lt ?_⟩
    refine ENNReal.toReal_lt_of_lt_ofReal ((hn₀ m hm).trans_lt ?_)
    exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
  · intro h x hxN hx
    obtain ⟨p, hp⟩ := h (fun k => (⟨x k, hxN k⟩ : Sub hN)) (fun ε hε => by
      obtain ⟨n₀, hn₀⟩ := hx ε hε
      refine ⟨n₀, fun m hm k hk => (rho_eq' _ _).trans_lt ?_⟩
      exact ENNReal.toReal_lt_of_lt_ofReal (hn₀ m hm k hk))
    refine ⟨incl hN p, p.2, ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_⟩
    rcases eq_or_ne ε ⊤ with rfl | hεtop
    · exact Eventually.of_forall fun _ => le_top
    have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    obtain ⟨n₀, hn₀⟩ := hp ε.toReal hε'
    refine eventually_atTop.2 ⟨n₀, fun m hm => ?_⟩
    have := (rho_eq' _ _).symm.trans_lt (hn₀ m hm)
    exact ((ENNReal.toReal_lt_toReal (hne _ _) hεtop).1 this).le

/-- `B` specialised to `Sub hN`: Milnor's equivalence for the induced metric and connection.
(The instances of `Sub hN` are passed explicitly: the search for the smooth-Riemannian-bundle
instance exceeds the default heartbeat budget.) -/
theorem B_sub (hB : B) [FiniteDimensional ℝ W] (hconn : IsPreconnected N) (hne : N.Nonempty) :
    RoundTrip.V7_29.GeodComplete (conn (hN := hN)) ↔
      RoundTrip.V7_29.MetricComplete n (Sub hN) := by
  have hcs : ConnectedSpace (Sub hN) := isConnected_iff_connectedSpace.1 ⟨hne, hconn⟩
  have hLC : RoundTrip.V7_29.IsLC (conn (hN := hN)) := conn_isLC
  have h1 := @hB n (Sub hN)
  have h2 := @h1 inferInstance inferInstance inferInstance inferInstance
  have h3 := @h2
    (@RoundTrip.Bridge.instRiemannianBundleSubTangentSpaceRealRnModelWithCornersSelf V _ _ _ W _ _ n N hN)
    (@RoundTrip.Bridge.instIsContMDiffRiemannianBundleRnModelWithCornersSelfRealSomeENatTopSubTangentSpace
      V _ _ _ W _ _ n N hN) hcs
  exact h3 (conn (hN := hN)) hLC

/-- **The embedded special case of `B`**: for a connected nonempty slice submanifold `N ⊆ V`
modelled on `ℝⁿ`, Milnor's equivalence gives the equivalence `1 ↔ 2` of the project's
`Morse.hopf_rinow`. -/
theorem embedded_special_case (hB : B) [FiniteDimensional ℝ W] (hconn : IsPreconnected N)
    (hne : N.Nonempty) :
    Morse.IsRiemComplete N ↔ Morse.IsGeodesicallyComplete hN := by
  rw [isRiemComplete_iff_metricComplete (hN := hN) hconn,
    isGeodesicallyComplete_iff_geodComplete (hN := hN)]
  exact (B_sub (hN := hN) hB hconn hne).symm

end Embedded

#rt_check RoundTrip.V7_29.embedded_special_case [Morse.hopf_rinow, Morse.hopf_rinow_of_isRiemComplete, Morse.isCompact_of_isClosed_of_isRiemBounded]
#rt_overlap RoundTrip.V7_29.embedded_special_case [Morse.hopf_rinow, Morse.hopf_rinow_of_isRiemComplete, Morse.isCompact_of_isClosed_of_isRiemBounded]

end RoundTrip.V7_29
