import Morse
import RoundTrip.Check
import RoundTrip.Blind.V13_1
import RoundTrip.Bridge

open Set Filter Topology Function
open scoped ContDiff Manifold

namespace RoundTrip.V13_1

/-- The project's statement (universes instantiated at `0`; `Morse.minPaths`, the paths of least
energy, is vocabulary): for ANY slice submanifold `N ⊆ V` (any model `Z`, complete or not) and
`p, q ∈ V`, a path `γ ∈ Ω(N; p, q)` of least energy (`E(γ) ≤ E(γ')` for all `γ' ∈ Ω(N; p, q)`) is
an unbroken geodesic (`C^∞` on `[0, 1]`, a geodesic on `(0, 1)`). -/
def A : Prop := type_of% @Morse.isUnbrokenGeodesic_of_minimal.{0,0,0}

theorem A_holds : A := @Morse.isUnbrokenGeodesic_of_minimal

/-! Neither `A → B` nor `B → A` is proved; see `V13_1.json`. B quantifies over abstract complete
Riemannian manifolds (any smooth metric, any Levi-Civita connection) and characterizes
`Ω^d = E⁻¹[0, ρ(p,q)²]` as the set of minimal geodesics (both inclusions); A is for slice
submanifolds with the induced metric, defines `Ω^d` as the least-energy paths (no `ρ²`) and proves
only one inclusion ("least energy ⇒ unbroken geodesic"), but without any completeness.

## The embedded special case -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-! ### Geodesics on `[0, 1]` (copied from Items/V8_10.lean) -/

/-- A blind geodesic on `[0, 1]` (induced connection) is a project unbroken geodesic. -/
theorem isUnbrokenGeodesic_of_isGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1)) :
    Morse.IsUnbrokenGeodesic hN (Bridge.incl hN ∘ pw) := by
  have h' : RoundTrip.BridgePrelude.IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1) := h
  exact ⟨(Bridge.isGeodesic_iff.1 h').2.1, Bridge.isGeodesicOn_Ioo h'⟩

/-- A project unbroken geodesic is a blind geodesic on the closed interval `[0, 1]`. -/
theorem isGeodesic_of_isUnbrokenGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : Morse.IsUnbrokenGeodesic hN (Bridge.incl hN ∘ pw)) :
    IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1) := by
  show RoundTrip.BridgePrelude.IsGeodesic _ _ _
  refine Bridge.isGeodesic_iff.2 ⟨⟨ordConnected_Icc, uniqueDiffOn_Icc zero_lt_one⟩, h.1, ?_⟩
  set f := Bridge.incl hN ∘ pw
  set I := Icc (0 : ℝ) 1
  have uI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc zero_lt_one
  have hg : ContinuousOn (derivWithin (derivWithin f I) I) I :=
    ((h.1.derivWithin uI (m := ∞) (by simp)).derivWithin uI (m := 0) (by simp)).continuousOn
  have hpw : ContinuousOn pw I := fun t ht =>
    (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := pw)).2 (h.1.continuousOn t ht)
  have hP : ContinuousOn (fun t => Bridge.P hN (pw t)) I :=
    Bridge.contMDiff_P.continuous.comp_continuousOn hpw
  have hcont : ContinuousOn
      (fun t => Bridge.P hN (pw t) (derivWithin (derivWithin f I) I t)) I := hP.clm_apply hg
  have hzero : EqOn (fun t => Bridge.P hN (pw t) (derivWithin (derivWithin f I) I t)) 0
      (Ioo 0 1) := by
    intro t ht
    have h1 : deriv f =ᶠ[𝓝 t] derivWithin f I := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
      exact (derivWithin_of_mem_nhds (Icc_mem_nhds hτ.1 hτ.2)).symm
    have e : derivWithin (derivWithin f I) I t = deriv (deriv f) t := by
      rw [h1.deriv_eq, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    show Bridge.P hN (pw t) _ = 0
    rw [e]
    exact (Morse.tanProj_eq_zero_iff hN).2 (h.2.normal t ht)
  intro t ht
  exact hzero.of_subset_closure hcont continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo zero_ne_one]) ht

/-! ### Paths (copied from Items/V10_19.lean) -/

/-- A blind path of `Ω(↥N; p, q)` is, in `V`, a project path of `Ω(N; p, q)`. -/
theorem mem_pathSpace {p q : Bridge.Sub hN} {w : ℝ → Bridge.Sub hN}
    (hw : InOmega (n := n) p q w) :
    incl hN ∘ w ∈ Morse.pathSpace N (incl hN p) (incl hN q) :=
  ⟨isPiecewiseSmooth_of_isPW hw.1, fun t _ => (w t).2, congrArg (incl hN) hw.2.1,
    congrArg (incl hN) hw.2.2⟩

/-- A project path of `Ω(N; p, q)` lifts to a blind path agreeing with it on `[0, 1]`. -/
theorem inOmega_lift {p' q' : Bridge.Sub hN} {c : ℝ → V}
    (hc : c ∈ Morse.pathSpace N (incl hN p') (incl hN q')) :
    InOmega (n := n) p' q' (lift c p') ∧ EqOn (incl hN ∘ lift c p') c (Icc 0 1) := by
  have heq : EqOn (incl hN ∘ lift c p') c (Icc 0 1) := fun t ht => incl_lift p' (hc.2.1 t ht)
  refine ⟨⟨isPW_lift hc.1 hc.2.1 p', ?_, ?_⟩, heq⟩
  · apply Subtype.ext
    exact (heq ⟨le_rfl, zero_le_one⟩).trans hc.2.2.1
  · apply Subtype.ext
    exact (heq ⟨zero_le_one, le_rfl⟩).trans hc.2.2.2

/-! ### Distance, length and energy (new) -/

theorem rho_nonneg (p q : Bridge.Sub hN) : 0 ≤ rho (n := n) p q := by
  have e : rho (n := n) p q = RoundTrip.BridgePrelude.rho (n := n) p q := rfl
  rw [e, rho_eq]
  exact ENNReal.toReal_nonneg

theorem rho_eq' (p q : Bridge.Sub hN) :
    rho (n := n) p q = (Morse.riemDist (N := N) (incl hN p) (incl hN q)).toReal :=
  rho_eq p q

/-- `ρ(p, q)` is at most the length of any piecewise smooth path from `p` to `q`. -/
theorem rho_le_arcLen {p q : Bridge.Sub hN} {pw : ℝ → Bridge.Sub hN} {a b : ℝ} (hab : a ≤ b)
    (hpw : IsPW (n := n) pw a b) (ha : pw a = p) (hb : pw b = q) :
    rho (n := n) p q ≤ arcLen (n := n) pw a b :=
  csInf_le ⟨0, fun _ ⟨_, _, _, hab', _, _, _, hL⟩ => hL ▸ arcLen_nonneg hab'⟩
    ⟨pw, a, b, hab, hpw, ha, hb, rfl⟩

/-- The blind energy is the project's energy. -/
theorem efun_eq (w : ℝ → Bridge.Sub hN) : Efun (n := n) w = Morse.energy (incl hN ∘ w) 0 1 :=
  energy_eq w 0 1

/-- `ρ(p, q)² ≤ E(γ')` for every project path `γ' ∈ Ω(N; p, q)` (Schwarz). -/
theorem rho_sq_le_energy {p q : Bridge.Sub hN} {γ' : ℝ → V}
    (hγ' : γ' ∈ Morse.pathSpace N (incl hN p) (incl hN q)) :
    rho (n := n) p q ^ 2 ≤ Morse.energy γ' 0 1 := by
  have h := Morse.riemDist_sq_le_energy (N := N) hγ'.1 hγ'.2.1
  rw [hγ'.2.2.1, hγ'.2.2.2, sub_zero, one_mul] at h
  rw [rho_eq']
  exact h

/-- A blind minimal geodesic on `[0, 1]` has length `≤ ρ` of its end points. -/
theorem arcLen_le_rho {p q : Bridge.Sub hN} {w : ℝ → Bridge.Sub hN} (hw : InOmega (n := n) p q w)
    (h : IsMinimal (Bridge.conn (hN := hN)) w 0 1) : arcLen (n := n) w 0 1 ≤ rho (n := n) p q := by
  refine le_csInf ⟨_, w, 0, 1, zero_le_one, hw.1, hw.2.1, hw.2.2, rfl⟩ ?_
  rintro _ ⟨pth, a, b, hab, hpw, ha, hb, rfl⟩
  exact h.2 pth a b hab hpw (ha.trans hw.2.1.symm) (hb.trans hw.2.2.symm)

/-- **On `↥N`: a minimal geodesic lies in `Ω^d`** (`E = L² ≤ ρ²`; not part of A). -/
theorem mem_OmD_of_isMinimal {p q : Bridge.Sub hN} (w : Om n p q)
    (h : IsMinimal (Bridge.conn (hN := hN)) w.1 0 1) : w ∈ OmD n p q := by
  have hγ := mem_pathSpace w.2
  have hgeo := isUnbrokenGeodesic_of_isGeodesic h.1
  have hE := Morse.energy_eq_pathLength_sq_of_geodesic hγ hgeo
  have hL : Morse.pathLength (incl hN ∘ w.1) 0 1 ≤ rho (n := n) p q := by
    rw [← arcLen_eq]; exact arcLen_le_rho w.2 h
  have hL0 : 0 ≤ Morse.pathLength (incl hN ∘ w.1) 0 1 := by
    rw [← arcLen_eq]; exact arcLen_nonneg zero_le_one
  show Efun (n := n) w.1 ≤ rho (n := n) p q ^ 2
  rw [efun_eq, hE]
  exact pow_le_pow_left₀ hL0 hL 2

/-- **On `↥N`: a path of `Ω^d` has least energy** (`E(w) ≤ ρ² ≤ E(γ')`). -/
theorem leastEnergy_of_mem_OmD {p q : Bridge.Sub hN} {w : Om n p q} (hw : w ∈ OmD n p q) :
    ∀ γ' ∈ Morse.pathSpace N (incl hN p) (incl hN q),
      Morse.energy (incl hN ∘ w.1) 0 1 ≤ Morse.energy γ' 0 1 := by
  intro γ' hγ'
  have h1 : Efun (n := n) w.1 ≤ rho (n := n) p q ^ 2 := hw
  rw [efun_eq] at h1
  exact h1.trans (rho_sq_le_energy hγ')

/-- On `↥N`, a least-energy unbroken geodesic of `Ω^d` is minimal. -/
theorem isMinimal_of_mem_OmD {p q : Bridge.Sub hN} {w : Om n p q} (hw : w ∈ OmD n p q)
    (hgeo : Morse.IsUnbrokenGeodesic hN (incl hN ∘ w.1)) :
    IsMinimal (Bridge.conn (hN := hN)) w.1 0 1 := by
  refine ⟨isGeodesic_of_isUnbrokenGeodesic hgeo, fun pw a' b' hab hpw ha hb => ?_⟩
  have hγ := mem_pathSpace w.2
  have h1 : Efun (n := n) w.1 ≤ rho (n := n) p q ^ 2 := hw
  rw [efun_eq] at h1
  have hS := Morse.pathLength_sq_le_energy hγ.1
  rw [sub_zero, one_mul] at hS
  have hL0 : 0 ≤ Morse.pathLength (incl hN ∘ w.1) 0 1 := by
    rw [← arcLen_eq]; exact arcLen_nonneg zero_le_one
  have hL : Morse.pathLength (incl hN ∘ w.1) 0 1 ≤ rho (n := n) p q :=
    (pow_le_pow_iff_left₀ hL0 (rho_nonneg p q) two_ne_zero).1 (hS.trans h1)
  have e : arcLen (n := n) w.1 0 1 = Morse.pathLength (incl hN ∘ w.1) 0 1 := arcLen_eq w.1 0 1
  rw [e]
  exact hL.trans (rho_le_arcLen hab hpw (ha.trans w.2.2.1) (hb.trans w.2.2.2))

/-! ### Completeness (copied from Items/V7_29.lean) -/

theorem riemDist_eq_ofReal_rho (hpre : IsPreconnected N) (p q : Bridge.Sub hN) :
    Morse.riemDist (N := N) (incl hN p) (incl hN q) = ENNReal.ofReal (rho (n := n) p q) := by
  rw [rho_eq']
  exact (ENNReal.ofReal_toReal (Morse.riemDist_ne_top hN hpre p.2 q.2)).symm

theorem rho_lt_iff (hpre : IsPreconnected N) (p q : Bridge.Sub hN) {ε : ℝ} (hε : 0 < ε) :
    rho (n := n) p q < ε ↔ Morse.riemDist (N := N) (incl hN p) (incl hN q) < ENNReal.ofReal ε := by
  rw [riemDist_eq_ofReal_rho hpre, ENNReal.ofReal_lt_ofReal_iff hε]

theorem metricComplete_of (hpre : IsPreconnected N) (h : Morse.IsRiemComplete N) :
    MetricComplete n (Bridge.Sub hN) := by
  intro x hcau
  obtain ⟨y, hy, hlim⟩ := h (fun k => incl hN (x k)) (fun k => (x k).2) fun ε hε => by
    obtain ⟨n₀, hn₀⟩ := hcau ε hε
    exact ⟨n₀, fun m hm k hk => (rho_lt_iff hpre _ _ hε).1 (hn₀ m hm k hk)⟩
  refine ⟨⟨y, hy⟩, fun ε hε => ?_⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε)))
  exact ⟨n₀, fun m hm => (rho_lt_iff hpre _ _ hε).2 (hn₀ m hm)⟩

end Emb

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric, connected) with the induced
Levi-Civita connection `Bridge.conn`. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], MetricComplete n (Bridge.Sub hN) →
    ∀ (p q : Bridge.Sub hN) (w : Om n p q), w ∈ OmD n p q ↔ IsMinimal (Bridge.conn (hN := hN)) w.1 0 1

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds.** `Ω^d ⊆ {minimal geodesics}` uses A (a path with
`E ≤ ρ²` has least energy, hence is an unbroken geodesic by A, and then `L² ≤ E ≤ ρ²`);
`{minimal geodesics} ⊆ Ω^d` is not in A and comes from the project's constant-speed lemma
`Morse.energy_eq_pathLength_sq_of_geodesic`. Completeness is not used. -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ _ p q w
  refine ⟨fun hw => Emb.isMinimal_of_mem_OmD hw ?_, Emb.mem_OmD_of_isMinimal w⟩
  exact hA (hN := hN) (Emb.mem_pathSpace w.2) (Emb.leastEnergy_of_mem_OmD hw)

/-- The part of A that `B_emb` covers: least-energy paths are unbroken geodesics, for slice
submanifolds modelled on `ℝⁿ` that are connected and complete (`IsRiemComplete`). -/
def A_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
    IsPreconnected N → Morse.IsRiemComplete N →
    ∀ {p q : V} {γ : ℝ → V}, γ ∈ Morse.pathSpace N p q →
      (∀ γ' ∈ Morse.pathSpace N p q, Morse.energy γ 0 1 ≤ Morse.energy γ' 0 1) →
      Morse.IsUnbrokenGeodesic hN γ

theorem A_to_A_emb : A → A_emb := fun hA _ _ _ _ _ _ _ _ _ _ hN _ _ _ _ _ hγ hmin =>
  hA (hN := hN) hγ hmin

/-- **B on embedded manifolds gives A** for connected complete `N` modelled on `ℝⁿ`: lift the
least-energy path `γ` to `↥N`; its energy is `≤` that of a minimal geodesic of length `ρ`
(Hopf–Rinow, `Morse.hopf_rinow_of_isRiemComplete`, outside A), i.e. `≤ ρ²`; so it is in `Ω^d`,
hence (B) a blind minimal geodesic, hence an unbroken geodesic on `[0, 1]`. -/
theorem B_emb_to_A_emb : B_emb → A_emb := by
  intro hB V _ _ _ W _ _ _ n N hN hpre hcpl p q γ hγ hmin
  have hpN : p ∈ N := hγ.2.2.1 ▸ hγ.2.1 0 ⟨le_rfl, zero_le_one⟩
  have hqN : q ∈ N := hγ.2.2.2 ▸ hγ.2.1 1 ⟨zero_le_one, le_rfl⟩
  let p' : Bridge.Sub hN := ⟨p, hpN⟩
  let q' : Bridge.Sub hN := ⟨q, hqN⟩
  have : ConnectedSpace (Bridge.Sub hN) :=
    isConnected_iff_connectedSpace.1 ⟨⟨p, hpN⟩, hpre⟩
  have hγ' : γ ∈ Morse.pathSpace N (Bridge.incl hN p') (Bridge.incl hN q') := hγ
  obtain ⟨hw, heq⟩ := Emb.inOmega_lift (n := n) hγ'
  let w : Om n p' q' := ⟨Bridge.lift γ p', hw⟩
  have hEw : Morse.energy (Bridge.incl hN ∘ w.1) 0 1 = Morse.energy γ 0 1 :=
    Morse.energy_congr_Icc zero_le_one heq
  -- a minimal geodesic of length `ρ(p, q)` (Hopf–Rinow)
  obtain ⟨-, -, hHR, -⟩ := Morse.hopf_rinow_of_isRiemComplete hN hpre hcpl
  obtain ⟨γ₀, hγ₀min, hγ₀0, hγ₀1, hρ⟩ := hHR ⟨p, hpN⟩ ⟨q, hqN⟩
  obtain ⟨hγ₀, hγ₀geo, -⟩ := hγ₀min.isMinimalPath
  rw [hγ₀0, hγ₀1] at hγ₀
  have hE₀ := Morse.energy_eq_pathLength_sq_of_geodesic hγ₀ hγ₀geo
  have hL₀ : Morse.pathLength γ₀ 0 1 = rho (n := n) p' q' := by
    rw [Emb.rho_eq']
    show _ = (Morse.riemDist (N := N) p q).toReal
    rw [hρ, ENNReal.toReal_ofReal hγ₀.1.isAdmissible.pathLength_nonneg]
  have hmem : w ∈ OmD n p' q' := by
    show Efun (n := n) w.1 ≤ rho (n := n) p' q' ^ 2
    rw [Emb.efun_eq, hEw, ← hL₀, ← hE₀]
    exact hmin γ₀ hγ₀
  have hM := (hB V W n N hN (Emb.metricComplete_of hpre hcpl) p' q' w).1 hmem
  have hg := Emb.isUnbrokenGeodesic_of_isGeodesic hM.1
  exact ⟨hg.1.congr fun t ht => (heq ht).symm,
    hg.2.congr fun t ht => heq (Ioo_subset_Icc_self ht)⟩

#rt_check RoundTrip.V13_1.A_to_B_emb [Morse.isUnbrokenGeodesic_of_minimal]
#rt_check RoundTrip.V13_1.B_emb_to_A_emb [Morse.isUnbrokenGeodesic_of_minimal]
#rt_overlap RoundTrip.V13_1.B_emb_to_A_emb [Morse.isUnbrokenGeodesic_of_minimal]
#rt_overlap RoundTrip.V13_1.A_to_B_emb [Morse.isUnbrokenGeodesic_of_minimal]

end RoundTrip.V13_1
