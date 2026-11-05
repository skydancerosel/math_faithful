import Morse
import RoundTrip.Check
import RoundTrip.Blind.V8_6
import RoundTrip.Bridge

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V8_6

/-- The project's statement (universes instantiated at 0): for a slice submanifold `N ⊆ V` with the
induced metric (completeness NOT assumed), if `γ ∈ Ω(N; p, q)` has length `≤` that of every path of
`Ω(N; p, q)` (`IsMinimalPath`) and is an unbroken geodesic (`C^∞` on `[0, 1]`, geodesic on
`(0, 1)`), then `E(γ) ≤ E(ω)` for every `ω ∈ Ω(N; p, q)`. -/
def A : Prop := type_of% @Morse.energy_le_of_isMinimalPath.{0,0,0}

theorem A_holds : A := @Morse.energy_le_of_isMinimalPath

/-! Neither `A → B` nor `B → A` is proved; see `V8_6.json`. Below: the embedded special case. -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- Geodesic completeness, blind vs project (copied from `Items/V7_29.lean`). -/
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

/-- `ρ(p, q) ≤ L(ω)` for a piecewise smooth path in `N` (the real-valued `ρ` of the blind file). -/
theorem rho_le_pathLength {c : ℝ → V} {a b : ℝ} (hc : Morse.IsPiecewiseSmooth c a b)
    (hcN : ∀ t ∈ Icc a b, c t ∈ N) {p q : Bridge.Sub hN} (hp : c a = incl hN p)
    (hq : c b = incl hN q) : rho (n := n) p q ≤ Morse.pathLength c a b := by
  have e : rho (n := n) p q = RoundTrip.BridgePrelude.rho (n := n) p q := rfl
  rw [e, rho_eq]
  refine ENNReal.toReal_le_of_le_ofReal hc.isAdmissible.pathLength_nonneg ?_
  rw [← hp, ← hq]
  exact Morse.riemDist_le_pathLength hc hcN

theorem rho_nonneg (p q : Bridge.Sub hN) : 0 ≤ rho (n := n) p q := by
  have e : rho (n := n) p q = RoundTrip.BridgePrelude.rho (n := n) p q := rfl
  rw [e, rho_eq]
  exact ENNReal.toReal_nonneg

/-- A minimal geodesic in the project's sense (Chapter 7) is a minimal path and an unbroken
geodesic in the sense of A. -/
theorem of_isMinimalGeodesic {γ : ℝ → V} (h : Morse.IsMinimalGeodesic hN γ 0 1) :
    Morse.IsMinimalPath N γ (γ 0) (γ 1) ∧ Morse.IsUnbrokenGeodesic hN γ := by
  obtain ⟨-, ⟨s, hs, hg⟩, hmin⟩ := h
  have hcd : ContDiffOn ℝ ∞ γ (Icc 0 1) := hg.contDiffOn.mono hs
  have hps : Morse.IsPiecewiseSmooth γ 0 1 :=
    Morse.IsPiecewiseSmooth.of_contDiffOn hcd zero_le_one subset_rfl
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ N := fun t ht => hg.mem t (hs ht)
  exact ⟨⟨⟨hps, hmem, rfl, rfl⟩, fun c' hc' => hmin c' 0 1 hc'.1 hc'.2.1 hc'.2.2.1 hc'.2.2.2⟩,
    hcd, hg.mono isOpen_Ioo (Ioo_subset_Icc_self.trans hs)⟩

/-- An unbroken geodesic has `E = L²` (constant speed, equality in Schwarz's inequality). -/
theorem energy_eq_sq {γ : ℝ → V} (hγ : Morse.IsPiecewiseSmooth γ 0 1)
    (hgeo : Morse.IsUnbrokenGeodesic hN γ) : Morse.energy γ 0 1 = Morse.pathLength γ 0 1 ^ 2 := by
  have hk : ∃ k, ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ γ t → ‖deriv γ t‖ = k :=
    ⟨‖deriv γ (1 / 2)‖, fun t ht _ => hgeo.2.norm_deriv_eq isPreconnected_Ioo ht
      ⟨by norm_num, by norm_num⟩⟩
  have h1 := (Morse.pathLength_sq_eq_energy_iff hγ).2 hk
  simp only [sub_zero, one_mul] at h1
  exact h1.symm

/-- A blind geodesic of the induced connection on `[0, 1]` is an unbroken geodesic. -/
theorem unbroken_of_isGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hN)) pw (Icc 0 1)) :
    Morse.IsUnbrokenGeodesic hN (incl hN ∘ pw) :=
  ⟨(isGeodesic_iff.1 h).2.1, isGeodesicOn_Ioo h⟩

/-- An unbroken geodesic is a blind geodesic on the closed interval `[0, 1]` (the normal
acceleration condition at the end points by continuity). -/
theorem isGeodesic_of_unbroken {pw : ℝ → Bridge.Sub hN}
    (h : Morse.IsUnbrokenGeodesic hN (incl hN ∘ pw)) :
    RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hN)) pw (Icc 0 1) := by
  have hU : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  rw [isGeodesic_iff]
  refine ⟨⟨ordConnected_Icc, hU⟩, h.1, ?_⟩
  set c := incl hN ∘ pw
  set dd := derivWithin (derivWithin c (Icc 0 1)) (Icc 0 1)
  have hd1 : ContDiffOn ℝ ∞ (derivWithin c (Icc 0 1)) (Icc 0 1) := h.1.derivWithin hU (by simp)
  have hd2 : ContinuousOn dd (Icc 0 1) := (hd1.derivWithin hU (m := 0) (by simp)).continuousOn
  have hpw : ContinuousOn pw (Icc 0 1) :=
    (Topology.IsInducing.subtypeVal.continuousOn_iff (f := pw)).2 h.1.continuousOn
  have hP : ContinuousOn (fun t => P hN (pw t)) (Icc 0 1) :=
    contMDiff_P.continuous.comp_continuousOn hpw
  have hf : ContinuousOn (fun t => P hN (pw t) (dd t)) (Icc 0 1) := hP.clm_apply hd2
  have hzero : EqOn (fun t => P hN (pw t) (dd t)) (fun _ => 0) (Ioo 0 1) := by
    intro t ht
    have e : dd t = deriv (deriv c) t := by
      simp only [dd]
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      exact derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)
    simp only
    rw [e]
    exact (Morse.tanProj_eq_zero_iff hN).2 (h.2.normal t ht)
  have hcl : Icc (0 : ℝ) 1 ⊆ closure (Ioo 0 1) := by rw [closure_Ioo zero_ne_one]
  exact fun t ht => hzero.of_subset_closure hf continuousOn_const Ioo_subset_Icc_self hcl ht

/-- The blind path space in `↥N`, read in `V`. -/
theorem mem_pathSpace {pw : ℝ → Bridge.Sub hN} {p q : Bridge.Sub hN}
    (h : InOmega (n := n) p q pw) : incl hN ∘ pw ∈ Morse.pathSpace N (incl hN p) (incl hN q) :=
  ⟨isPiecewiseSmooth_of_isPW h.1, fun t _ => (pw t).2, congrArg (incl hN) h.2.1,
    congrArg (incl hN) h.2.2⟩

theorem lift_mem {c : ℝ → V} {p q : Bridge.Sub hN} (hc : c ∈ Morse.pathSpace N (incl hN p) (incl hN q)) :
    InOmega (n := n) p q (lift c p) ∧ EqOn (incl hN ∘ lift c p) c (Icc 0 1) := by
  obtain ⟨hps, hmem, h0, h1⟩ := hc
  refine ⟨⟨isPW_lift hps hmem p, ?_, ?_⟩, fun t ht => incl_lift p (hmem t ht)⟩
  · rw [lift_of_mem p (hmem 0 ⟨le_rfl, zero_le_one⟩)]
    exact Subtype.ext h0
  · rw [lift_of_mem p (hmem 1 ⟨zero_le_one, le_rfl⟩)]
    exact Subtype.ext h1

theorem efun_eq (pw : ℝ → Bridge.Sub hN) :
    Efun (n := n) pw = Morse.energy (incl hN ∘ pw) 0 1 := Bridge.energy_eq pw 0 1

theorem arcLen_eq' (pw : ℝ → Bridge.Sub hN) (a b : ℝ) :
    arcLen (n := n) pw a b = Morse.pathLength (incl hN ∘ pw) a b := Bridge.arcLen_eq pw a b

/-- Affine reparametrization of a piecewise smooth path from `[a, b]` to `[0, 1]`: still piecewise
smooth, same length. -/
theorem reparam {c : ℝ → V} {a b : ℝ} (hc : Morse.IsPiecewiseSmooth c a b) (hab : a < b) :
    Morse.IsPiecewiseSmooth (fun t => c (a + (b - a) * t)) 0 1 ∧
      Morse.pathLength (fun t => c (a + (b - a) * t)) 0 1 = Morse.pathLength c a b := by
  have hpos : 0 < b - a := sub_pos.2 hab
  set φ : ℝ → ℝ := fun t => a + (b - a) * t with hφ
  have hφc : ContDiff ℝ ∞ φ := contDiff_const.add (contDiff_const.mul contDiff_id)
  have hφmono : StrictMono φ := fun x y hxy => by
    simp only [hφ]; nlinarith
  have hmaps : ∀ {s t : ℝ}, MapsTo φ (Icc s t) (Icc (φ s) (φ t)) := fun hx =>
    ⟨hφmono.monotone hx.1, hφmono.monotone hx.2⟩
  have hφ0 : φ 0 = a := by simp [hφ]
  have hφ1 : φ 1 = b := by simp [hφ]
  have hm01 : MapsTo φ (Icc 0 1) (Icc a b) := by
    have := @hmaps 0 1; rwa [hφ0, hφ1] at this
  obtain ⟨-, hcont, B, hB⟩ := hc
  refine ⟨⟨zero_le_one, hcont.comp hφc.continuous.continuousOn hm01,
    B.image fun x => (x - a) / (b - a), fun s t hs hst ht hB' => ?_⟩, ?_⟩
  · have hpiece : ContDiffOn ℝ ∞ c (Icc (φ s) (φ t)) := by
      refine hB (φ s) (φ t) (hφ0 ▸ hφmono.monotone hs) (hφmono hst) (hφ1 ▸ hφmono.monotone ht)
        fun x hx hxi => hB' ((x - a) / (b - a)) (Finset.mem_image.2 ⟨x, hx, rfl⟩) ⟨?_, ?_⟩
      · rw [lt_div_iff₀ hpos]; have := hxi.1; simp only [hφ] at this; linarith
      · rw [div_lt_iff₀ hpos]; have := hxi.2; simp only [hφ] at this; linarith
    exact hpiece.comp hφc.contDiffOn hmaps
  · unfold Morse.pathLength
    have hd : ∀ t, deriv (fun t => c (a + (b - a) * t)) t = (b - a) • deriv c (a + (b - a) * t) :=
      fun t => by
        rw [show (fun t => c (a + (b - a) * t)) = (fun y => (fun z => c (a + z)) ((b - a) * y)) from
          rfl, deriv_comp_mul_left (b - a) (fun z => c (a + z)) t, deriv_comp_const_add]
    simp_rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    rw [intervalIntegral.integral_const_mul]
    have := intervalIntegral.smul_integral_comp_add_mul (a := 0) (b := 1)
      (fun x => ‖deriv c x‖) (b - a) a
    simp only [smul_eq_mul, mul_zero, add_zero, mul_one, add_sub_cancel] at this
    exact this

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    GeodComplete (n := n) (Bridge.conn (hN := hN)) → ∀ p q : Bridge.Sub hN,
    (∃ pw : ℝ → Bridge.Sub hN, InOmega (n := n) p q pw ∧ Efun (n := n) pw = rho (n := n) p q ^ 2) ∧
    (∀ pw : ℝ → Bridge.Sub hN, InOmega (n := n) p q pw → rho (n := n) p q ^ 2 ≤ Efun (n := n) pw) ∧
    ∀ pw : ℝ → Bridge.Sub hN, InOmega (n := n) p q pw →
      (Efun (n := n) pw = rho (n := n) p q ^ 2 ↔ IsMinimal (Bridge.conn (hN := hN)) pw 0 1)

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

open Emb Bridge in
/-- **A implies B on embedded manifolds.** Besides A (the inequality `E(γ) ≤ E(ω)` at a minimal
unbroken geodesic, used for the lower bound and for "minimal geodesic ⇒ `E = d²`"), the proof needs
two project theorems that A does not contain: Hopf–Rinow / Theorem 10.9 (`Morse.theorem_10_9'`,
existence of a minimal geodesic) and Corollary 12.3 with Theorem 12.2 (`Morse.corollary_12_3`,
`Morse.IsVariation.hasDerivAt_energy`: a minimizer of `E` is an unbroken geodesic). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN hconn hgc p q
  have hpre : IsPreconnected N :=
    isPreconnected_iff_preconnectedSpace.2 (inferInstance : PreconnectedSpace (Bridge.Sub hN))
  have hcomp : Morse.IsGeodesicallyComplete hN := geodComplete_iff.1 hgc
  -- a minimal geodesic `γ` from `p` to `q` of length `ρ(p, q)` (Hopf–Rinow)
  obtain ⟨γ, hγmin, hγ0, hγ1, hρ⟩ := Morse.theorem_10_9' hpre hcomp p q
  obtain ⟨hγpath, hγgeo⟩ := of_isMinimalGeodesic hγmin
  rw [hγ0, hγ1] at hγpath
  have hγps := hγpath.1.1
  have hρL : rho (n := n) p q = Morse.pathLength γ 0 1 := by
    have e : rho (n := n) p q = RoundTrip.BridgePrelude.rho (n := n) p q := rfl
    rw [e, rho_eq]
    have hρ' : Morse.riemDist (N := N) (incl hN p) (incl hN q) =
        ENNReal.ofReal (Morse.pathLength γ 0 1) := hρ
    rw [hρ', ENNReal.toReal_ofReal hγps.isAdmissible.pathLength_nonneg]
  have hEγ : Morse.energy γ 0 1 = rho (n := n) p q ^ 2 := by
    rw [energy_eq_sq hγps hγgeo, hρL]
  -- A: `E(γ) ≤ E(ω)` on `Ω(N; p, q)`
  have hlow : ∀ c ∈ Morse.pathSpace N (incl hN p) (incl hN q),
      rho (n := n) p q ^ 2 ≤ Morse.energy c 0 1 := fun c hc => by
    rw [← hEγ]
    exact hA hN hγpath hγgeo hc
  refine ⟨?_, fun pw hpw => ?_, fun pw hpw => ?_⟩
  · -- the minimum is attained
    obtain ⟨hpw, heq⟩ := lift_mem (n := n) hγpath.1
    refine ⟨_, hpw, ?_⟩
    rw [efun_eq, ← hEγ]
    exact Morse.energy_congr heq
  · rw [efun_eq]
    exact hlow _ (mem_pathSpace hpw)
  · have hc := mem_pathSpace hpw
    rw [efun_eq]
    constructor
    · intro hE
      -- `ω` minimizes `E`, hence is a critical path, hence an unbroken geodesic
      have hcrit : Morse.IsCriticalPath N (incl hN ∘ pw) := by
        intro U α B hα hαc
        have hd := hα.hasDerivAt_energy hN hα.zero_mem
        have hmin : IsLocalMin (fun u => Morse.energy (α u) 0 1) 0 := by
          filter_upwards [hα.isOpen.mem_nhds hα.zero_mem] with u hu
          have h0 : α 0 0 = incl hN p := by
            rw [hαc 0 ⟨le_rfl, zero_le_one⟩]; exact hc.2.2.1
          have h1 : α 0 1 = incl hN q := by
            rw [hαc 1 ⟨zero_le_one, le_rfl⟩]; exact hc.2.2.2
          have hmem := hα.mem_pathSpace hu
          rw [h0, h1] at hmem
          rw [Morse.energy_congr hαc, hE]
          exact hlow _ hmem
        have h0 := hmin.hasDerivAt_eq_zero hd
        rw [h0] at hd
        exact hd
      have hgeo := (Morse.corollary_12_3 hN hc).1 hcrit
      refine ⟨isGeodesic_of_unbroken hgeo, fun pw' a' b' hab' hpw' h0' h1' => ?_⟩
      have hL : arcLen (n := n) pw 0 1 = rho (n := n) p q := by
        rw [arcLen_eq']
        have h2 := energy_eq_sq hc.1 hgeo
        rw [hE] at h2
        have := hc.1.isAdmissible.pathLength_nonneg
        nlinarith [rho_nonneg (n := n) p q]
      rw [hL, arcLen_eq']
      refine rho_le_pathLength (isPiecewiseSmooth_of_isPW hpw') (fun t _ => (pw' t).2) ?_ ?_
      · show incl hN (pw' a') = incl hN p
        rw [h0', hpw.2.1]
      · show incl hN (pw' b') = incl hN q
        rw [h1', hpw.2.2]
    · rintro ⟨hgeo, hlen⟩
      have hgeo' := unbroken_of_isGeodesic (hN := hN) hgeo
      have hminp : Morse.IsMinimalPath N (incl hN ∘ pw) (incl hN p) (incl hN q) := by
        refine ⟨hc, fun c' hc' => ?_⟩
        obtain ⟨hpw', heq'⟩ := lift_mem (n := n) hc'
        have := hlen (lift c' p) 0 1 zero_le_one hpw'.1 (hpw'.2.1.trans hpw.2.1.symm)
          (hpw'.2.2.trans hpw.2.2.symm)
        rw [arcLen_eq', arcLen_eq'] at this
        rwa [pathLength_congr zero_le_one heq'] at this
      refine le_antisymm ?_ (hlow _ hc)
      rw [← hEγ]
      exact hA hN hminp hgeo' hγpath.1

/-- A for complete connected slice submanifolds modelled on `ℝⁿ` (B assumes completeness). -/
def A_complete : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], Morse.IsGeodesicallyComplete hN →
    ∀ {γ : ℝ → V} {p q : V}, Morse.IsMinimalPath N γ p q → Morse.IsUnbrokenGeodesic hN γ →
      ∀ {c : ℝ → V}, c ∈ Morse.pathSpace N p q → Morse.energy γ 0 1 ≤ Morse.energy c 0 1

open Emb Bridge in
/-- **B on embedded manifolds implies A for complete `N`**: a minimal unbroken geodesic is a
blind minimal geodesic (affine reparametrization for the comparison paths on `[a', b']`), so
`E(γ) = d²` by B, and `d² ≤ E(ω)` by B. -/
theorem B_emb_to_A_complete : B_emb → A_complete := by
  intro h V _ _ _ W _ _ _ n N hN _ hcomp γ p q hmin hgeo c hc
  have hγ := hmin.1
  let p' : Bridge.Sub hN := ⟨p, hγ.2.2.1 ▸ hγ.2.1 0 ⟨le_rfl, zero_le_one⟩⟩
  let q' : Bridge.Sub hN := ⟨q, hγ.2.2.2 ▸ hγ.2.1 1 ⟨zero_le_one, le_rfl⟩⟩
  obtain ⟨-, hlow, hchar⟩ := h V W n N hN (geodComplete_iff.2 hcomp) p' q'
  obtain ⟨hpw, heq⟩ := lift_mem (n := n) (p := p') (q := q') hγ
  obtain ⟨hpwc, heqc⟩ := lift_mem (n := n) (p := p') (q := q') hc
  -- the lift of `γ` is a blind minimal geodesic
  have hgeo' : Morse.IsUnbrokenGeodesic hN (incl hN ∘ lift γ p') :=
    ⟨hgeo.1.congr fun t ht => heq ht, hgeo.2.congr fun t ht => (heq (Ioo_subset_Icc_self ht)).symm⟩
  have hmin' : IsMinimal (Bridge.conn (hN := hN)) (lift γ p') 0 1 := by
    refine ⟨isGeodesic_of_unbroken hgeo', fun pw' a' b' hab' hpw' h0' h1' => ?_⟩
    rw [arcLen_eq', arcLen_eq', pathLength_congr zero_le_one heq]
    have hps := isPiecewiseSmooth_of_isPW hpw'
    rcases eq_or_lt_of_le hab' with rfl | hlt
    · -- a constant comparison path
      have hpq : p = q := by
        have : p' = q' := hpw.2.1.symm.trans (h0'.symm.trans (h1'.trans hpw.2.2))
        exact congrArg (incl hN) this
      have hconst : (fun _ : ℝ => p) ∈ Morse.pathSpace N p q :=
        ⟨Morse.IsPiecewiseSmooth.of_contDiffOn contDiffOn_const zero_le_one subset_rfl,
          fun _ _ => p'.2, rfl, hpq⟩
      have := hmin.2 _ hconst
      simp only [Morse.pathLength, deriv_const, norm_zero, intervalIntegral.integral_zero,
        intervalIntegral.integral_same] at this ⊢
      exact this
    · obtain ⟨hps', hlen⟩ := reparam hps hlt
      rw [← hlen]
      refine hmin.2 _ ⟨hps', fun t _ => (pw' _).2, ?_, ?_⟩
      · show incl hN (pw' (a' + (b' - a') * 0)) = p
        rw [mul_zero, add_zero, h0', hpw.2.1]; rfl
      · show incl hN (pw' (a' + (b' - a') * 1)) = q
        rw [mul_one, add_sub_cancel, h1', hpw.2.2]; rfl
  have h1 := (hchar _ hpw).2 hmin'
  have h2 := hlow _ hpwc
  rw [efun_eq] at h1 h2
  rw [Morse.energy_congr heqc] at h2
  rw [← Morse.energy_congr heq, h1]
  exact h2

theorem B_to_A_complete : B → A_complete := fun hB => B_emb_to_A_complete (B_to_B_emb hB)

#rt_check RoundTrip.V8_6.A_to_B_emb [Morse.energy_le_of_isMinimalPath]
#rt_check RoundTrip.V8_6.B_to_A_complete [Morse.energy_le_of_isMinimalPath]
#rt_overlap RoundTrip.V8_6.B_to_A_complete [Morse.energy_le_of_isMinimalPath]

end RoundTrip.V8_6
