import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_2
import RoundTrip.Bridge

open Set Filter Topology Bundle
open scoped ContDiff Manifold

namespace RoundTrip.V7_2

/-- The project's statement (universes instantiated at 0): For a geodesic `γ` of a slice submanifold `N ⊆ V` on an open set `s` (`IsGeodesicOn`: ambient `γ''` normal to `N`): `d/dt ‖γ'‖² = 0`, constant speed on preconnected `s`, length on `[a,b] ⊆ s` is `‖γ'(a)‖ (b − a)`, and `t ↦ γ(at + b)` is a geodesic on the preimage. -/
def A : Prop :=
  type_of% @Morse.IsGeodesicOn.hasDerivAt_norm_sq.{0,0,0} ∧
    type_of% @Morse.IsGeodesicOn.norm_deriv_eq.{0,0,0} ∧
    type_of% @Morse.IsGeodesicOn.pathLength_eq.{0,0,0} ∧
    type_of% @Morse.IsGeodesicOn.comp_mul_add.{0,0,0}

theorem A_holds : A := ⟨@Morse.IsGeodesicOn.hasDerivAt_norm_sq, @Morse.IsGeodesicOn.norm_deriv_eq, @Morse.IsGeodesicOn.pathLength_eq, @Morse.IsGeodesicOn.comp_mul_add⟩

/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ`, the induced metric and the induced Levi-Civita connection `Bridge.conn` (`B_emb`;
`B_to_B_emb`). Through the Bridge's dictionary a blind geodesic on an interval `s` is a curve smooth
on `s` that is a project geodesic on `interior s` (`Emb.isGeodesic_iff_interior`), and its blind
speed is `‖derivWithin γ s‖`. `A_to_B_emb`: constant speed from A's `norm_deriv_eq` on
`interior s`, extended to the endpoints by continuity; arc length by integrating the constant
speed; homogeneity from A's `comp_mul_add` on `interior s` (`k ≠ 0`), resp. constant curves
(`k = 0`). -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

/-- Every point of a nondegenerate interval lies in the closure of its interior. -/
theorem subset_closure_interior {s : Set ℝ} (hs : IsIntv s) : s ⊆ closure (interior s) := by
  intro t ht
  obtain ⟨u, ⟨-, hu⟩, hne⟩ :=
    accPt_iff_nhds.1 (uniqueDiffWithinAt_iff_accPt.1 (hs.2 t ht)) univ univ_mem
  have hsub : Ioo (min t u) (max t u) ⊆ interior s :=
    interior_maximal (Ioo_subset_Icc_self.trans (hs.1.uIcc_subset ht hu)) isOpen_Ioo
  refine closure_mono hsub ?_
  rw [closure_Ioo (min_lt_max.2 hne.symm).ne]
  exact ⟨min_le_left _ _, le_max_left _ _⟩

/-- A function continuous on a nondegenerate interval and constant on its interior is constant. -/
theorem eqOn_of_interior {X : Type*} [TopologicalSpace X] [T2Space X] {s : Set ℝ} (hs : IsIntv s)
    {h : ℝ → X} {x : X} (hh : ContinuousOn h s) (h0 : ∀ t ∈ interior s, h t = x) :
    ∀ t ∈ s, h t = x := by
  intro t ht
  have h1 := ((hh t ht).mono interior_subset).mem_closure_image (subset_closure_interior hs ht)
  have h2 : h '' interior s ⊆ {x} := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact h0 τ hτ
  have := closure_mono h2 h1
  rwa [closure_singleton] at this

theorem derivWithin_eq_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    {s : Set ℝ} {t : ℝ} (ht : t ∈ interior s) : derivWithin f s t = deriv f t :=
  derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 ht)

theorem derivWithin2_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    {s : Set ℝ} {t : ℝ} (ht : t ∈ interior s) :
    derivWithin (derivWithin f s) s t = deriv (deriv f) t := by
  rw [derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 ht)]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_interior.mem_nhds ht] with u hu
  exact derivWithin_eq_deriv hu

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- **Dictionary: geodesics on any interval.** A blind geodesic of the induced connection on `s`
is a curve smooth (in `V`) on the interval `s` which is a project geodesic on `interior s`. -/
theorem isGeodesic_iff_interior {c : ℝ → Bridge.Sub hN} {s : Set ℝ} :
    BridgePrelude.IsGeodesic (conn (hN := hN)) c s ↔ IsIntv s ∧ ContDiffOn ℝ ∞ (incl hN ∘ c) s ∧
      Morse.IsGeodesicOn hN (incl hN ∘ c) (interior s) := by
  rw [isGeodesic_iff]
  constructor
  · rintro ⟨hs, hc, hP⟩
    refine ⟨hs, hc, isOpen_interior, fun t _ => (c t).2, hc.mono interior_subset, fun t ht => ?_⟩
    rw [← Morse.tanProj_eq_zero_iff, ← derivWithin2_eq ht]
    exact hP t (interior_subset ht)
  · rintro ⟨hs, hc, hg⟩
    refine ⟨hs, hc, eqOn_of_interior hs ?_ fun t ht => ?_⟩
    · have h1 : ContinuousOn (derivWithin (derivWithin (incl hN ∘ c) s) s) s :=
        (hc.derivWithin hs.2 (m := 1) (WithTop.coe_le_coe.2 le_top)).continuousOn_derivWithin hs.2 le_rfl
      have h2 : ContinuousOn (fun t => P hN (c t)) s :=
        contMDiff_P.continuous.comp_continuousOn (contMDiffOn_curve_iff.2 hc).continuousOn
      exact h2.clm_apply h1
    · rw [derivWithin2_eq ht]
      exact (Morse.tanProj_eq_zero_iff hN).2 (hg.normal t ht)

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    ∀ (c : ℝ → Bridge.Sub hN) (s : Set ℝ), IsGeodesic (Bridge.conn (hN := hN)) c s →
    (∃ r : ℝ, 0 ≤ r ∧ (∀ t ∈ s, ‖vel (n := n) c s t‖ = r) ∧
      ∀ t₀ ∈ s, ∀ t ∈ s, ∫ u in t₀..t, ‖vel (n := n) c s u‖ = r * (t - t₀)) ∧
    ∀ k : ℝ, IsGeodesic (Bridge.conn (hN := hN)) (fun t => c (k * t)) {t | k * t ∈ s}

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds** (uses A's `norm_deriv_eq` and `comp_mul_add`). -/
theorem A_to_B_emb (hA : A) : B_emb := by
  intro V _ _ _ W _ _ _ n N hN _ c s hg
  have hg' : BridgePrelude.IsGeodesic (Bridge.conn (hN := hN)) c s := hg
  obtain ⟨hs, hc, hgi⟩ := Emb.isGeodesic_iff_interior.1 hg'
  have hspeed : ∀ t ∈ s, ‖vel (n := n) c s t‖ = ‖derivWithin (Bridge.incl hN ∘ c) s t‖ :=
    fun t ht => (Bridge.norm_eq _ _).trans
      (congrArg norm (Bridge.D_vel (Bridge.isSmoothCurve_iff.2 hc) hs.2 ht))
  have hcont : ContinuousOn (fun t => ‖derivWithin (Bridge.incl hN ∘ c) s t‖) s :=
    (hc.continuousOn_derivWithin hs.2 (by simp)).norm
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ ∀ t ∈ s, ‖derivWithin (Bridge.incl hN ∘ c) s t‖ = r := by
    rcases (interior s).eq_empty_or_nonempty with he | ⟨t₀, ht₀⟩
    · refine ⟨0, le_rfl, fun t ht => ?_⟩
      have := Emb.subset_closure_interior hs ht
      rw [he, closure_empty] at this
      exact absurd this (notMem_empty t)
    · refine ⟨‖deriv (Bridge.incl hN ∘ c) t₀‖, norm_nonneg _,
        Emb.eqOn_of_interior hs hcont fun t ht => ?_⟩
      show ‖derivWithin (Bridge.incl hN ∘ c) s t‖ = _
      rw [Emb.derivWithin_eq_deriv ht]
      exact hA.2.1 hgi (isPreconnected_iff_ordConnected.2 hs.1.interior) ht ht₀
  refine ⟨⟨r, hr0, fun t ht => (hspeed t ht).trans (hr t ht), fun t₀ ht₀ t ht => ?_⟩, fun k => ?_⟩
  · rw [intervalIntegral.integral_congr (g := fun _ => r) fun u hu =>
      (hspeed u (hs.1.uIcc_subset ht₀ ht hu)).trans (hr u (hs.1.uIcc_subset ht₀ ht hu)),
      intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  · show BridgePrelude.IsGeodesic _ _ _
    rw [Emb.isGeodesic_iff_interior]
    rcases eq_or_ne k 0 with rfl | hk
    · have hfun : (Bridge.incl hN ∘ fun t => c (0 * t)) = fun _ => Bridge.incl hN (c 0) := by
        funext t; simp
      rw [hfun]
      by_cases h0 : (0 : ℝ) ∈ s
      · have hset : {t : ℝ | 0 * t ∈ s} = univ := by ext t; simp [h0]
        rw [hset, interior_univ]
        exact ⟨⟨ordConnected_univ, uniqueDiffOn_univ⟩, contDiffOn_const,
          Morse.isGeodesicOn_const hN (c 0).2 isOpen_univ⟩
      · have hset : {t : ℝ | 0 * t ∈ s} = ∅ := by ext t; simp [h0]
        rw [hset, interior_empty]
        exact ⟨⟨ordConnected_empty, uniqueDiffOn_empty⟩, contDiffOn_empty,
          Morse.isGeodesicOn_const hN (c 0).2 isOpen_empty⟩
    · have hoc : {t : ℝ | k * t ∈ s}.OrdConnected :=
        convex_iff_ordConnected.1
          ((convex_iff_ordConnected.2 hs.1).linear_preimage (LinearMap.mulLeft ℝ k))
      have hud : UniqueDiffOn ℝ {t : ℝ | k * t ∈ s} := by
        let e : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ k hk).toContinuousLinearEquiv
        exact (e.uniqueDiffOn_preimage_iff (s := s)).2 hs.2
      have hset : (fun t : ℝ => k * t + 0) ⁻¹' interior s = interior {t : ℝ | k * t ∈ s} := by
        have := (Homeomorph.mulLeft₀ k hk).preimage_interior s
        rw [Homeomorph.coe_mulLeft₀] at this
        simp only [add_zero]
        exact this
      have hfun : (fun t => (Bridge.incl hN ∘ c) (k * t + 0)) = Bridge.incl hN ∘ fun t => c (k * t) := by
        funext t; simp
      have h4 := hA.2.2.2 hgi k 0
      rw [hset, hfun] at h4
      exact ⟨⟨hoc, hud⟩, hc.comp (contDiff_const.mul contDiff_id).contDiffOn fun t ht => ht, h4⟩

#rt_check RoundTrip.V7_2.A_to_B_emb [Morse.IsGeodesicOn.hasDerivAt_norm_sq,
  Morse.IsGeodesicOn.norm_deriv_eq, Morse.IsGeodesicOn.pathLength_eq,
  Morse.IsGeodesicOn.comp_mul_add]

/-! ### B on embedded manifolds ⇒ A (except the translation in `comp_mul_add`)

B, hence B_emb, assumes `M` connected; a project geodesic on a preconnected `s` stays in one
component `N ∩ O` of `N`, an open part with the same tangent spaces, to which B_emb applies. -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! Changing the model `Z` to `ℝ^{dim Z}` (copied from `Items/V7_28.lean`). -/

/-- A linear equivalence `Z ≃ ℝᵐ`, `m = dim Z`. -/
noncomputable def eZ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] :
    Z ≃L[ℝ] Bridge.Rn (Module.finrank ℝ Z) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

/-- A slice chart modelled on `Z`, read in `ℝᵐ`. -/
noncomputable def chartRn {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) :
    Milnor.SliceChart 𝓘(ℝ, V) (Bridge.Rn (Module.finrank ℝ Z)) W N where
  φ := σ.φ.trans
    ((eZ Z).prodCongr (ContinuousLinearEquiv.refl ℝ W)).toDiffeomorph.toPartialDiffeomorph
  x₀ := σ.x₀
  x₀_mem := σ.x₀_mem
  x₀_source := ⟨σ.x₀_source, trivial⟩
  slice := fun p hp => σ.slice p hp.1

theorem isSliceRn {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn (Module.finrank ℝ Z)) W N :=
  fun p hp => ⟨chartRn (hN p hp).choose, ⟨(hN p hp).choose_spec, trivial⟩⟩

theorem tangentSubspace_rn {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (q : N) :
    Morse.tangentSubspace (isSliceRn hN) q = Morse.tangentSubspace hN q := by
  obtain ⟨σ, hσ⟩ := hN q q.2
  rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam (isSliceRn hN) (chartRn σ) ⟨hσ, trivial⟩,
    Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ]
  have e1 : Morse.sliceParam (chartRn σ) = Morse.sliceParam σ ∘ (eZ Z).symm := rfl
  have e2 : ((chartRn σ).φ q).1 = eZ Z (σ.φ q).1 := rfl
  rw [e1, e2, ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearEquiv.symm_apply_apply]
  exact LinearMap.range_comp_of_range_eq_top
    ((fderiv ℝ (Morse.sliceParam σ) (σ.φ q).1 : Z →L[ℝ] V) : Z →ₗ[ℝ] V)
    (LinearMap.range_eq_top.2 (eZ Z).symm.surjective)

theorem isGeodesicOn_rn {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {γ : ℝ → V} {s : Set ℝ}
    (h : Morse.IsGeodesicOn hN γ s) : Morse.IsGeodesicOn (isSliceRn hN) γ s :=
  ⟨h.isOpen, h.mem, h.contDiffOn, fun t ht => by
    rw [tangentSubspace_rn]
    exact h.normal t ht⟩

theorem isGeodesicOn_of_rn {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {γ : ℝ → V} {s : Set ℝ}
    (h : Morse.IsGeodesicOn (isSliceRn hN) γ s) : Morse.IsGeodesicOn hN γ s :=
  ⟨h.isOpen, h.mem, h.contDiffOn, fun t ht => by
    rw [← tangentSubspace_rn]
    exact h.normal t ht⟩

/-! Connected components (adapted from `Items/V7_28.lean`). -/

theorem exists_component {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {m : ℕ} {N : Set V}
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn m) W N) (q : N) :
    ∃ O : Set V, IsOpen O ∧ IsConnected (N ∩ O) ∧ N ∩ O = connectedComponentIn N (q : V) := by
  let _ := hN.chartedSpace
  have := ChartedSpace.locallyConnectedSpace (Bridge.Rn m) N
  have hK : IsOpen (connectedComponent q) := isOpen_connectedComponent
  obtain ⟨O, hO, hOK⟩ := isOpen_induced_iff.1 hK
  have hNO : N ∩ O = connectedComponentIn N (q : V) := by
    rw [connectedComponentIn_eq_image q.2]
    ext x
    constructor
    · rintro ⟨hxN, hxO⟩
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      rw [← hOK]
      exact hxO
    · rintro ⟨y, hyK, rfl⟩
      refine ⟨y.2, ?_⟩
      rw [← hOK] at hyK
      exact hyK
  refine ⟨O, hO, ?_, hNO⟩
  rw [hNO]
  exact isConnected_connectedComponentIn_iff.2 q.2

theorem tangentSubspace_inter {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {O : Set V}
    (hO : IsOpen O) (x : V) (hx : x ∈ N ∩ O) :
    Morse.tangentSubspace (Morse.IsSliceSubmanifold.inter_isOpen hN hO) ⟨x, hx⟩ =
      Morse.tangentSubspace hN ⟨x, hx.1⟩ := by
  obtain ⟨σ, hσ⟩ := hN x hx.1
  rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam _ (Morse.SliceChart.inter σ hO hx hσ)
    ⟨hσ, hx.2⟩, Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ]
  rfl

end Emb

open Emb in
/-- **What B_emb says about a project geodesic** on a preconnected open `s` of a slice submanifold
modelled on `ℝⁿ`: constant speed `r`, `∫_{t₀}^t ‖γ'‖ = r (t − t₀)`, and `t ↦ γ(kt)` is a project
geodesic on `{t | kt ∈ s}`. -/
theorem of_B_emb (hB : B_emb) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {n : ℕ} {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}
    {γ : ℝ → V} {s : Set ℝ} (h : Morse.IsGeodesicOn hN γ s) (hs : IsPreconnected s) :
    (∃ r : ℝ, (∀ t ∈ s, ‖deriv γ t‖ = r) ∧
      ∀ t₀ ∈ s, ∀ t ∈ s, ∫ u in t₀..t, ‖deriv γ u‖ = r * (t - t₀)) ∧
    ∀ k : ℝ, Morse.IsGeodesicOn hN (fun t => γ (k * t)) {t | k * t ∈ s} := by
  have hoc : s.OrdConnected := isPreconnected_iff_ordConnected.1 hs
  have hopen' : ∀ k : ℝ, IsOpen {t : ℝ | k * t ∈ s} :=
    fun k => h.isOpen.preimage (continuous_const.mul continuous_id)
  rcases s.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · refine ⟨⟨0, fun t ht => ht.elim, fun t ht => ht.elim⟩, fun k => ?_⟩
    have : {t : ℝ | k * t ∈ (∅ : Set ℝ)} = ∅ := by ext; simp
    rw [this]
    exact ⟨isOpen_empty, fun t ht => ht.elim, contDiffOn_empty, fun t ht => ht.elim⟩
  -- the component of `γ t₀`
  obtain ⟨O, hO, hconn, hNO⟩ := exists_component hN ⟨γ t₀, h.mem t₀ ht₀⟩
  have hmem : ∀ t ∈ s, γ t ∈ N ∩ O := by
    have hsub : γ '' s ⊆ connectedComponentIn N (γ t₀) :=
      (hs.image γ h.contDiffOn.continuousOn).subset_connectedComponentIn ⟨t₀, ht₀, rfl⟩
        (by rintro _ ⟨t, ht, rfl⟩; exact h.mem t ht)
    intro t ht
    rw [hNO]
    exact hsub ⟨t, ht, rfl⟩
  set hN' := Morse.IsSliceSubmanifold.inter_isOpen hN hO
  have hT : ∀ x (hx : x ∈ N ∩ O), Morse.tangentSubspace hN' ⟨x, hx⟩ =
      Morse.tangentSubspace hN ⟨x, hx.1⟩ := tangentSubspace_inter hN hO
  have h' : Morse.IsGeodesicOn hN' γ s := ⟨h.isOpen, hmem, h.contDiffOn, fun t ht => by
    rw [hT]
    exact h.normal t ht⟩
  have : ConnectedSpace (Bridge.Sub hN') := isConnected_iff_connectedSpace.1 hconn
  let q : Bridge.Sub hN' := ⟨γ t₀, hmem t₀ ht₀⟩
  set c := Bridge.lift γ q
  have e : EqOn (Bridge.incl hN' ∘ c) γ s := fun t ht => Bridge.incl_lift q (hmem t ht)
  have g := (Bridge.isGeodesic_iff_isGeodesicOn h.isOpen hoc).2 (h'.congr e.symm)
  obtain ⟨⟨r, -, hr, hint⟩, hk⟩ := hB V W n (N ∩ O) hN' c s g
  have hv : ∀ t ∈ s, ‖vel (n := n) c s t‖ = ‖deriv γ t‖ := fun t ht => by
    refine (Bridge.norm_eq _ _).trans (congrArg norm ?_)
    refine (Bridge.D_vel (Bridge.isSmoothCurve_iff.2 (Bridge.isGeodesic_iff.1 g).2.1)
      h.isOpen.uniqueDiffOn ht).trans ?_
    rw [derivWithin_congr e (e ht)]
    exact derivWithin_of_isOpen h.isOpen ht
  refine ⟨⟨r, fun t ht => (hv t ht).symm.trans (hr t ht), fun t₁ ht₁ t ht => ?_⟩, fun k => ?_⟩
  · rw [← hint t₁ ht₁ t ht]
    exact intervalIntegral.integral_congr fun u hu => (hv u (hoc.uIcc_subset ht₁ ht hu)).symm
  · have hoc' : {t : ℝ | k * t ∈ s}.OrdConnected :=
      convex_iff_ordConnected.1
        ((convex_iff_ordConnected.2 hoc).linear_preimage (LinearMap.mulLeft ℝ k))
    have gk := (Bridge.isGeodesic_iff_isGeodesicOn (hopen' k) hoc').1 (hk k)
    have gk' : Morse.IsGeodesicOn hN' (fun t => γ (k * t)) {t | k * t ∈ s} :=
      gk.congr fun t ht => e ht
    exact ⟨gk'.isOpen, fun t ht => (gk'.mem t ht).1, gk'.contDiffOn, fun t ht => by
      have := gk'.normal t ht
      rwa [hT] at this⟩

/-- The part of A that B covers: A's `hasDerivAt_norm_sq`, `norm_deriv_eq`, `pathLength_eq`, and
`comp_mul_add` without the translation (`t ↦ γ(at)`; finite-dimensional spaces as in B_emb). -/
def A_part : Prop :=
  type_of% @Morse.IsGeodesicOn.hasDerivAt_norm_sq.{0,0,0} ∧
    type_of% @Morse.IsGeodesicOn.norm_deriv_eq.{0,0,0} ∧
    type_of% @Morse.IsGeodesicOn.pathLength_eq.{0,0,0} ∧
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type} [NormedAddCommGroup Z]
      [NormedSpace ℝ Z] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
      {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} [FiniteDimensional ℝ V]
      [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] {γ : ℝ → V} {s : Set ℝ},
      Morse.IsGeodesicOn hN γ s → ∀ a : ℝ,
        Morse.IsGeodesicOn hN (fun t => γ (a * t)) ((fun t => a * t) ⁻¹' s)

theorem A_to_A_part : A → A_part := fun hA =>
  ⟨hA.1, hA.2.1, hA.2.2.1, fun h a => by simpa using hA.2.2.2 h a 0⟩

/-- **B on embedded manifolds implies the part of A it covers** (any model `Z`, via
`ℝ^{dim Z}`; non-connected `N` via components). -/
theorem B_emb_to_A_part (hB : B_emb) : A_part := by
  have hND : type_of% @Morse.IsGeodesicOn.norm_deriv_eq.{0,0,0} := by
    intro V _ _ Z _ _ W _ _ N hN _ _ _ γ s h hs t t' ht ht'
    obtain ⟨⟨r, hr, -⟩, -⟩ := of_B_emb hB (Emb.isGeodesicOn_rn h) hs
    rw [hr t ht, hr t' ht']
  refine ⟨?_, hND, ?_, ?_⟩
  · intro V _ _ Z _ _ W _ _ N hN _ _ _ γ s h t ht
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 h.isOpen t ht
    have hB' := h.mono Metric.isOpen_ball hball
    have hev : (fun τ => ‖deriv γ τ‖ ^ 2) =ᶠ[𝓝 t] fun _ => ‖deriv γ t‖ ^ 2 := by
      filter_upwards [Metric.ball_mem_nhds t hε] with τ hτ
      rw [hND hB' (convex_ball t ε).isPreconnected hτ (Metric.mem_ball_self hε)]
    exact (hasDerivAt_const t _).congr_of_eventuallyEq hev
  · intro V _ _ _ Z _ _ _ W _ _ _ N hN γ s h hs a b hab hsub t₀ ht₀
    obtain ⟨⟨r, hr, hint⟩, -⟩ := of_B_emb hB (Emb.isGeodesicOn_rn h) hs
    have ha : a ∈ s := hsub ⟨le_rfl, hab⟩
    have hb : b ∈ s := hsub ⟨hab, le_rfl⟩
    rw [Morse.pathLength, hint a ha b hb, hr t₀ ht₀]
  · intro V _ _ Z _ _ W _ _ N hN _ _ _ γ s h k
    refine ⟨h.isOpen.preimage (continuous_const.mul continuous_id), fun t ht => h.mem _ ht,
      h.contDiffOn.comp (contDiff_const.mul contDiff_id).contDiffOn fun t ht => ht,
      fun t ht => ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 h.isOpen (k * t) ht
    have hB' := Emb.isGeodesicOn_rn (h.mono Metric.isOpen_ball hball)
    have hk := Emb.isGeodesicOn_of_rn (hN := hN) ((of_B_emb hB hB' (convex_ball (k * t) ε).isPreconnected).2 k)
    exact hk.normal t (Metric.mem_ball_self hε)

#rt_check RoundTrip.V7_2.B_emb_to_A_part [Morse.IsGeodesicOn.hasDerivAt_norm_sq,
  Morse.IsGeodesicOn.norm_deriv_eq, Morse.IsGeodesicOn.pathLength_eq,
  Morse.IsGeodesicOn.comp_mul_add]
/-- **B ⇒ the part of A it covers** (revised: via `RoundTrip/Bridge.lean`). -/
theorem B_to_A_part : B → A_part := fun hB => B_emb_to_A_part (B_to_B_emb hB)

#rt_check RoundTrip.V7_2.B_to_A_part [Morse.IsGeodesicOn.hasDerivAt_norm_sq,
  Morse.IsGeodesicOn.norm_deriv_eq, Morse.IsGeodesicOn.pathLength_eq,
  Morse.IsGeodesicOn.comp_mul_add]
#rt_overlap RoundTrip.V7_2.B_emb_to_A_part [Morse.IsGeodesicOn.hasDerivAt_norm_sq,
  Morse.IsGeodesicOn.norm_deriv_eq, Morse.IsGeodesicOn.pathLength_eq,
  Morse.IsGeodesicOn.comp_mul_add]

end RoundTrip.V7_2
