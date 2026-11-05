import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_1
import RoundTrip.Bridge

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V7_1

/-- The project's statement (universes instantiated at 0; `IsGeodesicOn` is a definition: `γ`
smooth on an OPEN set `s`, with values in the slice submanifold `N ⊆ V`, and ambient acceleration
`γ''` normal to `N`): velocities of curves in `N` are tangent; a geodesic has `P(γ'') = 0`
(Milnor's `D/dt (dγ/dt) = 0` for the induced connection); on `ℝ` this is
`covDeriv (velocity) = 0`; constant curves are geodesics. -/
def A : Prop :=
  type_of% @Morse.hasDerivAt_mem_tangentSubspace.{0,0,0} ∧
    type_of% @Morse.IsGeodesicOn.tanProj_deriv_deriv.{0,0,0} ∧
    type_of% @Morse.isGeodesicOn_univ_iff_covDeriv.{0,0,0} ∧
    type_of% @Morse.isGeodesicOn_const.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.hasDerivAt_mem_tangentSubspace, @Morse.IsGeodesicOn.tanProj_deriv_deriv,
    @Morse.isGeodesicOn_univ_iff_covDeriv, @Morse.isGeodesicOn_const⟩

/-- B is provable outright: with B's definitions, `IsGeodesic` is literally "the velocity is
smooth along `c` and `D/dt` of it is `0`", i.e. `IsParallel` of the velocity. The hypothesis A
(about embedded `N ⊆ V`) is not used and could not be: B concerns abstract manifolds. -/
theorem B_holds : B := by
  intro n M _ _ _ _ _ _ _ cov _ c s
  refine ⟨⟨fun ⟨hI, hc, hv, hD⟩ => ⟨hI, hc, hv, fun _ => 0, hD, fun _ _ => rfl⟩,
    fun ⟨hI, hc, hv, W, ⟨hsm, D, hD, hDW⟩, hW⟩ =>
      ⟨hI, hc, hv, hsm, D, hD, fun t ht => (hDW t ht).trans (hW t ht)⟩⟩, ?_⟩
  exact ⟨fun ⟨hI, hc, _, hD⟩ => ⟨hI, hc, hD⟩, fun ⟨hI, hc, hD⟩ => ⟨hI, hc, hD.1, hD⟩⟩

theorem A_to_B : A → B := fun _ => B_holds

/-- B ⇒ A holds only because A is provable outright from project lemmas outside the item
(`hasDerivWithinAt_mem_tangentSubspace` of Chapter 8 for the tangency of velocities, and
`tanProj_eq_zero_iff`); B, about abstract manifolds, does not specialize to `N ⊆ V`. -/
theorem B_to_A : B → A := by
  intro _
  have hT : type_of% @Morse.hasDerivAt_mem_tangentSubspace.{0,0,0} := by
    intro V _ _ Z _ _ W _ _ N hN _ _ _ c t v hc hmem
    exact Morse.hasDerivWithinAt_mem_tangentSubspace hN hc.hasDerivWithinAt
      (uniqueDiffWithinAt_of_mem_nhds hmem) (fun _ h => h) hmem.self_of_nhds
  refine ⟨hT, ?_, ?_, ?_⟩
  · intro V _ _ Z _ _ W _ _ N hN _ γ s h t ht
    exact (Morse.tanProj_eq_zero_iff hN).2 (h.normal t ht)
  · intro V _ _ Z _ _ W _ _ N hN _ c hc
    constructor
    · intro h t
      exact (Morse.tanProj_eq_zero_iff hN).2 (h.normal t (mem_univ t))
    · intro h
      exact ⟨isOpen_univ, fun t _ => (c t).2, hc.contDiffOn,
        fun t _ => (Morse.tanProj_eq_zero_iff hN).1 (h t)⟩
  · intro V _ _ Z _ _ W _ _ N hN q hq s hs
    refine ⟨hs, fun _ _ => hq, contDiffOn_const, fun t _ => ?_⟩
    simp

#rt_check RoundTrip.V7_1.A_to_B [Morse.hasDerivAt_mem_tangentSubspace,
  Morse.IsGeodesicOn.tanProj_deriv_deriv, Morse.isGeodesicOn_univ_iff_covDeriv,
  Morse.isGeodesicOn_const]
#rt_check RoundTrip.V7_1.B_to_A [Morse.hasDerivAt_mem_tangentSubspace,
  Morse.IsGeodesicOn.tanProj_deriv_deriv, Morse.isGeodesicOn_univ_iff_covDeriv,
  Morse.isGeodesicOn_const]
#rt_overlap RoundTrip.V7_1.B_to_A [Morse.hasDerivAt_mem_tangentSubspace,
  Morse.IsGeodesicOn.tanProj_deriv_deriv, Morse.isGeodesicOn_univ_iff_covDeriv,
  Morse.isGeodesicOn_const]

/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ`, the induced metric and the induced Levi-Civita connection `Bridge.conn` (`B_emb`;
`B_to_B_emb`). Like B, `B_emb` is a tautology of the blind definitions, so `A_to_B_emb` is vacuous.
The substantive embedded comparison is the dictionary between Milnor's definition and the
project's:
* `Emb.isGeodesic_iff_interior`: a blind geodesic of `Bridge.conn` on any interval `s` is a curve,
  smooth in `V` on `s`, which is a project `IsGeodesicOn` on `interior s`;
* `Emb.isParallel_vel_iff_covDeriv`: Milnor's "the velocity field is parallel" for
  `Bridge.conn` on `ℝ` is the project's `∀ t, covDeriv hN c (velocity c) t = 0`.
With them, B_emb's second clause on `ℝ` is A's `isGeodesicOn_univ_iff_covDeriv` (`B_emb_to_A3`,
for model `ℝⁿ`). -/

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

/-- **Dictionary: "the velocity is parallel"** on `ℝ`, for the induced connection, is the
project's `covDeriv hN c (velocity c) = 0`. -/
theorem isParallel_vel_iff_covDeriv {c : ℝ → Bridge.Sub hN} (hc : ContDiff ℝ ∞ (incl hN ∘ c)) :
    BridgePrelude.IsParallel (conn (hN := hN)) c univ (BridgePrelude.vel (n := n) c univ) ↔
      ∀ t, Morse.covDeriv hN c (Morse.velocity c) t = 0 := by
  have hs : IsIntv (univ : Set ℝ) := ⟨ordConnected_univ, uniqueDiffOn_univ⟩
  have hc' : BridgePrelude.IsSmoothCurve (n := n) c univ := isSmoothCurve_iff.2 hc.contDiffOn
  have hamb : ambA c (BridgePrelude.vel (n := n) c univ) = deriv (incl hN ∘ c) :=
    funext fun t => (ambA_vel_eqOn uniqueDiffOn_univ hc' (mem_univ t)).trans (by rw [derivWithin_univ])
  have hvel : Morse.velocity (N := N) c = deriv (incl hN ∘ c) := rfl
  unfold BridgePrelude.IsParallel
  rw [hasCovDeriv_iff' hs hc']
  constructor
  · rintro ⟨-, h⟩ t
    have := h t (mem_univ t)
    rw [hamb, derivWithin_univ] at this
    show Morse.tanProj hN (c t) (deriv (Morse.velocity c) t) = 0
    rw [hvel]
    exact this.symm.trans (D_tzero (c t))
  · intro h
    refine ⟨isSmoothAlong_iff.2 ⟨hc', ?_⟩, fun t _ => ?_⟩
    · rw [hamb]
      exact (contDiff_infty_iff_deriv.1 hc).2.contDiffOn
    · rw [hamb, derivWithin_univ]
      have : Morse.tanProj hN (c t) (deriv (deriv (incl hN ∘ c)) t) = 0 := h t
      exact (D_tzero (c t)).trans this.symm

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], ∀ (c : ℝ → Bridge.Sub hN) (s : Set ℝ),
    (IsGeodesic (Bridge.conn (hN := hN)) c s ↔ IsIntv s ∧ IsSmoothCurve (n := n) c s ∧
      IsSmoothAlong c s (vel (n := n) c s) ∧
      ∃ W : FA n c, HasCovDeriv (Bridge.conn (hN := hN)) c s (vel (n := n) c s) W ∧
        ∀ t ∈ s, W t = 0) ∧
    (IsGeodesic (Bridge.conn (hN := hN)) c s ↔ IsIntv s ∧ IsSmoothCurve (n := n) c s ∧
      IsParallel (Bridge.conn (hN := hN)) c s (vel (n := n) c s))

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds** — vacuously: `B_emb` holds outright (`B_holds`). -/
theorem A_to_B_emb : A → B_emb := fun _ => B_to_B_emb B_holds

/-- **B on embedded manifolds gives A's `isGeodesicOn_univ_iff_covDeriv`** (model `ℝⁿ`): B_emb's
second clause on `ℝ`, read through `isGeodesic_iff_isGeodesicOn` and
`Emb.isParallel_vel_iff_covDeriv`. (`N` connected, since B, hence B_emb, assumes
`ConnectedSpace`.) -/
theorem B_emb_to_A3 (hB : B_emb) : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (n : ℕ) (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (c : ℝ → N), ContDiff ℝ ∞ (fun t => (c t : V)) →
      (Morse.IsGeodesicOn hN (fun t => (c t : V)) univ ↔
        ∀ t, Morse.covDeriv hN c (Morse.velocity c) t = 0) := by
  intro V _ _ _ W _ _ _ n N hN _ c hc
  let c' : ℝ → Bridge.Sub hN := c
  have hc' : ContDiff ℝ ∞ (Bridge.incl hN ∘ c') := hc
  have h1 := (Bridge.isGeodesic_iff_isGeodesicOn (c := c') isOpen_univ ordConnected_univ).symm
  have h2 := (hB V W n N hN c' univ).2
  have h3 := Emb.isParallel_vel_iff_covDeriv hc'
  have hs : IsIntv (univ : Set ℝ) := ⟨ordConnected_univ, uniqueDiffOn_univ⟩
  have hsm : IsSmoothCurve (n := n) c' univ := Bridge.isSmoothCurve_iff.2 hc'.contDiffOn
  refine h1.trans (h2.trans ?_)
  exact ⟨fun h => h3.1 h.2.2, fun h => ⟨hs, hsm, h3.2 h⟩⟩

#rt_check RoundTrip.V7_1.A_to_B_emb [Morse.hasDerivAt_mem_tangentSubspace,
  Morse.IsGeodesicOn.tanProj_deriv_deriv, Morse.isGeodesicOn_univ_iff_covDeriv,
  Morse.isGeodesicOn_const]
#rt_check RoundTrip.V7_1.B_emb_to_A3 [Morse.hasDerivAt_mem_tangentSubspace,
  Morse.IsGeodesicOn.tanProj_deriv_deriv, Morse.isGeodesicOn_univ_iff_covDeriv,
  Morse.isGeodesicOn_const]

end RoundTrip.V7_1
