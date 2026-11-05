import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.V7_25

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

set_option linter.unusedSectionVars false

/-! Glue for the embedded case of `B` (partly copied from `RoundTrip/Items/V7_28.lean`). -/

namespace RoundTrip.V7_25.Aux

open RoundTrip.Bridge

section Lift

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

/-- A project geodesic on an open set `s ⊇ [a, b]` lifts to a blind geodesic on `[a, b]`. -/
theorem isGeodesic_lift_Icc {γ : ℝ → V} {s : Set ℝ} (hγ : Morse.IsGeodesicOn hN γ s) {a b : ℝ}
    (hab : a < b) (hsub : Icc a b ⊆ s) (x : Sub hN) :
    BridgePrelude.IsGeodesic (conn (hN := hN)) (lift γ x) (Icc a b) ∧
      EqOn (incl hN ∘ lift γ x) γ (Icc a b) ∧
      derivWithin (incl hN ∘ lift γ x) (Icc a b) a = deriv γ a := by
  set I := Icc a b
  have uI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have heq : EqOn (incl hN ∘ lift γ x) γ I := fun t ht => incl_lift x (hγ.mem t (hsub ht))
  have hd : EqOn (derivWithin (incl hN ∘ lift γ x) I) (deriv γ) I := fun t ht => by
    rw [derivWithin_congr heq (heq ht)]
    exact (hγ.hasDerivAt (hsub ht)).hasDerivWithinAt.derivWithin (uI t ht)
  have hdd : ∀ t ∈ I, derivWithin (derivWithin (incl hN ∘ lift γ x) I) I t =
      deriv (deriv γ) t := fun t ht => by
    rw [derivWithin_congr hd (hd ht)]
    exact (hγ.hasDerivAt_deriv (hsub ht)).hasDerivWithinAt.derivWithin (uI t ht)
  refine ⟨isGeodesic_iff.2 ⟨⟨ordConnected_Icc, uI⟩, (hγ.contDiffOn.mono hsub).congr heq,
    fun t ht => ?_⟩, heq, hd ⟨le_rfl, hab.le⟩⟩
  rw [hdd t ht, lift_of_mem x (hγ.mem t (hsub ht))]
  exact hγ.tanProj_deriv_deriv (hsub ht)

end Lift

section Model

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A linear equivalence `Z ≃ ℝᵐ`, `m = dim Z`. -/
def eZ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] :
    Z ≃L[ℝ] Bridge.Rn (finrank ℝ Z) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}

/-- A slice chart modelled on `Z`, read in `ℝᵐ`. -/
def chartRn (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) :
    Milnor.SliceChart 𝓘(ℝ, V) (Bridge.Rn (finrank ℝ Z)) W N where
  φ := σ.φ.trans ((eZ Z).prodCongr (ContinuousLinearEquiv.refl ℝ W)).toDiffeomorph.toPartialDiffeomorph
  x₀ := σ.x₀
  x₀_mem := σ.x₀_mem
  x₀_source := ⟨σ.x₀_source, trivial⟩
  slice := fun p hp => σ.slice p hp.1

/-- A slice submanifold modelled on `Z` is one modelled on `ℝᵐ`. -/
theorem isSliceRn (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn (finrank ℝ Z)) W N :=
  fun p hp => ⟨chartRn (hN p hp).choose, ⟨(hN p hp).choose_spec, trivial⟩⟩

/-- ... with the same tangent spaces. -/
theorem tangentSubspace_rn (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (q : N) :
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

/-- An open part has the same tangent spaces. -/
theorem tangentSubspace_inter (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {O : Set V}
    (hO : IsOpen O) (x : V) (hx : x ∈ N ∩ O) :
    Morse.tangentSubspace (Morse.IsSliceSubmanifold.inter_isOpen hN hO) ⟨x, hx⟩ =
      Morse.tangentSubspace hN ⟨x, hx.1⟩ := by
  obtain ⟨σ, hσ⟩ := hN x hx.1
  rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam _ (Morse.SliceChart.inter σ hO hx hσ)
    ⟨hσ, hx.2⟩, Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ]
  rfl

end Model

section Mono

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z₁ : Type} [NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁] {W₁ : Type} [NormedAddCommGroup W₁]
  [NormedSpace ℝ W₁] {Z₂ : Type} [NormedAddCommGroup Z₂] [NormedSpace ℝ Z₂] {W₂ : Type}
  [NormedAddCommGroup W₂] [NormedSpace ℝ W₂] {N₁ N₂ : Set V}
  {hN₁ : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z₁ W₁ N₁}
  {hN₂ : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z₂ W₂ N₂}

/-- Geodesics of `N₁ ⊆ N₂` with the same tangent spaces are geodesics of `N₂`. -/
theorem isGeodesicOn_mono (hsub : N₁ ⊆ N₂)
    (hT : ∀ x (h₁ : x ∈ N₁), Morse.tangentSubspace hN₁ ⟨x, h₁⟩ =
      Morse.tangentSubspace hN₂ ⟨x, hsub h₁⟩)
    {γ : ℝ → V} {s : Set ℝ} (h : Morse.IsGeodesicOn hN₁ γ s) : Morse.IsGeodesicOn hN₂ γ s :=
  ⟨h.isOpen, fun t ht => hsub (h.mem t ht), h.contDiffOn, fun t ht => by
    have := h.normal t ht
    rwa [hT] at this⟩

theorem mem_expDom_mono (hsub : N₁ ⊆ N₂)
    (hT : ∀ x (h₁ : x ∈ N₁), Morse.tangentSubspace hN₁ ⟨x, h₁⟩ =
      Morse.tangentSubspace hN₂ ⟨x, hsub h₁⟩)
    {q v : V} (h : (q, v) ∈ Morse.expDom hN₁) : (q, v) ∈ Morse.expDom hN₂ := by
  obtain ⟨γ, δ, hδ, hγ, h0, h0'⟩ := h
  exact ⟨γ, δ, hδ, isGeodesicOn_mono hsub hT hγ, h0, h0'⟩


/-- Conversely, a geodesic of `N₂` with values in `N₁` (same tangent spaces) is one of `N₁`. -/
theorem isGeodesicOn_of_mem (hsub : N₁ ⊆ N₂)
    (hT : ∀ x (h₁ : x ∈ N₁), Morse.tangentSubspace hN₁ ⟨x, h₁⟩ =
      Morse.tangentSubspace hN₂ ⟨x, hsub h₁⟩)
    {γ : ℝ → V} {s : Set ℝ} (h : Morse.IsGeodesicOn hN₂ γ s) (hmem : ∀ t ∈ s, γ t ∈ N₁) :
    Morse.IsGeodesicOn hN₁ γ s :=
  ⟨h.isOpen, hmem, h.contDiffOn, fun t ht => by
    rw [hT]
    exact h.normal t ht⟩

end Mono

section Component

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {m : ℕ} {N : Set V}

/-- The connected component of `x₀` in a slice submanifold is an open part `N ∩ O`, connected,
containing every preconnected subset of `N` that meets it. -/
theorem exists_component' (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn m) W N) (x₀ : N) :
    ∃ O : Set V, IsOpen O ∧ (x₀ : V) ∈ O ∧ IsConnected (N ∩ O) ∧
      ∀ P ⊆ N, IsPreconnected P → ∀ y ∈ P, y ∈ N ∩ O → P ⊆ N ∩ O := by
  let _ := hN.chartedSpace
  have := ChartedSpace.locallyConnectedSpace (Bridge.Rn m) N
  have hK : IsOpen (connectedComponent x₀) := isOpen_connectedComponent
  obtain ⟨O, hO, hOK⟩ := isOpen_induced_iff.1 hK
  have hNO : N ∩ O = connectedComponentIn N (x₀ : V) := by
    rw [connectedComponentIn_eq_image x₀.2]
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
  refine ⟨O, hO, ?_, ?_, ?_⟩
  · have : x₀ ∈ connectedComponent x₀ := mem_connectedComponent
    rw [← hOK] at this
    exact this
  · rw [hNO]
    exact isConnected_connectedComponentIn_iff.2 x₀.2
  · intro P hPN hP y hyP hy
    rw [hNO] at hy ⊢
    rw [connectedComponentIn_eq hy]
    exact hP.subset_connectedComponentIn hyP hPN

variable {C : Set V}

theorem riemDist_eq_of_closed' (hCN : C ⊆ N)
    (hpre : ∀ P ⊆ N, IsPreconnected P → ∀ y ∈ P, y ∈ C → P ⊆ C) {x : V} (hx : x ∈ C) (y : V) :
    Morse.riemDist (N := C) x y = Morse.riemDist (N := N) x y := by
  unfold Morse.riemDist Morse.pathLengths
  congr 1
  ext L
  constructor
  · rintro ⟨c, a, b, hc, hcC, ha, hb, rfl⟩
    exact ⟨c, a, b, hc, fun t ht => hCN (hcC t ht), ha, hb, rfl⟩
  · rintro ⟨c, a, b, hc, hcN, ha, hb, rfl⟩
    refine ⟨c, a, b, hc, fun t ht => ?_, ha, hb, rfl⟩
    have hsub := hpre (c '' Icc a b) (by rintro _ ⟨s, hs, rfl⟩; exact hcN s hs)
      (isPreconnected_Icc.image c hc.2.1) (c a) ⟨a, ⟨le_rfl, hc.1⟩, rfl⟩ (by rw [ha]; exact hx)
    exact hsub ⟨t, ht, rfl⟩

end Component

end RoundTrip.V7_25.Aux

namespace RoundTrip.V7_25

open RoundTrip.Bridge RoundTrip.V7_25.Aux Bundle

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V` with
the induced metric: (1) for normal coordinates `nc` of radius `ε` at `p` and `0 < δ < ε`, if
`δ < ρ(p, q) < ∞` there is `w ∈ T_pN`, `‖w‖ = δ`, with `ρ(p, q) = δ + ρ(exp_p w, q)`;
(2) a broken geodesic of minimal length is unbroken: `γ` a unit-speed geodesic on `ℝ`, `σ` a
unit-speed geodesic on a preconnected (open) `s ⊇ [t₀, t₁]`, `0 < t₀ < t₁`, `σ(t₀) = γ(t₀)` and
`ρ(γ(0), σ(t₁)) ≥ t₁` imply `σ(t₁) = γ(t₁)`. -/
def A : Prop :=
  type_of% @Morse.NormalCoord.exists_riemDist_eq_add.{0,0,0} ∧
    type_of% @Morse.broken_geodesic_eq.{0,0,0}

theorem A_holds : A := ⟨@Morse.NormalCoord.exists_riemDist_eq_add, @Morse.broken_geodesic_eq⟩

/-- **Partial `B → A`: part (2) of `B` gives the second conjunct of `A`**
(`Morse.broken_geodesic_eq`), by applying `B` to the connected component of `γ(0)` in `N` (an
open part, re-modelled on `ℝᵐ`) with the induced metric and Levi-Civita connection of
`RoundTrip.Bridge`, with `γ' = γ` and `T = t₁`. The broken path has length `t₁` (unit speed), which
is `ρ` by the hypothesis. The first conjunct (`Morse.NormalCoord.exists_riemDist_eq_add`, for
EVERY normal radius `ε` and every `δ < ε`) is stronger than part (1) of `B` (some `δ₀`). -/
theorem B_to_A_broken : B → type_of% @Morse.broken_geodesic_eq.{0,0,0} := by
  intro hB V _ _ _ Z _ _ _ W _ _ _ N hN γ σ hγ hγ1 s hσ hs t₀ t₁ ht₀ ht₀₁ hsub hσ1 hjoin hmin
  classical
  set m := finrank ℝ Z
  set hN' : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn m) W N := isSliceRn hN
  have hγ0N : γ 0 ∈ N := hγ.mem 0 trivial
  obtain ⟨O, hO, hqO, hconn, hpre⟩ := exists_component' hN' ⟨γ 0, hγ0N⟩
  set C := N ∩ O with hC_def
  set hC : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn m) W C :=
    Morse.IsSliceSubmanifold.inter_isOpen hN' hO
  have hγ0C : γ 0 ∈ C := ⟨hγ0N, hqO⟩
  have : ConnectedSpace (Sub hC) := isConnected_iff_connectedSpace.1 hconn
  have hTC : ∀ x (hx : x ∈ C), Morse.tangentSubspace hC ⟨x, hx⟩ =
      Morse.tangentSubspace hN ⟨x, inter_subset_left hx⟩ := fun x hx =>
    (tangentSubspace_inter hN' hO x hx).trans (tangentSubspace_rn hN ⟨x, hx.1⟩)
  -- `γ` and `σ` stay in the component
  have hγC : ∀ t, γ t ∈ C := by
    have h := hpre (range γ) (by rintro _ ⟨t, rfl⟩; exact hγ.mem t trivial)
      (isPreconnected_range (continuousOn_univ.1 hγ.contDiffOn.continuousOn)) (γ 0) ⟨0, rfl⟩
      hγ0C
    exact fun t => h ⟨t, rfl⟩
  have hσC : ∀ t ∈ s, σ t ∈ C := by
    have ht₀s : t₀ ∈ s := hsub ⟨le_rfl, ht₀₁.le⟩
    have h := hpre (σ '' s) (by rintro _ ⟨t, ht, rfl⟩; exact hσ.mem t ht)
      (hs.image σ hσ.contDiffOn.continuousOn) (σ t₀) ⟨t₀, ht₀s, rfl⟩ (by rw [hjoin]; exact hγC t₀)
    exact fun t ht => h ⟨t, ht, rfl⟩
  have hγg : Morse.IsGeodesicOn hC γ univ :=
    isGeodesicOn_of_mem inter_subset_left hTC hγ fun t _ => hγC t
  have hσg : Morse.IsGeodesicOn hC σ s := isGeodesicOn_of_mem inter_subset_left hTC hσ hσC
  set x₀ : Sub hC := (⟨γ 0, hγ0C⟩ : C)
  have ht₁ : 0 < t₁ := ht₀.trans ht₀₁
  obtain ⟨hΓ, hΓeq, -⟩ := isGeodesic_lift_Icc hγg ht₀ (subset_univ _) x₀
  obtain ⟨hΓ', hΓ'eq, -⟩ := isGeodesic_lift_Icc hγg ht₁ (subset_univ _) x₀
  obtain ⟨hS, hSeq, -⟩ := isGeodesic_lift_Icc hσg ht₀₁ hsub x₀
  set Γ := lift γ x₀
  set Sg := lift σ x₀
  -- unit speeds
  have hγspeed : ∀ t, ‖deriv γ t‖ = 1 := fun t =>
    (hγ.norm_deriv_eq isPreconnected_univ (mem_univ t) (mem_univ 0)).trans hγ1
  have hσspeed : ∀ t ∈ s, ‖deriv σ t‖ = 1 := fun t ht =>
    (hσ.norm_deriv_eq hs ht (hsub ⟨le_rfl, ht₀₁.le⟩)).trans hσ1
  have hspeed : ‖vel (n := m) Γ (Icc 0 t₀) t₀‖ = ‖vel (n := m) Sg (Icc t₀ t₁) t₀‖ := by
    have u1 : UniqueDiffOn ℝ (Icc 0 t₀) := uniqueDiffOn_Icc ht₀
    have u2 : UniqueDiffOn ℝ (Icc t₀ t₁) := uniqueDiffOn_Icc ht₀₁
    have e1 : ‖BridgePrelude.vel (n := m) Γ (Icc 0 t₀) t₀‖ = 1 := by
      rw [show ‖BridgePrelude.vel (n := m) Γ (Icc 0 t₀) t₀‖ = ‖D hC (Γ t₀) (BridgePrelude.vel (n := m) Γ (Icc 0 t₀) t₀)‖
        from norm_eq _ _, D_vel (isSmoothCurve_iff.2 (isGeodesic_iff.1 hΓ).2.1) u1
        ⟨ht₀.le, le_rfl⟩, derivWithin_congr hΓeq (hΓeq ⟨ht₀.le, le_rfl⟩),
        ((hγ.hasDerivAt (mem_univ t₀)).hasDerivWithinAt.derivWithin (u1 t₀ ⟨ht₀.le, le_rfl⟩))]
      exact hγspeed t₀
    have e2 : ‖BridgePrelude.vel (n := m) Sg (Icc t₀ t₁) t₀‖ = 1 := by
      rw [show ‖BridgePrelude.vel (n := m) Sg (Icc t₀ t₁) t₀‖ = ‖D hC (Sg t₀) (BridgePrelude.vel (n := m) Sg (Icc t₀ t₁) t₀)‖
        from norm_eq _ _, D_vel (isSmoothCurve_iff.2 (isGeodesic_iff.1 hS).2.1) u2
        ⟨le_rfl, ht₀₁.le⟩, derivWithin_congr hSeq (hSeq ⟨le_rfl, ht₀₁.le⟩),
        ((hσ.hasDerivAt (hsub ⟨le_rfl, ht₀₁.le⟩)).hasDerivWithinAt.derivWithin
          (u2 t₀ ⟨le_rfl, ht₀₁.le⟩))]
      exact hσ1
    exact e1.trans e2.symm
  -- the broken path, its length `t₁`, and `ρ = t₁`
  set c : ℝ → V := fun t => if t ≤ t₀ then γ t else σ t with hc_def
  have hγps : Morse.IsPiecewiseSmooth γ 0 t₀ :=
    Morse.IsPiecewiseSmooth.of_contDiffOn hγ.contDiffOn ht₀.le (subset_univ _)
  have hσps : Morse.IsPiecewiseSmooth σ t₀ t₁ :=
    Morse.IsPiecewiseSmooth.of_contDiffOn hσ.contDiffOn ht₀₁.le hsub
  have hcps : Morse.IsPiecewiseSmooth c 0 t₁ := hγps.concat hσps hjoin.symm
  have hcN : ∀ t ∈ Icc 0 t₁, c t ∈ N := fun t ht => by
    simp only [hc_def]
    split_ifs with h
    · exact hγ.mem t (mem_univ _)
    · exact hσ.mem t (hsub ⟨(not_le.1 h).le, ht.2⟩)
  have hunit : ∀ t ∈ Ioo 0 t₁, DifferentiableAt ℝ c t → ‖deriv c t‖ = 1 := by
    intro t ht hdiff
    rcases lt_trichotomy t t₀ with hlt | heq | hgt
    · have hev : c =ᶠ[𝓝 t] γ := by
        filter_upwards [Iio_mem_nhds hlt] with x hx
        simp only [hc_def, if_pos (mem_Iio.1 hx).le]
      rw [hev.deriv_eq]
      exact hγspeed t
    · subst heq
      have h1 : HasDerivWithinAt c (deriv c t) (Iic t) t := hdiff.hasDerivAt.hasDerivWithinAt
      have h2 : HasDerivWithinAt c (deriv γ t) (Iic t) t :=
        ((hγ.hasDerivAt (mem_univ t)).hasDerivWithinAt).congr
          (fun x hx => by simp only [hc_def, if_pos (mem_Iic.1 hx)])
          (by simp only [hc_def, le_refl, if_true])
      rw [(uniqueDiffWithinAt_Iic t).eq_deriv _ h1 h2]
      exact hγspeed t
    · have hev : c =ᶠ[𝓝 t] σ := by
        filter_upwards [Ioi_mem_nhds hgt] with x hx
        simp only [hc_def, if_neg (not_le.2 (mem_Ioi.1 hx))]
      rw [hev.deriv_eq]
      exact hσspeed t (hsub ⟨hgt.le, ht.2.le⟩)
  have hlen : Morse.pathLength c 0 t₁ = t₁ := by
    rw [Morse.pathLength_eq_of_norm_deriv hcps.isAdmissible hunit]
    ring
  have hc0 : c 0 = γ 0 := by simp only [hc_def, if_pos ht₀.le]
  have hct₁ : c t₁ = σ t₁ := by simp only [hc_def, if_neg (not_le.2 ht₀₁)]
  have hdist : Morse.riemDist (N := N) (γ 0) (σ t₁) = ENNReal.ofReal t₁ := by
    refine le_antisymm ?_ hmin
    have := Morse.riemDist_le_pathLength (N := N) hcps hcN
    rwa [hc0, hct₁, hlen] at this
  set br : ℝ → Sub hC := fun t => if t ≤ t₀ then Γ t else Sg t with hbr
  have hbreq : EqOn (incl hC ∘ br) c (Icc 0 t₁) := fun t ht => by
    simp only [hbr, hc_def, comp_apply]
    split_ifs with h
    · exact hΓ'eq ht
    · exact hSeq ⟨(not_le.1 h).le, ht.2⟩
  have harc : arcLen (n := m) br 0 t₁ = rho (n := m) (Γ 0) (Sg t₁) := by
    rw [show arcLen (n := m) br 0 t₁ = BridgePrelude.arcLen (n := m) br 0 t₁ from rfl, arcLen_eq,
      pathLength_congr ht₁.le hbreq, hlen,
      show rho (n := m) (Γ 0) (Sg t₁) = BridgePrelude.rho (n := m) (Γ 0) (Sg t₁) from rfl,
      rho_eq]
    have e0 : incl hC (Γ 0) = γ 0 := hΓeq ⟨le_rfl, ht₀.le⟩
    have e1 : incl hC (Sg t₁) = σ t₁ := hSeq ⟨ht₀₁.le, le_rfl⟩
    rw [e0, e1, riemDist_eq_of_closed' inter_subset_left hpre hγ0C, hdist,
      ENNReal.toReal_ofReal ht₁.le]
  have hjoin' : Γ t₀ = Sg t₀ := by
    apply Subtype.ext
    change incl hC (Γ t₀) = incl hC (Sg t₀)
    exact (hΓeq ⟨ht₀.le, le_rfl⟩).trans (hjoin.symm.trans (hSeq ⟨le_rfl, ht₀₁.le⟩).symm)
  have key := ((hB m (Sub hC) (conn (hN := hC)) conn_isLC).2 Γ Sg Γ t₀ t₁ t₁ ht₀ ht₀₁ le_rfl
    hΓ hS hjoin' hspeed hΓ' (fun _ _ => rfl) harc).2 ⟨ht₁.le, le_rfl⟩
  have h1 : incl hC (br t₁) = σ t₁ := by
    simp only [hbr, if_neg (not_le.2 ht₀₁)]
    exact hSeq ⟨ht₀₁.le, le_rfl⟩
  rw [← h1, show br t₁ = Γ t₁ from key]
  exact hΓ'eq ⟨ht₁.le, le_rfl⟩

#rt_check RoundTrip.V7_25.B_to_A_broken [Morse.NormalCoord.exists_riemDist_eq_add, Morse.broken_geodesic_eq]
#rt_overlap RoundTrip.V7_25.B_to_A_broken [Morse.NormalCoord.exists_riemDist_eq_add, Morse.broken_geodesic_eq]

/-! No full direction is proved; see `V7_25.json`. -/

end RoundTrip.V7_25
