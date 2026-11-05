import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_6
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold

namespace RoundTrip.V7_6

/-- The project's statement (universes instantiated at 0) for a slice submanifold `N ⊆ V` of a finite-dimensional inner product space, with the induced
connection: a local spray `LocalSpray σ u₀` exists in every slice chart; its curves `L.geo u w` are
geodesics on `(-2, 2)` (`IsGeodesicOn`: OPEN time set, ambient acceleration normal to `N`) depending
smoothly on `(u, w, t)`; and Lemma 10.2: around `q₀ ∈ N` there are an open `U`, `ε > 0` and
`Γ` smooth on `U × ball 0 ε × (-2, 2)` with `t ↦ Γ(p, v, t)` the unique geodesic on `(-2, 2)` with
`γ(0) = p`, `γ'(0) = v` (for `p ∈ U ∩ N`, `v ∈ T_pN`, `‖v‖ < ε`). -/
def A : Prop :=
  type_of% @Morse.nonempty_localSpray.{0,0,0} ∧
    type_of% @Morse.LocalSpray.isGeodesicOn_geo.{0,0,0} ∧
    type_of% @Morse.LocalSpray.contDiffOn_geo.{0,0,0} ∧
    type_of% @Morse.lemma_10_2.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.nonempty_localSpray,
    @Morse.LocalSpray.isGeodesicOn_geo,
    @Morse.LocalSpray.contDiffOn_geo,
    @Morse.lemma_10_2⟩

/-! No direction is proved; see `V7_6.json`.

## The embedded special case

`B_emb` is B for `M = ↥N` (`RoundTrip.Bridge.Sub hN`, model `ℝⁿ`, connected) with the induced
metric and the induced Levi-Civita connection `Bridge.conn`. Through the Bridge's dictionary
(blind geodesics on the open `(-2, 2)` = the project's `IsGeodesicOn`; Riemannian norm of `T_pN` =
ambient norm), `B_emb` follows from A's `lemma_10_2` (`A_to_B_emb`). Conversely B gives A's
Lemma 10.2 without the smooth dependence on `(p, v, t)` (`A_core`), for every slice submanifold
(any model `Z`, `N` not assumed connected): B is applied to the connected component of `q₀`, an open
part `N ∩ O` re-modelled on `ℝᵐ` (`B_emb_to_A_core`). -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

/-! ### Changing the model space, open parts, connected components (from `Items/V7_28.lean`) -/

section Comp

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A linear equivalence `Z ≃ ℝᵐ`, `m = dim Z`. -/
noncomputable def eZ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] :
    Z ≃L[ℝ] Bridge.Rn (finrank ℝ Z) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}

/-- A slice chart modelled on `Z`, read in `ℝᵐ`. -/
noncomputable def chartRn (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) :
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

/-- The connected component of `q` in a slice submanifold modelled on `ℝᵐ` is an open part
`N ∩ O`; it contains every preconnected subset of `N` meeting it. -/
theorem exists_component {m : ℕ} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn m) W N)
    (q : N) :
    ∃ O : Set V, IsOpen O ∧ (q : V) ∈ O ∧ IsConnected (N ∩ O) ∧
      ∀ S ⊆ N, IsPreconnected S → ∀ x ∈ S, x ∈ N ∩ O → S ⊆ N ∩ O := by
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
  refine ⟨O, hO, ?_, ?_, ?_⟩
  · have : q ∈ connectedComponent q := mem_connectedComponent
    rw [← hOK] at this
    exact this
  · rw [hNO]
    exact isConnected_connectedComponentIn_iff.2 q.2
  · intro S hSN hS x hxS hx
    rw [hNO] at hx ⊢
    rw [connectedComponentIn_eq hx]
    exact hS.subset_connectedComponentIn hxS hSN

/-- **Reduction to a connected slice submanifold modelled on `ℝᵐ`**: the component of `q`. -/
theorem reduce (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (q : N) :
    ∃ O : Set V, IsOpen O ∧ (q : V) ∈ O ∧
      ∃ hC : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn (finrank ℝ Z)) W (N ∩ O),
      ConnectedSpace (Bridge.Sub hC) ∧
      (∀ x (hx : x ∈ N ∩ O), Morse.tangentSubspace hC ⟨x, hx⟩ =
        Morse.tangentSubspace hN ⟨x, hx.1⟩) ∧
      ∀ S ⊆ N, IsPreconnected S → ∀ x ∈ S, x ∈ N ∩ O → S ⊆ N ∩ O := by
  obtain ⟨O, hO, hqO, hconn, hS⟩ := exists_component (isSliceRn hN) q
  refine ⟨O, hO, hqO, Morse.IsSliceSubmanifold.inter_isOpen (isSliceRn hN) hO,
    isConnected_iff_connectedSpace.1 hconn, fun x hx => ?_, hS⟩
  exact (tangentSubspace_inter (isSliceRn hN) hO x hx).trans (tangentSubspace_rn hN ⟨x, hx.1⟩)

end Comp

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

/-- ... and conversely, geodesics of `N₂` with values in `N₁` are geodesics of `N₁`. -/
theorem isGeodesicOn_restrict (hsub : N₁ ⊆ N₂)
    (hT : ∀ x (h₁ : x ∈ N₁), Morse.tangentSubspace hN₁ ⟨x, h₁⟩ =
      Morse.tangentSubspace hN₂ ⟨x, hsub h₁⟩)
    {γ : ℝ → V} {s : Set ℝ} (hmem : ∀ t ∈ s, γ t ∈ N₁) (h : Morse.IsGeodesicOn hN₂ γ s) :
    Morse.IsGeodesicOn hN₁ γ s :=
  ⟨h.isOpen, hmem, h.contDiffOn, fun t ht => by
    rw [hT (γ t) (hmem t ht)]
    exact h.normal t ht⟩

end Mono

/-! ### The dictionary on `(-2, 2)` -/

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

/-- A blind geodesic of the induced connection on an open interval `s`, read in `V`: a project
geodesic, with `deriv` its blind velocity. -/
theorem geod_open {γ : ℝ → Sub hN} {s : Set ℝ} (hso : IsOpen s) (hsc : s.OrdConnected)
    (h : IsGeodesic (conn (hN := hN)) γ s) {t : ℝ} (ht : t ∈ s) :
    Morse.IsGeodesicOn hN (incl hN ∘ γ) s ∧
      D hN (γ t) (vel (n := n) γ s t) = deriv (incl hN ∘ γ) t := by
  have h' : BridgePrelude.IsGeodesic (conn (hN := hN)) γ s := h
  have hg := (isGeodesic_iff_isGeodesicOn hso hsc).1 h'
  refine ⟨hg, ?_⟩
  have hc := (isGeodesic_iff.1 h').2.1
  rw [show D hN (γ t) (vel (n := n) γ s t) = D hN (γ t) (BridgePrelude.vel (n := n) γ s t) from rfl,
    D_vel (isSmoothCurve_iff.2 hc) hso.uniqueDiffOn ht, derivWithin_of_isOpen hso ht]

/-- A project geodesic on an open interval `s`, lifted to `N`: a blind geodesic. -/
theorem lift_geod {γ : ℝ → V} {s : Set ℝ} (hso : IsOpen s) (hsc : s.OrdConnected)
    (h : Morse.IsGeodesicOn hN γ s) (x : Sub hN) :
    IsGeodesic (conn (hN := hN)) (lift γ x) s ∧ EqOn (incl hN ∘ lift γ x) γ s := by
  have heq : EqOn (incl hN ∘ lift γ x) γ s := fun t ht => incl_lift x (h.mem t ht)
  exact ⟨(isGeodesic_iff_isGeodesicOn hso hsc).2 (h.congr heq.symm), heq⟩

/-- `InitData` on an open interval, read in `V`. -/
theorem initData_open {γ : ℝ → Sub hN} {s : Set ℝ} (hso : IsOpen s) (hsc : s.OrdConnected)
    (h : IsGeodesic (conn (hN := hN)) γ s) (h0s : (0 : ℝ) ∈ s) {p : Sub hN}
    {w : TangentSpace 𝓘(ℝ, Bridge.Rn n) p} :
    InitData (n := n) γ s p w ↔ γ 0 = p ∧ deriv (incl hN ∘ γ) 0 = D hN p w := by
  constructor
  · intro hi
    have hi' : BridgePrelude.InitData (n := n) γ s p w := hi
    have h0 : γ 0 = p := hi.1
    refine ⟨h0, ?_⟩
    rw [← (geod_open hso hsc h h0s).2]
    exact (initData_iff h0).1 hi'
  · rintro ⟨h0, hd⟩
    have : BridgePrelude.InitData (n := n) γ s p w := by
      refine (initData_iff h0).2 ?_
      rw [← hd]
      exact (geod_open hso hsc h h0s).2
    exact this

end Emb

open Bundle in
/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], ∀ p₀ : Bridge.Sub hN, ∃ U ∈ nhds p₀, ∃ ε > 0,
    ∀ p ∈ U, ∀ v : TangentSpace 𝓘(ℝ, Rn n) p, ‖v‖ < ε →
      ∃ γ : ℝ → Bridge.Sub hN, IsGeodesic Bridge.conn γ (Set.Ioo (-2) 2) ∧
        InitData γ (Set.Ioo (-2) 2) p v ∧
        ∀ γ' : ℝ → Bridge.Sub hN, IsGeodesic Bridge.conn γ' (Set.Ioo (-2) 2) →
          InitData γ' (Set.Ioo (-2) 2) p v → Set.EqOn γ γ' (Set.Ioo (-2) 2)

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- A's Lemma 10.2 without the smooth dependence on the initial data: around `q₀ ∈ N`, geodesics
on `(-2, 2)` exist and are unique for initial data `(p, v)`, `p ∈ U ∩ N`, `v ∈ T_pN`, `‖v‖ < ε`. -/
def A_core : Prop :=
  ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (q₀ : N),
    ∃ U : Set V, IsOpen U ∧ (q₀ : V) ∈ U ∧ ∃ ε > 0,
      ∀ p : N, (p : V) ∈ U → ∀ v ∈ Morse.tangentSubspace hN p, ‖v‖ < ε →
        ∃ γ : ℝ → V, Morse.IsGeodesicOn hN γ (Ioo (-2) 2) ∧ γ 0 = p ∧ HasDerivAt γ v 0 ∧
          ∀ γ' : ℝ → V, Morse.IsGeodesicOn hN γ' (Ioo (-2) 2) → γ' 0 = p → deriv γ' 0 = v →
            EqOn γ' γ (Ioo (-2) 2)

theorem A_to_A_core : A → A_core := by
  intro hA V _ _ _ Z _ _ _ W _ _ _ N hN q₀
  obtain ⟨U, hU, hq₀, ε, hε, Γ, -, hΓ⟩ := hA.2.2.2 hN q₀
  refine ⟨U, hU, hq₀, ε, hε, fun p hp v hv hvε => ?_⟩
  obtain ⟨hg, h0, hd, huniq⟩ := hΓ p hp v hv hvε
  exact ⟨_, hg, h0, hd, huniq⟩

open Bundle in
/-- **`A_core` gives B on embedded manifolds** (through the dictionary on `(-2, 2)`). -/
theorem A_core_to_B_emb : A_core → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ p₀
  obtain ⟨U, hU, hp₀U, ε, hε, hΓ⟩ := hA hN p₀
  have hI : IsOpen (Ioo (-2 : ℝ) 2) := isOpen_Ioo
  have hIc : (Ioo (-2 : ℝ) 2).OrdConnected := ordConnected_Ioo
  have h0 : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  refine ⟨Bridge.incl hN ⁻¹' U,
    (hU.preimage Bridge.contMDiff_incl.continuous).mem_nhds hp₀U, ε, hε, fun p hp v hv => ?_⟩
  set w := Bridge.D hN p v
  have hw : w ∈ Morse.tangentSubspace hN p := Bridge.D_mem p v
  have hwε : ‖w‖ < ε := by rw [← Bridge.norm_eq]; exact hv
  obtain ⟨γ₀, hg, hΓ0, hd, huniq⟩ := hΓ p hp w hw hwε
  obtain ⟨hγ, heq⟩ := Emb.lift_geod hI hIc (γ := γ₀) hg p
  have hγ0 : Bridge.lift γ₀ p 0 = p := by
    apply Subtype.ext
    exact (heq h0).trans hΓ0
  have hev : Bridge.incl hN ∘ Bridge.lift γ₀ p =ᶠ[𝓝 0] γ₀ :=
    eventually_of_mem (hI.mem_nhds h0) heq
  refine ⟨_, hγ, (Emb.initData_open hI hIc hγ h0).2 ⟨hγ0, ?_⟩, fun γ' hγ' hi' => ?_⟩
  · rw [hev.deriv_eq]
    exact hd.deriv
  · obtain ⟨hγ'0, hd'⟩ := (Emb.initData_open hI hIc hγ' h0).1 hi'
    have hg' := (Emb.geod_open hI hIc hγ' h0).1
    have := huniq _ hg' (by show Bridge.incl hN (γ' 0) = _; rw [hγ'0]; rfl) hd'
    intro t ht
    apply Subtype.ext
    exact (heq ht).trans (this ht).symm

/-- **A implies B on embedded manifolds** (uses A's `lemma_10_2`). -/
theorem A_to_B_emb : A → B_emb := fun hA => A_core_to_B_emb (A_to_A_core hA)

open Bundle in
/-- **B on embedded manifolds gives A's Lemma 10.2 without smooth dependence** (`A_core`), for every
slice submanifold: B is applied to the connected component of `q₀`. -/
theorem B_emb_to_A_core : B_emb → A_core := by
  intro hB V _ _ _ Z _ _ _ W _ _ _ N hN q₀
  obtain ⟨O, hO, hqO, hC, hconn, hT, hS⟩ := Emb.reduce hN q₀
  have hsub : N ∩ O ⊆ N := inter_subset_left
  have hI : IsOpen (Ioo (-2 : ℝ) 2) := isOpen_Ioo
  have hIc : (Ioo (-2 : ℝ) 2).OrdConnected := ordConnected_Ioo
  have h0 : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  set q₀' : Bridge.Sub hC := (⟨q₀, q₀.2, hqO⟩ : ↥(N ∩ O))
  obtain ⟨U, hU, ε, hε, H⟩ := hB V W (finrank ℝ Z) (N ∩ O) hC q₀'
  obtain ⟨u, hu, hus⟩ := (mem_nhds_subtype (N ∩ O) q₀' U).1 hU
  obtain ⟨U₁, hU₁u, hU₁, hq₀U₁⟩ := mem_nhds_iff.1 hu
  refine ⟨U₁ ∩ O, hU₁.inter hO, ⟨hq₀U₁, hqO⟩, ε, hε, fun p hp v hv hvε => ?_⟩
  have hpC : (p : V) ∈ N ∩ O := ⟨p.2, hp.2⟩
  let p' : Bridge.Sub hC := (⟨(p : V), hpC⟩ : ↥(N ∩ O))
  have hp'U : p' ∈ U := hus (hU₁u hp.1)
  have hvC : v ∈ Morse.tangentSubspace hC p' := by
    show v ∈ Morse.tangentSubspace hC ⟨(p : V), hpC⟩
    rw [hT (p : V) hpC]
    exact hv
  let w : TangentSpace 𝓘(ℝ, Bridge.Rn (finrank ℝ Z)) p' := Bridge.L hC p' v
  have hDw : Bridge.D hC p' w = v := Bridge.D_L hvC
  have hwε : ‖w‖ < ε := by rw [Bridge.norm_eq, hDw]; exact hvε
  obtain ⟨γ, hγ, hi, huniq⟩ := H p' hp'U w hwε
  obtain ⟨hγ0, hγd⟩ := (Emb.initData_open hI hIc hγ h0).1 hi
  have hg := (Emb.geod_open hI hIc hγ h0).1
  refine ⟨Bridge.incl hC ∘ γ, Emb.isGeodesicOn_mono hsub (fun x hx => hT x hx) hg, ?_, ?_, ?_⟩
  · show Bridge.incl hC (γ 0) = p
    rw [hγ0]
    rfl
  · have := hg.hasDerivAt h0
    rw [hγd, hDw] at this
    exact this
  · intro γ' hγ' hγ'0 hγ'd
    have hmem : ∀ t ∈ Ioo (-2 : ℝ) 2, γ' t ∈ N ∩ O := by
      have hsubS := hS (γ' '' Ioo (-2) 2) (by rintro _ ⟨t, ht, rfl⟩; exact hγ'.mem t ht)
        (isPreconnected_Ioo.image γ' hγ'.contDiffOn.continuousOn) (γ' 0) ⟨0, h0, rfl⟩
        (by rw [hγ'0]; exact hpC)
      exact fun t ht => hsubS ⟨t, ht, rfl⟩
    have hγ'C := Emb.isGeodesicOn_restrict hsub (fun x hx => hT x hx) hmem hγ'
    obtain ⟨hl, hleq⟩ := Emb.lift_geod hI hIc hγ'C p'
    have hl0 : Bridge.lift γ' p' 0 = p' := by
      apply Subtype.ext
      exact (hleq h0).trans hγ'0
    have hev : Bridge.incl hC ∘ Bridge.lift γ' p' =ᶠ[𝓝 0] γ' :=
      eventually_of_mem (hI.mem_nhds h0) hleq
    have hli : InitData (Bridge.lift γ' p') (Ioo (-2) 2) p' w :=
      (Emb.initData_open hI hIc hl h0).2 ⟨hl0, by rw [hev.deriv_eq, hγ'd, hDw]⟩
    have := huniq _ hl hli
    intro t ht
    rw [← hleq ht]
    exact congrArg (Bridge.incl hC) (this ht).symm

/-- **B implies A's Lemma 10.2 without smooth dependence**, by specializing B to the component of
`q₀` in `↥N`. -/
theorem B_to_A_core : B → A_core := fun hB => B_emb_to_A_core (B_to_B_emb hB)

/-- On embedded manifolds, B is exactly A's Lemma 10.2 without the smooth dependence. -/
theorem B_emb_iff_A_core : B_emb ↔ A_core := ⟨B_emb_to_A_core, A_core_to_B_emb⟩

#rt_check RoundTrip.V7_6.A_to_B_emb [Morse.nonempty_localSpray, Morse.LocalSpray.isGeodesicOn_geo,
  Morse.LocalSpray.contDiffOn_geo, Morse.lemma_10_2]
#rt_check RoundTrip.V7_6.B_to_A_core [Morse.nonempty_localSpray, Morse.LocalSpray.isGeodesicOn_geo,
  Morse.LocalSpray.contDiffOn_geo, Morse.lemma_10_2]
#rt_overlap RoundTrip.V7_6.B_to_A_core [Morse.nonempty_localSpray,
  Morse.LocalSpray.isGeodesicOn_geo, Morse.LocalSpray.contDiffOn_geo, Morse.lemma_10_2]

end RoundTrip.V7_6
