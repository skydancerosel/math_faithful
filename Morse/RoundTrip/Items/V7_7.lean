import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_7
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold

namespace RoundTrip.V7_7

/-- The project's statement (universes instantiated at 0) (`IsGeodesicFrom`, `expDom`, `exp` are definitions; `exp hN q v = γ(1)` for a chosen geodesic
`γ` on some `(-δ, 1 + δ)` with `γ 0 = q`, `deriv γ 0 = v`, junk `q`): `exp` equals `γ 1` for every
such `γ`; `exp_q 0 = q`; `exp_q(t v) = γ(t)` for `t ∈ (-δ, 1+δ)`; a geodesic on `(0, 1)` that is a
smooth curve in `N` is `t ↦ exp_{γ0}(t γ'(0))` on `[0, 1]`; and `(y, w) ∈ expDom` as soon as the ray
`t ↦ exp_y(t w)` is a geodesic on `(-η, 1+η)`. -/
def A : Prop :=
  type_of% @Morse.IsGeodesicFrom.exp_eq.{0,0,0} ∧
    type_of% @Morse.exp_zero.{0,0,0} ∧
    type_of% @Morse.IsGeodesicFrom.exp_smul.{0,0,0} ∧
    type_of% @Morse.exists_initial_ray.{0,0,0} ∧
    type_of% @Morse.mem_expDom_of_isGeodesicOn.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.IsGeodesicFrom.exp_eq,
    @Morse.exp_zero,
    @Morse.IsGeodesicFrom.exp_smul,
    @Morse.exists_initial_ray,
    @Morse.mem_expDom_of_isGeodesicOn⟩

/-! `B → A` is proved (`B_to_A`, through the embedded special case below); `A → B` is not (B is
about abstract Riemannian manifolds). See `V7_7.json`.

## The embedded special case

`B_emb` is B for `M = ↥N` (`RoundTrip.Bridge.Sub hN`, model `ℝⁿ`, connected) with the induced
metric and the induced Levi-Civita connection `Bridge.conn`.
* `A_to_B_emb`: A gives B_emb — (i) and (ii) from A's `exists_initial_ray` (a blind geodesic on the
  closed `[0, 1]` is the ray `t ↦ exp_q(t v)`, a geodesic on an open interval), `exp_smul` (the rays
  are in the domain of the project's `exp`) and `exp_eq` (the blind `exp` is the project's `exp`
  there, `Emb.expMap_eq'`); (iii) (`exp_q` defined for small `v`) is not in A and is proved
  outright from the project's `Morse.lemma_10_2` (item V7_6).
* `B_emb_to_A_exp`: B's uniqueness (ii) on the closed `[0, 1]`, applied to the connected component
  of `q` (re-modelled on `ℝᵐ`), gives A's `exp_eq`, hence `exp_zero` and `exp_smul`, for every
  slice submanifold.
* `B_emb_to_A`: the rest of A follows with project lemmas outside the item: a geodesic smooth on
  `[0, 1]` extends past its ends (`Emb.extend_closed'`, the uniform local existence of
  `Morse.lemma_10_2` rescaled) and is then the ray by `exp_smul` (`exists_initial_ray`); the ray of
  `w` has velocity `w` at `0` because near `0` it is a geodesic of Lemma 10.2, by `exp_eq`
  (`mem_expDom_of_isGeodesicOn`).
So `B_emb ↔ A`, and `B → A`. -/

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


/-! ### The blind `exp` and the project's `exp` -/

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

/-- `Bridge.expMap_eq`, with the well-definedness of the project's `exp` (`exp_eq`) as a
hypothesis. -/
theorem expMap_eq'
    (hexp : ∀ {γ : ℝ → V} {q v : V}, Morse.IsGeodesicFrom hN γ q v → Morse.exp hN q v = γ 1)
    {q : Sub hN} {w : TangentSpace 𝓘(ℝ, Bridge.Rn n) q}
    (h : (incl hN q, D hN q w) ∈ Morse.expDom hN) :
    incl hN (expMap (conn (hN := hN)) q w) = Morse.exp hN (incl hN q) (D hN q w) := by
  obtain ⟨γ, hγ⟩ := h
  obtain ⟨h1, h2, h3⟩ := isGeodesic_lift_of_isGeodesicFrom (w := w) hγ
  have hex : BridgePrelude.ExpDefined (conn (hN := hN)) q w := ⟨_, h1, h2⟩
  rw [hexp hγ, show expMap (conn (hN := hN)) q w = BridgePrelude.expMap (conn (hN := hN)) q w
    from rfl, BridgePrelude.expMap, dif_pos hex]
  obtain ⟨hc1, hc2⟩ := hex.choose_spec
  have uI : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have e0 : hex.choose 0 = lift γ q 0 := hc2.1.trans h2.1.symm
  have e0' : derivWithin (incl hN ∘ hex.choose) (Icc 0 1) 0 =
      derivWithin (incl hN ∘ lift γ q) (Icc 0 1) 0 := by
    rw [← D_vel (isSmoothCurve_iff.2 (isGeodesic_iff.1 hc1).2.1) uI h0I,
      ← D_vel (isSmoothCurve_iff.2 (isGeodesic_iff.1 h1).2.1) uI h0I,
      (initData_iff hc2.1).1 hc2, (initData_iff h2.1).1 h2]
  have := eqOn_Icc_of_isGeodesic zero_lt_one hc1 h1 e0 e0' ⟨zero_le_one, le_rfl⟩
  rw [this]
  exact h3 1 ⟨zero_le_one, le_rfl⟩

/-- A blind geodesic on `[0, 1]` from `q` with initial velocity `v` is, read in `V`, the ray
`t ↦ exp_q(t D v)` on `[0, 1]`, and the rays are in the project's `expDom` (from A's
`exists_initial_ray` and `exp_smul`). -/
theorem ray_of_isGeodesic
    (hray : type_of% @Morse.exists_initial_ray.{0,0,0})
    (hsmul : type_of% @Morse.IsGeodesicFrom.exp_smul.{0,0,0})
    {q : Sub hN} {v : TangentSpace 𝓘(ℝ, Bridge.Rn n) q} {γ : ℝ → Sub hN}
    (hγ : IsGeodesic (conn (hN := hN)) γ (Icc 0 1)) (hi : InitData (n := n) γ (Icc 0 1) q v) :
    ∀ t ∈ Icc (0 : ℝ) 1, incl hN (γ t) = Morse.exp hN (incl hN q) (t • D hN q v) ∧
      (incl hN q, t • D hN q v) ∈ Morse.expDom hN := by
  have hγ' : BridgePrelude.IsGeodesic (conn (hN := hN)) γ (Icc 0 1) := hγ
  obtain ⟨-, hcd, -⟩ := isGeodesic_iff.1 hγ'
  have hc : Morse.IsSmoothCurveIn hN (incl hN ∘ γ) := ⟨hcd, fun t _ => (γ t).2⟩
  obtain ⟨η, hη, hr, heq⟩ := hray hc (isGeodesicOn_Ioo hγ')
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h0J : (0 : ℝ) ∈ Ioo (-η) (1 + η) := ⟨by linarith, by linarith⟩
  have hγ0 : γ 0 = q := hi.1
  have hi' : BridgePrelude.InitData (n := n) γ (Icc 0 1) q v := hi
  have hD := (initData_iff hγ0).1 hi'
  have hvel : Morse.velAlong (incl hN ∘ γ) 0 = D hN q v := by
    rw [← hD, D_vel (isSmoothCurve_iff.2 hcd) (uniqueDiffOn_Icc zero_lt_one) h0I]
    rfl
  have hq : (incl hN ∘ γ) 0 = incl hN q := by
    show incl hN (γ 0) = incl hN q
    rw [hγ0]
  rw [hvel, hq] at hr heq
  set g : ℝ → V := fun t => Morse.exp hN (incl hN q) (t • D hN q v) with hg
  have hderiv : deriv g 0 = D hN q v := by
    have h1 : HasDerivWithinAt (incl hN ∘ γ) (deriv g 0) (Icc 0 1) 0 :=
      (hr.hasDerivAt h0J).hasDerivWithinAt.congr (fun t ht => (heq t ht).symm)
        (heq 0 h0I).symm
    rw [← hD, D_vel (isSmoothCurve_iff.2 hcd) (uniqueDiffOn_Icc zero_lt_one) h0I]
    exact (uniqueDiffOn_Icc zero_lt_one 0 h0I).eq_deriv _ h1
      (h1.differentiableWithinAt.hasDerivWithinAt)
  have hfrom : Morse.IsGeodesicFrom hN g (incl hN q) (D hN q v) :=
    ⟨η, hη, hr, (heq 0 h0I).trans hq, hderiv⟩
  obtain ⟨δ, hδ, -, hsm⟩ := hsmul hfrom
  intro t ht
  have htJ : t ∈ Ioo (-δ) (1 + δ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨hf, -⟩ := hsm t htJ
  exact ⟨(heq t ht).symm, hf.mem_expDom⟩

end Emb

open Bundle in
/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], ∀ q : Bridge.Sub hN,
    (∀ (v : TangentSpace 𝓘(ℝ, Rn n) q) (γ : ℝ → Bridge.Sub hN),
      IsGeodesic Bridge.conn γ (Set.Icc 0 1) → InitData γ (Set.Icc 0 1) q v →
      expMap Bridge.conn q v = γ 1 ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, expMap Bridge.conn q (t • v) = γ t) ∧
    (∀ (v : TangentSpace 𝓘(ℝ, Rn n) q) (γ γ' : ℝ → Bridge.Sub hN),
      IsGeodesic Bridge.conn γ (Set.Icc 0 1) → InitData γ (Set.Icc 0 1) q v →
      IsGeodesic Bridge.conn γ' (Set.Icc 0 1) → InitData γ' (Set.Icc 0 1) q v →
      Set.EqOn γ γ' (Set.Icc 0 1)) ∧
    ∃ ε > 0, ∀ v : TangentSpace 𝓘(ℝ, Rn n) q, ‖v‖ < ε → ExpDefined Bridge.conn q v

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

open Bundle in
/-- **A implies B on embedded manifolds**: (i), (ii) from A's `exists_initial_ray`, `exp_smul`,
`exp_eq`; (iii) outright from the project's Lemma 10.2 (`Morse.lemma_10_2`, not in A). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ q
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hi : ∀ (v : TangentSpace 𝓘(ℝ, Rn n) q) (γ : ℝ → Bridge.Sub hN),
      IsGeodesic Bridge.conn γ (Set.Icc 0 1) → InitData γ (Set.Icc 0 1) q v →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, expMap Bridge.conn q (t • v) = γ t := by
    intro v γ hγ hinit t ht
    obtain ⟨h1, h2⟩ := Emb.ray_of_isGeodesic hA.2.2.2.1 hA.2.2.1 hγ hinit t ht
    have hD : Bridge.D hN q (t • v) = t • Bridge.D hN q v := map_smul _ _ _
    apply Subtype.ext
    show Bridge.incl hN _ = Bridge.incl hN (γ t)
    rw [Emb.expMap_eq' hA.1 (by rw [hD]; exact h2), hD, h1]
  refine ⟨fun v γ hγ hinit => ⟨?_, hi v γ hγ hinit⟩, fun v γ γ' hγ hinit hγ' hinit' t ht => ?_, ?_⟩
  · have := hi v γ hγ hinit 1 h1I
    rwa [one_smul] at this
  · rw [← hi v γ hγ hinit t ht, ← hi v γ' hγ' hinit' t ht]
  · obtain ⟨U, -, hqU, ε, hε, Γ, -, hΓ⟩ := Morse.lemma_10_2 hN q
    refine ⟨ε, hε, fun v hv => ?_⟩
    have hw : Bridge.D hN q v ∈ Morse.tangentSubspace hN q := Bridge.D_mem q v
    have hwε : ‖Bridge.D hN q v‖ < ε := by rw [← Bridge.norm_eq]; exact hv
    obtain ⟨hg, h0, hd, -⟩ := hΓ q hqU _ hw hwε
    exact Bridge.expDefined_of_mem_expDom ⟨_, 1, one_pos,
      hg.mono isOpen_Ioo (Ioo_subset_Ioo (by norm_num) (by norm_num)), h0, hd.deriv⟩

/-- A's `exp_eq`, `exp_zero` and `exp_smul`: the well-definedness of the project's `exp` and its
consequences. -/
def A_exp : Prop :=
  type_of% @Morse.IsGeodesicFrom.exp_eq.{0,0,0} ∧
    type_of% @Morse.exp_zero.{0,0,0} ∧
    type_of% @Morse.IsGeodesicFrom.exp_smul.{0,0,0}

theorem A_to_A_exp : A → A_exp := fun hA => ⟨hA.1, hA.2.1, hA.2.2.1⟩

/-- **B's uniqueness (ii), read in `V`**: two project geodesics from `q` with initial velocity `v`
agree at time `1`, for every slice submanifold (via the component of `q`). -/
theorem B_emb_uniq (hB : B_emb) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}
    {γ₁ γ₂ : ℝ → V} {q v : V} (h₁ : Morse.IsGeodesicFrom hN γ₁ q v)
    (h₂ : Morse.IsGeodesicFrom hN γ₂ q v) : γ₁ 1 = γ₂ 1 := by
  have hq : q ∈ N := h₁.mem
  obtain ⟨O, hO, hqO, hC, hconn, hT, hS⟩ := Emb.reduce hN ⟨q, hq⟩
  have hsub : N ∩ O ⊆ N := inter_subset_left
  have hqC : q ∈ N ∩ O := ⟨hq, hqO⟩
  let q' : Bridge.Sub hC := (⟨q, hqC⟩ : ↥(N ∩ O))
  -- the geodesics stay in the component and are geodesics of it
  have toC : ∀ {γ : ℝ → V}, Morse.IsGeodesicFrom hN γ q v →
      Morse.IsGeodesicFrom hC γ (Bridge.incl hC q') v := by
    rintro γ ⟨δ, hδ, hγ, h0, hd⟩
    have h0J : (0 : ℝ) ∈ Ioo (-δ) (1 + δ) := ⟨by linarith, by linarith⟩
    have hmem : ∀ t ∈ Ioo (-δ) (1 + δ), γ t ∈ N ∩ O := by
      have hsubS := hS (γ '' Ioo (-δ) (1 + δ)) (by rintro _ ⟨t, ht, rfl⟩; exact hγ.mem t ht)
        (isPreconnected_Ioo.image γ hγ.contDiffOn.continuousOn) (γ 0) ⟨0, h0J, rfl⟩
        (by rw [h0]; exact hqC)
      exact fun t ht => hsubS ⟨t, ht, rfl⟩
    exact ⟨δ, hδ, Emb.isGeodesicOn_restrict hsub (fun x hx => hT x hx) hmem hγ, h0, hd⟩
  have hvC : v ∈ Morse.tangentSubspace hC q' := by
    obtain ⟨δ, hδ, hγ, h0, hd⟩ := h₁
    have h0J : (0 : ℝ) ∈ Ioo (-δ) (1 + δ) := ⟨by linarith, by linarith⟩
    have := (toC ⟨δ, hδ, hγ, h0, hd⟩)
    obtain ⟨δ', hδ', hγ', h0', hd'⟩ := this
    have h0J' : (0 : ℝ) ∈ Ioo (-δ') (1 + δ') := ⟨by linarith, by linarith⟩
    have hm := hγ'.deriv_mem h0J'
    rw [hd'] at hm
    rwa [Morse.tangentSubspace_congr hC _ hqC h0'] at hm
  set w : TangentSpace 𝓘(ℝ, Bridge.Rn (finrank ℝ Z)) q' := Bridge.L hC q' v
  have hDw : Bridge.D hC q' w = v := Bridge.D_L hvC
  have l₁ := Bridge.isGeodesic_lift_of_isGeodesicFrom (w := w) (by rw [hDw]; exact toC h₁)
  have l₂ := Bridge.isGeodesic_lift_of_isGeodesicFrom (w := w) (by rw [hDw]; exact toC h₂)
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have := (hB V W _ (N ∩ O) hC q').2.1 w _ _ l₁.1 l₁.2.1 l₂.1 l₂.2.1 h1I
  rw [← l₁.2.2 1 h1I, ← l₂.2.2 1 h1I, this]

/-- **B on embedded manifolds gives A's `exp_eq`, `exp_zero`, `exp_smul`** (all slice
submanifolds, any model). -/
theorem B_emb_to_A_exp : B_emb → A_exp := by
  intro hB
  have hexp : type_of% @Morse.IsGeodesicFrom.exp_eq.{0,0,0} := by
    intro V _ _ _ Z _ _ _ W _ _ _ N hN γ q v h
    have hex : ∃ γ, Morse.IsGeodesicFrom hN γ q v := ⟨γ, h⟩
    rw [Morse.exp, dif_pos hex]
    exact B_emb_uniq hB hex.choose_spec h
  refine ⟨hexp, ?_, ?_⟩
  · intro V _ _ _ Z _ _ _ W _ _ _ N hN q hq
    exact hexp (Morse.isGeodesicFrom_const hq)
  · -- the project's proof of `exp_smul`, with `exp_eq` from B
    intro V _ _ _ Z _ _ _ W _ _ _ N hN γ q v h
    obtain ⟨δ, hδ, hγ, h0, h0'⟩ := h
    refine ⟨δ, hδ, hγ, fun t ht => ?_⟩
    have hη := hγ.comp_mul_add t 0
    simp only [add_zero] at hη
    have hconv : Convex ℝ ((fun s => t * s) ⁻¹' Ioo (-δ) (1 + δ)) := by
      intro x hx y hy a b ha hb hab
      have := convex_Ioo (-δ) (1 + δ) hx hy ha hb hab
      simp only [mem_preimage, smul_eq_mul] at this ⊢
      convert this using 1
      ring
    have h00 : (0 : ℝ) ∈ (fun s => t * s) ⁻¹' Ioo (-δ) (1 + δ) := by
      simp only [mem_preimage, mul_zero]
      exact ⟨by linarith, by linarith⟩
    have h11 : (1 : ℝ) ∈ (fun s => t * s) ⁻¹' Ioo (-δ) (1 + δ) := by
      simpa only [mem_preimage, mul_one] using ht
    have hfrom := Morse.isGeodesicFrom_of_isGeodesicOn hη hconv.isPreconnected h00 h11
    have hd : deriv (fun s => γ (t * s)) 0 = t • v := by
      have h1 : HasDerivAt (fun s : ℝ => t * s) t 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_mul t
      have h2 := (hγ.hasDerivAt (t := t * 0) (by simp only [mul_zero]; exact
        ⟨by linarith, by linarith⟩)).scomp (0 : ℝ) h1
      rw [show (t * 0 : ℝ) = 0 by ring, h0'] at h2
      exact h2.deriv
    have h0q : γ (t * 0) = q := by simp only [mul_zero, h0]
    rw [hd, h0q] at hfrom
    refine ⟨hfrom, ?_⟩
    rw [hexp hfrom, mul_one]

/-- **B implies A's `exp_eq`, `exp_zero`, `exp_smul`**, by specializing B to the component of
`q` in `↥N`. -/
theorem B_to_A_exp : B → A_exp := fun hB => B_emb_to_A_exp (B_to_B_emb hB)

/-! ### B gives all of A: extension of geodesics past the ends (from `Items/V7_20.lean`, with the
uniform local existence taken from `Morse.lemma_10_2` by rescaling, without `exp`) -/

namespace Emb

set_option linter.unusedSectionVars false

section Extend

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-- **Uniform local existence of geodesics** (Lemma 10.2 rescaled; no `exp`). -/
theorem localFlow' (x₀ : N) {R : ℝ} (hR : 0 < R) : ∃ U : Set V, IsOpen U ∧ (x₀ : V) ∈ U ∧
    ∃ τ > 0, ∀ y : N, (y : V) ∈ U → ∀ w ∈ Morse.tangentSubspace hN y, ‖w‖ < R →
      ∃ g : ℝ → V, Morse.IsGeodesicOn hN g (Ioo (-τ) τ) ∧ g 0 = y ∧ HasDerivAt g w 0 := by
  obtain ⟨U, hU, hx₀U, ε, hε, Γ, -, hgeo⟩ := Morse.lemma_10_2 hN x₀
  set a := ε / (2 * R) with ha_def
  have ha : 0 < a := by positivity
  have haR : a * R < ε := by
    have : a * R = ε / 2 := by rw [ha_def]; field_simp
    linarith
  refine ⟨U, hU, hx₀U, 2 * a, by positivity, fun y hy w hw hwR => ?_⟩
  have hw' : a • w ∈ Morse.tangentSubspace hN y := Submodule.smul_mem _ _ hw
  have hwε : ‖a • w‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    calc a * ‖w‖ ≤ a * R := by gcongr
      _ < ε := haR
  obtain ⟨hg, h0, hd, -⟩ := hgeo y hy (a • w) hw' hwε
  have hg2 := hg.comp_mul_add a⁻¹ 0
  have ha' : 0 < a⁻¹ := inv_pos.2 ha
  have hpre : Ioo (-(2 * a)) (2 * a) ⊆ (fun t => a⁻¹ * t + 0) ⁻¹' Ioo (-2) 2 := by
    intro t ht
    simp only [mem_preimage, mem_Ioo, add_zero]
    constructor
    · have := mul_lt_mul_of_pos_left ht.1 ha'
      rwa [show a⁻¹ * -(2 * a) = -2 by field_simp] at this
    · have := mul_lt_mul_of_pos_left ht.2 ha'
      rwa [show a⁻¹ * (2 * a) = 2 by field_simp] at this
  refine ⟨fun t => Γ ((y : V), a • w, a⁻¹ * t + 0), hg2.mono isOpen_Ioo hpre, ?_, ?_⟩
  · show Γ ((y : V), a • w, a⁻¹ * 0 + 0) = y
    rw [mul_zero, add_zero]
    exact h0
  · have hlin : HasDerivAt (fun t : ℝ => a⁻¹ * t + 0) a⁻¹ 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul a⁻¹
    have h1 : HasDerivAt (fun t => Γ ((y : V), a • w, t)) (a • w) (a⁻¹ * 0 + 0) := by
      rw [mul_zero, add_zero]; exact hd
    have := HasDerivAt.scomp (h := fun t : ℝ => a⁻¹ * t + 0) (0 : ℝ) h1 hlin
    rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at this
    exact this

/-- A geodesic on `(a, b)` which is smooth up to `b` continues past `b`. -/
theorem extend_right' {f : ℝ → V} {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f (Icc a b)) (hgeo : Morse.IsGeodesicOn hN f (Ioo a b)) (hb : f b ∈ N) :
    ∃ c ∈ Ioo a b, ∃ ε > 0, ∃ h : ℝ → V, Morse.IsGeodesicOn hN h (Ioo c (b + ε)) ∧
      EqOn h f (Ioc c b) := by
  have uI : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hbI : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hd : ContinuousOn (derivWithin f (Icc a b)) (Icc a b) :=
    hf.continuousOn_derivWithin uI (by simp)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hd
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM b hbI)
  have hMd : ∀ t ∈ Ioo a b, ‖deriv f t‖ ≤ M := fun t ht => by
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    exact hM t (Ioo_subset_Icc_self ht)
  obtain ⟨U, hUo, hbU, τ, hτ, hloc⟩ := localFlow' (hN := hN) ⟨f b, hb⟩ (R := M + 1) (by linarith)
  have hpre : f ⁻¹' U ∈ 𝓝[Icc a b] b :=
    (hf.continuousOn b hbI).preimage_mem_nhdsWithin (hUo.mem_nhds hbU)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  set s₀ := max ((a + b) / 2) (b - min δ τ / 2) with hs₀_def
  have hmin : 0 < min δ τ := lt_min hδ hτ
  have hs₁ : (a + b) / 2 ≤ s₀ := le_max_left _ _
  have hs₂ : b - min δ τ / 2 ≤ s₀ := le_max_right _ _
  have hs₃ : s₀ < b := max_lt (by linarith) (by linarith)
  have hs₀ : s₀ ∈ Ioo a b := ⟨by linarith, hs₃⟩
  have hδ' : b - s₀ < δ := by have := min_le_left δ τ; linarith
  have hτ' : b - s₀ < τ := by have := min_le_right δ τ; linarith
  have hs₀U : f s₀ ∈ U := hδU ⟨by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith, Ioo_subset_Icc_self hs₀⟩
  set y : N := ⟨f s₀, hgeo.mem s₀ hs₀⟩
  set w := deriv f s₀
  have hw : w ∈ Morse.tangentSubspace hN y := hgeo.deriv_mem hs₀
  have hwR : ‖w‖ < M + 1 := by linarith [hMd s₀ hs₀]
  obtain ⟨g, hge, hg0, hd0⟩ := hloc y hs₀U w hw hwR
  set h : ℝ → V := fun t => g (t - s₀) with hh_def
  have hpre' : (fun t => 1 * t + -s₀) ⁻¹' Ioo (-τ) τ = Ioo (s₀ - τ) (s₀ + τ) := by
    ext t; simp only [mem_preimage, mem_Ioo]; constructor <;> rintro ⟨h1, h2⟩ <;>
      constructor <;> linarith
  have hhgeo : Morse.IsGeodesicOn hN h (Ioo (s₀ - τ) (s₀ + τ)) := by
    have := hge.comp_mul_add 1 (-s₀)
    rw [hpre'] at this
    refine this.congr fun t _ => ?_
    show g (1 * t + -s₀) = g (t - s₀)
    rw [one_mul, ← sub_eq_add_neg]
  have hh0 : h s₀ = f s₀ := by
    show g (s₀ - s₀) = f s₀
    rw [sub_self]
    exact hg0
  have hh0' : deriv h s₀ = deriv f s₀ := by
    have h1 : HasDerivAt g w (s₀ - s₀) := by
      rw [sub_self]; exact hd0
    exact (h1.comp_sub_const s₀ s₀).deriv
  set c := max ((a + s₀) / 2) (s₀ - τ / 2) with hc_def
  have hc₁ : (a + s₀) / 2 ≤ c := le_max_left _ _
  have hc₂ : s₀ - τ / 2 ≤ c := le_max_right _ _
  have hc₃ : c < s₀ := max_lt (by linarith [hs₀.1]) (by linarith)
  have hcI : c ∈ Ioo a b := ⟨by linarith [hs₀.1], by linarith⟩
  have heq : EqOn h f (Ioo c b) :=
    (hhgeo.mono isOpen_Ioo fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩).eqOn
      (hgeo.mono isOpen_Ioo fun t ht => ⟨by linarith [ht.1], ht.2⟩) isPreconnected_Ioo
      ⟨hc₃, hs₃⟩ hh0 hh0'
  have heq' : EqOn h f (Ioc c b) :=
    heq.of_subset_closure
      (hhgeo.contDiffOn.continuousOn.mono fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (hf.continuousOn.mono fun t ht => ⟨by linarith [ht.1], ht.2⟩) Ioo_subset_Ioc_self
      (by rw [closure_Ioo (by linarith : c ≠ b)]; exact Ioc_subset_Icc_self)
  refine ⟨c, hcI, s₀ + τ - b, by linarith, h,
    hhgeo.mono isOpen_Ioo fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩, heq'⟩

/-- **A geodesic smooth on a closed interval extends to an open one** (a blind geodesic on
`[a, b]` continues past both end points). -/
theorem extend_closed' {f : ℝ → V} {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f (Icc a b)) (hgeo : Morse.IsGeodesicOn hN f (Ioo a b))
    (ha : f a ∈ N) (hb : f b ∈ N) :
    ∃ ε > 0, ∃ g : ℝ → V, Morse.IsGeodesicOn hN g (Ioo (a - ε) (b + ε)) ∧ EqOn g f (Icc a b) := by
  obtain ⟨c₁, hc₁, ε₁, hε₁, h₁, hh₁, he₁⟩ := extend_right' hab hf hgeo hb
  -- the left end, by reflection
  have hab' : -b < -a := by linarith
  have hf' : ContDiffOn ℝ ∞ (fun t => f (-t)) (Icc (-b) (-a)) :=
    hf.comp contDiff_neg.contDiffOn fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hpre : (fun t => -1 * t + 0) ⁻¹' Ioo a b = Ioo (-b) (-a) := by
    ext t; simp only [mem_preimage, mem_Ioo]; constructor <;> rintro ⟨h1, h2⟩ <;>
      constructor <;> linarith
  have hgeo' : Morse.IsGeodesicOn hN (fun t => f (-t)) (Ioo (-b) (-a)) := by
    have := hgeo.comp_mul_add (-1) 0
    rw [hpre] at this
    exact this.congr fun t _ => by simp
  obtain ⟨c₂, hc₂, ε₂, hε₂, h₂, hh₂, he₂⟩ :=
    extend_right' hab' hf' hgeo' (by simpa using ha)
  set d := -c₂ with hd_def
  have hdI : d ∈ Ioo a b := ⟨by linarith [hc₂.2], by linarith [hc₂.1]⟩
  have hpre2 : (fun t => -1 * t + 0) ⁻¹' Ioo c₂ (-a + ε₂) = Ioo (a - ε₂) d := by
    ext t; simp only [mem_preimage, mem_Ioo, hd_def]; constructor <;> rintro ⟨h1, h2⟩ <;>
      constructor <;> linarith
  have hL : Morse.IsGeodesicOn hN (fun t => h₂ (-t)) (Ioo (a - ε₂) d) := by
    have := hh₂.comp_mul_add (-1) 0
    rw [hpre2] at this
    exact this.congr fun t _ => by simp
  have heL : EqOn (fun t => h₂ (-t)) f (Ico a d) := fun t ht => by
    have := he₂ (⟨by linarith [ht.2], by linarith [ht.1]⟩ : -t ∈ Ioc c₂ (-a))
    simpa using this
  set ε := min ε₁ ε₂ with hε_def
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hεle₁ : ε ≤ ε₁ := min_le_left _ _
  have hεle₂ : ε ≤ ε₂ := min_le_right _ _
  classical
  set g : ℝ → V := fun t => if t < a then h₂ (-t) else if t ≤ b then f t else h₁ t with hg_def
  have hgf : EqOn g f (Icc a b) := fun t ht => by
    simp only [hg_def, if_neg (not_lt.2 ht.1), if_pos ht.2]
  refine ⟨ε, hε, g, Morse.isGeodesicOn_of_locally hN isOpen_Ioo fun t ht => ?_, hgf⟩
  by_cases htd : t < d
  · refine ⟨Ioo (a - ε) d, ⟨ht.1, htd⟩, fun u hu => ⟨hu.1, by linarith [hu.2, hdI.2]⟩,
      (hL.mono isOpen_Ioo fun u hu => ⟨by linarith [hu.1], hu.2⟩).congr fun u hu => ?_⟩
    by_cases hua : u < a
    · simp only [hg_def, if_pos hua]
    · have hub : u ≤ b := by linarith [hu.2, hdI.2]
      simp only [hg_def, if_neg hua, if_pos hub]
      exact heL ⟨not_lt.1 hua, hu.2⟩
  by_cases htc : c₁ < t
  · refine ⟨Ioo c₁ (b + ε), ⟨htc, ht.2⟩, fun u hu => ⟨by linarith [hu.1, hc₁.1], hu.2⟩,
      (hh₁.mono isOpen_Ioo fun u hu => ⟨hu.1, by linarith [hu.2]⟩).congr fun u hu => ?_⟩
    have hua : ¬ u < a := by linarith [hu.1, hc₁.1]
    by_cases hub : u ≤ b
    · simp only [hg_def, if_neg hua, if_pos hub]
      exact he₁ ⟨hu.1, hub⟩
    · simp only [hg_def, if_neg hua, if_neg hub]
  · have htI : t ∈ Ioo a b := ⟨by linarith [hdI.1], by linarith [hc₁.2]⟩
    refine ⟨Ioo a b, htI, fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩,
      hgeo.congr fun u hu => ?_⟩
    simp only [hg_def, if_neg (not_lt.2 hu.1.le), if_pos hu.2.le]


end Extend

end Emb

/-- **B on embedded manifolds gives all of A**: `exp_eq`, `exp_zero`, `exp_smul` from B's
uniqueness (`B_emb_to_A_exp`); `exists_initial_ray` from the extension of a closed geodesic past
its ends (`Emb.extend_closed'`, from the project's Lemma 10.2) and `exp_smul`;
`mem_expDom_of_isGeodesicOn` from Lemma 10.2 (a geodesic with initial velocity `w`) and `exp_eq`. -/
theorem B_emb_to_A : B_emb → A := by
  intro hB
  obtain ⟨hexp, hzero, hsmul⟩ := B_emb_to_A_exp hB
  refine ⟨hexp, hzero, hsmul, ?_, ?_⟩
  · -- `exists_initial_ray`
    intro V _ _ _ Z _ _ _ W _ _ _ N hN γ hc hgeo
    obtain ⟨ε, hε, g, hg, hgeq⟩ := Emb.extend_closed' zero_lt_one hc.contDiffOn hgeo
      (hc.mem 0 ⟨le_rfl, zero_le_one⟩) (hc.mem 1 ⟨zero_le_one, le_rfl⟩)
    rw [zero_sub] at hg
    have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have h0J : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := ⟨by linarith, by linarith⟩
    have hvel : Morse.velAlong γ 0 = deriv g 0 := by
      show derivWithin γ (Icc 0 1) 0 = deriv g 0
      rw [derivWithin_congr (fun t ht => (hgeq ht).symm) (hgeq h0I).symm]
      exact (hg.hasDerivAt h0J).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc zero_lt_one 0 h0I)
    have hfrom : Morse.IsGeodesicFrom hN g (γ 0) (Morse.velAlong γ 0) :=
      ⟨ε, hε, hg, hgeq h0I, hvel.symm⟩
    obtain ⟨δ, hδ, -, hsm⟩ := hsmul hfrom
    set η := min δ ε with hη
    have hηδ : η ≤ δ := min_le_left _ _
    have hηε : η ≤ ε := min_le_right _ _
    have hsubδ : Ioo (-η) (1 + η) ⊆ Ioo (-δ) (1 + δ) := fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hsubε : Ioo (-η) (1 + η) ⊆ Ioo (-ε) (1 + ε) := fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ⟨η, lt_min hδ hε, (hg.mono isOpen_Ioo hsubε).congr fun t ht =>
      ((hsm t (hsubδ ht)).2).symm, fun t ht => ?_⟩
    have htδ : t ∈ Ioo (-δ) (1 + δ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [(hsm t htδ).2]
    exact hgeq ht
  · -- `mem_expDom_of_isGeodesicOn`
    intro V _ _ _ Z _ _ _ W _ _ _ N hN y w hy hw η hη hg
    obtain ⟨U, -, hyU, τ, hτ, hloc⟩ := Emb.localFlow' (hN := hN) ⟨y, hy⟩ (R := ‖w‖ + 1)
      (by positivity)
    obtain ⟨g, hgg, hg0, hgd⟩ := hloc ⟨y, hy⟩ hyU w hw (by linarith)
    have hnear : ∀ t ∈ Ioo (-(τ / 2)) (τ / 2), Morse.exp hN y (t • w) = g t := by
      intro t ht
      have hc := hgg.comp_mul_add t 0
      have hsub : Ioo (-1 : ℝ) (1 + 1) ⊆ (fun s => t * s + 0) ⁻¹' Ioo (-τ) τ := by
        intro s hs
        have hs' : |s| < 2 := abs_lt.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
        have ht' : |t| < τ / 2 := abs_lt.2 ht
        have : |t * s + 0| < τ := by
          rw [add_zero, abs_mul]
          calc |t| * |s| ≤ |t| * 2 := by gcongr
            _ < τ / 2 * 2 := by gcongr
            _ = τ := by ring
        exact abs_lt.1 this
      have hlin : HasDerivAt (fun s : ℝ => t * s + 0) t 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_mul t
      have hgd' : HasDerivAt g w (t * 0 + 0) := by rw [mul_zero, add_zero]; exact hgd
      have hfrom : Morse.IsGeodesicFrom hN (fun s => g (t * s + 0)) y (t • w) :=
        ⟨1, one_pos, hc.mono isOpen_Ioo hsub, by
          show g (t * 0 + 0) = y
          rw [mul_zero, add_zero]
          exact hg0, (HasDerivAt.scomp (h := fun s : ℝ => t * s + 0) (0 : ℝ) hgd' hlin).deriv⟩
      rw [hexp hfrom]
      show g (t * 1 + 0) = g t
      rw [mul_one, add_zero]
    refine ⟨fun t => Morse.exp hN y (t • w), η, hη, hg, ?_, ?_⟩
    · show Morse.exp hN y ((0 : ℝ) • w) = y
      rw [zero_smul]
      exact hzero hy
    · have hev : (fun t => Morse.exp hN y (t • w)) =ᶠ[𝓝 0] g :=
        eventually_of_mem (Ioo_mem_nhds (by linarith) (by linarith)) hnear
      rw [hev.deriv_eq]
      exact hgd.deriv

/-- On embedded manifolds, B is equivalent to A. -/
theorem B_emb_iff_A : B_emb ↔ A := ⟨B_emb_to_A, A_to_B_emb⟩

/-- **B implies A**: Milnor's abstract statement, specialized to (the components of) slice
submanifolds with the induced metric and connection, gives the project's theorems. -/
theorem B_to_A : B → A := fun hB => B_emb_to_A (B_to_B_emb hB)

#rt_check RoundTrip.V7_7.A_to_B_emb [Morse.IsGeodesicFrom.exp_eq, Morse.exp_zero,
  Morse.IsGeodesicFrom.exp_smul, Morse.exists_initial_ray, Morse.mem_expDom_of_isGeodesicOn]
#rt_check RoundTrip.V7_7.B_to_A_exp [Morse.IsGeodesicFrom.exp_eq, Morse.exp_zero,
  Morse.IsGeodesicFrom.exp_smul, Morse.exists_initial_ray, Morse.mem_expDom_of_isGeodesicOn]
#rt_check RoundTrip.V7_7.B_to_A [Morse.IsGeodesicFrom.exp_eq, Morse.exp_zero,
  Morse.IsGeodesicFrom.exp_smul, Morse.exists_initial_ray, Morse.mem_expDom_of_isGeodesicOn]
#rt_overlap RoundTrip.V7_7.B_to_A [Morse.IsGeodesicFrom.exp_eq, Morse.exp_zero,
  Morse.IsGeodesicFrom.exp_smul, Morse.exists_initial_ray, Morse.mem_expDom_of_isGeodesicOn]

end RoundTrip.V7_7
