import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_8
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold

namespace RoundTrip.V7_8

/-- The project's statement (universes instantiated at 0) (`tangentBundleSet` a definition): `TN = {(q, v) | v ∈ T_qN} ⊆ V × V` is a slice submanifold;
locally `exp` agrees on `TN` with a smooth `F` on `U × ball 0 ε`; there is an open `O ⊇ N × {0}`
with `O ∩ TN ⊆ expDom` on which `exp` is locally the restriction of smooth maps, and `exp` is `C^∞`
on `O ∩ TN` as a map of manifolds; and `d(exp_q)_0 = (T_qN ↪ V)`. -/
def A : Prop :=
  type_of% @Milnor.Problems.isSliceSubmanifold_tangentBundle.{0,0,0} ∧
    type_of% @Morse.exists_exp_eq.{0,0,0} ∧
    type_of% @Morse.exists_isOpen_exp.{0,0,0} ∧
    type_of% @Morse.contMDiffOn_exp.{0,0,0} ∧
    type_of% @Morse.hasFDerivAt_exp_zero.{0,0,0}

theorem A_holds : A :=
  ⟨@Milnor.Problems.isSliceSubmanifold_tangentBundle,
    @Morse.exists_exp_eq,
    @Morse.exists_isOpen_exp,
    @Morse.contMDiffOn_exp,
    @Morse.hasFDerivAt_exp_zero⟩

/-! No direction is proved; see `V7_8.json`.

## The embedded special case

`B_emb` is B for `M = ↥N` (`RoundTrip.Bridge.Sub hN`, model `ℝⁿ`, connected) with the induced
metric and the induced Levi-Civita connection `Bridge.conn`, on Mathlib's tangent bundle of `↥N`.
`A_to_B_emb`: A gives B_emb — the open set is the preimage of A's `O` (`exists_isOpen_exp`) under
`TN → V × V`, `(x, w) ↦ (x, D_x w)`; smoothness of `exp` on it from A's local smooth extensions;
`d(exp_p)_0 = id` from A's `hasFDerivAt_exp_zero` by the chain rule for `↥N ↪ V`.
`B_to_A_open`: B gives A's `exists_exp_eq`, `exists_isOpen_exp` and `hasFDerivAt_exp_zero` for every
slice submanifold (via the component of `q₀`, re-modelled on `ℝᵐ`): B's smoothness of `exp` on
Mathlib's `TM` is transported to an open set of `V × V` with a smooth retraction `r` onto the
component (`Morse.exists_retraction`), `F(y, u) = exp_{r y}(P_{r y} u)`; `d(exp_q)_0 = id` by the
chain rule. So `B_emb ↔ A_open` (`exists_isOpen_exp ∧ hasFDerivAt_exp_zero`). The domain glue
(B's closed-interval geodesics ⇒ the project's `expDom`) uses `Morse.exists_initial_ray`.
A's `isSliceSubmanifold_tangentBundle` (no Riemannian content) and `contMDiffOn_exp` (stated with
the slice structure of `TN ⊆ V × V`, i.e. with A's first theorem) are outside B. -/

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


section MonoFrom

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z₁ : Type} [NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁] {W₁ : Type} [NormedAddCommGroup W₁]
  [NormedSpace ℝ W₁] {Z₂ : Type} [NormedAddCommGroup Z₂] [NormedSpace ℝ Z₂] {W₂ : Type}
  [NormedAddCommGroup W₂] [NormedSpace ℝ W₂] {N₁ N₂ : Set V}
  {hN₁ : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z₁ W₁ N₁}
  {hN₂ : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z₂ W₂ N₂}

theorem isGeodesicFrom_mono (hsub : N₁ ⊆ N₂)
    (hT : ∀ x (h₁ : x ∈ N₁), Morse.tangentSubspace hN₁ ⟨x, h₁⟩ =
      Morse.tangentSubspace hN₂ ⟨x, hsub h₁⟩)
    {γ : ℝ → V} {q v : V} (h : Morse.IsGeodesicFrom hN₁ γ q v) : Morse.IsGeodesicFrom hN₂ γ q v := by
  obtain ⟨δ, hδ, hγ, h0, hd⟩ := h
  exact ⟨δ, hδ, isGeodesicOn_mono hsub hT hγ, h0, hd⟩

end MonoFrom

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

section Into

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} {MB : Type*} [TopologicalSpace MB] [ChartedSpace HB MB]

/-- **A map into `↥N` is smooth if it is smooth in `V`** (any source manifold). -/
theorem contMDiffAt_of_incl {f : MB → Sub hN} {b : MB}
    (h : ContMDiffAt IB 𝓘(ℝ, V) ∞ (incl hN ∘ f) b) : ContMDiffAt IB 𝓘(ℝ, Bridge.Rn n) ∞ f b := by
  have hcont : ContinuousAt f b :=
    (Topology.IsInducing.subtypeVal.continuousAt_iff (f := f)).2 h.continuousAt
  rw [contMDiffAt_iff_target]
  refine ⟨hcont, ?_⟩
  set σ := Morse.sliceAt hN (f b)
  have hφ : ContDiffAt ℝ ∞ (fun y => (σ.φ y).1) (incl hN (f b)) :=
    contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt
      (σ.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (f b))))
  have e : (extChartAt 𝓘(ℝ, Bridge.Rn n) (f b) ∘ f) = (fun y => (σ.φ y).1) ∘ (incl hN ∘ f) := rfl
  rw [e]
  exact hφ.contMDiffAt.comp b h

end Into

/-- `(x, w) ↦ (x, D_x w)`, `TN → V × V`, is smooth. -/
theorem contMDiff_amb : ContMDiff (𝓘(ℝ, Bridge.Rn n)).tangent 𝓘(ℝ, V × V) ∞
    (fun z : TangentBundle 𝓘(ℝ, Bridge.Rn n) (Sub hN) => (incl hN z.proj, D hN z.proj z.2)) := by
  intro z
  have h := (contMDiffWithinAt_tangent_iff (F := id) (s := univ) (b := z)).1 contMDiffWithinAt_id
  rw [← contMDiffWithinAt_univ]
  exact ((contMDiff_incl (z.proj)).comp_contMDiffWithinAt z h.1).prodMk_space h.2

/-- The fibre `w ↦ (q, w)`, `ℝⁿ → TN`, is smooth. -/
theorem contMDiff_fibre (q : Sub hN) : ContMDiff 𝓘(ℝ, Bridge.Rn n) (𝓘(ℝ, Bridge.Rn n)).tangent ∞
    (fun w : Bridge.Rn n => (⟨q, w⟩ : TangentBundle 𝓘(ℝ, Bridge.Rn n) (Sub hN))) := by
  intro w
  rw [← contMDiffWithinAt_univ]
  refine contMDiffWithinAt_tangent_iff.2 ⟨contMDiffWithinAt_const, ?_⟩
  exact (D hN q).contDiff.contMDiff.contMDiffAt.contMDiffWithinAt

/-- A blind `exp_q(w)` (a geodesic of the induced connection on the closed `[0, 1]`) is in the
project's `expDom` (a geodesic on an open interval containing `[0, 1]`), via
`Morse.exists_initial_ray` (from `Items/V7_13.lean`). -/
theorem mem_expDom_of_expDefined {q : Sub hN} {w : Bridge.Rn n}
    (h : ExpDefined (conn (hN := hN)) q w) : (incl hN q, D hN q w) ∈ Morse.expDom hN := by
  obtain ⟨γ, hγ, hinit⟩ := h
  have hγ' : RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hN)) γ (Icc 0 1) := hγ
  obtain ⟨-, hcd, -⟩ := isGeodesic_iff.1 hγ'
  have hc : Morse.IsSmoothCurveIn hN (incl hN ∘ γ) := ⟨hcd, fun t _ => (γ t).2⟩
  obtain ⟨η, hη, hray, heq⟩ := Morse.exists_initial_ray (hN := hN) hc (isGeodesicOn_Ioo hγ')
  set g : ℝ → V := fun t => Morse.exp hN ((incl hN ∘ γ) 0)
    (t • Morse.velAlong (incl hN ∘ γ) 0) with hg
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h0J : (0 : ℝ) ∈ Ioo (-η) (1 + η) := ⟨by linarith, by linarith⟩
  have hγ0 : γ 0 = q := hinit.1
  have hinit' : RoundTrip.BridgePrelude.InitData (n := n) γ (Icc 0 1) q w := hinit
  have hD := (initData_iff hγ0).1 hinit'
  have hderiv : deriv g 0 = D hN q w := by
    have h1 : HasDerivWithinAt (incl hN ∘ γ) (deriv g 0) (Icc 0 1) 0 :=
      (hray.hasDerivAt h0J).hasDerivWithinAt.congr (fun t ht => (heq t ht).symm)
        (heq 0 h0I).symm
    rw [← hD, D_vel (isSmoothCurve_iff.2 hcd) (uniqueDiffOn_Icc zero_lt_one) h0I]
    exact (uniqueDiffOn_Icc zero_lt_one 0 h0I).eq_deriv _ h1
      (h1.differentiableWithinAt.hasDerivWithinAt)
  refine ⟨g, η, hη, hray, ?_, hderiv⟩
  show g 0 = incl hN q
  refine (heq 0 h0I).trans ?_
  show incl hN (γ 0) = incl hN q
  rw [hγ0]

end Emb

open Bundle in
/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], ∀ p : Bridge.Sub hN,
    (∃ V' : Set (TangentBundle 𝓘(ℝ, Rn n) (Bridge.Sub hN)), IsOpen V' ∧
      (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, Rn n) (Bridge.Sub hN)) ∈ V' ∧
      (∀ z ∈ V', ExpDefined Bridge.conn z.proj z.snd) ∧
      ContMDiffOn (𝓘(ℝ, Rn n)).tangent 𝓘(ℝ, Rn n) ∞
        (fun z : TangentBundle 𝓘(ℝ, Rn n) (Bridge.Sub hN) => expMap Bridge.conn z.proj z.snd) V') ∧
    mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (fun w : Rn n => expMap Bridge.conn p w) 0 =
      ContinuousLinearMap.id ℝ (Rn n)

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- The two theorems of A used for B on embedded manifolds: `exists_isOpen_exp` and
`hasFDerivAt_exp_zero`. (A itself cannot be the hypothesis of a `#rt_check`ed theorem: the
statement of A's `contMDiffOn_exp` mentions A's first theorem `isSliceSubmanifold_tangentBundle`,
through the charted space of `TN`.) -/
def A_open : Prop :=
  type_of% @Morse.exists_isOpen_exp.{0,0,0} ∧ type_of% @Morse.hasFDerivAt_exp_zero.{0,0,0}

theorem A_to_A_open : A → A_open := fun hA => ⟨hA.2.2.1, hA.2.2.2.2⟩

/-- **A implies B on embedded manifolds** (uses A's `exists_isOpen_exp` and
`hasFDerivAt_exp_zero`). -/
theorem A_open_to_B_emb : A_open → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ p
  obtain ⟨O, hO, h0, hexp⟩ := hA.1 (hN := hN)
  set Φ : TangentBundle 𝓘(ℝ, Rn n) (Bridge.Sub hN) → V × V :=
    fun z => (Bridge.incl hN z.proj, Bridge.D hN z.proj z.2) with hΦ_def
  have hΦ : Continuous Φ := Emb.contMDiff_amb.continuous
  have hTN : ∀ z, Φ z ∈ Milnor.Problems.tangentBundleSet hN := fun z =>
    ⟨(z.proj).2, Bridge.D_mem z.proj z.2⟩
  have hdom : ∀ z, Φ z ∈ O → Φ z ∈ Morse.expDom hN := fun z hz => (hexp (Φ z) hz (hTN z)).1
  have hE : ∀ z, Φ z ∈ O → Bridge.incl hN (expMap Bridge.conn z.proj z.2) =
      Morse.exp hN (Bridge.incl hN z.proj) (Bridge.D hN z.proj z.2) := fun z hz =>
    Bridge.expMap_eq (hdom z hz)
  have hsm : ∀ z, Φ z ∈ O → ContMDiffAt (𝓘(ℝ, Rn n)).tangent 𝓘(ℝ, V) ∞
      (fun z : TangentBundle 𝓘(ℝ, Rn n) (Bridge.Sub hN) =>
        Bridge.incl hN (expMap Bridge.conn z.proj z.2)) z := by
    intro z hz
    obtain ⟨-, F, O', hO', hzO', hF, hFeq⟩ := hexp (Φ z) hz (hTN z)
    have h1 : ContMDiffAt (𝓘(ℝ, Rn n)).tangent 𝓘(ℝ, V) ∞ (F ∘ Φ) z :=
      (hF.contDiffAt (hO'.mem_nhds hzO')).contMDiffAt.comp z (Emb.contMDiff_amb z)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [((hO.inter hO').preimage hΦ).mem_nhds ⟨hz, hzO'⟩] with z' hz'
    rw [hE z' hz'.1]
    exact hFeq (Φ z') hz'.2 (hTN z')
  have hp0 : Φ ⟨p, 0⟩ ∈ O := by
    show (Bridge.incl hN p, Bridge.D hN p 0) ∈ O
    rw [map_zero]
    exact h0 _ p.2
  refine ⟨⟨Φ ⁻¹' O, hO.preimage hΦ, hp0, fun z hz => Bridge.expDefined_of_mem_expDom (hdom z hz),
    fun z hz => (Emb.contMDiffAt_of_incl (hsm z hz)).contMDiffWithinAt⟩, ?_⟩
  -- `d(exp_p)_0 = id`
  set f : Rn n → Bridge.Sub hN := fun w => expMap Bridge.conn p w with hf_def
  have hι : Continuous (fun w : Rn n => (Bridge.incl hN p, Bridge.D hN p w)) :=
    continuous_const.prodMk (Bridge.D hN p).continuous
  have hnb : {w : Rn n | (Bridge.incl hN p, Bridge.D hN p w) ∈ O} ∈ 𝓝 (0 : Rn n) :=
    (hO.preimage hι).mem_nhds hp0
  have hf_eq : ∀ w ∈ {w : Rn n | (Bridge.incl hN p, Bridge.D hN p w) ∈ O},
      Bridge.incl hN (f w) = Morse.exp hN (Bridge.incl hN p) (Bridge.D hN p w) :=
    fun w hw => hE ⟨p, w⟩ hw
  have hf0 : f 0 = p := by
    apply Subtype.ext
    show Bridge.incl hN (f 0) = Bridge.incl hN p
    rw [hf_eq 0 (mem_of_mem_nhds hnb), map_zero]
    exact Morse.exp_zero p.2
  -- the derivative of `w ↦ exp_p(D_p w)`, from A
  set T := Morse.tangentSubspace hN p
  set Dc : Rn n →L[ℝ] T := (Bridge.D hN p).codRestrict T (Bridge.D_mem p) with hDc
  have hT' : HasFDerivAt (fun v : T => Morse.exp hN (Bridge.incl hN p) v) T.subtypeL (Dc 0) := by
    rw [map_zero]
    exact hA.2 (hN := hN) p
  have hg : HasFDerivAt (fun w : Rn n => Morse.exp hN (Bridge.incl hN p) (Bridge.D hN p w))
      (Bridge.D hN p) 0 :=
    (hT'.comp (0 : Rn n) Dc.hasFDerivAt).congr_fderiv (ContinuousLinearMap.ext fun w => rfl)
  have hincl_f : HasFDerivAt (Bridge.incl hN ∘ f) (Bridge.D hN p) 0 :=
    hg.congr_of_eventuallyEq (eventually_of_mem hnb hf_eq)
  -- smoothness of `f` at `0`
  obtain ⟨-, F, O', hO', h0O', hF, hFeq⟩ := hexp (Bridge.incl hN p, Bridge.D hN p 0) hp0 (hTN ⟨p, 0⟩)
  have hf_sm : ContMDiffAt 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) ∞ f 0 := by
    apply Emb.contMDiffAt_of_incl
    have h1 : ContDiffAt ℝ ∞ (F ∘ fun w : Rn n => (Bridge.incl hN p, Bridge.D hN p w)) 0 :=
      (hF.contDiffAt (hO'.mem_nhds h0O')).comp (0 : Rn n)
        (contDiffAt_const.prodMk (Bridge.D hN p).contDiff.contDiffAt)
    refine h1.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hnb, (hO'.preimage hι).mem_nhds h0O'] with w hw hw'
    show Bridge.incl hN (f w) = F (Bridge.incl hN p, Bridge.D hN p w)
    rw [hf_eq w hw]
    exact hFeq _ hw' (hTN ⟨p, w⟩)
  have hf_md : MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) f 0 := hf_sm.mdifferentiableAt (by simp)
  have hincl_md : MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (Bridge.incl hN) (f 0) :=
    (Bridge.contMDiff_incl (f 0)).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp (0 : Rn n) hincl_md hf_md
  rw [mfderiv_eq_fderiv, hincl_f.fderiv] at hcomp
  refine ContinuousLinearMap.ext fun w => Bridge.D_injective (f 0) ?_
  have e := congrArg (fun T => T w) hcomp
  calc Bridge.D hN (f 0) (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) f 0 w) = Bridge.D hN p w := e.symm
    _ = Bridge.D hN (f 0) w := by rw [hf0]
    _ = Bridge.D hN (f 0) ((ContinuousLinearMap.id ℝ (Rn n)) w) := rfl

/-- **A implies B on embedded manifolds.** -/
theorem A_to_B_emb : A → B_emb := fun hA => A_open_to_B_emb (A_to_A_open hA)

/-- A's `d(exp_q)_0 = id`. -/
def A_deriv : Prop := type_of% @Morse.hasFDerivAt_exp_zero.{0,0,0}

theorem A_to_A_deriv : A → A_deriv := fun hA => hA.2.2.2.2

/-- **B on embedded manifolds gives A's `hasFDerivAt_exp_zero`** for every slice submanifold (via
the component of `q`, re-modelled on `ℝᵐ`). -/
theorem B_emb_to_A_deriv : B_emb → A_deriv := by
  intro hB V _ _ _ Z _ _ _ W _ _ _ N hN q
  obtain ⟨O, hO, hqO, hC, hconn, hT, hS⟩ := Emb.reduce hN q
  have hsub : N ∩ O ⊆ N := inter_subset_left
  have hqC : (q : V) ∈ N ∩ O := ⟨q.2, hqO⟩
  let q' : Bridge.Sub hC := (⟨(q : V), hqC⟩ : ↥(N ∩ O))
  obtain ⟨⟨V', hV'o, hq'V', hdef, hsm⟩, hmf⟩ := hB V W _ (N ∩ O) hC q'
  set f : Bridge.Rn (finrank ℝ Z) → Bridge.Sub hC := fun w => expMap Bridge.conn q' w with hf_def
  have hι := Emb.contMDiff_fibre (hN := hC) q'
  have hnb : (fun w : Bridge.Rn (finrank ℝ Z) =>
      (⟨q', w⟩ : TangentBundle 𝓘(ℝ, Bridge.Rn (finrank ℝ Z)) (Bridge.Sub hC))) ⁻¹' V' ∈
      𝓝 (0 : Bridge.Rn (finrank ℝ Z)) :=
    (hV'o.preimage hι.continuous).mem_nhds hq'V'
  have hf_sm : ContMDiffAt 𝓘(ℝ, Bridge.Rn (finrank ℝ Z)) 𝓘(ℝ, Bridge.Rn (finrank ℝ Z)) ∞ f 0 :=
    (hsm.contMDiffAt (hV'o.mem_nhds hq'V')).comp (0 : Bridge.Rn (finrank ℝ Z)) (hι 0)
  have hf0 : f 0 = q' := by
    apply Subtype.ext
    have hdom : (Bridge.incl hC q', Bridge.D hC q' 0) ∈ Morse.expDom hC := by
      rw [map_zero]
      exact (Morse.isGeodesicFrom_const (hN := hC) hqC).mem_expDom
    have := Bridge.expMap_eq hdom
    rw [map_zero] at this
    exact this.trans (Morse.exp_zero hqC)
  have hf_md := hf_sm.mdifferentiableAt (by simp)
  have hincl_md : MDifferentiableAt 𝓘(ℝ, Bridge.Rn (finrank ℝ Z)) 𝓘(ℝ, V) (Bridge.incl hC) (f 0) :=
    (Bridge.contMDiff_incl (f 0)).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp (0 : Bridge.Rn (finrank ℝ Z)) hincl_md hf_md
  have hdiff : HasFDerivAt (Bridge.incl hC ∘ f) (Bridge.D hC q') 0 := by
    have h1 := (hincl_md.comp (0 : Bridge.Rn (finrank ℝ Z)) hf_md).hasMFDerivAt
    rw [hcomp, hmf] at h1
    refine (hasMFDerivAt_iff_hasFDerivAt.1 h1).congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
    show Bridge.D hC (f 0) w = Bridge.D hC q' w
    rw [hf0]
  have hnear : ∀ w ∈ (fun w : Bridge.Rn (finrank ℝ Z) =>
      (⟨q', w⟩ : TangentBundle 𝓘(ℝ, Bridge.Rn (finrank ℝ Z)) (Bridge.Sub hC))) ⁻¹' V',
      Bridge.incl hC (f w) = Morse.exp hN q (Bridge.D hC q' w) := by
    intro w hw
    have hdom : (Bridge.incl hC q', Bridge.D hC q' w) ∈ Morse.expDom hC :=
      Emb.mem_expDom_of_expDefined (hdef _ hw)
    refine (Bridge.expMap_eq hdom).trans ?_
    obtain ⟨γ, hγ⟩ := hdom
    rw [hγ.exp_eq]
    exact (Emb.isGeodesicFrom_mono hsub (fun x hx => hT x hx) hγ).exp_eq.symm
  have hg : HasFDerivAt (fun w => Morse.exp hN q (Bridge.D hC q' w)) (Bridge.D hC q') 0 :=
    hdiff.congr_of_eventuallyEq (eventually_of_mem hnb fun w hw => (hnear w hw).symm)
  set T := Morse.tangentSubspace hN q
  set Lc : T →L[ℝ] Bridge.Rn (finrank ℝ Z) := (Bridge.L hC q').comp T.subtypeL with hLc
  have hg' : HasFDerivAt (fun w => Morse.exp hN q (Bridge.D hC q' w)) (Bridge.D hC q') (Lc 0) := by
    rw [map_zero]
    exact hg
  have hTC : ∀ v : T, (v : V) ∈ Morse.tangentSubspace hC q' := fun v => by
    show (v : V) ∈ Morse.tangentSubspace hC ⟨(q : V), hqC⟩
    rw [hT]
    exact v.2
  have h3 := hg'.comp (0 : T) Lc.hasFDerivAt
  refine (h3.congr_fderiv (ContinuousLinearMap.ext fun v => Bridge.D_L (hTC v))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun v => ?_)
  show Morse.exp hN q v = Morse.exp hN q (Bridge.D hC q' (Bridge.L hC q' v))
  rw [Bridge.D_L (hTC v)]

/-- **B implies A's `hasFDerivAt_exp_zero`**, by specializing B to the component of `q`. -/
theorem B_to_A_deriv : B → A_deriv := fun hB => B_emb_to_A_deriv (B_to_B_emb hB)

/-! ### B gives A's local smooth extensions of `exp` (`exists_exp_eq`, `exists_isOpen_exp`)

B's smoothness of `exp` on Mathlib's tangent bundle of the component `C` of `q₀` is transported to
an open set of `V × V` with a smooth retraction `r` onto `C` (`Morse.exists_retraction`, outside the
item): `F(y, u) = exp_{r y}(P_{r y} u)`, read through `Ψ(y, u) = (r y, P_{r y} u) ∈ TC`. -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

open Classical in
/-- Lift a point of `V` to `N` (junk `q₀` off `N`). -/
noncomputable def liftV (q₀ : Sub hN) (y : V) : Sub hN := if h : y ∈ N then (⟨y, h⟩ : N) else q₀

theorem liftV_of_mem (q₀ : Sub hN) {y : V} (h : y ∈ N) : liftV q₀ y = (⟨y, h⟩ : N) := by
  unfold liftV; exact dif_pos h

theorem incl_liftV (q₀ : Sub hN) {y : V} (h : y ∈ N) : incl hN (liftV q₀ y) = y := by
  rw [liftV_of_mem q₀ h]; rfl

/-- `(y, u) ↦ (r y, P_{r y} u) ∈ TN`, for a map `r` into `N` (junk off `N`). -/
noncomputable def Ψ (q₀ : Sub hN) (r : V → V) (z : V × V) : TangentBundle 𝓘(ℝ, Bridge.Rn n) (Sub hN) :=
  ⟨liftV q₀ (r z.1), L hN (liftV q₀ (r z.1)) (P hN (liftV q₀ (r z.1)) z.2)⟩

theorem contMDiffAt_Ψ (q₀ : Sub hN) {r : V → V} {U₀ : Set V} (hU₀ : IsOpen U₀)
    (hr : ContDiffOn ℝ ∞ r U₀) (hrN : ∀ y ∈ U₀, r y ∈ N) {z : V × V} (hz : z.1 ∈ U₀) :
    ContMDiffAt 𝓘(ℝ, V × V) (𝓘(ℝ, Bridge.Rn n)).tangent ∞ (Ψ q₀ r) z := by
  have hb : ContMDiffAt 𝓘(ℝ, V × V) 𝓘(ℝ, Bridge.Rn n) ∞ (fun z : V × V => liftV q₀ (r z.1)) z := by
    apply contMDiffAt_of_incl
    have h1 : ContDiffAt ℝ ∞ (fun z : V × V => r z.1) z :=
      (hr.contDiffAt (hU₀.mem_nhds hz)).comp z contDiffAt_fst
    refine h1.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [(hU₀.preimage continuous_fst).mem_nhds hz] with z' hz'
    exact incl_liftV q₀ (hrN _ hz')
  rw [← contMDiffWithinAt_univ]
  refine contMDiffWithinAt_tangent_iff.2 ⟨hb.contMDiffWithinAt, ?_⟩
  have h2 : ContMDiffAt 𝓘(ℝ, V × V) 𝓘(ℝ, V) ∞
      (fun z : V × V => P hN (liftV q₀ (r z.1)) z.2) z :=
    ((contMDiff_P (liftV q₀ (r z.1))).comp z hb).clm_apply contDiff_snd.contMDiff.contMDiffAt
  refine (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z' => ?_)).contMDiffWithinAt
  exact D_L_P _ _

theorem Ψ_eq (q₀ : Sub hN) {r : V → V} {p : Sub hN} (hr : r (incl hN p) = incl hN p) {v : V}
    (hv : v ∈ Morse.tangentSubspace hN p) :
    Ψ q₀ r (incl hN p, v) = (⟨p, L hN p v⟩ : TangentBundle 𝓘(ℝ, Bridge.Rn n) (Sub hN)) := by
  have hb : liftV q₀ (r (incl hN p)) = p := by
    apply Subtype.ext
    show incl hN (liftV q₀ (r (incl hN p))) = incl hN p
    rw [hr]
    exact incl_liftV q₀ p.2
  have hP : P hN p v = v := by
    rw [← D_L hv, P_D]
  unfold Ψ
  simp only
  rw [hb, hP]

end Emb

/-- **B on embedded manifolds gives A's `exists_exp_eq`** (for every slice submanifold, via the
component of `q₀`): near `(q₀, 0)`, the project's `exp` on `TN` is the restriction of a smooth map
on `U × B_ε(0) ⊆ V × V`. -/
theorem B_emb_to_exists_exp_eq : B_emb → type_of% @Morse.exists_exp_eq.{0,0,0} := by
  intro hB V _ _ _ Z _ _ _ W _ _ _ N hN q₀
  obtain ⟨O, hO, hqO, hC, hconn, hT, hS⟩ := Emb.reduce hN q₀
  have hsub : N ∩ O ⊆ N := inter_subset_left
  have hqC : (q₀ : V) ∈ N ∩ O := ⟨q₀.2, hqO⟩
  let q₀' : Bridge.Sub hC := (⟨(q₀ : V), hqC⟩ : ↥(N ∩ O))
  obtain ⟨⟨V', hV'o, hq'V', hdef, hsm⟩, -⟩ := hB V W _ (N ∩ O) hC q₀'
  obtain ⟨U₀, hU₀, hq₀U₀, r, hr, hrN, hrid⟩ := Morse.exists_retraction hC q₀'
  set Ψ := Emb.Ψ q₀' r with hΨ
  have hΨc : ContinuousOn Ψ (U₀ ×ˢ univ) := fun z hz =>
    (Emb.contMDiffAt_Ψ q₀' hU₀ hr hrN hz.1).continuousAt.continuousWithinAt
  set S := (U₀ ∩ O) ×ˢ univ ∩ Ψ ⁻¹' V' with hS_def
  have hSo : IsOpen S :=
    (hΨc.mono (prod_mono inter_subset_left subset_rfl)).isOpen_inter_preimage
      ((hU₀.inter hO).prod isOpen_univ) hV'o
  have hrq : r (Bridge.incl hC q₀') = Bridge.incl hC q₀' := hrid _ hq₀U₀ hqC
  have hΨ0 : Ψ ((q₀ : V), 0) = (⟨q₀', 0⟩ : TangentBundle 𝓘(ℝ, Bridge.Rn (finrank ℝ Z)) _) := by
    have := Emb.Ψ_eq q₀' hrq (zero_mem (Morse.tangentSubspace hC q₀'))
    rw [map_zero] at this
    exact this
  have hq₀S : ((q₀ : V), (0 : V)) ∈ S := ⟨⟨⟨hq₀U₀, hqO⟩, trivial⟩, by
    show Ψ ((q₀ : V), 0) ∈ V'
    rw [hΨ0]
    exact hq'V'⟩
  obtain ⟨u, hu, v', hv', huv⟩ := mem_nhds_prod_iff.1 (hSo.mem_nhds hq₀S)
  obtain ⟨U, hUu, hU, hq₀U⟩ := mem_nhds_iff.1 hu
  obtain ⟨ε, hε, hεv⟩ := Metric.mem_nhds_iff.1 hv'
  have hsubS : U ×ˢ Metric.ball (0 : V) ε ⊆ S := fun z hz => huv ⟨hUu hz.1, hεv hz.2⟩
  set F : V × V → V := fun z => Bridge.incl hC (expMap Bridge.conn (Ψ z).proj (Ψ z).snd) with hF
  refine ⟨U, hU, hq₀U, ε, hε, F, ?_, fun p hpU v hv hvε => ?_⟩
  · -- smoothness
    refine (contMDiffOn_iff_contDiffOn.1 fun z hz => ?_).mono hsubS
    have hE : ContMDiffAt (𝓘(ℝ, Bridge.Rn (finrank ℝ Z))).tangent 𝓘(ℝ, Bridge.Rn (finrank ℝ Z)) ∞
        (fun z' : TangentBundle 𝓘(ℝ, Bridge.Rn (finrank ℝ Z)) (Bridge.Sub hC) =>
          expMap Bridge.conn z'.proj z'.snd) (Ψ z) :=
      hsm.contMDiffAt (hV'o.mem_nhds hz.2)
    exact ((Bridge.contMDiff_incl _).comp z (hE.comp z
      (Emb.contMDiffAt_Ψ q₀' hU₀ hr hrN hz.1.1.1))).contMDiffWithinAt
  · -- values
    have hpS : ((p : V), v) ∈ S := hsubS ⟨hpU, show v ∈ Metric.ball (0 : V) ε by
      rw [Metric.mem_ball, dist_zero_right]; exact hvε⟩
    have hpC : (p : V) ∈ N ∩ O := ⟨p.2, hpS.1.1.2⟩
    let p' : Bridge.Sub hC := (⟨(p : V), hpC⟩ : ↥(N ∩ O))
    have hvC : v ∈ Morse.tangentSubspace hC p' := by
      show v ∈ Morse.tangentSubspace hC ⟨(p : V), hpC⟩
      rw [hT]
      exact hv
    have hΨp : Ψ ((p : V), v) = (⟨p', Bridge.L hC p' v⟩ : TangentBundle _ _) :=
      Emb.Ψ_eq (p := p') q₀' (hrid (p : V) hpS.1.1.1 hpC) hvC
    have hV'p : (⟨p', Bridge.L hC p' v⟩ : TangentBundle 𝓘(ℝ, Bridge.Rn (finrank ℝ Z)) _) ∈ V' := by
      rw [← hΨp]
      exact hpS.2
    have hdom : (Bridge.incl hC p', Bridge.D hC p' (Bridge.L hC p' v)) ∈ Morse.expDom hC :=
      Emb.mem_expDom_of_expDefined (hdef _ hV'p)
    have hFp : F ((p : V), v) = Bridge.incl hC (expMap Bridge.conn p' (Bridge.L hC p' v)) := by
      show Bridge.incl hC (expMap Bridge.conn (Ψ ((p : V), v)).proj (Ψ ((p : V), v)).snd) = _
      rw [hΨp]
    rw [Bridge.D_L hvC] at hdom
    obtain ⟨γ, hγ⟩ : ∃ γ, Morse.IsGeodesicFrom hC γ (p : V) v := hdom
    have hγN := Emb.isGeodesicFrom_mono hsub (fun x hx => hT x hx) hγ
    refine ⟨γ, hγN, ?_⟩
    rw [hFp, hγN.exp_eq]
    refine Eq.trans ?_ (Bridge.expMap_eq (q := p') (w := Bridge.L hC p' v)
      (by rw [Bridge.D_L hvC]; exact ⟨γ, hγ⟩)).symm
    rw [Bridge.D_L hvC]
    exact hγ.exp_eq.symm

/-- **B on embedded manifolds gives A's `exists_isOpen_exp`** (the project's proof from
`exists_exp_eq`, with `exists_exp_eq` from B) **and `hasFDerivAt_exp_zero`**. -/
theorem B_emb_to_A_open : B_emb → A_open := by
  intro hB
  have hloc : type_of% @Morse.exists_exp_eq.{0,0,0} := B_emb_to_exists_exp_eq hB
  refine ⟨?_, B_emb_to_A_deriv hB⟩
  intro V _ _ _ Z _ _ _ W _ _ _ N hN
  choose U hU hqU ε hε F hF hexp using fun q₀ : N => hloc (hN := hN) q₀
  refine ⟨⋃ q₀ : N, U q₀ ×ˢ Metric.ball (0 : V) (ε q₀),
    isOpen_iUnion fun q₀ => (hU q₀).prod Metric.isOpen_ball, fun q hq => ?_, fun z hz hzT => ?_⟩
  · exact mem_iUnion.2 ⟨⟨q, hq⟩, hqU _, Metric.mem_ball_self (hε _)⟩
  · obtain ⟨q₀, hz1, hz2⟩ := mem_iUnion.1 hz
    obtain ⟨hzN, hzv⟩ := hzT
    have hz2' : ‖z.2‖ < ε q₀ := by rwa [Metric.mem_ball, dist_zero_right] at hz2
    obtain ⟨γ, hγ, -⟩ := hexp q₀ ⟨z.1, hzN⟩ hz1 z.2 hzv hz2'
    refine ⟨hγ.mem_expDom, F q₀, U q₀ ×ˢ Metric.ball (0 : V) (ε q₀), (hU q₀).prod Metric.isOpen_ball,
      ⟨hz1, hz2⟩, hF q₀, fun z' hz' hz'T => ?_⟩
    obtain ⟨hz'N, hz'v⟩ := hz'T
    have h2 : ‖z'.2‖ < ε q₀ := by
      have := hz'.2
      rwa [Metric.mem_ball, dist_zero_right] at this
    exact (hexp q₀ ⟨z'.1, hz'N⟩ hz'.1 z'.2 hz'v h2).choose_spec.2

/-- On embedded manifolds, B is exactly A's `exists_isOpen_exp` and `hasFDerivAt_exp_zero`. -/
theorem B_emb_iff_A_open : B_emb ↔ A_open := ⟨B_emb_to_A_open, A_open_to_B_emb⟩

/-- **B implies A's `exists_isOpen_exp` and `hasFDerivAt_exp_zero`**, by specializing B to the
components of `↥N`. -/
theorem B_to_A_open : B → A_open := fun hB => B_emb_to_A_open (B_to_B_emb hB)

#rt_check RoundTrip.V7_8.A_open_to_B_emb [Milnor.Problems.isSliceSubmanifold_tangentBundle,
  Morse.exists_exp_eq, Morse.exists_isOpen_exp, Morse.contMDiffOn_exp, Morse.hasFDerivAt_exp_zero]
#rt_check RoundTrip.V7_8.B_to_A_deriv [Milnor.Problems.isSliceSubmanifold_tangentBundle,
  Morse.exists_exp_eq, Morse.exists_isOpen_exp, Morse.contMDiffOn_exp, Morse.hasFDerivAt_exp_zero]
#rt_check RoundTrip.V7_8.B_to_A_open [Milnor.Problems.isSliceSubmanifold_tangentBundle,
  Morse.exists_exp_eq, Morse.exists_isOpen_exp, Morse.contMDiffOn_exp, Morse.hasFDerivAt_exp_zero]
#rt_overlap RoundTrip.V7_8.B_to_A_open [Milnor.Problems.isSliceSubmanifold_tangentBundle,
  Morse.exists_exp_eq, Morse.exists_isOpen_exp, Morse.contMDiffOn_exp, Morse.hasFDerivAt_exp_zero]

end RoundTrip.V7_8
