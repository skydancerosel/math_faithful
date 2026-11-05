import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_18
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold

namespace RoundTrip.V7_18

/-- The project's statement (universes instantiated at 0) (`riemDist` a definition: the `ℝ≥0∞`-valued infimum of `pathLength` over piecewise smooth
paths in `N`; `riemDist_le_pathLength`, `riemDist_triangle`: universe 0, ANY subset `N ⊆ V`):
`riemDist ≤ pathLength` of any such path, the triangle inequality, points outside the normal ball of
radius `s` are at distance `≥ s`, and (for slice submanifolds) `riemDist p q = 0 ⇒ p = q`. -/
def A : Prop :=
  type_of% @Morse.riemDist_le_pathLength.{0} ∧
    type_of% @Morse.riemDist_triangle.{0} ∧
    type_of% @Morse.NormalCoord.ofReal_le_riemDist.{0,0,0} ∧
    type_of% @Morse.eq_of_riemDist_eq_zero.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.riemDist_le_pathLength,
    @Morse.riemDist_triangle,
    @Morse.NormalCoord.ofReal_le_riemDist,
    @Morse.eq_of_riemDist_eq_zero⟩

/-! No direction is proved; see `V7_18.json`.

## The embedded special case

B quantifies over Riemannian manifolds (no connection). `B_emb` is B for `M = ↥N`
(`RoundTrip.Bridge.Sub hN`, model `ℝⁿ`, connected) with the induced metric; the Bridge's
`rho_eq` identifies B's `ρ` with `(riemDist p q).toReal`. On embedded manifolds B is exactly the
part `A_metric` of A — the triangle inequality (for slice submanifolds) and positivity
(`eq_of_riemDist_eq_zero`) — `B_emb_iff_A_metric`:
* `A_metric_to_B_emb`: finiteness of `riemDist` on a connected `N` (the joining paths of B) is
  proved from A's triangle inequality and straight segments in slice charts (`Emb.fin`, the
  project's `riemDist_ne_top` uses A's theorems), then `ρ ≥ 0`, `ρ = 0 ↔ p = q`, symmetry
  (`Morse.riemDist_comm`, outside the item) and the triangle inequality follow through `rho_eq`;
* `B_emb_to_A_metric`: for any slice submanifold (any model, `N` not assumed connected), B is
  applied to the connected component of the first point (paths in `N` from it stay in it, so its
  distance is that of `N`).
A's `riemDist_le_pathLength` (the definition of an infimum) and the triangle inequality for an
arbitrary subset `N ⊆ V` are not about Riemannian manifolds; A's `NormalCoord.ofReal_le_riemDist`
(the quantitative lower bound of Theorem 10.4) is not a consequence of B. -/

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

/-! ### Components and the distance (from `Items/V7_28.lean`) -/

section Component

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {N C : Set V}

theorem riemDist_eq_of_closed (hCN : C ⊆ N)
    (hpath : ∀ (c : ℝ → V) (a b : ℝ), Morse.IsPiecewiseSmooth c a b → (∀ t ∈ Icc a b, c t ∈ N) →
      c a ∈ C → ∀ t ∈ Icc a b, c t ∈ C) {x : V} (hx : x ∈ C) (y : V) :
    Morse.riemDist (N := C) x y = Morse.riemDist (N := N) x y := by
  unfold Morse.riemDist Morse.pathLengths
  congr 1
  ext L
  constructor
  · rintro ⟨c, a, b, hc, hcC, ha, hb, rfl⟩
    exact ⟨c, a, b, hc, fun t ht => hCN (hcC t ht), ha, hb, rfl⟩
  · rintro ⟨c, a, b, hc, hcN, ha, hb, rfl⟩
    exact ⟨c, a, b, hc, hpath c a b hc hcN (by rw [ha]; exact hx), ha, hb, rfl⟩

theorem mem_of_riemDist_ne_top
    (hpath : ∀ (c : ℝ → V) (a b : ℝ), Morse.IsPiecewiseSmooth c a b → (∀ t ∈ Icc a b, c t ∈ N) →
      c a ∈ C → ∀ t ∈ Icc a b, c t ∈ C) {x y : V} (hx : x ∈ C)
    (h : Morse.riemDist (N := N) x y ≠ ⊤) : y ∈ C := by
  unfold Morse.riemDist at h
  have hne : (Morse.pathLengths (N := N) x y).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, sInf_empty] at h
    exact h rfl
  obtain ⟨L, c, a, b, hc, hcN, ha, hb, -⟩ := hne
  rw [← hb]
  exact hpath c a b hc hcN (by rw [ha]; exact hx) b ⟨hc.1, le_rfl⟩

/-- A finite distance comes from a path; in particular its first point is in `N`. -/
theorem exists_path_of_ne_top {x y : V} (h : Morse.riemDist (N := N) x y ≠ ⊤) :
    ∃ (c : ℝ → V) (a b : ℝ), Morse.IsPiecewiseSmooth c a b ∧ (∀ t ∈ Icc a b, c t ∈ N) ∧
      c a = x ∧ c b = y := by
  unfold Morse.riemDist at h
  have hne : (Morse.pathLengths (N := N) x y).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, sInf_empty] at h
    exact h rfl
  obtain ⟨L, c, a, b, hc, hcN, ha, hb, -⟩ := hne
  exact ⟨c, a, b, hc, hcN, ha, hb⟩

end Component

/-! ### Finiteness of the distance on a connected `N`, from the triangle inequality -/

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

/-- Points of `N` near `y` are joined to `y` by a smooth path in `N` (a straight segment in the
slice chart at `y`). -/
theorem local_path (y : Sub hN) : ∃ U ∈ 𝓝 y, ∀ y' ∈ U, ∃ c : ℝ → V,
    Morse.IsPiecewiseSmooth c 0 1 ∧ (∀ t ∈ Icc (0 : ℝ) 1, c t ∈ N) ∧ c 0 = incl hN y ∧
      c 1 = incl hN y' := by
  set σ := Morse.sliceAt hN y
  have hy : incl hN y ∈ σ.φ.source := Morse.mem_sliceAt_source hN y
  set u₀ := σ.toChart y with hu₀_def
  have hu₀ : u₀ ∈ σ.toChart.target := Morse.toChart_apply_mem_target σ hy
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (Morse.isOpen_toChart_target σ) u₀ hu₀
  refine ⟨σ.toChart.source ∩ σ.toChart ⁻¹' Metric.ball u₀ r,
    Filter.inter_mem (σ.toChart.open_source.mem_nhds hy)
      ((σ.toChart.continuousAt hy).preimage_mem_nhds (Metric.ball_mem_nhds u₀ hr)),
    fun y' hy' => ?_⟩
  set u₁ := σ.toChart y' with hu₁_def
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, u₀ + t • (u₁ - u₀) ∈ Metric.ball u₀ r := by
    intro t ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    have h1 : ‖u₁ - u₀‖ < r := by rw [← dist_eq_norm]; exact hy'.2
    calc t * ‖u₁ - u₀‖ ≤ 1 * ‖u₁ - u₀‖ := by gcongr; exact ht.2
      _ < r := by rw [one_mul]; exact h1
  refine ⟨fun t => Morse.sliceParam σ (u₀ + t • (u₁ - u₀)), ?_,
    fun t ht => Morse.sliceParam_mem σ (hball (hseg t ht)), ?_, ?_⟩
  · exact Morse.IsPiecewiseSmooth.of_contDiffOn (s := Icc 0 1)
      ((Morse.contDiffOn_sliceParam σ).comp
        (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn
        fun t ht => hball (hseg t ht)) zero_le_one subset_rfl
  · show Morse.sliceParam σ (u₀ + (0 : ℝ) • (u₁ - u₀)) = incl hN y
    rw [zero_smul, add_zero]
    exact Morse.sliceParam_toChart σ hy
  · show Morse.sliceParam σ (u₀ + (1 : ℝ) • (u₁ - u₀)) = incl hN y'
    have e : u₀ + (1 : ℝ) • (u₁ - u₀) = u₁ := by rw [one_smul]; abel
    rw [e]
    exact Morse.sliceParam_toChart σ hy'.1

/-- **On a connected `N` the distance is finite**, from the triangle inequality and local paths
(the points at finite distance form an open and closed set). -/
theorem fin (htri : ∀ p q r : V,
      Morse.riemDist (N := N) p r ≤ Morse.riemDist (N := N) p q + Morse.riemDist (N := N) q r)
    [ConnectedSpace (Sub hN)] (p q : Sub hN) :
    Morse.riemDist (N := N) (incl hN p) (incl hN q) ≠ ⊤ := by
  have hloc : ∀ y : Sub hN, ∀ᶠ y' in 𝓝 y,
      Morse.riemDist (N := N) (incl hN y) (incl hN y') ≠ ⊤ := by
    intro y
    obtain ⟨U, hU, hpath⟩ := local_path y
    filter_upwards [hU] with y' hy'
    obtain ⟨c, hc, hcN, h0, h1⟩ := hpath y' hy'
    have : Morse.riemDist (N := N) (incl hN y) (incl hN y') ≤
        ENNReal.ofReal (Morse.pathLength c 0 1) := by
      rw [← h0, ← h1]
      exact sInf_le ⟨c, 0, 1, hc, hcN, rfl, rfl, rfl⟩
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this
  set T : Set (Sub hN) := {y | Morse.riemDist (N := N) (incl hN p) (incl hN y) ≠ ⊤} with hT
  have hopen : IsOpen T := isOpen_iff_mem_nhds.2 fun y hy => by
    filter_upwards [hloc y] with y' hy'
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hy, hy'⟩) (htri _ _ _)
  have hclosed : IsClosed T := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    filter_upwards [hloc y] with y' hy' hy'T
    refine hy (ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hy'T, ?_⟩)
      (htri _ (incl hN y') _))
    rw [Morse.riemDist_comm]
    exact hy'
  have hpT : p ∈ T := (hloc p).self_of_nhds
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨p, hpT⟩
  have : q ∈ T := by rw [huniv]; exact mem_univ _
  exact this

end Emb

open Bundle in
/-- B on embedded manifolds: `M = ↥N` with the induced metric (a special case of B, see
`B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], ∀ p q : Bridge.Sub hN,
    (∃ (pth : ℝ → Bridge.Sub hN) (a b : ℝ), a ≤ b ∧ IsPW (n := n) pth a b ∧ pth a = p ∧
      pth b = q) ∧
    0 ≤ rho (n := n) p q ∧ (rho (n := n) p q = 0 ↔ p = q) ∧ rho (n := n) p q = rho (n := n) q p ∧
    ∀ r : Bridge.Sub hN, rho (n := n) p r ≤ rho (n := n) p q + rho (n := n) q r

/-- `B_emb` is a special case of B. -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ => hB n (Bridge.Sub hN)

/-- The part of A about slice submanifolds that B covers: the triangle inequality and positivity
(`riemDist p q = 0 ⇒ p = q`). -/
def A_metric : Prop :=
  (∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {N : Set V}, Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N → ∀ p q r : V,
      Morse.riemDist (N := N) p r ≤ Morse.riemDist (N := N) p q + Morse.riemDist (N := N) q r) ∧
    type_of% @Morse.eq_of_riemDist_eq_zero.{0,0,0}

theorem A_to_A_metric : A → A_metric := fun hA => ⟨fun _ p q r => hA.2.1 p q r, hA.2.2.2⟩

/-- **A's triangle inequality and positivity give B on embedded manifolds.** -/
theorem A_metric_to_B_emb : A_metric → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ p q
  have htri : ∀ x y z : V, Morse.riemDist (N := N) x z ≤
      Morse.riemDist (N := N) x y + Morse.riemDist (N := N) y z := hA.1 hN
  have hfin : ∀ x y : Bridge.Sub hN,
      Morse.riemDist (N := N) (Bridge.incl hN x) (Bridge.incl hN y) ≠ ⊤ :=
    fun x y => Emb.fin htri x y
  have hrho : ∀ x y : Bridge.Sub hN, ENNReal.ofReal (rho (n := n) x y) =
      Morse.riemDist (N := N) (Bridge.incl hN x) (Bridge.incl hN y) := fun x y => by
    rw [show rho (n := n) x y = BridgePrelude.rho (n := n) x y from rfl, Bridge.rho_eq,
      ENNReal.ofReal_toReal (hfin x y)]
  have hnn : ∀ x y : Bridge.Sub hN, 0 ≤ rho (n := n) x y := fun x y => by
    rw [show rho (n := n) x y = BridgePrelude.rho (n := n) x y from rfl, Bridge.rho_eq]
    exact ENNReal.toReal_nonneg
  refine ⟨?_, hnn p q, ⟨fun h => ?_, fun h => ?_⟩, ?_, fun r => ?_⟩
  · obtain ⟨c, a, b, hc, hcN, ha, hb⟩ := Emb.exists_path_of_ne_top (hfin p q)
    refine ⟨Bridge.lift c p, a, b, hc.1, Bridge.isPW_lift hc hcN p, ?_, ?_⟩
    · apply Subtype.ext
      exact (Bridge.incl_lift p (hcN a ⟨le_rfl, hc.1⟩)).trans ha
    · apply Subtype.ext
      exact (Bridge.incl_lift p (hcN b ⟨hc.1, le_rfl⟩)).trans hb
  · have h0 : Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q) = 0 := by
      rw [← hrho, h, ENNReal.ofReal_zero]
    exact hA.2 hN h0
  · subst h
    have h0 : Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN p) ≤
        ENNReal.ofReal (Morse.pathLength (fun _ => Bridge.incl hN p) 0 0) :=
      sInf_le ⟨fun _ => Bridge.incl hN p, 0, 0,
        Morse.IsPiecewiseSmooth.of_contDiffOn (s := univ) contDiffOn_const le_rfl (subset_univ _),
        fun _ _ => p.2, rfl, rfl, rfl⟩
    rw [Morse.pathLength, intervalIntegral.integral_same, ENNReal.ofReal_zero] at h0
    have := hrho p p
    rw [le_antisymm h0 bot_le] at this
    exact le_antisymm (ENNReal.ofReal_eq_zero.1 this) (hnn p p)
  · rw [show rho (n := n) p q = BridgePrelude.rho (n := n) p q from rfl,
      show rho (n := n) q p = BridgePrelude.rho (n := n) q p from rfl, Bridge.rho_eq,
      Bridge.rho_eq, Morse.riemDist_comm]
  · have h := htri (Bridge.incl hN p) (Bridge.incl hN q) (Bridge.incl hN r)
    rw [← hrho, ← hrho, ← hrho, ← ENNReal.ofReal_add (hnn p q) (hnn q r)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (hnn p q) (hnn q r))).1 h

/-- **A implies B on embedded manifolds** (A's triangle inequality and positivity). -/
theorem A_to_B_emb : A → B_emb := fun hA => A_metric_to_B_emb (A_to_A_metric hA)

/-- **B on embedded manifolds gives the triangle inequality and positivity** for every slice
submanifold (via the component of the first point). -/
theorem B_emb_to_A_metric : B_emb → A_metric := by
  intro hB
  -- the component of `x ∈ N`, its distance, and the finiteness from B's joining paths
  have key : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
      {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
      {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (x : N),
      ∃ C : Set V, C ⊆ N ∧ (x : V) ∈ C ∧
        (∀ (c : ℝ → V) (a b : ℝ), Morse.IsPiecewiseSmooth c a b → (∀ t ∈ Icc a b, c t ∈ N) →
          c a ∈ C → ∀ t ∈ Icc a b, c t ∈ C) ∧
        ∃ hC : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn (finrank ℝ Z)) W C,
        ConnectedSpace (Bridge.Sub hC) ∧ ∀ y z : Bridge.Sub hC,
          Morse.riemDist (N := C) (Bridge.incl hC y) (Bridge.incl hC z) =
            ENNReal.ofReal (rho (n := finrank ℝ Z) y z) ∧ 0 ≤ rho (n := finrank ℝ Z) y z := by
    intro V _ _ _ Z _ _ _ W _ _ _ N hN x
    obtain ⟨O, hO, hxO, hC, hconn, -, hS⟩ := Emb.reduce hN x
    have hpath : ∀ (c : ℝ → V) (a b : ℝ), Morse.IsPiecewiseSmooth c a b →
        (∀ t ∈ Icc a b, c t ∈ N) → c a ∈ N ∩ O → ∀ t ∈ Icc a b, c t ∈ N ∩ O := by
      intro c a b hc hcN ha
      have h := hS (c '' Icc a b) (by rintro _ ⟨t, ht, rfl⟩; exact hcN t ht)
        (isPreconnected_Icc.image c hc.2.1) (c a) ⟨a, ⟨le_rfl, hc.1⟩, rfl⟩ ha
      exact fun t ht => h ⟨t, ht, rfl⟩
    refine ⟨N ∩ O, inter_subset_left, ⟨x.2, hxO⟩, hpath, hC, hconn, fun y z => ?_⟩
    have hfin : Morse.riemDist (N := N ∩ O) (Bridge.incl hC y) (Bridge.incl hC z) ≠ ⊤ := by
      obtain ⟨⟨pth, a, b, hab, hpw, ha, hb⟩, -⟩ := hB V W _ (N ∩ O) hC y z
      have hpw' : BridgePrelude.IsPW (n := finrank ℝ Z) pth a b := hpw
      have hc := Bridge.isPiecewiseSmooth_of_isPW hpw'
      have : Morse.riemDist (N := N ∩ O) (Bridge.incl hC y) (Bridge.incl hC z) ≤
          ENNReal.ofReal (Morse.pathLength (Bridge.incl hC ∘ pth) a b) := by
        rw [← ha, ← hb]
        exact sInf_le ⟨_, a, b, hc, fun t _ => (pth t).2, rfl, rfl, rfl⟩
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this
    have e : rho (n := finrank ℝ Z) y z =
        (Morse.riemDist (N := N ∩ O) (Bridge.incl hC y) (Bridge.incl hC z)).toReal :=
      Bridge.rho_eq y z
    rw [e, ENNReal.ofReal_toReal hfin]
    exact ⟨rfl, ENNReal.toReal_nonneg⟩
  refine ⟨?_, ?_⟩
  · intro V _ _ _ Z _ _ _ W _ _ _ N hN p q r
    by_cases hpq : Morse.riemDist (N := N) p q = ⊤
    · rw [hpq, top_add]; exact le_top
    by_cases hqr : Morse.riemDist (N := N) q r = ⊤
    · rw [hqr, add_top]; exact le_top
    obtain ⟨c, a, b, hc, hcN, ha, -⟩ := Emb.exists_path_of_ne_top hpq
    have hpN : p ∈ N := ha ▸ hcN a ⟨le_rfl, hc.1⟩
    obtain ⟨C, hCN, hpC, hpath, hC, hconn, hd⟩ := key hN ⟨p, hpN⟩
    have hqC : q ∈ C := Emb.mem_of_riemDist_ne_top hpath hpC hpq
    have hrC : r ∈ C := Emb.mem_of_riemDist_ne_top hpath hqC hqr
    let p' : Bridge.Sub hC := (⟨p, hpC⟩ : ↥C)
    let q' : Bridge.Sub hC := (⟨q, hqC⟩ : ↥C)
    let r' : Bridge.Sub hC := (⟨r, hrC⟩ : ↥C)
    rw [← Emb.riemDist_eq_of_closed hCN hpath hpC, ← Emb.riemDist_eq_of_closed hCN hpath hpC,
      ← Emb.riemDist_eq_of_closed hCN hpath hqC]
    have h1 := hd p' r'
    have h2 := hd p' q'
    have h3 := hd q' r'
    change Morse.riemDist (N := C) (Bridge.incl hC p') (Bridge.incl hC r') ≤
      Morse.riemDist (N := C) (Bridge.incl hC p') (Bridge.incl hC q') +
        Morse.riemDist (N := C) (Bridge.incl hC q') (Bridge.incl hC r')
    rw [h1.1, h2.1, h3.1, ← ENNReal.ofReal_add h2.2 h3.2]
    exact ENNReal.ofReal_le_ofReal ((hB V W _ C hC p' q').2.2.2.2 r')
  · intro V _ _ _ Z _ _ _ W _ _ _ N hN p q h
    obtain ⟨C, hCN, hpC, hpath, hC, hconn, hd⟩ := key hN p
    have hqC : (q : V) ∈ C := Emb.mem_of_riemDist_ne_top hpath hpC (by rw [h]; exact ENNReal.zero_ne_top)
    let p' : Bridge.Sub hC := (⟨p, hpC⟩ : ↥C)
    let q' : Bridge.Sub hC := (⟨q, hqC⟩ : ↥C)
    have h0 : rho (n := finrank ℝ Z) p' q' = 0 := by
      have e := (hd p' q').1
      rw [show Morse.riemDist (N := C) (Bridge.incl hC p') (Bridge.incl hC q') =
        Morse.riemDist (N := N) p q from Emb.riemDist_eq_of_closed hCN hpath hpC q, h] at e
      exact le_antisymm (ENNReal.ofReal_eq_zero.1 e.symm) (hd p' q').2
    have := ((hB V W _ C hC p' q').2.2.1).1 h0
    exact Subtype.ext (show (p : V) = q from congrArg (fun z : Bridge.Sub hC => Bridge.incl hC z) this)

/-- On embedded manifolds, B is exactly A's triangle inequality and positivity. -/
theorem B_emb_iff_A_metric : B_emb ↔ A_metric := ⟨B_emb_to_A_metric, A_metric_to_B_emb⟩

/-- **B implies A's triangle inequality (for slice submanifolds) and positivity.** -/
theorem B_to_A_metric : B → A_metric := fun hB => B_emb_to_A_metric (B_to_B_emb hB)

#rt_check RoundTrip.V7_18.A_metric_to_B_emb [Morse.riemDist_le_pathLength,
  Morse.riemDist_triangle, Morse.NormalCoord.ofReal_le_riemDist, Morse.eq_of_riemDist_eq_zero]
#rt_check RoundTrip.V7_18.A_to_B_emb [Morse.riemDist_le_pathLength,
  Morse.riemDist_triangle, Morse.NormalCoord.ofReal_le_riemDist, Morse.eq_of_riemDist_eq_zero]
#rt_check RoundTrip.V7_18.B_to_A_metric [Morse.riemDist_le_pathLength,
  Morse.riemDist_triangle, Morse.NormalCoord.ofReal_le_riemDist, Morse.eq_of_riemDist_eq_zero]
#rt_overlap RoundTrip.V7_18.B_to_A_metric [Morse.riemDist_le_pathLength,
  Morse.riemDist_triangle, Morse.NormalCoord.ofReal_le_riemDist, Morse.eq_of_riemDist_eq_zero]

end RoundTrip.V7_18
