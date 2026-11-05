import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_17
import RoundTrip.Bridge

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold

namespace RoundTrip.V7_17

/-- The project's statement (universes instantiated at 0) being a geodesic on an open set is local; a minimizing unit-speed piecewise smooth path `c`
on `[0, ℓ]` in `N` coincides on each subinterval lying in a uniformly normal `O` with a geodesic;
Corollary 10.7: such `c` is a geodesic on `(0, ℓ)` (`IsGeodesicOn`, open interval), and extends to
a geodesic on `(-δ, ℓ + δ)`. (Unit speed is `‖c'‖ = 1` wherever `c` is differentiable.) -/
def A : Prop :=
  type_of% @Morse.isGeodesicOn_of_locally.{0,0,0} ∧
    type_of% @Morse.minimal_segment.{0,0,0} ∧
    type_of% @Morse.corollary_10_7.{0,0,0} ∧
    type_of% @Morse.corollary_10_7_extend.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.isGeodesicOn_of_locally,
    @Morse.minimal_segment,
    @Morse.corollary_10_7,
    @Morse.corollary_10_7_extend⟩

/-! ## The embedded special case

`B_emb` is B for `M = ↥N` (`RoundTrip.Bridge.Sub hN`, model `ℝⁿ`, connected) with the induced
metric and the induced Levi-Civita connection `Bridge.conn`. Through the Bridge's dictionary
(blind piecewise smooth paths and arc length = the project's `IsPiecewiseSmooth`/`pathLength`,
blind geodesics on `[0, ℓ]` = smooth curves with normal acceleration):
* `A_to_B_emb`: A's `corollary_10_7_extend` gives B_emb; the glue converts B's parametrization by
  arc length (`L(ω|[0,t]) = t`) into A's `‖c'‖ = 1` wherever `c` is differentiable
  (`Emb.norm_deriv_eq_one`, one-sided fundamental theorem of calculus on a smooth piece);
* `B_emb_to_A`: B_emb gives all of A, for every slice submanifold (any model, `N` not assumed
  connected): B is applied to the connected component of `c(0)`, re-modelled on `ℝᵐ`; the closed
  geodesic is extended past its ends by the project's `Morse.exists_initial_ray` (outside the
  item), and `isGeodesicOn_of_locally` (locality, no Riemannian content) is reproved.
So `B_emb ↔ A`, and with `B_to_B_emb`, **`B → A`** (`B_to_A`). -/

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

/-! ### Locality, extension past the ends, unit speed -/

section General

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- Being a geodesic is a local property (the project's proof of `isGeodesicOn_of_locally`). -/
theorem isGeodesicOn_of_locally' {γ : ℝ → V} {s : Set ℝ} (hs : IsOpen s)
    (h : ∀ t ∈ s, ∃ s' : Set ℝ, t ∈ s' ∧ s' ⊆ s ∧ Morse.IsGeodesicOn hN γ s') :
    Morse.IsGeodesicOn hN γ s := by
  choose s' hts' hs's hgeo using h
  refine ⟨hs, fun t ht => (hgeo t ht).mem t (hts' t ht), ?_, fun t ht => ?_⟩
  · refine contDiffOn_of_locally_contDiffOn fun t ht => ⟨s' t ht, (hgeo t ht).isOpen,
      hts' t ht, ?_⟩
    exact (hgeo t ht).contDiffOn.mono inter_subset_right
  · exact (hgeo t ht).normal t (hts' t ht)

/-! The extension of a geodesic past the ends of a closed interval, from `Items/V7_20.lean`
(with the locality lemma `isGeodesicOn_of_locally'` in place of the project's). -/

/-- Uniform local existence of geodesics (the content of `Morse.exists_localFlow_exp`, without
the continuity of the flow). -/
def LocalFlow (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) : Prop :=
  ∀ (x₀ : N) {R : ℝ}, 0 < R → ∃ U : Set V, IsOpen U ∧ (x₀ : V) ∈ U ∧ ∃ τ > 0,
    ∀ y : N, (y : V) ∈ U → ∀ w ∈ Morse.tangentSubspace hN y, ‖w‖ < R →
      Morse.IsGeodesicOn hN (fun t => Morse.exp hN y (t • w)) (Ioo (-τ) τ) ∧
      HasDerivAt (fun t : ℝ => Morse.exp hN y (t • w)) w 0

theorem localFlow_of (h : type_of% @Morse.exists_localFlow_exp.{0,0,0}) : LocalFlow hN := by
  intro x₀ R hR
  obtain ⟨U, hU, hx, τ, hτ, Φ, -, hΦ⟩ := h hN x₀ hR
  exact ⟨U, hU, hx, τ, hτ, fun y hy w hw hwR => ⟨(hΦ y hy w hw hwR).1, (hΦ y hy w hw hwR).2.1⟩⟩

/-- A geodesic on `(a, b)` which is smooth up to `b` continues past `b`. -/
theorem extend_right (hfl : LocalFlow hN) {f : ℝ → V} {a b : ℝ} (hab : a < b)
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
  obtain ⟨U, hUo, hbU, τ, hτ, hloc⟩ := hfl ⟨f b, hb⟩ (R := M + 1) (by linarith)
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
  obtain ⟨hge, hd0⟩ := hloc y hs₀U w hw hwR
  set h : ℝ → V := fun t => Morse.exp hN (f s₀) ((t - s₀) • w) with hh_def
  have hpre' : (fun t => 1 * t + -s₀) ⁻¹' Ioo (-τ) τ = Ioo (s₀ - τ) (s₀ + τ) := by
    ext t; simp only [mem_preimage, mem_Ioo]; constructor <;> rintro ⟨h1, h2⟩ <;>
      constructor <;> linarith
  have hhgeo : Morse.IsGeodesicOn hN h (Ioo (s₀ - τ) (s₀ + τ)) := by
    have := hge.comp_mul_add 1 (-s₀)
    rw [hpre'] at this
    refine this.congr fun t _ => ?_
    simp only [hh_def, one_mul, ← sub_eq_add_neg]
    rfl
  have hh0 : h s₀ = f s₀ := by
    simp only [hh_def, sub_self, zero_smul]
    exact Morse.exp_zero (hgeo.mem s₀ hs₀)
  have hh0' : deriv h s₀ = deriv f s₀ := by
    have h1 : HasDerivAt (fun t : ℝ => Morse.exp hN y (t • w)) w (s₀ - s₀) := by
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
theorem extend_closed (hfl : LocalFlow hN) {f : ℝ → V} {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f (Icc a b)) (hgeo : Morse.IsGeodesicOn hN f (Ioo a b))
    (ha : f a ∈ N) (hb : f b ∈ N) :
    ∃ ε > 0, ∃ g : ℝ → V, Morse.IsGeodesicOn hN g (Ioo (a - ε) (b + ε)) ∧ EqOn g f (Icc a b) := by
  obtain ⟨c₁, hc₁, ε₁, hε₁, h₁, hh₁, he₁⟩ := extend_right hfl hab hf hgeo hb
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
    extend_right hfl hab' hf' hgeo' (by simpa using ha)
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
  refine ⟨ε, hε, g, isGeodesicOn_of_locally' isOpen_Ioo fun t ht => ?_, hgf⟩
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


/-- A geodesic on `(0, ℓ)` which is smooth on `[0, ℓ]` extends to a geodesic on an open interval
`(-δ, ℓ + δ)` (`extend_closed`, from the uniform local existence `Morse.exists_localFlow_exp`). -/
theorem extend_of_closed {c : ℝ → V} {ℓ : ℝ} (hℓ : 0 < ℓ) (hcd : ContDiffOn ℝ ∞ c (Icc 0 ℓ))
    (hcN : ∀ t ∈ Icc 0 ℓ, c t ∈ N) (hgeo : Morse.IsGeodesicOn hN c (Ioo 0 ℓ)) :
    ∃ δ > 0, ∃ γ : ℝ → V, Morse.IsGeodesicOn hN γ (Ioo (-δ) (ℓ + δ)) ∧ EqOn γ c (Icc 0 ℓ) := by
  obtain ⟨ε, hε, g, hg, hgeq⟩ := extend_closed (localFlow_of Morse.exists_localFlow_exp) hℓ hcd hgeo
    (hcN 0 ⟨le_rfl, hℓ.le⟩) (hcN ℓ ⟨hℓ.le, le_rfl⟩)
  rw [zero_sub] at hg
  exact ⟨ε, hε, g, hg, hgeq⟩

end General

/-- **Parametrization by arc length gives unit speed**: if `L(c|[0,t]) = t` on `[0, ℓ]` for a
piecewise smooth `c`, then `‖c'(t₀)‖ = 1` wherever `c` is differentiable in `(0, ℓ)`. -/
theorem norm_deriv_eq_one {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {c : ℝ → V} {ℓ : ℝ} (hc : Morse.IsPiecewiseSmooth c 0 ℓ)
    (harc : ∀ t ∈ Icc 0 ℓ, Morse.pathLength c 0 t = t) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 ℓ)
    (hd : DifferentiableAt ℝ c t₀) : ‖deriv c t₀‖ = 1 := by
  borelize V
  obtain ⟨B, hB⟩ := hc.2.2
  classical
  set S : Finset ℝ := insert ℓ (B.filter (t₀ < ·)) with hS
  have hSne : S.Nonempty := ⟨ℓ, Finset.mem_insert_self _ _⟩
  set u := S.min' hSne with hu
  have hu_le : u ≤ ℓ := S.min'_le ℓ (Finset.mem_insert_self _ _)
  have hu_gt : t₀ < u := by
    have hm := S.min'_mem hSne
    rw [← hu] at hm
    simp only [hS, Finset.mem_insert, Finset.mem_filter] at hm
    rcases hm with h | h
    · rw [h]; exact ht₀.2
    · exact h.2
  have hsm : ContDiffOn ℝ ∞ c (Icc t₀ u) := hB t₀ u ht₀.1.le hu_gt hu_le fun x hx hxI => by
    have hxS : x ∈ S := Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hx, hxI.1⟩)
    exact absurd (S.min'_le x hxS) (not_le.2 hxI.2)
  have uI : UniqueDiffOn ℝ (Icc t₀ u) := uniqueDiffOn_Icc hu_gt
  have ht₀I : t₀ ∈ Icc t₀ u := ⟨le_rfl, hu_gt.le⟩
  set g := derivWithin c (Icc t₀ u) with hg_def
  have hg : ContinuousOn g (Icc t₀ u) := hsm.continuousOn_derivWithin uI (by simp)
  have hg0 : deriv c t₀ = g t₀ := (hd.hasDerivAt.hasDerivWithinAt.derivWithin (uI t₀ ht₀I)).symm
  have hgint : ∀ s ∈ Ioo t₀ u, deriv c s = g s := fun s hs =>
    (derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)).symm
  have hcont : ContinuousWithinAt (fun s => ‖deriv c s‖) (Ioi t₀) t₀ := by
    have h1 : ContinuousWithinAt (fun s => ‖g s‖) (Ioo t₀ u) t₀ :=
      ((hg t₀ ht₀I).mono Ioo_subset_Icc_self).norm
    have h2 : ContinuousWithinAt (fun s => ‖deriv c s‖) (Ioo t₀ u) t₀ :=
      h1.congr (fun s hs => by rw [hgint s hs]) (by rw [hg0])
    exact h2.mono_of_mem_nhdsWithin (Ioo_mem_nhdsGT hu_gt)
  have hint : IntervalIntegrable (fun s => ‖deriv c s‖) volume 0 t₀ :=
    (hc.isAdmissible.mono le_rfl ht₀.1.le ht₀.2.le).integrable
  have hmeas : StronglyMeasurableAtFilter (fun s => ‖deriv c s‖) (𝓝[Ioi t₀] t₀) :=
    (measurable_deriv c).norm.stronglyMeasurable.stronglyMeasurableAtFilter
  have hF := intervalIntegral.integral_hasDerivWithinAt_right hint (s := Ici t₀) (t := Ioi t₀)
    hmeas hcont
  have hid : HasDerivWithinAt (fun u => ∫ x in (0 : ℝ)..u, ‖deriv c x‖) 1 (Ici t₀) t₀ := by
    refine (hasDerivWithinAt_id t₀ (Ici t₀)).congr_of_eventuallyEq ?_
      (harc t₀ ⟨ht₀.1.le, ht₀.2.le⟩)
    filter_upwards [Ico_mem_nhdsGE ht₀.2] with s hs
    exact harc s ⟨ht₀.1.le.trans hs.1, hs.2.le⟩
  exact (uniqueDiffWithinAt_Ici t₀).eq_deriv _ hF hid

/-! ### The dictionary on `[a, b]` -/

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

/-- A curve in `N` agreeing on `[a, b]` with a project geodesic on an open set `s ⊇ [a, b]` is a
blind geodesic of the induced connection on `[a, b]`. -/
theorem isGeodesic_of_eqOn {γ : ℝ → V} {s : Set ℝ} (hγ : Morse.IsGeodesicOn hN γ s) {a b : ℝ}
    (hab : a < b) (hsub : Icc a b ⊆ s) {c : ℝ → Sub hN} (heq : EqOn (incl hN ∘ c) γ (Icc a b)) :
    IsGeodesic (conn (hN := hN)) c (Icc a b) := by
  set I := Icc a b
  have uI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have hd : EqOn (derivWithin (incl hN ∘ c) I) (deriv γ) I := fun t ht => by
    rw [derivWithin_congr heq (heq ht)]
    exact (hγ.hasDerivAt (hsub ht)).hasDerivWithinAt.derivWithin (uI t ht)
  have hdd : ∀ t ∈ I, derivWithin (derivWithin (incl hN ∘ c) I) I t = deriv (deriv γ) t :=
    fun t ht => by
      rw [derivWithin_congr hd (hd ht)]
      exact (hγ.hasDerivAt_deriv (hsub ht)).hasDerivWithinAt.derivWithin (uI t ht)
  have : BridgePrelude.IsGeodesic (conn (hN := hN)) c I := by
    refine isGeodesic_iff.2 ⟨⟨ordConnected_Icc, uI⟩, (hγ.contDiffOn.mono hsub).congr heq,
      fun t ht => ?_⟩
    rw [hdd t ht]
    have hct : incl hN (c t) = γ t := heq ht
    have hm : γ t ∈ N := hγ.mem t (hsub ht)
    have e : c t = (⟨γ t, hm⟩ : N) := Subtype.ext hct
    rw [e]
    exact hγ.tanProj_deriv_deriv (hsub ht)
  exact this

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], ∀ (pth : ℝ → Bridge.Sub hN) (ℓ : ℝ), 0 < ℓ →
    IsPW (n := n) pth 0 ℓ → (∀ t ∈ Set.Icc 0 ℓ, arcLen (n := n) pth 0 t = t) →
    (∀ (pth' : ℝ → Bridge.Sub hN) (a b : ℝ), a ≤ b → IsPW (n := n) pth' a b → pth' a = pth 0 →
      pth' b = pth ℓ → arcLen (n := n) pth 0 ℓ ≤ arcLen (n := n) pth' a b) →
    IsGeodesic Bridge.conn pth (Set.Icc 0 ℓ)

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds** (uses A's `corollary_10_7_extend`). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ pth ℓ hℓ hpw harc hmin
  set c : ℝ → V := Bridge.incl hN ∘ pth with hc_def
  have hpw' : BridgePrelude.IsPW (n := n) pth 0 ℓ := hpw
  have hc : Morse.IsPiecewiseSmooth c 0 ℓ := Bridge.isPiecewiseSmooth_of_isPW hpw'
  have harc' : ∀ t ∈ Icc 0 ℓ, Morse.pathLength c 0 t = t := fun t ht => by
    rw [← Bridge.arcLen_eq]
    exact harc t ht
  have hunit : ∀ t ∈ Ioo 0 ℓ, DifferentiableAt ℝ c t → ‖deriv c t‖ = 1 :=
    fun t ht hd => Emb.norm_deriv_eq_one hc harc' ht hd
  have hmin' : ∀ (c' : ℝ → V) (a b : ℝ), Morse.IsPiecewiseSmooth c' a b →
      (∀ t ∈ Icc a b, c' t ∈ N) → c' a = c 0 → c' b = c ℓ →
      Morse.pathLength c 0 ℓ ≤ Morse.pathLength c' a b := by
    intro c' a b hc' hc'N ha hb
    have hab := hc'.1
    have heq : EqOn (Bridge.incl hN ∘ Bridge.lift c' (pth 0)) c' (Icc a b) := fun t ht =>
      Bridge.incl_lift (pth 0) (hc'N t ht)
    have h := hmin (Bridge.lift c' (pth 0)) a b hab (Bridge.isPW_lift hc' hc'N (pth 0))
      (Subtype.ext ((heq ⟨le_rfl, hab⟩).trans ha)) (Subtype.ext ((heq ⟨hab, le_rfl⟩).trans hb))
    rw [show arcLen (n := n) pth 0 ℓ = BridgePrelude.arcLen (n := n) pth 0 ℓ from rfl,
      show arcLen (n := n) (Bridge.lift c' (pth 0)) a b =
        BridgePrelude.arcLen (n := n) (Bridge.lift c' (pth 0)) a b from rfl,
      Bridge.arcLen_eq, Bridge.arcLen_eq, Bridge.pathLength_congr hab heq] at h
    exact h
  obtain ⟨δ, hδ, γ, hγ, heq⟩ := hA.2.2.2 hN hc (fun t _ => (pth t).2) hunit hmin'
  exact Emb.isGeodesic_of_eqOn hγ hℓ (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    fun t ht => (heq ht).symm

/-- **B on embedded manifolds gives all of A**, for every slice submanifold: B is applied to the
connected component of `c(0)`. -/
theorem B_emb_to_A : B_emb → A := by
  intro hB
  have hext : type_of% @Morse.corollary_10_7_extend.{0,0,0} := by
    intro V _ _ _ Z _ _ _ W _ _ _ N hN c ℓ hc hcN hunit hmin
    rcases eq_or_lt_of_le hc.1 with hℓ | hℓ
    · subst hℓ
      refine ⟨1, one_pos, fun _ => c 0,
        Morse.isGeodesicOn_const hN (hcN 0 ⟨le_rfl, le_rfl⟩) isOpen_Ioo, fun t ht => ?_⟩
      simp only
      rw [le_antisymm ht.2 ht.1]
    have hc0 : c 0 ∈ N := hcN 0 ⟨le_rfl, hℓ.le⟩
    obtain ⟨O, hO, hqO, hC, hconn, hT, hS⟩ := Emb.reduce hN ⟨c 0, hc0⟩
    have hsub : N ∩ O ⊆ N := inter_subset_left
    have hcC : ∀ t ∈ Icc 0 ℓ, c t ∈ N ∩ O := by
      have h := hS (c '' Icc 0 ℓ) (by rintro _ ⟨t, ht, rfl⟩; exact hcN t ht)
        (isPreconnected_Icc.image c hc.2.1) (c 0) ⟨0, ⟨le_rfl, hℓ.le⟩, rfl⟩ ⟨hc0, hqO⟩
      exact fun t ht => h ⟨t, ht, rfl⟩
    let p₀ : Bridge.Sub hC := (⟨c 0, hc0, hqO⟩ : ↥(N ∩ O))
    set pth : ℝ → Bridge.Sub hC := Bridge.lift c p₀ with hpth
    have heq : EqOn (Bridge.incl hC ∘ pth) c (Icc 0 ℓ) := fun t ht =>
      Bridge.incl_lift p₀ (hcC t ht)
    have hpw : IsPW (n := finrank ℝ Z) pth 0 ℓ := Bridge.isPW_lift hc hcC p₀
    have harc : ∀ t ∈ Icc 0 ℓ, arcLen (n := finrank ℝ Z) pth 0 t = t := by
      intro t ht
      rw [show arcLen (n := finrank ℝ Z) pth 0 t = BridgePrelude.arcLen (n := finrank ℝ Z) pth 0 t
        from rfl, Bridge.arcLen_eq, Bridge.pathLength_congr ht.1
        (heq.mono (Icc_subset_Icc le_rfl ht.2)),
        Morse.pathLength_eq_of_norm_deriv (hc.isAdmissible.mono le_rfl ht.1 ht.2)
          (fun s hs hd => hunit s ⟨hs.1, hs.2.trans_le ht.2⟩ hd)]
      ring
    have hmin' : ∀ (pth' : ℝ → Bridge.Sub hC) (a b : ℝ), a ≤ b →
        IsPW (n := finrank ℝ Z) pth' a b → pth' a = pth 0 → pth' b = pth ℓ →
        arcLen (n := finrank ℝ Z) pth 0 ℓ ≤ arcLen (n := finrank ℝ Z) pth' a b := by
      intro pth' a b hab hpw' ha hb
      have hpw'' : BridgePrelude.IsPW (n := finrank ℝ Z) pth' a b := hpw'
      rw [show arcLen (n := finrank ℝ Z) pth 0 ℓ = BridgePrelude.arcLen (n := finrank ℝ Z) pth 0 ℓ
        from rfl, show arcLen (n := finrank ℝ Z) pth' a b =
          BridgePrelude.arcLen (n := finrank ℝ Z) pth' a b from rfl,
        Bridge.arcLen_eq, Bridge.arcLen_eq, Bridge.pathLength_congr hℓ.le heq]
      refine hmin _ a b (Bridge.isPiecewiseSmooth_of_isPW hpw'') (fun t _ => hsub (pth' t).2) ?_ ?_
      · show Bridge.incl hC (pth' a) = c 0
        rw [ha]
        exact heq ⟨le_rfl, hℓ.le⟩
      · show Bridge.incl hC (pth' b) = c ℓ
        rw [hb]
        exact heq ⟨hℓ.le, le_rfl⟩
    have hg := hB V W _ (N ∩ O) hC pth ℓ hℓ hpw harc hmin'
    have hg' : BridgePrelude.IsGeodesic (Bridge.conn (hN := hC)) pth (Icc 0 ℓ) := hg
    obtain ⟨-, hcd, -⟩ := Bridge.isGeodesic_iff.1 hg'
    have hgeo : Morse.IsGeodesicOn hN c (Ioo 0 ℓ) :=
      Emb.isGeodesicOn_mono hsub (fun x hx => hT x hx)
        ((Bridge.isGeodesicOn_Ioo hg').congr (heq.mono Ioo_subset_Icc_self))
    exact Emb.extend_of_closed hℓ (hcd.congr fun t ht => (heq ht).symm) hcN hgeo
  refine ⟨fun hN _ _ hs h => Emb.isGeodesicOn_of_locally' (hN := hN) hs h, ?_, ?_, hext⟩
  · intro V _ _ _ Z _ _ _ W _ _ _ N hN c ℓ hc hcN hunit hmin O ε h1 h3 α β hα0 hαβ hβℓ hinO
    obtain ⟨δ, hδ, γ, hγ, heq⟩ := hext hN hc hcN hunit hmin
    exact ⟨Ioo (-δ) (ℓ + δ), fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩, γ, hγ,
      heq.mono (Icc_subset_Icc hα0 hβℓ)⟩
  · intro V _ _ _ Z _ _ _ W _ _ _ N hN c ℓ hc hcN hunit hmin
    obtain ⟨δ, hδ, γ, hγ, heq⟩ := hext hN hc hcN hunit hmin
    exact (hγ.mono isOpen_Ioo fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩).congr
      (heq.mono Ioo_subset_Icc_self)

/-- On embedded manifolds, B is equivalent to A. -/
theorem B_emb_iff_A : B_emb ↔ A := ⟨B_emb_to_A, A_to_B_emb⟩

/-- **B implies A**: Milnor's abstract statement, specialized to (the components of) slice
submanifolds with the induced metric and connection, gives the project's theorems. -/
theorem B_to_A : B → A := fun hB => B_emb_to_A (B_to_B_emb hB)

#rt_check RoundTrip.V7_17.A_to_B_emb [Morse.isGeodesicOn_of_locally, Morse.minimal_segment,
  Morse.corollary_10_7, Morse.corollary_10_7_extend]
#rt_check RoundTrip.V7_17.B_to_A [Morse.isGeodesicOn_of_locally, Morse.minimal_segment,
  Morse.corollary_10_7, Morse.corollary_10_7_extend]
#rt_overlap RoundTrip.V7_17.B_to_A [Morse.isGeodesicOn_of_locally, Morse.minimal_segment,
  Morse.corollary_10_7, Morse.corollary_10_7_extend]

end RoundTrip.V7_17
