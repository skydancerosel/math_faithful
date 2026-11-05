import Morse
import RoundTrip.L2.Blind.Morse_expDom

/-! Layer-2 check of `Morse.expDom` against the blind textbook definition: equal for every slice
submanifold `N`. Both ask for a geodesic on an open interval containing `[0, 1]` with
`γ(0) = q`, `γ'(0) = v`: the project's interval is `(-δ, 1 + δ)`, the blind one any `(a, b)`
with `a < 0 < 1 < b` (shrink to `δ = min (-a) (b - 1)`); the blind conditions `q ∈ N`,
`v ∈ T_qN` follow from the geodesic (`Morse.IsGeodesicOn.deriv_mem`, and the project tangent space
is the span of velocities, `tsp_eq`, copied from `Morse_tangentSubspace`). -/

namespace RoundTrip.L2.Morse_expDom

open Set Filter Topology
open scoped ContDiff Manifold

/-! ### The tangent space (copied from `RoundTrip/L2/Items/Morse_tangentSubspace.lean`) -/

section TangentSpan

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}

theorem tsp_exists_curve (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) {q : N} (hq : q.1 ∈ σ.φ.source)
    (a : Z) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V, ContDiffOn ℝ ∞ γ (Set.Ioo (-ε) ε) ∧
      Set.MapsTo γ (Set.Ioo (-ε) ε) N ∧ γ 0 = q ∧
      HasDerivAt γ (fderiv ℝ (Morse.sliceParam σ) (σ.φ q).1 a) 0 := by
  set z₀ : Z := (σ.φ q).1 with hz₀
  have hz₀mem : z₀ ∈ σ.toChart.target := Morse.toChart_apply_mem_target σ hq
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (Morse.isOpen_toChart_target σ) z₀ hz₀mem
  set ε : ℝ := r / (‖a‖ + 1) with hε
  have hε0 : 0 < ε := div_pos hr (by positivity)
  have hmaps : Set.MapsTo (fun t : ℝ => z₀ + t • a) (Set.Ioo (-ε) ε) σ.toChart.target := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have ht' : |t| < ε := abs_lt.2 ht
    have h1 : |t| * (‖a‖ + 1) < r := by
      rw [hε, lt_div_iff₀ (by positivity)] at ht'
      exact ht'
    nlinarith [abs_nonneg t, norm_nonneg a]
  refine ⟨ε, hε0, fun t => Morse.sliceParam σ (z₀ + t • a), ?_, ?_, ?_, ?_⟩
  · exact (Morse.contDiffOn_sliceParam σ).comp
      (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn hmaps
  · exact fun t ht => Morse.sliceParam_mem σ (hmaps ht)
  · simpa using Morse.sliceParam_toChart σ hq
  · have hd : HasDerivAt (fun t : ℝ => z₀ + t • a) a 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add z₀
    have hx : HasFDerivAt (Morse.sliceParam σ) (fderiv ℝ (Morse.sliceParam σ) z₀)
        (z₀ + (0:ℝ) • a) := by
      rw [zero_smul, add_zero]
      exact ((Morse.contDiffAt_sliceParam σ hz₀mem).differentiableAt (by simp)).hasFDerivAt
    exact hx.comp_hasDerivAt 0 hd

theorem tsp_mem_of_velocity (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (q : N) {v : V}
    (hv : ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V, ContDiffOn ℝ ∞ γ (Set.Ioo (-ε) ε) ∧
      Set.MapsTo γ (Set.Ioo (-ε) ε) N ∧ γ 0 = q ∧ HasDerivAt γ v 0) :
    v ∈ Morse.tangentSubspace hN q := by
  obtain ⟨ε, hε, γ, -, hγN, hγ0, hγv⟩ := hv
  obtain ⟨σ, hσ⟩ := hN q.1 q.2
  rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ]
  have hφ : DifferentiableAt ℝ σ.φ q := by
    have h1 := σ.φ.contMDiffOn_toFun
    rw [contMDiffOn_iff_contDiffOn] at h1
    exact (h1.contDiffAt (σ.φ.open_source.mem_nhds hσ)).differentiableAt (by simp)
  set c : ℝ → Z := fun t => (σ.φ (γ t)).1 with hc_def
  have hc : HasDerivAt c (fderiv ℝ (fun x => (σ.φ x).1) q v) 0 := by
    have hfst : DifferentiableAt ℝ (fun x => (σ.φ x).1) (γ 0) := by
      rw [hγ0]
      exact differentiableAt_fst.comp _ hφ
    exact hγ0 ▸ hfst.hasFDerivAt.comp_hasDerivAt 0 hγv
  have hc0 : c 0 = (σ.φ q).1 := by simp [hc_def, hγ0]
  have hev : γ =ᶠ[𝓝 0] Morse.sliceParam σ ∘ c := by
    have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ σ.φ.source :=
      hγv.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact σ.φ.open_source.mem_nhds hσ)
    have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Set.Ioo (-ε) ε :=
      Ioo_mem_nhds (by linarith) hε
    filter_upwards [h1, h2] with t ht1 ht2
    have hs : (σ.φ (γ t)).2 = 0 := (σ.slice _ ht1).1 (hγN ht2)
    have : ((σ.φ (γ t)).1, (0 : W)) = σ.φ (γ t) := Prod.ext rfl hs.symm
    simp only [Function.comp_apply, hc_def, Morse.sliceParam]
    rw [this, σ.φ.invFun_apply ht1]
  have hx : HasFDerivAt (Morse.sliceParam σ) (fderiv ℝ (Morse.sliceParam σ) (σ.φ q).1) (c 0) := by
    rw [hc0]
    exact ((Morse.contDiffAt_sliceParam σ (Morse.toChart_apply_mem_target σ hσ)).differentiableAt
      (by simp)).hasFDerivAt
  have hγ' := (hx.comp_hasDerivAt 0 hc).congr_of_eventuallyEq hev
  exact ⟨_, (hγv.unique hγ').symm⟩

/-- The project tangent space is the blind one (span of velocities). -/
theorem tsp_eq (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (q : N) :
    Morse.tangentSubspace hN q = tangentSpace N (q : V) := by
  apply le_antisymm
  · obtain ⟨σ, hσ⟩ := hN q.1 q.2
    rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ]
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span (tsp_exists_curve σ hσ a)
  · exact Submodule.span_le.2 fun v hv => tsp_mem_of_velocity hN q hv

end TangentSpan
/-! ### Blind geodesics vs project geodesics -/

section GeoGlue

set_option linter.unusedSectionVars false

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}

/-- A blind geodesic on `s` is a project geodesic on every open `s' ⊆ s`. -/
theorem isGeodesicOn_of_isGeo (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ : ℝ → V}
    {s s' : Set ℝ} (h : IsGeo N γ s) (hs' : IsOpen s') (hss : s' ⊆ s) :
    Morse.IsGeodesicOn hN γ s' := by
  have hd1 : ∀ u ∈ s', derivWithin γ s u = deriv γ u := fun u hu =>
    derivWithin_of_mem_nhds (mem_of_superset (hs'.mem_nhds hu) hss)
  have hdd : ∀ t ∈ s', derivWithin (derivWithin γ s) s t = deriv (deriv γ) t := fun t ht => by
    rw [derivWithin_of_mem_nhds (mem_of_superset (hs'.mem_nhds ht) hss)]
    exact Filter.EventuallyEq.deriv_eq (eventually_of_mem (hs'.mem_nhds ht) hd1)
  refine ⟨hs', fun t ht => h.2.1 (hss ht), h.1.mono hss, fun t ht => ?_⟩
  rw [tsp_eq hN]
  refine (Submodule.mem_orthogonal' _ _).2 fun w hw => ?_
  rw [← hdd t ht]
  exact h.2.2 t (hss ht) w hw

/-- A project geodesic on `s` is a blind geodesic on every `s' ⊆ s` with unique derivatives. -/
theorem isGeo_of_isGeodesicOn (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ : ℝ → V}
    {s s' : Set ℝ} (h : Morse.IsGeodesicOn hN γ s) (hs' : UniqueDiffOn ℝ s') (hss : s' ⊆ s) :
    IsGeo N γ s' := by
  have hd : EqOn (derivWithin γ s') (deriv γ) s' := fun t ht =>
    (h.hasDerivAt (hss ht)).hasDerivWithinAt.derivWithin (hs' t ht)
  have hdd : ∀ t ∈ s', derivWithin (derivWithin γ s') s' t = deriv (deriv γ) t := fun t ht => by
    rw [derivWithin_congr hd (hd ht)]
    exact (h.hasDerivAt_deriv (hss ht)).hasDerivWithinAt.derivWithin (hs' t ht)
  refine ⟨h.contDiffOn.mono hss, fun t ht => h.mem t (hss ht), fun t ht w hw => ?_⟩
  rw [hdd t ht]
  have h1 := h.normal t (hss ht)
  rw [tsp_eq hN] at h1
  exact (Submodule.mem_orthogonal' _ _).1 h1 w hw

/-- On an open set the two notions agree. -/
theorem isGeo_iff_of_isOpen (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ : ℝ → V}
    {s : Set ℝ} (hs : IsOpen s) : IsGeo N γ s ↔ Morse.IsGeodesicOn hN γ s :=
  ⟨fun h => isGeodesicOn_of_isGeo hN h hs subset_rfl,
    fun h => isGeo_of_isGeodesicOn hN h hs.uniqueDiffOn subset_rfl⟩

end GeoGlue

/-- **Agreement**: the project's domain of `exp` is the blind one. -/
theorem agree {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {N : Set V}
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) :
    Morse.expDom hN = T hN := by
  ext ⟨q, v⟩
  constructor
  · rintro ⟨γ, δ, hδ, hg, h0, h0'⟩
    have hm : (0 : ℝ) ∈ Ioo (-δ) (1 + δ) := ⟨by linarith, by linarith⟩
    have hq : q ∈ N := by simpa [h0] using hg.mem 0 hm
    have hv := hg.deriv_mem hm
    rw [tsp_eq hN] at hv
    refine ⟨hq, ?_, -δ, 1 + δ, by linarith, by linarith, γ,
      (isGeo_iff_of_isOpen hN isOpen_Ioo).2 hg, h0, ?_⟩
    · simpa [h0, h0'] using hv
    · rw [← h0']
      exact hg.hasDerivAt hm
  · rintro ⟨-, -, a, b, ha, hb, γ, hg, h0, hd⟩
    have hg' := (isGeo_iff_of_isOpen hN isOpen_Ioo).1 hg
    refine ⟨γ, min (-a) (b - 1), lt_min (by linarith) (by linarith),
      hg'.mono isOpen_Ioo fun t ht => ⟨?_, ?_⟩, h0, hd.deriv⟩
    · linarith [ht.1, min_le_left (-a) (b - 1)]
    · linarith [ht.2, min_le_right (-a) (b - 1)]

end RoundTrip.L2.Morse_expDom
