import Morse
import RoundTrip.L2.Blind.Morse_IsUnbrokenGeodesic

/-! Layer-2 check of `Morse.IsUnbrokenGeodesic hN c` (`C^∞` on `[0, 1]`, and
`Morse.IsGeodesicOn hN c (Ioo 0 1)`: values in `N` and `c''(t) ⊥ T_{c(t)}N` for `t ∈ (0, 1)`)
against the blind textbook definition (`C^∞` on `[0, 1]`, values in `N` on `[0, 1]`, and
`c''(t) ⊥ T_{c(t)}N` for `t ∈ [0, 1]`, `c''` the second derivative within `[0, 1]`, `T_xN` the
span of the velocities of curves in `N`).

* `of_T`: the blind notion implies the project's (no hypothesis).
* `agree_of`: equal when `c 0, c 1 ∈ N` (Milnor: `c ∈ Ω`, so `c([0, 1]) ⊆ N`) in the
  finite-dimensional setting. At the end points the normality follows by continuity:
  `t ↦ P_{c(t)}(c''(t))` is continuous on `[0, 1]` and vanishes on `(0, 1)` (`normal_closed`).
  The tangent spaces agree by `tangentSpace_eq` (from the item `Morse_tangentSubspace`).
* `differ`: the project does not require `c 0, c 1 ∈ N`: for `N = (0, ∞) ⊆ ℝ` the path `c = id`
  is a project unbroken geodesic, not a blind one (`c 0 = 0 ∉ N`). Harmless: outside `Ω`. -/

namespace RoundTrip.L2.Morse_IsUnbrokenGeodesic

open Set
open scoped ContDiff

section TangentSpace

/-! The tangent space: velocities of curves in `N` versus `Morse.tangentSubspace` (copied from the
layer-2 item `Morse_tangentSubspace`). -/

open Filter Topology
open scoped Manifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}

/-- Every vector of the project tangent space is a velocity. -/
theorem exists_curve (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) {q : N} (hq : q.1 ∈ σ.φ.source)
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
    have hx : HasFDerivAt (Morse.sliceParam σ) (fderiv ℝ (Morse.sliceParam σ) z₀) (z₀ + (0:ℝ) • a) := by
      rw [zero_smul, add_zero]
      exact ((Morse.contDiffAt_sliceParam σ hz₀mem).differentiableAt (by simp)).hasFDerivAt
    exact hx.comp_hasDerivAt 0 hd

/-- Every velocity lies in the project tangent space. -/
theorem mem_of_velocity (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (q : N) {v : V}
    (hv : ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V, ContDiffOn ℝ ∞ γ (Set.Ioo (-ε) ε) ∧
      Set.MapsTo γ (Set.Ioo (-ε) ε) N ∧ γ 0 = q ∧ HasDerivAt γ v 0) :
    v ∈ Morse.tangentSubspace hN q := by
  obtain ⟨ε, hε, γ, -, hγN, hγ0, hγv⟩ := hv
  obtain ⟨σ, hσ⟩ := hN q.1 q.2
  rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ]
  -- `φ` is differentiable at `q`
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
  -- near `0`, `γ = x ∘ c`
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

end TangentSpace

/-- The blind tangent space at a point of `N` is the project's `Morse.tangentSubspace`. -/
theorem tangentSpace_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {N : Set V} (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) {x : V}
    (hx : x ∈ N) : tangentSpace N x = Morse.tangentSubspace hN ⟨x, hx⟩ := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun v hv => mem_of_velocity hN ⟨x, hx⟩ hv
  · obtain ⟨σ, hσ⟩ := hN x hx
    rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ (q := ⟨x, hx⟩) hσ]
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span (exists_curve σ (q := ⟨x, hx⟩) hσ a)

/-- Off `N` the blind tangent space is `0` (no curve in `N` passes through the point). -/
theorem tangentSpace_of_notMem {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {N : Set V} {x : V} (hx : x ∉ N) : tangentSpace N x = ⊥ := by
  rw [tangentSpace, Submodule.span_eq_bot]
  rintro v ⟨ε, hε, γ, -, hγN, hγ0, -⟩
  exact absurd (hγ0 ▸ hγN ⟨by linarith, hε⟩ : x ∈ N) hx

section Geodesic

open Filter Topology

/-- Inside the interval, the second derivative within `[s, s']` is the ordinary one. -/
theorem derivWithin2_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {c : ℝ → V}
    {s s' t : ℝ} (ht : t ∈ Ioo s s') :
    derivWithin (derivWithin c (Icc s s')) (Icc s s') t = deriv (deriv c) t := by
  have hev : derivWithin c (Icc s s') =ᶠ[𝓝 t] deriv c := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), hev.deriv_eq]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)

/-- The blind geodesic condition on `[s, s']` gives the project's on `(s, s')`. -/
theorem isGeodesicOn_of {c : ℝ → V} {s s' : ℝ} (hcd : ContDiffOn ℝ ∞ c (Icc s s'))
    (hmem : MapsTo c (Icc s s') N)
    (hnorm : ∀ t ∈ Icc s s',
      derivWithin (derivWithin c (Icc s s')) (Icc s s') t ∈ (tangentSpace N (c t))ᗮ) :
    Morse.IsGeodesicOn hN c (Ioo s s') where
  isOpen := isOpen_Ioo
  mem _ ht := hmem (Ioo_subset_Icc_self ht)
  contDiffOn := hcd.mono Ioo_subset_Icc_self
  normal t ht := by
    have h := hnorm t (Ioo_subset_Icc_self ht)
    rwa [derivWithin2_eq ht, tangentSpace_eq hN (hmem (Ioo_subset_Icc_self ht))] at h

/-- **The end points**: for `c` smooth on `[s, s']` with values in `N`, a geodesic on `(s, s')`
satisfies the blind condition on all of `[s, s']`: `t ↦ P_{c(t)}(c''(t))` is continuous on
`[s, s']` (`Morse.ContDiffOn.prj_comp`) and vanishes on `(s, s')`, hence on its closure. -/
theorem normal_closed [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] {c : ℝ → V} {s s' : ℝ}
    (hss : s < s') (hcd : ContDiffOn ℝ ∞ c (Icc s s')) (hmem : ∀ t ∈ Icc s s', c t ∈ N)
    (hgeo : Morse.IsGeodesicOn hN c (Ioo s s')) :
    ∀ t ∈ Icc s s',
      derivWithin (derivWithin c (Icc s s')) (Icc s s') t ∈ (tangentSpace N (c t))ᗮ := by
  have hu : UniqueDiffOn ℝ (Icc s s') := uniqueDiffOn_Icc hss
  have hc1 : ContDiffOn ℝ ∞ (derivWithin c (Icc s s')) (Icc s s') :=
    hcd.derivWithin hu (m := ∞) (by simp)
  have hc2 : ContinuousOn (derivWithin (derivWithin c (Icc s s')) (Icc s s')) (Icc s s') :=
    hc1.continuousOn_derivWithin hu (by simp)
  have hP : ContinuousOn (fun t => Morse.prj hN (c t)) (Icc s s') :=
    (Morse.ContDiffOn.prj_comp hN hcd hmem).continuousOn
  have hg : ContinuousOn
      (fun t => Morse.prj hN (c t) (derivWithin (derivWithin c (Icc s s')) (Icc s s') t))
      (Icc s s') := hP.clm_apply hc2
  have hzero : EqOn
      (fun t => Morse.prj hN (c t) (derivWithin (derivWithin c (Icc s s')) (Icc s s') t)) 0
      (Ioo s s') := by
    intro t ht
    have h := hgeo.normal t ht
    simp only [Pi.zero_apply]
    rw [Morse.prj_of_mem hN (hmem t (Ioo_subset_Icc_self ht)), Morse.tanProj, derivWithin2_eq ht]
    exact (Submodule.starProjection_apply_eq_zero_iff _).2 h
  have hall := hzero.of_subset_closure hg continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hss.ne])
  intro t ht
  have h := hall ht
  simp only [Pi.zero_apply] at h
  rw [Morse.prj_of_mem hN (hmem t ht), Morse.tanProj] at h
  rw [tangentSpace_eq hN (hmem t ht)]
  exact (Submodule.starProjection_apply_eq_zero_iff _).1 h

end Geodesic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)

/-- The blind notion implies the project's. -/
theorem of_T {c : ℝ → V} (h : T hN c) : Morse.IsUnbrokenGeodesic hN c :=
  ⟨h.1, isGeodesicOn_of hN h.1 h.2.1 h.2.2⟩

/-- **Agreement** when the end points lie in `N` (in particular on `Ω`). -/
theorem agree_of [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] {c : ℝ → V} (h0 : c 0 ∈ N)
    (h1 : c 1 ∈ N) : Morse.IsUnbrokenGeodesic hN c ↔ T hN c := by
  refine ⟨fun ⟨hcd, hgeo⟩ => ?_, of_T hN⟩
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ N := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | h0'
    · exact h0
    rcases eq_or_lt_of_le ht.2 with rfl | h1'
    · exact h1
    exact hgeo.mem t ⟨h0', h1'⟩
  exact ⟨hcd, fun t ht => hmem t ht, normal_closed hN zero_lt_one hcd hmem hgeo⟩

/-- **Difference off `Ω`**: `N = (0, ∞) ⊆ ℝ` (an open set, a slice submanifold), `c = id`. -/
theorem differ :
    ∃ hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ ℝ) ℝ (Fin 0 → ℝ) (Ioi (0 : ℝ)),
      Morse.IsUnbrokenGeodesic hN (fun t => t) ∧ ¬ T hN (fun t => t) := by
  refine ⟨Morse.isSliceSubmanifold_of_isOpen (Fin 0 → ℝ) isOpen_Ioi, ⟨contDiffOn_id, ?_⟩, ?_⟩
  · exact ⟨isOpen_Ioo, fun t ht => ht.1, contDiffOn_id, fun t ht => by simp⟩
  · rintro ⟨-, h, -⟩
    have h0 : (0 : ℝ) ∈ Ioi (0 : ℝ) := h (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc 0 1)
    exact lt_irrefl _ (mem_Ioi.1 h0)

end RoundTrip.L2.Morse_IsUnbrokenGeodesic
