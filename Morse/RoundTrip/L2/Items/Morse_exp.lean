import Morse
import RoundTrip.L2.Blind.Morse_exp

/-! Layer-2 check of `Morse.exp` against the blind textbook definition: equal for every slice
submanifold `N` and all `q v : V` (including the junk value `q` off the domain).

The project's geodesics from `q` with velocity `v` live on an open interval `(-δ, 1 + δ)`
(`Morse.IsGeodesicFrom`); the blind ones on the closed interval `[0, 1]`. A blind geodesic on
`[0, 1]` extends to an open interval (`extend_closed`, copied from `RoundTrip/Items/V7_20.lean`,
built on the uniform local flow `Morse.exists_localFlow_exp`), and a project geodesic restricts to
`[0, 1]`; so the two domains agree, and on it both values are `γ(1)` by uniqueness of geodesics
(`Morse.IsGeodesicFrom.exp_eq`). Off the domain both are `q`. -/

namespace RoundTrip.L2.Morse_exp

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

/-- Blind geodesics only see the values on `s`. -/
theorem isGeo_congr {γ g : ℝ → V} {s : Set ℝ} (h : EqOn γ g s) (hg : IsGeo N g s) :
    IsGeo N γ s := by
  have hd : EqOn (derivWithin γ s) (derivWithin g s) s := fun t ht => derivWithin_congr h (h ht)
  refine ⟨hg.1.congr h, fun t ht => (h ht).symm ▸ hg.2.1 ht, fun t ht w hw => ?_⟩
  rw [derivWithin_congr hd (hd ht), h ht] at *
  exact hg.2.2 t ht w hw

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W]
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-- A geodesic on `(a, b)` which is smooth up to `b` continues past `b` (copied from
`RoundTrip/Items/V7_20.lean`, with the local flow `Morse.exists_localFlow_exp` inlined). -/
theorem extend_right {f : ℝ → V} {a b : ℝ} (hab : a < b)
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
  obtain ⟨U, hUo, hbU, τ, hτ, Φ, -, hloc⟩ :=
    Morse.exists_localFlow_exp hN ⟨f b, hb⟩ (R := M + 1) (by linarith)
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
  obtain ⟨hge, hd0, -⟩ := hloc y hs₀U w hw hwR
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

/-- **A geodesic smooth on a closed interval extends to an open one** (copied from
`RoundTrip/Items/V7_20.lean`). -/
theorem extend_closed {f : ℝ → V} {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f (Icc a b)) (hgeo : Morse.IsGeodesicOn hN f (Ioo a b))
    (ha : f a ∈ N) (hb : f b ∈ N) :
    ∃ ε > 0, ∃ g : ℝ → V, Morse.IsGeodesicOn hN g (Ioo (a - ε) (b + ε)) ∧ EqOn g f (Icc a b) := by
  obtain ⟨c₁, hc₁, ε₁, hε₁, h₁, hh₁, he₁⟩ := extend_right hab hf hgeo hb
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
    extend_right hab' hf' hgeo' (by simpa using ha)
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

/-- A blind geodesic on `[a, b]` (`a < b`) is the restriction of a project geodesic on an open
interval containing `[a, b]`. -/
theorem exists_extension {γ : ℝ → V} {a b : ℝ} (hab : a < b) (h : IsGeo N γ (Icc a b)) :
    ∃ ε > 0, ∃ g : ℝ → V, Morse.IsGeodesicOn hN g (Ioo (a - ε) (b + ε)) ∧
      EqOn g γ (Icc a b) :=
  extend_closed hab h.1 (isGeodesicOn_of_isGeo hN h isOpen_Ioo Ioo_subset_Icc_self)
    (h.2.1 ⟨le_rfl, hab.le⟩) (h.2.1 ⟨hab.le, le_rfl⟩)

/-- From a blind geodesic on `[0, 1]` to a project `IsGeodesicFrom`, equal on `[0, 1]`. -/
theorem isGeodesicFrom_of_isGeoFrom {γ : ℝ → V} {q v : V} (h : IsGeoFrom N q v γ) :
    ∃ g : ℝ → V, Morse.IsGeodesicFrom hN g q v ∧ EqOn g γ (Icc 0 1) := by
  obtain ⟨ε, hε, g, hg, hgγ⟩ := exists_extension (hN := hN) zero_lt_one h.1
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  refine ⟨g, ⟨ε, hε, by simpa using hg, (hgγ h0).trans h.2.1, ?_⟩, hgγ⟩
  have hd : HasDerivWithinAt g v (Icc 0 1) 0 :=
    h.2.2.congr (fun t ht => hgγ ht) (hgγ h0)
  exact (uniqueDiffOn_Icc zero_lt_one 0 h0).eq_deriv _
    (hg.hasDerivAt (by constructor <;> linarith)).hasDerivWithinAt hd

/-- From a project `IsGeodesicFrom` to a blind geodesic on `[0, 1]`. -/
theorem isGeoFrom_of_isGeodesicFrom {γ : ℝ → V} {q v : V} (h : Morse.IsGeodesicFrom hN γ q v) :
    IsGeoFrom N q v γ := by
  obtain ⟨δ, hδ, hg, h0, h0'⟩ := h
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-δ) (1 + δ) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨isGeo_of_isGeodesicOn hN hg (uniqueDiffOn_Icc zero_lt_one) hsub, h0, ?_⟩
  rw [← h0']
  exact (hg.hasDerivAt (hsub ⟨le_rfl, zero_le_one⟩)).hasDerivWithinAt

theorem exists_isGeoFrom_iff {q v : V} :
    (∃ γ, IsGeoFrom N q v γ) ↔ ((q, v) ∈ Morse.expDom hN) :=
  ⟨fun ⟨_, h⟩ => let ⟨g, hg, _⟩ := isGeodesicFrom_of_isGeoFrom (hN := hN) h; ⟨g, hg⟩,
    fun ⟨g, hg⟩ => ⟨g, isGeoFrom_of_isGeodesicFrom hg⟩⟩

/-- The value at `1` of any blind geodesic on `[0, 1]` is the project's `exp`. -/
theorem exp_eq_of_isGeoFrom {γ : ℝ → V} {q v : V} (h : IsGeoFrom N q v γ) :
    Morse.exp hN q v = γ 1 := by
  obtain ⟨g, hg, hgγ⟩ := isGeodesicFrom_of_isGeoFrom (hN := hN) h
  rw [hg.exp_eq, hgγ ⟨zero_le_one, le_rfl⟩]

end GeoGlue

/-- **Agreement**: the project's `exp` is the blind `exp` (everywhere). -/
theorem agree {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {N : Set V}
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (q v : V) :
    Morse.exp hN q v = T hN q v := by
  unfold T
  split_ifs with h
  · exact exp_eq_of_isGeoFrom h.choose_spec
  · have h' : ¬ ∃ γ, Morse.IsGeodesicFrom hN γ q v := fun ⟨g, hg⟩ =>
      h ⟨g, isGeoFrom_of_isGeodesicFrom hg⟩
    rw [Morse.exp, dif_neg h']

end RoundTrip.L2.Morse_exp
