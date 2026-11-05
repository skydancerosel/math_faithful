import Morse
import RoundTrip.L2.Blind.Morse_conjLocus

/-! Layer-2 check of `Morse.conjLocus` against the blind textbook definition: equal for every slice
submanifold `N` and every `p : V`.

* Geodesics: the project asks for a curve `C^∞` on `[0, 1]` in `N` which is a geodesic on the open
  `(0, 1)`; the blind definition for a geodesic on the closed `[0, 1]` (derivatives within). A
  project one extends past its end points (`extend_closed`, copied from
  `RoundTrip/Items/V7_20.lean`), so it is a blind one; the converse is a restriction.
* Projections: the blind `P_x` (projection onto the span of velocities, `0` off `N`) is the
  project's `Morse.prj` (`P_eq`); so the blind `D/dt` is `Morse.covAlong`.
* Second fundamental form: the blind `II_x(a, b) = (1 − P_x)((dP_x a) b)` with `dP_x` the
  `fderivWithin` along `N` equals the project's `secondFundForm` (`D_a b`, normal for tangent
  `b`) on tangent vectors (`II_eq`): `fderivWithin` along `N` agrees with the derivative of the
  smooth ambient representative `Morse.projRep` on the tangent cone, which contains `T_xN`.
  The blind Gauss-equation curvature term is then the project's `R(V, J)V` (`Morse.inner_curvOp`).
* Jacobi equation: the project imposes `D²J + R(V, J)V = 0` on `(0, 1)`, the blind definition its
  pairing with every tangent `u` on `[0, 1]`. The expression is tangent and continuous on
  `[0, 1]` (`Morse.IsSmoothCurveIn.contDiffOn_curvAlong`), so the two agree (`isJacobi_iff`). -/

namespace RoundTrip.L2.Morse_conjLocus

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

section Conj

set_option linter.unusedSectionVars false

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {N : Set V}

theorem starProjection_congr {K K' : Submodule ℝ V} (h : K = K') [K.HasOrthogonalProjection]
    [K'.HasOrthogonalProjection] : K.starProjection = K'.starProjection := by
  subst h; rfl

theorem tangentSpace_eq_bot {x : V} (hx : x ∉ N) : tangentSpace N x = ⊥ := by
  rw [tangentSpace, Submodule.span_eq_bot]
  rintro v ⟨ε, hε, c, -, hcN, hc0, -⟩
  exact absurd (hc0 ▸ hcN ⟨by linarith, hε⟩) hx

/-- The blind projection is the project's `prj`. -/
theorem P_eq (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (x : V) :
    P N x = Morse.prj hN x := by
  by_cases hx : x ∈ N
  · rw [Morse.prj_of_mem hN hx, P, Morse.tanProj]
    exact starProjection_congr (tsp_eq hN ⟨x, hx⟩).symm
  · rw [Morse.prj_of_notMem hN hx, P, starProjection_congr (tangentSpace_eq_bot hx),
      Submodule.starProjection_bot]

/-- A velocity lies in the tangent cone. -/
theorem mem_tangentConeAt_of_velocity {x v : V} (h : IsVelocity N x v) :
    v ∈ tangentConeAt ℝ N x := by
  obtain ⟨ε, hε, c, -, hcN, hc0, hv⟩ := h
  have hs := (hasDerivAt_iff_tendsto_slope.1 hv).mono_left
    (nhdsWithin_mono _ (fun t (ht : 0 < t) => ne_of_gt ht))
  refine mem_tangentConeAt_of_seq (𝓝[>] (0 : ℝ)) (fun t => t⁻¹) (fun t => c t - x) ?_ ?_ ?_
  · have h1 : Tendsto (fun t => c t - x) (𝓝 0) (𝓝 (c 0 - x)) :=
      hv.continuousAt.tendsto.sub_const x
    rw [hc0, sub_self] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    rw [add_sub_cancel]
    exact hcN ⟨by linarith [ht.1], ht.2⟩
  · refine hs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t _
    rw [slope_def_module, hc0, sub_zero]

variable {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-- On tangent vectors, the derivative of `P` within `N` is the project's `dN P`. -/
theorem fderivWithin_P_apply {x : V} (hx : x ∈ N) {a : V}
    (ha : a ∈ Morse.tangentSubspace hN ⟨x, hx⟩) :
    fderivWithin ℝ (P N) N x a = Morse.dN hN (Morse.tanProj hN) ⟨x, hx⟩ a := by
  set q : N := ⟨x, hx⟩
  set σ := Morse.sliceAt hN q
  have hq : q.1 ∈ σ.φ.source := Morse.mem_sliceAt_source hN q
  have hd : HasFDerivAt (Morse.projRep σ) (fderiv ℝ (Morse.projRep σ) x) x :=
    ((Morse.contDiffAt_projRep σ hq).differentiableAt (by simp)).hasFDerivAt
  have hev : P N =ᶠ[𝓝[N] x] Morse.projRep σ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (σ.φ.open_source.mem_nhds hq)]
      with y hyN hyS
    rw [P_eq hN, Morse.prj_of_mem hN hyN]
    exact (Morse.projRep_eq hN σ (x := ⟨y, hyN⟩) hyS).symm
  have h1 : HasFDerivWithinAt (P N) (fderiv ℝ (Morse.projRep σ) x) N x :=
    hd.hasFDerivWithinAt.congr_of_eventuallyEq hev (by
      rw [P_eq hN, Morse.prj_of_mem hN hx]; exact (Morse.projRep_eq hN σ hq).symm)
  have h2 := h1.differentiableWithinAt.hasFDerivWithinAt
  have hcone : a ∈ tangentConeAt ℝ N x := by
    have ha' := ha
    rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hq] at ha'
    obtain ⟨a', rfl⟩ := ha'
    obtain ⟨ε, hε, c, hc, hcN, hc0, hcd⟩ := tsp_exists_curve σ (q := q) hq a'
    exact mem_tangentConeAt_of_velocity ⟨ε, hε, c, hc, hcN, hc0, hcd⟩
  rw [Morse.dN_tanProj_eq_fderiv hN σ hq ha]
  exact (h1.unique_on h2 hcone).symm

/-- The blind second fundamental form is the project's on tangent vectors. -/
theorem II_eq {x : V} (hx : x ∈ N) {a b : V} (ha : a ∈ Morse.tangentSubspace hN ⟨x, hx⟩)
    (hb : b ∈ Morse.tangentSubspace hN ⟨x, hx⟩) :
    II N x a b = Morse.secondFundForm hN ⟨x, hx⟩ a b := by
  have h := Morse.tanProj_secondFundForm hN ha hb
  rw [Morse.secondFundForm] at h ⊢
  rw [II, fderivWithin_P_apply hx ha, P_eq hN, Morse.prj_of_mem hN hx, h, sub_zero]

/-- The blind curvature term is the project's `⟨R(a, b)a, u⟩`. -/
theorem curv_eq {x : V} (hx : x ∈ N) {a b u : V} (ha : a ∈ Morse.tangentSubspace hN ⟨x, hx⟩)
    (hb : b ∈ Morse.tangentSubspace hN ⟨x, hx⟩) (hu : u ∈ Morse.tangentSubspace hN ⟨x, hx⟩) :
    inner ℝ (II N x a a) (II N x b u) - inner ℝ (II N x b a) (II N x a u) =
      inner ℝ (Morse.curvR hN x a b a) u := by
  rw [II_eq hx ha ha, II_eq hx hb hu, II_eq hx hb ha, II_eq hx ha hu, Morse.curvR_of_mem hN hx,
    Morse.inner_curvOp, real_inner_comm (Morse.secondFundForm hN ⟨x, hx⟩ b a)]

/-- **Jacobi fields agree** along any smooth curve in `N` (on `[0, 1]`). -/
theorem isJacobi_iff {γ : ℝ → V} (hc : Morse.IsSmoothCurveIn hN γ) {J : ℝ → V} :
    Morse.IsJacobiField hN γ J ↔ IsJacobi N γ J := by
  have hcovD : ∀ Y : ℝ → V, covD N γ Y = Morse.covAlong hN γ Y := fun Y => by
    funext t; simp only [covD, Morse.covAlong, P_eq hN]
  have htan : ∀ t (ht : t ∈ Icc (0 : ℝ) 1),
      (Morse.prj hN (γ t) (J t) = J t ↔ J t ∈ tangentSpace N (γ t)) := fun t ht => by
    rw [Morse.prj_eq_self_iff hN (hc.mem t ht), tsp_eq hN]
  set E : ℝ → V := fun t => Morse.covAlong hN γ (Morse.covAlong hN γ J) t +
    Morse.curvAlong hN γ t (J t) with hE
  have hEtan : ∀ t (ht : t ∈ Icc (0 : ℝ) 1),
      E t ∈ Morse.tangentSubspace hN ⟨γ t, hc.mem t ht⟩ := fun t ht =>
    Submodule.add_mem _ (Morse.prj_mem hN (hc.mem t ht) _)
      ((Morse.prj_eq_self_iff hN (hc.mem t ht)).1 (hc.prj_curvAlong ht _))
  have hblind : ∀ t (ht : t ∈ Icc (0 : ℝ) 1), Morse.prj hN (γ t) (J t) = J t →
      ((∀ u ∈ tangentSpace N (γ t), inner ℝ (covD N γ (covD N γ J) t) u
        + inner ℝ (II N (γ t) (vel γ t) (vel γ t)) (II N (γ t) (J t) u)
        - inner ℝ (II N (γ t) (J t) (vel γ t)) (II N (γ t) (vel γ t) u) = 0) ↔ E t = 0) := by
    intro t ht hJt
    have hx := hc.mem t ht
    have hV : vel γ t ∈ Morse.tangentSubspace hN ⟨γ t, hx⟩ :=
      (Morse.prj_eq_self_iff hN hx).1 (hc.velAlong_mem ht)
    have hJ' : J t ∈ Morse.tangentSubspace hN ⟨γ t, hx⟩ := (Morse.prj_eq_self_iff hN hx).1 hJt
    have key : ∀ u ∈ Morse.tangentSubspace hN ⟨γ t, hx⟩,
        inner ℝ (covD N γ (covD N γ J) t) u
          + inner ℝ (II N (γ t) (vel γ t) (vel γ t)) (II N (γ t) (J t) u)
          - inner ℝ (II N (γ t) (J t) (vel γ t)) (II N (γ t) (vel γ t) u) = inner ℝ (E t) u := by
      intro u hu
      rw [add_sub_assoc, curv_eq hx hV hJ' hu, hE, inner_add_left, hcovD, hcovD,
        Morse.curvAlong_apply hx, hJt]
      rfl
    rw [← tsp_eq hN ⟨γ t, hx⟩]
    constructor
    · intro h
      have := h (E t) (hEtan t ht)
      rw [key _ (hEtan t ht)] at this
      exact inner_self_eq_zero.1 this
    · intro h u hu
      rw [key u hu, h, inner_zero_left]
  have hjac : ∀ t (ht : t ∈ Ioo (0 : ℝ) 1), Morse.prj hN (γ t) (J t) = J t →
      Morse.jacobiExpr hN γ J t = E t := by
    intro t ht hJt
    have hnh : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hcov : ∀ X : ℝ → V, Morse.covD hN γ X =ᶠ[𝓝 t] Morse.covAlong hN γ X := fun X => by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      simp only [Morse.covD, Morse.covAlong, derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)]
    rw [Morse.jacobiExpr, hE]
    simp only
    congr 1
    · rw [Morse.covD, (hcov J).deriv_eq, Morse.covAlong, derivWithin_of_mem_nhds hnh]
    · rw [Morse.curvAlong_apply (hc.mem t (Ioo_subset_Icc_self ht)), hJt,
        hc.velAlong_eq ht]
  have hEcont : ContDiffOn ℝ ∞ J (Icc 0 1) → ContinuousOn E (Icc 0 1) := by
    intro hJ
    have hcov : ∀ X : ℝ → V, ContDiffOn ℝ ∞ X (Icc 0 1) →
        ContDiffOn ℝ ∞ (Morse.covAlong hN γ X) (Icc 0 1) := fun X hX =>
      hc.contDiffOn_prj.clm_apply (hX.derivWithin (uniqueDiffOn_Icc zero_lt_one) (by simp))
    exact ((hcov _ (hcov J hJ)).add (hc.contDiffOn_curvAlong.clm_apply hJ)).continuousOn
  constructor
  · rintro ⟨hJ, hT, hEq⟩
    have hE0 : EqOn E 0 (Icc 0 1) := by
      have h1 : EqOn E 0 (Ioo 0 1) := fun t ht => by
        rw [← hjac t ht (hT t (Ioo_subset_Icc_self ht))]; exact hEq t ht
      exact h1.of_subset_closure (hEcont hJ) continuousOn_const Ioo_subset_Icc_self
        (by rw [closure_Ioo zero_ne_one])
    exact ⟨hJ, fun t ht => (htan t ht).1 (hT t ht),
      fun t ht => (hblind t ht (hT t ht)).2 (hE0 ht)⟩
  · rintro ⟨hJ, hT, hEq⟩
    have hT' : ∀ t (ht : t ∈ Icc (0 : ℝ) 1), Morse.prj hN (γ t) (J t) = J t := fun t ht =>
      (htan t ht).2 (hT t ht)
    exact ⟨hJ, hT', fun t ht => by
      rw [hjac t ht (hT' t (Ioo_subset_Icc_self ht))]
      exact (hblind t (Ioo_subset_Icc_self ht) (hT' t (Ioo_subset_Icc_self ht))).1
        (hEq t (Ioo_subset_Icc_self ht))⟩

end Conj

/-- **Agreement**. -/
theorem agree {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {N : Set V}
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (p : V) :
    Morse.conjLocus hN p = T hN p := by
  ext q
  constructor
  · rintro ⟨γ, hc, hgeo, h0, h1, -, -, -, J, hJ, hJ0, hJ1, t, ht, hJt⟩
    obtain ⟨ε, hε, g, hg, hgγ⟩ := extend_closed (hN := hN) zero_lt_one hc.contDiffOn hgeo
      (hc.mem 0 ⟨le_rfl, zero_le_one⟩) (hc.mem 1 ⟨zero_le_one, le_rfl⟩)
    have hIsGeo : IsGeo N γ (Icc 0 1) := isGeo_congr (fun t ht => (hgγ ht).symm)
      (isGeo_of_isGeodesicOn hN hg (uniqueDiffOn_Icc zero_lt_one)
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩))
    exact ⟨γ, hIsGeo, h0, h1, J, (isJacobi_iff hc).1 hJ, hJ0, hJ1, t, ht, hJt⟩
  · rintro ⟨γ, hγ, h0, h1, J, hJ, hJ0, hJ1, t, ht, hJt⟩
    have hc : Morse.IsSmoothCurveIn hN γ := ⟨hγ.1, fun t ht => hγ.2.1 ht⟩
    have hgeo := isGeodesicOn_of_isGeo hN hγ isOpen_Ioo Ioo_subset_Icc_self
    exact ⟨γ, hc, hgeo, h0, h1, ⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩, zero_ne_one, J,
      (isJacobi_iff hc).2 hJ, hJ0, hJ1, t, ht, hJt⟩

end RoundTrip.L2.Morse_conjLocus
