import Morse
import RoundTrip.L2.Blind.Morse_BrokenSetup_IsBroken

/-! Layer-2 check of `Morse.BrokenSetup.IsBroken B γ` (`γ` is a geodesic, `Morse.IsGeodesicOn`, on
each open segment `(t_i, t_{i+1})` of the subdivision of `B`) against the blind textbook definition
of `Ω(t₀, …, t_k)` (`γ ∈ Ω(N; p, q)`: continuous on `[0, 1]`, values in `N`, `γ 0 = p`,
`γ 1 = q`; and on each closed segment `[t_i, t_{i+1}]` `γ` is `C^∞` with acceleration (second
derivative within the segment) normal to `N`, the tangent space being the span of velocities).

* `agree_iff`: `B.IsBroken γ ∧ γ ∈ Ω(N; p, q) ↔ T B γ` for every `γ`: the project's predicate is
  Milnor's `Ω(t₀, …, t_k)` once intersected with `Ω` (as in Milnor's definition, which is a subset
  of `Ω`; the project always uses `IsBroken` together with `γ ∈ Ω` / energy conditions).
  Smoothness on the closed segments: at an end `t_i` of a segment, a piece of the piecewise smooth
  `γ` gives one-sided smoothness (`contDiffOn_closed`); normality at the ends by continuity of
  `t ↦ P_{γ(t)}(γ''(t))` (`normal_closed`); tangent spaces by `tangentSpace_eq` (from the item
  `Morse_tangentSubspace`); piecewise smoothness from the subdivision by `isPiecewiseSmooth_iff`
  (from the item `Morse_IsPiecewiseSmooth`).
* `agree_of`: hence `IsBroken ↔ T` for `γ ∈ Ω(N; p, q)`.
* `differ`: the project predicate alone constrains `γ` only on the open segments; for every setup
  `B` (with `V ≠ 0`) the path equal to `p` except `γ 0 = p + v` is `IsBroken` but not in the blind
  set. Harmless: outside `Ω`. -/

namespace RoundTrip.L2.Morse_BrokenSetup_IsBroken

open Set
open scoped ContDiff

/-- **Break sets versus subdivisions**, for any property `Q` of closed intervals inherited by
subintervals. -/
theorem pieces_iff {Q : ℝ → ℝ → Prop} (hQ : ∀ s₀ s₁ s s', s₀ ≤ s → s' ≤ s₁ → Q s₀ s₁ → Q s s')
    {a b : ℝ} :
    (a ≤ b ∧ ∃ B : Finset ℝ, ∀ s s', a ≤ s → s < s' → s' ≤ b → (∀ x ∈ B, x ∉ Ioo s s') →
        Q s s') ↔
      ∃ k : ℕ, ∃ t : Fin (k + 1) → ℝ, StrictMono t ∧ t 0 = a ∧ t (Fin.last k) = b ∧
        ∀ i : Fin k, Q (t i.castSucc) (t i.succ) := by
  classical
  constructor
  · rintro ⟨hab, B, hB⟩
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact ⟨0, fun _ => a, fun i j hij => absurd hij (by simp [Fin.lt_def]), rfl, rfl, fun i => i.elim0⟩
    set F : Finset ℝ := insert a (insert b (B.filter (· ∈ Ioo a b))) with hF
    have hFmem : ∀ x ∈ F, x ∈ Icc a b := by
      intro x hx
      simp only [hF, Finset.mem_insert, Finset.mem_filter] at hx
      rcases hx with rfl | rfl | ⟨-, hx⟩
      · exact ⟨le_rfl, hab⟩
      · exact ⟨hab, le_rfl⟩
      · exact Ioo_subset_Icc_self hx
    have haF : a ∈ F := Finset.mem_insert_self _ _
    have hbF : b ∈ F := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    obtain ⟨k, hk⟩ : ∃ k, F.card = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.2 ⟨a, haF⟩).ne'
    set e := F.orderEmbOfFin hk with he
    have hmem : ∀ j, e j ∈ F := fun j => Finset.orderEmbOfFin_mem F hk j
    refine ⟨k, e, e.strictMono, ?_, ?_, fun i => ?_⟩
    · have h1 := Finset.orderEmbOfFin_zero hk (Nat.succ_pos k)
      refine (h1.trans ?_)
      exact le_antisymm (F.min'_le a haF) (F.le_min' _ _ fun y hy => (hFmem y hy).1)
    · have h1 := Finset.orderEmbOfFin_last hk (Nat.succ_pos k)
      have h2 : (Fin.last k) = ⟨k + 1 - 1, by omega⟩ := Fin.ext (by simp)
      rw [h2, h1]
      exact le_antisymm (F.max'_le _ _ fun y hy => (hFmem y hy).2) (F.le_max' b hbF)
    · refine hB _ _ (hFmem _ (hmem _)).1 (e.strictMono Fin.castSucc_lt_succ)
        (hFmem _ (hmem _)).2 fun x hx hx' => ?_
      have hxF : x ∈ F := by
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hx, ?_⟩))
        exact ⟨(hFmem _ (hmem _)).1.trans_lt hx'.1, hx'.2.trans_le (hFmem _ (hmem _)).2⟩
      have : x ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact hxF
      obtain ⟨j, rfl⟩ := this
      have h1 := e.strictMono.lt_iff_lt.1 hx'.1
      have h2 := e.strictMono.lt_iff_lt.1 hx'.2
      rw [Fin.lt_def] at h1 h2
      simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
      omega
  · rintro ⟨k, t, ht, h0, hk, hQ'⟩
    have hab : a ≤ b := h0 ▸ hk ▸ ht.monotone (Fin.zero_le _)
    refine ⟨hab, Finset.univ.image t, fun s s' has hss' hs'b hB => ?_⟩
    set G := Finset.univ.filter (fun j => t j ≤ s) with hG
    have hGne : G.Nonempty := ⟨0, by simp [hG, h0, has]⟩
    set j := G.max' hGne
    have hjG : t j ≤ s := (Finset.mem_filter.1 (G.max'_mem hGne)).2
    have hjk : j.val < k := by
      by_contra hcon
      have : j = Fin.last k := Fin.ext (by have := j.isLt; simp; omega)
      rw [this, hk] at hjG
      linarith
    set i : Fin k := ⟨j.val, hjk⟩
    have hij : i.castSucc = j := Fin.ext rfl
    have hs1 : s < t i.succ := by
      by_contra hcon
      have hmemG : i.succ ∈ G := Finset.mem_filter.2 ⟨Finset.mem_univ _, not_lt.1 hcon⟩
      have := G.le_max' _ hmemG
      rw [Fin.le_def] at this
      simp [i, j] at this
    have hs2 : s' ≤ t i.succ := by
      by_contra hcon
      exact hB (t i.succ) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ⟨hs1, not_le.1 hcon⟩
    exact hQ _ _ _ _ (hij ▸ hjG) hs2 (hQ' i)

/-- The project's break-set formulation is the blind subdivision formulation. -/
theorem isPiecewiseSmooth_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ → V)
    (a b : ℝ) :
    Morse.IsPiecewiseSmooth c a b ↔
      ContinuousOn c (Icc a b) ∧
        ∃ k : ℕ, ∃ t : Fin (k + 1) → ℝ, StrictMono t ∧ t 0 = a ∧ t (Fin.last k) = b ∧
          ∀ i : Fin k, ContDiffOn ℝ ∞ c (Icc (t i.castSucc) (t i.succ)) := by
  have hQ : ∀ s₀ s₁ s s', s₀ ≤ s → s' ≤ s₁ → ContDiffOn ℝ ∞ c (Icc s₀ s₁) →
      ContDiffOn ℝ ∞ c (Icc s s') := fun _ _ _ _ h1 h2 h => h.mono (Icc_subset_Icc h1 h2)
  constructor
  · rintro ⟨hab, hcont, B, hB⟩
    exact ⟨hcont, (pieces_iff hQ).1 ⟨hab, B, hB⟩⟩
  · rintro ⟨hcont, h⟩
    obtain ⟨hab, B, hB⟩ := (pieces_iff hQ).2 h
    exact ⟨hab, hcont, B, hB⟩

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

section Closed

open Filter Topology

/-- A piecewise smooth path (break set `B'`) which is smooth on `(s, s')` is smooth on
`[s, s']`: at the ends, pieces of the path give the one-sided smoothness. -/
theorem contDiffOn_closed {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {γ : ℝ → V}
    {B' : Finset ℝ}
    (hB' : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ B', x ∉ Ioo s t) → ContDiffOn ℝ ∞ γ (Icc s t))
    {s s' : ℝ} (hs : 0 ≤ s) (hss : s < s') (hs' : s' ≤ 1) (hopen : ContDiffOn ℝ ∞ γ (Ioo s s')) :
    ContDiffOn ℝ ∞ γ (Icc s s') := by
  intro x hx
  by_cases hxs : x = s
  · subst hxs
    obtain ⟨r, hxr, hrs', hr⟩ := Morse.exists_piece_right B' hss
    have h := hB' x r hs hxr (hrs'.trans hs') hr x ⟨le_rfl, hxr.le⟩
    exact h.mono_of_mem_nhdsWithin (nhdsWithin_mono x Icc_subset_Ici_self (Icc_mem_nhdsGE hxr))
  by_cases hxs' : x = s'
  · subst hxs'
    obtain ⟨r, hsr, hrx, hr⟩ := Morse.exists_piece_left B' hss
    have h := hB' r x (hs.trans hsr) hrx hs' hr x ⟨hrx.le, le_rfl⟩
    exact h.mono_of_mem_nhdsWithin (nhdsWithin_mono x Icc_subset_Iic_self (Icc_mem_nhdsLE hrx))
  have hx' : x ∈ Ioo s s' := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxs), lt_of_le_of_ne hx.2 hxs'⟩
  exact (hopen.contDiffAt (Ioo_mem_nhds hx'.1 hx'.2)).contDiffWithinAt

end Closed

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N} {p q : V}
  {c : ℝ} {m : ℕ}

/-- **Agreement with `Ω(t₀, …, t_k)`**: the project predicate together with `γ ∈ Ω(N; p, q)` is
the blind one. -/
theorem agree_iff [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] (B : Morse.BrokenSetup hN p q c m)
    (γ : ℝ → V) : B.IsBroken γ ∧ γ ∈ Morse.pathSpace N p q ↔ T B γ := by
  constructor
  · rintro ⟨hP, hps, hmem, hγ0, hγ1⟩
    obtain ⟨-, hcont, B', hB'⟩ := hps
    refine ⟨hcont, fun t ht => hmem t ht, hγ0, hγ1, fun i => ?_⟩
    have hss : B.t i.castSucc < B.t i.succ := B.strictMono Fin.castSucc_lt_succ
    have hs0 : 0 ≤ B.t i.castSucc := B.toSubdivision.t_nonneg _
    have hs1 : B.t i.succ ≤ 1 := B.toSubdivision.t_le_one _
    have hcd := contDiffOn_closed hB' hs0 hss hs1 (hP i).contDiffOn
    have hmem' : ∀ t ∈ Icc (B.t i.castSucc) (B.t i.succ), γ t ∈ N :=
      fun t ht => hmem t ⟨hs0.trans ht.1, ht.2.trans hs1⟩
    exact ⟨hcd, normal_closed hN hss hcd hmem' (hP i)⟩
  · rintro ⟨hcont, hmem, hγ0, hγ1, hseg⟩
    refine ⟨fun i => isGeodesicOn_of hN (hseg i).1 (fun t ht => hmem
      ⟨(B.toSubdivision.t_nonneg _).trans ht.1, ht.2.trans (B.toSubdivision.t_le_one _)⟩)
      (hseg i).2, ?_, fun t ht => hmem ht, hγ0, hγ1⟩
    exact (isPiecewiseSmooth_iff γ 0 1).2 ⟨hcont, m + 1, B.t, B.strictMono, B.t_zero, B.t_last,
      fun i => (hseg i).1⟩

/-- **Agreement on `Ω`**. -/
theorem agree_of [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] (B : Morse.BrokenSetup hN p q c m)
    {γ : ℝ → V} (hγ : γ ∈ Morse.pathSpace N p q) : B.IsBroken γ ↔ T B γ :=
  ⟨fun h => (agree_iff B γ).1 ⟨h, hγ⟩, fun h => ((agree_iff B γ).2 h).1⟩

/-- **Difference off `Ω`**: for every setup `B` (and `V ≠ 0`), the path equal to `p` except at
`t = 0` is a geodesic on every open segment but not in `Ω(t₀, …, t_k)`. -/
theorem differ [Nontrivial V] (B : Morse.BrokenSetup hN p q c m) :
    ∃ γ : ℝ → V, B.IsBroken γ ∧ ¬ T B γ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨fun t => if t = 0 then p + v else p, fun i => ?_, fun h => ?_⟩
  · have hconst : Morse.IsGeodesicOn hN (fun _ => p) (Ioo (B.t i.castSucc) (B.t i.succ)) :=
      ⟨isOpen_Ioo, fun _ _ => B.mem_p, contDiffOn_const, fun t ht => by simp⟩
    refine hconst.congr fun t ht => ?_
    have : t ≠ 0 := (lt_of_le_of_lt (B.toSubdivision.t_nonneg _) ht.1).ne'
    simp [this]
  · have h0 := h.2.2.1
    simp at h0
    exact hv h0

end RoundTrip.L2.Morse_BrokenSetup_IsBroken
