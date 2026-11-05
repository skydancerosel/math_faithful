import Morse
import RoundTrip.L2.Blind.Morse_pathTangent

/-! Layer-2 check of `Morse.pathTangent hN c` (`TΩ_c`: fields `X : ℝ → V`, `Morse.IsPiecewiseSmooth`
on `[0, 1]`, tangent `P_{c(t)} X(t) = X(t)` for `t ∈ [0, 1]`, `X 0 = 0 = X 1`) against the blind
textbook definition (the span of the fields piecewise smooth for a subdivision, with
`X t ∈ T_{c(t)}N` (span of velocities of curves in `N`) on `[0, 1]`, vanishing at `0`, `1`).

Equal for all `c` (no `c ∈ Ω` needed): the two piecewise-smoothness notions agree
(`isPiecewiseSmooth_iff`, from the item `Morse_IsPiecewiseSmooth`); `P_x v = v` iff
`v ∈ T_xN` at `x ∈ N` (`Morse.prj_eq_self_iff` and `tangentSpace_eq`, from the item
`Morse_tangentSubspace`), and off `N` both say `v = 0`. So the blind generating set is the
project's carrier, and its span is itself. -/

namespace RoundTrip.L2.Morse_pathTangent

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

theorem prj_eq_self_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (x v : V) :
    Morse.prj hN x v = v ↔ v ∈ tangentSpace N x := by
  by_cases hx : x ∈ N
  · rw [Morse.prj_eq_self_iff hN hx, tangentSpace_eq hN hx]
  · rw [Morse.prj_of_notMem hN hx, tangentSpace_of_notMem hx, Submodule.mem_bot]
    exact eq_comm

/-- **Agreement**: equal for all `c`. -/
theorem agree {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {N : Set V} (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    (c : ℝ → V) : Morse.pathTangent hN c = T hN c := by
  have hset : {X : ℝ → V | IsPiecewiseSmooth X 0 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, X t ∈ tangentSpace N (c t)) ∧ X 0 = 0 ∧ X 1 = 0} =
      (Morse.pathTangent hN c : Set (ℝ → V)) := by
    ext X
    simp only [mem_ofPred_eq, SetLike.mem_coe, Morse.mem_pathTangent, IsPiecewiseSmooth,
      ← isPiecewiseSmooth_iff, prj_eq_self_iff]
  rw [T, hset, Submodule.span_eq]

end RoundTrip.L2.Morse_pathTangent
