import Morse
import RoundTrip.Check
import RoundTrip.Blind.V10_3
import RoundTrip.Bridge

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V10_3

/-- The project's statement (universes instantiated at `0`), for a slice submanifold `N ⊆ V` with
the induced metric and `S = closedRiemBall N p r = {x ∈ N : ρ(p, x) ≤ r}`:
* `mem_closedRiemBall_of_energy_le` (any set `N`): a path of `Ω(N; p, q)` with `E ≤ c` stays in
  `S` for `r = √c`;
* `isCompact_closedRiemBall_of_isClosed`: `S` is compact if `N` is CLOSED in `V`;
* `corollary_10_8'`: for compact `K ⊆ N` there is `δ > 0` with `Morse.IsShortJoin hN δ y z` for
  `y, z ∈ K`, `ρ(y, z) < δ` (a unique joining vector of norm `< δ`, `ρ = ‖v‖`, depending smoothly on
  `(y, z)` locally) and a normal radius `≥ δ` at every point of `K`;
* `exists_brokenSetup`: if `p, q ∈ N`, `c > 0` and `S` is compact, there is `η > 0` such that every
  subdivision of mesh `< η` carries Milnor's choices (`Morse.BrokenSetup`: such a `δ` on `S` with
  `c (t_{i+1} − t_i) < δ²`). `closedRiemBall`, `BrokenSetup`, `brokenPaths` are vocabulary. -/
def A : Prop :=
  type_of% @Morse.mem_closedRiemBall_of_energy_le.{0} ∧
    type_of% @Morse.isCompact_closedRiemBall_of_isClosed.{0, 0, 0} ∧
    type_of% @Morse.corollary_10_8'.{0, 0, 0} ∧
    type_of% @Morse.exists_brokenSetup.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.mem_closedRiemBall_of_energy_le, @Morse.isCompact_closedRiemBall_of_isClosed,
    @Morse.corollary_10_8', @Morse.exists_brokenSetup⟩

/-! Neither `A → B` nor `B → A` is proved: B quantifies over abstract connected Hausdorff
`ℝⁿ`-manifolds with an arbitrary smooth metric and Levi-Civita connection, A over slice
submanifolds with the induced metric. See `V10_3.json`.

## The embedded special case: `A` gives `B` on `↥N`

The joins of B (blind geodesics on `[0, 1]`) are read as project `exp`-geodesics and the smooth
map `G` is assembled from the local smooth maps of `IsShortJoin` (dictionary copied from
`Items/V7_20.lean`, lemma `shortGood_of`); B's completeness `MetricComplete` is the project's
`IsRiemComplete` (copied from `Items/V7_29.lean`), and the compactness of `S` then comes from the
project's `isCompact_closedRiemBall_of_isRiemComplete` (Hopf–Rinow; NOT A's
`isCompact_closedRiemBall_of_isClosed`, whose hypothesis "`N` closed in `V`" is stronger). -/

namespace Emb

section Embedded

set_option linter.unusedSectionVars false

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}

section Extend

set_option linter.unusedSectionVars false

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

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

variable {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- A blind short join, read in `V`: its initial vector `u` is tangent, `exp_p u = q`, and its
length is `‖u‖`. -/
theorem joinsShort_data (hfl : LocalFlow hN) {δ : ℝ} {γ : ℝ → Bridge.Sub hN}
    {p q : Bridge.Sub hN} (h : JoinsShort (n := n) Bridge.conn δ γ p q) :
    derivWithin (Bridge.incl hN ∘ γ) (Icc 0 1) 0 ∈ Morse.tangentSubspace hN p ∧
      Morse.exp hN (Bridge.incl hN p) (derivWithin (Bridge.incl hN ∘ γ) (Icc 0 1) 0) =
        Bridge.incl hN q ∧
      arcLen (n := n) γ 0 1 = ‖derivWithin (Bridge.incl hN ∘ γ) (Icc 0 1) 0‖ := by
  obtain ⟨hγ, h0, h1, -⟩ := h
  obtain ⟨-, hc, -⟩ := Bridge.isGeodesic_iff.1 hγ
  obtain ⟨ε, hε, g, hg, hgeq⟩ := extend_closed hfl zero_lt_one hc
    (Bridge.isGeodesicOn_Ioo (c := γ) hγ) (γ 0).2 (γ 1).2
  have uI : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h0g : (0 : ℝ) ∈ Ioo (0 - ε) (1 + ε) := ⟨by linarith, by linarith⟩
  have hd : deriv g 0 = derivWithin (Bridge.incl hN ∘ γ) (Icc 0 1) 0 := by
    rw [← derivWithin_congr hgeq (hgeq h0I)]
    exact ((hg.hasDerivAt h0g).hasDerivWithinAt.derivWithin (uI 0 h0I)).symm
  have hfrom : Morse.IsGeodesicFrom hN g (Bridge.incl hN p)
      (derivWithin (Bridge.incl hN ∘ γ) (Icc 0 1) 0) := by
    refine ⟨ε, hε, ?_, ?_, hd⟩
    · convert hg using 2; ring
    · rw [hgeq h0I]; show Bridge.incl hN (γ 0) = _; rw [h0]
  refine ⟨?_, ?_, ?_⟩
  · have := Bridge.D_mem (γ 0) (vel (n := n) γ (Icc 0 1) 0)
    have e : Bridge.D hN (γ 0) (vel (n := n) γ (Icc 0 1) 0) =
        derivWithin (Bridge.incl hN ∘ γ) (Icc 0 1) 0 := Bridge.D_vel (c := γ) hγ.2.1 uI h0I
    rw [e, h0] at this
    exact this
  · rw [hfrom.exp_eq, hgeq h1I]; show Bridge.incl hN (γ 1) = _; rw [h1]
  · rw [show arcLen (n := n) γ 0 1 = Morse.pathLength (Bridge.incl hN ∘ γ) 0 1 from
      Bridge.arcLen_eq γ 0 1, ← Bridge.pathLength_congr zero_le_one hgeq,
      hg.pathLength_eq isPreconnected_Ioo zero_le_one
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩) h0g, hd]
    ring


/-! ### Distances, completeness (copied from `Items/V7_29.lean`) and paths -/

theorem riemDist_eq_ofReal_rho (hpre : IsPreconnected N) (p q : Bridge.Sub hN) :
    Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q) =
      ENNReal.ofReal (rho (n := n) p q) := by
  have e : rho (n := n) p q = RoundTrip.BridgePrelude.rho (n := n) p q := rfl
  rw [e, Bridge.rho_eq]
  exact (ENNReal.ofReal_toReal (Morse.riemDist_ne_top hN hpre p.2 q.2)).symm

theorem rho_nonneg (p q : Bridge.Sub hN) : 0 ≤ rho (n := n) p q := by
  have e : rho (n := n) p q = RoundTrip.BridgePrelude.rho (n := n) p q := rfl
  rw [e, Bridge.rho_eq]
  exact ENNReal.toReal_nonneg

theorem rho_lt_iff (hpre : IsPreconnected N) (p q : Bridge.Sub hN) {ε : ℝ} (hε : 0 < ε) :
    rho (n := n) p q < ε ↔
      Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q) < ENNReal.ofReal ε := by
  rw [riemDist_eq_ofReal_rho hpre, ENNReal.ofReal_lt_ofReal_iff hε]

theorem metricComplete_iff (hpre : IsPreconnected N) :
    MetricComplete n (Bridge.Sub hN) ↔ Morse.IsRiemComplete N := by
  constructor
  · intro h x hx hcau
    let x' : ℕ → Bridge.Sub hN := fun k => ⟨x k, hx k⟩
    obtain ⟨p, hp⟩ := h x' fun ε hε => by
      obtain ⟨n₀, hn₀⟩ := hcau ε hε
      exact ⟨n₀, fun m hm k hk => (rho_lt_iff hpre _ _ hε).2 (hn₀ m hm k hk)⟩
    refine ⟨Bridge.incl hN p, p.2, ?_⟩
    have ht : Tendsto (fun k => rho (n := n) (x' k) p) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨n₀, hn₀⟩ := hp ε hε
      refine ⟨n₀, fun m hm => ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (rho_nonneg _ _)]
      exact hn₀ m hm
    have := ENNReal.tendsto_ofReal ht
    rw [ENNReal.ofReal_zero] at this
    refine this.congr fun k => ?_
    exact (riemDist_eq_ofReal_rho hpre (x' k) p).symm
  · intro h x hcau
    obtain ⟨y, hy, hlim⟩ := h (fun k => Bridge.incl hN (x k)) (fun k => (x k).2) fun ε hε => by
      obtain ⟨n₀, hn₀⟩ := hcau ε hε
      exact ⟨n₀, fun m hm k hk => (rho_lt_iff hpre _ _ hε).1 (hn₀ m hm k hk)⟩
    refine ⟨⟨y, hy⟩, fun ε hε => ?_⟩
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
      (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε)))
    exact ⟨n₀, fun m hm => (rho_lt_iff hpre _ _ hε).2 (hn₀ m hm)⟩

/-- A blind path of `Ω(↥N; p, q)` is, in `V`, a project path of `Ω(N; p, q)`. -/
theorem mem_pathSpace {p q : Bridge.Sub hN} {w : ℝ → Bridge.Sub hN}
    (hw : InOmega (n := n) p q w) :
    Bridge.incl hN ∘ w ∈ Morse.pathSpace N (Bridge.incl hN p) (Bridge.incl hN q) :=
  ⟨Bridge.isPiecewiseSmooth_of_isPW hw.1, fun t _ => (w t).2, congrArg (Bridge.incl hN) hw.2.1,
    congrArg (Bridge.incl hN) hw.2.2⟩

/-- Milnor's ball `S` in `↥N` is the project's `closedRiemBall` (for connected `N`). -/
theorem image_ball_eq (hpre : IsPreconnected N) (p : Bridge.Sub hN) {r : ℝ} (hr : 0 ≤ r) :
    Bridge.incl hN '' {x : Bridge.Sub hN | rho (n := n) p x ≤ r} =
      Morse.closedRiemBall N (Bridge.incl hN p) r := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    rw [riemDist_eq_ofReal_rho hpre]
    exact ENNReal.ofReal_le_ofReal hx
  · rintro ⟨hy, hd⟩
    refine ⟨(⟨y, hy⟩ : N), ?_, rfl⟩
    show rho (n := n) p (⟨y, hy⟩ : N) ≤ r
    have := riemDist_eq_ofReal_rho (n := n) hpre p (⟨y, hy⟩ : N)
    have hd' : Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN (⟨y, hy⟩ : N)) ≤
        ENNReal.ofReal r := hd
    rw [this] at hd'
    exact (ENNReal.ofReal_le_ofReal_iff hr).1 hd'

/-! ### Short joins (adapted from `Items/V7_20.lean`) -/

/-- **`IsShortJoin` on a set gives B's `ShortGood`** (blind unique short geodesics with a smooth
initial-velocity map), for connected `N`. -/
theorem shortGood_of (hconn : IsPreconnected N) (K : Set (Bridge.Sub hN)) {δ : ℝ} (hδ : 0 < δ)
    (hSJ : ∀ (y z : N), (y : V) ∈ Bridge.incl hN '' K → (z : V) ∈ Bridge.incl hN '' K →
      Morse.riemDist (N := N) y z < ENNReal.ofReal δ → Morse.IsShortJoin hN δ y z) :
    ShortGood (n := n) (Bridge.conn (hN := hN)) K δ := by
  have hfl : LocalFlow hN := localFlow_of @Morse.exists_localFlow_exp
  have hfin : ∀ p q : Bridge.Sub hN,
      Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q) ≠ ⊤ :=
    fun p q => Morse.riemDist_ne_top hN hconn (p : N).2 (q : N).2
  have hrho : ∀ p q : Bridge.Sub hN, rho (n := n) p q =
      (Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q)).toReal :=
    fun p q => Bridge.rho_eq p q
  have hlt : ∀ p q : Bridge.Sub hN, rho (n := n) p q < δ →
      Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q) < ENNReal.ofReal δ := by
    intro p q h
    rw [← ENNReal.ofReal_toReal (hfin p q)]
    rw [hrho] at h
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).2 h
  set S : Set (Bridge.Sub hN × Bridge.Sub hN) :=
    {x | x.1 ∈ K ∧ x.2 ∈ K ∧ rho (n := n) x.1 x.2 < δ} with hS_def
  have hSJ' : ∀ x ∈ S, Morse.IsShortJoin hN δ x.1 x.2 := fun x hx =>
    hSJ x.1 x.2 (mem_image_of_mem _ hx.1) (mem_image_of_mem _ hx.2.1) (hlt _ _ hx.2.2)
  -- the joining vector lies in the domain of `exp`
  have hmem : ∀ (p q : Bridge.Sub hN) (v : V), Morse.exp hN (Bridge.incl hN p) v = Bridge.incl hN q →
      Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q) = ENNReal.ofReal ‖v‖ →
      (Bridge.incl hN p, v) ∈ Morse.expDom hN := by
    intro p q v hexp hρ
    by_contra hne
    have hjunk : Morse.exp hN (Bridge.incl hN p) v = Bridge.incl hN p := by
      rw [Morse.exp, dif_neg (show ¬ ∃ γ, Morse.IsGeodesicFrom hN γ (Bridge.incl hN p) v
        from hne)]
    have hpq : Bridge.incl hN q = Bridge.incl hN p := hexp.symm.trans hjunk
    rw [hpq, show Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN p) = 0 from
      Morse.riemDist_self (p : N).2] at hρ
    have hv0 : v = 0 := by
      have := hρ.symm
      rw [ENNReal.ofReal_eq_zero] at this
      exact norm_le_zero_iff.1 this
    exact hne (by rw [hv0]; exact ⟨_, Morse.isGeodesicFrom_const (p : N).2⟩)
  -- a short join exists
  have hjoin : ∀ (p q : Bridge.Sub hN) (v : V), v ∈ Morse.tangentSubspace hN p → ‖v‖ < δ →
      Morse.exp hN (Bridge.incl hN p) v = Bridge.incl hN q →
      Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q) = ENNReal.ofReal ‖v‖ →
      ∃ γ, JoinsShort (n := n) Bridge.conn δ γ p q ∧
        InitData (n := n) γ (Icc 0 1) p (Bridge.L hN p v) := by
    intro p q v hv hvδ hexp hρ
    obtain ⟨g, hg⟩ := hmem p q v hexp hρ
    have hg' : Morse.IsGeodesicFrom hN g (Bridge.incl hN p) (Bridge.D hN p (Bridge.L hN p v)) := by
      rw [Bridge.D_L hv]; exact hg
    obtain ⟨h1, h2, h3⟩ := Bridge.isGeodesic_lift_of_isGeodesicFrom hg'
    have hg0 := hg
    obtain ⟨δ', hδ', hgo, -, hgd⟩ := hg0
    have hlen : arcLen (n := n) (Bridge.lift g p) 0 1 = ‖v‖ := by
      rw [show arcLen (n := n) (Bridge.lift g p) 0 1 =
          Morse.pathLength (Bridge.incl hN ∘ Bridge.lift g p) 0 1 from Bridge.arcLen_eq _ _ _,
        Bridge.pathLength_congr zero_le_one
          (show EqOn (Bridge.incl hN ∘ Bridge.lift g p) g (Icc 0 1) from fun t ht => h3 t ht),
        hgo.pathLength_eq isPreconnected_Ioo zero_le_one
          (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
          (⟨by linarith, by linarith⟩ : (0 : ℝ) ∈ Ioo (-δ') (1 + δ')), hgd]
      ring
    refine ⟨Bridge.lift g p, ⟨h1, h2.1, ?_, by rw [hlen]; exact hvδ⟩, h2⟩
    apply Subtype.ext
    show Bridge.incl hN (Bridge.lift g p 1) = Bridge.incl hN q
    rw [h3 1 ⟨zero_le_one, le_rfl⟩, ← hexp]
    exact (Morse.IsGeodesicFrom.exp_eq hg).symm
  -- every short join has the joining vector as initial vector
  have hident : ∀ (p q : Bridge.Sub hN) (v : V), (∀ w ∈ Morse.tangentSubspace hN p, ‖w‖ < δ →
      Morse.exp hN (Bridge.incl hN p) w = Bridge.incl hN q → w = v) →
      ∀ γ', JoinsShort (n := n) Bridge.conn δ γ' p q →
        derivWithin (Bridge.incl hN ∘ γ') (Icc 0 1) 0 = v ∧ arcLen (n := n) γ' 0 1 = ‖v‖ := by
    intro p q v huniq γ' hγ'
    obtain ⟨hT, hE, hL⟩ := joinsShort_data hfl hγ'
    have hu := huniq _ hT (by rw [← hL]; exact hγ'.2.2.2) hE
    exact ⟨hu, hL.trans (by rw [hu])⟩
  refine ⟨fun p hp q hq hpq => ?_, ?_⟩
  · have hx : (p, q) ∈ S := ⟨hp, hq, hpq⟩
    obtain ⟨v, hv, hvδ, hexp, hρ, huniq, -⟩ := hSJ' (p, q) hx
    obtain ⟨γ₀, hγ₀, -⟩ := hjoin p q v hv hvδ hexp hρ
    have hγ₀d := (hident p q v huniq γ₀ hγ₀).1
    refine ⟨γ₀, hγ₀, fun γ' hγ' => ?_⟩
    · exact Bridge.eqOn_Icc_of_isGeodesic zero_lt_one hγ₀.1 hγ'.1 (hγ₀.2.1.trans hγ'.2.1.symm)
        (hγ₀d.trans (hident p q v huniq γ' hγ').1.symm)
  · classical
    let vch : Bridge.Sub hN × Bridge.Sub hN → V :=
      fun x => if hx : x ∈ S then (hSJ' x hx).choose else 0
    let G : Bridge.Sub hN × Bridge.Sub hN → TangentBundle 𝓘(ℝ, Rn n) (Bridge.Sub hN) :=
      fun x => ⟨x.1, Bridge.L hN x.1 (vch x)⟩
    have hvch : ∀ x (hx : x ∈ S), vch x = (hSJ' x hx).choose := fun x hx => dif_pos hx
    refine ⟨G, fun x hx => ?_, fun p hp q hq hpq => ?_⟩
    · -- smoothness within `S`, from the local smooth maps of `IsShortJoin`
      obtain ⟨-, -, -, -, -, O₂, hO₂, hxO, G', hG', -, hG'S⟩ := (hSJ' x hx).choose_spec
      set U₂ : Set (Bridge.Sub hN × Bridge.Sub hN) :=
        (fun z => (Bridge.incl hN z.1, Bridge.incl hN z.2)) ⁻¹' O₂ with hU₂
      have hpair : ContMDiff ((𝓘(ℝ, Rn n)).prod (𝓘(ℝ, Rn n))) 𝓘(ℝ, V × V) ∞
          (fun z : Bridge.Sub hN × Bridge.Sub hN => (Bridge.incl hN z.1, Bridge.incl hN z.2)) :=
        (Bridge.contMDiff_incl.comp contMDiff_fst).prodMk_space
          (Bridge.contMDiff_incl.comp contMDiff_snd)
      have hU₂o : IsOpen U₂ := hO₂.preimage hpair.continuous
      have hxU : x ∈ U₂ := hxO
      set F : Bridge.Sub hN × Bridge.Sub hN → TangentBundle 𝓘(ℝ, Rn n) (Bridge.Sub hN) :=
        fun z => ⟨z.1, Bridge.L hN z.1 (Bridge.P hN z.1
          (G' (Bridge.incl hN z.1, Bridge.incl hN z.2)))⟩ with hF_def
      have hGF : ∀ z ∈ S ∩ U₂, G z = F z := by
        rintro z ⟨hzS, hzU⟩
        obtain ⟨hGT, hGδ, hGexp⟩ := hG'S z.1 z.2 hzU (hlt _ _ hzS.2.2)
        obtain ⟨-, -, -, -, huniq_z, -⟩ := (hSJ' z hzS).choose_spec
        have heqv : G' (Bridge.incl hN z.1, Bridge.incl hN z.2) = (hSJ' z hzS).choose :=
          huniq_z _ hGT hGδ hGexp
        have hP : Bridge.P hN z.1 (G' (Bridge.incl hN z.1, Bridge.incl hN z.2)) =
            G' (Bridge.incl hN z.1, Bridge.incl hN z.2) := Morse.tanProj_eq_self hN hGT
        show (⟨z.1, Bridge.L hN z.1 (vch z)⟩ : TangentBundle 𝓘(ℝ, Rn n) (Bridge.Sub hN)) =
          ⟨z.1, Bridge.L hN z.1 (Bridge.P hN z.1 (G' (Bridge.incl hN z.1, Bridge.incl hN z.2)))⟩
        rw [hvch z hzS, hP, heqv]
      have hG'at : ContMDiffAt 𝓘(ℝ, V × V) 𝓘(ℝ, V) ∞ G' (Bridge.incl hN x.1, Bridge.incl hN x.2) :=
        (hG'.contDiffAt (hO₂.mem_nhds hxO)).contMDiffAt
      have hGz : ContMDiffAt ((𝓘(ℝ, Rn n)).prod (𝓘(ℝ, Rn n))) 𝓘(ℝ, V) ∞
          (fun z : Bridge.Sub hN × Bridge.Sub hN => G' (Bridge.incl hN z.1, Bridge.incl hN z.2)) x :=
        hG'at.comp x hpair.contMDiffAt
      have hPz : ContMDiffAt ((𝓘(ℝ, Rn n)).prod (𝓘(ℝ, Rn n))) 𝓘(ℝ, V →L[ℝ] V) ∞
          (fun z : Bridge.Sub hN × Bridge.Sub hN => Bridge.P hN z.1) x :=
        (Bridge.contMDiff_P.comp contMDiff_fst).contMDiffAt
      have hPG := hPz.clm_apply hGz
      have hF : ContMDiffWithinAt ((𝓘(ℝ, Rn n)).prod (𝓘(ℝ, Rn n))) (𝓘(ℝ, Rn n)).tangent ∞ F S x :=
        Bridge.contMDiffWithinAt_tangent_iff.2 ⟨contMDiff_fst.contMDiffAt.contMDiffWithinAt,
          hPG.contMDiffWithinAt.congr (fun z _ => Bridge.D_L_P z.1 _) (Bridge.D_L_P x.1 _)⟩
      refine hF.congr_of_eventuallyEq ?_ (hGF x ⟨hx, hxU⟩)
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hU₂o.mem_nhds hxU)]
        with z hzS hzU
      exact hGF z ⟨hzS, hzU⟩
    · have hx : (p, q) ∈ S := ⟨hp, hq, hpq⟩
      obtain ⟨hv, hvδ, hexp, hρ, -, -⟩ := (hSJ' (p, q) hx).choose_spec
      obtain ⟨γ₀, hγ₀, hinit⟩ := hjoin p q _ hv hvδ hexp hρ
      refine ⟨rfl, γ₀, hγ₀, ?_⟩
      have : (G (p, q)).snd = Bridge.L hN p (hSJ' (p, q) hx).choose := by
        show Bridge.L hN p (vch (p, q)) = _
        rw [hvch _ hx]
      rw [this]
      exact hinit.2


end Embedded

end Emb

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric) with the induced Levi-Civita
connection `Bridge.conn` (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    ∀ (p q : Bridge.Sub hN) (c : ℝ), 0 < c → (∃ w, w ∈ OmegaC (n := n) p q c) →
    (∀ w ∈ OmegaC (n := n) p q c, ∀ t ∈ Set.Icc (0:ℝ) 1, rho (n := n) p (w t) ≤ Real.sqrt c) ∧
    (MetricComplete n (Bridge.Sub hN) →
      IsCompact {x : Bridge.Sub hN | rho (n := n) p x ≤ Real.sqrt c}) ∧
    (MetricComplete n (Bridge.Sub hN) → ∃ ε : ℝ, 0 < ε ∧
      ShortGood (Bridge.conn (hN := hN)) {x : Bridge.Sub hN | rho (n := n) p x ≤ Real.sqrt c} ε ∧
      ∀ (k : ℕ) (t : ℕ → ℝ), t 0 = 0 → t k = 1 → (∀ i < k, t i < t (i + 1)) →
        (∀ i < k, t (i + 1) - t i < ε ^ 2 / c) →
        ∀ w ∈ OmegaC (n := n) p q c, ∀ i < k, arcLen (n := n) w (t i) (t (i + 1)) < ε) ∧
    (∀ (k : ℕ) (t : ℕ → ℝ), {w | w ∈ OmegaSub (Bridge.conn (hN := hN)) p q k t ∧
      Efun (n := n) w < c} = IntOmegaC (n := n) p q c ∩ OmegaSub (Bridge.conn (hN := hN)) p q k t)

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds**: (a) from A's `mem_closedRiemBall_of_energy_le`;
(b) compactness of `S` from `MetricComplete` via `IsRiemComplete` and the project's Hopf–Rinow
consequence `isCompact_closedRiemBall_of_isRiemComplete` (outside the item: A's own compactness
lemma needs `N` closed in `V`); (c) `ShortGood` from A's `corollary_10_8'` on `K = S`, and
`L² ≤ (t_{i+1} − t_i) E ≤ (t_{i+1} − t_i) c < ε²` (Schwarz, `Morse.pathLength_sq_le_energy`);
(d) is a set identity. -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ p q c hc _
  have hpre : IsPreconnected N :=
    isPreconnected_iff_preconnectedSpace.2 (inferInstance : PreconnectedSpace (Bridge.Sub hN))
  have hEw : ∀ w ∈ OmegaC (n := n) p q c,
      Morse.energy (Bridge.incl hN ∘ w) 0 1 ≤ c := fun w hw => by
    have e : Efun (n := n) w = Morse.energy (Bridge.incl hN ∘ w) 0 1 := Bridge.energy_eq w 0 1
    rw [← e]; exact hw.2
  -- (b), used in (c)
  have hcomp : MetricComplete n (Bridge.Sub hN) →
      IsCompact {x : Bridge.Sub hN | rho (n := n) p x ≤ Real.sqrt c} := by
    intro hmc
    have h := Morse.isCompact_closedRiemBall_of_isRiemComplete hN hpre
      ((Emb.metricComplete_iff hpre).1 hmc) (Bridge.incl hN p) (Real.sqrt c)
    rw [← Emb.image_ball_eq hpre p (Real.sqrt_nonneg c)] at h
    exact Topology.IsEmbedding.subtypeVal.isCompact_iff.2 h
  refine ⟨fun w hw t ht => ?_, hcomp, fun hmc => ?_, fun k t => ?_⟩
  · -- (a)
    have h := hA.1 (Emb.mem_pathSpace hw.1) (hEw w hw) ht
    have hb : Bridge.incl hN (w t) ∈
        Bridge.incl hN '' {x : Bridge.Sub hN | rho (n := n) p x ≤ Real.sqrt c} := by
      rw [Emb.image_ball_eq hpre p (Real.sqrt_nonneg c)]; exact h
    obtain ⟨x, hx, hxw⟩ := hb
    rw [show x = w t from Subtype.ext hxw] at hx
    exact hx
  · -- (c)
    set S := {x : Bridge.Sub hN | rho (n := n) p x ≤ Real.sqrt c}
    have hS := hcomp hmc
    obtain ⟨δ, hδ, hSJ, -⟩ := hA.2.2.1 hN (hS.image continuous_subtype_val)
      (by rintro _ ⟨x, -, rfl⟩; exact (x : N).2)
    refine ⟨δ, hδ, Emb.shortGood_of hpre S hδ hSJ, fun k t ht0 htk hlt hfine w hw i hi => ?_⟩
    have h0i : 0 ≤ t i := ht0 ▸ Bridge.le_of_strictSeq hlt (Nat.zero_le i) hi.le
    have hi1 : t (i + 1) ≤ 1 := htk ▸ Bridge.le_of_strictSeq hlt hi (le_refl k)
    have hii : t i < t (i + 1) := hlt i hi
    have hpw := (Emb.mem_pathSpace hw.1).1
    have hsub := hpw.mono h0i hii.le hi1
    have hL : arcLen (n := n) w (t i) (t (i + 1)) =
        Morse.pathLength (Bridge.incl hN ∘ w) (t i) (t (i + 1)) := Bridge.arcLen_eq w _ _
    have hS2 := Morse.pathLength_sq_le_energy hsub
    have hEle : Morse.energy (Bridge.incl hN ∘ w) (t i) (t (i + 1)) ≤
        Morse.energy (Bridge.incl hN ∘ w) 0 1 :=
      intervalIntegral.integral_mono_interval h0i hii.le hi1
        (Eventually.of_forall fun _ => sq_nonneg _) hpw.intervalIntegrable_norm_deriv_sq
    have hE := hEw w hw
    have hL0 : 0 ≤ Morse.pathLength (Bridge.incl hN ∘ w) (t i) (t (i + 1)) :=
      hsub.isAdmissible.pathLength_nonneg
    have hstep : (t (i + 1) - t i) * c < δ ^ 2 := by
      have := hfine i hi
      rwa [lt_div_iff₀ hc] at this
    have hsq : Morse.pathLength (Bridge.incl hN ∘ w) (t i) (t (i + 1)) ^ 2 < δ ^ 2 := by
      calc _ ≤ (t (i + 1) - t i) * Morse.energy (Bridge.incl hN ∘ w) (t i) (t (i + 1)) := hS2
        _ ≤ (t (i + 1) - t i) * c :=
          mul_le_mul_of_nonneg_left (hEle.trans hE) (sub_nonneg.2 hii.le)
        _ < δ ^ 2 := hstep
    rw [hL]
    exact lt_of_pow_lt_pow_left₀ 2 hδ.le hsq
  · -- (d)
    ext w
    constructor
    · rintro ⟨hw, hE⟩; exact ⟨⟨hw.1, hE⟩, hw⟩
    · rintro ⟨⟨-, hE⟩, hw⟩; exact ⟨hw, hE⟩

#rt_check RoundTrip.V10_3.A_to_B_emb [Morse.mem_closedRiemBall_of_energy_le, Morse.isCompact_closedRiemBall_of_isClosed, Morse.corollary_10_8', Morse.exists_brokenSetup]
#rt_overlap RoundTrip.V10_3.A_to_B_emb [Morse.mem_closedRiemBall_of_energy_le, Morse.isCompact_closedRiemBall_of_isClosed, Morse.corollary_10_8', Morse.exists_brokenSetup]

end RoundTrip.V10_3
