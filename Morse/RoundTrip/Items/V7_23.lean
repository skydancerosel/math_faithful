import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.V7_23

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V7_23

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V` with
the induced metric: a geodesic on an open preconnected `s ∋ 0` is `t ↦ exp_{γ(0)}(t γ'(0))`; the
uniform local geodesic flow (near `x₀ ∈ N`, for speeds `< R`, `t ↦ exp_y(tw)` is a geodesic on a
uniform `(-τ, τ)`, with position and velocity continuous in `(y, w, t)`); continuation of
geodesics by gluing; the domain of `exp` is open in `TN` and `exp` is continuous on it; and
`exp_p` is continuous on `T_pN` when defined on all of it (one point `p`). -/
def A : Prop :=
  type_of% @Morse.IsGeodesicOn.exp_smul_eq.{0,0,0} ∧
    type_of% @Morse.exists_localFlow_exp.{0,0,0} ∧
    type_of% @Morse.isGeodesicOn_exp_smul_union.{0,0,0} ∧
    type_of% @Morse.eventually_mem_expDom_and_continuousWithinAt_exp.{0,0,0} ∧
    type_of% @Morse.continuousOn_exp.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.IsGeodesicOn.exp_smul_eq, @Morse.exists_localFlow_exp,
    @Morse.isGeodesicOn_exp_smul_union, @Morse.eventually_mem_expDom_and_continuousWithinAt_exp,
    @Morse.continuousOn_exp⟩

/-! ### Embedded special case

`B`'s third clause applied to a connected, geodesically complete slice submanifold `N ⊆ V` with
model `ℝⁿ`, made a Mathlib Riemannian manifold with its Levi-Civita connection by
`RoundTrip.Bridge` (`Bridge.Sub hN`, `Bridge.conn`), gives the last conjunct of `A`
(`continuousOn_exp`) for such `N`. `A`'s version needs `exp` defined on `T_pN` at the one point
`p` only; `B`'s needs geodesic completeness of all of `N`. -/

section Embedded

set_option linter.unusedSectionVars false

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}

theorem B_continuousOn_exp_embedded (hB : B) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    (hconn : IsPreconnected N) (hcomp : Morse.IsGeodesicallyComplete hN) (p : N) :
    ContinuousOn (fun v => Morse.exp hN p v) (Morse.tangentSubspace hN p) := by
  have : ConnectedSpace (Bridge.Sub hN) :=
    @ConnectedSpace.mk N _ (isPreconnected_iff_preconnectedSpace.1 hconn) ⟨p⟩
  obtain ⟨-, -, h3⟩ := hB n (Bridge.Sub hN) Bridge.conn Bridge.conn_isLC
  have hdom : ∀ (q : Bridge.Sub hN) (w : TangentSpace 𝓘(ℝ, Rn n) q),
      (Bridge.incl hN q, Bridge.D hN q w) ∈ Morse.expDom hN :=
    fun q w => hcomp q _ (Bridge.D_mem q w)
  have hgc : GeodComplete (n := n) (M := Bridge.Sub hN) Bridge.conn :=
    fun q w => Bridge.expDefined_of_mem_expDom (hdom q w)
  set q : Bridge.Sub hN := p
  have hc : Continuous (fun w : Rn n => expMap (n := n) Bridge.conn q w) := h3 hgc q
  have hc' : Continuous (fun v : V => Bridge.incl hN
      (expMap (n := n) Bridge.conn q (Bridge.L hN q v))) :=
    continuous_subtype_val.comp (hc.comp (Bridge.L hN q).continuous)
  refine hc'.continuousOn.congr fun v hv => ?_
  have h := Bridge.expMap_eq (hdom q (Bridge.L hN q v))
  rw [Bridge.D_L hv] at h
  exact h.symm

/-! #### The converse: `A` gives `B` on `↥N`

`B`'s three clauses on `↥N` with the induced Levi-Civita connection follow from `A`: (1) from
`IsGeodesicOn.exp_smul_eq` (after continuing the blind geodesic past the ends of `[0, t]`),
(2) from the uniform local flow `exists_localFlow_exp` (a blind geodesic on `[a, b]` continues past
both end points), (3) from `continuousOn_exp`. -/

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

/-- A project geodesic on an open `s ⊇ [a, b]`, lifted to `↥N`, is a blind geodesic on `[a, b]`. -/
theorem isGeodesic_lift_Icc {γ : ℝ → V} {s : Set ℝ} (hγ : Morse.IsGeodesicOn hN γ s) {a b : ℝ}
    (hab : a < b) (hsub : Icc a b ⊆ s) (q : Bridge.Sub hN) :
    IsGeodesic (n := n) Bridge.conn (Bridge.lift γ q) (Icc a b) ∧
      EqOn (Bridge.incl hN ∘ Bridge.lift γ q) γ (Icc a b) := by
  set I := Icc a b
  have uI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have heq : EqOn (Bridge.incl hN ∘ Bridge.lift γ q) γ I := fun t ht =>
    Bridge.incl_lift q (hγ.mem t (hsub ht))
  have hd : EqOn (derivWithin (Bridge.incl hN ∘ Bridge.lift γ q) I) (deriv γ) I := fun t ht => by
    rw [derivWithin_congr heq (heq ht)]
    exact (hγ.hasDerivAt (hsub ht)).hasDerivWithinAt.derivWithin (uI t ht)
  have hdd : ∀ t ∈ I, derivWithin (derivWithin (Bridge.incl hN ∘ Bridge.lift γ q) I) I t =
      deriv (deriv γ) t := fun t ht => by
    rw [derivWithin_congr hd (hd ht)]
    exact (hγ.hasDerivAt_deriv (hsub ht)).hasDerivWithinAt.derivWithin (uI t ht)
  refine ⟨Bridge.isGeodesic_iff.2 ⟨⟨ordConnected_Icc, uI⟩, (hγ.contDiffOn.mono hsub).congr heq,
    fun t ht => ?_⟩, heq⟩
  rw [hdd t ht, Bridge.lift_of_mem q (hγ.mem t (hsub ht))]
  exact hγ.tanProj_deriv_deriv (hsub ht)

/-- Restriction of a blind geodesic to a subinterval. -/
theorem isGeodesic_restrict {γ : ℝ → Bridge.Sub hN} {s I : Set ℝ}
    (hγ : IsGeodesic (n := n) Bridge.conn γ s) (hI : IsIntv I) (hIs : I ⊆ s) :
    IsGeodesic (n := n) Bridge.conn γ I ∧
      ∀ t ∈ I, derivWithin (Bridge.incl hN ∘ γ) I t = derivWithin (Bridge.incl hN ∘ γ) s t := by
  obtain ⟨hs, hc, hP⟩ := Bridge.isGeodesic_iff.1 hγ
  set f := Bridge.incl hN ∘ γ
  have hd1 : ∀ t ∈ I, derivWithin f I t = derivWithin f s t := fun t ht =>
    (((hc.differentiableOn (by simp)) t (hIs ht)).hasDerivWithinAt.mono hIs).derivWithin
      (hI.2 t ht)
  have hg : ContDiffOn ℝ ∞ (derivWithin f s) s := hc.derivWithin hs.2 (by simp)
  refine ⟨Bridge.isGeodesic_iff.2 ⟨hI, hc.mono hIs, fun t ht => ?_⟩, hd1⟩
  have hd2 : derivWithin (derivWithin f I) I t = derivWithin (derivWithin f s) s t := by
    rw [derivWithin_congr (fun u hu => hd1 u hu) (hd1 t ht)]
    exact (((hg.differentiableOn (by simp)) t (hIs ht)).hasDerivWithinAt.mono hIs).derivWithin
      (hI.2 t ht)
  rw [hd2]
  exact hP t (hIs ht)

/-- A blind `exp_q w` gives a project `exp` (continuing the blind geodesic past `0` and `1`). -/
theorem mem_expDom_of_expDefined (hfl : LocalFlow hN) {q : Bridge.Sub hN}
    {w : TangentSpace 𝓘(ℝ, Rn n) q} (h : ExpDefined (n := n) Bridge.conn q w) :
    (Bridge.incl hN q, Bridge.D hN q w) ∈ Morse.expDom hN := by
  obtain ⟨γ, hγ, hinit⟩ := h
  have hγ0 : γ 0 = q := hinit.1
  obtain ⟨-, hc, -⟩ := Bridge.isGeodesic_iff.1 hγ
  obtain ⟨ε, hε, g, hg, hgeq⟩ := extend_closed hfl zero_lt_one hc
    (Bridge.isGeodesicOn_Ioo (c := γ) hγ) (γ 0).2 (γ 1).2
  have uI : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h0g : (0 : ℝ) ∈ Ioo (0 - ε) (1 + ε) := ⟨by linarith, by linarith⟩
  refine ⟨g, ε, hε, ?_, ?_, ?_⟩
  · convert hg using 2; ring
  · rw [hgeq h0I]; show Bridge.incl hN (γ 0) = Bridge.incl hN q; rw [hγ0]
  · have h1 := (Bridge.initData_iff hγ0).1 hinit
    have h2 := Bridge.D_vel (c := γ) hγ.2.1 uI h0I
    rw [← h1, h2, ← derivWithin_congr hgeq (hgeq h0I)]
    exact ((hg.hasDerivAt h0g).hasDerivWithinAt.derivWithin (uI 0 h0I)).symm

/-- `B`'s conclusion on `↥N` (with the induced Levi-Civita connection `Bridge.conn`). -/
def Bemb (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) : Prop :=
  (∀ (q : Bridge.Sub hN) (v : TangentSpace 𝓘(ℝ, Rn n) q) (γ : ℝ → Bridge.Sub hN) (s : Set ℝ),
      IsGeodesic (n := n) Bridge.conn γ s → (0 : ℝ) ∈ s → InitData (n := n) γ s q v →
        ∀ t ∈ s, ExpDefined (n := n) Bridge.conn q (t • v) ∧
          expMap (n := n) Bridge.conn q (t • v) = γ t) ∧
    (∀ (γ : ℝ → Bridge.Sub hN) (a b : ℝ), a < b → IsGeodesic (n := n) Bridge.conn γ (Icc a b) →
      ∃ ε > 0, ∃ γ' : ℝ → Bridge.Sub hN,
        IsGeodesic (n := n) Bridge.conn γ' (Icc (a - ε) (b + ε)) ∧ EqOn γ γ' (Icc a b)) ∧
    (GeodComplete (n := n) (M := Bridge.Sub hN) Bridge.conn →
      ∀ q : Bridge.Sub hN, Continuous (fun w : Rn n => expMap (n := n) Bridge.conn q w))

theorem B_to_Bemb (hB : B) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] : Bemb hN :=
  hB n (Bridge.Sub hN) Bridge.conn Bridge.conn_isLC

/-- **`A` ⇒ `B` on `↥N`.** -/
theorem A_to_Bemb (hA : A) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) : Bemb hN := by
  have hfl : LocalFlow hN := localFlow_of hA.2.1
  refine ⟨?_, ?_, ?_⟩
  · -- (1): a geodesic is `t ↦ exp_q(tv)`
    intro q v γ s hγ h0 hinit t ht
    have hγ0 : γ 0 = q := hinit.1
    have hDt : Bridge.D hN q (t • v) = t • Bridge.D hN q v := map_smul _ _ _
    suffices hmem : (Bridge.incl hN q, Bridge.D hN q (t • v)) ∈ Morse.expDom hN ∧
        Morse.exp hN (Bridge.incl hN q) (Bridge.D hN q (t • v)) = Bridge.incl hN (γ t) by
      refine ⟨Bridge.expDefined_of_mem_expDom hmem.1, ?_⟩
      apply Subtype.ext
      exact (Bridge.expMap_eq hmem.1).trans hmem.2
    rcases eq_or_ne t 0 with rfl | ht0
    · rw [hDt, zero_smul]
      refine ⟨⟨_, Morse.isGeodesicFrom_const (q : N).2⟩, ?_⟩
      rw [hγ0]
      exact Morse.exp_zero (q : N).2
    set m := min 0 t
    set M := max 0 t
    have hmM : m < M := min_lt_max.2 ht0.symm
    have hIs : Icc m M ⊆ s := hγ.1.1.out (min_rec' (· ∈ s) h0 ht) (max_rec' (· ∈ s) h0 ht)
    have hI : IsIntv (Icc m M) := ⟨ordConnected_Icc, uniqueDiffOn_Icc hmM⟩
    obtain ⟨hγI, hdI⟩ := isGeodesic_restrict hγ hI hIs
    obtain ⟨-, hc, -⟩ := Bridge.isGeodesic_iff.1 hγI
    obtain ⟨ε, hε, g, hg, hgeq⟩ := extend_closed hfl hmM hc
      (Bridge.isGeodesicOn_Ioo (c := γ) hγI) (γ m).2 (γ M).2
    have h0I : (0 : ℝ) ∈ Icc m M := ⟨min_le_left _ _, le_max_left _ _⟩
    have htI : t ∈ Icc m M := ⟨min_le_right _ _, le_max_right _ _⟩
    have h0g : (0 : ℝ) ∈ Ioo (m - ε) (M + ε) := ⟨by linarith [h0I.1], by linarith [h0I.2]⟩
    have htg : t ∈ Ioo (m - ε) (M + ε) := ⟨by linarith [htI.1], by linarith [htI.2]⟩
    have hg0 : g 0 = Bridge.incl hN q := by
      rw [hgeq h0I]; show Bridge.incl hN (γ 0) = _; rw [hγ0]
    have hg0' : deriv g 0 = Bridge.D hN q v := by
      have h1 := (Bridge.initData_iff hγ0).1 hinit
      have h2 := Bridge.D_vel (c := γ) hγ.2.1 hγ.1.2 h0
      rw [← h1, h2, ← hdI 0 h0I, ← derivWithin_congr hgeq (hgeq h0I)]
      exact ((hg.hasDerivAt h0g).hasDerivWithinAt.derivWithin (hI.2 0 h0I)).symm
    -- `A`'s first conjunct along the continued geodesic `g`
    have hexp := hA.1 hg isPreconnected_Ioo h0g htg
    rw [hg0, hg0'] at hexp
    -- `(q, t • v) ∈ dom exp`
    have hη := hg.comp_mul_add t 0
    have hpre := Morse.isPreconnected_preimage_mul_add (isPreconnected_Ioo (a := m - ε) (b := M + ε)) t 0
    have h00 : (0 : ℝ) ∈ (fun σ => t * σ + 0) ⁻¹' Ioo (m - ε) (M + ε) := by simpa using h0g
    have h11 : (1 : ℝ) ∈ (fun σ => t * σ + 0) ⁻¹' Ioo (m - ε) (M + ε) := by simpa using htg
    have hfrom := Morse.isGeodesicFrom_of_isGeodesicOn hη hpre h00 h11
    have h1 : HasDerivAt (fun σ : ℝ => t * σ + 0) t 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul t).add_const 0
    have h2 := HasDerivAt.scomp (h := fun σ : ℝ => t * σ + 0) (0 : ℝ)
      (hg.hasDerivAt (t := t * 0 + 0) (by simpa using h0g)) h1
    rw [show t * 0 + 0 = 0 by ring] at h2
    have e2 : deriv (fun σ => g (t * σ + 0)) 0 = t • deriv g 0 := h2.deriv
    rw [e2, show t * 0 + 0 = 0 by ring, hg0, hg0'] at hfrom
    rw [hDt]
    exact ⟨⟨_, hfrom⟩, by rw [hexp, hgeq htI]; rfl⟩
  · -- (2): continuation of geodesic segments
    intro γ a b hab hγ
    obtain ⟨-, hc, -⟩ := Bridge.isGeodesic_iff.1 hγ
    obtain ⟨ε, hε, g, hg, hgeq⟩ := extend_closed hfl hab hc
      (Bridge.isGeodesicOn_Ioo (c := γ) hγ) (γ a).2 (γ b).2
    have hsub : Icc (a - ε / 2) (b + ε / 2) ⊆ Ioo (a - ε) (b + ε) := fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨hgeo', heq'⟩ := isGeodesic_lift_Icc hg (by linarith : a - ε / 2 < b + ε / 2) hsub (γ a)
    refine ⟨ε / 2, by linarith, _, hgeo', fun t ht => ?_⟩
    apply Subtype.ext
    show Bridge.incl hN (γ t) = Bridge.incl hN (Bridge.lift g (γ a) t)
    rw [show Bridge.incl hN (Bridge.lift g (γ a) t) = g t from
      heq' ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    exact (hgeq ht).symm
  · -- (3): continuity of `exp_q` for complete `↥N`
    intro hgc q
    have hdom : ∀ w : TangentSpace 𝓘(ℝ, Rn n) q,
        (Bridge.incl hN q, Bridge.D hN q w) ∈ Morse.expDom hN :=
      fun w => mem_expDom_of_expDefined hfl (hgc q w)
    have hco := hA.2.2.2.2 (hN := hN) (p := (q : N)) fun v hv => by
      have := hdom (Bridge.L hN q v)
      rwa [Bridge.D_L hv] at this
    have hc' : Continuous (fun w : Rn n => Bridge.incl hN (expMap (n := n) Bridge.conn q w)) := by
      have : Continuous (fun w : Rn n => Morse.exp hN (Bridge.incl hN q) (Bridge.D hN q w)) :=
        hco.comp_continuous (Bridge.D hN q).continuous fun w => Bridge.D_mem q w
      exact this.congr fun w => (Bridge.expMap_eq (hdom w)).symm
    exact Topology.IsInducing.subtypeVal.continuous_iff.2 hc'

end Embedded

#rt_check RoundTrip.V7_23.B_continuousOn_exp_embedded [Morse.IsGeodesicOn.exp_smul_eq,
  Morse.exists_localFlow_exp, Morse.isGeodesicOn_exp_smul_union,
  Morse.eventually_mem_expDom_and_continuousWithinAt_exp, Morse.continuousOn_exp]
#rt_overlap RoundTrip.V7_23.B_continuousOn_exp_embedded [Morse.IsGeodesicOn.exp_smul_eq,
  Morse.exists_localFlow_exp, Morse.isGeodesicOn_exp_smul_union,
  Morse.eventually_mem_expDom_and_continuousWithinAt_exp, Morse.continuousOn_exp]

#rt_check RoundTrip.V7_23.A_to_Bemb [Morse.IsGeodesicOn.exp_smul_eq,
  Morse.exists_localFlow_exp, Morse.isGeodesicOn_exp_smul_union,
  Morse.eventually_mem_expDom_and_continuousWithinAt_exp, Morse.continuousOn_exp]

/-! No direction `A → B` / `B → A` is proved; see `V7_23.json`. -/

end RoundTrip.V7_23
