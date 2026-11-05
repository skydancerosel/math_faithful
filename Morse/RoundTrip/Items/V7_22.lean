import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.V7_22

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V7_22

/-- The project's statement (universes instantiated at 0; `IsRiemComplete`, `IsRiemBounded`,
`IsGeodesicallyComplete` are definitions, i.e. vocabulary): for a slice submanifold `N ⊆ V` with
the induced metric, if `exp_q` is defined on all of `T_qN` (one point `q`), then `t ↦ exp_q(tv)` is
a geodesic on `ℝ`; and `N` is geodesically complete (`exp` defined on all of `TN`) iff every
geodesic on a nonempty open preconnected `s ⊆ ℝ` is the restriction of a geodesic on `ℝ`. -/
def A : Prop :=
  type_of% @Morse.isGeodesicOn_univ_exp_smul.{0,0,0} ∧
    type_of% @Morse.isGeodesicallyComplete_iff.{0,0,0}

theorem A_holds : A := ⟨@Morse.isGeodesicOn_univ_exp_smul, @Morse.isGeodesicallyComplete_iff⟩

/-! ### Embedded special case

`B` applied to a connected slice submanifold `N ⊆ V` with model `ℝⁿ`, made a Mathlib Riemannian
manifold with its Levi-Civita connection by `RoundTrip.Bridge` (`Bridge.Sub hN`, `Bridge.conn`),
gives the second conjunct of `A` (`isGeodesicallyComplete_iff`) for such `N`. `B` is used twice:
its `→` turns a blind geodesic `[0, 1] → N` into one on `ℝ`, which identifies the blind
`GeodComplete` with the project's `IsGeodesicallyComplete` (a geodesic on `[0, 1]` must be
continued past its end points, which the project does not do for closed intervals); then `B` itself
is read through the dictionary closed `[a, b]` ↔ open intervals. This is not `B → A`: `A`'s first
conjunct (`exp_q` defined on `T_qN` at ONE point `q` ⇒ `t ↦ exp_q(tv)` a geodesic on `ℝ`) is
pointwise, while `B` only concerns completeness of all of `M`; and `A` covers arbitrary slice
models `Z` and disconnected `N`. -/

section Embedded

set_option linter.unusedSectionVars false

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- A project geodesic on an open `s ⊇ [a, b]`, lifted to `↥N`, is a blind geodesic on `[a, b]`
(the Bridge's `isGeodesic_lift_of_isGeodesicFrom`, for an arbitrary closed interval). -/
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

/-- If blind geodesic segments extend to `ℝ`, a blind `exp_q w` gives a project `exp`. -/
theorem mem_expDom_of_ext (hext : ∀ (γ : ℝ → Bridge.Sub hN) (a b : ℝ), a < b →
      IsGeodesic (n := n) Bridge.conn γ (Icc a b) →
        ∃ γ' : ℝ → Bridge.Sub hN, IsGeodesic (n := n) Bridge.conn γ' univ ∧ EqOn γ γ' (Icc a b))
    {q : Bridge.Sub hN} {w : TangentSpace 𝓘(ℝ, Rn n) q}
    (hw : ExpDefined (n := n) Bridge.conn q w) :
    (Bridge.incl hN q, Bridge.D hN q w) ∈ Morse.expDom hN := by
  obtain ⟨γ, hγ, hinit⟩ := hw
  obtain ⟨γ', hγ', heq⟩ := hext γ 0 1 zero_lt_one hγ
  have hgeo : Morse.IsGeodesicOn hN (Bridge.incl hN ∘ γ') univ :=
    (Bridge.isGeodesic_iff_isGeodesicOn isOpen_univ ordConnected_univ).1 hγ'
  have uI : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hγ0 : γ 0 = q := hinit.1
  refine ⟨Bridge.incl hN ∘ γ', 1, one_pos, hgeo.mono isOpen_Ioo (subset_univ _), ?_, ?_⟩
  · show Bridge.incl hN (γ' 0) = Bridge.incl hN q
    rw [← heq h0I, hγ0]
  · have h1 := (Bridge.initData_iff hγ0).1 hinit
    have h2 := Bridge.D_vel (c := γ) hγ.2.1 uI h0I
    have e : derivWithin (Bridge.incl hN ∘ γ) (Icc 0 1) 0 =
        derivWithin (Bridge.incl hN ∘ γ') (Icc 0 1) 0 :=
      derivWithin_congr (fun t ht => congrArg (Bridge.incl hN) (heq ht))
        (congrArg (Bridge.incl hN) (heq h0I))
    show deriv (Bridge.incl hN ∘ γ') 0 = Bridge.D hN q w
    rw [← h1, h2, e]
    exact ((hgeo.hasDerivAt (mem_univ 0)).hasDerivWithinAt.derivWithin (uI 0 h0I)).symm

/-- Blind extension of geodesic segments `[a, b]` to `ℝ` ⇔ project extension of geodesics on open
intervals to `ℝ` (no completeness assumption; the dictionary closed ↔ open intervals). -/
theorem blindExt_iff_projExt :
    (∀ (γ : ℝ → Bridge.Sub hN) (a b : ℝ), a < b → IsGeodesic (n := n) Bridge.conn γ (Icc a b) →
      ∃ γ' : ℝ → Bridge.Sub hN, IsGeodesic (n := n) Bridge.conn γ' univ ∧ EqOn γ γ' (Icc a b)) ↔
    ∀ (γ : ℝ → V) (s : Set ℝ), Morse.IsGeodesicOn hN γ s → IsPreconnected s → s.Nonempty →
      ∃ γ' : ℝ → V, Morse.IsGeodesicOn hN γ' univ ∧ EqOn γ' γ s := by
  constructor
  · intro hext γ s hγ hs ⟨t₀, ht₀⟩
    set q₀ : Bridge.Sub hN := (⟨γ t₀, hγ.mem t₀ ht₀⟩ : N)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hγ.isOpen t₀ ht₀
    have hsub : Icc (t₀ - r / 2) (t₀ + r / 2) ⊆ s := fun t ht => hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [ht.1, ht.2])
    have hab : t₀ - r / 2 < t₀ + r / 2 := by linarith
    obtain ⟨hc, hceq⟩ := isGeodesic_lift_Icc hγ hab hsub q₀
    obtain ⟨γ', hγ', heq⟩ := hext _ _ _ hab hc
    have hgeo : Morse.IsGeodesicOn hN (Bridge.incl hN ∘ γ') univ :=
      (Bridge.isGeodesic_iff_isGeodesicOn isOpen_univ ordConnected_univ).1 hγ'
    refine ⟨_, hgeo, ?_⟩
    have ht₀I : t₀ ∈ Icc (t₀ - r / 2) (t₀ + r / 2) := ⟨by linarith, by linarith⟩
    have hEq : EqOn (Bridge.incl hN ∘ γ') γ (Icc (t₀ - r / 2) (t₀ + r / 2)) := fun t ht => by
      show Bridge.incl hN (γ' t) = γ t
      rw [← heq ht]
      exact hceq ht
    refine (hgeo.mono hγ.isOpen (subset_univ _)).eqOn hγ hs ht₀ (hEq ht₀I) ?_
    have hev : (Bridge.incl hN ∘ γ') =ᶠ[𝓝 t₀] γ :=
      eventually_of_mem (Icc_mem_nhds (by linarith) (by linarith)) hEq
    exact hev.deriv_eq
  · intro hext γ a b hab hγ
    set q₀ : Bridge.Sub hN := γ a
    have hgeo := Bridge.isGeodesicOn_Ioo (c := γ) hγ
    obtain ⟨γ'', hγ'', heq⟩ := hext _ _ hgeo isPreconnected_Ioo (nonempty_Ioo.2 hab)
    have hl : Bridge.incl hN ∘ Bridge.lift γ'' q₀ = γ'' :=
      funext fun t => Bridge.incl_lift q₀ (hγ''.mem t (mem_univ t))
    refine ⟨Bridge.lift γ'' q₀, ?_, ?_⟩
    · refine (Bridge.isGeodesic_iff_isGeodesicOn isOpen_univ ordConnected_univ).2 ?_
      rw [hl]
      exact hγ''
    · have hc1 : ContinuousOn (Bridge.incl hN ∘ γ) (Icc a b) :=
        (Bridge.isGeodesic_iff.1 hγ).2.1.continuousOn
      have hc2 : ContinuousOn γ'' (Icc a b) := hγ''.contDiffOn.continuousOn.mono (subset_univ _)
      have h := EqOn.of_subset_closure (fun t ht => (heq ht).symm) hc1 hc2 Ioo_subset_Icc_self
        (by rw [closure_Ioo hab.ne])
      intro t ht
      apply Subtype.ext
      show Bridge.incl hN (γ t) = Bridge.incl hN (Bridge.lift γ'' q₀ t)
      rw [Bridge.incl_lift q₀ (hγ''.mem t (mem_univ t))]
      exact h ht

theorem B_isGeodesicallyComplete_iff_embedded (hB : B)
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (hconn : IsPreconnected N) :
    Morse.IsGeodesicallyComplete hN ↔ ∀ (γ : ℝ → V) (s : Set ℝ), Morse.IsGeodesicOn hN γ s →
      IsPreconnected s → s.Nonempty →
        ∃ γ' : ℝ → V, Morse.IsGeodesicOn hN γ' univ ∧ EqOn γ' γ s := by
  rcases N.eq_empty_or_nonempty with hN0 | ⟨x₀, hx₀⟩
  · constructor
    · rintro - γ s hγ - ⟨t, ht⟩
      exact (eq_empty_iff_forall_notMem.1 hN0 _ (hγ.mem t ht)).elim
    · rintro - q
      exact (eq_empty_iff_forall_notMem.1 hN0 _ q.2).elim
  have : ConnectedSpace (Bridge.Sub hN) :=
    @ConnectedSpace.mk N _ (isPreconnected_iff_preconnectedSpace.1 hconn) ⟨⟨x₀, hx₀⟩⟩
  have hB' := hB n (Bridge.Sub hN) Bridge.conn Bridge.conn_isLC
  -- the blind and the project notions of geodesic completeness agree (using `B`'s `→`)
  have hGC : GeodComplete (n := n) (M := Bridge.Sub hN) Bridge.conn ↔
      Morse.IsGeodesicallyComplete hN := by
    constructor
    · intro h q v hv
      have := mem_expDom_of_ext (hB'.1 h) (h q (Bridge.L hN q v))
      rwa [Bridge.D_L hv] at this
    · intro h q w
      exact Bridge.expDefined_of_mem_expDom (h q _ (Bridge.D_mem q w))
  rw [← hGC, hB', blindExt_iff_projExt]

/-! #### The converse: `A`'s second conjunct gives `B` on `↥N`

Here the dictionary `GeodComplete ↔ IsGeodesicallyComplete` is obtained without `B`, by
continuing a blind geodesic on `[0, 1]` past its end points with the uniform local existence of
geodesics (`Morse.exists_localFlow_exp`, outside the item). -/


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

/-- The blind and project notions of geodesic completeness agree on `↥N`. -/
theorem geodComplete_iff (hfl : LocalFlow hN) :
    GeodComplete (n := n) (M := Bridge.Sub hN) Bridge.conn ↔ Morse.IsGeodesicallyComplete hN := by
  constructor
  · intro h q v hv
    obtain ⟨γ, hγ, hinit⟩ := h q (Bridge.L hN q v)
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
      rw [Bridge.D_L hv] at h1
      rw [← h1, h2, ← derivWithin_congr hgeq (hgeq h0I)]
      exact ((hg.hasDerivAt h0g).hasDerivWithinAt.derivWithin (uI 0 h0I)).symm
  · intro h q w
    exact Bridge.expDefined_of_mem_expDom (h q _ (Bridge.D_mem q w))

/-- `B`'s conclusion on `↥N` (with the induced Levi-Civita connection `Bridge.conn`). -/
def Bemb (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) : Prop :=
  GeodComplete (n := n) (M := Bridge.Sub hN) Bridge.conn ↔
    ∀ (γ : ℝ → Bridge.Sub hN) (a b : ℝ), a < b → IsGeodesic (n := n) Bridge.conn γ (Icc a b) →
      ∃ γ' : ℝ → Bridge.Sub hN, IsGeodesic (n := n) Bridge.conn γ' univ ∧ EqOn γ γ' (Icc a b)

theorem B_to_Bemb (hB : B) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] : Bemb hN :=
  hB n (Bridge.Sub hN) Bridge.conn Bridge.conn_isLC

/-- **`A` ⇒ `B` on `↥N`**: `A`'s second conjunct, through the dictionary. -/
theorem A_to_Bemb (hA : A) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) : Bemb hN := by
  unfold Bemb
  rw [geodComplete_iff (localFlow_of @Morse.exists_localFlow_exp), blindExt_iff_projExt]
  exact hA.2 (hN := hN)

end Embedded

#rt_check RoundTrip.V7_22.B_isGeodesicallyComplete_iff_embedded [Morse.isGeodesicOn_univ_exp_smul,
  Morse.isGeodesicallyComplete_iff]
#rt_overlap RoundTrip.V7_22.B_isGeodesicallyComplete_iff_embedded [Morse.isGeodesicOn_univ_exp_smul,
  Morse.isGeodesicallyComplete_iff]
#rt_check RoundTrip.V7_22.A_to_Bemb [Morse.isGeodesicOn_univ_exp_smul,
  Morse.isGeodesicallyComplete_iff]

/-! No direction `A → B` / `B → A` is proved; see `V7_22.json`. -/

end RoundTrip.V7_22
