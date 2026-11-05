import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.V7_20

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V7_20

/-- The project's statement (universes instantiated at 0; `Morse.IsShortJoin hN δ y z` is a
definition: `∃ v ∈ T_yN, ‖v‖ < δ, exp_y v = z, ρ(y, z) = ‖v‖`, `v` the only `w ∈ T_yN` with
`‖w‖ < δ` and `exp_y w = z`, and an open `O₂ ∋ (y, z)` in `V × V` with a smooth `G : V × V → V`,
`G (y, z) = v`, giving the joining vector of every pair `(y', z') ∈ O₂` of points of `N` at
distance `< δ`): the local form (`exists_isShortJoin`: around each `p ∈ N` an open `Ω` and `s > 0`
with `IsShortJoin δ y z` for `y ∈ N ∩ Ω`, `ρ(y, z) < δ ≤ s`) and Corollary 10.8 for compact
`K ⊆ N` of a slice submanifold `N ⊆ V` with the induced metric. -/
def A : Prop :=
  type_of% @Morse.exists_isShortJoin.{0,0,0} ∧ type_of% @Morse.corollary_10_8.{0,0,0}

theorem A_holds : A := ⟨@Morse.exists_isShortJoin, @Morse.corollary_10_8⟩

/-! ### Embedded special case: `A` gives `B` on `↥N`

`B`'s conclusion on a connected slice submanifold `N ⊆ V` with model `ℝⁿ`, made a Mathlib
Riemannian manifold with its Levi-Civita connection by `RoundTrip.Bridge` (`Bridge.Sub hN`,
`Bridge.conn`), follows from `A`'s `corollary_10_8`. The blind joins (geodesics on `[0, 1]`) are
continued past their end points (`extend_closed`, from the uniform local flow
`Morse.exists_localFlow_exp`, outside the item) to read them as project geodesics; the smooth map
`G` of `B` is assembled from the local smooth maps of `IsShortJoin` by uniqueness. -/

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

/-- `B`'s conclusion on `↥N` (with the induced Levi-Civita connection `Bridge.conn`). -/
def Bemb (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) : Prop :=
  ∀ K : Set (Bridge.Sub hN), IsCompact K → ∃ δ > 0,
    (∀ p ∈ K, ∀ q ∈ K, rho (n := n) p q < δ →
      (∃ γ, JoinsShort (n := n) Bridge.conn δ γ p q ∧
        ∀ γ', JoinsShort (n := n) Bridge.conn δ γ' p q → Set.EqOn γ γ' (Set.Icc 0 1)) ∧
      (∀ γ, JoinsShort (n := n) Bridge.conn δ γ p q → IsMinimal (n := n) Bridge.conn γ 0 1)) ∧
    ∃ G : Bridge.Sub hN × Bridge.Sub hN → TangentBundle 𝓘(ℝ, Rn n) (Bridge.Sub hN),
      ContMDiffOn ((𝓘(ℝ, Rn n)).prod (𝓘(ℝ, Rn n))) (𝓘(ℝ, Rn n)).tangent ∞ G
        {x : Bridge.Sub hN × Bridge.Sub hN | x.1 ∈ K ∧ x.2 ∈ K ∧ rho (n := n) x.1 x.2 < δ} ∧
      ∀ p ∈ K, ∀ q ∈ K, rho (n := n) p q < δ → (G (p, q)).proj = p ∧
        ∃ γ, JoinsShort (n := n) Bridge.conn δ γ p q ∧
          HEq (vel (n := n) γ (Set.Icc 0 1) 0) (G (p, q)).snd

theorem B_to_Bemb (hB : B) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] : Bemb hN :=
  hB n (Bridge.Sub hN) Bridge.conn Bridge.conn_isLC

/-- **`A` ⇒ `B` on `↥N`** (connected `N`; `A`'s `corollary_10_8`). -/
theorem A_to_Bemb (hA : A) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    (hconn : IsPreconnected N) : Bemb hN := by
  have hfl : LocalFlow hN := localFlow_of @Morse.exists_localFlow_exp
  intro K hK
  set K' : Set V := Bridge.incl hN '' K
  have hK' : IsCompact K' := hK.image continuous_subtype_val
  have hK'N : K' ⊆ N := by rintro _ ⟨x, -, rfl⟩; exact (x : N).2
  obtain ⟨δ, hδ, hSJ⟩ := hA.2 hN hK' hK'N
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
  refine ⟨δ, hδ, fun p hp q hq hpq => ?_, ?_⟩
  · have hx : (p, q) ∈ S := ⟨hp, hq, hpq⟩
    obtain ⟨v, hv, hvδ, hexp, hρ, huniq, -⟩ := hSJ' (p, q) hx
    obtain ⟨γ₀, hγ₀, -⟩ := hjoin p q v hv hvδ hexp hρ
    have hγ₀d := (hident p q v huniq γ₀ hγ₀).1
    refine ⟨⟨γ₀, hγ₀, fun γ' hγ' => ?_⟩, fun γ hγ => ⟨hγ.1, fun pw a' b' hab' hpw ha' hb' => ?_⟩⟩
    · exact Bridge.eqOn_Icc_of_isGeodesic zero_lt_one hγ₀.1 hγ'.1 (hγ₀.2.1.trans hγ'.2.1.symm)
        (hγ₀d.trans (hident p q v huniq γ' hγ').1.symm)
    · rw [(hident p q v huniq γ hγ).2]
      have hle : Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q) ≤
          ENNReal.ofReal (arcLen (n := n) pw a' b') := by
        apply sInf_le
        rw [Bridge.pathLengths_eq]
        refine ⟨_, ⟨pw, a', b', hab', hpw, ?_, ?_, rfl⟩, rfl⟩
        · rw [ha', hγ.2.1]
        · rw [hb', hγ.2.2.1]
      have hρ' : Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q) =
          ENNReal.ofReal ‖v‖ := hρ
      rw [hρ'] at hle
      exact (ENNReal.ofReal_le_ofReal_iff (Bridge.arcLen_nonneg hab')).1 hle
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

#rt_check RoundTrip.V7_20.A_to_Bemb [Morse.exists_isShortJoin, Morse.corollary_10_8]

/-! No direction `A → B` / `B → A` is proved; see `V7_20.json`. -/

end RoundTrip.V7_20
