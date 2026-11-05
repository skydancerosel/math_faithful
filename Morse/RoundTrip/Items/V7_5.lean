import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_5
import RoundTrip.Bridge

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V7_5

/-- The project's statement (universes instantiated at 0): Uniqueness of geodesics of a slice submanifold `N ⊆ V` (`projRep` is a definition: the smooth local extension of `x ↦ P_x` from a slice chart): two geodesics on an open set agreeing in position and velocity at `t₀` agree near `t₀`, and on all of an open preconnected `s`. -/
def A : Prop :=
  type_of% @Morse.IsGeodesicOn.eventuallyEq.{0,0,0} ∧
    type_of% @Morse.IsGeodesicOn.eqOn.{0,0,0}

theorem A_holds : A := ⟨@Morse.IsGeodesicOn.eventuallyEq, @Morse.IsGeodesicOn.eqOn⟩

/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ`, the induced metric and the induced Levi-Civita connection `Bridge.conn` (`B_emb`;
`B_to_B_emb`). Through the Bridge's dictionary a blind geodesic on an interval `s` is a curve smooth
on `s` that is a project geodesic on `interior s` (`Emb.isGeodesic_iff_interior`). `A_to_B_emb`:
when `t₀` is an endpoint of `s`, the initial data are first carried to an interior time by one-sided
ODE uniqueness in a slice chart (`Emb.loc_right`, `Emb.loc_left`, adapted from the Bridge's
`eqOn_Icc_of_isGeodesic`, which itself uses `IsGeodesicOn.eqOn` and so may not be used here); then
A's `eqOn` on `interior s` and continuity. `B_emb_to_A`: A in full (any model `Z`, via
`ℝ^{dim Z}`), from B_emb applied to the lifts of the project geodesics to `↥N`. -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

/-- Every point of a nondegenerate interval lies in the closure of its interior. -/
theorem subset_closure_interior {s : Set ℝ} (hs : IsIntv s) : s ⊆ closure (interior s) := by
  intro t ht
  obtain ⟨u, ⟨-, hu⟩, hne⟩ :=
    accPt_iff_nhds.1 (uniqueDiffWithinAt_iff_accPt.1 (hs.2 t ht)) univ univ_mem
  have hsub : Ioo (min t u) (max t u) ⊆ interior s :=
    interior_maximal (Ioo_subset_Icc_self.trans (hs.1.uIcc_subset ht hu)) isOpen_Ioo
  refine closure_mono hsub ?_
  rw [closure_Ioo (min_lt_max.2 hne.symm).ne]
  exact ⟨min_le_left _ _, le_max_left _ _⟩

/-- A function continuous on a nondegenerate interval and constant on its interior is constant. -/
theorem eqOn_of_interior {X : Type*} [TopologicalSpace X] [T2Space X] {s : Set ℝ} (hs : IsIntv s)
    {h : ℝ → X} {x : X} (hh : ContinuousOn h s) (h0 : ∀ t ∈ interior s, h t = x) :
    ∀ t ∈ s, h t = x := by
  intro t ht
  have h1 := ((hh t ht).mono interior_subset).mem_closure_image (subset_closure_interior hs ht)
  have h2 : h '' interior s ⊆ {x} := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact h0 τ hτ
  have := closure_mono h2 h1
  rwa [closure_singleton] at this

theorem derivWithin_eq_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    {s : Set ℝ} {t : ℝ} (ht : t ∈ interior s) : derivWithin f s t = deriv f t :=
  derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 ht)

theorem derivWithin2_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    {s : Set ℝ} {t : ℝ} (ht : t ∈ interior s) :
    derivWithin (derivWithin f s) s t = deriv (deriv f) t := by
  rw [derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 ht)]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_interior.mem_nhds ht] with u hu
  exact derivWithin_eq_deriv hu

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- **Dictionary: geodesics on any interval.** A blind geodesic of the induced connection on `s`
is a curve smooth (in `V`) on the interval `s` which is a project geodesic on `interior s`. -/
theorem isGeodesic_iff_interior {c : ℝ → Bridge.Sub hN} {s : Set ℝ} :
    BridgePrelude.IsGeodesic (conn (hN := hN)) c s ↔ IsIntv s ∧ ContDiffOn ℝ ∞ (incl hN ∘ c) s ∧
      Morse.IsGeodesicOn hN (incl hN ∘ c) (interior s) := by
  rw [isGeodesic_iff]
  constructor
  · rintro ⟨hs, hc, hP⟩
    refine ⟨hs, hc, isOpen_interior, fun t _ => (c t).2, hc.mono interior_subset, fun t ht => ?_⟩
    rw [← Morse.tanProj_eq_zero_iff, ← derivWithin2_eq ht]
    exact hP t (interior_subset ht)
  · rintro ⟨hs, hc, hg⟩
    refine ⟨hs, hc, eqOn_of_interior hs ?_ fun t ht => ?_⟩
    · have h1 : ContinuousOn (derivWithin (derivWithin (incl hN ∘ c) s) s) s :=
        (hc.derivWithin hs.2 (m := 1) (WithTop.coe_le_coe.2 le_top)).continuousOn_derivWithin hs.2 le_rfl
      have h2 : ContinuousOn (fun t => P hN (c t)) s :=
        contMDiff_P.continuous.comp_continuousOn (contMDiffOn_curve_iff.2 hc).continuousOn
      exact h2.clm_apply h1
    · rw [derivWithin2_eq ht]
      exact (Morse.tanProj_eq_zero_iff hN).2 (hg.normal t ht)

/-- A blind geodesic on `s` restricts to `[a, b] ⊆ s`, with the same velocities. -/
theorem isGeodesic_restrict {c : ℝ → Bridge.Sub hN} {s : Set ℝ} {a b : ℝ} (hab : a < b)
    (hsub : Icc a b ⊆ s) (h : BridgePrelude.IsGeodesic (conn (hN := hN)) c s) :
    BridgePrelude.IsGeodesic (conn (hN := hN)) c (Icc a b) ∧
      ∀ t ∈ Icc a b, derivWithin (incl hN ∘ c) (Icc a b) t = derivWithin (incl hN ∘ c) s t := by
  obtain ⟨hs, hc, hP⟩ := isGeodesic_iff.1 h
  have u' : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hd1 : ∀ t ∈ Icc a b, derivWithin (incl hN ∘ c) (Icc a b) t =
      derivWithin (incl hN ∘ c) s t :=
    fun t ht => derivWithin_subset hsub (u' t ht) ((hc.differentiableOn (by simp)) t (hsub ht))
  have hdc : ContDiffOn ℝ ∞ (derivWithin (incl hN ∘ c) s) s := hc.derivWithin hs.2 (by simp)
  refine ⟨isGeodesic_iff.2 ⟨⟨ordConnected_Icc, u'⟩, hc.mono hsub, fun t ht => ?_⟩, hd1⟩
  rw [derivWithin_congr hd1 (hd1 t ht),
    derivWithin_subset hsub (u' t ht) ((hdc.differentiableOn (by simp)) t (hsub ht))]
  exact hP t (hsub ht)

/-- One-sided local uniqueness from the left endpoint of `[a, b]` (the first half of the Bridge's
`eqOn_Icc_of_isGeodesic`, which then uses `IsGeodesicOn.eqOn`). -/
theorem loc_right {c₁ c₂ : ℝ → Bridge.Sub hN} {a b : ℝ} (hab : a < b)
    (h₁ : BridgePrelude.IsGeodesic (conn (hN := hN)) c₁ (Icc a b))
    (h₂ : BridgePrelude.IsGeodesic (conn (hN := hN)) c₂ (Icc a b)) (h0 : c₁ a = c₂ a)
    (h0' : derivWithin (incl hN ∘ c₁) (Icc a b) a = derivWithin (incl hN ∘ c₂) (Icc a b) a) :
    ∃ ε, a < ε ∧ ε ≤ b ∧ ∀ t ∈ Icc a ε, incl hN (c₁ t) = incl hN (c₂ t) ∧
      derivWithin (incl hN ∘ c₁) (Icc a b) t = derivWithin (incl hN ∘ c₂) (Icc a b) t := by
  obtain ⟨-, hc₁, -⟩ := isGeodesic_iff.1 h₁
  obtain ⟨-, hc₂, -⟩ := isGeodesic_iff.1 h₂
  set I := Icc a b
  have uI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have haI : a ∈ I := left_mem_Icc.2 hab.le
  set F₁ : ℝ → V × V := fun t => (incl hN (c₁ t), derivWithin (incl hN ∘ c₁) I t)
  set F₂ : ℝ → V × V := fun t => (incl hN (c₂ t), derivWithin (incl hN ∘ c₂) I t)
  have hF₁ : ContinuousOn F₁ I :=
    hc₁.continuousOn.prodMk (hc₁.derivWithin uI (m := 0) (by simp)).continuousOn
  have hF₂ : ContinuousOn F₂ I :=
    hc₂.continuousOn.prodMk (hc₂.derivWithin uI (m := 0) (by simp)).continuousOn
  have hFa : F₁ a = F₂ a := by
    show (incl hN (c₁ a), _) = (incl hN (c₂ a), _)
    rw [h0, h0']
  set σ := Morse.sliceAt hN (c₁ a)
  have hσ : incl hN (c₁ a) ∈ σ.φ.source := Morse.mem_sliceAt_source hN (c₁ a)
  set G : V × V → V × V := fun z => (z.2, fderiv ℝ (Morse.projRep σ) z.1 z.2 z.2)
  have hG : ContDiffAt ℝ 1 G (F₁ a) := by
    have hQ : ContDiffAt ℝ ∞ (fderiv ℝ (Morse.projRep σ)) (incl hN (c₁ a)) :=
      (Morse.contDiffAt_projRep σ (q := c₁ a) hσ).fderiv_right (m := ∞) (by simp)
    have h1 : ContDiffAt ℝ ∞ (fun z : V × V => fderiv ℝ (Morse.projRep σ) z.1) (F₁ a) :=
      ContDiffAt.comp (F₁ a) hQ contDiffAt_fst
    exact (contDiffAt_snd.prodMk ((h1.clm_apply contDiffAt_snd).clm_apply contDiffAt_snd)).of_le
      (by exact_mod_cast le_top)
  obtain ⟨K, U₀, hU₀, hK⟩ := hG.exists_lipschitzOnWith
  set U := U₀ ∩ σ.φ.source ×ˢ (univ : Set V)
  have hU : U ∈ 𝓝 (F₁ a) :=
    Filter.inter_mem hU₀ (prod_mem_nhds (σ.φ.open_source.mem_nhds hσ) univ_mem)
  have hU₂ : U ∈ 𝓝 (F₂ a) := hFa ▸ hU
  have e₁ : ∀ᶠ t in 𝓝[I] a, F₁ t ∈ U := (hF₁ a haI).preimage_mem_nhdsWithin hU
  have e₂ : ∀ᶠ t in 𝓝[I] a, F₂ t ∈ U := (hF₂ a haI).preimage_mem_nhdsWithin hU₂
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 (e₁.and e₂)
  set ε := min (a + δ / 2) b
  have haε : a < ε := lt_min (by linarith) hab
  have hεb : ε ≤ b := min_le_right _ _
  have hεa : ε ≤ a + δ / 2 := min_le_left _ _
  have hsub : Icc a ε ⊆ Metric.ball a δ ∩ I := fun t ht => by
    refine ⟨?_, ht.1, ht.2.trans hεb⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hlift : ∀ {c : ℝ → Bridge.Sub hN}, BridgePrelude.IsGeodesic (conn (hN := hN)) c I →
      ∀ t ∈ Ico a ε, incl hN (c t) ∈ σ.φ.source →
      HasDerivWithinAt (fun τ => (incl hN (c τ), derivWithin (incl hN ∘ c) I τ))
        (G (incl hN (c t), derivWithin (incl hN ∘ c) I t)) (Ici t) t := by
    intro c h t ht hsrc
    obtain ⟨-, hc, -⟩ := isGeodesic_iff.1 h
    have htI : t ∈ Ico a b := ⟨ht.1, ht.2.trans_le hεb⟩
    have hf' : HasDerivWithinAt (incl hN ∘ c) (derivWithin (incl hN ∘ c) I t) I t :=
      ((hc.differentiableOn (by simp)) t (Ico_subset_Icc_self htI)).hasDerivWithinAt
    have hg' : HasDerivWithinAt (derivWithin (incl hN ∘ c) I)
        (derivWithin (derivWithin (incl hN ∘ c) I) I t) I t :=
      (((hc.derivWithin uI (m := 1) (WithTop.coe_le_coe.2 le_top)).differentiableOn (by simp)) t
        (Ico_subset_Icc_self htI)).hasDerivWithinAt
    rw [derivWithin_derivWithin_eq hab h (Ico_subset_Icc_self htI) σ hsrc] at hg'
    exact (hf'.prodMk hg').mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem htI)
  have hloc : EqOn F₁ F₂ (Icc a ε) := by
    refine ODE_solution_unique_of_mem_Icc_right (v := fun _ => G) (s := fun _ => U) (K := K)
      (fun _ _ => hK.mono inter_subset_left) (hF₁.mono fun t ht => (hsub ht).2)
      (fun t ht => hlift h₁ t ht ((hδs (hsub (Ico_subset_Icc_self ht))).1).2.1)
      (fun t ht => (hδs (hsub (Ico_subset_Icc_self ht))).1)
      (hF₂.mono fun t ht => (hsub ht).2)
      (fun t ht => hlift h₂ t ht ((hδs (hsub (Ico_subset_Icc_self ht))).2).2.1)
      (fun t ht => (hδs (hsub (Ico_subset_Icc_self ht))).2) hFa
  exact ⟨ε, haε, hεb, fun t ht => ⟨congrArg Prod.fst (hloc ht), congrArg Prod.snd (hloc ht)⟩⟩

/-- One-sided local uniqueness from the right endpoint of `[a, b]` (mirror image of `loc_right`). -/
theorem loc_left {c₁ c₂ : ℝ → Bridge.Sub hN} {a b : ℝ} (hab : a < b)
    (h₁ : BridgePrelude.IsGeodesic (conn (hN := hN)) c₁ (Icc a b))
    (h₂ : BridgePrelude.IsGeodesic (conn (hN := hN)) c₂ (Icc a b)) (h0 : c₁ b = c₂ b)
    (h0' : derivWithin (incl hN ∘ c₁) (Icc a b) b = derivWithin (incl hN ∘ c₂) (Icc a b) b) :
    ∃ ε, a ≤ ε ∧ ε < b ∧ ∀ t ∈ Icc ε b, incl hN (c₁ t) = incl hN (c₂ t) ∧
      derivWithin (incl hN ∘ c₁) (Icc a b) t = derivWithin (incl hN ∘ c₂) (Icc a b) t := by
  obtain ⟨-, hc₁, -⟩ := isGeodesic_iff.1 h₁
  obtain ⟨-, hc₂, -⟩ := isGeodesic_iff.1 h₂
  set I := Icc a b
  have uI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have hbI : b ∈ I := right_mem_Icc.2 hab.le
  set F₁ : ℝ → V × V := fun t => (incl hN (c₁ t), derivWithin (incl hN ∘ c₁) I t)
  set F₂ : ℝ → V × V := fun t => (incl hN (c₂ t), derivWithin (incl hN ∘ c₂) I t)
  have hF₁ : ContinuousOn F₁ I :=
    hc₁.continuousOn.prodMk (hc₁.derivWithin uI (m := 0) (by simp)).continuousOn
  have hF₂ : ContinuousOn F₂ I :=
    hc₂.continuousOn.prodMk (hc₂.derivWithin uI (m := 0) (by simp)).continuousOn
  have hFb : F₁ b = F₂ b := by
    show (incl hN (c₁ b), _) = (incl hN (c₂ b), _)
    rw [h0, h0']
  set σ := Morse.sliceAt hN (c₁ b)
  have hσ : incl hN (c₁ b) ∈ σ.φ.source := Morse.mem_sliceAt_source hN (c₁ b)
  set G : V × V → V × V := fun z => (z.2, fderiv ℝ (Morse.projRep σ) z.1 z.2 z.2)
  have hG : ContDiffAt ℝ 1 G (F₁ b) := by
    have hQ : ContDiffAt ℝ ∞ (fderiv ℝ (Morse.projRep σ)) (incl hN (c₁ b)) :=
      (Morse.contDiffAt_projRep σ (q := c₁ b) hσ).fderiv_right (m := ∞) (by simp)
    have h1 : ContDiffAt ℝ ∞ (fun z : V × V => fderiv ℝ (Morse.projRep σ) z.1) (F₁ b) :=
      ContDiffAt.comp (F₁ b) hQ contDiffAt_fst
    exact (contDiffAt_snd.prodMk ((h1.clm_apply contDiffAt_snd).clm_apply contDiffAt_snd)).of_le
      (by exact_mod_cast le_top)
  obtain ⟨K, U₀, hU₀, hK⟩ := hG.exists_lipschitzOnWith
  set U := U₀ ∩ σ.φ.source ×ˢ (univ : Set V)
  have hU : U ∈ 𝓝 (F₁ b) :=
    Filter.inter_mem hU₀ (prod_mem_nhds (σ.φ.open_source.mem_nhds hσ) univ_mem)
  have hU₂ : U ∈ 𝓝 (F₂ b) := hFb ▸ hU
  have e₁ : ∀ᶠ t in 𝓝[I] b, F₁ t ∈ U := (hF₁ b hbI).preimage_mem_nhdsWithin hU
  have e₂ : ∀ᶠ t in 𝓝[I] b, F₂ t ∈ U := (hF₂ b hbI).preimage_mem_nhdsWithin hU₂
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 (e₁.and e₂)
  set ε := max (b - δ / 2) a
  have hεb : ε < b := max_lt (by linarith) hab
  have haε : a ≤ ε := le_max_right _ _
  have hεa : b - δ / 2 ≤ ε := le_max_left _ _
  have hsub : Icc ε b ⊆ Metric.ball b δ ∩ I := fun t ht => by
    refine ⟨?_, haε.trans ht.1, ht.2⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hlift : ∀ {c : ℝ → Bridge.Sub hN}, BridgePrelude.IsGeodesic (conn (hN := hN)) c I →
      ∀ t ∈ Ioc ε b, incl hN (c t) ∈ σ.φ.source →
      HasDerivWithinAt (fun τ => (incl hN (c τ), derivWithin (incl hN ∘ c) I τ))
        (G (incl hN (c t), derivWithin (incl hN ∘ c) I t)) (Iic t) t := by
    intro c h t ht hsrc
    obtain ⟨-, hc, -⟩ := isGeodesic_iff.1 h
    have htI : t ∈ Ioc a b := ⟨haε.trans_lt ht.1, ht.2⟩
    have hf' : HasDerivWithinAt (incl hN ∘ c) (derivWithin (incl hN ∘ c) I t) I t :=
      ((hc.differentiableOn (by simp)) t (Ioc_subset_Icc_self htI)).hasDerivWithinAt
    have hg' : HasDerivWithinAt (derivWithin (incl hN ∘ c) I)
        (derivWithin (derivWithin (incl hN ∘ c) I) I t) I t :=
      (((hc.derivWithin uI (m := 1) (WithTop.coe_le_coe.2 le_top)).differentiableOn (by simp)) t
        (Ioc_subset_Icc_self htI)).hasDerivWithinAt
    rw [derivWithin_derivWithin_eq hab h (Ioc_subset_Icc_self htI) σ hsrc] at hg'
    exact (hf'.prodMk hg').mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem htI)
  have hloc : EqOn F₁ F₂ (Icc ε b) := by
    refine ODE_solution_unique_of_mem_Icc_left (v := fun _ => G) (s := fun _ => U) (K := K)
      (fun _ _ => hK.mono inter_subset_left) (hF₁.mono fun t ht => (hsub ht).2)
      (fun t ht => hlift h₁ t ht ((hδs (hsub (Ioc_subset_Icc_self ht))).1).2.1)
      (fun t ht => (hδs (hsub (Ioc_subset_Icc_self ht))).1)
      (hF₂.mono fun t ht => (hsub ht).2)
      (fun t ht => hlift h₂ t ht ((hδs (hsub (Ioc_subset_Icc_self ht))).2).2.1)
      (fun t ht => (hδs (hsub (Ioc_subset_Icc_self ht))).2) hFb
  exact ⟨ε, haε, hεb, fun t ht => ⟨congrArg Prod.fst (hloc ht), congrArg Prod.snd (hloc ht)⟩⟩

/-- Velocities at the same point, compared by `HEq`, are equal iff their images in `V` are. -/
theorem D_eq_of_heq {x y : Bridge.Sub hN} (hxy : x = y) {v : TangentSpace 𝓘(ℝ, Rn n) x}
    {w : TangentSpace 𝓘(ℝ, Rn n) y} (h : HEq v w) : D hN x v = D hN y w := by
  subst hxy
  rw [eq_of_heq h]

theorem heq_of_D_eq {x y : Bridge.Sub hN} (hxy : x = y) {v : TangentSpace 𝓘(ℝ, Rn n) x}
    {w : TangentSpace 𝓘(ℝ, Rn n) y} (h : D hN x v = D hN y w) : HEq v w := by
  subst hxy
  exact heq_of_eq (D_injective x h)

/-! Changing the model `Z` to `ℝ^{dim Z}` (copied from `Items/V7_28.lean`). -/

/-- A linear equivalence `Z ≃ ℝᵐ`, `m = dim Z`. -/
noncomputable def eZ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] :
    Z ≃L[ℝ] Bridge.Rn (Module.finrank ℝ Z) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

/-- A slice chart modelled on `Z`, read in `ℝᵐ`. -/
noncomputable def chartRn {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) :
    Milnor.SliceChart 𝓘(ℝ, V) (Bridge.Rn (Module.finrank ℝ Z)) W N where
  φ := σ.φ.trans
    ((eZ Z).prodCongr (ContinuousLinearEquiv.refl ℝ W)).toDiffeomorph.toPartialDiffeomorph
  x₀ := σ.x₀
  x₀_mem := σ.x₀_mem
  x₀_source := ⟨σ.x₀_source, trivial⟩
  slice := fun p hp => σ.slice p hp.1

theorem isSliceRn {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn (Module.finrank ℝ Z)) W N :=
  fun p hp => ⟨chartRn (hN p hp).choose, ⟨(hN p hp).choose_spec, trivial⟩⟩

theorem tangentSubspace_rn {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (q : N) :
    Morse.tangentSubspace (isSliceRn hN) q = Morse.tangentSubspace hN q := by
  obtain ⟨σ, hσ⟩ := hN q q.2
  rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam (isSliceRn hN) (chartRn σ) ⟨hσ, trivial⟩,
    Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ]
  have e1 : Morse.sliceParam (chartRn σ) = Morse.sliceParam σ ∘ (eZ Z).symm := rfl
  have e2 : ((chartRn σ).φ q).1 = eZ Z (σ.φ q).1 := rfl
  rw [e1, e2, ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearEquiv.symm_apply_apply]
  exact LinearMap.range_comp_of_range_eq_top
    ((fderiv ℝ (Morse.sliceParam σ) (σ.φ q).1 : Z →L[ℝ] V) : Z →ₗ[ℝ] V)
    (LinearMap.range_eq_top.2 (eZ Z).symm.surjective)

theorem isGeodesicOn_rn {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {γ : ℝ → V} {s : Set ℝ}
    (h : Morse.IsGeodesicOn hN γ s) : Morse.IsGeodesicOn (isSliceRn hN) γ s :=
  ⟨h.isOpen, h.mem, h.contDiffOn, fun t ht => by
    rw [tangentSubspace_rn]
    exact h.normal t ht⟩

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
    ∀ (c c' : ℝ → Bridge.Sub hN) (s : Set ℝ), IsGeodesic (Bridge.conn (hN := hN)) c s →
      IsGeodesic (Bridge.conn (hN := hN)) c' s →
      ∀ t₀ ∈ s, c t₀ = c' t₀ → HEq (vel (n := n) c s t₀) (vel (n := n) c' s t₀) → Set.EqOn c c' s

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds** (uses A's `eqOn`). -/
theorem A_to_B_emb (hA : A) : B_emb := by
  intro V _ _ _ W _ _ _ n N hN c₁ c₂ s h₁ h₂ t₀ ht₀ h0 hv
  have h₁' : BridgePrelude.IsGeodesic (Bridge.conn (hN := hN)) c₁ s := h₁
  have h₂' : BridgePrelude.IsGeodesic (Bridge.conn (hN := hN)) c₂ s := h₂
  obtain ⟨hs, hc₁, hg₁⟩ := Emb.isGeodesic_iff_interior.1 h₁'
  obtain ⟨-, hc₂, hg₂⟩ := Emb.isGeodesic_iff_interior.1 h₂'
  have hd0 : derivWithin (Bridge.incl hN ∘ c₁) s t₀ = derivWithin (Bridge.incl hN ∘ c₂) s t₀ := by
    rw [← Bridge.D_vel (Bridge.isSmoothCurve_iff.2 hc₁) hs.2 ht₀,
      ← Bridge.D_vel (Bridge.isSmoothCurve_iff.2 hc₂) hs.2 ht₀]
    exact Emb.D_eq_of_heq h0 hv
  -- an interior time at which the data agree
  have key : ∃ t₁ ∈ interior s, (Bridge.incl hN ∘ c₁) t₁ = (Bridge.incl hN ∘ c₂) t₁ ∧
      deriv (Bridge.incl hN ∘ c₁) t₁ = deriv (Bridge.incl hN ∘ c₂) t₁ := by
    by_cases hint : t₀ ∈ interior s
    · refine ⟨t₀, hint, congrArg (Bridge.incl hN) h0, ?_⟩
      rw [← Emb.derivWithin_eq_deriv hint, ← Emb.derivWithin_eq_deriv hint, hd0]
    obtain ⟨u, ⟨-, hu⟩, hne⟩ :=
      accPt_iff_nhds.1 (uniqueDiffWithinAt_iff_accPt.1 (hs.2 t₀ ht₀)) univ univ_mem
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hsub : Icc u t₀ ⊆ s := hs.1.out hu ht₀
      obtain ⟨g₁, e₁⟩ := Emb.isGeodesic_restrict hlt hsub h₁'
      obtain ⟨g₂, e₂⟩ := Emb.isGeodesic_restrict hlt hsub h₂'
      have hb : t₀ ∈ Icc u t₀ := right_mem_Icc.2 hlt.le
      obtain ⟨ε, huε, hεt, hloc⟩ :=
        Emb.loc_left hlt g₁ g₂ h0 (by rw [e₁ t₀ hb, e₂ t₀ hb, hd0])
      have ht₁ : (ε + t₀) / 2 ∈ Ioo u t₀ := ⟨by linarith, by linarith⟩
      have ht₁s : (ε + t₀) / 2 ∈ interior s :=
        interior_maximal (Ioo_subset_Icc_self.trans hsub) isOpen_Ioo ht₁
      have ht₁I : (ε + t₀) / 2 ∈ interior (Icc u t₀) := by rw [interior_Icc]; exact ht₁
      obtain ⟨hp, hd⟩ := hloc ((ε + t₀) / 2) ⟨by linarith, by linarith⟩
      refine ⟨(ε + t₀) / 2, ht₁s, hp, ?_⟩
      rw [← Emb.derivWithin_eq_deriv ht₁I, ← Emb.derivWithin_eq_deriv ht₁I]
      exact hd
    · have hsub : Icc t₀ u ⊆ s := hs.1.out ht₀ hu
      obtain ⟨g₁, e₁⟩ := Emb.isGeodesic_restrict hlt hsub h₁'
      obtain ⟨g₂, e₂⟩ := Emb.isGeodesic_restrict hlt hsub h₂'
      have ha : t₀ ∈ Icc t₀ u := left_mem_Icc.2 hlt.le
      obtain ⟨ε, htε, hεu, hloc⟩ :=
        Emb.loc_right hlt g₁ g₂ h0 (by rw [e₁ t₀ ha, e₂ t₀ ha, hd0])
      have ht₁ : (t₀ + ε) / 2 ∈ Ioo t₀ u := ⟨by linarith, by linarith⟩
      have ht₁s : (t₀ + ε) / 2 ∈ interior s :=
        interior_maximal (Ioo_subset_Icc_self.trans hsub) isOpen_Ioo ht₁
      have ht₁I : (t₀ + ε) / 2 ∈ interior (Icc t₀ u) := by rw [interior_Icc]; exact ht₁
      obtain ⟨hp, hd⟩ := hloc ((t₀ + ε) / 2) ⟨by linarith, by linarith⟩
      refine ⟨(t₀ + ε) / 2, ht₁s, hp, ?_⟩
      rw [← Emb.derivWithin_eq_deriv ht₁I, ← Emb.derivWithin_eq_deriv ht₁I]
      exact hd
  obtain ⟨t₁, ht₁, hp, hd⟩ := key
  have hpre : IsPreconnected (interior s) := isPreconnected_iff_ordConnected.2 hs.1.interior
  have heq := hA.2 hg₁ hg₂ hpre ht₁ hp hd
  intro t ht
  apply Subtype.ext
  have := Emb.eqOn_of_interior hs
    (h := fun t => (Bridge.incl hN ∘ c₁) t - (Bridge.incl hN ∘ c₂) t) (x := 0)
    (hc₁.continuousOn.sub hc₂.continuousOn) (fun t ht => sub_eq_zero.2 (heq ht)) t ht
  exact sub_eq_zero.1 this

/-- B_emb gives A's `eqOn` for slice submanifolds modelled on `ℝⁿ`. -/
theorem eqOn_of_B_emb (hB : B_emb) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {n : ℕ} {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}
    {s : Set ℝ} {γ₁ γ₂ : ℝ → V} (h₁ : Morse.IsGeodesicOn hN γ₁ s)
    (h₂ : Morse.IsGeodesicOn hN γ₂ s) (hs : IsPreconnected s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (h0 : γ₁ t₀ = γ₂ t₀) (h0' : deriv γ₁ t₀ = deriv γ₂ t₀) : EqOn γ₁ γ₂ s := by
  have hoc : s.OrdConnected := isPreconnected_iff_ordConnected.1 hs
  have us : UniqueDiffOn ℝ s := h₁.isOpen.uniqueDiffOn
  let q : Bridge.Sub hN := ⟨γ₁ t₀, h₁.mem t₀ ht₀⟩
  have e₁ : EqOn (Bridge.incl hN ∘ Bridge.lift γ₁ q) γ₁ s :=
    fun t ht => Bridge.incl_lift q (h₁.mem t ht)
  have e₂ : EqOn (Bridge.incl hN ∘ Bridge.lift γ₂ q) γ₂ s :=
    fun t ht => Bridge.incl_lift q (h₂.mem t ht)
  have g₁ := (Bridge.isGeodesic_iff_isGeodesicOn h₁.isOpen hoc).2 (h₁.congr e₁.symm)
  have g₂ := (Bridge.isGeodesic_iff_isGeodesicOn h₂.isOpen hoc).2 (h₂.congr e₂.symm)
  have hc0 : Bridge.lift γ₁ q t₀ = Bridge.lift γ₂ q t₀ :=
    Subtype.ext ((e₁ ht₀).trans (h0.trans (e₂ ht₀).symm))
  have hd : ∀ {γ : ℝ → V}, Morse.IsGeodesicOn hN γ s → EqOn (Bridge.incl hN ∘ Bridge.lift γ q) γ s →
      derivWithin (Bridge.incl hN ∘ Bridge.lift γ q) s t₀ = deriv γ t₀ := fun h e => by
    rw [derivWithin_congr e (e ht₀)]
    exact (h.hasDerivAt ht₀).hasDerivWithinAt.derivWithin (us t₀ ht₀)
  have dv₁ : Bridge.D hN (Bridge.lift γ₁ q t₀) (vel (n := n) (Bridge.lift γ₁ q) s t₀) =
      deriv γ₁ t₀ :=
    (Bridge.D_vel (Bridge.isSmoothCurve_iff.2 (Bridge.isGeodesic_iff.1 g₁).2.1) us ht₀).trans
      (hd h₁ e₁)
  have dv₂ : Bridge.D hN (Bridge.lift γ₂ q t₀) (vel (n := n) (Bridge.lift γ₂ q) s t₀) =
      deriv γ₂ t₀ :=
    (Bridge.D_vel (Bridge.isSmoothCurve_iff.2 (Bridge.isGeodesic_iff.1 g₂).2.1) us ht₀).trans
      (hd h₂ e₂)
  have hv := Emb.heq_of_D_eq hc0 (dv₁.trans (h0'.trans dv₂.symm))
  have key := hB V W n N hN (Bridge.lift γ₁ q) (Bridge.lift γ₂ q) s g₁ g₂ t₀ ht₀ hc0 hv
  intro t ht
  exact (e₁ ht).symm.trans ((congrArg (Bridge.incl hN) (key ht)).trans (e₂ ht))

/-- **B on embedded manifolds implies A** (all of it, for any model `Z`, through `ℝ^{dim Z}`). -/
theorem B_emb_to_A (hB : B_emb) : A := by
  have heqOn : type_of% @Morse.IsGeodesicOn.eqOn.{0,0,0} := by
    intro V _ _ Z _ _ W _ _ N hN _ _ _ s γ₁ γ₂ h₁ h₂ hs t₀ ht₀ h0 h0'
    exact eqOn_of_B_emb hB (Emb.isGeodesicOn_rn h₁) (Emb.isGeodesicOn_rn h₂) hs ht₀ h0 h0'
  refine ⟨?_, heqOn⟩
  intro V _ _ Z _ _ W _ _ N hN _ _ _ γ₁ γ₂ s₁ s₂ h₁ h₂ t₀ ht₁ ht₂ h0 h0'
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 (h₁.isOpen.inter h₂.isOpen) t₀ ⟨ht₁, ht₂⟩
  have := heqOn (h₁.mono Metric.isOpen_ball fun t ht => (hsub ht).1)
    (h₂.mono Metric.isOpen_ball fun t ht => (hsub ht).2) (convex_ball t₀ r).isPreconnected
    (Metric.mem_ball_self hr) h0 h0'
  exact Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds t₀ hr) this

#rt_check RoundTrip.V7_5.A_to_B_emb [Morse.IsGeodesicOn.eventuallyEq, Morse.IsGeodesicOn.eqOn]
#rt_check RoundTrip.V7_5.B_emb_to_A [Morse.IsGeodesicOn.eventuallyEq, Morse.IsGeodesicOn.eqOn]
#rt_overlap RoundTrip.V7_5.B_emb_to_A [Morse.IsGeodesicOn.eventuallyEq, Morse.IsGeodesicOn.eqOn]

/-- **B ⇒ A** (revised: possible now that `RoundTrip/Bridge.lean` packages `↥N` as a Riemannian
manifold): specialize B to `↥N` with the induced connection, then `B_emb_to_A`. -/
theorem B_to_A : B → A := fun hB => B_emb_to_A (B_to_B_emb hB)

#rt_check RoundTrip.V7_5.B_to_A [Morse.IsGeodesicOn.eventuallyEq, Morse.IsGeodesicOn.eqOn]
#rt_overlap RoundTrip.V7_5.B_to_A [Morse.IsGeodesicOn.eventuallyEq, Morse.IsGeodesicOn.eqOn]

end RoundTrip.V7_5
