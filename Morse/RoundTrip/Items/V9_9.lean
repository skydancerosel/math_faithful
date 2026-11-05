import Morse
import RoundTrip.Check
import RoundTrip.Blind.V9_9
import RoundTrip.Bridge

open Set Filter Topology Function
open scoped ContDiff Manifold

namespace RoundTrip.V9_9

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V` with the
induced metric: (1) the uniform local geodesic flow `exists_smooth_ray`; (2) a geodesic segment
`γ|[0,1]` is the radial geodesic `t ↦ exp_{γ(0)}(t γ'(0))` on an open interval containing `[0,1]`;
(3) smooth dependence of radial geodesics on initial data over a compact interval
(`raysGood_of_isGeodesicOn`, with the vocabulary `Morse.RaysGood`); (4) **Lemma 14.4**: every
Jacobi field `J` along a geodesic `γ : [0,1] → N` (smooth on `[0,1]`, geodesic on `(0,1)`) is
`t ↦ ∂α/∂u (0,t)` on `[0,1]` for some `α` smooth on `(−ε, ε) ×ˢ [0,1]`, with values in `N`, each
`α(u, ·)` a geodesic on `(0,1)` and `α(0, ·) = γ` on `[0,1]`. -/
def A : Prop :=
  type_of% @Morse.exists_smooth_ray.{0,0,0} ∧ type_of% @Morse.exists_initial_ray.{0,0,0} ∧
    type_of% @Morse.raysGood_of_isGeodesicOn.{0,0,0} ∧ type_of% @Morse.lemma_14_4.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.exists_smooth_ray, @Morse.exists_initial_ray, @Morse.raysGood_of_isGeodesicOn,
    @Morse.lemma_14_4⟩

/-! Neither `A → B` nor `B → A` is proved; see `V9_9.json`. -/

/-! ## The embedded special case: dictionary -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

theorem intv_Icc : RoundTrip.BridgePrelude.IsIntv (Icc (0 : ℝ) 1) :=
  ⟨ordConnected_Icc, uniqueDiffOn_Icc zero_lt_one⟩

theorem prj_incl (x : Bridge.Sub hN) : Morse.prj hN (incl hN x) = P hN x := Morse.prj_of_mem hN x.2

/-- The ambient field of `D/dt U` (derivative within `s`). -/
theorem ambA_covA (γ : ℝ → Bridge.Sub hN) (s : Set ℝ) (U : FA n γ) (t : ℝ) :
    ambA γ (covA γ s U) t = P hN (γ t) (derivWithin (ambA γ U) s t) := D_covA γ s U t

theorem contDiffOn_ambA_covA {γ : ℝ → Bridge.Sub hN} (hc : IsSmoothCurve (n := n) γ (Icc 0 1))
    {U : FA n γ} (hU : ContDiffOn ℝ ∞ (ambA γ U) (Icc 0 1)) :
    ContDiffOn ℝ ∞ (ambA γ (covA γ (Icc 0 1) U)) (Icc 0 1) := by
  have hc' : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) ∞ γ (Icc 0 1) := hc
  have hP : ContDiffOn ℝ ∞ (fun t => P hN (γ t)) (Icc 0 1) :=
    contMDiffOn_iff_contDiffOn.1 (contMDiff_P.comp_contMDiffOn hc')
  have hd : ContDiffOn ℝ ∞ (derivWithin (ambA γ U) (Icc 0 1)) (Icc 0 1) :=
    hU.derivWithin (uniqueDiffOn_Icc zero_lt_one) (by simp)
  exact (hP.clm_apply hd).congr fun t _ => ambA_covA γ _ U t

/-- **Dictionary: Jacobi fields (blind ⇒ project).** -/
theorem isJacobiField_of_isJacobi {γ : ℝ → Bridge.Sub hN} (hc : IsSmoothCurve (n := n) γ (Icc 0 1))
    {J : FA n γ} (hJ : IsJacobi (Bridge.conn (hN := hN)) γ (Icc 0 1) J) :
    Morse.IsJacobiField hN (incl hN ∘ γ) (ambA γ J) := by
  obtain ⟨J', J'', h1, h2, h3⟩ := hJ
  have hs := intv_Icc
  have h1' := (hasCovDeriv_iff' hs hc).1 h1
  have h2' := (hasCovDeriv_iff' hs hc).1 h2
  have hJs := (isSmoothAlong_iff.1 h1'.1).2
  refine ⟨hJs, fun t _ => ?_, fun t ht => ?_⟩
  · rw [comp_apply, prj_incl]
    exact P_D (γ t) (J t)
  · have ht' : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    have hnhds : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hcov : Morse.covD hN (incl hN ∘ γ) (ambA γ J) =ᶠ[𝓝 t] ambA γ J' := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
      rw [h1'.2 x hx', Morse.covD, derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2), comp_apply,
        prj_incl]
    have e1 : Morse.covD hN (incl hN ∘ γ) (Morse.covD hN (incl hN ∘ γ) (ambA γ J)) t =
        ambA γ J'' t := by
      rw [Morse.covD, hcov.deriv_eq, h2'.2 t ht', derivWithin_of_mem_nhds hnhds, comp_apply,
        prj_incl]
    obtain ⟨r, hr, hr0⟩ := h3 t ht'
    have hr' := (isCurvVal_iff (γ t) (vel (n := n) γ (Icc 0 1) t) (J t)
      (vel (n := n) γ (Icc 0 1) t) r).1 hr
    have hv : D hN (γ t) (vel (n := n) γ (Icc 0 1) t) = deriv (incl hN ∘ γ) t :=
      (D_vel hc (uniqueDiffOn_Icc zero_lt_one) ht').trans (derivWithin_of_mem_nhds hnhds)
    rw [Morse.jacobiExpr, e1]
    have := congrArg (D hN (γ t)) hr0
    rw [D_tadd, D_tzero, hr', hv] at this
    exact this

/-- **Dictionary: Jacobi fields (project ⇒ blind)**, using that the Jacobi expression is
continuous on `[0, 1]` (so the equation on `(0, 1)` extends to the end points). -/
theorem isJacobi_of_isJacobiField {γ : ℝ → Bridge.Sub hN} (hc : IsSmoothCurve (n := n) γ (Icc 0 1))
    {J : FA n γ} (hJ : Morse.IsJacobiField hN (incl hN ∘ γ) (ambA γ J)) :
    IsJacobi (Bridge.conn (hN := hN)) γ (Icc 0 1) J := by
  have hs := intv_Icc
  have uI : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hJ'c : ContDiffOn ℝ ∞ (ambA γ (covA γ (Icc 0 1) J)) (Icc 0 1) :=
    contDiffOn_ambA_covA hc hJ.contDiffOn
  have hJ''c : ContDiffOn ℝ ∞ (ambA γ (covA γ (Icc 0 1) (covA γ (Icc 0 1) J))) (Icc 0 1) :=
    contDiffOn_ambA_covA hc hJ'c
  have hJs : RoundTrip.BridgePrelude.IsSmoothAlong γ (Icc 0 1) J :=
    isSmoothAlong_iff.2 ⟨hc, hJ.contDiffOn⟩
  have hJ's : RoundTrip.BridgePrelude.IsSmoothAlong γ (Icc 0 1) (covA γ (Icc 0 1) J) :=
    isSmoothAlong_iff.2 ⟨hc, hJ'c⟩
  refine ⟨covA γ (Icc 0 1) J, covA γ (Icc 0 1) (covA γ (Icc 0 1) J),
    (hasCovDeriv_iff hs hc).2 ⟨hJs, fun t _ => rfl⟩,
    (hasCovDeriv_iff hs hc).2 ⟨hJ's, fun t _ => rfl⟩, fun t ht => ?_⟩
  have hcd : ContDiffOn ℝ ∞ (incl hN ∘ γ) (Icc 0 1) := isSmoothCurve_iff.1 hc
  have hvc : ContinuousOn (derivWithin (incl hN ∘ γ) (Icc 0 1)) (Icc 0 1) :=
    (hcd.derivWithin uI (m := ∞) (by simp)).continuousOn
  have hvT : ∀ τ ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) τ)
      (derivWithin (incl hN ∘ γ) (Icc 0 1) τ) = derivWithin (incl hN ∘ γ) (Icc 0 1) τ :=
    fun τ hτ => by
      rw [← D_vel hc uI hτ, comp_apply, prj_incl]
      exact P_D _ _
  -- the ambient Jacobi expression within `[0, 1]`
  set F : ℝ → V := fun τ => ambA γ (covA γ (Icc 0 1) (covA γ (Icc 0 1) J)) τ +
    Morse.curvR hN ((incl hN ∘ γ) τ) (derivWithin (incl hN ∘ γ) (Icc 0 1) τ) (ambA γ J τ)
      (derivWithin (incl hN ∘ γ) (Icc 0 1) τ) with hF
  have hF0 : EqOn F 0 (Ioo 0 1) := by
    intro τ hτ
    have hnhds : Icc (0 : ℝ) 1 ∈ 𝓝 τ := Icc_mem_nhds hτ.1 hτ.2
    have hcov : Morse.covD hN (incl hN ∘ γ) (ambA γ J) =ᶠ[𝓝 τ] ambA γ (covA γ (Icc 0 1) J) := by
      filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with x hx
      rw [ambA_covA, Morse.covD, derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2), comp_apply,
        prj_incl]
    have := hJ.eq τ hτ
    rw [Morse.jacobiExpr, Morse.covD, hcov.deriv_eq] at this
    simp only [hF, Pi.zero_apply]
    rw [ambA_covA, derivWithin_of_mem_nhds hnhds, derivWithin_of_mem_nhds hnhds]
    rw [comp_apply, prj_incl] at this
    exact this
  have hFc : ContinuousOn F (Icc 0 1) := by
    refine hJ''c.continuousOn.add fun τ hτ => ?_
    exact Morse.continuousWithinAt_curvR hN hτ (hcd.continuousOn τ hτ) (fun τ _ => (γ τ).2)
      (hvc τ hτ) (hJ.contDiffOn.continuousOn τ hτ) (hvc τ hτ) hvT hJ.tangent
  have hFI : EqOn F 0 (Icc 0 1) :=
    hF0.of_subset_closure hFc continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo zero_ne_one])
  have hvt : derivWithin (incl hN ∘ γ) (Icc 0 1) t = D hN (γ t) (vel (n := n) γ (Icc 0 1) t) :=
    (D_vel hc uI ht).symm
  have hRT : Morse.curvR hN ((incl hN ∘ γ) t) (derivWithin (incl hN ∘ γ) (Icc 0 1) t)
      (ambA γ J t) (derivWithin (incl hN ∘ γ) (Icc 0 1) t) ∈ Morse.tangentSubspace hN (γ t) := by
    have h := Morse.curvOp_mem hN (D_mem (γ t) (vel (n := n) γ (Icc 0 1) t)) (D_mem (γ t) (J t))
      (D_mem (γ t) (vel (n := n) γ (Icc 0 1) t))
    convert h using 1
    rw [hvt]
    exact Morse.curvR_of_mem hN (γ t).2 _ _ _
  refine ⟨L hN (γ t) (Morse.curvR hN ((incl hN ∘ γ) t) (derivWithin (incl hN ∘ γ) (Icc 0 1) t)
      (ambA γ J t) (derivWithin (incl hN ∘ γ) (Icc 0 1) t)),
    (isCurvVal_iff (γ t) (vel (n := n) γ (Icc 0 1) t) (J t) (vel (n := n) γ (Icc 0 1) t) _).2 ?_,
    ?_⟩
  · rw [D_L hRT, hvt]
    rfl
  · apply D_injective (γ t)
    refine (D_tadd (γ t) _ _).trans (Eq.trans ?_ (D_tzero (γ t)).symm)
    rw [D_L hRT]
    exact hFI ht

/-! ### Variations through geodesics -/

/-- Smoothness of maps from a normed space into `↥N`, read in `V` (Bridge's
`contMDiffWithinAt_curve_iff`, for any source space). -/
theorem contMDiffWithinAt_iff_incl {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} {x : E} :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s x ↔ ContDiffWithinAt ℝ ∞ (incl hN ∘ f) s x := by
  constructor
  · intro h
    exact contMDiffWithinAt_iff_contDiffWithinAt.1
      ((contMDiff_incl (f x)).comp_contMDiffWithinAt x h)
  · intro h
    have hcont : ContinuousWithinAt f s x :=
      (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := f)).2 h.continuousWithinAt
    rw [contMDiffWithinAt_iff_target]
    refine ⟨hcont, ?_⟩
    set σ := Morse.sliceAt hN (f x)
    have hφ : ContDiffAt ℝ ∞ (fun y => (σ.φ y).1) (incl hN (f x)) :=
      contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt
        (σ.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (f x))))
    have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) = (fun y => (σ.φ y).1) ∘ (incl hN ∘ f) := rfl
    rw [e]
    exact contMDiffWithinAt_iff_contDiffWithinAt.2 (hφ.comp_contDiffWithinAt x h)

/-- The unit vector of `ℝ¹`. -/
noncomputable abbrev e1 : Rn 1 := EuclideanSpace.single 0 (1 : ℝ)

theorem norm_smul_e1 (s : ℝ) : ‖s • e1‖ = |s| := by
  rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs]

theorem smul_e1_apply (s : ℝ) : (s • e1) 0 = s := by simp [e1]

theorem fderiv_e1 {G : Rn 1 → V} (hG : DifferentiableAt ℝ G 0) :
    fderiv ℝ G 0 e1 = deriv (fun s : ℝ => G (s • e1)) 0 := by
  have h := hG.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const e1)
    (by simp)
  rw [one_smul] at h
  exact h.deriv.symm

/-- For a fixed `t ∈ [0, 1]`, `u ↦ α(u, t)` is differentiable at `0`. -/
theorem mdiff_slice {ε : ℝ} (hε : 0 < ε) {α : Rn 1 → ℝ → Bridge.Sub hN}
    (h : ContMDiffOn 𝓘(ℝ, Rn 1 × ℝ) 𝓘(ℝ, Rn n) ∞ (fun x : Rn 1 × ℝ => α x.1 x.2)
      (Metric.ball (0 : Rn 1) ε ×ˢ Icc 0 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    MDifferentiableAt 𝓘(ℝ, Rn 1) 𝓘(ℝ, Rn n) (fun u => α u t) 0 := by
  have hg : ContMDiff 𝓘(ℝ, Rn 1) 𝓘(ℝ, Rn 1 × ℝ) ∞ (fun u : Rn 1 => (u, t)) :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  have h2 : ContMDiffOn 𝓘(ℝ, Rn 1) 𝓘(ℝ, Rn n) ∞ (fun u => α u t) (Metric.ball (0 : Rn 1) ε) :=
    h.comp hg.contMDiffOn (fun u hu => ⟨hu, ht⟩)
  exact (h2.contMDiffAt (Metric.ball_mem_nhds 0 hε)).mdifferentiableAt (by simp)

/-- The variation field, read in `V`, is the derivative of the ambient variation along `e₁`. -/
theorem D_varField {α : Rn 1 → ℝ → Bridge.Sub hN} {t : ℝ}
    (hd : MDifferentiableAt 𝓘(ℝ, Rn 1) 𝓘(ℝ, Rn n) (fun u => α u t) 0) :
    D hN (α 0 t) (varField (n := n) α 0 t) = deriv (fun s : ℝ => incl hN (α (s • e1) t)) 0 := by
  have hi : MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (incl hN) (α 0 t) :=
    (contMDiff_incl (α 0 t)).mdifferentiableAt (by simp)
  have hc := mfderiv_comp (0 : Rn 1) hi hd
  have hG : DifferentiableAt ℝ (fun u => incl hN (α u t)) 0 :=
    mdifferentiableAt_iff_differentiableAt.1 (hi.comp (0 : Rn 1) hd)
  rw [← fderiv_e1 hG, ← mfderiv_eq_fderiv]
  exact (DFunLike.congr_fun hc e1).symm

/-- A blind variation through geodesics, read in `V` along the line `s ↦ s e₁`. -/
theorem ambient_of_isGeodVar {ε : ℝ} (hε : 0 < ε) {α : Rn 1 → ℝ → Bridge.Sub hN}
    (hα : IsGeodVar (Bridge.conn (hN := hN)) ε α) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => incl hN (α (p.1 • e1) p.2)) (Ioo (-ε) ε ×ˢ Icc (0 : ℝ) 1) ∧
    (∀ u ∈ Ioo (-ε) ε, Morse.IsGeodesicOn hN (fun t => incl hN (α (u • e1) t)) (Ioo 0 1)) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, deriv (fun s : ℝ => incl hN (α (s • e1) t)) 0 =
      D hN (α 0 t) (varField (n := n) α 0 t) := by
  obtain ⟨h1, h2⟩ := hα
  have hmem : ∀ u ∈ Ioo (-ε) ε, u • e1 ∈ Metric.ball (0 : Rn 1) ε := fun u hu => by
    rw [mem_ball_zero_iff, norm_smul_e1, abs_lt]; exact hu
  refine ⟨?_, fun u hu => ?_, fun t ht => (D_varField (mdiff_slice hε h1 ht)).symm⟩
  · have hsm : ContDiffOn ℝ ∞ (fun x : Rn 1 × ℝ => incl hN (α x.1 x.2))
        (Metric.ball (0 : Rn 1) ε ×ˢ Icc 0 1) :=
      contMDiffOn_iff_contDiffOn.1 (contMDiff_incl.comp_contMDiffOn h1)
    have hg : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1 • e1, p.2)) :=
      (contDiff_fst.smul contDiff_const).prodMk contDiff_snd
    exact hsm.comp hg.contDiffOn fun p hp => ⟨hmem p.1 hp.1, hp.2⟩
  · exact isGeodesicOn_Ioo (h2 (u • e1) (hmem u hu))

/-- Lift an ambient family of curves to a blind family `ℝ¹ × ℝ → ↥N`. -/
noncomputable def liftVar (α : ℝ → ℝ → V) (q : Bridge.Sub hN) : Rn 1 → ℝ → Bridge.Sub hN :=
  fun u t => lift (α (u 0)) q t

/-- A project geodesic on `(0, 1)`, smooth on `[0, 1]`, lifts to a blind geodesic on `[0, 1]`. -/
theorem isGeodesic_lift_of {c : ℝ → V} (q : Bridge.Sub hN) (hc : ContDiffOn ℝ ∞ c (Icc 0 1))
    (hcN : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ N) (hgeo : Morse.IsGeodesicOn hN c (Ioo 0 1)) :
    IsGeodesic (Bridge.conn (hN := hN)) (lift c q) (Icc 0 1) := by
  have uI : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have heq : EqOn (incl hN ∘ lift c q) c (Icc 0 1) := fun t ht => incl_lift q (hcN t ht)
  have hd : EqOn (derivWithin (incl hN ∘ lift c q) (Icc 0 1)) (derivWithin c (Icc 0 1))
      (Icc 0 1) := fun t ht => derivWithin_congr heq (heq ht)
  have hdd : EqOn (derivWithin (derivWithin (incl hN ∘ lift c q) (Icc 0 1)) (Icc 0 1))
      (derivWithin (derivWithin c (Icc 0 1)) (Icc 0 1)) (Icc 0 1) :=
    fun t ht => derivWithin_congr hd (hd ht)
  have hG : EqOn (fun t => Morse.prj hN (c t) (derivWithin (derivWithin c (Icc 0 1)) (Icc 0 1) t))
      0 (Icc 0 1) := by
    refine EqOn.of_subset_closure (s := Ioo 0 1) ?_ ?_ continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo zero_ne_one])
    · intro t ht
      have hn : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
      have e1 : derivWithin c (Icc 0 1) =ᶠ[𝓝 t] deriv c := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
        exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
      simp only [Pi.zero_apply]
      rw [derivWithin_of_mem_nhds hn, e1.deriv_eq, Morse.prj_of_mem hN (hgeo.mem t ht)]
      exact hgeo.tanProj_deriv_deriv ht
    · exact (Morse.ContDiffOn.prj_comp hN hc hcN).continuousOn.clm_apply
        ((hc.derivWithin uI (m := ∞) (by simp)).derivWithin uI (m := ∞) (by simp)).continuousOn
  refine (isGeodesic_iff (c := lift c q) (s := Icc 0 1)).2 ⟨intv_Icc, hc.congr heq, fun t ht => ?_⟩
  rw [hdd ht]
  have := hG ht
  simp only [Pi.zero_apply, Morse.prj_of_mem hN (hcN t ht)] at this
  rw [lift_of_mem q (hcN t ht)]
  exact this

/-- An ambient smooth variation through project geodesics lifts to a blind variation through
geodesics, with the same variation field. -/
theorem isGeodVar_of_ambient {ε : ℝ} (hε : 0 < ε) {α : ℝ → ℝ → V} (q : Bridge.Sub hN)
    (hsm : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => α p.1 p.2) (Ioo (-ε) ε ×ˢ Icc (0 : ℝ) 1))
    (hαN : ∀ u ∈ Ioo (-ε) ε, ∀ t ∈ Icc (0 : ℝ) 1, α u t ∈ N)
    (hgeo : ∀ u ∈ Ioo (-ε) ε, Morse.IsGeodesicOn hN (α u) (Ioo 0 1)) :
    IsGeodVar (Bridge.conn (hN := hN)) ε (liftVar α q) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, incl hN (liftVar α q 0 t) = α 0 t) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, D hN (liftVar α q 0 t) (varField (n := n) (liftVar α q) 0 t) =
      deriv (fun u => α u t) 0 := by
  have hb : ∀ x : Rn 1, x ∈ Metric.ball (0 : Rn 1) ε → x 0 ∈ Ioo (-ε) ε := fun x hx => by
    rw [mem_ball_zero_iff] at hx
    exact abs_lt.1 (lt_of_le_of_lt (by simpa using PiLp.norm_apply_le x 0) hx)
  have hz : (0 : Rn 1) 0 = 0 := by simp
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  -- smoothness
  have hsm' : ContDiffOn ℝ ∞ (fun x : Rn 1 × ℝ => α (x.1 0) x.2)
      (Metric.ball (0 : Rn 1) ε ×ˢ Icc 0 1) := by
    have hg : ContDiff ℝ ∞ (fun x : Rn 1 × ℝ => ((EuclideanSpace.proj (0 : Fin 1) : Rn 1 →L[ℝ] ℝ) x.1, x.2)) :=
      ((EuclideanSpace.proj (0 : Fin 1) : Rn 1 →L[ℝ] ℝ).contDiff.comp contDiff_fst).prodMk contDiff_snd
    exact hsm.comp hg.contDiffOn fun x hx => ⟨hb x.1 hx.1, hx.2⟩
  have hC : ContMDiffOn 𝓘(ℝ, Rn 1 × ℝ) 𝓘(ℝ, Rn n) ∞ (fun x : Rn 1 × ℝ => liftVar α q x.1 x.2)
      (Metric.ball (0 : Rn 1) ε ×ˢ Icc 0 1) := fun x hx =>
    contMDiffWithinAt_iff_incl.2 ((hsm' x hx).congr (fun y hy => incl_lift q (hαN _ (hb y.1 hy.1) _ hy.2))
      (incl_lift q (hαN _ (hb x.1 hx.1) _ hx.2)))
  refine ⟨⟨hC, fun u hu => ?_⟩, fun t ht => ?_, fun t ht => ?_⟩
  · have hu' := hb u hu
    exact isGeodesic_lift_of q (hsm.comp (contDiffOn_const.prodMk contDiffOn_id)
      fun t ht => ⟨hu', ht⟩) (hαN _ hu') (hgeo _ hu')
  · show incl hN (lift (α ((0 : Rn 1) 0)) q t) = α 0 t
    rw [hz]; exact incl_lift q (hαN 0 h0 t ht)
  · rw [D_varField (mdiff_slice hε hC ht)]
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioo_mem_nhds (show -ε < (0 : ℝ) by linarith) hε] with s hs
    show incl hN (lift (α ((s • e1) 0)) q t) = α s t
    rw [smul_e1_apply]
    exact incl_lift q (hαN s hs t ht)

/-- A copy of the (trivial) fact that a Jacobi field along `γ` only depends on `γ|[0,1]`
(copied from `Items/V9_8.lean`). -/
theorem congr_curve' {γ γ' J : ℝ → V} (hJ : Morse.IsJacobiField hN γ J)
    (heq : EqOn γ γ' (Icc 0 1)) : Morse.IsJacobiField hN γ' J where
  contDiffOn := hJ.contDiffOn
  tangent t ht := by rw [← heq ht]; exact hJ.tangent t ht
  eq t ht := by
    have hev : γ =ᶠ[𝓝 t] γ' := eventually_of_mem (Icc_mem_nhds ht.1 ht.2) heq
    have hcov : ∀ X : ℝ → V, Morse.covD hN γ X =ᶠ[𝓝 t] Morse.covD hN γ' X := fun X => by
      filter_upwards [eventually_eventually_nhds.2 hev] with x hx
      rw [Morse.covD, Morse.covD, hx.self_of_nhds]
    have h1 : deriv (Morse.covD hN γ J) t = deriv (Morse.covD hN γ' J) t := (hcov J).deriv_eq
    have h2 : γ t = γ' t := hev.self_of_nhds
    have h3 : deriv γ t = deriv γ' t := hev.deriv_eq
    have := hJ.eq t ht
    rw [Morse.jacobiExpr] at this ⊢
    change Morse.prj hN (γ t) (deriv (Morse.covD hN γ J) t) +
      Morse.curvR hN (γ t) (deriv γ t) (J t) (deriv γ t) = 0 at this
    change Morse.prj hN (γ' t) (deriv (Morse.covD hN γ' J) t) +
      Morse.curvR hN (γ' t) (deriv γ' t) (J t) (deriv γ' t) = 0
    rw [← h1, ← h2, ← h3]
    exact this

end Emb

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, connected) with the induced metric and the
induced Levi-Civita connection `Bridge.conn` (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) Y N) [ConnectedSpace (Bridge.Sub hN)]
    (γ : ℝ → Bridge.Sub hN), IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
    ∀ J : FA n γ, IsJacobi (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J →
      ∃ (ε : ℝ) (α : Rn 1 → ℝ → Bridge.Sub hN), 0 < ε ∧ IsGeodVar (Bridge.conn (hN := hN)) ε α ∧
        (∀ t ∈ Set.Icc (0:ℝ) 1, α 0 t = γ t) ∧
        ∀ t ∈ Set.Icc (0:ℝ) 1, HEq (J t) (varField (n := n) α 0 t)

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- A's Lemma 14.4 for connected slice submanifolds modelled on `ℝⁿ` (the part of A that `B_emb`
covers). -/
def A_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) Y N) [ConnectedSpace (Bridge.Sub hN)]
    (γ : ℝ → V), Morse.IsSmoothCurveIn hN γ → Morse.IsGeodesicOn hN γ (Ioo 0 1) →
    ∀ J : ℝ → V, Morse.IsJacobiField hN γ J →
      ∃ ε > 0, ∃ α : ℝ → ℝ → V,
        ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => α p.1 p.2) (Ioo (-ε) ε ×ˢ Icc (0 : ℝ) 1) ∧
        (∀ u ∈ Ioo (-ε) ε, ∀ t ∈ Icc (0 : ℝ) 1, α u t ∈ N) ∧
        (∀ u ∈ Ioo (-ε) ε, Morse.IsGeodesicOn hN (α u) (Ioo 0 1)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, deriv (fun u => α u t) 0 = J t

theorem A_to_A_emb : A → A_emb := fun hA _ _ _ _ _ _ _ _ _ _ _ _ _ hc hgeo _ hJ =>
  hA.2.2.2 hc hgeo hJ

open Emb Bridge in
/-- **A implies B on embedded manifolds** (uses A's `lemma_14_4`, through the Jacobi-field and
variation dictionaries of `Emb`). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ Y _ _ _ n N hN _ γ hγ J hJ
  have hc : Morse.IsSmoothCurveIn hN (incl hN ∘ γ) :=
    ⟨isSmoothCurve_iff.1 hγ.2.1, fun t _ => (γ t).2⟩
  obtain ⟨ε, hε, α, hsm, hαN, hgeo, h0, hder⟩ :=
    hA.2.2.2 hc (isGeodesicOn_Ioo hγ) (isJacobiField_of_isJacobi hγ.2.1 hJ)
  obtain ⟨hvar, hincl, hD⟩ := isGeodVar_of_ambient hε (γ 0) hsm hαN hgeo
  have e : ∀ t ∈ Icc (0 : ℝ) 1, liftVar α (γ 0) 0 t = γ t := fun t ht =>
    Subtype.ext ((hincl t ht).trans (h0 t ht))
  refine ⟨ε, liftVar α (γ 0), hε, hvar, e, fun t ht => heq_of_eq ?_⟩
  apply D_injective (γ t)
  calc D hN (γ t) (J t) = deriv (fun u => α u t) 0 := (hder t ht).symm
    _ = D hN (liftVar α (γ 0) 0 t) (varField (n := n) (liftVar α (γ 0)) 0 t) := (hD t ht).symm
    _ = D hN (γ t) (varField (n := n) (liftVar α (γ 0)) 0 t) :=
      congrArg (fun x => D hN x (varField (n := n) (liftVar α (γ 0)) 0 t)) (e t ht)

open Emb Bridge in
/-- **B implies A's Lemma 14.4** for connected slice submanifolds modelled on `ℝⁿ`, by
specializing B to `↥N` and reading the variation in `V` along `s ↦ s e₁`. -/
theorem B_to_A_emb : B → A_emb := by
  intro hB V _ _ _ Y _ _ _ n N hN _ γ hc hgeo J hJ
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  set q : Bridge.Sub hN := ⟨γ 0, hc.mem 0 h0I⟩
  have hγ' : IsGeodesic (Bridge.conn (hN := hN)) (lift γ q) (Icc 0 1) :=
    isGeodesic_lift_of q hc.contDiffOn hc.mem hgeo
  set J' : FA n (lift γ q) := fun t => L hN (lift γ q t) (J t)
  have hJT : ∀ t ∈ Icc (0 : ℝ) 1, ambA (lift γ q) J' t = J t := fun t ht => by
    have h1 : P hN (lift γ q t) (J t) = J t := by
      rw [← prj_incl, incl_lift q (hc.mem t ht)]
      exact hJ.tangent t ht
    show D hN (lift γ q t) (L hN (lift γ q t) (J t)) = J t
    rw [← h1, D_L_P]
  have hJ' : Morse.IsJacobiField hN (incl hN ∘ lift γ q) (ambA (lift γ q) J') :=
    (congr_curve' hJ fun t ht => (incl_lift q (hc.mem t ht)).symm).congr
      fun t ht => (hJT t ht).symm
  obtain ⟨ε, α, hε, hvar, h0, hheq⟩ := B_to_B_emb hB V Y n N hN (lift γ q) hγ' J'
    (isJacobi_of_isJacobiField hγ'.2.1 hJ')
  obtain ⟨hsm, hgeo', hder⟩ := ambient_of_isGeodVar hε hvar
  refine ⟨ε, hε, fun s t => incl hN (α (s • e1) t), hsm, fun u _ t _ => (α (u • e1) t).2, hgeo',
    fun t ht => ?_, fun t ht => ?_⟩
  · show incl hN (α ((0 : ℝ) • e1) t) = γ t
    rw [zero_smul, h0 t ht]
    exact incl_lift q (hc.mem t ht)
  · show deriv (fun s : ℝ => incl hN (α (s • e1) t)) 0 = J t
    rw [hder t ht, ← hJT t ht]
    show D hN (α 0 t) (varField (n := n) α 0 t) = D hN (lift γ q t) (J' t)
    rw [← eq_of_heq (hheq t ht)]
    exact congrArg (fun x => D hN x (J' t)) (h0 t ht)

#rt_check RoundTrip.V9_9.A_to_B_emb [Morse.exists_smooth_ray, Morse.exists_initial_ray,
  Morse.raysGood_of_isGeodesicOn, Morse.lemma_14_4]
#rt_check RoundTrip.V9_9.B_to_A_emb [Morse.exists_smooth_ray, Morse.exists_initial_ray,
  Morse.raysGood_of_isGeodesicOn, Morse.lemma_14_4]
#rt_overlap RoundTrip.V9_9.B_to_A_emb [Morse.exists_smooth_ray, Morse.exists_initial_ray,
  Morse.raysGood_of_isGeodesicOn, Morse.lemma_14_4]

end RoundTrip.V9_9
