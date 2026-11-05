import Morse.Chapter9.IndexForm
import Morse.Chapter7.GeodesicFlow

/-!
Milnor, *Morse Theory*, §14, pp. 79–82: Lemma 14.3 (variations through geodesics give Jacobi
fields) and Remark 14.5 (in a normal neighbourhood, Jacobi fields are determined by their values
at the end points of a geodesic segment), for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# Jacobi fields and families of geodesics

## Milnor's text, paraphrased

* (p. 79) Let `α : (−ε, ε) × [0, 1] → M` be a `C^∞` map with `α(0, t) = γ(t)` such that each
  `ᾱ(u) = α(u, ·)` is a geodesic (a *variation of `γ` through geodesics*; the end points need not
  be fixed).
* **Lemma 14.3** (p. 80): the variation vector field `W(t) = ∂α/∂u (0, t)` is then a Jacobi field.
  Proof: `D/∂t ∂α/∂t ≡ 0`; apply `D/∂u` and use Lemmas 9.2 and 8.7:
  `0 = D/∂t D/∂t ∂α/∂u + R(∂α/∂t, ∂α/∂u) ∂α/∂t`.
* **Remark 14.5** (pp. 81–82): in a neighbourhood `U` as in the proof of Lemma 14.4 (any two
  points joined by a unique minimal geodesic depending differentiably on them), the Jacobi fields
  along a geodesic segment in `U` are uniquely determined by their values at the end points.

## In the embedded setting

* `Morse.lemma_14_3`: for `α` smooth on `(−ε, ε) × [0, 1]`, with values in `N`, each `α(u, ·)` a
  geodesic on `(0, 1)`: `t ↦ ∂α/∂u (0, t)` is a Jacobi field along `α(0, ·)` (from
  `Morse.curvature_identity`, the embedded form of Lemmas 8.7 and 9.2).
* `Morse.remark_14_5_of_isNormalRadius`: if `ε` is a normal radius at `q` (`exp_q` maps the
  `ε`-ball of `T_qN` diffeomorphically onto an open subset of `N`, Lemma 10.3 (3)) and `‖v‖ < ε`,
  a Jacobi field along `t ↦ exp_q(tv)` vanishing at `t = 0` and `t = 1` vanishes;
  `Morse.remark_14_5`: Milnor's statement, for the neighbourhoods `W` of Lemma 10.3: the Jacobi
  fields along the geodesic segment joining two points of `W` (the unique one of length `< ε`) are
  determined by their values at the end points, and these values can be prescribed.

## What Milnor leaves implicit

* Remark 14.5 is stated for "a geodesic segment in `U`"; what is used is that the segment is the
  geodesic `t ↦ exp_q(tv)` with `‖v‖` less than a normal radius at `q`.  The argument here is the
  one implicit in Milnor's: the Jacobi field with `J(0) = 0`, `DJ/dt(0) = w` is the variation field
  `d(exp_q)_{tv}(tw)` of the variation `exp_q(t(v + uw))` through geodesics (Lemma 14.3 and
  uniqueness), and `d(exp_q)_v` is injective on `T_qN` because `exp_q` has a smooth inverse there.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- Being a Jacobi field along `γ` only depends on `γ` on `[0, 1]`. -/
theorem IsJacobiField.congr_curve {γ γ' J : ℝ → V} (hJ : IsJacobiField hN γ J)
    (heq : EqOn γ γ' (Icc 0 1)) : IsJacobiField hN γ' J where
  contDiffOn := hJ.contDiffOn
  tangent t ht := by rw [← heq ht]; exact hJ.tangent t ht
  eq t ht := by
    have hev : γ =ᶠ[𝓝 t] γ' := eventually_of_mem (Icc_mem_nhds ht.1 ht.2) heq
    have hcov : ∀ X : ℝ → V, covD hN γ X =ᶠ[𝓝 t] covD hN γ' X := fun X => by
      filter_upwards [eventually_eventually_nhds.2 hev] with x hx
      rw [covD, covD, hx.self_of_nhds]
    have h1 : deriv (covD hN γ J) t = deriv (covD hN γ' J) t := (hcov J).deriv_eq
    have h2 : γ t = γ' t := hev.self_of_nhds
    have h3 : deriv γ t = deriv γ' t := hev.deriv_eq
    have := hJ.eq t ht
    rw [jacobiExpr] at this ⊢
    change prj hN (γ t) (deriv (covD hN γ J) t) +
      curvR hN (γ t) (deriv γ t) (J t) (deriv γ t) = 0 at this
    change prj hN (γ' t) (deriv (covD hN γ' J) t) +
      curvR hN (γ' t) (deriv γ' t) (J t) (deriv γ' t) = 0
    rw [← h1, ← h2, ← h3]
    exact this

/-! ### Lemma 14.3 -/

/-- **Lemma 14.3** (Milnor p. 80): if `α : (−ε, ε) × [0, 1] → N` is a smooth variation of
`γ = α(0, ·)` through geodesics, its variation field `W(t) = ∂α/∂u (0, t)` is a Jacobi field. -/
theorem lemma_14_3 {ε : ℝ} (hε : 0 < ε) {α : ℝ → ℝ → V}
    (hα : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => α p.1 p.2) (Ioo (-ε) ε ×ˢ Icc (0 : ℝ) 1))
    (hαN : ∀ u ∈ Ioo (-ε) ε, ∀ t ∈ Icc (0 : ℝ) 1, α u t ∈ N)
    (hgeo : ∀ u ∈ Ioo (-ε) ε, IsGeodesicOn hN (α u) (Ioo 0 1)) :
    IsJacobiField hN (α 0) (fun t => deriv (fun u => α u t) 0) := by
  set F : ℝ × ℝ → V := fun p => α p.1 p.2 with hFdef
  set U : Set ℝ := Ioo (-ε) ε
  have hU : IsOpen U := isOpen_Ioo
  have h0U : (0 : ℝ) ∈ U := ⟨by linarith, hε⟩
  have hFd : DifferentiableOn ℝ F (U ×ˢ Icc 0 1) := hα.differentiableOn (by simp)
  have hW : ∀ t ∈ Icc (0 : ℝ) 1, deriv (fun u => α u t) 0 = pdU (U ×ˢ Icc 0 1) F (0, t) :=
    fun t ht => deriv_eq_pdU hU hFd h0U ht
  set O : Set (ℝ × ℝ) := U ×ˢ Ioo 0 1
  have hO : IsOpen O := hU.prod isOpen_Ioo
  have hFO : ContDiffOn ℝ ∞ F O := hα.mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  have hFN : ∀ p ∈ O, F p ∈ N := fun p hp => hαN p.1 hp.1 p.2 (Ioo_subset_Icc_self hp.2)
  have hFdiff : ∀ p ∈ O, DifferentiableAt ℝ F p := fun p hp =>
    (hFO.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)
  refine ⟨?_, fun t ht => ?_, fun t ht => ?_⟩
  · exact ((contDiffOn_pdU hU zero_lt_one hα).comp (contDiffOn_const.prodMk contDiffOn_id)
      fun t ht => mk_mem_prod h0U ht).congr hW
  · have hd := hasDerivAt_pdU hU hFd h0U ht
    have hmem : ∀ᶠ u in 𝓝 (0 : ℝ), (fun u => F (u, t)) u ∈ N :=
      eventually_of_mem (hU.mem_nhds h0U) fun u hu => hαN u hu t ht
    have := hasDerivAt_mem_tangentSubspace hN hd hmem
    rw [hW t ht, prj_eq_self_iff hN (hαN 0 h0U t ht)]
    exact this
  · have hp₀ : ((0 : ℝ), t) ∈ O := ⟨h0U, ht⟩
    have hci := curvature_identity hN hO hFO hFN hp₀
    -- the left side vanishes: each `α(u, ·)` is a geodesic
    have hpYY : ∀ p ∈ O, partialY (partialY F) p = deriv (deriv (α p.1)) p.2 := by
      intro p hp
      have hev : ∀ᶠ y in 𝓝 p.2, partialY F (p.1, y) = deriv (α p.1) y := by
        filter_upwards [isOpen_Ioo.mem_nhds hp.2] with y hy
        exact (hasDerivAt_partialY (hFdiff (p.1, y) ⟨hp.1, hy⟩)).deriv.symm
      have hd2 : DifferentiableAt ℝ (partialY F) p :=
        ((contDiffOn_partialY hO hFO).contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)
      rw [← (hasDerivAt_partialY hd2).deriv]
      exact (show (fun y => partialY F (p.1, y)) =ᶠ[𝓝 p.2] deriv (α p.1) from hev).deriv_eq
    have hzero : ∀ p ∈ O, prj hN (F p) (partialY (partialY F) p) = 0 := by
      intro p hp
      rw [hpYY p hp, prj_of_mem hN ((hgeo p.1 hp.1).mem p.2 hp.2)]
      exact (hgeo p.1 hp.1).tanProj_deriv_deriv hp.2
    have hL : partialX (fun p => prj hN (F p) (partialY (partialY F) p)) ((0 : ℝ), t) = 0 := by
      have hev : (fun p => prj hN (F p) (partialY (partialY F) p)) =ᶠ[𝓝 ((0 : ℝ), t)]
          fun _ => (0 : V) := eventually_of_mem (hO.mem_nhds hp₀) hzero
      rw [partialX_congr hev]
      simp [partialX]
    rw [hL, map_zero] at hci
    -- the right side is the Jacobi operator of the variation field
    set Wf : ℝ → V := fun t => deriv (fun u => α u t) 0
    have hWX : ∀ s ∈ Ioo (0 : ℝ) 1, partialX F ((0 : ℝ), s) = Wf s := fun s hs =>
      (hasDerivAt_partialX (hFdiff (0, s) ⟨h0U, hs⟩)).deriv.symm
    have hYX : ∀ s ∈ Ioo (0 : ℝ) 1, partialY (partialX F) ((0 : ℝ), s) = deriv Wf s := by
      intro s hs
      have hd : DifferentiableAt ℝ (partialX F) ((0 : ℝ), s) :=
        ((contDiffOn_partialX hO hFO).contDiffAt (hO.mem_nhds ⟨h0U, hs⟩)).differentiableAt
          (by simp)
      rw [← (hasDerivAt_partialY hd).deriv]
      exact (show (fun y => partialX F ((0 : ℝ), y)) =ᶠ[𝓝 s] Wf from
        eventually_of_mem (isOpen_Ioo.mem_nhds hs) hWX).deriv_eq
    have hgs : ContDiffOn ℝ ∞ (fun p => prj hN (F p) (partialY (partialX F) p)) O :=
      (ContDiffOn.prj_comp hN hFO hFN).clm_apply
        (contDiffOn_partialY hO (contDiffOn_partialX hO hFO))
    have hR1 : partialY (fun p => prj hN (F p) (partialY (partialX F) p)) ((0 : ℝ), t) =
        deriv (covD hN (α 0) Wf) t := by
      have hg : DifferentiableAt ℝ (fun p => prj hN (F p) (partialY (partialX F) p))
          ((0 : ℝ), t) := (hgs.contDiffAt (hO.mem_nhds hp₀)).differentiableAt (by simp)
      rw [← (hasDerivAt_partialY hg).deriv]
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy
      change prj hN (α 0 y) (partialY (partialX F) ((0 : ℝ), y)) = prj hN (α 0 y) (deriv Wf y)
      rw [hYX y hy]
    have hR2 : partialY F ((0 : ℝ), t) = deriv (α 0) t :=
      (hasDerivAt_partialY (hFdiff _ hp₀)).deriv.symm
    rw [hR1, hR2, hWX t ht] at hci
    rw [jacobiExpr, covD]
    exact hci.symm

/-! ### Remark 14.5 -/

/-- The radial geodesic `t ↦ exp_q(tv)`, `‖v‖` below a normal radius, is a smooth curve in `N` on
`[0, 1]` and a geodesic on an open interval containing `[0, 1]`. -/
theorem IsNormalRadius.isGeodesicOn_ray {q : N} {ε : ℝ} (hq : IsNormalRadius hN q ε) {v : V}
    (hv : v ∈ tangentSubspace hN q) (hvε : ‖v‖ < ε) :
    ∃ δ > 0, IsGeodesicOn hN (fun t => exp hN q (t • v)) (Ioo (-δ) (1 + δ)) := by
  obtain ⟨nc⟩ := hq
  obtain ⟨γ, hγ⟩ := nc.mem_expDom v hv hvε
  obtain ⟨δ, hδ, hgeo, -⟩ := hγ.isGeodesicOn_exp_smul
  exact ⟨δ, hδ, hgeo⟩

theorem IsNormalRadius.isSmoothCurveIn_ray {q : N} {ε : ℝ} (hq : IsNormalRadius hN q ε) {v : V}
    (hv : v ∈ tangentSubspace hN q) (hvε : ‖v‖ < ε) :
    IsSmoothCurveIn hN (fun t => exp hN q (t • v)) := by
  obtain ⟨δ, hδ, hgeo⟩ := hq.isGeodesicOn_ray hv hvε
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-δ) (1 + δ) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact ⟨hgeo.contDiffOn.mono hsub, fun t ht => hgeo.mem t (hsub ht)⟩

/-- The derivative at `0` of a smooth extension `F` of `exp_q` near `0` is the identity on
`T_qN` (`d(exp_q)₀ = id`, Milnor p. 58). -/
theorem fderiv_extension_exp_zero {q : N} {O : Set V} (hO : IsOpen O) (h0O : (0 : V) ∈ O)
    {F : V → V} (hF : ContDiffOn ℝ ∞ F O) {ε : ℝ} (hε : 0 < ε)
    (hFeq : ∀ v ∈ tangentSubspace hN q, ‖v‖ < ε → F v = exp hN q v)
    {w : V} (hw : w ∈ tangentSubspace hN q) : fderiv ℝ F 0 w = w := by
  have hFd : HasFDerivAt F (fderiv ℝ F 0) 0 :=
    ((hF.contDiffAt (hO.mem_nhds h0O)).differentiableAt (by simp)).hasFDerivAt
  have h1 : HasFDerivAt (fun x : tangentSubspace hN q => F x)
      ((fderiv ℝ F 0).comp (tangentSubspace hN q).subtypeL) 0 := by
    have : HasFDerivAt F (fderiv ℝ F 0) (((tangentSubspace hN q).subtypeL :
        tangentSubspace hN q →L[ℝ] V) 0) := by rw [map_zero]; exact hFd
    exact this.comp (0 : tangentSubspace hN q) (tangentSubspace hN q).subtypeL.hasFDerivAt
  have hev : (fun x : tangentSubspace hN q => F x) =ᶠ[𝓝 0]
      fun x : tangentSubspace hN q => exp hN q x := by
    filter_upwards [Metric.ball_mem_nhds (0 : tangentSubspace hN q) hε] with x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    exact hFeq x x.2 (by simpa using hx)
  have h2 := (h1.congr_of_eventuallyEq hev.symm).unique (hasFDerivAt_exp_zero q)
  have := congrArg (fun L => L ⟨w, hw⟩) h2
  simpa using this

/-- **Remark 14.5** (Milnor pp. 81–82), for a normal radius: if `ε` is a normal radius at `q` and
`‖v‖ < ε`, a Jacobi field along the geodesic segment `t ↦ exp_q(tv)` vanishing at both ends
vanishes. -/
theorem remark_14_5_of_isNormalRadius {q : N} {ε : ℝ} (hq : IsNormalRadius hN q ε) {v : V}
    (hv : v ∈ tangentSubspace hN q) (hvε : ‖v‖ < ε) {J : ℝ → V}
    (hJ : IsJacobiField hN (fun t => exp hN q (t • v)) J) (h0 : J 0 = 0) (h1 : J 1 = 0) :
    EqOn J 0 (Icc 0 1) := by
  have hc := hq.isSmoothCurveIn_ray hv hvε
  obtain ⟨nc⟩ := hq
  set γ : ℝ → V := fun t => exp hN q (t • v)
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hγ0 : γ 0 = q := by simp [γ, exp_zero q.2]
  set w := covAlong hN γ J 0
  have hwT : w ∈ tangentSubspace hN q := by
    have h1 : w ∈ tangentSubspace hN ⟨γ 0, hc.mem 0 h00⟩ := prj_mem hN (hc.mem 0 h00) _
    have h2 : (⟨γ 0, hc.mem 0 h00⟩ : N) = q := Subtype.ext hγ0
    rwa [h2] at h1
  -- it suffices to show `w = 0`
  suffices hw0 : w = 0 from hJ.eqOn_zero hc h00 h0 hw0
  -- the variation `α(u, t) = exp_q(t(v + uw))` through geodesics
  set ε₁ := (ε - ‖v‖) / (‖w‖ + 1)
  have hε₁ : 0 < ε₁ := div_pos (by linarith) (by positivity)
  have hsmall : ∀ u ∈ Ioo (-ε₁) ε₁, ‖v + u • w‖ < ε := by
    intro u hu
    have hu' : |u| < ε₁ := abs_lt.2 hu
    calc ‖v + u • w‖ ≤ ‖v‖ + |u| * ‖w‖ := by
          rw [← Real.norm_eq_abs, ← norm_smul]; exact norm_add_le _ _
      _ ≤ ‖v‖ + ε₁ * ‖w‖ := by gcongr
      _ < ε := by
          have : ε₁ * ‖w‖ < ε - ‖v‖ := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg w]
          linarith
  have hmemT : ∀ u (t : ℝ), t • (v + u • w) ∈ tangentSubspace hN q := fun u t =>
    Submodule.smul_mem _ t (Submodule.add_mem _ hv (Submodule.smul_mem _ u hwT))
  have hsmall' : ∀ u ∈ Ioo (-ε₁) ε₁, ∀ t ∈ Icc (0 : ℝ) 1, ‖t • (v + u • w)‖ < ε := by
    intro u hu t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖v + u • w‖ ≤ 1 * ‖v + u • w‖ := by gcongr; exact ht.2
      _ < ε := by rw [one_mul]; exact hsmall u hu
  set α : ℝ → ℝ → V := fun u t => exp hN q (t • (v + u • w))
  have hαF : ∀ u ∈ Ioo (-ε₁) ε₁, ∀ t ∈ Icc (0 : ℝ) 1, α u t = nc.F (t • (v + u • w)) :=
    fun u hu t ht => (nc.F_eq _ (hmemT u t) (hsmall' u hu t ht)).symm
  have hα : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => α p.1 p.2) (Ioo (-ε₁) ε₁ ×ˢ Icc (0 : ℝ) 1) := by
    have hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.2 • (v + p.1 • w)) := by fun_prop
    refine (nc.contDiffOn_F.comp hφ.contDiffOn fun p hp =>
      nc.mem_O _ (hmemT p.1 p.2) (hsmall' p.1 hp.1 p.2 hp.2)).congr fun p hp => ?_
    exact hαF p.1 hp.1 p.2 hp.2
  have hαN : ∀ u ∈ Ioo (-ε₁) ε₁, ∀ t ∈ Icc (0 : ℝ) 1, α u t ∈ N := fun u hu t ht =>
    nc.exp_mem (hmemT u t) (hsmall' u hu t ht)
  have hgeo : ∀ u ∈ Ioo (-ε₁) ε₁, IsGeodesicOn hN (α u) (Ioo 0 1) := by
    intro u hu
    obtain ⟨δ, hδ, hg⟩ := (IsNormalRadius.isGeodesicOn_ray ⟨nc⟩
      (Submodule.add_mem _ hv (Submodule.smul_mem _ u hwT)) (hsmall u hu))
    exact hg.mono isOpen_Ioo (Ioo_subset_Ioo (by linarith) (by linarith))
  have hJt := lemma_14_3 hε₁ hα hαN hgeo
  have hα0 : α 0 = γ := funext fun t => by simp [α, γ]
  rw [hα0] at hJt
  set J' : ℝ → V := fun t => deriv (fun u => α u t) 0
  -- `J'(t) = t • dF_{tv}(w)`
  have hO0 : ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ nc.O := fun t ht => by
    have := nc.mem_O _ (hmemT 0 t) (hsmall' 0 ⟨by linarith, hε₁⟩ t ht)
    simpa using this
  have hFd : ∀ x ∈ nc.O, DifferentiableAt ℝ nc.F x := fun x hx =>
    (nc.contDiffOn_F.contDiffAt (nc.isOpen_O.mem_nhds hx)).differentiableAt (by simp)
  have hJ'eq : ∀ t ∈ Icc (0 : ℝ) 1, J' t = t • fderiv ℝ nc.F (t • v) w := by
    intro t ht
    have hev : (fun u => α u t) =ᶠ[𝓝 0] fun u => nc.F (t • (v + u • w)) :=
      eventually_of_mem (isOpen_Ioo.mem_nhds ⟨by linarith, hε₁⟩) fun u hu => hαF u hu t ht
    have hline : HasDerivAt (fun u : ℝ => t • (v + u • w)) (t • w) 0 := by
      have h1 : HasDerivAt (fun u : ℝ => v + u • w) ((1 : ℝ) • w) 0 :=
        ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
      have h2 := h1.const_smul t
      rw [one_smul] at h2
      exact h2
    have hFd' : HasFDerivAt nc.F (fderiv ℝ nc.F (t • v)) (t • (v + (0 : ℝ) • w)) := by
      rw [zero_smul, add_zero]; exact (hFd _ (hO0 t ht)).hasFDerivAt
    have this' : HasDerivAt (fun u : ℝ => nc.F (t • (v + u • w)))
        (fderiv ℝ nc.F (t • v) (t • w)) 0 :=
      hFd'.comp_hasDerivAt (0 : ℝ) hline
    change deriv (fun u => α u t) 0 = _
    rw [hev.deriv_eq, this'.deriv, map_smul]
  -- `DJ'/dt(0) = w`
  have hcovJ' : covAlong hN γ J' 0 = w := by
    have hL : HasDerivAt (fun t : ℝ => fderiv ℝ nc.F (t • v) w)
        (deriv (fun t : ℝ => fderiv ℝ nc.F (t • v) w) 0) 0 := by
      have hO0' : (0 : ℝ) • v ∈ nc.O := hO0 0 h00
      have h1 : ContDiffAt ℝ ∞ (fun t : ℝ => fderiv ℝ nc.F (t • v)) 0 := by
        have hF2 : ContDiffAt ℝ ∞ (fderiv ℝ nc.F) ((0 : ℝ) • v) :=
          (nc.contDiffOn_F.contDiffAt (nc.isOpen_O.mem_nhds hO0')).fderiv_right (m := ∞)
            (by simp)
        exact hF2.comp (0 : ℝ) (contDiffAt_id.smul contDiffAt_const)
      exact ((h1.clm_apply contDiffAt_const).differentiableAt (by simp)).hasDerivAt
    have hd : HasDerivAt (fun t : ℝ => t • fderiv ℝ nc.F (t • v) w)
        (fderiv ℝ nc.F ((0 : ℝ) • v) w) 0 := by
      have h2 : HasDerivAt (fun t : ℝ => t • fderiv ℝ nc.F (t • v) w)
          ((0 : ℝ) • deriv (fun t : ℝ => fderiv ℝ nc.F (t • v) w) 0 +
            (1 : ℝ) • fderiv ℝ nc.F ((0 : ℝ) • v) w) 0 :=
        (hasDerivAt_id' (0 : ℝ)).smul hL
      rw [zero_smul, zero_add, one_smul] at h2
      exact h2
    have hdW : derivWithin J' (Icc 0 1) 0 = fderiv ℝ nc.F 0 w := by
      rw [derivWithin_congr (fun t ht => hJ'eq t ht) (hJ'eq 0 h00)]
      rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one 0 h00), zero_smul]
    have hO00 : (0 : V) ∈ nc.O := by simpa using hO0 0 h00
    rw [covAlong, hdW,
      fderiv_extension_exp_zero nc.isOpen_O hO00 nc.contDiffOn_F nc.pos nc.F_eq hwT, hγ0,
      prj_eq_self_iff hN q.2 |>.2 hwT]
  -- `J = J'` by uniqueness
  have hJ'0 : J' 0 = 0 := by
    have : (fun u => α u 0) = fun _ => (q : V) := funext fun u => by simp [α, exp_zero q.2]
    change deriv (fun u => α u 0) 0 = 0
    rw [this, deriv_const]
  have hJJ' : EqOn J J' (Icc 0 1) := fun t ht => by
    have e1 := hJ.eqOn_jacSol hc h00 ht
    have e2 := hJt.eqOn_jacSol hc h00 ht
    rw [h0, hJ'0, hcovJ'] at *
    exact congrArg Prod.fst (e1.trans e2.symm)
  -- `d(exp_q)_v` is injective on `T_qN`
  have hJ'1 : fderiv ℝ nc.F v w = 0 := by
    have := (hJJ' ⟨zero_le_one, le_rfl⟩).symm
    rw [hJ'eq 1 ⟨zero_le_one, le_rfl⟩, h1, one_smul, one_smul] at this
    exact this
  have hvO : v ∈ nc.O := nc.mem_O v hv hvε
  have hFvU : nc.F v ∈ nc.U := by rw [nc.F_eq v hv hvε]; exact nc.exp_mem_U v hv hvε
  have hGd : HasFDerivAt nc.G (fderiv ℝ nc.G (nc.F v)) (nc.F v) :=
    ((nc.contDiffOn_G.contDiffAt (nc.isOpen_U.mem_nhds hFvU)).differentiableAt
      (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun u : ℝ => v + u • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  have hFv : HasFDerivAt nc.F (fderiv ℝ nc.F v) (v + (0 : ℝ) • w) := by
    simpa using (hFd v hvO).hasFDerivAt
  have hGd' : HasFDerivAt nc.G (fderiv ℝ nc.G (nc.F v)) (nc.F (v + (0 : ℝ) • w)) := by
    rw [zero_smul, add_zero]; exact hGd
  have hcomp := (hGd'.comp (v + (0 : ℝ) • w) hFv).comp_hasDerivAt (0 : ℝ) hline
  have hid : (fun u : ℝ => (nc.G ∘ nc.F) (v + u • w)) =ᶠ[𝓝 0] fun u => v + u • w := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-ε₁) ε₁ from ⟨by linarith, hε₁⟩)]
      with u hu
    have hmem : v + u • w ∈ tangentSubspace hN q :=
      Submodule.add_mem _ hv (Submodule.smul_mem _ u hwT)
    simp only [comp_apply]
    rw [nc.F_eq _ hmem (hsmall u hu), nc.G_exp _ hmem (hsmall u hu)]
  have := (hcomp.congr_of_eventuallyEq hid.symm).unique hline
  simp only [ContinuousLinearMap.comp_apply, hJ'1, map_zero] at this
  exact this.symm

/-- **Remark 14.5** (Milnor pp. 81–82): every point `p ∈ N` has a neighbourhood `W = N ∩ O` and
an `ε > 0` (Lemma 10.3) such that any two points `q₁, q₂ ∈ W` are joined by a geodesic segment
`t ↦ exp_{q₁}(tv)`, `‖v‖ < ε`, along which a Jacobi field vanishing at both ends vanishes (so the
Jacobi fields along it are determined by their values at the end points; see
`Morse.remark_14_5_bijective` for the prescription of these values). -/
theorem remark_14_5 (p : N) : ∃ O : Set V, IsOpen O ∧ (p : V) ∈ O ∧ ∃ ε > 0,
    ∀ q₁ q₂ : N, (q₁ : V) ∈ O → (q₂ : V) ∈ O → ∃ v ∈ tangentSubspace hN q₁, ‖v‖ < ε ∧
      exp hN q₁ v = q₂ ∧ IsNormalRadius hN q₁ ε ∧
      ∀ J, IsJacobiField hN (fun t => exp hN q₁ (t • v)) J → J 0 = 0 → J 1 = 0 →
        EqOn J 0 (Icc 0 1) := by
  obtain ⟨O, hO, hpO, ε, hε, h1, -, h3⟩ := lemma_10_3 hN p
  refine ⟨O, hO, hpO, ε, hε, fun q₁ q₂ hq₁ hq₂ => ?_⟩
  obtain ⟨v, ⟨hv, hvε, hexp⟩, -⟩ := h1 q₁ q₂ hq₁ hq₂
  exact ⟨v, hv, hvε, hexp, h3 q₁ hq₁, fun J hJ h0 h1 =>
    remark_14_5_of_isNormalRadius (h3 q₁ hq₁) hv hvε hJ h0 h1⟩

/-- **Remark 14.5, existence** (Milnor p. 81): along such a segment the values of Jacobi fields at
the two ends can be prescribed arbitrarily: `J ↦ (J(0), J(1))` is an isomorphism. -/
theorem remark_14_5_bijective {q : N} {ε : ℝ} (hq : IsNormalRadius hN q ε) {v : V}
    (hv : v ∈ tangentSubspace hN q) (hvε : ‖v‖ < ε) :
    Bijective (jacEvalEnds (hq.isSmoothCurveIn_ray hv hvε) (a := 0) (b := 1)
      ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩) := by
  set hc := hq.isSmoothCurveIn_ray hv hvε
  have hinj : Injective (jacEvalEnds hc (a := 0) (b := 1) ⟨le_rfl, zero_le_one⟩
      ⟨zero_le_one, le_rfl⟩) := by
    refine (injective_iff_map_eq_zero _).2 fun J hJ => ?_
    have h0 : (J : ℝ → V) 0 = 0 := congrArg (fun z => (z.1 : V)) hJ
    have h1 : (J : ℝ → V) 1 = 0 := congrArg (fun z => (z.2 : V)) hJ
    exact Subtype.ext (jacobiSpace_eq_zero hc J.2
      (remark_14_5_of_isNormalRadius hq hv hvε J.2.1 h0 h1))
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [finrank_jacobiSpace hc, Module.finrank_prod,
    finrank_tanAt hN (hc.mem 0 ⟨le_rfl, zero_le_one⟩),
    finrank_tanAt hN (hc.mem 1 ⟨zero_le_one, le_rfl⟩)]
  ring

end Morse
