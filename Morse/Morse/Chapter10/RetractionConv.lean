import Morse.Chapter10.RetractionCont

/-!
Milnor, *Morse Theory*, §16, p. 91: the continuity of the deformation `r_u` in both variables
(Milnor: "it is easily verified"), for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# Continuity of Milnor's deformation `r_u`

## In the embedded setting

For `B : Morse.BrokenSetup hN p q c m`, a segment `[tᵢ, t_{i+1}]` and, along a filter, `uⱼ → u` in
`[tᵢ, t_{i+1}]` and `γⱼ → γ` in `Int Ω^c` (Milnor's metric `d`):

* `Morse.BrokenSetup.tendsto_riemDist_retrSeg`: **pointwise convergence**
  `r_{uⱼ}(γⱼ)(s) → r_u(γ)(s)` for `ρ`, for each `s ∈ [0, 1]`;
* `Morse.BrokenSetup.eventually_supDist_retrSeg_le`: **uniform convergence**, from the pointwise
  one and the equicontinuity of paths of energy `< c` (`ρ(ω(s), ω(τ)) ≤ √(|τ − s| c)`);
* `Morse.BrokenSetup.eventually_integral_retrSeg_le`: **convergence of the speeds in `L²`**;
* `Morse.BrokenSetup.tendsto_retrSeg`: hence `d(r_{uⱼ}(γⱼ), r_u(γ)) → 0`.

## What Milnor leaves implicit

* **The `L²` part of `d` is the delicate one.**  For `u` close to `tᵢ`, the short geodesic over
  `[tᵢ, u]` may be very fast; its contribution to `∫ (ds/dt − ds'/dt)²` is controlled by its
  energy `ρ(ω(tᵢ), ω(u))²/(u − tᵢ) ≤ E_{tᵢ}^u(ω)`, which is uniformly small for `ω` near a given
  path (Lemma 16.B of the exposition).  Away from `u = tᵢ`, the speed of the short geodesic is
  `‖v(ω(tᵢ), ω(u))‖/(u − tᵢ)`, continuous in `(u, ω)` by the continuity of the short join vector
  (Corollary 10.8).
* **The uniform part of `d`**: pointwise convergence uses the continuous dependence of the short
  geodesics on their end points (Corollary 10.8 and the continuity of `exp`); uniform
  convergence then follows since all the paths involved have energy `< c`, hence are uniformly
  `½`-Hölder for `ρ`.
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Interval NNReal

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

namespace PathSp

variable {p q : V}

variable (hN) in
include hN in
/-- **Uniform convergence from pointwise convergence** for paths of bounded energy: if
`αⱼ(s) → α(s)` for every `s ∈ [0, 1]` and all the energies are `≤ C`, then eventually
`max_s ρ(αⱼ(s), α(s)) ≤ e` (the paths are uniformly `½`-Hölder for `ρ`). -/
theorem eventually_supDist_le_of_tendsto_apply {ι : Type*} {l : Filter ι} {αs : ι → ℝ → V}
    {α : ℝ → V} {C : ℝ} (hαs : ∀ᶠ j in l, αs j ∈ pathSpace N p q ∧ energy (αs j) 0 1 ≤ C)
    (hα : α ∈ pathSpace N p q) (hEα : energy α 0 1 ≤ C)
    (hpt : ∀ s ∈ Icc (0 : ℝ) 1, Tendsto (fun j => αs j s) l (𝓝 (α s))) {e : ℝ} (he : 0 < e) :
    ∀ᶠ j in l, supDist N (αs j) α ≤ ENNReal.ofReal e := by
  have hC : 0 ≤ C := (energy_nonneg_of_le zero_le_one).trans hEα
  set h := (e / 3) ^ 2 / (C + 1) with hh
  have hh0 : 0 < h := by positivity
  -- an `h`-net of `[0, 1]`
  obtain ⟨G, hG01, hGfin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_Icc (a := (0 : ℝ)) (b := 1)) hh0
  -- pointwise convergence at the points of the net
  have hpt' : ∀ᶠ j in l, ∀ g ∈ G, riemDist (N := N) (αs j g) (α g) ≤ ENNReal.ofReal (e / 3) := by
    refine (hGfin.eventually_all).2 fun g hg => ?_
    have hg01 := hG01 hg
    have := tendsto_riemDist_of_tendsto hN (hα.2.1 g hg01) (tendsto_nhdsWithin_iff.2
      ⟨hpt g hg01, hαs.mono fun j hj => hj.1.2.1 g hg01⟩)
    exact (ENNReal.tendsto_nhds_zero.1 this) _ (ENNReal.ofReal_pos.2 (by positivity))
  -- equicontinuity
  have hequi : ∀ {β : ℝ → V}, β ∈ pathSpace N p q → energy β 0 1 ≤ C → ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ τ ∈ Icc (0 : ℝ) 1, |τ - s| < h →
        riemDist (N := N) (β s) (β τ) ≤ ENNReal.ofReal (e / 3) := by
    intro β hβ hEβ s hs τ hτ hst
    refine (riemDist_le_sqrt hβ hs hτ).trans (ENNReal.ofReal_le_ofReal ?_)
    have hE0 : 0 ≤ energy β 0 1 := energy_nonneg_of_le zero_le_one
    calc √(|τ - s| * energy β 0 1) ≤ √((e / 3) ^ 2) := Real.sqrt_le_sqrt (by
          calc |τ - s| * energy β 0 1 ≤ h * C := mul_le_mul hst.le hEβ hE0 hh0.le
            _ = (e / 3) ^ 2 * (C / (C + 1)) := by rw [hh]; ring
            _ ≤ (e / 3) ^ 2 * 1 := by
                gcongr
                rw [div_le_one (by positivity)]
                linarith
            _ = (e / 3) ^ 2 := mul_one _)
      _ = e / 3 := Real.sqrt_sq (by positivity)
  filter_upwards [hpt', hαs] with j hj hj'
  refine iSup₂_le fun τ hτ => ?_
  obtain ⟨g, hgG, hτg⟩ := mem_iUnion₂.1 (hcover hτ)
  have hg01 := hG01 hgG
  have hτg' : |τ - g| < h := by rwa [mem_ball, Real.dist_eq] at hτg
  have hgτ' : |g - τ| < h := by rwa [abs_sub_comm]
  calc riemDist (N := N) (αs j τ) (α τ)
      ≤ riemDist (N := N) (αs j τ) (αs j g) +
        (riemDist (N := N) (αs j g) (α g) + riemDist (N := N) (α g) (α τ)) :=
        (riemDist_triangle _ _ _).trans (add_le_add le_rfl (riemDist_triangle _ _ _))
    _ ≤ ENNReal.ofReal (e / 3) + (ENNReal.ofReal (e / 3) + ENNReal.ofReal (e / 3)) :=
        add_le_add (hequi hj'.1 hj'.2 τ hτ g hg01 hgτ')
          (add_le_add (hj g hgG) (hequi hα hEα g hg01 τ hτ hτg'))
    _ = ENNReal.ofReal e := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

end PathSp

namespace BrokenSetup

open PathSp

variable {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

section Helpers

variable {ι : Type*} {l : Filter ι}

/-- **Short geodesics with converging data converge**: if `xⱼ → x`, `yⱼ → y` (joinable pairs),
`bⱼ → b > a` and `τⱼ → τ` with `a ≤ τⱼ ≤ bⱼ`, then `sgeo(xⱼ, yⱼ; a, bⱼ)(τⱼ) → sgeo(x, y; a, b)(τ)`
(in `V`). -/
theorem tendsto_sgeoOver {xs ys : ι → V} {x y : V} (hxs : Tendsto xs l (𝓝 x))
    (hys : Tendsto ys l (𝓝 y)) (hJs : ∀ᶠ j in l, (xs j, ys j) ∈ B.joinable)
    (hJ : (x, y) ∈ B.joinable) {a : ℝ} {bs : ι → ℝ} {b : ℝ} (hbs : Tendsto bs l (𝓝 b))
    (hab : a < b) {τs : ι → ℝ} {τ : ℝ} (hτs : Tendsto τs l (𝓝 τ))
    (hτsI : ∀ᶠ j in l, τs j ∈ Icc a (bs j)) (hτ : τ ∈ Icc a b) :
    Tendsto (fun j => B.sgeoOver (xs j) (ys j) a (bs j) (τs j)) l
      (𝓝 (B.sgeoOver x y a b τ)) := by
  have hθ : Tendsto (fun j => (τs j - a) / (bs j - a)) l (𝓝 ((τ - a) / (b - a))) :=
    (hτs.sub_const a).div (hbs.sub_const a) (sub_pos.2 hab).ne'
  have hθI : (τ - a) / (b - a) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.2 hτ.1) (sub_pos.2 hab).le,
      (div_le_one (sub_pos.2 hab)).2 (by linarith [hτ.2])⟩
  have hbs' : ∀ᶠ j in l, a < bs j := hbs.eventually (lt_mem_nhds hab)
  have hθsI : ∀ᶠ j in l, (τs j - a) / (bs j - a) ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [hbs', hτsI] with j hj hjτ
    exact ⟨div_nonneg (sub_nonneg.2 hjτ.1) (sub_pos.2 hj).le,
      (div_le_one (sub_pos.2 hj)).2 (by linarith [hjτ.2])⟩
  have h1 : Tendsto (fun j => ((xs j, ys j), (τs j - a) / (bs j - a))) l
      (𝓝[B.joinable ×ˢ Icc 0 1] ((x, y), (τ - a) / (b - a))) :=
    tendsto_nhdsWithin_iff.2 ⟨(hxs.prodMk_nhds hys).prodMk_nhds hθ, by
      filter_upwards [hJs, hθsI] with j h1 h2
      exact ⟨h1, h2⟩⟩
  exact (B.continuousWithinAt_shortGeo hJ hθI).tendsto.comp h1

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- Pairs `(γ(tᵢ), γ(σ))`, `σ` in the `i`-th segment, are joinable. -/
theorem mem_joinable {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q) (hE : energy γ 0 1 < c)
    (k : Fin (m + 1)) {σ σ' : ℝ} (hσ : B.t k.castSucc ≤ σ) (hσσ' : σ ≤ σ')
    (hσ' : σ' ≤ B.t k.succ) : (γ σ, γ σ') ∈ B.joinable := by
  have h0 := B.t_nonneg k.castSucc
  have h1 := B.t_le_one k.succ
  exact ⟨mem_closedRiemBall_of_energy_le hγ hE.le ⟨h0.trans hσ, by linarith⟩,
    mem_closedRiemBall_of_energy_le hγ hE.le ⟨by linarith, hσ'.trans h1⟩,
    B.riemDist_lt_of_seg hγ hE k hσ hσσ' hσ'⟩

/-- **The speed of `r_u(γ)` on `(tᵢ, u)`** is `‖v(γ(tᵢ), γ(u))‖/(u − tᵢ)`. -/
theorem speed_retrSeg_mid {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q) (hE : energy γ 0 1 < c)
    {i : Fin (m + 1)} {u : ℝ} (hu : u ∈ Icc (B.t i.castSucc) (B.t i.succ))
    (hau : B.t i.castSucc < u) {τ : ℝ} (hτ : τ ∈ Ioo (B.t i.castSucc) u) :
    speed (B.retrSeg i u γ) τ = ‖B.joinVec (γ (B.t i.castSucc)) (γ u)‖ / (u - B.t i.castSucc) := by
  have hJ := B.mem_joinable hγ hE i le_rfl hu.1 hu.2
  obtain ⟨η, hη, -, hspeed⟩ := B.sgeoOver_isGeodesicOn hJ.1 hJ.2.1 hJ.2.2 hau
  rw [speed_congr (B.retrSeg_eqOn_mid hγ hE) hτ]
  exact hspeed τ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩

/-- **The energy of `r_u(γ)` on `[s, t] ⊆ [tᵢ, u]`** is `σ² (t − s)`, `σ` its speed there. -/
theorem energy_retrSeg_mid {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q) (hE : energy γ 0 1 < c)
    {i : Fin (m + 1)} {u : ℝ} (hu : u ∈ Icc (B.t i.castSucc) (B.t i.succ))
    (hau : B.t i.castSucc < u) {s t : ℝ} (hs : B.t i.castSucc ≤ s) (hst : s ≤ t) (ht : t ≤ u) :
    energy (B.retrSeg i u γ) s t =
      (‖B.joinVec (γ (B.t i.castSucc)) (γ u)‖ / (u - B.t i.castSucc)) ^ 2 * (t - s) := by
  have hR := B.retrSeg_mem_pathSpace hγ hE hu
  have hu01 := B.u_mem hu
  have hadm : IsAdmissible (B.retrSeg i u γ) s t :=
    (hR.1.mono ((B.t_nonneg _).trans hs) hst (ht.trans hu01.2)).isAdmissible
  exact energy_eq_of_norm_deriv hadm fun τ hτ _ =>
    B.speed_retrSeg_mid hγ hE hu hau ⟨hs.trans_lt hτ.1, hτ.2.trans_le ht⟩

variable {γs : ι → PathSp N p q} {γ : PathSp N p q} (hγs : Tendsto γs l (𝓝 γ))
include hγs

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The `L²` distance to the limit tends to `0`. -/
theorem tendsto_l2Dist : Tendsto (fun j => l2Dist (γs j) γ) l (𝓝 0) := by
  have h1 : Tendsto (fun j => ENNReal.ofReal (l2Dist (γs j) γ)) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_iff_edist_tendsto_0.1 hγs) (fun _ => bot_le) fun j => ofReal_l2Dist_le_edist _ _
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  simpa [Function.comp_def, ENNReal.toReal_ofReal (l2Dist_nonneg _ _)] using h2

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- `γⱼ(σⱼ) → γ(σ)` in `V`. -/
theorem tendsto_apply {σs : ι → ℝ} {σ : ℝ} (hσs : Tendsto σs l (𝓝 σ))
    (hσsI : ∀ᶠ j in l, σs j ∈ Icc (0 : ℝ) 1) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun j => γs j (σs j)) l (𝓝 (γ σ)) :=
  tendsto_of_tendsto_riemDist (tendsto_riemDist_apply hγs hσs hσsI hσ)

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The break points converge. -/
theorem tendsto_nodeVal : Tendsto (fun j => B.nodeVal (γs j)) l (𝓝 (B.nodeVal γ)) :=
  tendsto_pi_nhds.2 fun _ => tendsto_apply hγs tendsto_const_nhds
    (Eventually.of_forall fun _ => ⟨B.t_nonneg _, B.t_le_one _⟩) ⟨B.t_nonneg _, B.t_le_one _⟩

end Helpers

/-! ### Pointwise convergence -/

section Conv

variable {ι : Type*} {l : Filter ι} {i : Fin (m + 1)} {us : ι → ℝ} {γs : ι → PathSp N p q}
  {u : ℝ} {γ : PathSp N p q}
  (hus : Tendsto us l (𝓝 u)) (hγs : Tendsto γs l (𝓝 γ))
  (husI : ∀ᶠ j in l, us j ∈ Icc (B.t i.castSucc) (B.t i.succ))
  (hu : u ∈ Icc (B.t i.castSucc) (B.t i.succ))
  (hEs : ∀ᶠ j in l, energy (γs j) 0 1 < c) (hE : energy γ 0 1 < c)
include hus hγs husI hu hEs hE

/-- **Pointwise convergence** of `r_{uⱼ}(γⱼ)(s)` to `r_u(γ)(s)` (in `V`). -/
theorem tendsto_retrSeg_apply {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun j => B.retrSeg i (us j) (γs j) s) l (𝓝 (B.retrSeg i u γ s)) := by
  have hu01 := B.u_mem hu
  have ha01 : B.t i.castSucc ∈ Icc (0 : ℝ) 1 := ⟨B.t_nonneg _, B.t_le_one _⟩
  have hconst : ∀ {σ : ℝ}, σ ∈ Icc (0 : ℝ) 1 → Tendsto (fun j => γs j σ) l (𝓝 (γ σ)) :=
    fun hσ => tendsto_apply hγs tendsto_const_nhds (Eventually.of_forall fun _ => hσ) hσ
  rcases le_or_gt s (B.t i.castSucc) with hsa | hsa
  · -- on `[0, tᵢ]`: broken geodesics
    set k := B.segOf s
    have hk := B.mem_Icc_segOf hs
    have hk0 : B.t k.castSucc ∈ Icc (0 : ℝ) 1 := ⟨B.t_nonneg _, B.t_le_one _⟩
    have hk1 : B.t k.succ ∈ Icc (0 : ℝ) 1 := ⟨B.t_nonneg _, B.t_le_one _⟩
    have hkk : B.t k.castSucc < B.t k.succ := B.t_lt_iff.2 Fin.castSucc_lt_succ
    rw [B.retrSeg_eqOn_left i u γ (mem_Iic.2 hsa), B.path_nodeVal_eq_sgeoOver γ.mem hE k hk]
    have hev : ∀ᶠ j in l, B.retrSeg i (us j) (γs j) s = B.sgeoOver (γs j (B.t k.castSucc))
        (γs j (B.t k.succ)) (B.t k.castSucc) (B.t k.succ) s := by
      filter_upwards [hEs] with j hEj
      rw [B.retrSeg_eqOn_left i (us j) (γs j) (mem_Iic.2 hsa),
        B.path_nodeVal_eq_sgeoOver (γs j).mem hEj k hk]
    refine Tendsto.congr' (EventuallyEq.symm hev) ?_
    exact B.tendsto_sgeoOver (hconst hk0) (hconst hk1)
      (hEs.mono fun j hEj => B.mem_joinable (γs j).mem hEj k le_rfl hkk.le le_rfl)
      (B.mem_joinable γ.mem hE k le_rfl hkk.le le_rfl) tendsto_const_nhds hkk tendsto_const_nhds
      (Eventually.of_forall fun _ => hk) hk
  have hJs : ∀ᶠ j in l, (γs j (B.t i.castSucc), γs j (us j)) ∈ B.joinable := by
    filter_upwards [hEs, husI] with j hEj hj
    exact B.mem_joinable (γs j).mem hEj i le_rfl hj.1 hj.2
  have hJ := B.mem_joinable γ.mem hE i le_rfl hu.1 hu.2
  have hus' := tendsto_apply hγs hus (husI.mono fun j hj => B.u_mem hj) hu01
  rcases lt_trichotomy s u with hsu | hsu | hsu
  · -- `tᵢ < s < u`: the short geodesics
    have hev1 : ∀ᶠ j in l, s < us j := hus.eventually (lt_mem_nhds hsu)
    rw [B.retrSeg_eqOn_mid γ.mem hE ⟨hsa.le, hsu.le⟩]
    have hev : ∀ᶠ j in l, B.retrSeg i (us j) (γs j) s = B.sgeoOver (γs j (B.t i.castSucc))
        (γs j (us j)) (B.t i.castSucc) (us j) s := by
      filter_upwards [hEs, hev1] with j hEj hj
      exact B.retrSeg_eqOn_mid (γs j).mem hEj ⟨hsa.le, hj.le⟩
    refine Tendsto.congr' (EventuallyEq.symm hev) ?_
    exact B.tendsto_sgeoOver (hconst ha01) hus' hJs hJ hus (hsa.trans hsu) tendsto_const_nhds
      (hev1.mono fun j hj => ⟨hsa.le, hj.le⟩) ⟨hsa.le, hsu.le⟩
  · -- `s = u`: both formulas tend to `γ(u)`
    have hau : B.t i.castSucc < u := hsu ▸ hsa
    have hR₀ : B.retrSeg i u γ s = γ u := by
      rw [B.retrSeg_eqOn_right γ.mem hE hu (show s ∈ Ici u from hsu.ge), hsu]
    rw [hR₀]
    have hev : ∀ j, B.retrSeg i (us j) (γs j) s = if s ≤ us j then B.sgeoOver
        (γs j (B.t i.castSucc)) (γs j (us j)) (B.t i.castSucc) (us j) (min s (us j))
        else γs j s := by
      intro j
      simp only [retrSeg, if_neg (not_le.2 hsa)]
      split_ifs with h
      · rw [min_eq_left h]
      · rfl
    simp only [hev]
    have hA := B.tendsto_sgeoOver (hconst ha01) hus' hJs hJ hus hau
      (tendsto_const_nhds.min hus) (husI.mono fun j hj => ⟨le_min hsa.le hj.1, min_le_right _ _⟩)
      ⟨le_min hsa.le hu.1, min_le_right _ _⟩
    have hlim : B.sgeoOver (γ (B.t i.castSucc)) (γ u) (B.t i.castSucc) u (min s u) = γ u := by
      rw [hsu, min_self, B.sgeoOver_right hJ.1 hJ.2.1 hJ.2.2 hau]
    rw [hlim] at hA
    have hC : Tendsto (fun j => γs j s) l (𝓝 (γ u)) := by
      have := hconst hs
      rwa [hsu] at this ⊢
    exact hA.if' hC
  · -- `u < s`: the path itself
    have hev1 : ∀ᶠ j in l, us j < s := hus.eventually (gt_mem_nhds hsu)
    rw [B.retrSeg_eqOn_right γ.mem hE hu (show s ∈ Ici u from hsu.le)]
    have hev : ∀ᶠ j in l, B.retrSeg i (us j) (γs j) s = γs j s := by
      filter_upwards [hEs, husI, hev1] with j hEj hj hj'
      exact B.retrSeg_eqOn_right (γs j).mem hEj hj (show s ∈ Ici (us j) from hj'.le)
    exact Tendsto.congr' (EventuallyEq.symm hev) (hconst hs)

/-- **Uniform convergence**: eventually `max_s ρ(r_{uⱼ}(γⱼ)(s), r_u(γ)(s)) ≤ e`. -/
theorem eventually_supDist_retrSeg_le {e : ℝ} (he : 0 < e) :
    ∀ᶠ j in l, supDist N (B.retrSeg i (us j) (γs j)) (B.retrSeg i u γ) ≤ ENNReal.ofReal e :=
  eventually_supDist_le_of_tendsto_apply hN (C := c) (by
      filter_upwards [husI, hEs] with j hj hEj
      exact ⟨B.retrSeg_mem_pathSpace (γs j).mem hEj hj,
        (B.energy_retrSeg_le (γs j).mem hEj hj).trans hEj.le⟩)
    (B.retrSeg_mem_pathSpace γ.mem hE hu) ((B.energy_retrSeg_le γ.mem hE hu).trans hE.le)
    (fun _ hs => B.tendsto_retrSeg_apply hus hγs husI hu hEs hE hs) he

/-- **Convergence of the speeds in `L²`**: eventually `∫₀¹ (ṡⱼ − ṡ)² ≤ e`, `ṡⱼ`, `ṡ` the speeds
of `r_{uⱼ}(γⱼ)` and `r_u(γ)`. -/
theorem eventually_integral_retrSeg_le {e : ℝ} (he : 0 < e) :
    ∀ᶠ j in l, ∫ τ in (0 : ℝ)..1,
      (speed (B.retrSeg i (us j) (γs j)) τ - speed (B.retrSeg i u γ) τ) ^ 2 ≤ e := by
  have ha01 : B.t i.castSucc ∈ Icc (0 : ℝ) 1 := ⟨B.t_nonneg _, B.t_le_one _⟩
  have hu01 := B.u_mem hu
  have hR₀ := B.retrSeg_mem_pathSpace γ.mem hE hu
  have hint : ∀ {α α' : ℝ → V}, α ∈ pathSpace N p q → α' ∈ pathSpace N p q → ∀ x y : ℝ,
      0 ≤ x → x ≤ y → y ≤ 1 →
        IntervalIntegrable (fun τ => (speed α τ - speed α' τ) ^ 2) volume x y :=
    fun hα hα' x y hx hxy hy => intervalIntegrable_speed hα hα' (Φ := fun z => (z.1 - z.2) ^ 2)
      (by fun_prop) hx hxy hy
  -- `L²` closeness of `γⱼ` and `γ`
  have hl2 : ∀ᶠ j in l, l2Dist (γs j) γ ^ 2 ≤ e / 4 := by
    have := (tendsto_l2Dist hγs).pow 2
    rw [zero_pow two_ne_zero] at this
    exact this.eventually (ge_mem_nhds (by positivity))
  -- the parts after `u` and `uⱼ` are `γ` and `γⱼ`
  have htail : ∀ j, energy (γs j) 0 1 < c → us j ∈ Icc (B.t i.castSucc) (B.t i.succ) →
      ∀ w, max (us j) u ≤ w → w ≤ 1 →
        ∫ τ in w..1, (speed (B.retrSeg i (us j) (γs j)) τ - speed (B.retrSeg i u γ) τ) ^ 2 ≤
          l2Dist (γs j) γ ^ 2 := by
    intro j hEj hjI w hw hw1
    have hcongr : ∫ τ in w..1, (speed (B.retrSeg i (us j) (γs j)) τ -
        speed (B.retrSeg i u γ) τ) ^ 2 = ∫ τ in w..1, (speed (γs j) τ - speed γ τ) ^ 2 :=
      intervalIntegral.integral_congr_Ioo_of_le hw1 fun τ hτ => by
        rw [speed_congr ((B.retrSeg_eqOn_right (γs j).mem hEj hjI).mono fun x hx =>
            (show us j ≤ x from (le_max_left _ _).trans (hw.trans hx.1))) hτ,
          speed_congr ((B.retrSeg_eqOn_right γ.mem hE hu).mono fun x hx =>
            (show u ≤ x from (le_max_right _ _).trans (hw.trans hx.1))) hτ]
    rw [hcongr]
    exact integral_speed_sub_sq_le (γs j).mem γ.mem
      ((B.u_mem hjI).1.trans ((le_max_left _ _).trans hw)) hw1 le_rfl
  -- (1) the broken geodesic part `[0, tᵢ]`
  have h1 : ∀ᶠ j in l, ∫ τ in (0 : ℝ)..B.t i.castSucc,
      (speed (B.retrSeg i (us j) (γs j)) τ - speed (B.retrSeg i u γ) τ) ^ 2 ≤ e / 4 := by
    have hy := B.nodeVal_mem γ.mem hE
    have hpath := B.tendsto_integral_speed_path hy
      (hEs.mono fun j hEj => B.nodeVal_mem (γs j).mem hEj) (B.tendsto_nodeVal hγs)
    filter_upwards [hpath.eventually (ge_mem_nhds (show (0 : ℝ) < e / 4 by positivity)), hEs]
      with j hj hEj
    have hyj := B.nodeVal_mem (γs j).mem hEj
    have hcongr : ∫ τ in (0 : ℝ)..B.t i.castSucc, (speed (B.retrSeg i (us j) (γs j)) τ -
        speed (B.retrSeg i u γ) τ) ^ 2 = ∫ τ in (0 : ℝ)..B.t i.castSucc,
          (speed (B.path (B.nodeVal (γs j))) τ - speed (B.path (B.nodeVal γ)) τ) ^ 2 :=
      intervalIntegral.integral_congr_Ioo_of_le ha01.1 fun τ hτ => by
        rw [speed_congr ((B.retrSeg_eqOn_left i (us j) (γs j)).mono Icc_subset_Iic_self) hτ,
          speed_congr ((B.retrSeg_eqOn_left i u γ).mono Icc_subset_Iic_self) hτ]
    rw [hcongr]
    refine le_trans ?_ hj
    exact intervalIntegral.integral_mono_interval le_rfl ha01.1 ha01.2
      (Eventually.of_forall fun _ => sq_nonneg _)
      (hint (B.path_mem_pathSpace hyj) (B.path_mem_pathSpace hy) 0 1 le_rfl zero_le_one le_rfl)
  -- (2) the part `[tᵢ, 1]`
  have h2 : ∀ᶠ j in l, ∫ τ in B.t i.castSucc..1,
      (speed (B.retrSeg i (us j) (γs j)) τ - speed (B.retrSeg i u γ) τ) ^ 2 ≤ 3 * e / 4 := by
    rcases eq_or_lt_of_le hu.1 with hua | hau
    · -- the degenerate case `u = tᵢ`: everything is controlled by energies on `[tᵢ, uⱼ]`
      obtain ⟨δ₁, hδ₁, hev₁⟩ := eventually_energy_lt hγs (η := e / 16) (by positivity)
      obtain ⟨δ₂, hδ₂, hev₂⟩ := eventually_energy_lt (tendsto_const_nhds (x := γ) (f := l))
        (η := e / 16) (by positivity)
      have hclose : ∀ᶠ j in l, us j - B.t i.castSucc < min δ₁ δ₂ := by
        have : Tendsto (fun j => us j - B.t i.castSucc) l (𝓝 0) := by
          have := hus.sub_const (B.t i.castSucc)
          rwa [← hua, sub_self] at this
        exact this.eventually (gt_mem_nhds (lt_min hδ₁ hδ₂))
      filter_upwards [hev₁, hev₂, hclose, hl2, husI, hEs] with j hj₁ hj₂ hjc hjl hjI hEj
      have hRj := B.retrSeg_mem_pathSpace (γs j).mem hEj hjI
      have huj01 := B.u_mem hjI
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := us j)
        (hint hRj hR₀ _ _ ha01.1 hjI.1 huj01.2) (hint hRj hR₀ _ _ huj01.1 huj01.2 le_rfl)]
      have hA := integral_speed_sub_sq_le_energy hRj hR₀ ha01.1 hjI.1 huj01.2
      have hER := B.energy_retrSeg_mid_le (γs j).mem hEj hjI
      have hER₀ : energy (B.retrSeg i u γ) (B.t i.castSucc) (us j) =
          energy γ (B.t i.castSucc) (us j) :=
        energy_congr_Icc hjI.1 fun τ hτ => B.retrSeg_eqOn_right γ.mem hE hu
          (show u ≤ τ by rw [← hua]; exact hτ.1)
      have e₁ : energy (γs j) (B.t i.castSucc) (us j) < e / 16 :=
        hj₁ _ _ ha01.1 hjI.1 huj01.2 (hjc.trans_le (min_le_left _ _))
      have e₂ : energy γ (B.t i.castSucc) (us j) < e / 16 :=
        hj₂ _ _ ha01.1 hjI.1 huj01.2 (hjc.trans_le (min_le_right _ _))
      have hC := htail j hEj hjI (us j) (max_le le_rfl (by rw [← hua]; exact hjI.1)) huj01.2
      linarith
    · -- the case `tᵢ < u`
      have hJ := B.mem_joinable γ.mem hE i le_rfl hu.1 hu.2
      have hJs : ∀ᶠ j in l, (γs j (B.t i.castSucc), γs j (us j)) ∈ B.joinable := by
        filter_upwards [hEs, husI] with j hEj hj
        exact B.mem_joinable (γs j).mem hEj i le_rfl hj.1 hj.2
      -- the speeds of the short geodesics converge
      have hσ : Tendsto (fun j => ‖B.joinVec (γs j (B.t i.castSucc)) (γs j (us j))‖ /
          (us j - B.t i.castSucc)) l
          (𝓝 (‖B.joinVec (γ (B.t i.castSucc)) (γ u)‖ / (u - B.t i.castSucc))) := by
        have h1 := tendsto_apply hγs tendsto_const_nhds (Eventually.of_forall fun _ => ha01) ha01
        have h2 := tendsto_apply hγs hus (husI.mono fun j hj => B.u_mem hj) hu01
        have hjv := (B.continuousWithinAt_joinVec hJ).tendsto.comp
          (tendsto_nhdsWithin_iff.2 ⟨h1.prodMk_nhds h2, hJs⟩)
        exact hjv.norm.div (hus.sub_const _) (sub_pos.2 hau).ne'
      have hσ2 : ∀ᶠ j in l, (‖B.joinVec (γs j (B.t i.castSucc)) (γs j (us j))‖ /
          (us j - B.t i.castSucc) - ‖B.joinVec (γ (B.t i.castSucc)) (γ u)‖ /
            (u - B.t i.castSucc)) ^ 2 ≤ e / 8 := by
        have := (hσ.sub_const (‖B.joinVec (γ (B.t i.castSucc)) (γ u)‖ /
          (u - B.t i.castSucc))).pow 2
        rw [sub_self, zero_pow two_ne_zero] at this
        exact this.eventually (ge_mem_nhds (by positivity))
      have hσE : ∀ᶠ j in l, |us j - u| * (‖B.joinVec (γs j (B.t i.castSucc)) (γs j (us j))‖ /
          (us j - B.t i.castSucc)) ^ 2 ≤ e / 32 := by
        have := ((hus.sub_const u).abs).mul (hσ.pow 2)
        rw [sub_self, abs_zero, zero_mul] at this
        exact this.eventually (ge_mem_nhds (by positivity))
      obtain ⟨δ₁, hδ₁, hev₁⟩ := eventually_energy_lt hγs (η := e / 32) (by positivity)
      let R₀P : PathSp N p q := ⟨B.retrSeg i u γ, hR₀⟩
      obtain ⟨δ₂, hδ₂, hev₂⟩ := eventually_energy_lt (tendsto_const_nhds (x := R₀P) (f := l))
        (η := e / 32) (by positivity)
      have hclose : ∀ᶠ j in l, |us j - u| < min δ₁ δ₂ := by
        have : Tendsto (fun j => |us j - u|) l (𝓝 0) := by
          have := (hus.sub_const u).abs
          rwa [sub_self, abs_zero] at this
        exact this.eventually (gt_mem_nhds (lt_min hδ₁ hδ₂))
      have hgt : ∀ᶠ j in l, B.t i.castSucc < us j := hus.eventually (lt_mem_nhds hau)
      filter_upwards [hev₁, hev₂, hclose, hl2, husI, hEs, hσ2, hσE, hgt]
        with j hj₁ hj₂ hjc hjl hjI hEj hjσ2 hjσE hjgt
      have hRj := B.retrSeg_mem_pathSpace (γs j).mem hEj hjI
      have huj01 := B.u_mem hjI
      have hav : B.t i.castSucc ≤ min (us j) u := le_min hjI.1 hu.1
      have hvw : min (us j) u ≤ max (us j) u := min_le_max
      have hw1 : max (us j) u ≤ 1 := max_le huj01.2 hu01.2
      have hv0 : 0 ≤ min (us j) u := ha01.1.trans hav
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := min (us j) u)
        (hint hRj hR₀ _ _ ha01.1 hav (hvw.trans hw1)) (hint hRj hR₀ _ _ hv0 (hvw.trans hw1) le_rfl),
        ← intervalIntegral.integral_add_adjacent_intervals (b := max (us j) u)
        (hint hRj hR₀ _ _ hv0 hvw hw1) (hint hRj hR₀ _ _ (hv0.trans hvw) hw1 le_rfl)]
      -- (i) `[tᵢ, min]`: both are short geodesics of constant speed
      have hi : ∫ τ in B.t i.castSucc..min (us j) u, (speed (B.retrSeg i (us j) (γs j)) τ -
          speed (B.retrSeg i u γ) τ) ^ 2 ≤ e / 8 := by
        have hcongr := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) hav
          (f := fun τ => (speed (B.retrSeg i (us j) (γs j)) τ - speed (B.retrSeg i u γ) τ) ^ 2)
          (g := fun _ => (‖B.joinVec (γs j (B.t i.castSucc)) (γs j (us j))‖ /
            (us j - B.t i.castSucc) - ‖B.joinVec (γ (B.t i.castSucc)) (γ u)‖ /
              (u - B.t i.castSucc)) ^ 2) fun τ hτ => by
          simp only
          rw [B.speed_retrSeg_mid (γs j).mem hEj hjI hjgt ⟨hτ.1, hτ.2.trans_le (min_le_left _ _)⟩,
            B.speed_retrSeg_mid γ.mem hE hu hau ⟨hτ.1, hτ.2.trans_le (min_le_right _ _)⟩]
        rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
        have hlen : min (us j) u - B.t i.castSucc ≤ 1 := by
          linarith [hu01.2, min_le_right (us j) u, ha01.1]
        nlinarith [sq_nonneg (‖B.joinVec (γs j (B.t i.castSucc)) (γs j (us j))‖ /
            (us j - B.t i.castSucc) - ‖B.joinVec (γ (B.t i.castSucc)) (γ u)‖ /
              (u - B.t i.castSucc)), sub_nonneg.2 hav]
      -- (ii) `[min, max]`: short, so small energies
      have hii := integral_speed_sub_sq_le_energy hRj hR₀ hv0 hvw hw1
      have hlen : max (us j) u - min (us j) u = |us j - u| := by
        rcases le_total (us j) u with h | h
        · rw [max_eq_right h, min_eq_left h, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
        · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]
      have eR₀ : energy (B.retrSeg i u γ) (min (us j) u) (max (us j) u) < e / 32 :=
        hj₂ _ _ hv0 hvw hw1 (by rw [hlen]; exact hjc.trans_le (min_le_right _ _))
      have eRj : energy (B.retrSeg i (us j) (γs j)) (min (us j) u) (max (us j) u) ≤ e / 32 := by
        rcases le_total (us j) u with h | h
        · rw [max_eq_right h, min_eq_left h, energy_congr_Icc h
            ((B.retrSeg_eqOn_right (γs j).mem hEj hjI).mono Icc_subset_Ici_self)]
          refine (hj₁ _ _ huj01.1 h hu01.2 ?_).le
          rw [← abs_of_nonneg (sub_nonneg.2 h), abs_sub_comm]
          exact hjc.trans_le (min_le_left _ _)
        · rw [max_eq_left h, min_eq_right h, B.energy_retrSeg_mid (γs j).mem hEj hjI hjgt hu.1 h
            le_rfl]
          rw [abs_of_nonneg (sub_nonneg.2 h)] at hjσE
          linarith
      -- (iii) `[max, 1]`: `γⱼ` and `γ`
      have hiii := htail j hEj hjI _ le_rfl hw1
      linarith
  filter_upwards [h1, h2, husI, hEs] with j hj1 hj2 hjI hEj
  have hRj := B.retrSeg_mem_pathSpace (γs j).mem hEj hjI
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := B.t i.castSucc)
    (hint hRj hR₀ _ _ le_rfl ha01.1 ha01.2) (hint hRj hR₀ _ _ ha01.1 ha01.2 le_rfl)]
  linarith

/-- **Continuity of `r_u` in both variables** (Milnor p. 91), on the `i`-th segment: if `uⱼ → u`
in `[tᵢ, t_{i+1}]` and `γⱼ → γ` in `Int Ω^c`, then `d(r_{uⱼ}(γⱼ), r_u(γ)) → 0`. -/
theorem tendsto_retrSeg :
    Tendsto (fun j => supDist N (B.retrSeg i (us j) (γs j)) (B.retrSeg i u γ) +
      ENNReal.ofReal (l2Dist (B.retrSeg i (us j) (γs j)) (B.retrSeg i u γ))) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hr' : 0 < r := ENNReal.ofReal_pos.1 hr
  filter_upwards [B.eventually_supDist_retrSeg_le hus hγs husI hu hEs hE (e := r / 2)
    (by positivity), B.eventually_integral_retrSeg_le hus hγs husI hu hEs hE (e := (r / 2) ^ 2)
    (by positivity)] with j h1 h2
  have h3 : l2Dist (B.retrSeg i (us j) (γs j)) (B.retrSeg i u γ) ≤ r / 2 := by
    rw [l2Dist]
    calc √(∫ τ in (0 : ℝ)..1, (speed (B.retrSeg i (us j) (γs j)) τ -
          speed (B.retrSeg i u γ) τ) ^ 2) ≤ √((r / 2) ^ 2) := Real.sqrt_le_sqrt h2
      _ = r / 2 := Real.sqrt_sq (by positivity)
  calc supDist N (B.retrSeg i (us j) (γs j)) (B.retrSeg i u γ) +
        ENNReal.ofReal (l2Dist (B.retrSeg i (us j) (γs j)) (B.retrSeg i u γ))
      ≤ ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) :=
        add_le_add h1 (ENNReal.ofReal_le_ofReal h3)
    _ = ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
    _ ≤ ε := hrε.le

end Conv

end BrokenSetup

end Morse
