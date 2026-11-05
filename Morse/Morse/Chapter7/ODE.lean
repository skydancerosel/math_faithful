import Morse.Flow.Smooth

/-!
Milnor, *Morse Theory*, §10, p. 56: the existence and uniqueness theorem for ordinary differential
equations that Milnor quotes as Theorem 10.1.

# Local solutions of smooth differential equations, with smooth dependence on the initial data

## Milnor's text, paraphrased

**Theorem 10.1** (p. 56) is about a system `d²u/dt² = F(u, du/dt)`, where `F` is an `n`-tuple of
`C^∞` functions on a neighbourhood `U` of a point `(u₁, v₁) ∈ ℝ²ⁿ`: there are a neighbourhood `W` of
`(u₁, v₁)` and an `ε > 0` such that for each `(u₀, v₀) ∈ W` the equation has a unique solution,
defined for `|t| < ε`, with `u(0) = u₀` and `u'(0) = v₀`; and `(u₀, v₀, t) ↦ u(t)` is `C^∞` on
`W × (-ε, ε)`.  Milnor reduces the system to the first-order system `du/dt = v`,
`dv/dt = F(u, v)`, and quotes Graves, *The Theory of Functions of Real Variables*, p. 166.

## What is proved here

For a `C^∞` vector field `G` on an open set `U` of a finite-dimensional real normed space `E`:

* `Morse.exists_localFlow`: **local existence with smooth dependence on the initial point.**
  Multiply `G` by a bump function equal to `1` near `x₁` and supported in `U`.  The product is a
  smooth vector field on all of `E` with compact support, so it has a global flow which is smooth in
  `(t, x)` (`Morse/Flow/Global.lean`, `Morse.contDiff_flow_uncurry`).  The speed of its flow lines
  is bounded, so those starting near `x₁` stay, for a time bounded below independently of the
  starting point, where the bump function is `1`; there they solve `x' = G(x)`.
* `Morse.ode_eventuallyEq`, `Morse.ode_eqOn`: **uniqueness.**  Two solutions with values in `U`
  which agree at one time agree near it (Grönwall's inequality, `G` being Lipschitz near the common
  value), and hence on every open interval on which both are defined
  (`Morse.eqOn_of_eventuallyEq`, a connectedness argument).
* `Morse.theorem_10_1`, `Morse.theorem_10_1_unique`: **Milnor's Theorem 10.1**, the second-order
  statement, with `ℝⁿ` replaced by `E`.

## What Milnor leaves implicit

* The theorem quoted from Graves gives uniqueness for small times.  Uniqueness on a whole interval
  is the connectedness argument of `Morse.eqOn_of_eventuallyEq`; Milnor uses it silently each time
  he speaks of "the unique geodesic" (see `Morse/Chapter7/Geodesic.lean`).
* The smooth dependence is asserted on a product `W × (-ε, ε)`: the time of existence must be
  bounded below uniformly for initial points in `W`.  The bump-function construction gives this at
  once, from the bound on the speed.
-/

open Set Filter Topology Metric Function
open scoped ContDiff NNReal

noncomputable section

namespace Morse

/-! ### A connectedness principle -/

/-- Two functions on an open preconnected set `s ⊆ ℝ`, continuous on `s`, which agree at one point
of `s` and agree near every point of `s` at which they agree, agree on `s`. -/
theorem eqOn_of_eventuallyEq {F : Type*} [TopologicalSpace F] [T2Space F] {f g : ℝ → F}
    {s : Set ℝ} (hs : IsOpen s) (hs' : IsPreconnected s) (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) (hloc : ∀ t ∈ s, f t = g t → f =ᶠ[𝓝 t] g) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (h₀ : f t₀ = g t₀) : EqOn f g s := by
  set u : Set ℝ := {t | f =ᶠ[𝓝 t] g} with hu
  have hu_open : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hsub : s ⊆ u := by
    refine hs'.subset_of_closure_inter_subset hu_open ⟨t₀, ht₀, hloc t₀ ht₀ h₀⟩ ?_
    rintro t ⟨htc, hts⟩
    refine hloc t hts ?_
    have hfreq : ∃ᶠ τ in 𝓝 t, f τ = g τ :=
      (mem_closure_iff_frequently.1 htc).mono fun τ hτ => hτ.self_of_nhds
    exact tendsto_nhds_unique_of_frequently_eq ((hf t hts).continuousAt (hs.mem_nhds hts))
      ((hg t hts).continuousAt (hs.mem_nhds hts)) hfreq
  intro t ht
  exact (hsub ht).self_of_nhds

/-! ### Uniqueness -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Prod

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂] {f : ℝ → E₁ × E₂} {f' : E₁ × E₂} {t : ℝ}

/-- The first component of a curve in a product. -/
theorem hasDerivAt_fst_comp (h : HasDerivAt f f' t) : HasDerivAt (fun s => (f s).1) f'.1 t :=
  (hasFDerivAt_fst (𝕜 := ℝ) (p := f t)).comp_hasDerivAt t h

/-- The second component of a curve in a product. -/
theorem hasDerivAt_snd_comp (h : HasDerivAt f f' t) : HasDerivAt (fun s => (f s).2) f'.2 t :=
  (hasFDerivAt_snd (𝕜 := ℝ) (p := f t)).comp_hasDerivAt t h

end Prod

/-- **Local uniqueness** for `x' = G(x)`, `G` of class `C¹` near the initial value: two solutions
which agree at `t₀` agree near `t₀`. -/
theorem ode_eventuallyEq {G : E → E} {f g : ℝ → E} {t₀ : ℝ} (hG : ContDiffAt ℝ 1 G (f t₀))
    (hf : ∀ᶠ t in 𝓝 t₀, HasDerivAt f (G (f t)) t) (hg : ∀ᶠ t in 𝓝 t₀, HasDerivAt g (G (g t)) t)
    (h : f t₀ = g t₀) : f =ᶠ[𝓝 t₀] g := by
  obtain ⟨K, S, hS, hK⟩ := hG.exists_lipschitzOnWith
  have hfS : ∀ᶠ t in 𝓝 t₀, f t ∈ S := hf.self_of_nhds.continuousAt.eventually hS
  have hgS : ∀ᶠ t in 𝓝 t₀, g t ∈ S :=
    hg.self_of_nhds.continuousAt.eventually (by rw [← h]; exact hS)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hf.and (hg.and (hfS.and hgS)))
  have hI : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), t ∈ ball t₀ ε := fun t ht => by
    rw [Real.ball_eq_Ioo]; exact ht
  have heq : EqOn f g (Ioo (t₀ - ε) (t₀ + ε)) :=
    ODE_solution_unique_of_mem_Ioo (v := fun _ => G) (s := fun _ => S) (K := K)
      (fun _ _ => hK) ⟨by linarith, by linarith⟩
      (fun t ht => ⟨(hball t (hI t ht)).1, (hball t (hI t ht)).2.2.1⟩)
      (fun t ht => ⟨(hball t (hI t ht)).2.1, (hball t (hI t ht)).2.2.2⟩) h
  filter_upwards [Ioo_mem_nhds (by linarith : t₀ - ε < t₀) (by linarith : t₀ < t₀ + ε)] with t ht
  exact heq ht

/-- **Uniqueness on an interval**: two solutions of `x' = G(x)` on an open preconnected set
`s ⊆ ℝ`, with values in the open set `U` on which `G` is `C¹`, which agree at one time, agree
on `s`. -/
theorem ode_eqOn {G : E → E} {U : Set E} (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U) {s : Set ℝ}
    (hs : IsOpen s) (hs' : IsPreconnected s) {f g : ℝ → E}
    (hf : ∀ t ∈ s, HasDerivAt f (G (f t)) t ∧ f t ∈ U)
    (hg : ∀ t ∈ s, HasDerivAt g (G (g t)) t ∧ g t ∈ U) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (h : f t₀ = g t₀) : EqOn f g s :=
  eqOn_of_eventuallyEq hs hs' (fun t ht => (hf t ht).1.continuousAt.continuousWithinAt)
    (fun t ht => (hg t ht).1.continuousAt.continuousWithinAt)
    (fun t ht hfg => ode_eventuallyEq (hG.contDiffAt (hU.mem_nhds (hf t ht).2))
      (eventually_of_mem (hs.mem_nhds ht) fun τ hτ => (hf τ hτ).1)
      (eventually_of_mem (hs.mem_nhds ht) fun τ hτ => (hg τ hτ).1) hfg) ht₀ h

/-! ### Local existence, with smooth dependence on the initial point -/

variable [FiniteDimensional ℝ E]

/-- **Local existence with smooth dependence on the initial point.**  For a `C^∞` field `G` on an
open set `U ∋ x₁` there are a smooth map `φ : ℝ × E → E` and `r, τ > 0` such that for every `x`
with `‖x − x₁‖ < r`, `t ↦ φ t x` is a solution of `x' = G(x)` on `(-τ, τ)`, with values in `U`,
starting at `x`. -/
theorem exists_localFlow {G : E → E} {U : Set E} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    {x₁ : E} (hx₁ : x₁ ∈ U) :
    ∃ φ : ℝ → E → E, ContDiff ℝ ∞ (fun p : ℝ × E => φ p.1 p.2) ∧ ∃ r > 0, ∃ τ > 0,
      ∀ x ∈ ball x₁ r, φ 0 x = x ∧
        ∀ t ∈ Ioo (-τ) τ, φ t x ∈ U ∧ HasDerivAt (fun s => φ s x) (G (φ t x)) t := by
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.1 hU x₁ hx₁
  set R := ρ / 3 with hR
  have hR0 : 0 < R := by positivity
  let χ : ContDiffBump x₁ := ⟨R, 2 * R, hR0, by linarith⟩
  have hcl : closedBall x₁ (2 * R) ⊆ U := fun y hy =>
    hρU (lt_of_le_of_lt (mem_closedBall.1 hy) (by linarith))
  set X : E → E := fun y => χ y • G y with hX
  have hXs : ContDiff ℝ ∞ X := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact (χ.contDiff.contDiffAt).smul (hG.contDiffAt (hU.mem_nhds hy))
    · have hy' : y ∉ tsupport χ := by
        rw [χ.tsupport_eq]
        exact fun h => hy (hcl h)
      have h0 : X =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hy'] with z hz
        simp [hX, image_eq_zero_of_notMem_tsupport hz]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  have hXc : HasCompactSupport X := χ.hasCompactSupport.smul_right
  have hb := IsBddLipschitz.of_contDiff (hXs.of_le (by exact_mod_cast le_top)) hXc
  obtain ⟨M, hM⟩ := hb.bounded
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₁)
  refine ⟨flow X, contDiff_flow_uncurry (n := ⊤) hXs le_top hXc, R / 2, by positivity,
    R / (2 * (M + 1)), by positivity, fun x hx => ⟨hb.flow_zero x, fun t ht => ?_⟩⟩
  have ht' : |t| < R / (2 * (M + 1)) := abs_lt.2 ⟨by linarith [ht.1], ht.2⟩
  have h2 : M * |t| < R / 2 := by
    have hM1 : 0 < M + 1 := by linarith
    calc M * |t| ≤ (M + 1) * |t| := by nlinarith [abs_nonneg t]
      _ < (M + 1) * (R / (2 * (M + 1))) := mul_lt_mul_of_pos_left ht' hM1
      _ = R / 2 := by field_simp
  have hdist : dist (flow X t x) x < R / 2 := by
    have h1 := hb.dist_flow_flow_le hM t 0 x
    rw [hb.flow_zero, sub_zero] at h1
    linarith
  have hmem : flow X t x ∈ closedBall x₁ R := by
    rw [mem_closedBall]
    have := dist_triangle (flow X t x) x x₁
    rw [mem_ball] at hx
    linarith
  have hχ : χ (flow X t x) = 1 := χ.one_of_mem_closedBall hmem
  refine ⟨hcl (closedBall_subset_closedBall (by linarith) hmem), ?_⟩
  have hXG : X (flow X t x) = G (flow X t x) := by
    change χ (flow X t x) • G (flow X t x) = _
    rw [hχ, one_smul]
  have := hb.hasDerivAt_flow t x
  rwa [hXG] at this

/-! ### Theorem 10.1 -/

/-- **Milnor's Theorem 10.1** (p. 56), existence and smooth dependence: for `F` smooth on an open
set `U ⊆ E × E` and `z₁ ∈ U` there are a neighbourhood `W` of `z₁`, an `ε > 0` and a map
`(z, t) ↦ u z t`, smooth on `W × (-ε, ε)`, such that for `z = (u₀, v₀) ∈ W`, `t ↦ u z t` solves
`u'' = F(u, u')` for `|t| < ε` with `(u, u') ∈ U`, `u(0) = u₀` and `u'(0) = v₀`. -/
theorem theorem_10_1 {F : E × E → E} {U : Set (E × E)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    {z₁ : E × E} (hz₁ : z₁ ∈ U) :
    ∃ W ∈ 𝓝 z₁, ∃ ε > 0, ∃ u : E × E → ℝ → E,
      ContDiffOn ℝ ∞ (fun p : (E × E) × ℝ => u p.1 p.2) (W ×ˢ Ioo (-ε) ε) ∧
      ∀ z ∈ W, u z 0 = z.1 ∧ deriv (u z) 0 = z.2 ∧ ∀ t ∈ Ioo (-ε) ε,
        (u z t, deriv (u z) t) ∈ U ∧ HasDerivAt (deriv (u z)) (F (u z t, deriv (u z) t)) t := by
  set G : E × E → E × E := fun z => (z.2, F z) with hG
  have hGs : ContDiffOn ℝ ∞ G U := contDiff_snd.contDiffOn.prodMk hF
  obtain ⟨φ, hφ, r, hr, τ, hτ, hsol⟩ := exists_localFlow hU hGs hz₁
  have hd : ∀ z ∈ ball z₁ r, ∀ t ∈ Ioo (-τ) τ, deriv (fun s => (φ s z).1) t = (φ t z).2 :=
    fun z hz t ht => (hasDerivAt_fst_comp ((hsol z hz).2 t ht).2).deriv
  refine ⟨ball z₁ r, ball_mem_nhds z₁ hr, τ, hτ, fun z t => (φ t z).1,
    (contDiff_fst.comp (hφ.comp (contDiff_snd.prodMk contDiff_fst))).contDiffOn,
    fun z hz => ⟨by simp [(hsol z hz).1], ?_, fun t ht => ?_⟩⟩
  · rw [hd z hz 0 ⟨by linarith, hτ⟩, (hsol z hz).1]
  · have hev : deriv (fun s => (φ s z).1) =ᶠ[𝓝 t] fun s => (φ s z).2 := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact hd z hz s hs
    have hpair : ((φ t z).1, deriv (fun s => (φ s z).1) t) = φ t z := by
      rw [hd z hz t ht]
    refine ⟨by rw [hpair]; exact ((hsol z hz).2 t ht).1, ?_⟩
    rw [hpair]
    exact (hasDerivAt_snd_comp ((hsol z hz).2 t ht).2).congr_of_eventuallyEq hev

omit [FiniteDimensional ℝ E] in
/-- **Milnor's Theorem 10.1** (p. 56), uniqueness: two solutions of `u'' = F(u, u')` on an open
interval `s`, with `(u, u')` in the open set `U` on which `F` is `C¹`, having the same position and
velocity at one time, agree on `s`. -/
theorem theorem_10_1_unique {F : E × E → E} {U : Set (E × E)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) {s : Set ℝ} (hs : IsOpen s) (hs' : IsPreconnected s)
    {u₁ u₂ v₁ v₂ : ℝ → E}
    (h₁ : ∀ t ∈ s, HasDerivAt u₁ (v₁ t) t ∧ HasDerivAt v₁ (F (u₁ t, v₁ t)) t ∧ (u₁ t, v₁ t) ∈ U)
    (h₂ : ∀ t ∈ s, HasDerivAt u₂ (v₂ t) t ∧ HasDerivAt v₂ (F (u₂ t, v₂ t)) t ∧ (u₂ t, v₂ t) ∈ U)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) (hu : u₁ t₀ = u₂ t₀) (hv : v₁ t₀ = v₂ t₀) : EqOn u₁ u₂ s := by
  set G : E × E → E × E := fun z => (z.2, F z) with hG
  have hGs : ContDiffOn ℝ 1 G U := contDiff_snd.contDiffOn.prodMk hF
  have h := ode_eqOn (f := fun t => (u₁ t, v₁ t)) (g := fun t => (u₂ t, v₂ t)) hU hGs hs hs'
    (fun t ht => ⟨((h₁ t ht).1.prodMk (h₁ t ht).2.1), (h₁ t ht).2.2⟩)
    (fun t ht => ⟨((h₂ t ht).1.prodMk (h₂ t ht).2.1), (h₂ t ht).2.2⟩) ht₀
    (by rw [hu, hv])
  exact fun t ht => congrArg Prod.fst (h ht)

end Morse
