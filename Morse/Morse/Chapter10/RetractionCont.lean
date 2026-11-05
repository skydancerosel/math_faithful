import Morse.Chapter10.Retraction

/-!
Milnor, *Morse Theory*, §16, p. 91: the continuity of the deformation `r_u` (Milnor: "it is easily
verified that `r_u(ω)` is continuous as a function of both variables"), first part: the
continuity of the ingredients, for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# Continuity of the ingredients of `r_u`

## In the embedded setting

* `Morse.mem_expDom_smul`: `exp_x(θv)` is defined for `0 ≤ θ ≤ 1` if `exp_x(v)` is.
* `Morse.tendsto_of_tendsto_riemDist` (with `Morse.tendsto_riemDist_of_tendsto`,
  `Morse/Chapter7/Metric.lean`): on `N`, convergence for `ρ` and for the norm of `V` agree.
* `Morse.BrokenSetup.joinable` (pairs of points of `S` at distance `< δ`),
  `Morse.BrokenSetup.continuousWithinAt_joinVec`, `Morse.BrokenSetup.continuousWithinAt_shortGeo`:
  **the short join vector and the short geodesics `θ ↦ exp_x(θ v(x, y))` depend continuously on
  their end points** (Corollary 10.8 together with the continuity of `exp`,
  `Morse.eventually_mem_expDom_and_continuousWithinAt_exp`).
* `Morse.PathSp.riemDist_le_sqrt`: `ρ(γ(s), γ(τ)) ≤ √(|τ − s| E(γ))` — paths of bounded energy
  are equicontinuous.
* `Morse.PathSp.tendsto_riemDist_apply`: if `γⱼ → γ` in `Ω` and `σⱼ → σ`, then `γⱼ(σⱼ) → γ(σ)`.
* `Morse.PathSp.eventually_energy_lt`: **Lemma 16.B of the exposition along a filter**: if
  `γⱼ → γ` in `Ω`, the energies of the `γⱼ` on short intervals are eventually uniformly small.
* `Morse.PathSp.integral_speed_sub_sq_le`, `Morse.PathSp.integral_speed_sub_sq_le_energy`:
  bounds for the `L²` distance of the speeds on a subinterval.
* `Morse.BrokenSetup.integral_speed_path_sub_sq`, `Morse.BrokenSetup.tendsto_integral_speed_path`:
  `∫₀¹ (s' − s)² = Σᵢ (ρ'ᵢ − ρᵢ)²/(t_{i+1} − tᵢ)` for two broken geodesics, so **the speeds of
  broken geodesics depend continuously (in `L²`) on the break points**.
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Interval NNReal

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-- `exp_x(θ v)` is defined for `0 ≤ θ ≤ 1` if `exp_x(v)` is. -/
theorem mem_expDom_smul {x v : V} (h : (x, v) ∈ expDom hN) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    (x, θ • v) ∈ expDom hN := by
  obtain ⟨γ, hγ⟩ := h
  obtain ⟨δ, hδ, -, hexp⟩ := hγ.exp_smul
  exact ⟨_, (hexp θ ⟨by linarith [hθ.1], by linarith [hθ.2]⟩).1⟩

section Conv

variable {ι : Type*} {l : Filter ι}

/-- Convergence for `ρ` implies convergence for the norm (`ρ` dominates the norm distance). -/
theorem tendsto_of_tendsto_riemDist {xs : ι → V} {x : V}
    (h : Tendsto (fun j => riemDist (N := N) (xs j) x) l (𝓝 0)) : Tendsto xs l (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun j => (riemDist (N := N) (xs j) x).toReal) l (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  refine squeeze_zero' (Eventually.of_forall fun j => norm_nonneg _) ?_ h1
  filter_upwards [h.eventually (gt_mem_nhds zero_lt_one)] with j hj
  have := ofReal_norm_sub_le_riemDist (N := N) (xs j) x
  rw [norm_sub_rev]
  exact (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_lt hj)).1 this

end Conv

/-! ### The short geodesics depend continuously on their end points -/

namespace BrokenSetup

variable {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

/-- **Pairs of points of `S` at distance `< δ`**: those joined by a short geodesic. -/
def joinable : Set (V × V) :=
  {z | z.1 ∈ closedRiemBall N p √c ∧ z.2 ∈ closedRiemBall N p √c ∧
    riemDist (N := N) z.1 z.2 < ENNReal.ofReal B.δ}

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **The short join vector depends continuously on its end points** (Corollary 10.8: near a pair
of `joinable`, it is the restriction of a smooth map). -/
theorem continuousWithinAt_joinVec {z : V × V} (hz : z ∈ B.joinable) :
    ContinuousWithinAt (fun z : V × V => B.joinVec z.1 z.2) B.joinable z := by
  obtain ⟨x, y⟩ := z
  obtain ⟨hx, hy, hxy⟩ := hz
  obtain ⟨-, -, -, -, -, -, O₂, hO₂, hmem, G, hG, -, hGspec⟩ :=
    B.join ⟨x, hx.1⟩ ⟨y, hy.1⟩ hx hy hxy
  have key : ∀ w ∈ B.joinable ∩ O₂, B.joinVec w.1 w.2 = G w := by
    rintro w ⟨⟨hw1, hw2, hw12⟩, hwO⟩
    obtain ⟨hGT, hGδ, hGexp⟩ := hGspec ⟨w.1, hw1.1⟩ ⟨w.2, hw2.1⟩ hwO hw12
    exact ((B.joinVec_spec hw1 hw2 hw12).2.2.2.2 _ ((prj_eq_self_iff hN hw1.1).2 hGT) hGδ
      hGexp).symm
  have hev : (fun w : V × V => B.joinVec w.1 w.2) =ᶠ[𝓝[B.joinable] (x, y)] G := by
    filter_upwards [inter_mem_nhdsWithin B.joinable (hO₂.mem_nhds hmem)] with w hw
    exact key w hw
  exact ((hG.continuousOn.continuousAt (hO₂.mem_nhds hmem)).continuousWithinAt
    ).congr_of_eventuallyEq hev (key _ ⟨⟨hx, hy, hxy⟩, hmem⟩)

/-- **The short geodesics depend continuously on their end points**: `(x, y, θ) ↦ exp_x(θ v(x, y))`
is continuous on `joinable × [0, 1]`. -/
theorem continuousWithinAt_shortGeo {z : V × V} (hz : z ∈ B.joinable) {θ : ℝ}
    (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ContinuousWithinAt (fun w : (V × V) × ℝ => exp hN w.1.1 (w.2 • B.joinVec w.1.1 w.1.2))
      (B.joinable ×ˢ Icc 0 1) (z, θ) := by
  have hj := B.continuousWithinAt_joinVec hz
  have h1 : ContinuousWithinAt (fun w : (V × V) × ℝ => (w.1.1, w.2 • B.joinVec w.1.1 w.1.2))
      (B.joinable ×ˢ Icc 0 1) (z, θ) := by
    refine (continuous_fst.comp continuous_fst).continuousWithinAt.prodMk ?_
    have h2 : ContinuousWithinAt (fun w : (V × V) × ℝ => B.joinVec w.1.1 w.1.2)
        (B.joinable ×ˢ Icc 0 1) (z, θ) :=
      ContinuousWithinAt.comp (g := fun z : V × V => B.joinVec z.1 z.2) (f := Prod.fst) hj
        continuousWithinAt_fst fun w hw => hw.1
    exact continuousWithinAt_snd.smul h2
  have hdom : (z.1, θ • B.joinVec z.1 z.2) ∈ expDom hN :=
    mem_expDom_smul (B.mem_expDom_joinVec hz.1 hz.2.1 hz.2.2) hθ
  refine ContinuousWithinAt.comp (f := fun w : (V × V) × ℝ => (w.1.1, w.2 • B.joinVec w.1.1 w.1.2))
    (x := (z, θ)) (eventually_mem_expDom_and_continuousWithinAt_exp hdom).2 h1 fun w hw => ?_
  obtain ⟨⟨hw1, hw2, hw12⟩, -⟩ := hw
  exact ⟨hw1.1, Submodule.smul_mem _ _
    ((prj_eq_self_iff hN hw1.1).1 (B.joinVec_spec hw1 hw2 hw12).1)⟩

end BrokenSetup

/-! ### Paths in `ρ` -/

namespace PathSp

variable {p q : V}

omit [FiniteDimensional ℝ V] in
/-- **Paths of bounded energy are equicontinuous**: `ρ(γ(s), γ(τ)) ≤ √(|τ − s| E(γ))`. -/
theorem riemDist_le_sqrt {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q) {s τ : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    riemDist (N := N) (γ s) (γ τ) ≤ ENNReal.ofReal √(|τ - s| * energy γ 0 1) := by
  have key : ∀ s τ, s ∈ Icc (0 : ℝ) 1 → τ ∈ Icc (0 : ℝ) 1 → s ≤ τ →
      riemDist (N := N) (γ s) (γ τ) ≤ ENNReal.ofReal √(|τ - s| * energy γ 0 1) := by
    intro s τ hs hτ hst
    have hps := hγ.1.mono hs.1 hst hτ.2
    refine (riemDist_le_pathLength (N := N) hps fun σ hσ =>
      hγ.2.1 σ ⟨hs.1.trans hσ.1, hσ.2.trans hτ.2⟩).trans (ENNReal.ofReal_le_ofReal ?_)
    have hE : energy γ s τ ≤ energy γ 0 1 := intervalIntegral.integral_mono_interval hs.1 hst
      hτ.2 (Eventually.of_forall fun _ => sq_nonneg _) hγ.1.intervalIntegrable_norm_deriv_sq
    refine Real.le_sqrt_of_sq_le ((pathLength_sq_le_energy hps).trans ?_)
    rw [abs_of_nonneg (sub_nonneg.2 hst)]
    exact mul_le_mul_of_nonneg_left hE (sub_nonneg.2 hst)
  rcases le_total s τ with h | h
  · exact key s τ hs hτ h
  · rw [riemDist_comm (N := N), abs_sub_comm]
    exact key τ s hτ hs h

section Filter

variable {ι : Type*} {l : Filter ι}

omit [FiniteDimensional ℝ V] in
/-- **`γⱼ(σⱼ) → γ(σ)` for `ρ`**, if `γⱼ → γ` in `Ω` and `σⱼ → σ` in `[0, 1]`. -/
theorem tendsto_riemDist_apply {γs : ι → PathSp N p q} {γ : PathSp N p q}
    (hγs : Tendsto γs l (𝓝 γ)) {σs : ι → ℝ} {σ : ℝ} (hσs : Tendsto σs l (𝓝 σ))
    (hσsI : ∀ᶠ j in l, σs j ∈ Icc (0 : ℝ) 1) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun j => riemDist (N := N) (γs j (σs j)) (γ σ)) l (𝓝 0) := by
  have h1 : Tendsto (fun j => edist (γs j) γ) l (𝓝 0) := tendsto_iff_edist_tendsto_0.1 hγs
  have h2 : Tendsto (fun j => ENNReal.ofReal √(|σ - σs j| * energy γ 0 1)) l (𝓝 0) := by
    have : Tendsto (fun j => √(|σ - σs j| * energy γ 0 1)) l (𝓝 0) := by
      have hc : Continuous fun x : ℝ => √(|σ - x| * energy γ 0 1) := by fun_prop
      simpa [Function.comp_def] using (hc.tendsto σ).comp hσs
    simpa using ENNReal.tendsto_ofReal this
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hσsI] with j hj
  calc riemDist (N := N) (γs j (σs j)) (γ σ)
      ≤ riemDist (N := N) (γs j (σs j)) (γ (σs j)) + riemDist (N := N) (γ (σs j)) (γ σ) :=
        riemDist_triangle _ _ _
    _ ≤ edist (γs j) γ + ENNReal.ofReal √(|σ - σs j| * energy γ 0 1) :=
        add_le_add ((riemDist_le_supDist hj).trans (supDist_le_edist _ _))
          (riemDist_le_sqrt γ.mem hj hσ)

omit [FiniteDimensional ℝ V] in
/-- **Lemma 16.B of the exposition, along a filter**: if `γⱼ → γ` in `Ω`, then for every `η > 0`
there is `δ > 0` such that eventually `E_a^b(γⱼ) < η` whenever `b − a < δ`. -/
theorem eventually_energy_lt {γs : ι → PathSp N p q} {γ : PathSp N p q}
    (h : Tendsto γs l (𝓝 γ)) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ᶠ j in l, ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → b - a < δ →
      energy (γs j) a b < η := by
  obtain ⟨M, hM0, hM⟩ := γ.mem.1.exists_bound_deriv
  have hev : ∀ᶠ j in l, l2Dist (γs j) γ < √η / 2 := by
    have := (tendsto_iff_edist_tendsto_0.1 h).eventually
      (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < √η / 2 by positivity)))
    filter_upwards [this] with j hj
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1
      (lt_of_le_of_lt (ofReal_l2Dist_le_edist _ _) hj)
  refine ⟨η / (4 * (M ^ 2 + 1)), by positivity, ?_⟩
  filter_upwards [hev] with j hj a b ha hab hb hδ
  have hsmall : M ^ 2 * (b - a) < η / 4 := by
    have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
    calc M ^ 2 * (b - a) ≤ M ^ 2 * (η / (4 * (M ^ 2 + 1))) := by gcongr
      _ < η / 4 := by
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  have hE0 := energy_nonneg_of_le (γ := (γs j : ℝ → V)) hab
  have h1 := abs_sqrt_energy_sub_le (γs j).mem γ.mem ha hab hb
  have hEγ := energy_le_of_bound γ.mem hM ha hab hb
  have h3 : √(energy γ a b) < √η / 2 := by
    rw [Real.sqrt_lt' (by positivity), div_pow, Real.sq_sqrt hη.le]
    linarith
  have h4 : √(energy (γs j) a b) < √η := by linarith [(abs_le.1 h1).2]
  calc energy (γs j) a b = √(energy (γs j) a b) ^ 2 := (Real.sq_sqrt hE0).symm
    _ < √η ^ 2 := by gcongr
    _ = η := Real.sq_sqrt hη.le

end Filter

/-! ### The `L²` distance of the speeds on subintervals -/

omit [FiniteDimensional ℝ V] in
/-- The speeds agree inside an interval on which the paths agree. -/
theorem speed_congr {γ γ' : ℝ → V} {a b : ℝ} (h : EqOn γ γ' (Icc a b)) {τ : ℝ}
    (hτ : τ ∈ Ioo a b) : speed γ τ = speed γ' τ := by
  have hev : γ =ᶠ[𝓝 τ] γ' := by
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with x hx
    exact h (Ioo_subset_Icc_self hx)
  simp only [speed, hev.deriv_eq]

omit [FiniteDimensional ℝ V] in
/-- The `L²` distance of the speeds over a subinterval is at most the full one. -/
theorem integral_speed_sub_sq_le {γ γ' : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hγ' : γ' ∈ pathSpace N p q) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∫ τ in a..b, (speed γ τ - speed γ' τ) ^ 2 ≤ l2Dist γ γ' ^ 2 := by
  rw [l2Dist, Real.sq_sqrt (intervalIntegral.integral_nonneg zero_le_one fun _ _ =>
    sq_nonneg _)]
  exact intervalIntegral.integral_mono_interval ha hab hb
    (Eventually.of_forall fun _ => sq_nonneg _)
    (intervalIntegrable_speed hγ hγ' (Φ := fun z => (z.1 - z.2) ^ 2) (by fun_prop) le_rfl
      zero_le_one le_rfl)

omit [FiniteDimensional ℝ V] in
/-- `∫ₐᵇ (s − s')² ≤ 2 E_a^b(γ) + 2 E_a^b(γ')`. -/
theorem integral_speed_sub_sq_le_energy {γ γ' : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hγ' : γ' ∈ pathSpace N p q) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∫ τ in a..b, (speed γ τ - speed γ' τ) ^ 2 ≤ 2 * energy γ a b + 2 * energy γ' a b := by
  have i1 := intervalIntegrable_speed hγ hγ' (Φ := fun z => (z.1 - z.2) ^ 2) (by fun_prop) ha
    hab hb
  have i2 := intervalIntegrable_speed hγ hγ' (Φ := fun z => 2 * z.1 ^ 2) (by fun_prop) ha hab hb
  have i3 := intervalIntegrable_speed hγ hγ' (Φ := fun z => 2 * z.2 ^ 2) (by fun_prop) ha hab hb
  calc ∫ τ in a..b, (speed γ τ - speed γ' τ) ^ 2
      ≤ ∫ τ in a..b, (2 * speed γ τ ^ 2 + 2 * speed γ' τ ^ 2) :=
        intervalIntegral.integral_mono_on hab i1 (i2.add i3) fun τ _ => by
          nlinarith [sq_nonneg (speed γ τ + speed γ' τ)]
    _ = 2 * energy γ a b + 2 * energy γ' a b := by
        rw [intervalIntegral.integral_add i2 i3, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
        rfl

end PathSp

/-! ### The speeds of broken geodesics depend continuously on the break points -/

namespace BrokenSetup

variable {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

open PathSp in
/-- **The `L²` distance of the speeds of two broken geodesics**:
`∫₀¹ (s' − s)² = Σᵢ (ρ'ᵢ − ρᵢ)²/(t_{i+1} − tᵢ)`, `ρᵢ = ρ(xᵢ, xᵢ₊₁)`. -/
theorem integral_speed_path_sub_sq {y y' : Fin m → V} (hy : y ∈ B.nodes) (hy' : y' ∈ B.nodes) :
    ∫ τ in (0 : ℝ)..1, (speed (B.path y') τ - speed (B.path y) τ) ^ 2 =
      ∑ k, ((gaps N p q y' k).toReal - (gaps N p q y k).toReal) ^ 2 / B.len k := by
  have hps := B.path_mem_pathSpace hy
  have hps' := B.path_mem_pathSpace hy'
  have hmem : ∀ k, B.t k ∈ uIcc (0 : ℝ) 1 := fun k => by
    rw [uIcc_of_le zero_le_one]; exact ⟨B.t_nonneg k, B.t_le_one k⟩
  have hint : ∀ k l, IntervalIntegrable
      (fun τ => (speed (B.path y') τ - speed (B.path y) τ) ^ 2) volume (B.t k) (B.t l) :=
    fun k l => (intervalIntegrable_speed hps' hps (Φ := fun z => (z.1 - z.2) ^ 2) (by fun_prop)
      le_rfl zero_le_one le_rfl).mono_set (uIcc_subset_uIcc (hmem k) (hmem l))
  have hsum := sum_integral_fin B.t hint
  rw [B.t_zero, B.t_last] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hl := (B.len_pos k).ne'
  have hc : EqOn (fun τ => (speed (B.path y') τ - speed (B.path y) τ) ^ 2)
      (fun _ => ((gaps N p q y' k).toReal - (gaps N p q y k).toReal) ^ 2 / B.len k ^ 2)
      (Ioo (B.t k.castSucc) (B.t k.succ)) := by
    intro τ hτ
    simp only [speed, B.norm_deriv_path hy' k hτ, B.norm_deriv_path hy k hτ, gaps,
      (B.joinVec_vert hy k).2.2.2, (B.joinVec_vert hy' k).2.2.2,
      ENNReal.toReal_ofReal (norm_nonneg _)]
    rw [div_sub_div_same, div_pow]
  rw [intervalIntegral.integral_congr_Ioo_of_le (B.t_le_iff.2 Fin.castSucc_lt_succ.le) hc,
    intervalIntegral.integral_const, smul_eq_mul]
  change B.len k * _ = _
  field_simp

open PathSp in
/-- **The speeds of broken geodesics depend continuously on the break points** (in `L²`). -/
theorem tendsto_integral_speed_path {ι : Type*} {l : Filter ι} {ys : ι → Fin m → V}
    {y : Fin m → V} (hy : y ∈ B.nodes) (hys : ∀ᶠ j in l, ys j ∈ B.nodes)
    (h : Tendsto ys l (𝓝 y)) :
    Tendsto (fun j => ∫ τ in (0 : ℝ)..1, (speed (B.path (ys j)) τ - speed (B.path y) τ) ^ 2)
      l (𝓝 0) := by
  have hg : Tendsto (fun j => gaps N p q (ys j)) l (𝓝 (gaps N p q y)) :=
    (B.continuousOn_gaps y fun k _ => hy.1 k).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨h, hys.mono fun j hj => fun k _ => hj.1 k⟩)
  have hk : ∀ k, Tendsto (fun j => ((gaps N p q (ys j) k).toReal - (gaps N p q y k).toReal) ^ 2 /
      B.len k) l (𝓝 0) := by
    intro k
    have h1 : Tendsto (fun j => (gaps N p q (ys j) k).toReal) l (𝓝 (gaps N p q y k).toReal) :=
      (ENNReal.tendsto_toReal (hy.2.1 k)).comp (((continuous_apply k).tendsto _).comp hg)
    simpa using ((h1.sub_const ((gaps N p q y k).toReal)).pow 2).div_const (B.len k)
  have hsum := tendsto_finsetSum Finset.univ fun k _ => hk k
  simp only [Finset.sum_const_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hys] with j hj
  exact (B.integral_speed_path_sub_sq hy hj).symm

end BrokenSetup

end Morse
