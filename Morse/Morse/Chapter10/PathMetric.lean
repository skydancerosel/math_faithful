import Morse.Chapter10.Finite

/-!
Milnor, *Morse Theory*, §16, p. 88: the topology of the path space, for a submanifold `N ⊆ ℝᴷ`
with the induced metric.

# Milnor's metric on the path space

## Milnor's text, paraphrased

(p. 88) The set `Ω = Ω(M; p, q)` of piecewise smooth paths from `p` to `q` is topologized by the
distance `d(ω, ω') = max_t ρ(ω(t), ω'(t)) + [∫₀¹ (ds/dt − ds'/dt)² dt]^{1/2}`, `s(t)`, `s'(t)` the
arc lengths; the last term is added so that the energy `E_a^b(ω) = ∫ₐᵇ (ds/dt)² dt` is a
continuous function on `Ω`.  `Ω^c = E⁻¹[0, c]` is closed and `Int Ω^c = E⁻¹[0, c)` is open.

## In the embedded setting

* `Morse.PathSp N p q`: `Ω(N; p, q)` as a type (paths `ℝ → V` in `Morse.pathSpace N p q`);
  `Morse.PathSp.speed γ t = ‖γ'(t)‖ = ds/dt`.
* `Morse.PathSp.instPseudoEMetricSpace`: **Milnor's metric** `d`, with
  `edist γ γ' = sup_{t ∈ [0, 1]} ρ(γ(t), γ'(t)) + (∫₀¹ (‖γ'‖ − ‖γ''‖)²)^{1/2}`
  (`Morse.PathSp.supDist`, `Morse.PathSp.l2Dist`).  It is a pseudometric (two paths that agree on
  `[0, 1]` are at distance `0`; the values off `[0, 1]` play no role).
* **Lemma 16.A of the exposition**: `Morse.PathSp.abs_sqrt_energy_sub_le`:
  `|√E_a^b(γ) − √E_a^b(γ')| ≤ (∫₀¹ (‖γ'‖ − ‖γ''‖)²)^{1/2}`; hence `√E` is `1`-Lipschitz for `d`
  (`Morse.PathSp.lipschitzWith_sqrt_energy`) and **`E` is continuous**
  (`Morse.PathSp.continuous_energy`); `Ω^c` is closed and `Int Ω^c` open
  (`Morse.PathSp.isClosed_sublevel`, `Morse.PathSp.isOpen_sublevel_lt`).
* **Lemma 16.B of the exposition** (no energy in short intervals),
  `Morse.PathSp.exists_energy_lt_of_tendsto`: along a convergent sequence `γₙ → γ`, the energy of
  `γₙ` on intervals of length `< δ` is uniformly small.

## What Milnor leaves implicit

* **"This metric induces the required topology"**: the continuity of `E` is the triangle
  inequality in `L²` (Minkowski), `√E_a^b = ‖ds/dt‖_{L²[a, b]}`; with `max ρ` alone, a normal wiggle
  of amplitude `1/n` and frequency `n²` added to a path gives paths converging uniformly whose
  energies tend to `∞`.
* **That `d` is a metric** needs Minkowski's inequality for the `L²` term (proved here from the
  Cauchy–Schwarz inequality for integrals) and the triangle inequality for `ρ`; and it is only a
  pseudometric on functions `ℝ → V` (a metric on paths `[0, 1] → M`).
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Interval NNReal

noncomputable section

namespace Morse

/-! ### Cauchy–Schwarz and Minkowski for interval integrals -/

section Integrals

variable {f g : ℝ → ℝ} {a b : ℝ}

/-- **The Cauchy–Schwarz inequality** for integrals over `[a, b]`. -/
theorem integral_mul_sq_le (hab : a ≤ b) (hf : IntervalIntegrable (fun t => f t ^ 2) volume a b)
    (hg : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : IntervalIntegrable (fun t => f t * g t) volume a b) :
    (∫ t in a..b, f t * g t) ^ 2 ≤ (∫ t in a..b, f t ^ 2) * ∫ t in a..b, g t ^ 2 := by
  have hq : ∀ x : ℝ, 0 ≤ (∫ t in a..b, g t ^ 2) * (x * x) + (-2 * ∫ t in a..b, f t * g t) * x +
      ∫ t in a..b, f t ^ 2 := by
    intro x
    have h0 : 0 ≤ ∫ t in a..b, (f t - x * g t) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg _
    have e : (fun t => (f t - x * g t) ^ 2) =
        fun t => f t ^ 2 + (-2 * x) * (f t * g t) + (x * x) * g t ^ 2 := by
      funext t; ring
    rw [e, intervalIntegral.integral_add (hf.add (hfg.const_mul _)) (hg.const_mul _),
      intervalIntegral.integral_add hf (hfg.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at h0
    linarith
  have := discrim_le_zero hq
  rw [discrim] at this
  nlinarith

/-- **Minkowski's inequality** for integrals over `[a, b]`:
`(∫ (f + g)²)^{1/2} ≤ (∫ f²)^{1/2} + (∫ g²)^{1/2}`. -/
theorem sqrt_integral_add_sq_le (hab : a ≤ b)
    (hf : IntervalIntegrable (fun t => f t ^ 2) volume a b)
    (hg : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : IntervalIntegrable (fun t => f t * g t) volume a b) :
    √(∫ t in a..b, (f t + g t) ^ 2) ≤ √(∫ t in a..b, f t ^ 2) + √(∫ t in a..b, g t ^ 2) := by
  have hF : 0 ≤ ∫ t in a..b, f t ^ 2 := intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg _
  have hG : 0 ≤ ∫ t in a..b, g t ^ 2 := intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg _
  have hCS := integral_mul_sq_le hab hf hg hfg
  have hCS' : ∫ t in a..b, f t * g t ≤ √(∫ t in a..b, f t ^ 2) * √(∫ t in a..b, g t ^ 2) := by
    rw [← Real.sqrt_mul hF]
    exact Real.le_sqrt_of_sq_le hCS
  have e : (fun t => (f t + g t) ^ 2) = fun t => f t ^ 2 + 2 * (f t * g t) + g t ^ 2 := by
    funext t; ring
  rw [e, intervalIntegral.integral_add (hf.add (hfg.const_mul _)) hg,
    intervalIntegral.integral_add hf (hfg.const_mul _), intervalIntegral.integral_const_mul]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt hF
  have h2 := Real.sq_sqrt hG
  nlinarith [Real.sqrt_nonneg (∫ t in a..b, f t ^ 2), Real.sqrt_nonneg (∫ t in a..b, g t ^ 2)]

end Integrals

/-! ### Velocities of piecewise smooth paths -/

section Velocity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : ℝ → E} {a b : ℝ}

/-- The velocity of a piecewise smooth path is continuous on the open pieces, extending
continuously to the closed pieces. -/
theorem IsPiecewiseSmooth.exists_deriv_piece (hγ : IsPiecewiseSmooth γ a b) :
    ∃ B : Finset ℝ, ∀ s t, a ≤ s → s < t → t ≤ b → (∀ x ∈ B, x ∉ Ioo s t) →
      ∃ K : ℝ → E, ContinuousOn K (Icc s t) ∧ EqOn (deriv γ) K (Ioo s t) := by
  obtain ⟨-, -, B, hB⟩ := hγ
  refine ⟨B, fun s t hs hst ht hBst => ?_⟩
  obtain ⟨h1, h2⟩ := IsPiecewiseSmooth.derivWithin_piece hst (hB s t hs hst ht hBst)
  exact ⟨_, h1.continuousOn, h2⟩

/-- A continuous function of the velocities of two piecewise smooth paths is integrable. -/
theorem intervalIntegrable_comp_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {γ' : ℝ → F} (hγ : IsPiecewiseSmooth γ a b) (hγ' : IsPiecewiseSmooth γ' a b)
    {Φ : E × F → ℝ} (hΦ : Continuous Φ) {a' b' : ℝ} (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b) :
    IntervalIntegrable (fun t => Φ (deriv γ t, deriv γ' t)) volume a' b' := by
  classical
  obtain ⟨B₁, h₁⟩ := hγ.exists_deriv_piece
  obtain ⟨B₂, h₂⟩ := hγ'.exists_deriv_piece
  refine intervalIntegrable_of_piecewise (B := B₁ ∪ B₂) (lo := a) (hi := b)
    (fun s t hs hst ht hB => ?_) ha hab hb
  obtain ⟨K₁, hK₁, hE₁⟩ := h₁ s t hs hst ht fun x hx => hB x (Finset.mem_union_left _ hx)
  obtain ⟨K₂, hK₂, hE₂⟩ := h₂ s t hs hst ht fun x hx => hB x (Finset.mem_union_right _ hx)
  exact ⟨fun τ => Φ (K₁ τ, K₂ τ), hΦ.comp_continuousOn (hK₁.prodMk hK₂), fun τ hτ => by
    simp only [hE₁ hτ, hE₂ hτ]⟩

/-- A continuous function of the velocities of three piecewise smooth paths is integrable. -/
theorem intervalIntegrable_comp_deriv₃ {γ' γ'' : ℝ → E} (hγ : IsPiecewiseSmooth γ a b)
    (hγ' : IsPiecewiseSmooth γ' a b) (hγ'' : IsPiecewiseSmooth γ'' a b) {Φ : E × E × E → ℝ}
    (hΦ : Continuous Φ) {a' b' : ℝ} (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b) :
    IntervalIntegrable (fun t => Φ (deriv γ t, deriv γ' t, deriv γ'' t)) volume a' b' := by
  classical
  obtain ⟨B₁, h₁⟩ := hγ.exists_deriv_piece
  obtain ⟨B₂, h₂⟩ := hγ'.exists_deriv_piece
  obtain ⟨B₃, h₃⟩ := hγ''.exists_deriv_piece
  refine intervalIntegrable_of_piecewise (B := B₁ ∪ B₂ ∪ B₃) (lo := a) (hi := b)
    (fun s t hs hst ht hB => ?_) ha hab hb
  obtain ⟨K₁, hK₁, hE₁⟩ := h₁ s t hs hst ht fun x hx =>
    hB x (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  obtain ⟨K₂, hK₂, hE₂⟩ := h₂ s t hs hst ht fun x hx =>
    hB x (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
  obtain ⟨K₃, hK₃, hE₃⟩ := h₃ s t hs hst ht fun x hx => hB x (Finset.mem_union_right _ hx)
  exact ⟨fun τ => Φ (K₁ τ, K₂ τ, K₃ τ), hΦ.comp_continuousOn (hK₁.prodMk (hK₂.prodMk hK₃)),
    fun τ hτ => by simp only [hE₁ hτ, hE₂ hτ, hE₃ hτ]⟩

/-- **The speed of a piecewise smooth path is bounded.** -/
theorem IsPiecewiseSmooth.exists_bound_deriv (hγ : IsPiecewiseSmooth γ a b) :
    ∃ M, 0 ≤ M ∧ ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M := by
  obtain ⟨hab, -, B, hB⟩ := hγ
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact ⟨‖deriv γ a‖, norm_nonneg _, fun t ht => by rw [le_antisymm ht.2 ht.1]⟩
  refine piecewise_induction (B := B) (lo := a) (hi := b)
    (P := fun s t => ∃ M, 0 ≤ M ∧ ∀ τ ∈ Icc s t, ‖deriv γ τ‖ ≤ M) (fun s t hs hst ht hBst => ?_)
    (fun s x t _ _ _ _ _ ⟨M₁, hM₁, h₁⟩ ⟨M₂, hM₂, h₂⟩ => ⟨max M₁ M₂, le_max_of_le_left hM₁,
      fun τ hτ => by
        rcases le_total τ x with h | h
        · exact (h₁ τ ⟨hτ.1, h⟩).trans (le_max_left _ _)
        · exact (h₂ τ ⟨h, hτ.2⟩).trans (le_max_right _ _)⟩) a b le_rfl hlt le_rfl
  have hc := hB s t hs hst ht hBst
  obtain ⟨h1, h2⟩ := IsPiecewiseSmooth.derivWithin_piece hst hc
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn h1.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun τ hτ => ?_⟩
  by_cases hd : DifferentiableAt ℝ γ τ
  · rw [← hd.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hst τ hτ)]
    exact (hM τ hτ).trans (le_max_left _ _)
  · rw [deriv_zero_of_not_differentiableAt hd, norm_zero]
    exact le_max_right _ _

end Velocity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {N : Set V}

/-! ### The path space with Milnor's metric -/

variable (N) in
/-- **Milnor's path space** `Ω(N; p, q)` (p. 67), as a type carrying Milnor's metric `d`
(p. 88).  A path is a function `ℝ → V` in `Morse.pathSpace N p q`; its values off `[0, 1]` play
no role. -/
def PathSp (p q : V) : Type _ := {γ : ℝ → V // γ ∈ pathSpace N p q}

namespace PathSp

variable {p q : V}

instance : CoeFun (PathSp N p q) fun _ => ℝ → V := ⟨fun γ => γ.1⟩

theorem mem (γ : PathSp N p q) : (γ : ℝ → V) ∈ pathSpace N p q := γ.2

/-- The speed `ds/dt = ‖γ'(t)‖`. -/
def speed (γ : ℝ → V) (t : ℝ) : ℝ := ‖deriv γ t‖

variable (N) in
/-- The uniform part of Milnor's metric: `max_{t ∈ [0, 1]} ρ(γ(t), γ'(t))`. -/
def supDist (γ γ' : ℝ → V) : ℝ≥0∞ := ⨆ t ∈ Icc (0 : ℝ) 1, riemDist (N := N) (γ t) (γ' t)

/-- The `L²` part of Milnor's metric: `(∫₀¹ (‖γ'‖ − ‖γ''‖)²)^{1/2}`. -/
def l2Dist (γ γ' : ℝ → V) : ℝ := √(∫ t in (0 : ℝ)..1, (speed γ t - speed γ' t) ^ 2)

theorem l2Dist_nonneg (γ γ' : ℝ → V) : 0 ≤ l2Dist γ γ' := Real.sqrt_nonneg _

theorem l2Dist_comm (γ γ' : ℝ → V) : l2Dist γ γ' = l2Dist γ' γ := by
  simp only [l2Dist, ← neg_sub (speed γ' _), neg_sq]

theorem l2Dist_self (γ : ℝ → V) : l2Dist γ γ = 0 := by simp [l2Dist]

theorem intervalIntegrable_speed {γ γ' : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hγ' : γ' ∈ pathSpace N p q) {Φ : ℝ × ℝ → ℝ} (hΦ : Continuous Φ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable (fun t => Φ (speed γ t, speed γ' t)) volume a b :=
  intervalIntegrable_comp_deriv hγ.1 hγ'.1 (Φ := fun z : V × V => Φ (‖z.1‖, ‖z.2‖))
    (hΦ.comp ((continuous_norm.comp continuous_fst).prodMk (continuous_norm.comp
      continuous_snd))) ha hab hb

/-- The triangle inequality for the `L²` part (Minkowski). -/
theorem l2Dist_triangle {γ γ' γ'' : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hγ' : γ' ∈ pathSpace N p q) (hγ'' : γ'' ∈ pathSpace N p q) :
    l2Dist γ γ'' ≤ l2Dist γ γ' + l2Dist γ' γ'' := by
  have e : (fun t => (speed γ t - speed γ'' t) ^ 2) =
      fun t => ((speed γ t - speed γ' t) + (speed γ' t - speed γ'' t)) ^ 2 := by
    funext t; ring
  rw [l2Dist, e]
  refine sqrt_integral_add_sq_le zero_le_one ?_ ?_ ?_
  · exact intervalIntegrable_speed hγ hγ' (Φ := fun z => (z.1 - z.2) ^ 2) (by fun_prop) le_rfl
      zero_le_one le_rfl
  · exact intervalIntegrable_speed hγ' hγ'' (Φ := fun z => (z.1 - z.2) ^ 2) (by fun_prop) le_rfl
      zero_le_one le_rfl
  · exact intervalIntegrable_comp_deriv₃ hγ.1 hγ'.1 hγ''.1
      (Φ := fun z : V × V × V => (‖z.1‖ - ‖z.2.1‖) * (‖z.2.1‖ - ‖z.2.2‖)) (by fun_prop)
      le_rfl zero_le_one le_rfl

theorem supDist_self {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q) : supDist N γ γ = 0 := by
  rw [supDist]
  refine le_antisymm (iSup₂_le fun t ht => ?_) bot_le
  rw [riemDist_self (hγ.2.1 t ht)]

theorem supDist_comm (γ γ' : ℝ → V) : supDist N γ γ' = supDist N γ' γ := by
  simp only [supDist, riemDist_comm (γ _)]

theorem supDist_triangle (γ γ' γ'' : ℝ → V) :
    supDist N γ γ'' ≤ supDist N γ γ' + supDist N γ' γ'' := by
  refine iSup₂_le fun t ht => (riemDist_triangle (N := N) _ (γ' t) _).trans (add_le_add ?_ ?_)
  · exact le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) 1) => riemDist (N := N) (γ t) (γ' t)) t ht
  · exact le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) 1) => riemDist (N := N) (γ' t) (γ'' t)) t ht

theorem riemDist_le_supDist {γ γ' : ℝ → V} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    riemDist (N := N) (γ t) (γ' t) ≤ supDist N γ γ' :=
  le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) 1) => riemDist (N := N) (γ t) (γ' t)) t ht

/-- **Milnor's metric** `d(γ, γ') = max_t ρ(γ(t), γ'(t)) + (∫₀¹ (ds/dt − ds'/dt)²)^{1/2}`
(p. 88), as an extended pseudometric on `Ω(N; p, q)`. -/
instance instPseudoEMetricSpace : PseudoEMetricSpace (PathSp N p q) where
  edist γ γ' := supDist N γ γ' + ENNReal.ofReal (l2Dist γ γ')
  edist_self γ := by simp [supDist_self γ.mem, l2Dist_self]
  edist_comm γ γ' := by simp only [supDist_comm (N := N) (γ : ℝ → V), l2Dist_comm (γ : ℝ → V)]
  edist_triangle γ γ' γ'' := by
    calc supDist N γ γ'' + ENNReal.ofReal (l2Dist γ γ'')
        ≤ (supDist N γ γ' + supDist N γ' γ'') +
          (ENNReal.ofReal (l2Dist γ γ') + ENNReal.ofReal (l2Dist γ' γ'')) := by
          refine add_le_add (supDist_triangle _ _ _) ?_
          rw [← ENNReal.ofReal_add (l2Dist_nonneg _ _) (l2Dist_nonneg _ _)]
          exact ENNReal.ofReal_le_ofReal (l2Dist_triangle γ.mem γ'.mem γ''.mem)
      _ = _ := by ring

theorem edist_def (γ γ' : PathSp N p q) :
    edist γ γ' = supDist N γ γ' + ENNReal.ofReal (l2Dist γ γ') := rfl

theorem ofReal_l2Dist_le_edist (γ γ' : PathSp N p q) :
    ENNReal.ofReal (l2Dist γ γ') ≤ edist γ γ' := le_add_self

theorem supDist_le_edist (γ γ' : PathSp N p q) : supDist N γ γ' ≤ edist γ γ' := le_self_add

/-! ### Lemma 16.A: the energy is continuous -/

theorem energy_eq_integral_speed (γ : ℝ → V) (a b : ℝ) :
    energy γ a b = ∫ t in a..b, speed γ t ^ 2 := rfl

/-- **Lemma 16.A of the exposition**: `|√E_a^b(γ) − √E_a^b(γ')| ≤ (∫₀¹ (ds/dt − ds'/dt)²)^{1/2}`
for `0 ≤ a ≤ b ≤ 1` (Minkowski's inequality on `[a, b]`). -/
theorem abs_sqrt_energy_sub_le {γ γ' : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hγ' : γ' ∈ pathSpace N p q) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |√(energy γ a b) - √(energy γ' a b)| ≤ l2Dist γ γ' := by
  have key : ∀ {γ γ' : ℝ → V}, γ ∈ pathSpace N p q → γ' ∈ pathSpace N p q →
      √(energy γ a b) ≤ √(energy γ' a b) + l2Dist γ γ' := by
    intro γ γ' hγ hγ'
    have e : (fun t => speed γ t ^ 2) =
        fun t => ((speed γ t - speed γ' t) + speed γ' t) ^ 2 := by funext t; ring
    rw [energy_eq_integral_speed, e]
    refine (sqrt_integral_add_sq_le hab ?_ ?_ ?_).trans ?_
    · exact intervalIntegrable_speed hγ hγ' (Φ := fun z => (z.1 - z.2) ^ 2) (by fun_prop) ha
        hab hb
    · exact intervalIntegrable_speed hγ' hγ' (Φ := fun z => z.1 ^ 2) (by fun_prop) ha hab hb
    · exact intervalIntegrable_speed hγ hγ' (Φ := fun z => (z.1 - z.2) * z.2) (by fun_prop) ha
        hab hb
    rw [add_comm, ← energy_eq_integral_speed]
    gcongr
    rw [l2Dist]
    exact Real.sqrt_le_sqrt (intervalIntegral.integral_mono_interval ha hab hb
      (Eventually.of_forall fun _ => sq_nonneg _)
      (intervalIntegrable_speed hγ hγ' (Φ := fun z => (z.1 - z.2) ^ 2) (by fun_prop) le_rfl
        zero_le_one le_rfl))
  rw [abs_le]
  constructor
  · have := key hγ' hγ
    rw [l2Dist_comm] at this
    linarith
  · linarith [key hγ hγ']

/-- **`√E_a^b` is `1`-Lipschitz for Milnor's metric.** -/
theorem lipschitzWith_sqrt_energy {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    LipschitzWith 1 fun γ : PathSp N p q => √(energy γ a b) := by
  refine LipschitzWith.of_edist_le fun γ γ' => ?_
  rw [edist_dist, Real.dist_eq]
  exact (ENNReal.ofReal_le_ofReal (abs_sqrt_energy_sub_le γ.mem γ'.mem ha hab hb)).trans
    (ofReal_l2Dist_le_edist γ γ')

theorem energy_nonneg_of_le {γ : ℝ → V} {a b : ℝ} (hab : a ≤ b) : 0 ≤ energy γ a b :=
  intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _

/-- **The energy is continuous on `Ω`** (Milnor p. 88, the purpose of the `L²` term of `d`). -/
theorem continuous_energy {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Continuous fun γ : PathSp N p q => energy γ a b := by
  have h := (lipschitzWith_sqrt_energy (N := N) (p := p) (q := q) ha hab hb).continuous.pow 2
  refine h.congr fun γ => ?_
  exact Real.sq_sqrt (energy_nonneg_of_le hab)

/-- `Ω^c` is closed. -/
theorem isClosed_sublevel (c : ℝ) : IsClosed {γ : PathSp N p q | energy γ 0 1 ≤ c} :=
  isClosed_le (continuous_energy le_rfl zero_le_one le_rfl) continuous_const

/-- `Int Ω^c = E⁻¹[0, c)` is open. -/
theorem isOpen_sublevel_lt (c : ℝ) : IsOpen {γ : PathSp N p q | energy γ 0 1 < c} :=
  isOpen_lt (continuous_energy le_rfl zero_le_one le_rfl) continuous_const

/-! ### Lemma 16.B: no energy in short intervals -/

theorem energy_le_of_bound {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q) {M : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ t‖ ≤ M) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) : energy γ a b ≤ M ^ 2 * (b - a) := by
  have h := intervalIntegral.integral_mono_on hab
    ((hγ.1.mono ha hab hb).intervalIntegrable_norm_deriv_sq)
    (intervalIntegrable_const (c := M ^ 2)) fun t ht =>
      pow_le_pow_left₀ (norm_nonneg _) (hM t ⟨ha.trans ht.1, ht.2.trans hb⟩) 2
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  rw [energy]
  linarith

/-- **Lemma 16.B of the exposition** (no energy in short intervals): if `γₙ → γ` in `Ω`, then for
every `η > 0` there is `δ > 0` with `E_a^b(γₙ) < η` for all `n` whenever `b − a < δ`. -/
theorem exists_energy_lt_of_tendsto {γs : ℕ → PathSp N p q} {γ : PathSp N p q}
    (h : Tendsto γs atTop (𝓝 γ)) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ n a b, 0 ≤ a → a ≤ b → b ≤ 1 → b - a < δ → energy (γs n) a b < η := by
  -- from some `n₀` on, the `L²` distance to `γ` is `< √η/2`
  obtain ⟨n₀, hn₀⟩ := (EMetric.tendsto_atTop.1 h) (ENNReal.ofReal (√η / 2))
    (ENNReal.ofReal_pos.2 (by positivity))
  have hl2 : ∀ n ≥ n₀, l2Dist (γs n) γ < √η / 2 := fun n hn =>
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1
      (lt_of_le_of_lt (ofReal_l2Dist_le_edist _ _) (hn₀ n hn))
  -- bounds for the speeds of `γ` and of `γ₀, …, γ_{n₀ − 1}`
  choose M hM0 hM using fun n => (γs n).mem.1.exists_bound_deriv
  obtain ⟨M₀, hM₀0, hM₀⟩ := γ.mem.1.exists_bound_deriv
  set K := M₀ + ∑ n ∈ Finset.range n₀, M n with hK
  have hsum0 : 0 ≤ ∑ n ∈ Finset.range n₀, M n := Finset.sum_nonneg fun n _ => hM0 n
  have hK0 : 0 ≤ K := add_nonneg hM₀0 hsum0
  have hKγ : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ t‖ ≤ K := fun t ht =>
    (hM₀ t ht).trans (le_add_of_nonneg_right hsum0)
  have hKn : ∀ n < n₀, ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (γs n) t‖ ≤ K := fun n hn t ht =>
    (hM n t ht).trans (by
      have := Finset.single_le_sum (fun i _ => hM0 i) (Finset.mem_range.2 hn)
      linarith)
  refine ⟨η / (4 * (K ^ 2 + 1)), by positivity, fun n a b ha hab hb hδ => ?_⟩
  have hsmall : K ^ 2 * (b - a) < η / 4 := by
    have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
    calc K ^ 2 * (b - a) ≤ K ^ 2 * (η / (4 * (K ^ 2 + 1))) := by gcongr
      _ < η / 4 := by
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  have hE0 := energy_nonneg_of_le (γ := (γs n : ℝ → V)) hab
  by_cases hn : n < n₀
  · have := energy_le_of_bound (γs n).mem (hKn n hn) ha hab hb
    linarith
  · have h1 := abs_sqrt_energy_sub_le (γs n).mem γ.mem ha hab hb
    have h2 := hl2 n (not_lt.1 hn)
    have hEγ := energy_le_of_bound γ.mem hKγ ha hab hb
    have h3 : √(energy γ a b) < √η / 2 := by
      rw [Real.sqrt_lt' (by positivity), div_pow, Real.sq_sqrt hη.le]
      linarith
    have h4 : √(energy (γs n) a b) < √η := by linarith [(abs_le.1 h1).2]
    calc energy (γs n) a b = √(energy (γs n) a b) ^ 2 := (Real.sq_sqrt hE0).symm
      _ < √η ^ 2 := by gcongr
      _ = η := Real.sq_sqrt hη.le

end PathSp

end Morse
