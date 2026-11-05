import Morse.Chapter10.FullPathSpace

/-!
Milnor, *Morse Theory*, §17, pp. 93–94 (proof of Theorem 17.1), with the counterexample of
Exposition/Chapter10.md, §5.

# Milnor's map `h : Ω* → Ω` is not continuous

## Milnor's text, paraphrased

(p. 93) `Ω*` is the space of continuous paths from `p` to `q` (compact-open topology, that of the
uniform metric `d*`), `Ω` the space of piecewise smooth paths with the metric `d` of p. 88 (`d*`
plus the `L²` distance of the speeds, `Morse/Chapter10/PathMetric.lean`).  To prove that
`i : Ω → Ω*` is a homotopy equivalence, Milnor picks a continuous `f : M → [0, ∞)` with compact
sets `f⁻¹[0, r]`, lets `ε₁(r) ≤ ∞` be the largest number such that two points of `f⁻¹[0, r]`
closer than `ε₁(r)` are joined by a unique minimal geodesic depending differentiably on its ends,
and chooses a continuous `ε₂` with `0 < ε₂ < ε₁`.  (p. 94) He sets `ε(ω) = ε₂(max_t f(ω(t)))` and
`F(ω, α) = (α − 1) ε(ω) + max_{|t − t'| ≤ α} ρ(ω(t), ω(t'))`, notes that `F(ω, ·)` is strictly
increasing with `F(ω, 0) < 0 ≤ F(ω, 1)`, and calls `2A(ω)` its unique zero in `(0, 1]`.  Then
`h(ω)` is the path which agrees with `ω` at `t = 0, A, 2A, …, kA` (`A = A(ω)`, `k` the largest
integer `≤ 1/A`) and at `t = 1`, and is a geodesic on each intermediate interval.  He says that
`h` is clearly continuous, and that the arguments of §16 give `h ∘ i ≃ id` and `i ∘ h ≃ id`.

## Milnor's choices, fixed here

* `M = ℝ`, `p = q = 0`.  `Ω* = Morse.PathC univ 0 0` (continuous `ω : [0, 1] → ℝ` with
  `ω(0) = ω(1) = 0`, uniform metric) and `Ω = Morse.PathSp univ 0 0` (Milnor's metric `d`).
* `ρ(x, y) = |x − y|`: this is Milnor's distance of `ℝ` (`Morse.MilnorH.riemDist_real`).  The
  geodesics of `ℝ` are the affine maps, so the minimal geodesic between two points is the
  segment, and it is unique.
* `f(x) = |x|` (`Morse.MilnorH.exhaust`).  Any two points of `ℝ` are joined by a unique minimal
  geodesic, depending affinely (so smoothly) on its ends; hence `ε₁ ≡ ∞`, and **`ε₂ ≡ 1` is an
  admissible choice** (`Morse.MilnorH.epsTwo`): it is continuous and `0 < 1 < ε₁(r)`.  Then
  `ε(ω) = 1` and `F(ω, α) = α − 1 + m_ω(α)`, `m_ω(α) = max_{|t − t'| ≤ α} |ω(t) − ω(t')|`
  (`Morse.MilnorH.modulus`, `Morse.MilnorH.milnorF`).
* `2A(ω)` (`Morse.MilnorH.twoA`) is defined as `inf {α ∈ [0, 1] : F(ω, α) ≥ 0}`.
  `Morse.MilnorH.twoA_spec` proves Milnor's claims for every `ω ∈ Ω*`: `2A(ω) ∈ (0, 1]` and
  `F(ω, 2A(ω)) = 0`, and `Morse.MilnorH.twoA_eq` shows it is the only zero in `[0, 1]`; so this
  is exactly Milnor's `2A(ω)`.  `k = ⌊1/A⌋` (`Morse.MilnorH.milnorK`).
* `h(ω)` (`Morse.MilnorH.hPath`) is the interpolation of `ω` at `0, A, …, kA, 1` by affine
  segments (`Morse.MilnorH.plin`), i.e. by the minimal geodesics of `ℝ`; when `kA = 1` the last
  interval is empty.  Milnor's two conditions: it agrees with `ω` at `jA`, `j ≤ k`, and at `1`
  (`Morse.MilnorH.hPath_node`, `Morse.MilnorH.hPath_one`), and its acceleration vanishes on each
  intermediate interval (`Morse.MilnorH.deriv_deriv_hPath`).  It lies in `Ω`
  (`Morse.MilnorH.hPath_mem`), which gives the map `Morse.MilnorH.hMap : Ω* → Ω`.
* Other constant choices `ε₂ ≡ c` give nothing new: `F_c(cω, α) = c F_1(ω, α)`, so
  `A_c(cω) = A_1(ω)` and `h_c(cω) = c h_1(ω)`, and the family `cω_λ` behaves in the same way
  (a remark, not formalized).

## The counterexample (Exposition/Chapter10.md, §5)

`ω_λ(t) = λ g(t)` with `g(t) = (1 − t)^{1/3} − (1 − t)` (`Morse.MilnorH.omegaFam`).  On `[0, 1]`,
`0 ≤ g ≤ c₀ = 2√3/9 = g(1 − √3/9)` (`Morse.MilnorH.g_le`, `Morse.MilnorH.g_one_sub_s₀`), so
`m_{ω_λ}(α) = λc₀` for `α ≥ √3/9` and `2A(ω_λ) = 1 − λc₀` while `λc₀ ≤ 1/2`.

* **`λ* = √3/2`** (`Morse.MilnorH.lamStar`): `λ*c₀ = 1/3`, so `A(ω_{λ*}) = 1/3`, `1/A = 3 = k` and
  `kA = 1` (`Morse.MilnorH.milnorA_lamStar`, `Morse.MilnorH.milnorK_lamStar`).
* `ω_λ → ω_{λ*}` uniformly: `d*(ω_λ, ω_μ) ≤ c₀|λ − μ|` (`Morse.MilnorH.dist_omegaFam_le`,
  `Morse.MilnorH.tendsto_omegaFam`).
* `E(h(ω_{λ*})) = 3λ*²(g(1/3)² + (g(2/3) − g(1/3))² + g(2/3)²) ≤ 1` (numerically `≈ 0.44`;
  `Morse.MilnorH.energy_hPath_lamStar`, `Morse.MilnorH.energy_hPath_lamStar_le`).
* For `λ* < λ ≤ 5λ*/4`, still `k = 3`, but now `kA = 1 − δ` with `δ = (3λc₀ − 1)/2 > 0`: a new
  last segment, from `ω_λ(1 − δ) = λ(δ^{1/3} − δ)` to `0` in time `δ`, of energy
  `λ²(δ^{1/3} − δ)²/δ ≥ (27/64) δ^{−1/3}` (`Morse.MilnorH.le_energy_hPath`).  Hence
  **`E(h(ω_λ)) → ∞` as `λ ↓ λ*`** (`Morse.MilnorH.tendsto_energy_hPath`).
* `√E` is `1`-Lipschitz for `d` (`Morse.PathSp.lipschitzWith_sqrt_energy`, Lemma 16.A of the
  exposition), so **`d(h(ω_λ), h(ω_{λ*})) → ∞`** (`Morse.MilnorH.tendsto_edist_hMap`), and
* **`Morse.milnor_h_not_continuous`**: `h : Ω* → Ω` is not continuous at `ω_{λ*}`
  (`Morse.milnor_h_not_continuous'`: not continuous).

The failure is in the `L²` term of `d`: the new segment is short in time and in space, but its
energy `ℓ²/δ` need not be small when `ω` is merely continuous.  Milnor's claim that `A` is
continuous is true (Lemma 17.A of the exposition) and is not involved: here
`A(ω_λ) = (1 − λc₀)/2` depends continuously on `λ`, and `k = 3` for all `λ* ≤ λ ≤ 5λ*/4`; what
moves is the last break point `kA = 3A`, which leaves `1`.

## Theorem 17.1 itself is true

Only this step of the proof fails.  The theorem is proved as `Morse.theorem_17_1`
(`Morse/Chapter10/FullPathTheorem.lean`) by a different route: dyadic subdivisions kept fixed on
the open sets `Y_k ⊆ Ω*`, and Theorem A of the Appendix applied to telescopes.
-/

open Set Filter Topology Function MeasureTheory
open scoped unitInterval ContDiff ENNReal

noncomputable section

namespace Morse

namespace MilnorH

/-! ### Milnor's distance on `ℝ` -/

/-- **In `M = ℝ`, Milnor's distance is `ρ(x, y) = |x − y|`.** -/
theorem riemDist_real (x y : ℝ) : riemDist (N := (univ : Set ℝ)) x y = ENNReal.ofReal |x - y| := by
  refine le_antisymm ?_ ?_
  · have hc : IsPiecewiseSmooth (fun t : ℝ => x + t * (y - x)) 0 1 :=
      IsPiecewiseSmooth.of_contDiffOn (s := univ) (by fun_prop) zero_le_one (subset_univ _)
    have h := riemDist_le_pathLength (N := (univ : Set ℝ)) hc fun _ _ => trivial
    have hd : ∀ t, deriv (fun t : ℝ => x + t * (y - x)) t = y - x := fun t => by
      simp
    have hL : pathLength (fun t : ℝ => x + t * (y - x)) 0 1 = |x - y| := by
      simp only [pathLength, hd, intervalIntegral.integral_const, smul_eq_mul, sub_zero, one_mul,
        Real.norm_eq_abs, abs_sub_comm]
    simpa [hL] using h
  · have := ofReal_norm_sub_le_riemDist (N := (univ : Set ℝ)) x y
    rwa [Real.norm_eq_abs, abs_sub_comm] at this

/-! ### Milnor's choices for `M = ℝ` and his `F`, `A`, `k` -/

/-- Milnor's `f : M → [0, ∞)` with compact sets `f⁻¹[0, r]` (p. 93): here `f(x) = |x|`. -/
def exhaust (x : ℝ) : ℝ := |x|

/-- Milnor's `ε₂` (p. 93): here `ε₂ ≡ 1`, admissible since `ε₁ ≡ ∞` for `M = ℝ`. -/
def epsTwo (_r : ℝ) : ℝ := 1

/-- `ε(ω) = ε₂(max_t f(ω(t)))` (p. 94). -/
def eps (γ : C(I, ℝ)) : ℝ := epsTwo (⨆ t, exhaust (γ t))

/-- `m_ω(α) = max_{|t − t'| ≤ α} ρ(ω(t), ω(t'))`, with `ρ(x, y) = |x − y|`. -/
def modulus (γ : C(I, ℝ)) (α : ℝ) : ℝ :=
  sSup {r | ∃ t t' : I, |(t : ℝ) - t'| ≤ α ∧ |γ t - γ t'| = r}

/-- **Milnor's `F(ω, α) = (α − 1) ε(ω) + max_{|t − t'| ≤ α} ρ(ω(t), ω(t'))`** (p. 94). -/
def milnorF (γ : C(I, ℝ)) (α : ℝ) : ℝ := (α - 1) * eps γ + modulus γ α

/-- **Milnor's `2A(ω)`** (p. 94): the zero of `F(ω, ·)`, taken as
`inf {α ∈ [0, 1] : F(ω, α) ≥ 0}` (it is the unique zero, `Morse.MilnorH.twoA_spec`). -/
def twoA (γ : C(I, ℝ)) : ℝ := sInf {α | α ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ milnorF γ α}

/-- **Milnor's `A(ω)`** (p. 94). -/
def milnorA (γ : C(I, ℝ)) : ℝ := twoA γ / 2

/-- **Milnor's `k`**: the largest integer `≤ 1/A(ω)` (p. 94). -/
def milnorK (γ : C(I, ℝ)) : ℕ := ⌊1 / milnorA γ⌋₊

theorem eps_eq (γ : C(I, ℝ)) : eps γ = 1 := rfl

theorem bddAbove_modulus (γ : C(I, ℝ)) (α : ℝ) :
    BddAbove {r | ∃ t t' : I, |(t : ℝ) - t'| ≤ α ∧ |γ t - γ t'| = r} := by
  refine ⟨2 * ‖γ‖, ?_⟩
  rintro r ⟨t, t', -, rfl⟩
  have h1 := γ.norm_coe_le_norm t
  have h2 := γ.norm_coe_le_norm t'
  rw [Real.norm_eq_abs] at h1 h2
  linarith [abs_sub (γ t) (γ t')]

theorem le_modulus (γ : C(I, ℝ)) {α : ℝ} (t t' : I) (h : |(t : ℝ) - t'| ≤ α) :
    |γ t - γ t'| ≤ modulus γ α :=
  le_csSup (bddAbove_modulus γ α) ⟨t, t', h, rfl⟩

theorem modulus_le (γ : C(I, ℝ)) {α C : ℝ} (hα : 0 ≤ α)
    (h : ∀ t t' : I, |(t : ℝ) - t'| ≤ α → |γ t - γ t'| ≤ C) : modulus γ α ≤ C :=
  csSup_le ⟨0, 0, 0, by simpa using hα, by simp⟩ (by rintro r ⟨t, t', ht, rfl⟩; exact h t t' ht)

theorem modulus_nonneg (γ : C(I, ℝ)) {α : ℝ} (hα : 0 ≤ α) : 0 ≤ modulus γ α :=
  (abs_nonneg _).trans (le_modulus γ 0 0 (by simpa using hα) : |γ 0 - γ 0| ≤ _)

theorem modulus_mono (γ : C(I, ℝ)) {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) :
    modulus γ α ≤ modulus γ β :=
  modulus_le γ hα fun t t' h => le_modulus γ t t' (h.trans hαβ)

theorem modulus_zero (γ : C(I, ℝ)) : modulus γ 0 = 0 := by
  refine le_antisymm (modulus_le γ le_rfl fun t t' h => ?_) (modulus_nonneg γ le_rfl)
  have : t = t' := Subtype.ext (sub_eq_zero.1 (abs_nonpos_iff.1 h))
  rw [this, sub_self, abs_zero]

/-- The modulus is subadditive: split a long step at a point at distance `α`. -/
theorem modulus_add_le (γ : C(I, ℝ)) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    modulus γ (α + β) ≤ modulus γ α + modulus γ β := by
  refine modulus_le γ (add_nonneg hα hβ) fun t t' h => ?_
  have hm := modulus_nonneg γ hβ
  by_cases hαt : |(t : ℝ) - t'| ≤ α
  · linarith [le_modulus γ t t' hαt]
  push Not at hαt
  have key : ∀ s : I, |(t : ℝ) - s| ≤ α → |(s : ℝ) - t'| ≤ β →
      |γ t - γ t'| ≤ modulus γ α + modulus γ β := fun s h1 h2 =>
    (abs_sub_le _ (γ s) _).trans (add_le_add (le_modulus γ t s h1) (le_modulus γ s t' h2))
  rcases le_or_gt (t : ℝ) t' with htt | htt
  · rw [abs_of_nonpos (by linarith)] at h hαt
    refine key ⟨t + α, by linarith [t.2.1], by linarith [t'.2.2]⟩ ?_ ?_ <;>
      · simp only
        rw [abs_le]
        constructor <;> linarith
  · rw [abs_of_pos (by linarith)] at h hαt
    refine key ⟨t - α, by linarith [t'.2.1], by linarith [t.2.2]⟩ ?_ ?_ <;>
      · simp only
        rw [abs_le]
        constructor <;> linarith

theorem abs_modulus_sub_le (γ : C(I, ℝ)) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    |modulus γ α - modulus γ β| ≤ modulus γ |α - β| := by
  wlog hab : α ≤ β generalizing α β
  · rw [abs_sub_comm, abs_sub_comm α]
    exact this hβ hα (le_of_not_ge hab)
  have h1 := modulus_mono γ hα hab
  have h2 := modulus_add_le γ hα (sub_nonneg.2 hab)
  rw [show α + (β - α) = β by ring] at h2
  rw [abs_sub_comm α, abs_of_nonneg (sub_nonneg.2 hab), abs_of_nonpos (sub_nonpos.2 h1)]
  linarith

/-- `m_ω(δ) → 0` as `δ → 0` (uniform continuity of `ω`). -/
theorem exists_modulus_le (γ : C(I, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ δ, 0 ≤ δ → δ < η → modulus γ δ ≤ ε := by
  obtain ⟨η, hη, h⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous γ.continuous) ε hε
  refine ⟨η, hη, fun δ hδ hδη => modulus_le γ hδ fun t t' htt => ?_⟩
  have := h (a := t) (b := t') (by rw [Subtype.dist_eq, Real.dist_eq]; linarith)
  rw [Real.dist_eq] at this
  exact this.le

theorem continuousOn_modulus (γ : C(I, ℝ)) : ContinuousOn (modulus γ) (Ici 0) := by
  intro α hα
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨η, hη, h⟩ := exists_modulus_le γ (half_pos hε)
  refine ⟨η, hη, fun {β} hβ hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  calc |modulus γ β - modulus γ α| ≤ modulus γ |β - α| := abs_modulus_sub_le γ hβ hα
    _ ≤ ε / 2 := h _ (abs_nonneg _) hdist
    _ < ε := half_lt_self hε

/-- `F(ω, ·)` is strictly increasing (p. 94). -/
theorem milnorF_lt (γ : C(I, ℝ)) {α β : ℝ} (hα : 0 ≤ α) (hαβ : α < β) :
    milnorF γ α < milnorF γ β := by
  have := modulus_mono γ hα hαβ.le
  simp only [milnorF, eps_eq, mul_one]
  linarith

theorem one_mem_twoA_set (γ : C(I, ℝ)) :
    (1 : ℝ) ∈ {α | α ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ milnorF γ α} :=
  ⟨⟨zero_le_one, le_rfl⟩, by
    simp only [milnorF, sub_self, zero_mul, zero_add]; exact modulus_nonneg γ zero_le_one⟩

/-- A zero of `F(ω, ·)` in `[0, 1]` is `2A(ω)`. -/
theorem twoA_eq (γ : C(I, ℝ)) {α₀ : ℝ} (h0 : α₀ ∈ Icc (0 : ℝ) 1) (hF : milnorF γ α₀ = 0) :
    twoA γ = α₀ := by
  refine IsLeast.csInf_eq ⟨⟨h0, hF.ge⟩, fun α hα => ?_⟩
  by_contra hlt
  push Not at hlt
  have := milnorF_lt γ hα.1.1 hlt
  linarith [hα.2]

/-- **Milnor's claims on `A`** (p. 94): for every `ω ∈ Ω*`, `F(ω, 0) < 0 ≤ F(ω, 1)`, and
`2A(ω) ∈ (0, 1]` is a zero of `F(ω, ·)` (the only one, `Morse.MilnorH.twoA_eq`). -/
theorem twoA_spec (γ : C(I, ℝ)) : twoA γ ∈ Ioc (0 : ℝ) 1 ∧ milnorF γ (twoA γ) = 0 := by
  have hc : ContinuousOn (milnorF γ) (Icc 0 1) :=
    ((continuousOn_id.sub continuousOn_const).mul continuousOn_const).add
      ((continuousOn_modulus γ).mono Icc_subset_Ici_self)
  have h0 : milnorF γ 0 = -1 := by simp [milnorF, eps_eq, modulus_zero]
  obtain ⟨α₀, hα₀, hF⟩ := intermediate_value_Icc zero_le_one hc
    ⟨by rw [h0]; norm_num, (one_mem_twoA_set γ).2⟩
  have h := twoA_eq γ hα₀ hF
  refine ⟨⟨?_, h ▸ hα₀.2⟩, h ▸ hF⟩
  rcases eq_or_lt_of_le hα₀.1 with h' | h'
  · rw [← h', h0] at hF
    norm_num at hF
  · rwa [h]

theorem milnorA_pos (γ : C(I, ℝ)) : 0 < milnorA γ := by
  unfold milnorA; linarith [(twoA_spec γ).1.1]

theorem milnorK_mul_le (γ : C(I, ℝ)) : (milnorK γ : ℝ) * milnorA γ ≤ 1 := by
  have hA := milnorA_pos γ
  calc (milnorK γ : ℝ) * milnorA γ ≤ 1 / milnorA γ * milnorA γ :=
        mul_le_mul_of_nonneg_right (Nat.floor_le (one_div_nonneg.2 hA.le)) hA.le
    _ = 1 := by field_simp

/-! ### Milnor's `h`: interpolation by segments at `0, A, …, kA, 1` -/

section plin

variable {x : ℝ → ℝ} {A : ℝ} {k j : ℕ} {t : ℝ}

/-- The segment from `(jA, x(jA))` to `((j + 1)A, x((j + 1)A))`. -/
def seg (x : ℝ → ℝ) (A : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  x (j * A) + (t - j * A) / A * (x ((j + 1) * A) - x (j * A))

/-- The last segment, from `(kA, x(kA))` to `(1, x(1))`. -/
def lastSeg (x : ℝ → ℝ) (A : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  x (k * A) + (t - k * A) / (1 - k * A) * (x 1 - x (k * A))

/-- **The path through `x(0), x(A), …, x(kA), x(1)`**, affine on `[jA, (j + 1)A]` (`j < k`) and
on `[kA, 1]`. -/
def plin (x : ℝ → ℝ) (A : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  if t < k * A then seg x A ⌊t / A⌋₊ t else lastSeg x A k t

theorem seg_right (hA : 0 < A) : seg x A j ((j + 1) * A) = x ((j + 1) * A) := by
  simp only [seg]
  field_simp
  ring

theorem plin_eq_seg (hA : 0 < A) (hj : j < k) (ht : t ∈ Icc (j * A) ((j + 1) * A)) :
    plin x A k t = seg x A j t := by
  rcases eq_or_lt_of_le ht.2 with heq | hlt
  · rw [heq, seg_right hA]
    rcases Nat.lt_or_ge (j + 1) k with hjk | hjk
    · have hlt' : ((j : ℝ) + 1) * A < k * A :=
        mul_lt_mul_of_pos_right (by exact_mod_cast hjk) hA
      have hfl : ⌊((j : ℝ) + 1) * A / A⌋₊ = j + 1 := by
        rw [mul_div_assoc, div_self hA.ne', mul_one]
        exact_mod_cast Nat.floor_natCast (j + 1)
      rw [plin, if_pos hlt', hfl, seg]
      push_cast
      simp
    · have hk : k = j + 1 := by omega
      subst hk
      rw [plin, if_neg (by push_cast; exact lt_irrefl _), lastSeg]
      push_cast
      simp
  · have h0 : 0 ≤ t := le_trans (by positivity) ht.1
    have hfl : ⌊t / A⌋₊ = j := by
      rw [Nat.floor_eq_iff (div_nonneg h0 hA.le), le_div_iff₀ hA, div_lt_iff₀ hA]
      exact ⟨ht.1, hlt⟩
    have htk : t < k * A := lt_of_lt_of_le hlt
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hA.le)
    rw [plin, if_pos htk, hfl]

theorem plin_eq_last (h : k * A ≤ t) : plin x A k t = lastSeg x A k t := by
  rw [plin, if_neg (not_lt.2 h)]

theorem contDiff_seg : ContDiff ℝ ∞ (seg x A j) := by unfold seg; fun_prop

theorem contDiff_lastSeg : ContDiff ℝ ∞ (lastSeg x A k) := by unfold lastSeg; fun_prop

/-- The break points `0, A, …, kA`. -/
def breaks (A : ℝ) (k : ℕ) : Finset ℝ := (Finset.range (k + 1)).image fun j : ℕ => (j : ℝ) * A

/-- `plin` is smooth on every piece `[s, t] ⊆ [0, 1]` free of break points. -/
theorem plin_piece (s t : ℝ) (hs : 0 ≤ s) (_hst : s < t) (_ht : t ≤ 1)
    (hB : ∀ y ∈ breaks A k, y ∉ Ioo s t) : ContDiffOn ℝ ∞ (plin x A k) (Icc s t) := by
  rcases le_or_gt ((k : ℝ) * A) s with hks | hks
  · exact contDiff_lastSeg.contDiffOn.congr fun τ hτ => plin_eq_last (hks.trans hτ.1)
  have hA : 0 < A := by
    by_contra hA
    push Not at hA
    linarith [mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) hA]
  have hsA : 0 ≤ s / A := div_nonneg hs hA.le
  have hjk : ⌊s / A⌋₊ < k := by
    rw [Nat.floor_lt hsA, div_lt_iff₀ hA]; exact hks
  have hjs : (⌊s / A⌋₊ : ℝ) * A ≤ s := by
    have := Nat.floor_le hsA
    rwa [le_div_iff₀ hA] at this
  have hsj : s < ((⌊s / A⌋₊ : ℝ) + 1) * A := by
    have := Nat.lt_floor_add_one (s / A)
    rwa [div_lt_iff₀ hA] at this
  have htj : t ≤ ((⌊s / A⌋₊ : ℝ) + 1) * A := by
    by_contra htj
    push Not at htj
    refine hB (((⌊s / A⌋₊ + 1 : ℕ) : ℝ) * A)
      (Finset.mem_image.2 ⟨⌊s / A⌋₊ + 1, Finset.mem_range.2 (by omega), rfl⟩) ?_
    push_cast
    exact ⟨hsj, htj⟩
  exact contDiff_seg.contDiffOn.congr fun τ hτ =>
    plin_eq_seg hA hjk ⟨hjs.trans hτ.1, hτ.2.trans htj⟩

theorem plin_isPiecewiseSmooth : IsPiecewiseSmooth (plin x A k) 0 1 :=
  ⟨zero_le_one, continuousOn_of_piecewise fun s t hs hst ht hB =>
    (plin_piece s t hs hst ht hB).continuousOn, breaks A k, plin_piece⟩

theorem plin_zero (hA : 0 < A) : plin x A k 0 = x 0 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [plin_eq_last (by simp [hk]), lastSeg, hk]
    simp
  · rw [plin_eq_seg hA hk ⟨by simp, by positivity⟩, seg]
    simp

theorem plin_one (hk : (k : ℝ) * A ≤ 1) : plin x A k 1 = x 1 := by
  rw [plin_eq_last hk, lastSeg]
  rcases eq_or_lt_of_le hk with h | h
  · rw [h]; simp
  · rw [div_self (by linarith : (1 : ℝ) - k * A ≠ 0)]; ring

theorem hasDerivAt_seg (t : ℝ) :
    HasDerivAt (seg x A j) ((x ((j + 1) * A) - x (j * A)) / A) t := by
  have := ((((hasDerivAt_id' t).sub_const ((j : ℝ) * A)).div_const A).mul_const
    (x ((j + 1) * A) - x (j * A))).const_add (x (j * A))
  rw [show (x ((j + 1) * A) - x (j * A)) / A = 1 / A * (x ((j + 1) * A) - x (j * A)) by ring]
  exact this

theorem hasDerivAt_lastSeg (t : ℝ) :
    HasDerivAt (lastSeg x A k) ((x 1 - x (k * A)) / (1 - k * A)) t := by
  have := ((((hasDerivAt_id' t).sub_const ((k : ℝ) * A)).div_const (1 - k * A)).mul_const
    (x 1 - x (k * A))).const_add (x (k * A))
  rw [show (x 1 - x (k * A)) / (1 - k * A) = 1 / (1 - k * A) * (x 1 - x (k * A)) by ring]
  exact this

theorem deriv_plin_seg (hA : 0 < A) (hj : j < k) (ht : t ∈ Ioo ((j : ℝ) * A) ((j + 1) * A)) :
    deriv (plin x A k) t = (x ((j + 1) * A) - x (j * A)) / A := by
  have heq : plin x A k =ᶠ[𝓝 t] seg x A j :=
    Filter.eventually_of_mem (Icc_mem_nhds ht.1 ht.2) fun τ hτ => plin_eq_seg hA hj hτ
  rw [heq.deriv_eq, (hasDerivAt_seg t).deriv]

theorem deriv_plin_last (ht : t ∈ Ioo ((k : ℝ) * A) 1) :
    deriv (plin x A k) t = (x 1 - x (k * A)) / (1 - k * A) := by
  have heq : plin x A k =ᶠ[𝓝 t] lastSeg x A k :=
    Filter.eventually_of_mem (Ioi_mem_nhds ht.1) fun τ hτ => plin_eq_last (le_of_lt hτ)
  rw [heq.deriv_eq, (hasDerivAt_lastSeg t).deriv]

/-- `plin` agrees with `x` at the nodes `jA`, `j ≤ k` (and at `1`, `Morse.MilnorH.plin_one`). -/
theorem plin_node (hA : 0 < A) (hj : j ≤ k) : plin x A k (j * A) = x (j * A) := by
  rcases lt_or_eq_of_le hj with hj | rfl
  · rw [plin_eq_seg hA hj ⟨le_rfl, by nlinarith⟩, seg]
    simp
  · rw [plin_eq_last le_rfl, lastSeg]
    simp

/-- On `(jA, (j + 1)A)` the acceleration of `plin` vanishes: it is a geodesic of `ℝ` there. -/
theorem deriv_deriv_plin_seg (hA : 0 < A) (hj : j < k)
    (ht : t ∈ Ioo ((j : ℝ) * A) ((j + 1) * A)) : deriv (deriv (plin x A k)) t = 0 := by
  have h : deriv (plin x A k) =ᶠ[𝓝 t] fun _ => (x ((j + 1) * A) - x (j * A)) / A :=
    Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun _ hτ => deriv_plin_seg hA hj hτ
  rw [h.deriv_eq, deriv_const]

/-- On `(kA, 1)` the acceleration of `plin` vanishes: it is a geodesic of `ℝ` there. -/
theorem deriv_deriv_plin_last (ht : t ∈ Ioo ((k : ℝ) * A) 1) :
    deriv (deriv (plin x A k)) t = 0 := by
  have h : deriv (plin x A k) =ᶠ[𝓝 t] fun _ => (x 1 - x (k * A)) / (1 - k * A) :=
    Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun _ hτ => deriv_plin_last hτ
  rw [h.deriv_eq, deriv_const]

theorem integral_seg (hA : 0 < A) (hj : j < k) :
    ∫ t in (j * A)..((j + 1) * A), ‖deriv (plin x A k) t‖ ^ 2 =
      (x ((j + 1) * A) - x (j * A)) ^ 2 / A := by
  rw [intervalIntegral.integral_congr_Ioo_of_le
    (g := fun _ => ((x ((j + 1) * A) - x (j * A)) / A) ^ 2) (by nlinarith)
    fun t ht => by simp only [Real.norm_eq_abs, sq_abs, deriv_plin_seg hA hj ht],
    intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

theorem integral_last (hk : (k : ℝ) * A ≤ 1) :
    ∫ t in (k * A)..1, ‖deriv (plin x A k) t‖ ^ 2 = (x 1 - x (k * A)) ^ 2 / (1 - k * A) := by
  rw [intervalIntegral.integral_congr_Ioo_of_le
    (g := fun _ => ((x 1 - x (k * A)) / (1 - k * A)) ^ 2) hk
    fun t ht => by simp only [Real.norm_eq_abs, sq_abs, deriv_plin_last ht],
    intervalIntegral.integral_const, smul_eq_mul]
  rcases eq_or_lt_of_le hk with h | h
  · rw [h]; simp
  · have : (1 : ℝ) - k * A ≠ 0 := by linarith
    field_simp

/-- **The energy of `plin`**: `Σ_{j < k} (x((j + 1)A) − x(jA))²/A + (x(1) − x(kA))²/(1 − kA)`
(the last term is `0` when `kA = 1`). -/
theorem energy_plin (hA : 0 < A) (hk : (k : ℝ) * A ≤ 1) :
    energy (plin x A k) 0 1 = ∑ j ∈ Finset.range k, (x ((j + 1) * A) - x (j * A)) ^ 2 / A +
      (x 1 - x (k * A)) ^ 2 / (1 - k * A) := by
  have hint : IntervalIntegrable (fun t => ‖deriv (plin x A k) t‖ ^ 2) volume 0 1 :=
    plin_isPiecewiseSmooth.intervalIntegrable_norm_deriv_sq
  have hkA : 0 ≤ (k : ℝ) * A := by positivity
  have hsub : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable (fun t => ‖deriv (plin x A k) t‖ ^ 2) volume a b :=
    fun a b ha hab hb => hint.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le zero_le_one]; exact Icc_subset_Icc ha hb)
  rw [energy, ← intervalIntegral.integral_add_adjacent_intervals (hsub 0 _ le_rfl hkA hk)
    (hsub _ 1 hkA hk le_rfl), integral_last hk]
  congr 1
  have := intervalIntegral.sum_integral_adjacent_intervals (a := fun j : ℕ => (j : ℝ) * A)
    (n := k) (f := fun t => ‖deriv (plin x A k) t‖ ^ 2) (μ := volume) fun j hj => by
      refine hsub _ _ (by positivity) (by gcongr; linarith) ?_
      have : ((j + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hj
      nlinarith
  simp only [Nat.cast_zero, zero_mul, Nat.cast_succ] at this
  rw [← this]
  exact Finset.sum_congr rfl fun j hj => integral_seg hA (Finset.mem_range.1 hj)

end plin

/-- **Milnor's `h(ω)`** (p. 94): agrees with `ω` at `0, A, 2A, …, kA` and `1`, and is the
(unique minimal) geodesic of `ℝ`, an affine segment, on each intermediate interval. -/
def hPath (γ : C(I, ℝ)) : ℝ → ℝ := plin (IccExtend zero_le_one γ) (milnorA γ) (milnorK γ)

/-- **Milnor's condition 1)**: `h(ω)` coincides with `ω` at `t = jA(ω)`, `j = 0, 1, …, k`. -/
theorem hPath_node (γ : C(I, ℝ)) {j : ℕ} (hj : j ≤ milnorK γ) :
    hPath γ (j * milnorA γ) = IccExtend zero_le_one γ (j * milnorA γ) :=
  plin_node (milnorA_pos γ) hj

/-- **Milnor's condition 1)**, at `t = 1`. -/
theorem hPath_one (γ : C(I, ℝ)) : hPath γ 1 = γ 1 := by
  rw [hPath, plin_one (milnorK_mul_le γ), IccExtend_of_mem _ _ ⟨zero_le_one, le_rfl⟩]
  rfl

/-- **Milnor's condition 2)**: `h(ω)` is a geodesic of `ℝ` (zero acceleration) on each
intermediate interval `(jA, (j + 1)A)`, `j < k`, and `(kA, 1)`. -/
theorem deriv_deriv_hPath (γ : C(I, ℝ)) {t : ℝ}
    (ht : (∃ j < milnorK γ, t ∈ Ioo ((j : ℝ) * milnorA γ) ((j + 1) * milnorA γ)) ∨
      t ∈ Ioo ((milnorK γ : ℝ) * milnorA γ) 1) : deriv (deriv (hPath γ)) t = 0 := by
  rcases ht with ⟨j, hj, ht⟩ | ht
  · exact deriv_deriv_plin_seg (milnorA_pos γ) hj ht
  · exact deriv_deriv_plin_last ht

theorem hPath_mem (γ : PathC (univ : Set ℝ) 0 0) :
    hPath γ ∈ pathSpace (univ : Set ℝ) 0 0 := by
  refine ⟨plin_isPiecewiseSmooth, fun _ _ => trivial, ?_, ?_⟩
  · rw [hPath, plin_zero (milnorA_pos _), IccExtend_of_mem _ _ ⟨le_rfl, zero_le_one⟩]
    exact γ.2.2.1
  · rw [hPath, plin_one (milnorK_mul_le _), IccExtend_of_mem _ _ ⟨zero_le_one, le_rfl⟩]
    exact γ.2.2.2

/-- **Milnor's map `h : Ω* → Ω`** (p. 94), for `M = ℝ`, `p = q = 0`. -/
def hMap (γ : PathC (univ : Set ℝ) 0 0) : PathSp (univ : Set ℝ) 0 0 :=
  ⟨hPath γ, hPath_mem γ⟩

/-! ### The family `ω_λ = λ ((1 − t)^{1/3} − (1 − t))` -/

/-- `g(t) = (1 − t)^{1/3} − (1 − t)`. -/
def g (t : ℝ) : ℝ := (1 - t) ^ (1 / 3 : ℝ) - (1 - t)

/-- `c₀ = max_{[0, 1]} g = 2√3/9`. -/
def c₀ : ℝ := 2 * √3 / 9

/-- `s₀ = √3/9`: `g(1 − s₀) = c₀`. -/
def s₀ : ℝ := √3 / 9

/-- **`λ* = √3/2`**, so that `λ* c₀ = 1/3` and `A(ω_{λ*}) = 1/3`. -/
def lamStar : ℝ := √3 / 2

theorem cbrt_cube {u : ℝ} (hu : 0 ≤ u) : (u ^ 3) ^ (1 / 3 : ℝ) = u := by
  have := Real.pow_rpow_inv_natCast hu (n := 3) (by norm_num)
  rwa [show ((3 : ℕ) : ℝ)⁻¹ = 1 / 3 by norm_num] at this

theorem cube_cbrt {s : ℝ} (hs : 0 ≤ s) : (s ^ (1 / 3 : ℝ)) ^ 3 = s := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
  norm_num

theorem sqrt3_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem sqrt3_pos : 0 < √3 := Real.sqrt_pos.2 (by norm_num)

theorem sqrt3_lt_two : √3 < 2 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem c₀_pos : 0 < c₀ := by unfold c₀; have := sqrt3_pos; positivity

theorem s₀_pos : 0 < s₀ := by unfold s₀; have := sqrt3_pos; positivity

theorem s₀_lt_half : s₀ < 1 / 2 := by unfold s₀; linarith [sqrt3_lt_two]

theorem lamStar_pos : 0 < lamStar := by unfold lamStar; have := sqrt3_pos; positivity

theorem lamStar_mul_c₀ : lamStar * c₀ = 1 / 3 := by
  unfold lamStar c₀
  nlinarith [sqrt3_sq]

theorem lamStar_sq : lamStar ^ 2 = 3 / 4 := by
  unfold lamStar
  rw [div_pow, sqrt3_sq]
  norm_num

theorem g_one_sub (s : ℝ) : g (1 - s) = s ^ (1 / 3 : ℝ) - s := by simp [g]

theorem g_zero : g 0 = 0 := by simp [g]

theorem g_one : g 1 = 0 := by simp [g]

/-- `0 ≤ g` on `[0, 1]`. -/
theorem g_nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ g t := by
  have hs : 0 ≤ 1 - t := by linarith [ht.2]
  have hu0 : 0 ≤ (1 - t) ^ (1 / 3 : ℝ) := Real.rpow_nonneg hs _
  have hu1 : (1 - t) ^ (1 / 3 : ℝ) ≤ 1 := Real.rpow_le_one hs (by linarith [ht.1]) (by norm_num)
  have : g t = (1 - t) ^ (1 / 3 : ℝ) - ((1 - t) ^ (1 / 3 : ℝ)) ^ 3 := by rw [g, cube_cbrt hs]
  rw [this]
  nlinarith [mul_nonneg hu0 (mul_nonneg hu0 (sub_nonneg.2 hu1))]

/-- `g ≤ c₀` on `[0, 1]`: with `u = (1 − t)^{1/3}`, `c₀ − g = (u − √3/3)²(u + 2√3/3)`. -/
theorem g_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : g t ≤ c₀ := by
  have hs : 0 ≤ 1 - t := by linarith [ht.2]
  have hu0 : 0 ≤ (1 - t) ^ (1 / 3 : ℝ) := Real.rpow_nonneg hs _
  have : g t = (1 - t) ^ (1 / 3 : ℝ) - ((1 - t) ^ (1 / 3 : ℝ)) ^ 3 := by rw [g, cube_cbrt hs]
  rw [this, c₀]
  have h0 := sqrt3_pos
  have key : 0 ≤ ((1 - t) ^ (1 / 3 : ℝ) - √3 / 3) ^ 2 * ((1 - t) ^ (1 / 3 : ℝ) + 2 * √3 / 3) := by
    positivity
  nlinarith [key, sqrt3_sq]

/-- `g(1 − s₀) = c₀`: the maximum of `g`. -/
theorem g_one_sub_s₀ : g (1 - s₀) = c₀ := by
  have h3 : √3 ^ 3 = 3 * √3 := by rw [pow_succ, sqrt3_sq]
  have hs : s₀ = (√3 / 3) ^ 3 := by rw [s₀, div_pow, h3]; ring
  rw [g_one_sub, hs, cbrt_cube (by have := sqrt3_pos; positivity), c₀, div_pow, h3]
  ring

/-- **The family `ω_λ(t) = λ((1 − t)^{1/3} − (1 − t))`** in `Ω*(ℝ; 0, 0)`. -/
def omegaFam (lam : ℝ) : PathC (univ : Set ℝ) 0 0 :=
  ⟨⟨fun t => lam * g t, continuous_const.mul
      (((Real.continuous_rpow_const (by norm_num)).comp
        (continuous_const.sub continuous_subtype_val)).sub
        (continuous_const.sub continuous_subtype_val))⟩,
    fun _ => trivial, by simp [g_zero], by simp [g_one]⟩

theorem omegaFam_apply (lam : ℝ) (t : I) : (omegaFam lam : C(I, ℝ)) t = lam * g t := rfl

theorem extend_omegaFam (lam : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IccExtend zero_le_one (omegaFam lam : C(I, ℝ)) t = lam * g t := by
  rw [IccExtend_of_mem _ _ ht]
  rfl

/-- **Uniform convergence**: `d*(ω_λ, ω_μ) ≤ c₀ |λ − μ|`. -/
theorem dist_omegaFam_le (lam mu : ℝ) : dist (omegaFam lam) (omegaFam mu) ≤ c₀ * |lam - mu| := by
  rw [Subtype.dist_eq]
  refine (ContinuousMap.dist_le (by have := c₀_pos; positivity)).2 fun t => ?_
  rw [omegaFam_apply, omegaFam_apply, Real.dist_eq, ← sub_mul, abs_mul,
    abs_of_nonneg (g_nonneg t.2), mul_comm]
  exact mul_le_mul_of_nonneg_right (g_le t.2) (abs_nonneg _)

theorem continuous_omegaFam : Continuous omegaFam := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨c₀, c₀_pos.le⟩) fun lam mu => ?_).continuous
  change dist (omegaFam lam) (omegaFam mu) ≤ c₀ * dist lam mu
  rw [Real.dist_eq]
  exact dist_omegaFam_le lam mu

/-- **`ω_λ → ω_{λ*}` uniformly as `λ → λ*`.** -/
theorem tendsto_omegaFam : Tendsto omegaFam (𝓝 lamStar) (𝓝 (omegaFam lamStar)) :=
  continuous_omegaFam.tendsto lamStar

/-- `m_{ω_λ}(α) = λ c₀` for `α ≥ s₀`. -/
theorem modulus_omegaFam {lam α : ℝ} (hlam : 0 ≤ lam) (hα : s₀ ≤ α) :
    modulus (omegaFam lam) α = lam * c₀ := by
  refine le_antisymm (modulus_le _ (s₀_pos.le.trans hα) fun t t' _ => ?_) ?_
  · rw [omegaFam_apply, omegaFam_apply, ← mul_sub, abs_mul, abs_of_nonneg hlam]
    refine mul_le_mul_of_nonneg_left ?_ hlam
    rw [abs_le]
    constructor <;> linarith [g_nonneg t.2, g_le t.2, g_nonneg t'.2, g_le t'.2]
  · have h1 : (1 : ℝ) - s₀ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [s₀_lt_half], by linarith [s₀_pos]⟩
    have := le_modulus (omegaFam lam) (α := α) ⟨1 - s₀, h1⟩ 1
      (by simp only [Set.Icc.coe_one]; rw [sub_sub_cancel_left, abs_neg, abs_of_pos s₀_pos]
          exact hα)
    rw [omegaFam_apply, omegaFam_apply] at this
    simpa [g_one_sub_s₀, g_one, abs_of_nonneg (mul_nonneg hlam c₀_pos.le)] using this

/-- `2A(ω_λ) = 1 − λc₀` while `0 ≤ λc₀ ≤ 1/2`. -/
theorem twoA_omegaFam {lam : ℝ} (hlam : 0 ≤ lam) (h : lam * c₀ ≤ 1 / 2) :
    twoA (omegaFam lam) = 1 - lam * c₀ := by
  have hp : 0 ≤ lam * c₀ := mul_nonneg hlam c₀_pos.le
  refine twoA_eq _ ⟨by linarith, by linarith⟩ ?_
  rw [milnorF, eps_eq, modulus_omegaFam hlam (by linarith [s₀_lt_half])]
  ring

theorem milnorA_omegaFam {lam : ℝ} (hlam : 0 ≤ lam) (h : lam * c₀ ≤ 1 / 2) :
    milnorA (omegaFam lam) = (1 - lam * c₀) / 2 := by
  rw [milnorA, twoA_omegaFam hlam h]

theorem lam_mul_c₀_mem {lam : ℝ} (h1 : lamStar ≤ lam) (h2 : lam ≤ 5 / 4 * lamStar) :
    1 / 3 ≤ lam * c₀ ∧ lam * c₀ ≤ 5 / 12 := by
  have hc := c₀_pos
  have := lamStar_mul_c₀
  constructor <;> nlinarith

/-- `k(ω_λ) = 3` for `λ* ≤ λ ≤ 5λ*/4`. -/
theorem milnorK_omegaFam {lam : ℝ} (h1 : lamStar ≤ lam) (h2 : lam ≤ 5 / 4 * lamStar) :
    milnorK (omegaFam lam) = 3 := by
  obtain ⟨hp1, hp2⟩ := lam_mul_c₀_mem h1 h2
  have hlam : 0 ≤ lam := lamStar_pos.le.trans h1
  rw [milnorK, milnorA_omegaFam hlam (by linarith), Nat.floor_eq_iff (by
    rw [one_div_div]; exact div_nonneg (by norm_num) (by linarith)), one_div_div,
    le_div_iff₀ (by linarith), div_lt_iff₀ (by linarith)]
  push_cast
  constructor <;> linarith

/-- **`A(ω_{λ*}) = 1/3`**, so `1/A(ω_{λ*}) = 3` is an integer. -/
theorem milnorA_lamStar : milnorA (omegaFam lamStar) = 1 / 3 := by
  rw [milnorA_omegaFam lamStar_pos.le (by rw [lamStar_mul_c₀]; norm_num), lamStar_mul_c₀]
  norm_num

/-- `1/A(ω_{λ*}) = 3`, an integer: the last break point `kA` is `1`. -/
theorem one_div_milnorA_lamStar : 1 / milnorA (omegaFam lamStar) = 3 := by
  rw [milnorA_lamStar]
  norm_num

theorem milnorK_lamStar : milnorK (omegaFam lamStar) = 3 :=
  milnorK_omegaFam le_rfl (by linarith [lamStar_pos])

/-- **`E(h(ω_{λ*}))` is finite**: `h(ω_{λ*})` has break points `0, 1/3, 2/3, 1`, and
`E = 3λ*²(g(1/3)² + (g(2/3) − g(1/3))² + g(2/3)²)` (`≈ 0.44`). -/
theorem energy_hPath_lamStar : energy (hPath (omegaFam lamStar)) 0 1 =
    3 * lamStar ^ 2 * (g (1 / 3) ^ 2 + (g (2 / 3) - g (1 / 3)) ^ 2 + g (2 / 3) ^ 2) := by
  rw [hPath, milnorA_lamStar, milnorK_lamStar, energy_plin (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  rw [extend_omegaFam lamStar (t := 1 / 3) ⟨by norm_num, by norm_num⟩,
    extend_omegaFam lamStar (t := 2 / 3) ⟨by norm_num, by norm_num⟩, omegaFam_apply,
    omegaFam_apply]
  simp only [Set.Icc.coe_zero, Set.Icc.coe_one, g_zero, g_one]
  ring

theorem energy_hPath_lamStar_le : energy (hPath (omegaFam lamStar)) 0 1 ≤ 1 := by
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ lamStar * g t ∧ lamStar * g t ≤ 1 / 3 := fun t ht =>
    ⟨mul_nonneg lamStar_pos.le (g_nonneg ht), by
      rw [← lamStar_mul_c₀]; exact mul_le_mul_of_nonneg_left (g_le ht) lamStar_pos.le⟩
  obtain ⟨h1, h1'⟩ := hb (1 / 3) ⟨by norm_num, by norm_num⟩
  obtain ⟨h2, h2'⟩ := hb (2 / 3) ⟨by norm_num, by norm_num⟩
  rw [energy_hPath_lamStar]
  nlinarith [mul_nonneg h1 h2]

/-- `δ_λ = (3λc₀ − 1)/2 = 1 − 3A(ω_λ)`: the length of the new last interval. -/
def delta (lam : ℝ) : ℝ := (3 * (lam * c₀) - 1) / 2

theorem delta_pos {lam : ℝ} (h : lamStar < lam) : 0 < delta lam := by
  have := lamStar_mul_c₀
  have := c₀_pos
  unfold delta
  nlinarith

/-- **The new last segment**: for `λ* < λ ≤ 5λ*/4`,
`E(h(ω_λ)) ≥ λ²(δ^{1/3} − δ)²/δ ≥ (27/64) δ^{−1/3}`, `δ = δ_λ`. -/
theorem le_energy_hPath {lam : ℝ} (h1 : lamStar < lam) (h2 : lam ≤ 5 / 4 * lamStar) :
    27 / 64 * (delta lam ^ (1 / 3 : ℝ))⁻¹ ≤ energy (hPath (omegaFam lam)) 0 1 := by
  obtain ⟨hp1, hp2⟩ := lam_mul_c₀_mem h1.le h2
  have hlam : 0 ≤ lam := lamStar_pos.le.trans h1.le
  have hA := milnorA_omegaFam hlam (by linarith)
  have hK := milnorK_omegaFam h1.le h2
  have hδ := delta_pos h1
  have hδ8 : delta lam ≤ 1 / 8 := by unfold delta; linarith
  set v := delta lam ^ (1 / 3 : ℝ) with hv
  have hv0 : 0 < v := Real.rpow_pos_of_pos hδ _
  have hv3 : v ^ 3 = delta lam := cube_cbrt hδ.le
  have hv2 : v ≤ 1 / 2 := by
    have := Real.rpow_le_rpow hδ.le hδ8 (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rwa [show (1 / 8 : ℝ) = (1 / 2) ^ 3 by norm_num, cbrt_cube (by norm_num)] at this
  -- the energy formula, keeping only the last segment
  have hkA : ((3 : ℕ) : ℝ) * ((1 - lam * c₀) / 2) = 1 - delta lam := by
    unfold delta; push_cast; ring
  have hE : (lam * (v - v ^ 3)) ^ 2 / v ^ 3 ≤ energy (hPath (omegaFam lam)) 0 1 := by
    rw [hPath, hA, hK, energy_plin (by linarith) (by rw [hkA]; linarith), hkA,
      extend_omegaFam _ ⟨zero_le_one, le_rfl⟩, extend_omegaFam _ ⟨by linarith, by linarith⟩,
      g_one, g_one_sub, ← hv, ← hv3, sub_sub_cancel]
    have hsum : 0 ≤ ∑ j ∈ Finset.range 3,
        (IccExtend zero_le_one (omegaFam lam : C(I, ℝ)) ((j + 1) * ((1 - lam * c₀) / 2)) -
          IccExtend zero_le_one (omegaFam lam : C(I, ℝ)) (j * ((1 - lam * c₀) / 2))) ^ 2 /
            ((1 - lam * c₀) / 2) :=
      Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (by linarith)
    have : (lam * 0 - lam * (v - v ^ 3)) ^ 2 = (lam * (v - v ^ 3)) ^ 2 := by ring
    rw [this]
    linarith
  -- `λ²(v − v³)²/v³ = λ²(1 − v²)²/v ≥ (3/4)(9/16)/v`
  have hlam2 : 3 / 4 ≤ lam ^ 2 := by rw [← lamStar_sq]; nlinarith [lamStar_pos]
  have h1v : 9 / 16 ≤ (1 - v ^ 2) ^ 2 := by nlinarith
  have heq : (lam * (v - v ^ 3)) ^ 2 / v ^ 3 = lam ^ 2 * (1 - v ^ 2) ^ 2 / v := by
    field_simp
  refine le_trans ?_ (heq ▸ hE)
  rw [← div_eq_mul_inv, div_le_div_iff_of_pos_right hv0]
  nlinarith [mul_le_mul hlam2 h1v (by norm_num) (by positivity)]

theorem tendsto_delta_cbrt :
    Tendsto (fun lam => delta lam ^ (1 / 3 : ℝ)) (𝓝[>] lamStar) (𝓝[>] 0) := by
  have hc : Continuous fun lam => delta lam ^ (1 / 3 : ℝ) :=
    (Real.continuous_rpow_const (by norm_num)).comp (by unfold delta; fun_prop)
  have h0 : delta lamStar ^ (1 / 3 : ℝ) = 0 := by
    rw [delta, lamStar_mul_c₀, show (3 * (1 / 3 : ℝ) - 1) / 2 = 0 by norm_num,
      Real.zero_rpow (by norm_num)]
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := hc.tendsto lamStar
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with lam hlam
    exact Real.rpow_pos_of_pos (delta_pos hlam) _

/-- **`E(h(ω_λ)) → ∞` as `λ ↓ λ*`.** -/
theorem tendsto_energy_hPath :
    Tendsto (fun lam => energy (hPath (omegaFam lam)) 0 1) (𝓝[>] lamStar) atTop := by
  have h1 : Tendsto (fun lam => 27 / 64 * (delta lam ^ (1 / 3 : ℝ))⁻¹) (𝓝[>] lamStar) atTop :=
    (tendsto_inv_nhdsGT_zero.comp tendsto_delta_cbrt).const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [Ioo_mem_nhdsGT (show lamStar < 5 / 4 * lamStar by linarith [lamStar_pos])]
    with lam hlam
  exact le_energy_hPath hlam.1 hlam.2.le

/-- **`√E` is `1`-Lipschitz for Milnor's metric `d`** (Lemma 16.A of the exposition). -/
theorem lipschitzWith_sqrt_energy :
    LipschitzWith 1 fun γ : PathSp (univ : Set ℝ) 0 0 => √(energy γ 0 1) :=
  PathSp.lipschitzWith_sqrt_energy le_rfl zero_le_one le_rfl

/-- **`d(h(ω_λ), h(ω_{λ*})) → ∞` as `λ ↓ λ*`.** -/
theorem tendsto_edist_hMap :
    Tendsto (fun lam => edist (hMap (omegaFam lam)) (hMap (omegaFam lamStar)))
      (𝓝[>] lamStar) (𝓝 ⊤) := by
  set E₀ := √(energy (hPath (omegaFam lamStar)) 0 1)
  have h1 : Tendsto (fun lam => √(energy (hPath (omegaFam lam)) 0 1) - E₀) (𝓝[>] lamStar)
      atTop := by
    exact (tendsto_atTop_add_const_right _ (-E₀)
      (Real.tendsto_sqrt_atTop.comp tendsto_energy_hPath)).congr fun _ =>
        (sub_eq_add_neg _ _).symm
  refine tendsto_nhds_top_mono (ENNReal.tendsto_ofReal_atTop.comp h1)
    (Eventually.of_forall fun lam => ?_)
  have := lipschitzWith_sqrt_energy.edist_le_mul (hMap (omegaFam lam)) (hMap (omegaFam lamStar))
  rw [ENNReal.coe_one, one_mul, edist_dist, Real.dist_eq] at this
  exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans this

end MilnorH

open MilnorH in
/-- **Milnor's `h : Ω* → Ω` (p. 94) is not continuous** (for `d` on `Ω`): for `M = ℝ`,
`p = q = 0`, `f = |·|` and `ε₂ ≡ 1`, `h` is not continuous at `ω_{λ*}`, `λ* = √3/2`:
`ω_λ → ω_{λ*}` uniformly, while `E(h(ω_λ)) → ∞` as `λ ↓ λ*` and `E` is continuous on `Ω`. -/
theorem milnor_h_not_continuous : ¬ ContinuousAt hMap (omegaFam lamStar) := by
  intro hcont
  have h1 : Tendsto (fun lam => hMap (omegaFam lam)) (𝓝[>] lamStar)
      (𝓝 (hMap (omegaFam lamStar))) :=
    (hcont.tendsto.comp tendsto_omegaFam).mono_left nhdsWithin_le_nhds
  have h2 := ((PathSp.continuous_energy (N := (univ : Set ℝ)) (p := (0 : ℝ)) (q := 0) le_rfl
    zero_le_one le_rfl).tendsto _).comp h1
  exact not_tendsto_nhds_of_tendsto_atTop tendsto_energy_hPath _ h2

open MilnorH in
/-- **Milnor's `h : Ω* → Ω` is not continuous.** -/
theorem milnor_h_not_continuous' : ¬ Continuous hMap := fun h =>
  milnor_h_not_continuous h.continuousAt

end Morse
