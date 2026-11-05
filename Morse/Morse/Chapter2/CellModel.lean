import Morse.Chapter2.Crossing

/-!
Milnor, *Morse Theory*, §3, pp. 14–19 (the part of the proof of Theorem 3.2 that takes place in
Morse coordinates).

# Passing a non-degenerate critical point: the local model

**Theorem 3.2** (p. 14), paraphrased: let `p` be a non-degenerate critical point, of index `λ`, of
a smooth `f : M → ℝ`, put `c = f(p)`, and suppose that `f⁻¹[c - ε, c + ε]` is compact and contains
no critical point other than `p`. Then for all sufficiently small `ε`, `M^{c+ε}` has the homotopy
type of `M^{c-ε}` with a `λ`-cell attached. (The text as reproduced in the scan reads "a `k`-cell",
and the index "`A`"; probably defects of the scan, see `Exposition/Findings.md`, "About the
scan".)

Milnor's proof (pp. 15–19) works in coordinates `u¹, …, uⁿ` around `p` in which
`f = c - ξ + η`, with `ξ = (u¹)² + ⋯ + (u^λ)²` and `η = (u^{λ+1})² + ⋯ + (uⁿ)²` (Lemma 2.2), on a
neighbourhood whose image contains the ball `∑ (uⁱ)² ≤ 2ε`. He replaces `f` by
`F = f - μ(ξ + 2η)` for a smooth `μ` (p. 16), proves that `F` has the same sublevel set
`M^{c+ε}` and the same critical points as `f` (Assertions 1, 2), applies Theorem 3.1 to `F`
(Assertion 3), and finally pushes the "handle" `H` onto the cell `e^λ = {ξ ≤ ε, η = 0}` along
"vertical" lines (Assertion 4, Diagram 7).

This file contains everything that happens inside the coordinate patch. Points of the patch are
written `v = (x, y) ∈ X × Y`, for two real inner product spaces `X` (Milnor's `ℝ^λ`) and `Y`
(`ℝ^{n-λ}`), with `ξ = ‖x‖²` and `η = ‖y‖²` (`CellModel.xi`, `CellModel.eta`); `f` becomes
`CellModel.morseQuad c v = c - ξ + η`. Since these formulas make sense on all of `X × Y`, every
statement is proved there. The transfer to a neighbourhood of `p`, the application of Theorem 3.1
and the global conclusion are in `Morse/Chapter2/CellAttach.lean`.

## What Milnor's text leaves implicit

* **The function `μ`** (p. 16) is required to be `C^∞` with `μ(0) > ε`, `μ(r) = 0` for `r ≥ 2ε`
  and `-1 < μ' ≤ 0`; Milnor does not show that one exists. Since `μ` must drop by more than `ε`
  on `[0, 2ε]` with slope less than `1` in absolute value, its slope has to be controlled
  everywhere (the obvious candidate `A (1 - ψ(r/2ε))`, `A > ε`, has slope `-A/ε < -1` at `r = ε`,
  where Mathlib's smooth step `ψ = Real.smoothTransition` has slope `2`). We integrate a plateau:
  `μ(r) = (3/4) ∫_r^{2ε} β`, where `β(s) = ψ(4 - 2s/ε)`, so that
  `β = 1` on `(-∞, 3ε/2]` and `β = 0` on `[2ε, ∞)`. Then `μ' = -(3/4) β ∈ [-3/4, 0]` by the
  fundamental theorem of calculus, and `μ(0) ≥ (3/4)(3ε/2) > ε` (`Morse.milnorMu`,
  `Morse.isMilnorMu_milnorMu`). Every other statement uses only Milnor's four conditions
  (`Morse.IsMilnorMu`), from which follow `μ ≥ 0`, `μ` decreasing, and `s ↦ s + μ(s)` increasing.
* **Assertion 1** (p. 16) needs `μ ≥ 0` (for `F ≤ f`), which Milnor uses without stating it.
* **Assertion 2** (p. 17). As reproduced in the scan, the display reads
  `∂F/∂η = 1 - 2μ'(ξ + 2η) > 1` (with the `∂F` of `∂F/∂η` dropped, so the scan may also have
  lost the bar of a `≥`); since `μ' = 0` for `r ≥ 2ε`, the correct bound is `≥ 1`, which suffices. His conclusion, that `dF` vanishes only
  where "`dξ` and `dη` are simultaneously zero", uses that `dξ` and `dη` involve disjoint sets of
  coordinates, so that `a dξ + b dη = 0` with `a, b ≠ 0` forces `dξ = dη = 0`. Here: the
  derivative of `F` at `(x, y)` sends `(x, 0)` to `-2(1 + μ')‖x‖²` and `(0, y)` to
  `2(1 - 2μ')‖y‖²` (`CellModel.hasFDerivAt_morseF`), so it vanishes only at the origin
  (`CellModel.eq_zero_of_hasFDerivAt_morseF`). The same computation with `μ = 0` is the statement
  for `f`.
* **`e^λ ⊆ H`** (p. 18): "since `∂F/∂ξ < 0` we have `F(q) ≤ F(p)`". On the cell `η = 0`, so
  `F = c - (ξ + μ(ξ))`, and `s ↦ s + μ(s)` is increasing (`μ' > -1`), whence
  `F ≤ c - μ(0) < c - ε` on all of `e^λ` (`CellModel.morseF_lt_of_mem_cellModel`). The points of
  `e^λ` with `ξ = ε` lie in `M^{c-ε}`; they belong to `H` only as limits of points with `ξ < ε`
  (`CellModel.cellModel_subset_handleModel`). The scan's `f(q) ≥ c - e` reads `c - ε`.
* **`F⁻¹(-∞, c-ε] = M^{c-ε} ∪ H`** (p. 17, the notation introduced after Assertion 3) holds
  because `F⁻¹(-∞, c-ε]` is closed and contains `M^{c-ε}` (as `F ≤ f`); `H` is defined as the
  closure of the difference (`Morse.eq_union_closure_diff`, `CellModel.sublevel_morseF_eq_union`).
* **The three cases of `r_t` are one formula.** Milnor's deformation (pp. 18–19) is
  `r_t(x, y) = (x, s y)` with `s = t` (Case 1, `ξ ≤ ε`),
  `s = t + (1 - t)((ξ - ε)/η)^{1/2}` (Case 2, `ε ≤ ξ ≤ η + ε`) and `s = 1` (Case 3,
  `η + ε ≤ ξ`), with `r_1 = id`. We let the parameter run the other way, `r_0 = id`, as in
  Theorem 3.1 and in Mathlib's homotopies, and use
  `σ_t(v) = 1 - t + t √(min(1, (ξ - ε)/η))`, `r_t(x, y) = (x, σ_t y)` (`CellModel.retractModel`).
  In Case 1, `(ξ - ε)/η ≤ 0` and the (Mathlib) square root of a non-positive number is `0`; in
  Case 3 the minimum is `1`. So the single formula agrees with Milnor's three
  (`CellModel.retractModel_of_xi_le`, `retractModel_of_case2`, `retractModel_of_le_xi`), and the
  formulas agree on the overlaps of the cases, which Milnor checks.
* **The point `ξ = ε`, `η = 0`.** There Case 2 reads `(ξ - ε)/η = 0/0`, which Milnor does not
  discuss. With Lean's convention `x / 0 = 0` the formula gives `y ↦ (1 - t) y`, harmless because
  `y = 0`.
* **Continuity** ("the reader should verify that the functions `s_t uⁱ` remain continuous as
  `ξ → ε`, `η → 0`", p. 19). Away from `η = 0` the formula is continuous. At a point `(x₀, 0)`,
  `σ_t` itself is discontinuous, but `0 ≤ σ_t ≤ 1` gives `‖r_t(v) - (x₀, 0)‖ ≤ ‖v - (x₀, 0)‖`
  (sup norm). So `(t, v) ↦ r_t(v)` is continuous on all of `[0, 1] × X × Y`
  (`CellModel.continuous_retractModel`), not only on `F⁻¹(-∞, c-ε]`.
* **What `r_t` does** (p. 19, "each `r_t` maps `F⁻¹(-∞, c-ε]` into itself", "`r_0` maps the entire
  region into `e^λ`", resp. "into the hypersurface `f⁻¹(c - ε)`"): `r_t` keeps `ξ` and does not
  increase `η`, and `F` increases with `η` (`CellModel.morseF_retractModel_le`); `r_1` takes
  every point of `X × Y` into `M^{c-ε} ∪ e^λ` (`CellModel.retractModel_one_mem`); `r_t` fixes
  `M^{c-ε} ∪ e^λ` pointwise. On `F⁻¹(-∞, c-ε]` it moves only points of the ellipsoid
  `ξ + 2η ≤ 2ε` and keeps them there (`CellModel.retractModel_of_notMem_ellipsoid`,
  `CellModel.retractModel_mem_ellipsoid`); this is what makes "let `r_t` be the identity outside
  of `U`" continuous in `CellAttach.lean`.

## Main definitions and results

* `Morse.IsMilnorMu ε μ`: Milnor's conditions on `μ`; `Morse.milnorMu`, `Morse.isMilnorMu_milnorMu`.
* `CellModel.xi`, `CellModel.eta`, `CellModel.morseQuad c = c - ξ + η`,
  `CellModel.morseF μ c = c - ξ + η - μ(ξ + 2η)` (Milnor's `F`), `CellModel.ellipsoid`,
  `CellModel.cellModel ε = {ξ ≤ ε, η = 0}` (Milnor's `e^λ`), `CellModel.handleModel` (`H`).
* Assertion 1: `CellModel.morseF_le_iff`. Assertion 2: `CellModel.hasFDerivAt_morseF_zero_iff`,
  `CellModel.hasFDerivAt_morseQuad_zero_iff` (a critical point in the sense of
  `Morse.IsCriticalPoint` is a point where the derivative is `0`).
* `CellModel.sublevel_morseF_eq_union`, `CellModel.cellModel_subset_handleModel`,
  `CellModel.cellModel_inter_sublevel`.
* `CellModel.retractModel` (Milnor's `r_t`), its properties, and
  `CellModel.isStrongDeformationRetract_model`: **Assertion 4 in the model**,
  `M^{c-ε} ∪ e^λ` is a strong deformation retract of `F⁻¹(-∞, c-ε] = M^{c-ε} ∪ H`.
-/

open Set Filter Topology Function
open scoped ContDiff unitInterval

noncomputable section

namespace Morse

/-! ### A closed set is the union of a subset and the closure of the difference -/

/-- If `A ⊆ B` and `B` is closed, then `B = A ∪ closure (B \ A)`. This is Milnor's
`F⁻¹(-∞, c-ε] = M^{c-ε} ∪ H` (p. 17), with `H` the closure of `F⁻¹(-∞, c-ε] - M^{c-ε}`. -/
theorem eq_union_closure_diff {T : Type*} [TopologicalSpace T] {A B : Set T} (hAB : A ⊆ B)
    (hB : IsClosed B) : B = A ∪ closure (B \ A) := by
  refine Subset.antisymm (fun x hx => ?_) (union_subset hAB ?_)
  · by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · exact Or.inr (subset_closure ⟨hx, hxA⟩)
  · exact closure_minimal sdiff_subset hB

/-! ### Milnor's function `μ` -/

/-- **Milnor's conditions on `μ`** (p. 16): `μ : ℝ → ℝ` is `C^∞`, `μ(0) > ε`, `μ(r) = 0` for
`r ≥ 2ε`, and `-1 < μ'(r) ≤ 0` for all `r`. -/
structure IsMilnorMu (ε : ℝ) (μ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ μ
  lt_apply_zero : ε < μ 0
  eq_zero : ∀ r, 2 * ε ≤ r → μ r = 0
  neg_one_lt_deriv : ∀ r, -1 < deriv μ r
  deriv_nonpos : ∀ r, deriv μ r ≤ 0

namespace IsMilnorMu

variable {ε : ℝ} {μ : ℝ → ℝ}

theorem differentiable (h : IsMilnorMu ε μ) : Differentiable ℝ μ :=
  h.contDiff.differentiable (by simp)

theorem continuous (h : IsMilnorMu ε μ) : Continuous μ :=
  h.contDiff.continuous

/-- `μ` is decreasing (`μ' ≤ 0`). -/
theorem antitone (h : IsMilnorMu ε μ) : Antitone μ :=
  antitone_of_deriv_nonpos h.differentiable h.deriv_nonpos

/-- `μ ≥ 0`: it decreases to `μ(2ε) = 0`. -/
theorem nonneg (h : IsMilnorMu ε μ) (r : ℝ) : 0 ≤ μ r := by
  rcases le_total (2 * ε) r with hr | hr
  · rw [h.eq_zero r hr]
  · rw [← h.eq_zero (2 * ε) le_rfl]
    exact h.antitone hr

/-- `s ↦ s + μ(s)` is increasing, since its derivative `1 + μ'` is positive. This is Milnor's
`∂F/∂ξ = -1 - μ' < 0` along `η = 0`. -/
theorem monotone_add (h : IsMilnorMu ε μ) : Monotone fun s => s + μ s := by
  have hd : ∀ s, HasDerivAt (fun s => s + μ s) (1 + deriv μ s) s := fun s =>
    (hasDerivAt_id s).add (h.differentiable s).hasDerivAt
  refine monotone_of_deriv_nonneg (fun s => (hd s).differentiableAt) fun s => ?_
  rw [(hd s).deriv]
  linarith [h.neg_one_lt_deriv s]

end IsMilnorMu

/-- The plateau `β(s) = ψ(4 - 2s/ε)`, `ψ = Real.smoothTransition`: `β = 1` for `s ≤ 3ε/2` and
`β = 0` for `s ≥ 2ε`. -/
def muBump (ε s : ℝ) : ℝ :=
  Real.smoothTransition (4 - 2 * s / ε)

theorem contDiff_muBump (ε : ℝ) : ContDiff ℝ ∞ (muBump ε) :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((contDiff_const.mul contDiff_id).div_const ε))

theorem continuous_muBump (ε : ℝ) : Continuous (muBump ε) :=
  (contDiff_muBump ε).continuous

theorem muBump_nonneg (ε s : ℝ) : 0 ≤ muBump ε s :=
  Real.smoothTransition.nonneg _

theorem muBump_le_one (ε s : ℝ) : muBump ε s ≤ 1 :=
  Real.smoothTransition.le_one _

theorem muBump_of_le {ε s : ℝ} (hε : 0 < ε) (hs : s ≤ 3 * ε / 2) : muBump ε s = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have : 2 * s / ε ≤ 3 := by rw [div_le_iff₀ hε]; linarith
  linarith

theorem muBump_of_ge {ε s : ℝ} (hε : 0 < ε) (hs : 2 * ε ≤ s) : muBump ε s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : 4 ≤ 2 * s / ε := by rw [le_div_iff₀ hε]; linarith
  linarith

/-- **An explicit `μ`**: `μ(r) = (3/4) ∫_r^{2ε} β(s) ds`. -/
def milnorMu (ε r : ℝ) : ℝ :=
  3 / 4 * ∫ s in r..2 * ε, muBump ε s

/-- The fundamental theorem of calculus: `μ' = -(3/4) β`. -/
theorem hasDerivAt_milnorMu (ε r : ℝ) :
    HasDerivAt (milnorMu ε) (-(3 / 4 * muBump ε r)) r := by
  have h := intervalIntegral.integral_hasDerivAt_left (b := 2 * ε)
    ((continuous_muBump ε).intervalIntegrable r (2 * ε))
    ((continuous_muBump ε).stronglyMeasurableAtFilter _ _) (continuous_muBump ε).continuousAt
  have := h.const_mul (3 / 4 : ℝ)
  rw [mul_neg] at this
  exact this

theorem deriv_milnorMu (ε : ℝ) : deriv (milnorMu ε) = fun r => -(3 / 4 * muBump ε r) :=
  funext fun r => (hasDerivAt_milnorMu ε r).deriv

theorem contDiff_milnorMu (ε : ℝ) : ContDiff ℝ ∞ (milnorMu ε) := by
  rw [contDiff_infty_iff_deriv, deriv_milnorMu]
  exact ⟨fun r => (hasDerivAt_milnorMu ε r).differentiableAt,
    (contDiff_const.mul (contDiff_muBump ε)).neg⟩

theorem milnorMu_of_ge {ε r : ℝ} (hε : 0 < ε) (hr : 2 * ε ≤ r) : milnorMu ε r = 0 := by
  have : ∫ s in r..2 * ε, muBump ε s = ∫ _ in r..2 * ε, (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_ge hr] at hs
    exact muBump_of_ge hε hs.1
  simp [milnorMu, this]

/-- `μ(0) ≥ (3/4)(3ε/2) = 9ε/8 > ε`. -/
theorem lt_milnorMu_zero {ε : ℝ} (hε : 0 < ε) : ε < milnorMu ε 0 := by
  have hi := (continuous_muBump ε).intervalIntegrable (μ := MeasureTheory.volume)
  have h1 : ∫ s in (0 : ℝ)..3 * ε / 2, muBump ε s = 3 * ε / 2 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) fun s hs => ?_]
    · simp
    · rw [uIcc_of_le (by linarith)] at hs
      exact muBump_of_le hε hs.2
  have h2 : 0 ≤ ∫ s in 3 * ε / 2..2 * ε, muBump ε s :=
    intervalIntegral.integral_nonneg (by linarith) fun s _ => muBump_nonneg ε s
  have h3 := intervalIntegral.integral_add_adjacent_intervals (hi 0 (3 * ε / 2)) (hi _ (2 * ε))
  unfold milnorMu
  rw [← h3, h1]
  nlinarith

/-- **Milnor's `μ` exists** (p. 16): `milnorMu ε` satisfies his conditions for every `ε > 0`. -/
theorem isMilnorMu_milnorMu {ε : ℝ} (hε : 0 < ε) : IsMilnorMu ε (milnorMu ε) where
  contDiff := contDiff_milnorMu ε
  lt_apply_zero := lt_milnorMu_zero hε
  eq_zero _ hr := milnorMu_of_ge hε hr
  neg_one_lt_deriv r := by
    rw [deriv_milnorMu]
    linarith [muBump_le_one ε r]
  deriv_nonpos r := by
    rw [deriv_milnorMu]
    linarith [muBump_nonneg ε r]

namespace CellModel

/-! ### Morse coordinates: `ξ`, `η`, `f` and `F` -/

section Norm

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]

/-- Milnor's `ξ = (u¹)² + ⋯ + (u^λ)²`, for `v = (x, y)`: `ξ = ‖x‖²`. -/
def xi (v : X × Y) : ℝ :=
  ‖v.1‖ ^ 2

/-- Milnor's `η = (u^{λ+1})² + ⋯ + (uⁿ)²`, for `v = (x, y)`: `η = ‖y‖²`. -/
def eta (v : X × Y) : ℝ :=
  ‖v.2‖ ^ 2

omit [NormedAddCommGroup Y] in
theorem xi_nonneg (v : X × Y) : 0 ≤ xi v :=
  sq_nonneg _

omit [NormedAddCommGroup X] in
theorem eta_nonneg (v : X × Y) : 0 ≤ eta v :=
  sq_nonneg _

omit [NormedAddCommGroup X] in
theorem eta_eq_zero_iff {v : X × Y} : eta v = 0 ↔ v.2 = 0 := by
  simp [eta]

theorem continuous_xi : Continuous (xi : X × Y → ℝ) := by
  unfold xi; fun_prop

theorem continuous_eta : Continuous (eta : X × Y → ℝ) := by
  unfold eta; fun_prop

/-- `f` in Morse coordinates: `f = c - ξ + η` (p. 15). -/
def morseQuad (c : ℝ) (v : X × Y) : ℝ :=
  c - xi v + eta v

/-- **Milnor's `F`** in Morse coordinates (p. 16): `F = c - ξ + η - μ(ξ + 2η)`. -/
def morseF (μ : ℝ → ℝ) (c : ℝ) (v : X × Y) : ℝ :=
  c - xi v + eta v - μ (xi v + 2 * eta v)

theorem morseQuad_eq_morseF (c : ℝ) : (morseQuad c : X × Y → ℝ) = morseF (fun _ => 0) c := by
  funext v
  simp [morseQuad, morseF]

/-- The ellipsoid `ξ + 2η ≤ 2ε`, outside of which `F = f`. -/
def ellipsoid (ε : ℝ) : Set (X × Y) :=
  {v | xi v + 2 * eta v ≤ 2 * ε}

/-- **Milnor's cell** `e^λ = {ξ ≤ ε, η = 0}` (p. 15). -/
def cellModel (ε : ℝ) : Set (X × Y) :=
  {v | xi v ≤ ε ∧ v.2 = 0}

/-- **Milnor's handle** `H` (p. 17): the closure of `F⁻¹(-∞, c-ε] - f⁻¹(-∞, c-ε]`. -/
def handleModel (μ : ℝ → ℝ) (c ε : ℝ) : Set (X × Y) :=
  closure (sublevel (morseF μ c) (c - ε) \ sublevel (morseQuad c) (c - ε))

theorem continuous_morseQuad (c : ℝ) : Continuous (morseQuad c : X × Y → ℝ) :=
  (continuous_const.sub continuous_xi).add continuous_eta

theorem continuous_morseF {μ : ℝ → ℝ} (hμ : Continuous μ) (c : ℝ) :
    Continuous (morseF μ c : X × Y → ℝ) :=
  ((continuous_const.sub continuous_xi).add continuous_eta).sub
    (hμ.comp (continuous_xi.add (continuous_const.mul continuous_eta)))

theorem isClosed_ellipsoid (ε : ℝ) : IsClosed (ellipsoid ε : Set (X × Y)) :=
  isClosed_le (continuous_xi.add (continuous_const.mul continuous_eta)) continuous_const

theorem ellipsoid_subset_ball (ε : ℝ) :
    (ellipsoid ε : Set (X × Y)) ⊆ {v | xi v + eta v ≤ 2 * ε} := fun v hv => by
  simp only [ellipsoid, mem_ofPred_eq] at hv ⊢
  linarith [eta_nonneg v]

theorem cellModel_subset_ellipsoid {ε : ℝ} : (cellModel ε : Set (X × Y)) ⊆ ellipsoid ε :=
  fun v hv => by
    simp only [ellipsoid, mem_ofPred_eq, eta_eq_zero_iff.2 hv.2]
    linarith [hv.1, xi_nonneg v]

variable {ε : ℝ} {μ : ℝ → ℝ}

theorem morseF_le_morseQuad (hμ : IsMilnorMu ε μ) (c : ℝ) (v : X × Y) :
    morseF μ c v ≤ morseQuad c v := by
  unfold morseF morseQuad
  linarith [hμ.nonneg (xi v + 2 * eta v)]

/-- Outside the ellipsoid `ξ + 2η ≤ 2ε`, `F = f` (p. 16). -/
theorem morseF_eq_of_notMem_ellipsoid (hμ : IsMilnorMu ε μ) (c : ℝ) {v : X × Y}
    (hv : v ∉ ellipsoid ε) : morseF μ c v = morseQuad c v := by
  unfold morseF morseQuad
  rw [hμ.eq_zero _ (le_of_lt (not_le.1 hv)), sub_zero]

/-- **Assertion 1** (p. 16) in Morse coordinates: `F ≤ c + ε ⟺ f ≤ c + ε`. Outside the
ellipsoid `F = f`; within it, `F ≤ f = c - ξ + η ≤ c + ξ/2 + η ≤ c + ε`. -/
theorem morseF_le_iff (hμ : IsMilnorMu ε μ) (c : ℝ) (v : X × Y) :
    morseF μ c v ≤ c + ε ↔ morseQuad c v ≤ c + ε := by
  by_cases hv : v ∈ ellipsoid ε
  · have h1 : morseQuad c v ≤ c + ε := by
      simp only [ellipsoid, mem_ofPred_eq] at hv
      unfold morseQuad; linarith [xi_nonneg v]
    exact ⟨fun _ => h1, fun _ => (morseF_le_morseQuad hμ c v).trans h1⟩
  · rw [morseF_eq_of_notMem_ellipsoid hμ c hv]

/-- **The cell lies below the level `c - ε` of `F`** (p. 18): on `e^λ`,
`F = c - (ξ + μ(ξ)) ≤ c - μ(0) = F(p) < c - ε`. -/
theorem morseF_lt_of_mem_cellModel (hμ : IsMilnorMu ε μ) (c : ℝ) {v : X × Y}
    (hv : v ∈ cellModel ε) : morseF μ c v < c - ε := by
  have h0 : eta v = 0 := eta_eq_zero_iff.2 hv.2
  have h1 := hμ.monotone_add (xi_nonneg v)
  simp only [zero_add] at h1
  unfold morseF
  rw [h0, mul_zero, add_zero, add_zero]
  linarith [hμ.lt_apply_zero]

/-- `e^λ ∩ M^{c-ε}` is the boundary sphere `{ξ = ε, η = 0}` of the cell (p. 16). -/
theorem cellModel_inter_sublevel (c ε : ℝ) :
    (cellModel ε : Set (X × Y)) ∩ sublevel (morseQuad c) (c - ε) = {v | xi v = ε ∧ v.2 = 0} := by
  ext v
  simp only [cellModel, mem_inter_iff, mem_ofPred_eq, mem_sublevel, morseQuad]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rw [eta_eq_zero_iff.2 h2] at h3
    exact ⟨le_antisymm h1 (by linarith), h2⟩
  · rintro ⟨h1, h2⟩
    rw [eta_eq_zero_iff.2 h2]
    exact ⟨⟨h1.le, h2⟩, by linarith⟩

/-- `F⁻¹(-∞, c-ε] = M^{c-ε} ∪ H` (p. 17). -/
theorem sublevel_morseF_eq_union (hμ : IsMilnorMu ε μ) (c : ℝ) :
    sublevel (morseF μ c : X × Y → ℝ) (c - ε) =
      sublevel (morseQuad c) (c - ε) ∪ handleModel μ c ε :=
  eq_union_closure_diff (fun v hv => (morseF_le_morseQuad hμ c v).trans hv)
    (isClosed_le (continuous_morseF hμ.continuous c) continuous_const)

end Norm

/-! ### Derivatives (Assertion 2) -/

section Deriv

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

theorem hasFDerivAt_xi (v : X × Y) :
    HasFDerivAt xi (2 • (innerSL ℝ v.1).comp (ContinuousLinearMap.fst ℝ X Y)) v :=
  (hasFDerivAt_fst (p := v)).norm_sq

theorem hasFDerivAt_eta (v : X × Y) :
    HasFDerivAt eta (2 • (innerSL ℝ v.2).comp (ContinuousLinearMap.snd ℝ X Y)) v :=
  (hasFDerivAt_snd (p := v)).norm_sq

/-- Milnor's `dF = (∂F/∂ξ) dξ + (∂F/∂η) dη` (p. 17), with `∂F/∂ξ = -1 - μ'(ξ + 2η)`,
`∂F/∂η = 1 - 2μ'(ξ + 2η)`, `dξ = 2⟨x, ·⟩`, `dη = 2⟨y, ·⟩`. -/
theorem hasFDerivAt_morseF {μ : ℝ → ℝ} (hμ : Differentiable ℝ μ) (c : ℝ) (v : X × Y) :
    HasFDerivAt (morseF μ c)
      (-(1 + deriv μ (xi v + 2 * eta v)) •
          (2 • (innerSL ℝ v.1).comp (ContinuousLinearMap.fst ℝ X Y)) +
        (1 - 2 * deriv μ (xi v + 2 * eta v)) •
          (2 • (innerSL ℝ v.2).comp (ContinuousLinearMap.snd ℝ X Y))) v := by
  have h1 := ((hasFDerivAt_const c v).sub (hasFDerivAt_xi v)).add (hasFDerivAt_eta v)
  have h2 : HasFDerivAt (fun w : X × Y => xi w + 2 * eta w) _ v :=
    (hasFDerivAt_xi v).add ((hasFDerivAt_eta v).const_mul 2)
  have h3 := (hμ (xi v + 2 * eta v)).hasDerivAt.comp_hasFDerivAt v h2
  refine (h1.sub h3).congr_fderiv ?_
  ext w <;> simp <;> ring

/-- **Assertion 2, the computation** (p. 17): if `μ` is differentiable with `-1 < μ' ≤ 0`, the
derivative of `c - ξ + η - μ(ξ + 2η)` vanishes only at the origin. -/
theorem eq_zero_of_hasFDerivAt_morseF {μ : ℝ → ℝ} (hμ : Differentiable ℝ μ)
    (h1 : ∀ r, -1 < deriv μ r) (h2 : ∀ r, deriv μ r ≤ 0) (c : ℝ) {v : X × Y}
    (hv : HasFDerivAt (morseF μ c) (0 : X × Y →L[ℝ] ℝ) v) : v = 0 := by
  have h := (hasFDerivAt_morseF hμ c v).unique hv
  have hd1 := h1 (xi v + 2 * eta v)
  have hd2 := h2 (xi v + 2 * eta v)
  have e1 := congrArg (fun L : X × Y →L[ℝ] ℝ => L (v.1, 0)) h
  have e2 := congrArg (fun L : X × Y →L[ℝ] ℝ => L (0, v.2)) h
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    innerSL_apply_apply, inner_zero_right, real_inner_self_eq_norm_sq, smul_zero,
    zero_apply, smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, zero_add,
    Nat.cast_ofNat] at e1 e2
  have hx : ‖v.1‖ ^ 2 = 0 := by
    by_contra hne
    have : 0 < ‖v.1‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
    nlinarith [mul_pos (show 0 < 1 + deriv μ (xi v + 2 * eta v) by linarith) this]
  have hy : ‖v.2‖ ^ 2 = 0 := by
    by_contra hne
    have : 0 < ‖v.2‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
    nlinarith [mul_pos (show 0 < 1 - 2 * deriv μ (xi v + 2 * eta v) by linarith) this]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    norm_eq_zero] at hx hy
  exact Prod.ext hx hy

/-- The origin is a critical point of `c - ξ + η - μ(ξ + 2η)`. -/
theorem hasFDerivAt_morseF_zero {μ : ℝ → ℝ} (hμ : Differentiable ℝ μ) (c : ℝ) :
    HasFDerivAt (morseF μ c) (0 : X × Y →L[ℝ] ℝ) 0 := by
  refine (hasFDerivAt_morseF hμ c 0).congr_fderiv ?_
  ext w <;> simp

/-- **Assertion 2** (p. 17) in Morse coordinates: the only critical point of `F` is the origin. -/
theorem hasFDerivAt_morseF_zero_iff {ε : ℝ} {μ : ℝ → ℝ} (hμ : IsMilnorMu ε μ) (c : ℝ)
    (v : X × Y) : HasFDerivAt (morseF μ c) (0 : X × Y →L[ℝ] ℝ) v ↔ v = 0 :=
  ⟨eq_zero_of_hasFDerivAt_morseF hμ.differentiable hμ.neg_one_lt_deriv hμ.deriv_nonpos c,
    fun h => h ▸ hasFDerivAt_morseF_zero hμ.differentiable c⟩

/-- The only critical point of `f = c - ξ + η` is the origin (Milnor's computation with
`μ = 0`). -/
theorem hasFDerivAt_morseQuad_zero_iff (c : ℝ) (v : X × Y) :
    HasFDerivAt (morseQuad c) (0 : X × Y →L[ℝ] ℝ) v ↔ v = 0 := by
  rw [morseQuad_eq_morseF]
  have hd : Differentiable ℝ (fun _ : ℝ => (0 : ℝ)) := differentiable_const 0
  refine ⟨eq_zero_of_hasFDerivAt_morseF hd (fun r => by simp) (fun r => by simp) c,
    fun h => h ▸ hasFDerivAt_morseF_zero hd c⟩

end Deriv

/-! ### Milnor's deformation `r_t` (Assertion 4) -/

section Retract

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The factor `σ_t(v) = 1 - t + t √(min(1, (ξ - ε)/η))` by which `r_t` shrinks `y`; in Case 2
it is Milnor's `s_t` (with `t` replaced by `1 - t`). -/
def retractScale (ε t : ℝ) (v : X × Y) : ℝ :=
  1 - t + t * Real.sqrt (min 1 ((xi v - ε) / eta v))

/-- **Milnor's deformation `r_t`** (pp. 18–19), his three cases in one formula:
`r_t(x, y) = (x, σ_t(x, y) y)`. Here `r_0 = id`; Milnor's `r_t` is our `r_{1-t}`. -/
def retractModel (ε t : ℝ) (v : X × Y) : X × Y :=
  (v.1, retractScale ε t v • v.2)

variable {ε t : ℝ} {v : X × Y}

omit [NormedSpace ℝ Y] in
theorem retractScale_zero (ε : ℝ) (v : X × Y) : retractScale ε 0 v = 1 := by
  simp [retractScale]

omit [NormedSpace ℝ Y] in
theorem retractScale_nonneg (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ retractScale ε t v := by
  unfold retractScale
  have := Real.sqrt_nonneg (min 1 ((xi v - ε) / eta v))
  nlinarith [ht.1, ht.2]

omit [NormedSpace ℝ Y] in
theorem retractScale_le_one (ht : t ∈ Icc (0 : ℝ) 1) : retractScale ε t v ≤ 1 := by
  unfold retractScale
  have h : Real.sqrt (min 1 ((xi v - ε) / eta v)) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact min_le_left _ _
  nlinarith [ht.1, ht.2]

omit [NormedSpace ℝ Y] in
theorem abs_retractScale_le_one (ht : t ∈ Icc (0 : ℝ) 1) : |retractScale ε t v| ≤ 1 := by
  rw [abs_of_nonneg (retractScale_nonneg ht)]
  exact retractScale_le_one ht

/-- `r_0 = id`. -/
theorem retractModel_zero (ε : ℝ) (v : X × Y) : retractModel ε 0 v = v := by
  simp [retractModel, retractScale_zero]

theorem xi_retractModel (ε t : ℝ) (v : X × Y) : xi (retractModel ε t v) = xi v :=
  rfl

theorem eta_retractModel (ε t : ℝ) (v : X × Y) :
    eta (retractModel ε t v) = retractScale ε t v ^ 2 * eta v := by
  simp only [eta, retractModel, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- `r_t` does not increase `η` (for `0 ≤ t ≤ 1`). -/
theorem eta_retractModel_le (ht : t ∈ Icc (0 : ℝ) 1) : eta (retractModel ε t v) ≤ eta v := by
  rw [eta_retractModel]
  have h0 := retractScale_nonneg (ε := ε) (v := v) ht
  have h1 := retractScale_le_one (ε := ε) (v := v) ht
  have : retractScale ε t v ^ 2 ≤ 1 := by nlinarith
  nlinarith [eta_nonneg v]

theorem retractModel_of_snd_eq_zero (ε t : ℝ) (hv : v.2 = 0) : retractModel ε t v = v :=
  Prod.ext rfl (by simp [retractModel, hv])

/-- **Case 1** (`ξ ≤ ε`, p. 18): `r_t(x, y) = (x, (1 - t) y)`. -/
theorem retractModel_of_xi_le (t : ℝ) (h : xi v ≤ ε) :
    retractModel ε t v = (v.1, (1 - t) • v.2) := by
  rcases (eta_nonneg v).eq_or_lt with h0 | h0
  · have hv : v.2 = 0 := eta_eq_zero_iff.1 h0.symm
    simp [retractModel, hv]
  · have : Real.sqrt (min 1 ((xi v - ε) / eta v)) = 0 := by
      refine Real.sqrt_eq_zero'.2 ((min_le_right _ _).trans ?_)
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) h0.le
    simp [retractModel, retractScale, this]

/-- **Case 2** (`ε ≤ ξ ≤ η + ε`, p. 19): `r_t(x, y) = (x, s y)` with
`s = 1 - t + t ((ξ - ε)/η)^{1/2}`, where `η > 0` (Milnor's formula is not defined at `η = 0`).
The hypothesis `ε ≤ ξ` is not needed: for `ξ < ε` this is Case 1, since Mathlib's square root of
a negative number is `0`. -/
theorem retractModel_of_case2 (t : ℝ) (h : xi v ≤ eta v + ε) (h0 : 0 < eta v) :
    retractModel ε t v = (v.1, (1 - t + t * Real.sqrt ((xi v - ε) / eta v)) • v.2) := by
  have : min 1 ((xi v - ε) / eta v) = (xi v - ε) / eta v :=
    min_eq_right ((div_le_one h0).2 (by linarith))
  simp [retractModel, retractScale, this]

/-- **Case 3** (`η + ε ≤ ξ`, i.e. `M^{c-ε}`, p. 19): `r_t` is the identity. -/
theorem retractModel_of_le_xi (t : ℝ) (h : eta v + ε ≤ xi v) : retractModel ε t v = v := by
  rcases (eta_nonneg v).eq_or_lt with h0 | h0
  · exact retractModel_of_snd_eq_zero ε t (eta_eq_zero_iff.1 h0.symm)
  · have : min 1 ((xi v - ε) / eta v) = 1 :=
      min_eq_left ((one_le_div h0).2 (by linarith))
    simp [retractModel, retractScale, this]

/-- `r_t` fixes `M^{c-ε}` pointwise. -/
theorem retractModel_of_morseQuad_le {c : ℝ} (t : ℝ) (h : morseQuad c v ≤ c - ε) :
    retractModel ε t v = v :=
  retractModel_of_le_xi t (by unfold morseQuad at h; linarith)

/-- `r_t` fixes `e^λ` pointwise. -/
theorem retractModel_of_mem_cellModel (t : ℝ) (h : v ∈ cellModel ε) : retractModel ε t v = v :=
  retractModel_of_snd_eq_zero ε t h.2

/-- **`r_1` lands in `M^{c-ε} ∪ e^λ`** (p. 19): Case 1 goes into `e^λ`, Case 2 into the
hypersurface `f⁻¹(c - ε)`, Case 3 is already in `M^{c-ε}`. -/
theorem retractModel_one_mem (c : ℝ) (v : X × Y) :
    retractModel ε 1 v ∈ sublevel (morseQuad c) (c - ε) ∪ cellModel ε := by
  rcases le_total (xi v) ε with h1 | h1
  · right
    rw [retractModel_of_xi_le 1 h1]
    exact ⟨h1, by simp⟩
  · left
    rw [mem_sublevel]
    rcases le_total (xi v) (eta v + ε) with h2 | h2
    · rcases (eta_nonneg v).eq_or_lt with h0 | h0
      · rw [retractModel_of_snd_eq_zero ε 1 (eta_eq_zero_iff.1 h0.symm)]
        unfold morseQuad; linarith
      · have hr : eta (retractModel ε 1 v) = xi v - ε := by
          rw [eta_retractModel]
          have : min 1 ((xi v - ε) / eta v) = (xi v - ε) / eta v :=
            min_eq_right ((div_le_one h0).2 (by linarith))
          simp only [retractScale, this, sub_self, one_mul, zero_add]
          rw [Real.sq_sqrt (div_nonneg (by linarith) h0.le), div_mul_cancel₀ _ h0.ne']
        unfold morseQuad
        rw [xi_retractModel, hr]
        linarith
    · rw [retractModel_of_le_xi 1 h2]
      unfold morseQuad; linarith

/-- `r_t` keeps the ellipsoid `ξ + 2η ≤ 2ε` in itself. -/
theorem retractModel_mem_ellipsoid {δ : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hv : v ∈ ellipsoid ε) :
    retractModel δ t v ∈ ellipsoid ε := by
  simp only [ellipsoid, mem_ofPred_eq, xi_retractModel] at hv ⊢
  linarith [eta_retractModel_le (ε := δ) (v := v) ht]

/-- **The continuity of `r_t`** (p. 19, "the reader should verify"): `(t, v) ↦ r_t(v)` is
continuous on `[0, 1] × X × Y`. Where `η ≠ 0` the formula is continuous; at a point `(x₀, 0)`,
`0 ≤ σ_t ≤ 1` gives `‖r_t(v) - (x₀, 0)‖ ≤ ‖v - (x₀, 0)‖`. -/
theorem continuous_retractModel (ε : ℝ) :
    Continuous fun p : I × (X × Y) => retractModel ε p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, v₀⟩
  by_cases h0 : eta v₀ = 0
  · have hv₀ : v₀.2 = 0 := eta_eq_zero_iff.1 h0
    have hr₀ : retractModel ε t₀ v₀ = v₀ := retractModel_of_snd_eq_zero ε t₀ hv₀
    rw [ContinuousAt, hr₀, Metric.tendsto_nhds_nhds]
    intro δ hδ
    refine ⟨δ, hδ, fun p hp => lt_of_le_of_lt ?_ hp⟩
    have hs := abs_retractScale_le_one (ε := ε) (v := p.2) p.1.2
    have key : dist (retractModel ε p.1 p.2) v₀ ≤ dist p.2 v₀ := by
      rw [Prod.dist_eq, Prod.dist_eq]
      refine max_le_max le_rfl ?_
      simp only [retractModel, hv₀, dist_zero_right, norm_smul, Real.norm_eq_abs]
      calc |retractScale ε p.1 p.2| * ‖p.2.2‖ ≤ 1 * ‖p.2.2‖ := by gcongr
        _ = ‖p.2.2‖ := one_mul _
    exact key.trans (by rw [Prod.dist_eq (x := p)]; exact le_max_right _ _)
  · have hd : ContinuousAt (fun p : I × (X × Y) => (xi p.2 - ε) / eta p.2) (t₀, v₀) :=
      ((continuous_xi.comp continuous_snd).sub continuous_const).continuousAt.div
        (continuous_eta.comp continuous_snd).continuousAt h0
    have ht : Continuous fun p : I × (X × Y) => (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hs : ContinuousAt (fun p : I × (X × Y) => retractScale ε p.1 p.2) (t₀, v₀) :=
      (continuous_const.sub ht).continuousAt.add
        (ht.continuousAt.mul (Real.continuous_sqrt.continuousAt.comp
          (continuous_const.continuousAt.min hd)))
    exact (continuous_fst.comp continuous_snd).continuousAt.prodMk
      (hs.smul (continuous_snd.comp continuous_snd).continuousAt)

variable {μ : ℝ → ℝ}

/-- **`r_t` maps `F⁻¹(-∞, c-ε]` into itself** (p. 19): `r_t` keeps `ξ`, does not increase `η`,
and `F` increases with `η` (`∂F/∂η ≥ 1`). -/
theorem morseF_retractModel_le (hμ : IsMilnorMu ε μ) (c : ℝ) {δ : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (v : X × Y) : morseF μ c (retractModel δ t v) ≤ morseF μ c v := by
  have he := eta_retractModel_le (ε := δ) (v := v) ht
  have hμle := hμ.antitone
    (show xi v + 2 * eta (retractModel δ t v) ≤ xi v + 2 * eta v by linarith)
  unfold morseF
  rw [xi_retractModel]
  linarith

/-- On `F⁻¹(-∞, c-ε]`, `r_t` moves only points of the ellipsoid `ξ + 2η ≤ 2ε`: outside it
`F = f ≤ c - ε`, which is Case 3. (Stated for the deformation `r_t` built with any level `δ` in
place of `ε`, as used for Remark 3.4 with `δ = 0`.) -/
theorem retractModel_of_notMem_ellipsoid (hμ : IsMilnorMu ε μ) {c δ : ℝ} (t : ℝ)
    (hv : morseF μ c v ≤ c - δ) (hE : v ∉ ellipsoid ε) : retractModel δ t v = v :=
  retractModel_of_morseQuad_le t (morseF_eq_of_notMem_ellipsoid hμ c hE ▸ hv)

end Retract

/-! ### The cell lies in the handle -/

section Handle

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  {ε : ℝ} {μ : ℝ → ℝ}

omit [NormedSpace ℝ X] in
/-- The points of the cell with `ξ < ε` lie in `F⁻¹(-∞, c-ε] - M^{c-ε}` (p. 18: `F(q) < c - ε`
but `f(q) > c - ε`). -/
theorem mem_diff_of_mem_cellModel (hμ : IsMilnorMu ε μ) (c : ℝ) {v : X × Y}
    (hv : v ∈ cellModel ε) (h : xi v < ε) :
    v ∈ sublevel (morseF μ c) (c - ε) \ sublevel (morseQuad c) (c - ε) := by
  refine ⟨(morseF_lt_of_mem_cellModel hμ c hv).le, fun h' => ?_⟩
  have h'' : morseQuad c v ≤ c - ε := h'
  simp only [morseQuad, eta_eq_zero_iff.2 hv.2] at h''
  linarith

/-- Every point `(x, 0)` of the cell is the limit, as `s → 1⁻`, of the points `(s x, 0)` of the
cell with `ξ < ε`. -/
theorem tendsto_smul_cellModel (hε : 0 < ε) {v : X × Y}
    (hv : v ∈ cellModel ε) :
    Tendsto (fun s : ℝ => ((s • v.1, (0 : Y)) : X × Y)) (𝓝[<] 1) (𝓝 v) ∧
      ∀ᶠ s in 𝓝[<] (1 : ℝ), ((s • v.1, (0 : Y)) : X × Y) ∈ cellModel ε ∧
        xi ((s • v.1, (0 : Y)) : X × Y) < ε := by
  refine ⟨?_, ?_⟩
  · have h : Continuous fun s : ℝ => ((s • v.1, (0 : Y)) : X × Y) := by fun_prop
    have h1 := h.tendsto 1
    rw [one_smul, show ((v.1, (0 : Y)) : X × Y) = v from Prod.ext rfl hv.2.symm] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
    have hs2 : s ^ 2 < 1 := by nlinarith [hs.1, hs.2]
    have hx : ‖v.1‖ ^ 2 ≤ ε := hv.1
    have h1 : s ^ 2 * ‖v.1‖ ^ 2 ≤ s ^ 2 * ε := mul_le_mul_of_nonneg_left hx (sq_nonneg s)
    have h2 : s ^ 2 * ε < ε := by nlinarith [mul_pos (sub_pos.2 hs2) hε]
    have hxi : xi ((s • v.1, (0 : Y)) : X × Y) = s ^ 2 * ‖v.1‖ ^ 2 := by
      simp only [xi, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact ⟨⟨by rw [hxi]; linarith, rfl⟩, by rw [hxi]; linarith⟩

/-- **`e^λ ⊆ H`** (p. 18): the cell is contained in the handle. -/
theorem cellModel_subset_handleModel (hμ : IsMilnorMu ε μ) (hε : 0 < ε) (c : ℝ) :
    (cellModel ε : Set (X × Y)) ⊆ handleModel μ c ε := fun _ hv =>
  have h := tendsto_smul_cellModel hε hv
  mem_closure_of_tendsto h.1 (h.2.mono fun _ hs => mem_diff_of_mem_cellModel hμ c hs.1 hs.2)

end Handle

/-! ### Assertion 4 in the model -/

section Assertion4

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {ε : ℝ} {μ : ℝ → ℝ}

/-- `r_t` maps each sublevel set of `F` into itself, as a statement about the subtype. -/
theorem retractModel_mem_sublevel (hμ : IsMilnorMu ε μ) (c a δ : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (v : sublevel (morseF μ c : X × Y → ℝ) a) :
    retractModel δ t (v : X × Y) ∈ sublevel (morseF μ c : X × Y → ℝ) a := by
  have h1 := morseF_retractModel_le hμ c (δ := δ) ht (v : X × Y)
  have h2 : morseF μ c (v : X × Y) ≤ a := v.2
  exact h1.trans h2

/-- Milnor's retraction `r_1` (his `r_0`) of `F⁻¹(-∞, c-ε]` onto `M^{c-ε} ∪ e^λ`. -/
def retractOne (hμ : IsMilnorMu ε μ) (c : ℝ) :
    C(sublevel (morseF μ c : X × Y → ℝ) (c - ε), sublevel (morseF μ c : X × Y → ℝ) (c - ε)) where
  toFun v := ⟨retractModel ε 1 v, retractModel_mem_sublevel hμ c _ ε ⟨zero_le_one, le_rfl⟩ v⟩
  continuous_toFun := ((continuous_retractModel ε).comp
    ((continuous_const : Continuous fun _ : sublevel (morseF μ c : X × Y → ℝ) (c - ε) =>
      (1 : I)).prodMk continuous_subtype_val)).subtype_mk _

/-- **Milnor's deformation retraction** (Assertion 4, p. 18): `r_t`, `0 ≤ t ≤ 1`, as a homotopy
of `F⁻¹(-∞, c-ε]` from the identity to `r_1`, fixing `M^{c-ε} ∪ e^λ` pointwise. -/
def retractHomotopy (hμ : IsMilnorMu ε μ) (c : ℝ) :
    (ContinuousMap.id (sublevel (morseF μ c : X × Y → ℝ) (c - ε))).HomotopyRel (retractOne hμ c)
      ((↑) ⁻¹' (sublevel (morseQuad c : X × Y → ℝ) (c - ε) ∪ cellModel ε) :
        Set (sublevel (morseF μ c : X × Y → ℝ) (c - ε))) where
  toFun p := ⟨retractModel ε p.1 p.2, retractModel_mem_sublevel hμ c _ ε p.1.2 p.2⟩
  continuous_toFun := ((continuous_retractModel ε).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left v := Subtype.ext (retractModel_zero ε (v : X × Y))
  map_one_left _ := rfl
  prop' t v hv := Subtype.ext <| by
    rcases hv with hv | hv
    · exact retractModel_of_morseQuad_le _ hv
    · exact retractModel_of_mem_cellModel _ hv

/-- **Assertion 4 in Morse coordinates** (p. 18): `M^{c-ε} ∪ e^λ` is a strong deformation retract
of `F⁻¹(-∞, c-ε] = M^{c-ε} ∪ H`. -/
theorem isStrongDeformationRetract_model (hμ : IsMilnorMu ε μ) (c : ℝ) :
    IsStrongDeformationRetract
      ((↑) ⁻¹' (sublevel (morseQuad c : X × Y → ℝ) (c - ε) ∪ cellModel ε) :
        Set (sublevel (morseF μ c : X × Y → ℝ) (c - ε))) :=
  ⟨retractOne hμ c, fun v => retractModel_one_mem c (v : X × Y), ⟨retractHomotopy hμ c⟩⟩

end Assertion4

/-! ### Remark 3.4 in the model -/

section Level

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {ε : ℝ} {μ : ℝ → ℝ}

/-- **The "simple modification" for Remark 3.4** (p. 20, Diagram 8) is `r_t` with `ε` replaced
by `0`: `(x, y) ↦ (x, s y)` with `s = 1 - t + t (ξ/η)^{1/2}` where `ξ ≤ η`, the identity where
`η ≤ ξ` (i.e. on `M^c`). Its `r_1` maps everything into `M^c`. -/
theorem morseQuad_retractModel_zero_one_le (c : ℝ) (v : X × Y) :
    morseQuad c (retractModel 0 1 v) ≤ c := by
  rcases retractModel_one_mem (ε := 0) c v with h | h
  · simpa using h
  · have h1 : xi (retractModel 0 1 v) ≤ 0 := h.1
    have h2 := eta_eq_zero_iff.2 h.2
    unfold morseQuad
    linarith [xi_nonneg (retractModel 0 1 v)]

/-- The retraction `r_1` of `F⁻¹(-∞, c]` onto `M^c`. -/
def levelRetractOne (hμ : IsMilnorMu ε μ) (c : ℝ) :
    C(sublevel (morseF μ c : X × Y → ℝ) c, sublevel (morseF μ c : X × Y → ℝ) c) where
  toFun v := ⟨retractModel 0 1 v, retractModel_mem_sublevel hμ c _ 0 ⟨zero_le_one, le_rfl⟩ v⟩
  continuous_toFun := ((continuous_retractModel 0).comp
    ((continuous_const : Continuous fun _ : sublevel (morseF μ c : X × Y → ℝ) c =>
      (1 : I)).prodMk continuous_subtype_val)).subtype_mk _

/-- The deformation of `F⁻¹(-∞, c]` onto `M^c`, fixing `M^c` pointwise. -/
def levelHomotopy (hμ : IsMilnorMu ε μ) (c : ℝ) :
    (ContinuousMap.id (sublevel (morseF μ c : X × Y → ℝ) c)).HomotopyRel (levelRetractOne hμ c)
      ((↑) ⁻¹' sublevel (morseQuad c : X × Y → ℝ) c :
        Set (sublevel (morseF μ c : X × Y → ℝ) c)) where
  toFun p := ⟨retractModel 0 p.1 p.2, retractModel_mem_sublevel hμ c _ 0 p.1.2 p.2⟩
  continuous_toFun := ((continuous_retractModel 0).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left v := Subtype.ext (retractModel_zero 0 (v : X × Y))
  map_one_left _ := rfl
  prop' t v hv := Subtype.ext <|
    retractModel_of_morseQuad_le (ε := 0) (c := c) _ (by rw [sub_zero]; exact hv)

/-- **Remark 3.4 in Morse coordinates** (p. 20): `M^c` is a strong deformation retract of
`F⁻¹(-∞, c]`. -/
theorem isStrongDeformationRetract_model_level (hμ : IsMilnorMu ε μ) (c : ℝ) :
    IsStrongDeformationRetract
      ((↑) ⁻¹' sublevel (morseQuad c : X × Y → ℝ) c :
        Set (sublevel (morseF μ c : X × Y → ℝ) c)) :=
  ⟨levelRetractOne hμ c, fun v => morseQuad_retractModel_zero_one_le c (v : X × Y),
    ⟨levelHomotopy hμ c⟩⟩

end Level

end CellModel

end Morse
