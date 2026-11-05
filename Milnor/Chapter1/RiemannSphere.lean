import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §1, p. 8: "For the proof it is first necessary
to pass from the plane of complex numbers to a compact manifold."

# The Riemann sphere `ℂ ∪ {∞}` as a smooth manifold

Milnor uses the unit sphere `S² ⊂ ℝ³` together with stereographic projection `h₊` from the north
pole to transport a polynomial map `P : ℂ → ℂ` to a smooth map `f : S² → S²`. The only properties
of `S²` that his argument uses are:

* `S²` is a compact smooth 2-manifold;
* `S² ∖ {north pole}` is diffeomorphic to `ℂ` via `h₊`;
* near the north pole, the chart `h₋` (projection from the south pole) satisfies
  `h₊ h₋⁻¹(z) = 1/z̄`, so that `f` written in the chart `h₋` at both ends is
  `Q(z) = zⁿ / (ā₀ + ā₁ z + ⋯ + āₙ zⁿ)`.

We use instead the one-point compactification `ℂ ∪ {∞}` (Mathlib's `OnePoint ℂ`) with the two
charts `z ↦ z` on `ℂ` and `z ↦ 1/z` on `(ℂ ∪ {∞}) ∖ {0}`. This is the same manifold (the
stereographic projection `h₊` extends to a diffeomorphism `S² ≃ ℂ ∪ {∞}`), and it removes the
complex conjugation from Milnor's formula: `f` written in the chart `1/z` at both ends is exactly
`Q(w) = wⁿ / (a₀ + a₁ w + ⋯ + aₙ wⁿ)` with the *original* coefficients, i.e. `wⁿ / P̃(w)` where
`P̃` is the reversed polynomial. See `Milnor.Chapter1.FTA`.

This file constructs the smooth structure. The manifold is modelled on `ℂ` viewed as a real
normed space, so it is a real 2-manifold, as in Milnor.
-/

open Filter Topology Set Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

namespace RiemannSphere

/-- The point at infinity of `ℂ ∪ {∞}`. -/
local notation "∞'" => (OnePoint.infty : OnePoint ℂ)

/-! ### Inversion `z ↦ 1/z` on `ℂ ∪ {∞}` -/

/-- Inversion `z ↦ 1/z` on the Riemann sphere, exchanging `0` and `∞`. -/
def invert : OnePoint ℂ → OnePoint ℂ := fun p =>
  p.elim ((0 : ℂ) : OnePoint ℂ) fun z => if z = 0 then ∞' else ((z⁻¹ : ℂ) : OnePoint ℂ)

@[simp] theorem invert_infty : invert ∞' = ((0 : ℂ) : OnePoint ℂ) := rfl

@[simp] theorem invert_coe_zero : invert ((0 : ℂ) : OnePoint ℂ) = ∞' := by
  simp [invert]

theorem invert_coe_of_ne {z : ℂ} (hz : z ≠ 0) :
    invert (z : OnePoint ℂ) = ((z⁻¹ : ℂ) : OnePoint ℂ) := by
  simp [invert, hz]

theorem invert_invert (p : OnePoint ℂ) : invert (invert p) = p := by
  induction p using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · subst hz; simp
    · rw [invert_coe_of_ne hz, invert_coe_of_ne (inv_ne_zero hz), inv_inv]

theorem invert_eq_infty_iff {p : OnePoint ℂ} : invert p = ∞' ↔ p = ((0 : ℂ) : OnePoint ℂ) := by
  induction p using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · subst hz; simp
    · rw [invert_coe_of_ne hz]
      simp [hz]

theorem tendsto_inv_cocompact : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  have h' := h.inv_tendsto_atTop
  refine h'.congr fun z => ?_
  simp [Pi.inv_apply, norm_inv]

theorem tendsto_inv_nhdsNE_zero : Tendsto (fun z : ℂ => z⁻¹) (𝓝[≠] 0) (cocompact ℂ) :=
  tendsto_cocompact_of_tendsto_dist_comp_atTop 0
    (by simpa [dist_zero_right] using tendsto_norm_inv_nhdsNE_zero_atTop (α := ℂ))

theorem continuous_invert : Continuous invert := by
  rw [OnePoint.continuous_iff]
  constructor
  · -- Continuity at `∞`: `1/z → 0` as `z → ∞`.
    rw [coclosedCompact_eq_cocompact]
    have h : (fun z : ℂ => invert (z : OnePoint ℂ)) =ᶠ[cocompact ℂ]
        fun z : ℂ => ((z⁻¹ : ℂ) : OnePoint ℂ) := by
      filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with z hz
      exact invert_coe_of_ne fun h => hz (by simp [h])
    refine Tendsto.congr' h.symm ?_
    rw [invert_infty]
    exact (OnePoint.continuous_coe.tendsto 0).comp tendsto_inv_cocompact
  · -- Continuity on `ℂ`.
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = 0
    · -- At `0`: `1/z → ∞` as `z → 0`.
      subst hz
      rw [ContinuousAt, invert_coe_zero, ← nhdsNE_sup_pure (0 : ℂ), tendsto_sup]
      constructor
      · have h : (fun w : ℂ => invert (w : OnePoint ℂ)) =ᶠ[𝓝[≠] (0 : ℂ)]
            fun w : ℂ => ((w⁻¹ : ℂ) : OnePoint ℂ) := by
          filter_upwards [self_mem_nhdsWithin] with w hw
          exact invert_coe_of_ne fun h => hw (by simp [h])
        refine Tendsto.congr' h.symm ?_
        refine OnePoint.tendsto_coe_infty.comp ?_
        rw [coclosedCompact_eq_cocompact]
        exact tendsto_inv_nhdsNE_zero
      · have := tendsto_pure_nhds (fun w : ℂ => invert (w : OnePoint ℂ)) 0
        rwa [invert_coe_zero] at this
    · -- Away from `0`: `1/z` is continuous.
      have h : (fun w : ℂ => invert (w : OnePoint ℂ)) =ᶠ[𝓝 z]
          fun w : ℂ => ((w⁻¹ : ℂ) : OnePoint ℂ) := by
        filter_upwards [(isOpen_ne (x := (0 : ℂ))).mem_nhds hz] with w hw
        exact invert_coe_of_ne hw
      refine ContinuousAt.congr ?_ h.symm
      exact OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)

/-- Inversion as a homeomorphism of the Riemann sphere. -/
def invertHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ where
  toFun := invert
  invFun := invert
  left_inv := invert_invert
  right_inv := invert_invert
  continuous_toFun := continuous_invert
  continuous_invFun := continuous_invert

/-! ### The two charts -/

/-- The chart `z ↦ z` on `ℂ ⊂ ℂ ∪ {∞}`. -/
def chart₀ : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : ℂ → OnePoint ℂ)).symm

@[simp] theorem chart₀_source : chart₀.source = {∞'}ᶜ := by
  simp [chart₀, OnePoint.compl_infty]

@[simp] theorem chart₀_target : chart₀.target = univ := by
  simp [chart₀]

@[simp] theorem chart₀_symm_apply (z : ℂ) : chart₀.symm z = (z : OnePoint ℂ) := by
  simp [chart₀]

@[simp] theorem chart₀_coe (z : ℂ) : chart₀ (z : OnePoint ℂ) = z :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_left_inv

/-- The chart `z ↦ 1/z` on `(ℂ ∪ {∞}) ∖ {0}`, sending `∞` to `0`. -/
def chartInf : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  invertHomeomorph.toOpenPartialHomeomorph.trans chart₀

@[simp] theorem chartInf_apply (p : OnePoint ℂ) : chartInf p = chart₀ (invert p) := rfl

@[simp] theorem chartInf_symm_apply (z : ℂ) : chartInf.symm z = invert (z : OnePoint ℂ) := by
  simp [chartInf, OpenPartialHomeomorph.coe_trans_symm, invertHomeomorph]

@[simp] theorem chartInf_source : chartInf.source = {((0 : ℂ) : OnePoint ℂ)}ᶜ := by
  ext p
  simp [chartInf, OpenPartialHomeomorph.trans_source, invertHomeomorph, invert_eq_infty_iff]

@[simp] theorem chartInf_infty : chartInf ∞' = 0 := by simp

theorem chartInf_coe_of_ne {z : ℂ} (hz : z ≠ 0) : chartInf (z : OnePoint ℂ) = z⁻¹ := by
  simp [invert_coe_of_ne hz]

/-! ### The charted space and manifold structure -/

open Classical in
instance instChartedSpace : ChartedSpace ℂ (OnePoint ℂ) where
  atlas := {chart₀, chartInf}
  chartAt p := if p = ∞' then chartInf else chart₀
  mem_chart_source p := by
    induction p using OnePoint.rec with
    | infty => simp
    | coe z => simp [OnePoint.coe_ne_infty]
  chart_mem_atlas p := by
    split_ifs <;> simp

open Classical in
theorem chartAt_infty : chartAt ℂ ∞' = chartInf := by
  show (if ∞' = ∞' then chartInf else chart₀) = chartInf
  exact if_pos rfl

open Classical in
theorem chartAt_coe (z : ℂ) : chartAt ℂ (z : OnePoint ℂ) = chart₀ := by
  show (if (z : OnePoint ℂ) = ∞' then chartInf else chart₀) = chart₀
  exact if_neg (OnePoint.coe_ne_infty z)

theorem mem_atlas_iff (e : OpenPartialHomeomorph (OnePoint ℂ) ℂ) :
    e ∈ atlas ℂ (OnePoint ℂ) ↔ e = chart₀ ∨ e = chartInf := by
  simp [atlas, ChartedSpace.atlas, instChartedSpace]

/-- The Riemann sphere is a smooth (real, 2-dimensional) manifold: the transition map between the
two charts is `z ↦ 1/z` on `ℂ ∖ {0}`, which is smooth. -/
instance instIsManifold : IsManifold 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) (OnePoint ℂ) :=
  isManifold_of_contDiffOn 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) (OnePoint ℂ) (by
    intro e e' he he'
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
      Set.inter_univ, Set.preimage_id_eq, id_eq, CompTriple.comp_eq, Function.comp_id,
      Function.id_comp]
    rw [mem_atlas_iff] at he he'
    -- In all four cases the transition map is `id` or `z ↦ z⁻¹` on a set avoiding `0`.
    have hinv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z⁻¹) {0}ᶜ := contDiffOn_inv ℝ
    rcases he with rfl | rfl <;> rcases he' with rfl | rfl
    · refine contDiffOn_id.congr fun z hz => ?_
      simp
    · refine (hinv.mono ?_).congr fun z hz => ?_
      · intro z hz
        rw [OpenPartialHomeomorph.trans_source] at hz
        simpa using hz.2
      · simp only [OpenPartialHomeomorph.trans_apply, chart₀_symm_apply]
        rw [OpenPartialHomeomorph.trans_source] at hz
        have hz0 : z ≠ 0 := by simpa using hz.2
        exact chartInf_coe_of_ne hz0
    · refine (hinv.mono ?_).congr fun z hz => ?_
      · intro z hz
        rw [OpenPartialHomeomorph.trans_source] at hz
        have := hz.2
        simp only [OpenPartialHomeomorph.symm_source, chartInf_symm_apply, mem_preimage,
          chart₀_source, mem_compl_iff, mem_singleton_iff, invert_eq_infty_iff,
          OnePoint.coe_eq_coe] at this
        exact this
      · simp only [OpenPartialHomeomorph.trans_apply, chartInf_symm_apply]
        rw [OpenPartialHomeomorph.trans_source] at hz
        have hz0 : z ≠ 0 := by
          have := hz.2
          simpa [invert_eq_infty_iff] using this
        rw [invert_coe_of_ne hz0, chart₀_coe]
    · refine contDiffOn_id.congr fun z hz => ?_
      simp [invert_invert])

end RiemannSphere

end Milnor
