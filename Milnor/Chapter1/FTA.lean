import Milnor.Chapter1.Counting
import Milnor.Chapter1.RiemannSphere
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Topology.Algebra.Polynomial

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §1, pp. 8–9.

# The fundamental theorem of algebra

Milnor's proof, with the sphere `S²` replaced by the Riemann sphere `ℂ ∪ {∞}`
(see `Milnor.Chapter1.RiemannSphere` for why this is harmless):

1. A nonconstant polynomial `P` extends to a map `f : ℂ ∪ {∞} → ℂ ∪ {∞}` with `f(∞) = ∞`
   (`polyMap`). It is smooth: away from `∞` it is `P` itself, and near `∞`, read in the chart
   `w = 1/z` at both ends, it is `Q(w) = wⁿ / P̃(w)` where `P̃` is the reversed polynomial, whose
   constant term is the leading coefficient of `P` (`contMDiff_polyMap`).
2. `f` has only finitely many critical values: the images of the zeros of `P'`, together with `∞`
   (`critVals`, `critVals_finite`, `isRegularValue_of_notMem_critVals`).
3. The complement of a finite set in `ℂ ∪ {∞}` is connected (`isPreconnected_compl_critVals`).
4. Some regular value is in the image of `f` (`exists_regularValue_mem_range`), because `P` takes
   infinitely many values and there are only finitely many critical values.
5. By the counting argument (`Milnor.subset_range_of_isPreconnected`), every regular value is in
   the image of `f`; critical values are in the image by definition; so `f` is onto and in
   particular `0 = f(z)` for some `z ∈ ℂ`, i.e. `P(z) = 0`.
-/

open Filter Topology Set Function Polynomial Module
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

namespace RiemannSphere

local notation "∞'" => (OnePoint.infty : OnePoint ℂ)

/-! ### Polynomials are smooth (over `ℝ` and over `ℂ`) -/

theorem contDiff_eval (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] (P : ℂ[X]) :
    ContDiff 𝕜 ∞ (fun z : ℂ => P.eval z) := by
  induction P using Polynomial.induction_on' with
  | add f g hf hg => simpa [eval_add] using hf.add hg
  | monomial n a => simpa [eval_monomial] using contDiff_const.mul (contDiff_id.pow _)

/-! ### The polynomial map on the Riemann sphere -/

variable (P : ℂ[X])

/-- The polynomial `P` extended to the Riemann sphere by `P(∞) = ∞`. -/
def polyMap : OnePoint ℂ → OnePoint ℂ := fun p =>
  p.elim ∞' fun z => ((P.eval z : ℂ) : OnePoint ℂ)

@[simp] theorem polyMap_infty : polyMap P ∞' = ∞' := rfl

@[simp] theorem polyMap_coe (z : ℂ) : polyMap P (z : OnePoint ℂ) = ((P.eval z : ℂ) : OnePoint ℂ) :=
  rfl

variable {P}

theorem ne_zero_of_degree_pos (hP : 0 < P.degree) : P ≠ 0 := by
  rintro rfl
  simp at hP

theorem natDegree_pos (hP : 0 < P.degree) : 0 < P.natDegree :=
  natDegree_pos_iff_degree_pos.2 hP

/-! ### Continuity -/

theorem continuousAt_polyMap_coe (z : ℂ) : ContinuousAt (polyMap P) (z : OnePoint ℂ) := by
  rw [OnePoint.continuousAt_coe]
  exact OnePoint.continuous_coe.continuousAt.comp P.continuous.continuousAt

theorem continuousAt_polyMap_infty (hP : 0 < P.degree) : ContinuousAt (polyMap P) ∞' := by
  rw [OnePoint.continuousAt_infty', polyMap_infty, coclosedCompact_eq_cocompact]
  refine OnePoint.tendsto_coe_infty.comp ?_
  rw [coclosedCompact_eq_cocompact]
  refine tendsto_cocompact_of_tendsto_dist_comp_atTop 0 ?_
  simpa [dist_zero_right] using
    Polynomial.tendsto_norm_atTop P hP (tendsto_norm_cocompact_atTop (E := ℂ))

/-! ### Smoothness -/

/-- Away from `∞`, `polyMap P` read in the charts is just `P`. -/
theorem contMDiffAt_polyMap_coe (z : ℂ) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (polyMap P) (z : OnePoint ℂ) := by
  rw [contMDiffAt_iff_of_mem_source (x := (z : OnePoint ℂ)) (y := ((P.eval z : ℂ) : OnePoint ℂ))
    (by simp [chartAt_coe]) (by simp [chartAt_coe])]
  refine ⟨continuousAt_polyMap_coe z, ?_⟩
  have hfun : (extChartAt 𝓘(ℝ, ℂ) ((P.eval z : ℂ) : OnePoint ℂ) ∘ polyMap P ∘
      (extChartAt 𝓘(ℝ, ℂ) (z : OnePoint ℂ)).symm) = fun w : ℂ => P.eval w := by
    funext w
    simp [extChartAt_coe, extChartAt_coe_symm, chartAt_coe]
  rw [hfun]
  exact (contDiff_eval ℝ P).contDiffAt.contDiffWithinAt

/-- The key computation (Milnor p. 9): for `w ≠ 0` with `P̃(w) ≠ 0`, where `P̃ = P.reverse`,
`P(1/w) = P̃(w) / wⁿ`, and hence `1 / P(1/w) = wⁿ / P̃(w)`. -/
theorem eval_inv_eq (w : ℂ) (hw : w ≠ 0) :
    P.eval w⁻¹ = P.reverse.eval w * (w⁻¹) ^ P.natDegree := by
  have := invertibleOfNonzero (inv_ne_zero hw)
  have h := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) w⁻¹ P
  rw [invOf_eq_inv, inv_inv, eval₂_id, eval₂_id] at h
  exact h.symm

/-- Near `∞`, `polyMap P` read in the chart `1/z` at both ends is `w ↦ wⁿ / P̃(w)`. -/
theorem contMDiffAt_polyMap_infty (hP : 0 < P.degree) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (polyMap P) ∞' := by
  rw [contMDiffAt_iff_of_mem_source (x := ∞') (y := ∞')
    (by simp [chartAt_infty]) (by simp [chartAt_infty])]
  refine ⟨continuousAt_polyMap_infty hP, ?_⟩
  -- The point and the function, in the chart `1/z`.
  have hpt : extChartAt 𝓘(ℝ, ℂ) ∞' ∞' = 0 := by simp [extChartAt_coe, chartAt_infty]
  have hg : ∀ w : ℂ, (extChartAt 𝓘(ℝ, ℂ) ∞' ∘ polyMap P ∘ (extChartAt 𝓘(ℝ, ℂ) ∞').symm) w =
      chartInf (polyMap P (chartInf.symm w)) := fun w => by
    simp [extChartAt_coe, extChartAt_coe_symm, chartAt_infty]
  rw [hpt]
  -- The model function `Q`.
  set R := P.reverse with hR
  set Q : ℂ → ℂ := fun w => w ^ P.natDegree / R.eval w with hQ
  have hR0 : R.eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero, hR, coeff_zero_reverse]
    exact leadingCoeff_ne_zero.2 (ne_zero_of_degree_pos hP)
  have hQsmooth : ContDiffAt ℝ ∞ Q 0 := by
    have : ContDiffAt ℂ ∞ Q 0 :=
      ((contDiff_id.pow _).contDiffAt).div (contDiff_eval ℂ R).contDiffAt hR0
    exact this.restrict_scalars ℝ
  -- The function agrees with `Q` on the open set `{w | R.eval w ≠ 0}`, which contains `0`.
  have hU : {w : ℂ | R.eval w ≠ 0} ∈ 𝓝 (0 : ℂ) :=
    (isOpen_compl_singleton.preimage R.continuous).mem_nhds hR0
  have heq : (extChartAt 𝓘(ℝ, ℂ) ∞' ∘ polyMap P ∘ (extChartAt 𝓘(ℝ, ℂ) ∞').symm) =ᶠ[𝓝 (0 : ℂ)] Q := by
    filter_upwards [hU] with w hw
    rw [hg w]
    by_cases hw0 : w = 0
    · subst hw0
      simp [hQ, (natDegree_pos hP).ne']
    · have hPw : P.eval w⁻¹ ≠ 0 := by
        rw [eval_inv_eq w hw0]
        exact mul_ne_zero hw (pow_ne_zero _ (inv_ne_zero hw0))
      rw [chartInf_symm_apply, invert_coe_of_ne hw0, polyMap_coe, chartInf_coe_of_ne hPw,
        eval_inv_eq w hw0, hQ]
      simp only [inv_pow, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
      rw [← hR]
  exact (hQsmooth.congr_of_eventuallyEq heq).contDiffWithinAt

theorem contMDiff_polyMap (hP : 0 < P.degree) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (polyMap P) := fun p => by
  induction p using OnePoint.rec with
  | infty => exact contMDiffAt_polyMap_infty hP
  | coe z => exact contMDiffAt_polyMap_coe z

/-! ### Regular points: the derivative of `polyMap P` at `z ∈ ℂ` is multiplication by `P'(z)` -/

theorem hasMFDerivAt_polyMap_coe (z : ℂ) :
    HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (polyMap P) (z : OnePoint ℂ)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (P.derivative.eval z)).restrictScalars ℝ) := by
  unfold HasMFDerivAt
  refine ⟨continuousAt_polyMap_coe z, ?_⟩
  have hfun : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (z : OnePoint ℂ) (polyMap P) =
      fun w : ℂ => P.eval w := by
    funext w
    simp [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm, chartAt_coe]
  have hpt : extChartAt 𝓘(ℝ, ℂ) (z : OnePoint ℂ) (z : OnePoint ℂ) = z := by
    simp [extChartAt_coe, chartAt_coe]
  rw [hfun, hpt]
  exact ((hasDerivAt_iff_hasFDerivAt.1 (P.hasDerivAt z)).restrictScalars ℝ).hasFDerivWithinAt

/-- Milnor p. 9: "`P` fails to be a local diffeomorphism only at the zeros of the derivative
polynomial `P'`." -/
theorem isRegularPoint_polyMap_coe {z : ℂ} (hz : P.derivative.eval z ≠ 0) :
    IsRegularPoint 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (polyMap P) (z : OnePoint ℂ) := by
  rw [IsRegularPoint, (hasMFDerivAt_polyMap_coe z).mfderiv]
  intro v
  let v' : ℂ := v
  refine ⟨v' / P.derivative.eval z, ?_⟩
  show (v' / P.derivative.eval z) * P.derivative.eval z = v'
  exact div_mul_cancel₀ v' hz

/-! ### The critical values form a finite set -/

variable (P) in
/-- The set of (candidate) critical values of `polyMap P`: `∞` together with the images of the
zeros of `P'`. -/
def critVals : Set (OnePoint ℂ) :=
  insert ∞' (((↑) : ℂ → OnePoint ℂ) '' ((fun z => P.eval z) '' {z | P.derivative.eval z = 0}))

theorem finite_zeros_derivative (hP : 0 < P.degree) : {z : ℂ | P.derivative.eval z = 0}.Finite := by
  have hd : P.derivative ≠ 0 := derivative_ne_zero.2 (natDegree_pos hP).ne'
  exact Polynomial.finite_setOfPred_isRoot hd

theorem critVals_finite (hP : 0 < P.degree) : (critVals P).Finite :=
  (((finite_zeros_derivative hP).image _).image _).insert _

theorem critVals_subset_range : critVals P ⊆ range (polyMap P) := by
  rintro y (rfl | ⟨_, ⟨z, -, rfl⟩, rfl⟩)
  · exact ⟨∞', rfl⟩
  · exact ⟨z, rfl⟩

theorem isRegularValue_of_notMem_critVals {y : OnePoint ℂ} (hy : y ∉ critVals P) :
    IsRegularValue 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (polyMap P) y := by
  intro x hx
  induction x using OnePoint.rec with
  | infty =>
    exact absurd (hx ▸ mem_insert _ _) hy
  | coe z =>
    refine isRegularPoint_polyMap_coe fun hz => hy ?_
    exact mem_insert_of_mem _ ⟨P.eval z, ⟨z, hz, rfl⟩, hx⟩

/-! ### The complement of the critical values is connected -/

theorem compl_critVals_eq :
    (critVals P)ᶜ =
      ((↑) : ℂ → OnePoint ℂ) '' ((fun z => P.eval z) '' {z | P.derivative.eval z = 0})ᶜ := by
  ext p
  induction p using OnePoint.rec with
  | infty => simp [critVals]
  | coe z => simp [critVals, OnePoint.coe_ne_infty]

theorem isPreconnected_compl_critVals (hP : 0 < P.degree) : IsPreconnected (critVals P)ᶜ := by
  rw [compl_critVals_eq]
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact_mod_cast Nat.one_lt_two
  have hfin : ((fun z => P.eval z) '' {z : ℂ | P.derivative.eval z = 0}).Finite :=
    (finite_zeros_derivative hP).image _
  exact (hfin.countable.isPathConnected_compl_of_one_lt_rank hrank).isConnected.isPreconnected.image
    _ OnePoint.continuous_coe.continuousOn

/-! ### Some regular value is in the image -/

theorem finite_fiber (hP : 0 < P.degree) (c : ℂ) : {z : ℂ | P.eval z = c}.Finite := by
  have hne : P - C c ≠ 0 := by
    intro h
    have : P = C c := sub_eq_zero.1 h
    rw [this] at hP
    exact absurd hP (not_lt.2 (degree_C_le))
  refine (Polynomial.finite_setOfPred_isRoot hne).subset fun z hz => ?_
  simp only [mem_setOf_eq, IsRoot.def, eval_sub, eval_C] at hz ⊢
  rw [hz, sub_self]

theorem infinite_range_eval (hP : 0 < P.degree) : (range fun z : ℂ => P.eval z).Infinite := by
  intro hfin
  have hcover : (univ : Set ℂ) ⊆ ⋃ c ∈ range (fun z : ℂ => P.eval z), {z : ℂ | P.eval z = c} :=
    fun z _ => mem_iUnion₂.2 ⟨P.eval z, mem_range_self z, rfl⟩
  exact Set.infinite_univ ((hfin.biUnion fun c _ => finite_fiber hP c).subset hcover)

theorem exists_regularValue_mem_range (hP : 0 < P.degree) :
    ∃ y ∈ (critVals P)ᶜ, y ∈ range (polyMap P) := by
  have hfin : ((fun z => P.eval z) '' {z : ℂ | P.derivative.eval z = 0}).Finite :=
    (finite_zeros_derivative hP).image _
  obtain ⟨w, ⟨z, rfl⟩, hw⟩ := ((infinite_range_eval hP).sdiff hfin).nonempty
  refine ⟨((P.eval z : ℂ) : OnePoint ℂ), ?_, z, rfl⟩
  rw [compl_critVals_eq]
  exact ⟨P.eval z, hw, rfl⟩

/-! ### The theorem -/

/-- **The fundamental theorem of algebra** (Milnor pp. 8–9): every nonconstant complex polynomial
has a zero. -/
theorem exists_root (hP : 0 < P.degree) : ∃ z : ℂ, P.eval z = 0 := by
  have hsub : (critVals P)ᶜ ⊆ range (polyMap P) :=
    Milnor.subset_range_of_isPreconnected (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, ℂ)) rfl
      (contMDiff_polyMap hP) (by simp) (fun y hy => isRegularValue_of_notMem_critVals hy)
      (isPreconnected_compl_critVals hP) (exists_regularValue_mem_range hP)
  have hsurj : Function.Surjective (polyMap P) := fun y => by
    by_cases hy : y ∈ critVals P
    · exact critVals_subset_range hy
    · exact hsub hy
  obtain ⟨x, hx⟩ := hsurj ((0 : ℂ) : OnePoint ℂ)
  induction x using OnePoint.rec with
  | infty => exact absurd hx (OnePoint.infty_ne_coe 0)
  | coe z => exact ⟨z, OnePoint.coe_eq_coe.1 hx⟩

end RiemannSphere

/-- **The fundamental theorem of algebra**, proved following Milnor §1. -/
theorem fundamental_theorem_of_algebra (P : Polynomial ℂ) (hP : 0 < P.degree) :
    ∃ z : ℂ, P.IsRoot z :=
  RiemannSphere.exists_root hP

end Milnor
