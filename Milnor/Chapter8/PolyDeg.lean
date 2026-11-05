import Milnor.Chapter1.FTA
import Milnor.Chapter6.LevelMap
import Milnor.Chapter5.Degree

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §8, Problem 2.

# The degree of a complex polynomial

"Show that every complex polynomial of degree `n` gives rise to a smooth map from the Gauss
sphere `S²` to itself of degree `n`."

As in Chapter 1 we use the Riemann sphere `ℂ ∪ {∞}` (`OnePoint ℂ`) in place of `S²`, with the
charts `z` and `1/z`, and the extension `polyMap P` of `P` by `P(∞) = ∞`
(`Milnor.RiemannSphere.polyMap`, smooth by `Milnor.RiemannSphere.contMDiff_polyMap`).

* `riemannOr`: the orientation of `ℂ ∪ {∞}` given by the standard orientation `(1, i)` of `ℂ` in
  both charts. It is an orientation because the chart transitions `z ↦ z` and `z ↦ 1/z` are
  holomorphic: their derivatives are multiplication by a nonzero complex number `w`, a real-linear
  map of determinant `|w|² > 0` (`orSign_complexMul`).
* `deg_polyMap`: `deg (polyMap P) = n` for `P` of degree `n ≥ 1`. Choose `y ∈ ℂ` which is not a
  critical value. Its preimages are the roots of `P - y`; there are `n` of them, all distinct
  because `P' ≠ 0` there, and at each of them the derivative of `polyMap P` is multiplication by
  `P'(z) ≠ 0`, which has sign `+1`.
-/

open Set Module Filter Topology Function Polynomial
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

namespace Problems

open RiemannSphere

local notation "∞'" => (OnePoint.infty : OnePoint ℂ)

/-! ### Multiplication by a nonzero complex number preserves orientation -/

/-- Multiplication by `w : ℂ`, as a real-linear map `ℂ → ℂ`. -/
abbrev cmul (w : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w).restrictScalars ℝ

theorem cmul_apply (w v : ℂ) : cmul w v = v * w := by simp [cmul]

theorem cmul_one : cmul 1 = ContinuousLinearMap.id ℝ ℂ :=
  ContinuousLinearMap.ext fun v => by simp [cmul_apply]

/-- The real determinant of multiplication by `w` is `|w|²`. -/
theorem det_cmul (w : ℂ) : LinearMap.det (cmul w : ℂ →ₗ[ℝ] ℂ) = Complex.normSq w := by
  have h : (cmul w : ℂ →ₗ[ℝ] ℂ) =
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w : ℂ →ₗ[ℂ] ℂ)).restrictScalars ℝ := rfl
  rw [h, LinearMap.det_restrictScalars, LinearMap.det_ring, Algebra.norm_complex_apply]
  simp

/-- Multiplication by a nonzero complex number preserves the standard orientation of `ℂ`. -/
theorem orSign_complexMul (w : ℂ) (hw : w ≠ 0) :
    orSign Complex.orientation Complex.orientation (cmul w) = 1 := by
  rw [orSign_self_eq_sgn_det Complex.finrank_real_complex, det_cmul]
  exact sgn_pos (Complex.normSq_pos.2 hw)

theorem cmul_eq_smul_id (w : ℂ) : cmul w = w • ContinuousLinearMap.id ℝ ℂ :=
  ContinuousLinearMap.ext fun v => by simp [cmul_apply, mul_comm]

/-- `orSign_complexMul`, with multiplication by `w` written as `w • id`. -/
theorem orSign_smul_id (w : ℂ) (hw : w ≠ 0) :
    orSign Complex.orientation Complex.orientation (w • ContinuousLinearMap.id ℝ ℂ) = 1 := by
  rw [← cmul_eq_smul_id]
  exact orSign_complexMul w hw

/-! ### The orientation of the Riemann sphere -/

/-- Near any point of its source, a chart of the Riemann sphere has derivative multiplication by a
nonzero complex number: the transition maps are `z ↦ z` and `z ↦ 1/z`. -/
theorem exists_hasMFDerivAt_extChartAt {x y : OnePoint ℂ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℂ) x).source) :
    ∃ w : ℂ, w ≠ 0 ∧ HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (extChartAt 𝓘(ℝ, ℂ) x) y (cmul w) := by
  have hcont : ContinuousAt (extChartAt 𝓘(ℝ, ℂ) x) y := continuousAt_extChartAt' hy
  induction x using OnePoint.rec with
  | infty =>
    induction y using OnePoint.rec with
    | infty =>
      refine ⟨1, one_ne_zero, hcont, ?_⟩
      have hfun : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞' (extChartAt 𝓘(ℝ, ℂ) ∞') = id := by
        funext v
        simp [writtenInExtChartAt, chartAt_infty, chartAt_self_eq, invert_invert]
      rw [hfun, cmul_one]
      exact (hasFDerivAt_id _).hasFDerivWithinAt
    | coe u =>
      have hu : u ≠ 0 := by
        rintro rfl
        simp [chartAt_infty] at hy
      refine ⟨-(u ^ 2)⁻¹, neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 hu)), hcont, ?_⟩
      have hfun : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (u : OnePoint ℂ) (extChartAt 𝓘(ℝ, ℂ) ∞') =
          fun v : ℂ => chart₀ (invert (v : OnePoint ℂ)) := by
        funext v
        simp [writtenInExtChartAt, chartAt_infty, chartAt_coe, chartAt_self_eq]
      have hpt : extChartAt 𝓘(ℝ, ℂ) (u : OnePoint ℂ) (u : OnePoint ℂ) = u := by
        simp [chartAt_coe]
      have heq : (fun v : ℂ => v⁻¹) =ᶠ[𝓝 u] fun v : ℂ => chart₀ (invert (v : OnePoint ℂ)) := by
        filter_upwards [(isOpen_ne (x := (0 : ℂ))).mem_nhds hu] with v hv
        rw [invert_coe_of_ne hv, chart₀_coe]
      rw [hfun, hpt]
      have hD := ((hasDerivAt_iff_hasFDerivAt.1 (hasDerivAt_inv hu)).restrictScalars ℝ)
      exact (hD.congr_of_eventuallyEq heq.symm).hasFDerivWithinAt
  | coe z =>
    induction y using OnePoint.rec with
    | infty =>
      simp [chartAt_coe] at hy
    | coe u =>
      refine ⟨1, one_ne_zero, hcont, ?_⟩
      have hfun : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (u : OnePoint ℂ)
          (extChartAt 𝓘(ℝ, ℂ) (z : OnePoint ℂ)) = id := by
        funext v
        simp [writtenInExtChartAt, chartAt_coe, chartAt_self_eq]
      rw [hfun, cmul_one]
      exact (hasFDerivAt_id _).hasFDerivWithinAt

/-- **The orientation of the Riemann sphere**: the standard orientation `(1, i)` of `ℂ = ℝ²` in
every chart. -/
def riemannOr : Orient 𝓘(ℝ, ℂ) (OnePoint ℂ) 2 where
  or _ := Complex.orientation
  cont x := by
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ, ℂ)) x] with y hy
    obtain ⟨w, hw, hD⟩ := exists_hasMFDerivAt_extChartAt hy
    rw [HasMFDerivAt.mfd_eq hD]
    exact orSign_complexMul w hw

@[simp] theorem riemannOr_or (x : OnePoint ℂ) : riemannOr.or x = Complex.orientation := rfl

/-! ### Instances -/

/-- The Riemann sphere is second countable (it is compact and modelled on `ℂ`). -/
instance instSecondCountableTopologyRiemannSphere : SecondCountableTopology (OnePoint ℂ) :=
  ChartedSpace.secondCountable_of_sigmaCompact ℂ (OnePoint ℂ)

example : CompactSpace (OnePoint ℂ) := inferInstance
example : T2Space (OnePoint ℂ) := inferInstance
example : ConnectedSpace (OnePoint ℂ) := inferInstance

/-! ### The degree of `polyMap P` -/

/-- At a finite point where `P' ≠ 0`, `polyMap P` preserves orientation. -/
theorem signAt_polyMap_coe {P : ℂ[X]} {z : ℂ} (hz : P.derivative.eval z ≠ 0) :
    signAt riemannOr riemannOr (polyMap P) (z : OnePoint ℂ) = 1 := by
  unfold signAt
  rw [HasMFDerivAt.mfd_eq (hasMFDerivAt_polyMap_coe z)]
  exact orSign_complexMul _ hz

/-- **Milnor §8, Problem 2.** A complex polynomial of degree `n ≥ 1`, extended to the Riemann
sphere, has degree `n`. -/
theorem deg_polyMap (P : Polynomial ℂ) (hP : 0 < P.degree) :
    deg riemannOr riemannOr (polyMap P) = P.natDegree := by
  classical
  -- a value `y ∈ ℂ` which is not a critical value
  have hfin : (((↑) : ℂ → OnePoint ℂ) ⁻¹' critVals P).Finite :=
    (critVals_finite hP).preimage OnePoint.coe_injective.injOn
  obtain ⟨y, -, hy⟩ := Set.infinite_univ.exists_notMem_finite hfin
  have hy' : (y : OnePoint ℂ) ∉ critVals P := hy
  rw [deg_eq Complex.finrank_real_complex Complex.finrank_real_complex riemannOr riemannOr
    (contMDiff_polyMap hP) (isRegularValue_of_notMem_critVals hy')]
  -- `P'` does not vanish on the fibre over `y`
  have hderiv : ∀ z : ℂ, P.eval z = y → P.derivative.eval z ≠ 0 := fun z hz h0 =>
    hy' (mem_insert_of_mem _ ⟨P.eval z, ⟨z, h0, rfl⟩, by rw [hz]⟩)
  -- the fibre over `y` is the set of roots of `P - y`
  have hpre : polyMap P ⁻¹' {(y : OnePoint ℂ)} =
      ((↑) : ℂ → OnePoint ℂ) '' ((P - C y).roots.toFinset : Set ℂ) := by
    ext p
    induction p using OnePoint.rec with
    | infty => simp
    | coe z => simp [mem_roots_sub_C hP]
  have hsign : ∀ z ∈ ((P - C y).roots.toFinset : Set ℂ),
      signAt riemannOr riemannOr (polyMap P) (z : OnePoint ℂ) = 1 := fun z hz => by
    have hz' : P.eval z = y := by simpa [mem_roots_sub_C hP] using hz
    exact signAt_polyMap_coe (hderiv z hz')
  unfold degAt
  rw [hpre, finsum_mem_image OnePoint.coe_injective.injOn, finsum_mem_congr rfl hsign,
    finsum_mem_coe_finset, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- the roots of `P - y` are simple
  have hQ0 : P - C y ≠ 0 := fun h => by
    have := congrArg natDegree h
    rw [natDegree_sub_C, natDegree_zero] at this
    exact (natDegree_pos hP).ne' this
  have hnodup : (P - C y).roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro z
    rw [count_roots]
    by_contra h
    have h1 := (one_lt_rootMultiplicity_iff_isRoot hQ0).1 (not_le.1 h)
    have hz : P.eval z = y := by
      have := h1.1
      simpa [sub_eq_zero] using this
    have hz' : P.derivative.eval z = 0 := by
      have := h1.2
      simpa using this
    exact hderiv z hz hz'
  rw [Multiset.toFinset_card_of_nodup hnodup, IsAlgClosed.card_roots_eq_natDegree, natDegree_sub_C]

end Problems

end Milnor
