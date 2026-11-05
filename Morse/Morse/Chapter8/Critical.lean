import Morse.Chapter8.FirstVariation
import Morse.Chapter7.Minimal

/-!
Milnor, *Morse Theory*, §11, p. 69 (critical paths) and §12, p. 73 (Corollary 12.3), for a
submanifold `N ⊆ ℝᴷ` with the induced metric.

# The critical points of the energy are the geodesics

## Milnor's text, paraphrased

* (p. 69) A path `ω` is a *critical path* of `F : Ω → ℝ` if `dF(ᾱ(u))/du` at `u = 0` exists and
  is zero for every variation `ᾱ` of `ω`.
* (p. 73) A path `ω ∈ Ω` is a *geodesic* if it is `C^∞` on the whole interval `[0, 1]` and its
  acceleration vanishes identically ("unbroken geodesic").
* **Corollary 12.3** (p. 73): `ω` is a critical point of `E` if and only if it is a geodesic.
  Proof: a geodesic is clearly critical.  Conversely, a variation with `W(t) = f(t) A(t)`, `f`
  positive except at the break points, gives `0 = -∫ f ‖A‖²`, so each piece is a geodesic; a
  variation with `W(t_i) = Δ_{t_i} V` gives `0 = -Σ ‖Δ_{t_i} V‖²`, so `ω` is `C¹`; and then by the
  uniqueness theorem for differential equations `ω` is `C^∞`.

## In the embedded setting

* `Morse.IsCriticalPath N ω`: Milnor's definition, quantified over all variations
  (`Morse.IsVariation`, any parameter set, any break points).  By Theorem 12.2 the derivative
  always exists, and by Lemma 11.A criticality means that the first variation vanishes on `TΩ_ω`
  (`Morse.isCriticalPath_iff`).
* `Morse.IsUnbrokenGeodesic hN ω`: `C^∞` on `[0, 1]` (with one-sided derivatives at the ends) and
  a geodesic of Chapter 7 (`Morse.IsGeodesicOn`) on `(0, 1)`.
* **Corollary 12.3**: `Morse.corollary_12_3`.  The three steps: `Morse.accel_eq_zero_of_critical`,
  `Morse.jump_eq_zero_of_critical`, `Morse.isGeodesicOn_of_glue`.

## What Milnor leaves implicit

* **The test variations exist** only by Lemma 11.A, with an `ε` uniform along `ω`.
* **Step 1.**  `W = f A` with `f = Π (t - t_i)²` requires checking that `W` is continuous at the
  `t_i`, where the one-sided accelerations differ.  Here each point `x` off the break points is
  handled separately with `W = φ A`, `φ ≥ 0` a bump function at `x` supported where `ω` is smooth;
  this `W` is smooth on all of `ℝ`, and `0 = -∫ φ ‖A‖²` gives `A(x) = 0`.
* **Step 2.**  "Pick a variation such that `W(t_i) = Δ_{t_i} V`" needs an explicit field; here
  `W = φ P(Δ_x V)` with `φ` a bump function at the break point `x` and `P` the tangent projection
  (in place of parallel transport), so that `½ dE = -‖Δ_x V‖²`.  It uses that the one-sided
  velocities, hence the jumps, are tangent (`Morse.prj_jump`).
* **Step 3**, "by the uniqueness theorem for differential equations": at a former break point
  `t_i`, `ω` is known to be a geodesic only on each side.  The lift `(ω, ω')` is continuous at
  `t_i` (no jump) and solves the first-order system `(x, v)' = (v, II_x(v, v))` on both sides; by
  a derivative extension argument it is differentiable at `t_i` and solves the system there too,
  so two-sided uniqueness (Chapter 7) identifies `ω` near `t_i` with the geodesic through
  `(ω(t_i), ω'(t_i))`, which exists for any velocity by Lemma 10.2 and homogeneity
  (`Morse.exists_isGeodesicOn_through`).
* An unbroken geodesic on `[0, 1]` is not shown to extend to a geodesic on an open interval
  containing `[0, 1]` (true, by the same uniqueness argument at the end points; not needed here).
-/

open Set Filter Topology Function MeasureTheory Metric
open scoped ContDiff Manifold RealInnerProductSpace Interval

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-! ### Critical paths and unbroken geodesics -/

variable (N) in
/-- **A critical path of the energy** (Milnor p. 69): for every variation `ᾱ` of `ω`, the
derivative `dE(ᾱ(u))/du` at `u = 0` exists and is zero. -/
def IsCriticalPath (c : ℝ → V) : Prop :=
  ∀ (U : Set ℝ) (α : ℝ → ℝ → V) (B : Finset ℝ), IsVariation N U α B →
    (∀ t ∈ Icc (0 : ℝ) 1, α 0 t = c t) → HasDerivAt (fun u => energy (α u) 0 1) 0 0

/-- **An (unbroken) geodesic** in `Ω` (Milnor p. 73): `C^∞` on the whole closed interval `[0, 1]`
(one-sided derivatives at the ends), with zero acceleration. -/
def IsUnbrokenGeodesic (c : ℝ → V) : Prop :=
  ContDiffOn ℝ ∞ c (Icc 0 1) ∧ IsGeodesicOn hN c (Ioo 0 1)

/-- **Critical paths through the first variation**: by Theorem 12.2 and Lemma 11.A, `ω ∈ Ω` is a
critical path iff the linear form `W ↦ -Σ_t ⟨W_t, Δ_t V⟩ - ∫₀¹ ⟨W_t, A_t⟩ dt` vanishes on `TΩ_ω`. -/
theorem isCriticalPath_iff {c : ℝ → V} {p q : V} (hc : c ∈ pathSpace N p q) :
    IsCriticalPath N c ↔ ∀ X ∈ pathTangent hN c, firstVariation hN c X = 0 := by
  constructor
  · intro hcrit X hX
    obtain ⟨ε, hε, B, hα, h0, hd⟩ := exists_variation_one hN hc hX
    have h1 := hcrit _ _ B hα h0
    have h2 := first_variation hN hα h0
    have h3 : 2 * firstVariation hN c (varField fun u t => exp hN (c t) (u • X t)) = 0 :=
      h2.unique h1
    rw [firstVariation_congr_field hN hd] at h3
    linarith
  · intro h U α B hα hαc
    have h2 := first_variation hN hα hαc
    rwa [h _ (mem_pathTangent_congr hN hαc (hα.varField_mem hN)), mul_zero] at h2

/-! ### Corollary 12.3, the easy direction -/

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- A geodesic is a critical path (Milnor p. 73, "clearly a geodesic is a critical point"). -/
theorem IsUnbrokenGeodesic.firstVariation_eq_zero {c : ℝ → V} (h : IsUnbrokenGeodesic hN c)
    (X : ℝ → V) : firstVariation hN c X = 0 := by
  have hj : ∀ t ∈ Ioo (0 : ℝ) 1, ⟪X t, jump c t⟫ = 0 := fun t ht => by
    rw [jump_eq_zero (h.2.hasDerivAt ht).differentiableAt, inner_zero_right]
  have ha : ∀ t ∈ Ioo (0 : ℝ) 1, ⟪X t, accel hN c t⟫ = 0 := fun t ht => by
    rw [accel, covD, prj_of_mem hN (h.2.mem t ht), h.2.tanProj_deriv_deriv ht, inner_zero_right]
  rw [firstVariation, finsum_mem_eq_zero_of_forall_eq_zero hj,
    intervalIntegral.integral_congr_Ioo_of_le zero_le_one (g := fun _ => (0 : ℝ)) ha]
  simp

/-! ### Corollary 12.3, the converse -/

section Converse

variable {c : ℝ → V} {p q : V} {B : Finset ℝ}

/-- A function smooth on an open set `O` containing the support of a smooth `φ` becomes smooth
everywhere after multiplication by `φ`. -/
theorem contDiff_smul_of_tsupport_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {O : Set ℝ} (hO : IsOpen O) (hsupp : tsupport φ ⊆ O)
    {g : ℝ → E} (hg : ContDiffOn ℝ ∞ g O) : ContDiff ℝ ∞ (fun t => φ t • g t) := by
  refine contDiff_iff_contDiffAt.2 fun t => ?_
  by_cases ht : t ∈ O
  · exact hφ.contDiffAt.smul (hg.contDiffAt (hO.mem_nhds ht))
  · have ht' : t ∉ tsupport φ := fun h => ht (hsupp h)
    rw [notMem_tsupport_iff_eventuallyEq] at ht'
    refine contDiffAt_const (c := (0 : E)).congr_of_eventuallyEq ?_
    filter_upwards [ht'] with y hy
    simp [hy]

/-- A bump function on `ℝ` centred at `x`, equal to `1` near `x`, supported in
`(x - r, x + r)`. -/
def bumpAt (x : ℝ) {r : ℝ} (hr : 0 < r) : ContDiffBump x := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- On an open interval where the acceleration vanishes, a smooth path in `N` is a geodesic. -/
theorem isGeodesicOn_of_accel {s s' : ℝ} (hcs : ContDiffOn ℝ ∞ c (Ioo s s'))
    (hcN : ∀ t ∈ Ioo s s', c t ∈ N) (hA : ∀ t ∈ Ioo s s', accel hN c t = 0) :
    IsGeodesicOn hN c (Ioo s s') where
  isOpen := isOpen_Ioo
  mem := hcN
  contDiffOn := hcs
  normal t ht := by
    have h := hA t ht
    rw [accel, covD, prj_of_mem hN (hcN t ht)] at h
    exact (tanProj_eq_zero_iff hN).1 h

omit [FiniteDimensional ℝ W] in
/-- **Step 1 of Corollary 12.3** (Milnor p. 73): at a critical path, the acceleration vanishes
off the break points.  Test field: `W = φ A`, `φ ≥ 0` a bump function at the point, supported
where the path is smooth (Milnor uses `W = f A` with `f > 0` off the break points). -/
theorem accel_eq_zero_of_critical (hc : c ∈ pathSpace N p q)
    (hcrit : ∀ X ∈ pathTangent hN c, firstVariation hN c X = 0)
    (hB : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ B, x ∉ Ioo s t) → ContDiffOn ℝ ∞ c (Icc s t))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxB : x ∉ B) : accel hN c x = 0 := by
  obtain ⟨s, s', hs, hsx, hxs', hs', hBs⟩ := exists_piece_around B hx.1 hx.2 hxB
  set r := min (x - s) (s' - x) / 2
  have hr : 0 < r := half_pos (lt_min (by linarith) (by linarith))
  have hr1 : r < x - s := by
    have := min_le_left (x - s) (s' - x); simp only [r]; linarith
  have hr2 : r < s' - x := by
    have := min_le_right (x - s) (s' - x); simp only [r]; linarith
  have hball : closedBall x r ⊆ Ioo s s' := fun t ht => by
    rw [mem_closedBall, Real.dist_eq, abs_le] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcs : ContDiffOn ℝ ∞ c (Ioo s s') :=
    (hB s s' hs (hsx.trans hxs') hs' hBs).mono Ioo_subset_Icc_self
  have hcN : ∀ t ∈ Ioo s s', c t ∈ N := fun t ht =>
    hc.2.1 t ⟨hs.trans ht.1.le, ht.2.le.trans hs'⟩
  -- the acceleration is smooth on `(s, s')`
  have hA : ContDiffOn ℝ ∞ (accel hN c) (Ioo s s') := by
    have h1 := ContDiffOn.prj_comp hN hcs hcN
    have h2 : ContDiffOn ℝ ∞ (deriv (deriv c)) (Ioo s s') :=
      ((hcs.deriv_of_isOpen isOpen_Ioo (m := ∞) (by simp)).deriv_of_isOpen isOpen_Ioo
        (m := ∞) (by simp))
    exact h1.clm_apply h2
  set φ := bumpAt x hr
  have hrOut : φ.rOut = r := rfl
  have hrIn : φ.rIn = r / 2 := rfl
  have hφs : tsupport φ ⊆ Ioo s s' := by rw [φ.tsupport_eq, hrOut]; exact hball
  have hφc : ContDiff ℝ ∞ φ := φ.contDiff (n := ⊤)
  have hφ0 : φ 0 = 0 := by
    rw [← notMem_support, φ.support_eq, hrOut, mem_ball, Real.dist_eq, not_lt, zero_sub,
      abs_neg, abs_of_pos hx.1]
    linarith
  have hφ1 : φ 1 = 0 := by
    rw [← notMem_support, φ.support_eq, hrOut, mem_ball, Real.dist_eq, not_lt,
      abs_of_pos (by linarith : 0 < 1 - x)]
    linarith
  set X : ℝ → V := fun t => φ t • accel hN c t
  have hX : X ∈ pathTangent hN c := by
    refine ⟨IsPiecewiseSmooth.of_contDiff (contDiff_smul_of_tsupport_subset hφc isOpen_Ioo hφs hA)
      zero_le_one, fun t _ => ?_, ?_, ?_⟩
    · simp only [X, map_smul, accel, covD, prj_prj]
    · simp [X, hφ0]
    · simp [X, hφ1]
  have h0 := hcrit X hX
  -- the jump terms vanish: `φ = 0` off `(s, s')`, where `ω` is smooth
  have hj : ∀ t ∈ Ioo (0 : ℝ) 1, ⟪X t, jump c t⟫ = 0 := by
    intro t _
    by_cases ht : t ∈ Ioo s s'
    · rw [jump_eq_zero ((hcs.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)),
        inner_zero_right]
    · have : φ t = 0 := by
        by_contra h
        exact ht (hφs (subset_tsupport _ h))
      simp [X, this]
  rw [firstVariation, finsum_mem_eq_zero_of_forall_eq_zero hj, neg_zero, zero_sub,
    neg_eq_zero] at h0
  -- so `∫ φ ‖A‖² = 0`, with a continuous nonnegative integrand
  set g : ℝ → ℝ := fun t => ⟪X t, accel hN c t⟫
  have hg : ∀ t, g t = φ t * ‖accel hN c t‖ ^ 2 := fun t => by
    simp only [g, X, inner_smul_left, real_inner_self_eq_norm_sq, RCLike.conj_to_real]
  have hgc : Continuous g := by
    have : ContDiff ℝ ∞ (fun t => φ t • ‖accel hN c t‖ ^ 2) :=
      contDiff_smul_of_tsupport_subset hφc isOpen_Ioo hφs (hA.norm_sq ℝ)
    exact (this.continuous).congr fun t => by rw [hg, smul_eq_mul]
  have hg0 : ∀ t, 0 ≤ g t := fun t => by rw [hg]; exact mul_nonneg φ.nonneg (sq_nonneg _)
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
    (.of_forall hg0) (hgc.intervalIntegrable 0 1)).1 h0
  have hgx := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset
    Ioo_subset_Ioc_self hae) isOpen_Ioo hgc.continuousOn continuousOn_const hx
  have hφx : φ x = 1 := φ.one_of_mem_closedBall (mem_closedBall_self (by rw [hrIn]; positivity))
  simp only [Pi.zero_apply, hg, hφx, one_mul, pow_eq_zero_iff two_ne_zero, norm_eq_zero] at hgx
  exact hgx

/-- The one-sided velocities of a piecewise smooth path in `N` are tangent, hence so are its
velocity jumps. -/
theorem prj_jump (hc : c ∈ pathSpace N p q)
    (hB : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ B, x ∉ Ioo s t) → ContDiffOn ℝ ∞ c (Icc s t))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : prj hN (c x) (jump c x) = jump c x := by
  obtain ⟨s, hs, hsx, hBs⟩ := exists_piece_left B hx.1
  obtain ⟨s', hxs', hs', hBs'⟩ := exists_piece_right B hx.2
  have hL := hB s x hs hsx hx.2.le hBs
  have hR := hB x s' hx.1.le hxs' hs' hBs'
  have hxN : c x ∈ N := hc.2.1 x (Ioo_subset_Icc_self hx)
  have hT : ∀ {a b : ℝ}, 0 ≤ a → a < b → b ≤ 1 → ContDiffOn ℝ ∞ c (Icc a b) →
      ∀ y ∈ Icc a b, y = x → derivWithin c (Icc a b) y ∈ tangentSubspace hN ⟨c x, hxN⟩ := by
    intro a b ha hab hb hcab y hy hyx
    subst hyx
    exact hasDerivWithinAt_mem_tangentSubspace hN
      ((hcab.differentiableOn (by simp)) y hy).hasDerivWithinAt (uniqueDiffOn_Icc hab y hy)
      (fun z hz => hc.2.1 z ⟨ha.trans hz.1, hz.2.trans hb⟩) hy
  rw [prj_eq_self_iff hN hxN, jump, derivWithin_Ici_eq_of_piece hxs' (hR.differentiableOn
    (by simp)), derivWithin_Iic_eq_of_piece hsx (hL.differentiableOn (by simp))]
  exact Submodule.sub_mem _ (hT hx.1.le hxs' hs' hR x (left_mem_Icc.2 hxs'.le) rfl)
    (hT hs hsx hx.2.le hL x (right_mem_Icc.2 hsx.le) rfl)

/-- **Step 2 of Corollary 12.3** (Milnor p. 73): at a critical path the velocity has no jumps.
Test field: `W = φ P(Δ_x V)`, `φ` a bump function at the break point `x`, so that
`½ dE = -‖Δ_x V‖²`.  (Milnor: "pick a variation such that `W(t_i) = Δ_{t_i} V`".) -/
theorem jump_eq_zero_of_critical (hc : c ∈ pathSpace N p q)
    (hcrit : ∀ X ∈ pathTangent hN c, firstVariation hN c X = 0)
    (hB : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ B, x ∉ Ioo s t) → ContDiffOn ℝ ∞ c (Icc s t))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : jump c x = 0 := by
  by_cases hxB : x ∉ B
  · obtain ⟨s, s', hs, hsx, hxs', hs', hBs⟩ := exists_piece_around B hx.1 hx.2 hxB
    exact jump_eq_zero (((hB s s' hs (hsx.trans hxs') hs' hBs).contDiffAt
      (Icc_mem_nhds hsx hxs')).differentiableAt (by simp))
  push Not at hxB
  obtain ⟨s, hs, hsx, hBs⟩ := exists_piece_left B hx.1
  obtain ⟨s', hxs', hs', hBs'⟩ := exists_piece_right B hx.2
  have hL := hB s x hs hsx hx.2.le hBs
  have hR := hB x s' hx.1.le hxs' hs' hBs'
  set r := min (x - s) (s' - x) / 2
  have hr : 0 < r := half_pos (lt_min (by linarith) (by linarith))
  have hr1 : r < x - s := by
    have := min_le_left (x - s) (s' - x); simp only [r]; linarith
  have hr2 : r < s' - x := by
    have := min_le_right (x - s) (s' - x); simp only [r]; linarith
  set Δ := jump c x
  have hΔ : prj hN (c x) Δ = Δ := prj_jump hN hc hB hx
  set φ := bumpAt x hr
  have hrOut : φ.rOut = r := rfl
  have hrIn : φ.rIn = r / 2 := rfl
  have hφc : ContDiff ℝ ∞ φ := φ.contDiff (n := ⊤)
  have hφ0 : φ 0 = 0 := by
    rw [← notMem_support, φ.support_eq, hrOut, mem_ball, Real.dist_eq, not_lt, zero_sub,
      abs_neg, abs_of_pos hx.1]
    linarith
  have hφ1 : φ 1 = 0 := by
    rw [← notMem_support, φ.support_eq, hrOut, mem_ball, Real.dist_eq, not_lt,
      abs_of_pos (by linarith : 0 < 1 - x)]
    linarith
  set X : ℝ → V := fun t => φ t • prj hN (c t) Δ
  have hX : X ∈ pathTangent hN c := by
    refine ⟨(IsPiecewiseSmooth.of_contDiff hφc zero_le_one).smul
      ((hc.1.prj_comp hN hc.2.1).clm_apply
        (IsPiecewiseSmooth.of_contDiff contDiff_const zero_le_one)), fun t _ => ?_, ?_, ?_⟩
    · simp only [X, map_smul, prj_prj]
    · simp [X, hφ0]
    · simp [X, hφ1]
  have h0 := hcrit X hX
  -- the integral term vanishes, the acceleration being zero off the break points (Step 1)
  have hint : ∫ t in (0 : ℝ)..1, ⟪X t, accel hN c t⟫ = 0 := by
    have hfin : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ insert (1 : ℝ) (B : Set ℝ) :=
      (B.finite_toSet.insert 1).countable.ae_notMem _
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
    · simp
    filter_upwards [hfin] with t htB ht
    rw [uIoc_of_le zero_le_one] at ht
    rw [mem_insert_iff, not_or] at htB
    rw [accel_eq_zero_of_critical hN hc hcrit hB ⟨ht.1, lt_of_le_of_ne ht.2 htB.1⟩ htB.2,
      inner_zero_right]
  -- the jump sum reduces to the term at `x`
  have hsum : ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪X t, jump c t⟫ = ‖Δ‖ ^ 2 := by
    rw [finsum_mem_eq_sum_of_subset (t := {x}) _ ?_ (by simpa using hx), Finset.sum_singleton]
    · have hφx : φ x = 1 :=
        φ.one_of_mem_closedBall (mem_closedBall_self (by rw [hrIn]; positivity))
      simp only [X, hφx, one_smul, hΔ, real_inner_self_eq_norm_sq, Δ]
    · rintro t ⟨ht, hts⟩
      rw [Finset.coe_singleton, mem_singleton_iff]
      by_contra htx
      apply hts
      by_cases htb : t ∈ ball x r
      · rw [Real.ball_eq_Ioo] at htb
        have hdt : DifferentiableAt ℝ c t := by
          rcases lt_or_gt_of_ne htx with h | h
          · exact (hL.contDiffAt (Icc_mem_nhds (by linarith [htb.1]) h)).differentiableAt
              (by simp)
          · exact (hR.contDiffAt (Icc_mem_nhds h (by linarith [htb.2]))).differentiableAt
              (by simp)
        change ⟪X t, jump c t⟫ = 0
        rw [jump_eq_zero hdt, inner_zero_right]
      · have : φ t = 0 := by
          rw [← notMem_support, φ.support_eq, hrOut]; exact htb
        change ⟪X t, jump c t⟫ = 0
        simp [X, this]
  rw [firstVariation, hsum, hint, sub_zero, neg_eq_zero, pow_eq_zero_iff two_ne_zero,
    norm_eq_zero] at h0
  exact h0

/-! ### Step 3: no corners, by uniqueness of geodesics -/

/-- The vector field `G(x, v) = (v, dQ_x(v) v)` on `V × V` (`Q = Morse.projRep σ` the local ambient
extension of the tangent projection): the lifts `(γ, γ')` of geodesics are its integral curves
(the geodesic equation `γ'' = II(γ', γ')` of Chapter 7). -/
def liftField (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) (z : V × V) : V × V :=
  (z.2, fderiv ℝ (projRep σ) z.1 z.2 z.2)

theorem IsGeodesicOn.hasDerivAt_lift {γ : ℝ → V} {s : Set ℝ} (h : IsGeodesicOn hN γ s)
    (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) {t : ℝ} (ht : t ∈ s) (htσ : γ t ∈ σ.φ.source) :
    HasDerivAt (fun τ => (γ τ, deriv γ τ)) (liftField σ (γ t, deriv γ t)) t := by
  have e := h.deriv_deriv_eq ht
  rw [secondFundForm, dN_tanProj_eq_fderiv hN σ (q := ⟨γ t, h.mem t ht⟩) htσ
    (h.deriv_mem ht)] at e
  have hdd := h.hasDerivAt_deriv ht
  rw [e] at hdd
  exact (h.hasDerivAt ht).prodMk hdd

omit [FiniteDimensional ℝ W] in
theorem contDiffAt_liftField (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) {z : V × V} (hz : z.1 ∈ N)
    (hzσ : z.1 ∈ σ.φ.source) : ContDiffAt ℝ 1 (liftField σ) z := by
  have hQ : ContDiffAt ℝ ∞ (fderiv ℝ (projRep σ)) z.1 :=
    (contDiffAt_projRep σ (q := ⟨z.1, hz⟩) hzσ).fderiv_right (m := ∞) (by simp)
  have h1 : ContDiffAt ℝ ∞ (fun z : V × V => fderiv ℝ (projRep σ) z.1) z :=
    ContDiffAt.comp z hQ contDiffAt_fst
  exact (contDiffAt_snd.prodMk ((h1.clm_apply contDiffAt_snd).clm_apply contDiffAt_snd)).of_le
    (by exact_mod_cast le_top)

/-- **Local existence of geodesics with any initial velocity** (Theorem 10.1, via Lemma 10.2 and
homogeneity): through `q ∈ N` with velocity `v ∈ T_qN` at time `x` there is a geodesic on some
`(x - η, x + η)`. -/
theorem exists_isGeodesicOn_through (q : N) {v : V} (hv : v ∈ tangentSubspace hN q) (x : ℝ) :
    ∃ η > 0, ∃ σ : ℝ → V, IsGeodesicOn hN σ (Ioo (x - η) (x + η)) ∧ σ x = q ∧
      deriv σ x = v := by
  obtain ⟨U, -, hqU, ε, hε, Γ, -, hgeo⟩ := lemma_10_2 hN q
  set k : ℝ := 2 * (‖v‖ + 1) / ε
  have hk : 0 < k := by positivity
  set w : V := k⁻¹ • v
  have hw : ‖w‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hk, inv_mul_lt_iff₀ hk]
    simp only [k]
    rw [div_mul_cancel₀ _ hε.ne']
    linarith [norm_nonneg v]
  obtain ⟨hg, h0, hd, -⟩ := hgeo q hqU w (Submodule.smul_mem _ _ hv) hw
  have hg' := hg.comp_mul_add k (-(k * x))
  refine ⟨1 / k, by positivity, fun t => Γ (q, w, k * t + -(k * x)), hg'.mono isOpen_Ioo ?_, ?_, ?_⟩
  · intro t ht
    simp only [mem_preimage, mem_Ioo]
    have h1 : k * t + -(k * x) = k * (t - x) := by ring
    rw [h1]
    have := ht.1; have := ht.2
    constructor
    · have : -1 < k * (t - x) := by
        have h2 : -(1 / k) < t - x := by linarith
        calc (-1 : ℝ) = k * (-(1 / k)) := by field_simp
          _ < k * (t - x) := mul_lt_mul_of_pos_left h2 hk
      linarith
    · have : k * (t - x) < 1 := by
        have h2 : t - x < 1 / k := by linarith
        calc k * (t - x) < k * (1 / k) := mul_lt_mul_of_pos_left h2 hk
          _ = 1 := by field_simp
      linarith
  · simp only [show k * x + -(k * x) = 0 by ring, h0]
  · have h1 : HasDerivAt (fun t : ℝ => k * t + -(k * x)) k x := by
      simpa using ((hasDerivAt_id x).const_mul k).add_const (-(k * x))
    have h2 := (show HasDerivAt (fun t => Γ (q, w, t)) w (k * x + -(k * x)) by
      rw [show k * x + -(k * x) = 0 by ring]; exact hd).scomp x h1
    have h3 : HasDerivAt (fun t => Γ (q, w, k * t + -(k * x))) (k • w) x := h2
    rw [h3.deriv, smul_smul, mul_inv_cancel₀ hk.ne', one_smul]

/-- **Step 3 of Corollary 12.3** (Milnor p. 73, "it follows from the uniqueness theorem for
differential equations that `ω` is `C^∞` everywhere"): a path which is a geodesic on both sides of
`x`, smooth up to `x` from each side, and differentiable at `x`, is a geodesic near `x`.  Proof:
the lift `(ω, ω')` is continuous at `x` and solves `(x, v)' = G(x, v)` on both sides, hence also at
`x`; by uniqueness for this first-order system it is the lift of the geodesic with the same
position and velocity at `x`. -/
theorem isGeodesicOn_of_glue {γ : ℝ → V} {x r : ℝ} (hr : 0 < r)
    (hL : ContDiffOn ℝ ∞ γ (Icc (x - r) x)) (hR : ContDiffOn ℝ ∞ γ (Icc x (x + r)))
    (hgL : IsGeodesicOn hN γ (Ioo (x - r) x)) (hgR : IsGeodesicOn hN γ (Ioo x (x + r)))
    (hx : γ x ∈ N) (hd : DifferentiableAt ℝ γ x) :
    ∃ η > 0, IsGeodesicOn hN γ (Ioo (x - η) (x + η)) := by
  set q : N := ⟨γ x, hx⟩
  set τ := sliceAt hN q
  have hq : γ x ∈ τ.φ.source := mem_sliceAt_source hN q
  have hmemN : ∀ t ∈ Ioo (x - r) (x + r), γ t ∈ N := by
    intro t ht
    rcases lt_trichotomy t x with h | rfl | h
    · exact hgL.mem t ⟨ht.1, h⟩
    · exact hx
    · exact hgR.mem t ⟨h, ht.2⟩
  have hv : deriv γ x ∈ tangentSubspace hN q :=
    hasDerivAt_mem_tangentSubspace hN hd.hasDerivAt
      (eventually_of_mem (Ioo_mem_nhds (by linarith) (by linarith)) hmemN)
  obtain ⟨η₀, hη₀, σ, hσ, hσx, hσx'⟩ := exists_isGeodesicOn_through hN q hv x
  set G := liftField τ
  set f : ℝ → V × V := fun t => (γ t, deriv γ t)
  set g : ℝ → V × V := fun t => (σ t, deriv σ t)
  have hfx : f x = g x := by simp only [f, g, hσx, hσx', q]
  have hGc : ContDiffAt ℝ 1 G (f x) := contDiffAt_liftField τ hx hq
  have hx₀ : x ∈ Ioo (x - η₀) (x + η₀) := ⟨by linarith, by linarith⟩
  have hσsrc : ∀ᶠ t in 𝓝 x, σ t ∈ τ.φ.source :=
    (hσ.hasDerivAt hx₀).continuousAt.eventually (τ.φ.open_source.mem_nhds (by rw [hσx]; exact hq))
  have hg : ∀ᶠ t in 𝓝 x, HasDerivAt g (G (g t)) t := by
    filter_upwards [hσsrc, Ioo_mem_nhds hx₀.1 hx₀.2] with t h1 h2
    exact hσ.hasDerivAt_lift hN τ h2 h1
  -- continuity of `γ'` at `x`, from the two sides
  have hcont : ContinuousAt (deriv γ) x := by
    obtain ⟨hL1, hL2⟩ := IsPiecewiseSmooth.derivWithin_piece (by linarith : x - r < x) hL
    obtain ⟨hR1, hR2⟩ := IsPiecewiseSmooth.derivWithin_piece (by linarith : x < x + r) hR
    have eL := derivWithin_eq_deriv_of_piece (by linarith : x - r < x)
      (right_mem_Icc.2 (by linarith)) hd
    have eR := derivWithin_eq_deriv_of_piece (by linarith : x < x + r)
      (left_mem_Icc.2 (by linarith)) hd
    refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
    · refine (((hL1.continuousOn x (right_mem_Icc.2 (by linarith))).mono
        Ioc_subset_Icc_self).congr (fun y hy => ?_) eL.symm).mono_of_mem_nhdsWithin
        (Ioc_mem_nhdsLE (by linarith))
      rcases eq_or_lt_of_le hy.2 with rfl | h
      · exact eL.symm
      · exact hL2 ⟨hy.1, h⟩
    · refine (((hR1.continuousOn x (left_mem_Icc.2 (by linarith))).mono
        Ico_subset_Icc_self).congr (fun y hy => ?_) eR.symm).mono_of_mem_nhdsWithin
        (Ico_mem_nhdsGE (by linarith))
      rcases eq_or_lt_of_le hy.1 with rfl | h
      · exact eR.symm
      · exact hR2 ⟨h, hy.2⟩
  have hfc : ContinuousAt f x := hd.continuousAt.prodMk hcont
  have hγsrc : ∀ᶠ t in 𝓝 x, γ t ∈ τ.φ.source :=
    hd.continuousAt.eventually (τ.φ.open_source.mem_nhds hq)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hγsrc
  set r' := min r δ
  have hr' : 0 < r' := lt_min hr hδ
  have hfne : ∀ t ∈ Ioo (x - r') (x + r'), t ≠ x → HasDerivAt f (G (f t)) t := by
    intro t ht hne
    have hsrc : γ t ∈ τ.φ.source := hball t (by
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [ht.1, ht.2, min_le_right r δ])
    rcases lt_or_gt_of_ne hne with h | h
    · exact hgL.hasDerivAt_lift hN τ ⟨by linarith [ht.1, min_le_left r δ], h⟩ hsrc
    · exact hgR.hasDerivAt_lift hN τ ⟨h, by linarith [ht.2, min_le_left r δ]⟩ hsrc
  have hGf : ContinuousAt (fun t => G (f t)) x := hGc.continuousAt.comp hfc
  have hfx' : HasDerivAt f (G (f x)) x := by
    have hR' : HasDerivWithinAt f (G (f x)) (Ici x) x := by
      refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo x (x + r')) (fun t ht => ?_)
        hfc.continuousWithinAt (Ioo_mem_nhdsGT (by linarith)) ?_
      · exact (hfne t ⟨by linarith [ht.1], ht.2⟩ (ne_of_gt ht.1)).differentiableAt
          |>.differentiableWithinAt
      · have hev : (fun t => G (f t)) =ᶠ[𝓝[>] x] deriv f := by
          filter_upwards [Ioo_mem_nhdsGT (show x < x + r' by linarith)] with t ht
          exact (hfne t ⟨by linarith [ht.1], ht.2⟩ (ne_of_gt ht.1)).deriv.symm
        exact (hGf.tendsto.mono_left nhdsWithin_le_nhds).congr' hev
    have hL' : HasDerivWithinAt f (G (f x)) (Iic x) x := by
      refine hasDerivWithinAt_Iic_of_tendsto_deriv (s := Ioo (x - r') x) (fun t ht => ?_)
        hfc.continuousWithinAt (Ioo_mem_nhdsLT (by linarith)) ?_
      · exact (hfne t ⟨ht.1, by linarith [ht.2]⟩ (ne_of_lt ht.2)).differentiableAt
          |>.differentiableWithinAt
      · have hev : (fun t => G (f t)) =ᶠ[𝓝[<] x] deriv f := by
          filter_upwards [Ioo_mem_nhdsLT (show x - r' < x by linarith)] with t ht
          exact (hfne t ⟨ht.1, by linarith [ht.2]⟩ (ne_of_lt ht.2)).deriv.symm
        exact (hGf.tendsto.mono_left nhdsWithin_le_nhds).congr' hev
    have := hL'.union hR'
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  have hf : ∀ᶠ t in 𝓝 x, HasDerivAt f (G (f t)) t := by
    filter_upwards [Ioo_mem_nhds (show x - r' < x by linarith) (show x < x + r' by linarith)]
      with t ht
    rcases eq_or_ne t x with rfl | hne
    · exact hfx'
    · exact hfne t ht hne
  have key := ode_eventuallyEq hGc hf hg hfx
  obtain ⟨η, hη, hEq⟩ := Metric.eventually_nhds_iff_ball.1 key
  refine ⟨min η η₀, lt_min hη hη₀, (hσ.mono isOpen_Ioo (Ioo_subset_Ioo (by
    linarith [min_le_right η η₀]) (by linarith [min_le_right η η₀]))).congr fun t ht => ?_⟩
  have htb : t ∈ ball x η := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, min_le_left η η₀]
  exact (congrArg Prod.fst (hEq t htb)).symm

end Converse

/-! ### Corollary 12.3 -/

/-- **Corollary 12.3** (Milnor p. 73): a path `ω ∈ Ω(N; p, q)` is a critical point of the energy
if and only if it is an (unbroken) geodesic: `C^∞` on all of `[0, 1]` with zero acceleration. -/
theorem corollary_12_3 {c : ℝ → V} {p q : V} (hc : c ∈ pathSpace N p q) :
    IsCriticalPath N c ↔ IsUnbrokenGeodesic hN c := by
  rw [isCriticalPath_iff hN hc]
  refine ⟨fun hcrit => ?_, fun hgeo X _ => hgeo.firstVariation_eq_zero hN X⟩
  obtain ⟨⟨-, -, B, hB⟩, hcN, -, -⟩ := id hc
  -- near each point of `(0, 1)`, `ω` is a geodesic
  have hloc : ∀ x ∈ Ioo (0 : ℝ) 1, ∃ s' : Set ℝ, x ∈ s' ∧ s' ⊆ Ioo 0 1 ∧
      IsGeodesicOn hN c s' := by
    intro x hx
    by_cases hxB : x ∉ B
    · obtain ⟨s, s', hs, hsx, hxs', hs', hBs⟩ := exists_piece_around B hx.1 hx.2 hxB
      refine ⟨Ioo s s', ⟨hsx, hxs'⟩, Ioo_subset_Ioo (by linarith) (by linarith), ?_⟩
      refine isGeodesicOn_of_accel hN ((hB s s' hs (hsx.trans hxs') hs' hBs).mono
        Ioo_subset_Icc_self) (fun t ht => hcN t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
        fun t ht => accel_eq_zero_of_critical hN hc hcrit hB ⟨by linarith [ht.1],
          by linarith [ht.2]⟩ fun htB => hBs t htB ht
    push Not at hxB
    obtain ⟨s, hs, hsx, hBs⟩ := exists_piece_left B hx.1
    obtain ⟨s', hxs', hs', hBs'⟩ := exists_piece_right B hx.2
    set r := min (x - s) (s' - x)
    have hr : 0 < r := lt_min (by linarith) (by linarith)
    have hr1 : r ≤ x - s := min_le_left _ _
    have hr2 : r ≤ s' - x := min_le_right _ _
    have hL := (hB s x hs hsx hx.2.le hBs).mono (Icc_subset_Icc (by linarith) le_rfl)
      (t := Icc (x - r) x)
    have hR := (hB x s' hx.1.le hxs' hs' hBs').mono (Icc_subset_Icc le_rfl (by linarith))
      (t := Icc x (x + r))
    have hgeo : ∀ a b, x - r ≤ a → b ≤ x + r → (∀ y ∈ B, y ∉ Ioo a b) →
        ContDiffOn ℝ ∞ c (Icc a b) → IsGeodesicOn hN c (Ioo a b) := by
      intro a b ha hb hBab hcab
      refine isGeodesicOn_of_accel hN (hcab.mono Ioo_subset_Icc_self)
        (fun t ht => hcN t ⟨by linarith [ht.1], by linarith [ht.2]⟩) fun t ht =>
          accel_eq_zero_of_critical hN hc hcrit hB ⟨by linarith [ht.1], by linarith [ht.2]⟩
            fun htB => hBab t htB ht
    have hgL := hgeo (x - r) x le_rfl (by linarith) (fun y hy hy' => hBs y hy
      ⟨by linarith [hy'.1], hy'.2⟩) hL
    have hgR := hgeo x (x + r) (by linarith) le_rfl (fun y hy hy' => hBs' y hy
      ⟨hy'.1, by linarith [hy'.2]⟩) hR
    -- no corner at `x` (Step 2)
    have hjump := jump_eq_zero_of_critical hN hc hcrit hB hx
    have hdx : DifferentiableAt ℝ c x := by
      have h1 : HasDerivWithinAt c (derivWithin c (Ici x) x) (Ici x) x :=
        (((hR.differentiableOn (by simp)) x (left_mem_Icc.2 (by linarith))).hasDerivWithinAt
          |>.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE (by linarith))).congr_deriv
          (derivWithin_Ici_eq_of_piece (by linarith) (hR.differentiableOn (by simp))).symm
      have h2 : HasDerivWithinAt c (derivWithin c (Iic x) x) (Iic x) x :=
        (((hL.differentiableOn (by simp)) x (right_mem_Icc.2 (by linarith))).hasDerivWithinAt
          |>.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE (by linarith))).congr_deriv
          (derivWithin_Iic_eq_of_piece (by linarith) (hL.differentiableOn (by simp))).symm
      rw [jump, sub_eq_zero] at hjump
      rw [hjump] at h1
      have := h2.union h1
      rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
      exact this.differentiableAt
    obtain ⟨η, hη, hgη⟩ := isGeodesicOn_of_glue hN hr hL hR hgL hgR
      (hcN x (Ioo_subset_Icc_self hx)) hdx
    refine ⟨Ioo (x - min η r) (x + min η r), ⟨by linarith [lt_min hη hr],
      by linarith [lt_min hη hr]⟩, Ioo_subset_Ioo ?_ ?_, hgη.mono isOpen_Ioo
      (Ioo_subset_Ioo (by linarith [min_le_left η r]) (by linarith [min_le_left η r]))⟩
    · linarith [min_le_right η r]
    · linarith [min_le_right η r]
  have hgeo : IsGeodesicOn hN c (Ioo 0 1) := isGeodesicOn_of_locally hN isOpen_Ioo hloc
  refine ⟨fun t ht => ?_, hgeo⟩
  rcases eq_or_lt_of_le ht.1 with rfl | ht0
  · obtain ⟨s', h0s', hs', hBs'⟩ := exists_piece_right B zero_lt_one
    refine ((hB 0 s' le_rfl h0s' hs' hBs') 0 (left_mem_Icc.2 h0s'.le)).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Iio s', isOpen_Iio, h0s', fun y hy => ⟨hy.2.1, hy.1.le⟩⟩
  rcases eq_or_lt_of_le ht.2 with rfl | ht1
  · obtain ⟨s, hs, hs1, hBs⟩ := exists_piece_left B zero_lt_one
    refine ((hB s 1 hs hs1 le_rfl hBs) 1 (right_mem_Icc.2 hs1.le)).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Ioi s, isOpen_Ioi, hs1, fun y hy => ⟨hy.1.le, hy.2.2⟩⟩
  · exact (hgeo.contDiffAt ⟨ht0, ht1⟩).contDiffWithinAt

end Morse
