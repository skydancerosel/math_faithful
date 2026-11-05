import Morse.Chapter1.Nondegenerate

/-!
Milnor, *Morse Theory*, §2, pp. 8–9.

# Examples of degenerate critical points

After Corollary 2.3 Milnor lists five examples of degenerate critical points of functions on `ℝ`
and `ℝ²`, with pictures of their graphs (paraphrased):

* (a) `f(x) = x³`: the origin is a degenerate critical point;
* (b) `f(x) = e^{−1/x²} sin²(1/x)`: the origin is a degenerate, non-isolated critical point;
* (c) `f(x, y) = x³ − 3xy² = Re (x + iy)³`, the "monkey saddle": the origin is a degenerate
  critical point;
* (d) `f(x, y) = x²`: the critical points, all degenerate, form a line (a submanifold of `ℝ²`);
* (e) `f(x, y) = x²y²`: the critical points, all degenerate, form the union of the two
  coordinate axes, which is not a submanifold of `ℝ²`.

**A slip in (d).**  Milnor says the critical set of `x²` is the `x` axis.  Since `∂f/∂x = 2x` and
`∂f/∂y = 0`, it is the `y` axis `{x = 0}` (`Morse.Examples.isCriticalPoint_sqFst_iff`).

## What is formalized

* (a) and (c): the origin is the only critical point, and the Hessian there is `0`.
* (d) and (e): the critical sets, and that every critical point is degenerate.  The latter is
  the contrapositive of Corollary 2.3 (`Morse.not_isNondegenerate_of_frequently`: a critical
  point which is a limit of other critical points is degenerate), which is exactly how the
  pictures make the point.
* Not formalized: example (b), whose smoothness at `0` needs the flatness of `e^{−1/x²}` against
  the polynomial growth of the derivatives of `sin²(1/x)` (degeneracy and non-isolatedness would
  then follow as in (d): the points `1/(kπ)` are minima, hence critical); and the
  (non-)submanifold claims in (d) and (e).
-/

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Morse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Contrapositive of Corollary 2.3**: if `f` is `C²` at `p` and `p` is a limit of critical
points `x ≠ p`, then the Hessian of `f` at `p` is degenerate. -/
theorem not_isNondegenerate_of_frequently [FiniteDimensional ℝ E] {f : E → ℝ} {p : E}
    (hf : ContDiffAt ℝ 2 f p) (h : ∃ᶠ x in 𝓝[≠] p, IsCriticalPoint f x) :
    ¬ IsNondegenerate (hessian f p) := fun hnd =>
  h (eventually_not_isCriticalPoint hf hnd)

/-- If a property holds along a line through `p`, it holds at points `≠ p` arbitrarily close to
`p`. -/
theorem frequently_of_line {P : E → Prop} {p v : E} (hv : v ≠ 0) (h : ∀ t : ℝ, P (p + t • v)) :
    ∃ᶠ x in 𝓝[≠] p, P x := by
  have hc : Continuous fun t : ℝ => p + t • v :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun t : ℝ => p + t • v) (𝓝[≠] 0) (𝓝[≠] p) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := hc.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [mem_compl_iff, mem_singleton_iff, add_eq_left, smul_eq_zero, not_or] at ht ⊢
      exact ⟨ht, hv⟩
  exact ht.frequently (Eventually.frequently (Eventually.of_forall h))

namespace Examples

local notation "fst" => ContinuousLinearMap.fst ℝ ℝ ℝ
local notation "snd" => ContinuousLinearMap.snd ℝ ℝ ℝ

/-! ### (a) `f(x) = x³` -/

theorem hasFDerivAt_cube (x : ℝ) :
    HasFDerivAt (fun x : ℝ => x ^ 3) ((3 * x ^ 2) • ContinuousLinearMap.id ℝ ℝ) x := by
  refine (hasDerivAt_pow 3 x).hasFDerivAt.congr_fderiv ?_
  ext
  simp

theorem isCriticalPoint_cube_iff (x : ℝ) : IsCriticalPoint (fun x : ℝ => x ^ 3) x ↔ x = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) ((hasFDerivAt_cube x).unique h)
    simpa using h1
  · rintro rfl
    simpa [IsCriticalPoint] using hasFDerivAt_cube 0

theorem hessian_cube : hessian (fun x : ℝ => x ^ 3) 0 = 0 := by
  have h1 : fderiv ℝ (fun x : ℝ => x ^ 3) = fun x => (3 * x ^ 2) • ContinuousLinearMap.id ℝ ℝ :=
    funext fun x => (hasFDerivAt_cube x).fderiv
  have h2 : HasFDerivAt (fun x : ℝ => (3 * x ^ 2) • ContinuousLinearMap.id ℝ ℝ)
      (0 : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) 0 := by
    refine (((hasDerivAt_pow 2 (0 : ℝ)).const_mul (3 : ℝ)).hasFDerivAt.smul_const
      (ContinuousLinearMap.id ℝ ℝ)).congr_fderiv ?_
    ext
    simp
  rw [hessian, h1, h2.fderiv]

/-- **Example (a)**: the origin is a degenerate critical point of `x ↦ x³`. -/
theorem cube_degenerate :
    IsCriticalPoint (fun x : ℝ => x ^ 3) 0 ∧
      ¬ IsNondegenerate (hessian (fun x : ℝ => x ^ 3) 0) := by
  refine ⟨(isCriticalPoint_cube_iff 0).2 rfl, fun h => ?_⟩
  rw [hessian_cube, isNondegenerate_iff] at h
  exact one_ne_zero (h 1 fun w => by simp)

/-! ### (c) The monkey saddle `f(x, y) = x³ − 3xy²` -/

/-- The monkey saddle `x³ − 3xy²`. -/
def monkey (p : ℝ × ℝ) : ℝ := p.1 ^ 3 - 3 * p.1 * p.2 ^ 2

theorem hasFDerivAt_monkey (p : ℝ × ℝ) :
    HasFDerivAt monkey ((3 * p.1 ^ 2 - 3 * p.2 ^ 2) • fst - (6 * p.1 * p.2) • snd) p := by
  have h1 := (hasFDerivAt_fst (p := p) (𝕜 := ℝ)).pow 3
  have h2 := ((hasFDerivAt_fst (p := p) (𝕜 := ℝ)).const_mul 3).mul
    ((hasFDerivAt_snd (p := p) (𝕜 := ℝ)).pow 2)
  refine (h1.sub h2).congr_fderiv ?_
  ext <;> simp <;> ring

theorem isCriticalPoint_monkey_iff (p : ℝ × ℝ) : IsCriticalPoint monkey p ↔ p = 0 := by
  constructor
  · intro h
    have h1 := (hasFDerivAt_monkey p).unique h
    have ha := congrArg (fun T : ℝ × ℝ →L[ℝ] ℝ => T (1, 0)) h1
    have hb := congrArg (fun T : ℝ × ℝ →L[ℝ] ℝ => T (0, 1)) h1
    simp only [sub_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one, mul_zero,
      sub_zero, zero_sub, zero_apply, neg_eq_zero] at ha hb
    have hxy : p.1 * p.2 = 0 := by linarith
    have h4 : p.1 ^ 4 = 0 := by nlinarith
    have hx : p.1 = 0 := pow_eq_zero_iff (by norm_num) |>.1 h4
    have hy : p.2 = 0 := by
      rw [hx] at ha
      exact pow_eq_zero_iff (two_ne_zero) |>.1 (by linarith)
    exact Prod.ext hx hy
  · rintro rfl
    simpa [IsCriticalPoint] using hasFDerivAt_monkey 0

theorem hessian_monkey : hessian monkey 0 = 0 := by
  have h1 : fderiv ℝ monkey = fun p => (3 * p.1 ^ 2 - 3 * p.2 ^ 2) • fst - (6 * p.1 * p.2) • snd :=
    funext fun p => (hasFDerivAt_monkey p).fderiv
  have ha : HasFDerivAt (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - 3 * p.2 ^ 2) (0 : ℝ × ℝ →L[ℝ] ℝ) 0 := by
    refine ((((hasFDerivAt_fst (p := (0 : ℝ × ℝ)) (𝕜 := ℝ)).pow 2).const_mul 3).sub
      (((hasFDerivAt_snd (p := (0 : ℝ × ℝ)) (𝕜 := ℝ)).pow 2).const_mul 3)).congr_fderiv ?_
    ext <;> simp
  have hb : HasFDerivAt (fun p : ℝ × ℝ => 6 * p.1 * p.2) (0 : ℝ × ℝ →L[ℝ] ℝ) 0 := by
    refine (((hasFDerivAt_fst (p := (0 : ℝ × ℝ)) (𝕜 := ℝ)).const_mul 6).mul
      (hasFDerivAt_snd (p := (0 : ℝ × ℝ)) (𝕜 := ℝ))).congr_fderiv ?_
    ext <;> simp
  have h2 := (ha.smul_const fst).sub (hb.smul_const snd)
  rw [hessian, h1]
  exact h2.fderiv.trans (by simp)

/-- **Example (c)**: the origin is a degenerate critical point of the monkey saddle. -/
theorem monkey_degenerate : IsCriticalPoint monkey 0 ∧ ¬ IsNondegenerate (hessian monkey 0) := by
  refine ⟨(isCriticalPoint_monkey_iff 0).2 rfl, fun h => ?_⟩
  rw [hessian_monkey, isNondegenerate_iff] at h
  have := h (1, 0) fun w => by simp
  simp at this

/-! ### (d) `f(x, y) = x²` -/

/-- `f(x, y) = x²`. -/
def sqFst (p : ℝ × ℝ) : ℝ := p.1 ^ 2

theorem hasFDerivAt_sqFst (p : ℝ × ℝ) : HasFDerivAt sqFst ((2 * p.1) • fst) p := by
  refine ((hasFDerivAt_fst (p := p) (𝕜 := ℝ)).pow 2).congr_fderiv ?_
  ext <;> simp

/-- **Example (d)**: the critical set of `x²` is the `y` axis `{x = 0}` (Milnor says "the `x`
axis"). -/
theorem isCriticalPoint_sqFst_iff (p : ℝ × ℝ) : IsCriticalPoint sqFst p ↔ p.1 = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun T : ℝ × ℝ →L[ℝ] ℝ => T (1, 0)) ((hasFDerivAt_sqFst p).unique h)
    simpa using h1
  · intro h
    simpa [IsCriticalPoint, h] using hasFDerivAt_sqFst p

/-- **Example (d)**: every critical point of `x²` is degenerate. -/
theorem not_isNondegenerate_sqFst {p : ℝ × ℝ} (hp : IsCriticalPoint sqFst p) :
    ¬ IsNondegenerate (hessian sqFst p) := by
  have hp1 := (isCriticalPoint_sqFst_iff p).1 hp
  have hf : ContDiffAt ℝ 2 sqFst p := (contDiff_fst.pow 2).contDiffAt
  refine not_isNondegenerate_of_frequently hf
    (frequently_of_line (v := ((0 : ℝ), (1 : ℝ))) (by simp) fun t => ?_)
  rw [isCriticalPoint_sqFst_iff]
  simp [hp1]

/-! ### (e) `f(x, y) = x²y²` -/

/-- `f(x, y) = x²y²`. -/
def sqMul (p : ℝ × ℝ) : ℝ := p.1 ^ 2 * p.2 ^ 2

theorem hasFDerivAt_sqMul (p : ℝ × ℝ) :
    HasFDerivAt sqMul ((2 * p.1 * p.2 ^ 2) • fst + (2 * p.1 ^ 2 * p.2) • snd) p := by
  refine (((hasFDerivAt_fst (p := p) (𝕜 := ℝ)).pow 2).mul
    ((hasFDerivAt_snd (p := p) (𝕜 := ℝ)).pow 2)).congr_fderiv ?_
  ext <;> simp <;> ring

/-- **Example (e)**: the critical set of `x²y²` is the union of the two axes. -/
theorem isCriticalPoint_sqMul_iff (p : ℝ × ℝ) : IsCriticalPoint sqMul p ↔ p.1 = 0 ∨ p.2 = 0 := by
  constructor
  · intro h
    have h1 := (hasFDerivAt_sqMul p).unique h
    have ha := congrArg (fun T : ℝ × ℝ →L[ℝ] ℝ => T (1, 0)) h1
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one, mul_zero,
      add_zero, zero_apply] at ha
    by_contra hne
    rw [not_or] at hne
    have : 2 * p.1 * p.2 ^ 2 ≠ 0 := by
      have := hne.1; have := hne.2; positivity
    exact this ha
  · rintro (h | h)
    · simpa [IsCriticalPoint, h] using hasFDerivAt_sqMul p
    · simpa [IsCriticalPoint, h] using hasFDerivAt_sqMul p

/-- **Example (e)**: every critical point of `x²y²` is degenerate. -/
theorem not_isNondegenerate_sqMul {p : ℝ × ℝ} (hp : IsCriticalPoint sqMul p) :
    ¬ IsNondegenerate (hessian sqMul p) := by
  have hf : ContDiffAt ℝ 2 sqMul p := ((contDiff_fst.pow 2).mul (contDiff_snd.pow 2)).contDiffAt
  refine not_isNondegenerate_of_frequently hf ?_
  rcases (isCriticalPoint_sqMul_iff p).1 hp with h | h
  · refine frequently_of_line (v := ((0 : ℝ), (1 : ℝ))) (by simp) fun t => ?_
    rw [isCriticalPoint_sqMul_iff]
    left
    simp [h]
  · refine frequently_of_line (v := ((1 : ℝ), (0 : ℝ))) (by simp) fun t => ?_
    rw [isCriticalPoint_sqMul_iff]
    right
    simp [h]

end Examples

end Morse
