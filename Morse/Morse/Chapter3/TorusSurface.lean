import Morse.Chapter1.ManifoldSubmanifold
import Milnor.Chapter2.LevelSet
import Milnor.Chapter6.EulerSphere

/-!
Milnor, *Morse Theory*, §1, pp. 1–3 (Diagram 1): the torus `M` tangent to a plane `V`.

# The torus of Diagram 1 as a compact submanifold of `ℝ³`

Milnor's opening example (p. 1) is a torus `M` touching a plane `V`, drawn standing upright in
Diagram 1, with `f : M → ℝ` the height above `V`.  He gives no equations, and he does not say why
`M` is a smooth compact surface.  This file fixes the surface; the height function, its four
critical points and the consequences of §§3 and 5 are `Morse/Chapter3/Torus.lean`.

## The torus

For `0 < r < R`, `Morse.torus R r` is the torus of revolution about the `x₃`-axis, swept out by the
circle of radius `r` whose centre runs along the circle of radius `R` in the plane `x₃ = 0`:
`T = {x ∈ ℝ³ : (√(x₁² + x₂²) − R)² + x₃² = r²}`.  Here `ℝ³` is `EuclideanSpace ℝ (Fin 3)`, and the
coordinates `x₁, x₂, x₃` are written `x 0, x 1, x 2`.  In `Morse/Chapter3/Torus.lean` the "height"
is the coordinate `x₁` shifted by `R + r`, so the axis of revolution is parallel to the plane
`V = {x₁ = −(R + r)}` and `T` stands on `V`, touching it at the single point `(−(R + r), 0, 0)`,
as in Diagram 1.

## The defining function

The function `(√(x₁² + x₂²) − R)² + x₃² − r²` is not differentiable along the `x₃`-axis.  Rather
than work on the open set off the axis, we use that `T` is the zero set of the quartic polynomial
`g(x) = (‖x‖² + R² − r²)² − 4R²(x₁² + x₂²)` (`Morse.Torus.poly`): with `ρ = √(x₁² + x₂²)`,
`g = ((ρ − R)² + x₃² − r²) · ((ρ + R)² + x₃² − r²)` (`Morse.Torus.poly_eq_mul`), and the second
factor is at least `R² − r² > 0` (`Morse.Torus.mem_torus_iff`).

## Main results

* `Morse.Torus.hasFDerivAt_poly`, `Morse.Torus.hessian_poly`: the first and second derivatives
  of `g`, as explicit (bi)linear forms `Morse.Torus.dpoly`, `Morse.Torus.d2poly`.
* `Morse.Torus.dpoly_ne_zero`: `dg_x ≠ 0` at every point of `T`, so `0` is a regular value of `g`
  (`Morse.Torus.isRegularValue_poly1`, for `g` read with values in the model space `ℝ¹`).
* `Morse.isSliceSubmanifold_torus`: **`T` is a submanifold of `ℝ³` of dimension `2`**, in the
  sense of the companion project (`Milnor.IsSliceSubmanifold`, slice charts onto `ℝ² × ℝ¹`), by its
  level set theorem `Milnor.isSliceSubmanifold_preimage`.
* `Morse.isCompact_torus`, `Morse.nonempty_torus`: `T` is compact (`‖x‖ ≤ R + 2r` on `T`) and
  nonempty.
* `Morse.Torus.mem_tangentSubspace_torus_iff`: the tangent plane `T_qT ⊆ ℝ³` is the kernel of
  `dg_q` (Milnor's Lemma 2 of *Topology from the Differentiable Viewpoint*, §2, re-proved for the
  set `T` rather than the preimage `g⁻¹(0)`); `Morse.Torus.finrank_tangentSubspace_torus`: it has
  dimension `2`.
* `Morse.Torus.dpoly_onAxis`, `Morse.Torus.d2poly_onAxis`: `dg` and `d²g` at the points
  `(a, 0, 0)` of the `x₁`-axis, where the critical points of the height function will lie.

## What Milnor leaves implicit

* **Which torus, in which position.**  Diagram 1 shows a torus standing upright on `V`, and the
  whole discussion depends on that position: a torus of revolution lying flat on `V` (axis
  perpendicular to `V`) has its minimum and maximum along two circles, so its height function has
  degenerate critical points, and (2) fails (every nonempty `M^a` short of `M` is an annulus).
  Here the upright torus of revolution is fixed once and for all.  Implicit too is `r < R` (a
  ring torus, which is a smooth surface); it also makes the four critical values
  `0 < 2r < 2R < 2R + 2r` distinct, which (3) and (4) presuppose.
* **That `M` is a smooth compact surface.**  Milnor takes it for granted; here it is the regular
  value theorem applied to `g`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

/-- **The torus of Diagram 1** (Milnor, p. 1): the torus of revolution about the `x₃`-axis with
core radius `R` and tube radius `r`, `{x ∈ ℝ³ : (√(x₁² + x₂²) − R)² + x₃² = r²}`.  (The
coordinates `x₁, x₂, x₃` are `x 0, x 1, x 2`.)  It is a smooth surface when `0 < r < R`
(`Morse.isSliceSubmanifold_torus`). -/
def torus (R r : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | (√(x 0 ^ 2 + x 1 ^ 2) - R) ^ 2 + x 2 ^ 2 = r ^ 2}

namespace Torus

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)
local notation "𝔻" => EuclideanSpace ℝ (Fin 2)
local notation "π" => EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3)

variable {R r : ℝ}

/-! ### The defining polynomial and its derivatives -/

/-- The quadratic part `‖x‖² + R² − r²` of the defining polynomial. -/
def quad (R r : ℝ) (x : 𝔼) : ℝ := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + (R ^ 2 - r ^ 2)

/-- **The defining polynomial** `g(x) = (‖x‖² + R² − r²)² − 4R²(x₁² + x₂²)` of the torus
(`Morse.Torus.mem_torus_iff`). -/
def poly (R r : ℝ) (x : 𝔼) : ℝ := quad R r x ^ 2 - 4 * R ^ 2 * (x 0 ^ 2 + x 1 ^ 2)

/-- The derivative of `quad` at `x`: `v ↦ 2⟪x, v⟫`. -/
def dquad (x : 𝔼) : 𝔼 →L[ℝ] ℝ := (2 * x 0) • π 0 + (2 * x 1) • π 1 + (2 * x 2) • π 2

/-- The derivative of `g` at `x`:
`v ↦ 4 (Q − 2R²)(x₁v₁ + x₂v₂) + 4 Q x₃v₃`, `Q = ‖x‖² + R² − r²` (`Morse.Torus.dpoly_apply`). -/
def dpoly (R r : ℝ) (x : 𝔼) : 𝔼 →L[ℝ] ℝ :=
  (4 * quad R r x * x 0 - 8 * R ^ 2 * x 0) • π 0 + (4 * quad R r x * x 1 - 8 * R ^ 2 * x 1) • π 1 +
    (4 * quad R r x * x 2) • π 2

/-- The second derivative of `g` at `x`, as a bilinear form. -/
def d2poly (R r : ℝ) (x : 𝔼) : 𝔼 →L[ℝ] 𝔼 →L[ℝ] ℝ :=
  ((4 * x 0) • dquad x + (4 * quad R r x - 8 * R ^ 2) • π 0).smulRight (π 0) +
    ((4 * x 1) • dquad x + (4 * quad R r x - 8 * R ^ 2) • π 1).smulRight (π 1) +
    ((4 * x 2) • dquad x + (4 * quad R r x) • π 2).smulRight (π 2)

theorem proj_apply (i : Fin 3) (x : 𝔼) : π i x = x i := rfl

theorem hasFDerivAt_coord (i : Fin 3) (x : 𝔼) : HasFDerivAt (fun y : 𝔼 => y i) (π i) x :=
  (π i).hasFDerivAt

theorem hasFDerivAt_quad (x : 𝔼) : HasFDerivAt (quad R r) (dquad x) x := by
  have h := (((hasFDerivAt_coord 0 x).pow 2).add ((hasFDerivAt_coord 1 x).pow 2)).add
    ((hasFDerivAt_coord 2 x).pow 2) |>.add_const (R ^ 2 - r ^ 2)
  refine h.congr_fderiv ?_
  ext w
  simp [dquad]

/-- **The derivative of the defining polynomial.** -/
theorem hasFDerivAt_poly (x : 𝔼) : HasFDerivAt (poly R r) (dpoly R r x) x := by
  have h := ((hasFDerivAt_quad (R := R) (r := r) x).pow 2).sub
    ((((hasFDerivAt_coord 0 x).pow 2).add ((hasFDerivAt_coord 1 x).pow 2)).const_mul (4 * R ^ 2))
  refine h.congr_fderiv ?_
  ext w
  simp [dpoly, dquad]
  ring

/-- The derivative of a coefficient `4 Q xᵢ − c xᵢ` of `dpoly`. -/
theorem hasFDerivAt_coef (i : Fin 3) (c : ℝ) (x : 𝔼) :
    HasFDerivAt (fun y : 𝔼 => 4 * quad R r y * y i - c * y i)
      ((4 * x i) • dquad x + (4 * quad R r x - c) • π i) x := by
  have h := (((hasFDerivAt_quad (R := R) (r := r) x).const_mul 4).mul (hasFDerivAt_coord i x)).sub
    ((hasFDerivAt_coord i x).const_mul c)
  refine h.congr_fderiv ?_
  ext w
  simp [dquad]
  ring

/-- **The second derivative of the defining polynomial**, as the derivative of `dpoly`. -/
theorem hasFDerivAt_dpoly (x : 𝔼) : HasFDerivAt (dpoly R r) (d2poly R r x) x := by
  have h0 := (hasFDerivAt_coef (R := R) (r := r) 0 (8 * R ^ 2) x).smul_const (π 0)
  have h1 := (hasFDerivAt_coef (R := R) (r := r) 1 (8 * R ^ 2) x).smul_const (π 1)
  have h2 := (hasFDerivAt_coef (R := R) (r := r) 2 0 x).smul_const (π 2)
  have hfun : dpoly R r = fun y : 𝔼 => (4 * quad R r y * y 0 - 8 * R ^ 2 * y 0) • π 0 +
      (4 * quad R r y * y 1 - 8 * R ^ 2 * y 1) • π 1 + (4 * quad R r y * y 2 - 0 * y 2) • π 2 := by
    funext y
    simp [dpoly]
  rw [hfun]
  refine ((h0.add h1).add h2).congr_fderiv ?_
  ext v w
  simp [d2poly]

theorem fderiv_poly : fderiv ℝ (poly R r) = dpoly R r :=
  funext fun x => (hasFDerivAt_poly x).fderiv

/-- **The Hessian of the defining polynomial** is `d2poly`. -/
theorem hessian_poly (x : 𝔼) : hessian (poly R r) x = d2poly R r x := by
  rw [hessian, fderiv_poly]
  exact (hasFDerivAt_dpoly x).fderiv

theorem contDiff_poly : ContDiff ℝ ∞ (poly R r) := by
  unfold poly quad
  fun_prop

theorem dpoly_apply (x w : 𝔼) : dpoly R r x w =
    4 * (quad R r x - 2 * R ^ 2) * (x 0 * w 0 + x 1 * w 1) + 4 * quad R r x * (x 2 * w 2) := by
  simp [dpoly]
  ring

/-! ### The zero set of the polynomial is the torus -/

/-- **The factorization** `g = ((ρ − R)² + x₃² − r²)((ρ + R)² + x₃² − r²)`, `ρ = √(x₁² + x₂²)`. -/
theorem poly_eq_mul (x : 𝔼) : poly R r x =
    ((√(x 0 ^ 2 + x 1 ^ 2) - R) ^ 2 + x 2 ^ 2 - r ^ 2) *
      ((√(x 0 ^ 2 + x 1 ^ 2) + R) ^ 2 + x 2 ^ 2 - r ^ 2) := by
  have h : √(x 0 ^ 2 + x 1 ^ 2) ^ 2 = x 0 ^ 2 + x 1 ^ 2 := Real.sq_sqrt (by positivity)
  unfold poly quad
  linear_combination (-(x 0 ^ 2 + x 1 ^ 2 + √(x 0 ^ 2 + x 1 ^ 2) ^ 2 + 2 * x 2 ^ 2 +
    2 * (R ^ 2 - r ^ 2) - 4 * R ^ 2)) * h

/-- **The torus is the zero set of `g`**: the second factor of `Morse.Torus.poly_eq_mul` is at
least `R² − r² > 0`. -/
theorem mem_torus_iff (hr : 0 < r) (hrR : r < R) {x : 𝔼} : x ∈ torus R r ↔ poly R r x = 0 := by
  rw [poly_eq_mul, torus, mem_ofPred_eq]
  have hpos : 0 < (√(x 0 ^ 2 + x 1 ^ 2) + R) ^ 2 + x 2 ^ 2 - r ^ 2 := by
    have h0 : 0 ≤ √(x 0 ^ 2 + x 1 ^ 2) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (x 2)]
  rw [mul_eq_zero, or_iff_left hpos.ne', sub_eq_zero]

/-- `Q = ‖x‖² + R² − r²` is positive. -/
theorem quad_pos (hr : 0 ≤ r) (hrR : r < R) (x : 𝔼) : 0 < quad R r x := by
  unfold quad
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

/-- **`dg` does not vanish on the torus.**  If it did at `x`, its values at the three basis
vectors would give `Q x₃ = 0` and `(Q − 2R²) x₁ = (Q − 2R²) x₂ = 0`; as `Q > 0`, `x₃ = 0`, and
`g(x) = Q² − 4R²(x₁² + x₂²) = 0` then forces either `x₁ = x₂ = 0`, `Q = 0`, or `Q = 2R²`,
`x₁² + x₂² = R²`, `r = 0`. -/
theorem dpoly_ne_zero (hr : 0 < r) (hrR : r < R) {x : 𝔼} (hx : poly R r x = 0) :
    dpoly R r x ≠ 0 := by
  intro h
  have hQ := quad_pos hr.le hrR x
  have hR0 : 0 < R := hr.trans hrR
  have h0 : quad R r x - 2 * R ^ 2 = 0 ∨ x 0 = 0 := by
    have : dpoly R r x !₂[1, 0, 0] = 0 := by rw [h]; rfl
    simpa [dpoly_apply] using this
  have h1 : quad R r x - 2 * R ^ 2 = 0 ∨ x 1 = 0 := by
    have : dpoly R r x !₂[0, 1, 0] = 0 := by rw [h]; rfl
    simpa [dpoly_apply] using this
  have h2 : quad R r x = 0 ∨ x 2 = 0 := by
    have : dpoly R r x !₂[0, 0, 1] = 0 := by rw [h]; rfl
    simpa [dpoly_apply] using this
  set Q := quad R r x with hQdef
  have hz : x 2 = 0 := h2.resolve_left hQ.ne'
  have hpoly : Q ^ 2 = 4 * R ^ 2 * (x 0 ^ 2 + x 1 ^ 2) := by
    unfold poly at hx
    linarith
  have hQ' : Q = x 0 ^ 2 + x 1 ^ 2 + (R ^ 2 - r ^ 2) := by
    rw [hQdef, quad, hz]
    ring
  by_cases hc : Q - 2 * R ^ 2 = 0
  · have hs : x 0 ^ 2 + x 1 ^ 2 = R ^ 2 := by
      have hR : R ^ 2 ≠ 0 := pow_ne_zero 2 hR0.ne'
      have hQ2 : Q = 2 * R ^ 2 := by linarith
      rw [hQ2] at hpoly
      have : R ^ 2 * (R ^ 2 - (x 0 ^ 2 + x 1 ^ 2)) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hR
      · linarith
    have : r ^ 2 = 0 := by nlinarith
    exact absurd this (by positivity)
  · have hx0 : x 0 = 0 := h0.resolve_left hc
    have hx1 : x 1 = 0 := h1.resolve_left hc
    rw [hx0, hx1] at hpoly
    have : Q = 0 := by nlinarith
    exact absurd this hQ.ne'

/-! ### The torus is a compact submanifold of dimension `2` -/

/-- The defining polynomial, with values in the model space `ℝ¹` (as required by the companion
project's level set theorem and tubular neighbourhood machinery). -/
def poly1 (R r : ℝ) (x : 𝔼) : EuclideanSpace ℝ (Fin 1) := Milnor.Sphere.e1 (poly R r x)

theorem contMDiff_poly1 : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞ (poly1 R r) :=
  contMDiff_iff_contDiff.2
    ((Milnor.Sphere.e1 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).contDiff.comp contDiff_poly)

theorem preimage_poly1 (hr : 0 < r) (hrR : r < R) : poly1 R r ⁻¹' {0} = torus R r := by
  ext x
  simp only [mem_preimage, mem_singleton_iff, poly1, mem_torus_iff hr hrR]
  rw [← Milnor.Sphere.e1.map_zero]
  exact Milnor.Sphere.e1.injective.eq_iff

/-- **`0` is a regular value of the defining polynomial.** -/
theorem isRegularValue_poly1 (hr : 0 < r) (hrR : r < R) :
    Milnor.IsRegularValue 𝓘(ℝ, 𝔼) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (poly1 R r) 0 := by
  intro x hx
  change Surjective (mfderiv _ _ (poly1 R r) x)
  have hx' : poly R r x = 0 := by
    have : x ∈ poly1 R r ⁻¹' {0} := hx
    rwa [preimage_poly1 hr hrR, mem_torus_iff hr hrR] at this
  have h2 : mfderiv 𝓘(ℝ, 𝔼) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (poly1 R r) x =
      (Milnor.Sphere.e1 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).comp (dpoly R r x) := by
    rw [mfderiv_eq_fderiv]
    exact ((Milnor.Sphere.e1 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).hasFDerivAt.comp x
      (hasFDerivAt_poly x)).fderiv
  rw [h2]
  exact Milnor.Sphere.e1.surjective.comp
    ((surjective_iff_ne_zero _).2 (dpoly_ne_zero hr hrR hx'))

end Torus

open Torus

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)
local notation "𝔻" => EuclideanSpace ℝ (Fin 2)

variable {R r : ℝ}

/-- **The torus is a smooth surface in `ℝ³`**: a slice submanifold of dimension `2` (slice charts
onto `ℝ² × ℝ¹`), as the regular level set `g⁻¹(0)` (`Milnor.isSliceSubmanifold_preimage`). -/
theorem isSliceSubmanifold_torus (hr : 0 < r) (hrR : r < R) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼) 𝔻 (EuclideanSpace ℝ (Fin 1)) (torus R r) := by
  rw [← preimage_poly1 hr hrR]
  exact Milnor.isSliceSubmanifold_preimage (Z := 𝔻) (by simp) contMDiff_poly1
    (isRegularValue_poly1 hr hrR)

theorem isClosed_torus (hr : 0 < r) (hrR : r < R) : IsClosed (torus R r) := by
  rw [← preimage_poly1 hr hrR]
  exact isClosed_singleton.preimage contMDiff_poly1.continuous

/-- The torus lies in the ball of radius `R + 2r`. -/
theorem norm_le_of_mem_torus (hr : 0 < r) (hrR : r < R) {x : 𝔼} (hx : x ∈ torus R r) :
    ‖x‖ ≤ R + 2 * r := by
  have hx' : (√(x 0 ^ 2 + x 1 ^ 2) - R) ^ 2 + x 2 ^ 2 = r ^ 2 := hx
  set ρ := √(x 0 ^ 2 + x 1 ^ 2) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ2 : ρ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hn : ‖x‖ ^ 2 = ρ ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, hρ2]
  have hρle : ρ ≤ R + r := by nlinarith [sq_nonneg (x 2)]
  have hz : x 2 ^ 2 ≤ r ^ 2 := by nlinarith [sq_nonneg (ρ - R)]
  have h2 : ‖x‖ ^ 2 ≤ (R + 2 * r) ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg x) (by linarith) two_ne_zero).1 h2

/-- **The torus is compact**: closed and bounded. -/
theorem isCompact_torus (hr : 0 < r) (hrR : r < R) : IsCompact (torus R r) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_torus hr hrR)
    ((Metric.isBounded_closedBall (x := (0 : 𝔼)) (r := R + 2 * r)).subset fun _ hx =>
      mem_closedBall_zero_iff.2 (norm_le_of_mem_torus hr hrR hx))

namespace Torus

/-! ### Points on the `x₁`-axis -/

/-- The point `(a, 0, 0)` of the `x₁`-axis. -/
def onAxis (a : ℝ) : 𝔼 := EuclideanSpace.single 0 a

@[simp] theorem onAxis_apply_zero (a : ℝ) : onAxis a 0 = a := by simp [onAxis]
@[simp] theorem onAxis_apply_one (a : ℝ) : onAxis a 1 = 0 := by simp [onAxis]
@[simp] theorem onAxis_apply_two (a : ℝ) : onAxis a 2 = 0 := by simp [onAxis]

/-- `(a, 0, 0)` lies on the torus iff `(|a| − R)² = r²`. -/
theorem onAxis_mem_iff (a : ℝ) : onAxis a ∈ torus R r ↔ (|a| - R) ^ 2 = r ^ 2 := by
  simp [torus, Real.sqrt_sq_eq_abs]

/-- The four points `(±(R ± r), 0, 0)` lie on the torus. -/
theorem onAxis_mem {a : ℝ} (ha : |a| = R + r ∨ |a| = R - r) : onAxis a ∈ torus R r := by
  rw [onAxis_mem_iff]
  rcases ha with ha | ha <;> rw [ha] <;> ring

/-- At `(a, 0, 0)`, `dg = 4a(a² − R² − r²) dx₁`. -/
theorem dpoly_onAxis (a : ℝ) (w : 𝔼) :
    dpoly R r (onAxis a) w = 4 * a * (a ^ 2 - R ^ 2 - r ^ 2) * w 0 := by
  rw [dpoly_apply]
  simp [quad]
  ring

/-- At `(a, 0, 0)`, for `v` in the plane `x₁ = 0`,
`d²g(v, w) = 4(a² − R² − r²) v₂w₂ + 4(a² + R² − r²) v₃w₃`. -/
theorem d2poly_onAxis (a : ℝ) {v : 𝔼} (hv : v 0 = 0) (w : 𝔼) :
    d2poly R r (onAxis a) v w =
      4 * (a ^ 2 - R ^ 2 - r ^ 2) * (v 1 * w 1) + 4 * (a ^ 2 + R ^ 2 - r ^ 2) * (v 2 * w 2) := by
  simp [d2poly, dquad, quad, hv]
  ring

end Torus

theorem nonempty_torus (hr : 0 < r) (hrR : r < R) : (torus R r).Nonempty :=
  ⟨onAxis (R + r), onAxis_mem (Or.inl (abs_of_pos (by linarith)))⟩

namespace Torus

/-! ### The tangent plane -/

/-- **The tangent plane of the torus has dimension `2`.** -/
theorem finrank_tangentSubspace_torus (hr : 0 < r) (hrR : r < R) (q : torus R r) :
    finrank ℝ (tangentSubspace (isSliceSubmanifold_torus hr hrR) q) = 2 := by
  let _ := (isSliceSubmanifold_torus hr hrR).chartedSpace
  have h : Injective (Milnor.mfd 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) (Subtype.val : torus R r → 𝔼) q) :=
    Milnor.injective_mfderiv_val (isSliceSubmanifold_torus hr hrR) q
  exact (LinearMap.finrank_range_of_inj h).trans (by simp)

/-- **The tangent plane of the torus is the kernel of `dg`**: `w ∈ T_qT ↔ dg_q(w) = 0`.  The
inclusion `⊆` holds because `g` is constant on `T`; both sides have dimension `2`. -/
theorem mem_tangentSubspace_torus_iff (hr : 0 < r) (hrR : r < R) (q : torus R r) (w : 𝔼) :
    w ∈ tangentSubspace (isSliceSubmanifold_torus hr hrR) q ↔ dpoly R r q w = 0 := by
  set hT := isSliceSubmanifold_torus hr hrR
  let _ := hT.chartedSpace
  have := hT.isManifold
  have hcrit : IsCriticalPointM 𝔻 (poly R r ∘ Subtype.val) q := by
    have hconst : poly R r ∘ (Subtype.val : torus R r → 𝔼) = fun _ => 0 :=
      funext fun x => (mem_torus_iff hr hrR).1 x.2
    rw [IsCriticalPointM, hconst]
    exact mfderiv_const
  have hle : tangentSubspace hT q ≤ LinearMap.ker (dpoly R r q : 𝔼 →ₗ[ℝ] ℝ) := by
    intro v hv
    have h := (isCriticalPointM_comp_val_iff_forall_tangent hT
      (hasFDerivAt_poly (R := R) (r := r) q.1).differentiableAt).1 hcrit v hv
    rw [fderiv_poly] at h
    exact h
  have hker : finrank ℝ (LinearMap.ker (dpoly R r q : 𝔼 →ₗ[ℝ] ℝ)) = 2 := by
    have hsurj : Surjective (dpoly R r q) :=
      (surjective_iff_ne_zero _).2 (dpoly_ne_zero hr hrR ((mem_torus_iff hr hrR).1 q.2))
    have h := LinearMap.finrank_range_add_finrank_ker (dpoly R r q : 𝔼 →ₗ[ℝ] ℝ)
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, finrank_euclideanSpace_fin,
      Module.finrank_self] at h
    omega
  have heq := Submodule.eq_of_le_of_finrank_eq hle
    ((finrank_tangentSubspace_torus hr hrR q).trans hker.symm)
  rw [heq]
  rfl

end Torus

end Morse
