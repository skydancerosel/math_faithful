import Milnor.Chapter5.HairyBall
import Milnor.Chapter2.Corestrict

/-!
# The Hopf fibration (Milnor §8, Problem 15)

Milnor: "The Hopf fibration `π : S³ → S²` is defined by
`π(x₁, x₂, x₃, x₄) = h⁻¹((x₁ + i x₂)/(x₃ + i x₄))` where `h` denotes stereographic projection to
the complex plane."

With `z₁ = x₀ + i x₁`, `z₂ = x₂ + i x₃` (coordinates `0, …, 3`) and
`h⁻¹(w) = (2 Re w, 2 Im w, |w|² − 1)/(|w|² + 1)` this is the quadratic map
`π(z₁, z₂) = (2 z₁ z̄₂, |z₁|² − |z₂|²)`.

* `hopfPoly : ℝ⁴ → ℝ³`, the polynomial map, with `‖hopfPoly x‖ = ‖x‖²`;
* `hopfMap : S³ → S²`, smooth (`contMDiff_hopfMap`), agreeing with Milnor's formula
  (`hopfMap_eq_milnor`, `hopfMap_eq_top`);
* `isRegularValue_hopfMap`: every point of `S²` is a regular value.  The derivative
  `D = d(hopfPoly)ₓ` satisfies `D Dᵀ = 4‖x‖²`, and `Dᵀ u ⊥ x` when `u ⊥ π(x)`, so
  `(1/4) Dᵀ u` is a tangent vector of `S³` at `x` mapped to `u`;
* the fibres over `(±1, 0, 0)` (`hopfMap_eq_e0_iff`, `hopfMap_eq_neg_e0_iff`), the stereographic
  projection `stereoTop` from `(0, 0, 0, 1)`, and the unique pair of points of these fibres whose
  projections differ by a positive multiple of `(0, −1, 0)` (`hopf_link_pair_iff`);
* the explicit tangent data at this pair and the vector fields `hopfI`, `hopfJ`, `hopfK`
  (left multiplication by the quaternions `i, j, k`), used to compute the Hopf invariant.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Problems

open Sphere

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

/-- Evaluation of the coordinates of explicit vectors. -/
local macro "vec_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply,
    PiLp.zero_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons] $[$loc]?)

/-! ### Coordinates -/

private theorem inner4 (x y : 𝔼 4) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply, conj_trivial]
  ring

private theorem inner3 (x y : 𝔼 3) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

private theorem normSq4 (x : 𝔼 4) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]

private theorem normSq3 (x : 𝔼 3) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

private theorem sph3 (x : Sph 3) : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 + x.1 3 ^ 2 = 1 := by
  rw [← normSq4, (mem_iff_norm).1 x.2, one_pow]

/-! ### The polynomial map and the Hopf fibration -/

/-- The polynomial map `ℝ⁴ → ℝ³`, `(2(x₀x₂ + x₁x₃), 2(x₁x₂ − x₀x₃), x₀² + x₁² − x₂² − x₃²)`. -/
def hopfPoly (x : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 3) :=
  !₂[2 * (x 0 * x 2 + x 1 * x 3), 2 * (x 1 * x 2 - x 0 * x 3),
    x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2]

theorem contDiff_hopfPoly : ContDiff ℝ ∞ hopfPoly := by
  have h : ∀ j : Fin 4, ContDiff ℝ ∞ fun x : 𝔼 4 => x j := fun j =>
    contDiff_piLp_apply (p := 2)
  refine contDiff_piLp' (p := 2) fun i => ?_
  fin_cases i
  · exact contDiff_const.mul (((h 0).mul (h 2)).add ((h 1).mul (h 3)))
  · exact contDiff_const.mul (((h 1).mul (h 2)).sub ((h 0).mul (h 3)))
  · exact ((((h 0).pow 2).add ((h 1).pow 2)).sub ((h 2).pow 2)).sub ((h 3).pow 2)

/-- `‖hopfPoly x‖ = ‖x‖²` (so it maps `S³` to `S²`). -/
theorem norm_hopfPoly (x : EuclideanSpace ℝ (Fin 4)) : ‖hopfPoly x‖ = ‖x‖ ^ 2 := by
  have h : ‖hopfPoly x‖ ^ 2 = (‖x‖ ^ 2) ^ 2 := by
    rw [normSq3, normSq4]
    simp only [hopfPoly]
    vec_simp
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

theorem hopfPoly_mem_sph (x : Sph 3) : hopfPoly x.1 ∈ Sph 2 := by
  rw [mem_iff_norm, norm_hopfPoly, (mem_iff_norm).1 x.2, one_pow]

/-- **The Hopf fibration.** -/
def hopfMap (x : Sph 3) : Sph 2 := ⟨hopfPoly x.1, hopfPoly_mem_sph x⟩

theorem hopfMap_val (x : Sph 3) : (hopfMap x).1 = hopfPoly x.1 := rfl

theorem contMDiff_hopfMap :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ hopfMap :=
  (sphS 2).contMDiff_codRestrict (F := fun x : Sph 3 => hopfPoly x.1)
    (contDiff_hopfPoly.contMDiff.comp contMDiff_val) hopfPoly_mem_sph

/-! ### Milnor's formula -/

/-- Inverse stereographic projection `ℂ → S² ⊆ ℝ³` from `(0, 0, 1)`:
`h⁻¹(w) = (2 Re w, 2 Im w, |w|² − 1)/(|w|² + 1)`. -/
def invStereoC (w : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  (Complex.normSq w + 1)⁻¹ • !₂[2 * w.re, 2 * w.im, Complex.normSq w - 1]

/-- **Agreement with Milnor's formula**, where `x₃ + i x₄ ≠ 0` (1-indexed), i.e. `z₂ ≠ 0`:
`π(x) = h⁻¹(z₁ / z₂)` with `h⁻¹(w) = (2 Re w, 2 Im w, |w|² − 1)/(|w|² + 1)`. -/
theorem hopfMap_eq_milnor (x : Sph 3) (hx : (⟨x.1 2, x.1 3⟩ : ℂ) ≠ 0) :
    (hopfMap x).1 = invStereoC (⟨x.1 0, x.1 1⟩ / ⟨x.1 2, x.1 3⟩) := by
  have hs := sph3 x
  have hD : x.1 2 ^ 2 + x.1 3 ^ 2 ≠ 0 := by
    have h := Complex.normSq_pos.2 hx
    rw [Complex.normSq_mk] at h
    nlinarith
  have hre : (⟨x.1 0, x.1 1⟩ / ⟨x.1 2, x.1 3⟩ : ℂ).re =
      (x.1 0 * x.1 2 + x.1 1 * x.1 3) / (x.1 2 ^ 2 + x.1 3 ^ 2) := by
    rw [Complex.div_re, Complex.normSq_mk]
    field_simp
  have him : (⟨x.1 0, x.1 1⟩ / ⟨x.1 2, x.1 3⟩ : ℂ).im =
      (x.1 1 * x.1 2 - x.1 0 * x.1 3) / (x.1 2 ^ 2 + x.1 3 ^ 2) := by
    rw [Complex.div_im, Complex.normSq_mk]
    field_simp
  have hns : Complex.normSq (⟨x.1 0, x.1 1⟩ / ⟨x.1 2, x.1 3⟩ : ℂ) =
      (x.1 0 ^ 2 + x.1 1 ^ 2) / (x.1 2 ^ 2 + x.1 3 ^ 2) := by
    rw [Complex.normSq_div, Complex.normSq_mk, Complex.normSq_mk]
    ring
  have hinv : ((x.1 0 ^ 2 + x.1 1 ^ 2) / (x.1 2 ^ 2 + x.1 3 ^ 2) + 1)⁻¹ =
      x.1 2 ^ 2 + x.1 3 ^ 2 := by
    rw [inv_eq_iff_eq_inv]
    field_simp
    linear_combination hs
  unfold invStereoC
  rw [hre, him, hns, hinv, hopfMap_val]
  ext i
  fin_cases i
  · simp only [hopfPoly]
    vec_simp
    field_simp
  · simp only [hopfPoly]
    vec_simp
    field_simp
  · simp only [hopfPoly]
    vec_simp
    field_simp
    ring

/-- Where `z₂ = 0`, `π(x) = (0, 0, 1)`, the point `h⁻¹(∞)`. -/
theorem hopfMap_eq_top (x : Sph 3) (hx : x.1 2 = 0 ∧ x.1 3 = 0) :
    (hopfMap x).1 = !₂[0, 0, 1] := by
  have hs := sph3 x
  rw [hx.1, hx.2] at hs
  rw [hopfMap_val]
  ext i
  fin_cases i
  · simp only [hopfPoly]
    vec_simp
    rw [hx.1, hx.2]
    ring
  · simp only [hopfPoly]
    vec_simp
    rw [hx.1, hx.2]
    ring
  · simp only [hopfPoly]
    vec_simp
    rw [hx.1, hx.2]
    linear_combination hs

/-! ### The derivative of `hopfPoly` and regular values -/

/-- The derivative of `hopfPoly`, bilinear in `x` and `v`. -/
theorem hopfPoly_fderiv_apply (x v : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ hopfPoly x v = !₂[2 * (v 0 * x 2 + x 0 * v 2 + v 1 * x 3 + x 1 * v 3),
      2 * (v 1 * x 2 + x 1 * v 2 - v 0 * x 3 - x 0 * v 3),
      2 * (x 0 * v 0 + x 1 * v 1 - x 2 * v 2 - x 3 * v 3)] := by
  have h : ∀ j : Fin 4, HasFDerivAt (fun y : 𝔼 4 => y j)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) j) x :=
    fun j => PiLp.hasFDerivAt_apply 2 x j
  have hf : hopfPoly = fun y : 𝔼 4 =>
      (2 * (y 0 * y 2 + y 1 * y 3)) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
      (2 * (y 1 * y 2 - y 0 * y 3)) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) +
      (y 0 * y 0 + y 1 * y 1 - y 2 * y 2 - y 3 * y 3) •
        EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
    funext y
    ext i
    fin_cases i
    · simp [hopfPoly]
    · simp [hopfPoly]
    · simp [hopfPoly]; ring
  have hd := ((((((h 0).mul (h 2)).add ((h 1).mul (h 3))).const_mul 2).smul_const
      (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))).add
    (((((h 1).mul (h 2)).sub ((h 0).mul (h 3))).const_mul 2).smul_const
      (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)))).add
    ((((((h 0).mul (h 0)).add ((h 1).mul (h 1))).sub ((h 2).mul (h 2))).sub
      ((h 3).mul (h 3))).smul_const (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)))
  have hd' := hd.congr_of_eventuallyEq (f₁ := hopfPoly)
    (by rw [hf]; exact Filter.EventuallyEq.rfl)
  rw [hd'.fderiv]
  ext i
  fin_cases i
  · simp; ring
  · simp; ring
  · simp; ring

/-- `Dₓᵀ u`, the transpose of `D = d(hopfPoly)ₓ` applied to `u`. -/
private def hopfAdj (x : 𝔼 4) (u : 𝔼 3) : 𝔼 4 :=
  !₂[2 * (x 2 * u 0 - x 3 * u 1 + x 0 * u 2), 2 * (x 3 * u 0 + x 2 * u 1 + x 1 * u 2),
    2 * (x 0 * u 0 + x 1 * u 1 - x 2 * u 2), 2 * (x 1 * u 0 - x 0 * u 1 - x 3 * u 2)]

private theorem inner_hopfAdj (x : 𝔼 4) (u : 𝔼 3) :
    ⟪x, hopfAdj x u⟫ = 2 * ⟪hopfPoly x, u⟫ := by
  rw [inner4, inner3]
  simp only [hopfAdj, hopfPoly]
  vec_simp
  ring

/-- `D Dᵀ = 4 ‖x‖²`. -/
private theorem fderiv_hopfAdj (x : 𝔼 4) (u : 𝔼 3) :
    fderiv ℝ hopfPoly x (hopfAdj x u) = (4 * ‖x‖ ^ 2) • u := by
  rw [hopfPoly_fderiv_apply, normSq4]
  ext i
  fin_cases i <;>
  · simp only [hopfAdj]
    vec_simp
    ring

/-- The chain rule `dι ∘ dπ = D(hopfPoly) ∘ dι`. -/
theorem mfd_val_comp_hopfMap (x : Sph 3) :
    (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 + 1)))
        (Subtype.val : Sph 2 → EuclideanSpace ℝ (Fin (2 + 1))) (hopfMap x)).comp
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) hopfMap x) =
      (fderiv ℝ hopfPoly x.1).comp
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (3 + 1)))
          (Subtype.val : Sph 3 → EuclideanSpace ℝ (Fin (3 + 1))) x) := by
  have hπ : MDifferentiableAt 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap x :=
    contMDiff_hopfMap.mdifferentiableAt (by simp)
  have hv2 : MDifferentiableAt 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1))
      (hopfMap x) := contMDiff_val.mdifferentiableAt (by simp)
  have hv3 : MDifferentiableAt 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) x :=
    contMDiff_val.mdifferentiableAt (by simp)
  have h1 := (hasMFDerivAt_mfd hv2).comp x (hasMFDerivAt_mfd hπ)
  have hP : HasMFDerivAt 𝓘(ℝ, 𝔼 (3 + 1)) 𝓘(ℝ, 𝔼 (2 + 1)) hopfPoly x.1
      (fderiv ℝ hopfPoly x.1) :=
    (contDiff_hopfPoly.differentiable (by simp) x.1).hasFDerivAt.hasMFDerivAt
  have h2 := hP.comp x (hasMFDerivAt_mfd hv3)
  have h3 : (Subtype.val ∘ hopfMap : Sph 3 → 𝔼 (2 + 1)) = hopfPoly ∘ Subtype.val := rfl
  rw [h3] at h1
  exact hasMFDerivAt_unique h1 h2

/-- **Every point of `S²` is a regular value of the Hopf fibration.** -/
theorem isRegularValue_hopfMap (y : Sph 2) :
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) hopfMap y := by
  intro x _
  change Function.Surjective (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap x)
  intro t
  -- `u = dι t` is tangent to `S²` at `π x`
  obtain ⟨u, hu_def⟩ : ∃ u, mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1))
      (hopfMap x) t = u := ⟨_, rfl⟩
  have hu : ⟪(hopfMap x).1, u⟫ = 0 := by
    have h5 : fderiv ℝ sphG (hopfMap x).1 u = 0 := by
      rw [← mfderiv_eq_fderiv]
      exact (mem_range_mfderiv_val_iff (finrank_Z_add hE hZ) contMDiff_sphG isRegularValue_sphG
        (hopfMap x) u).1 ⟨t, hu_def⟩
    rw [fderiv_sphG] at h5
    linarith
  -- `v = Dᵀ u / 4` is tangent to `S³` at `x`, and `D v = u`
  have hv : fderiv ℝ sphG x.1 (((1 : ℝ) / 4) • hopfAdj x.1 u) = 0 := by
    rw [fderiv_sphG, inner_smul_right, inner_hopfAdj, ← hopfMap_val, hu]
    ring
  obtain ⟨s, hs⟩ := (mem_range_mfderiv_val_iff (finrank_Z_add hE hZ) contMDiff_sphG
    isRegularValue_sphG x (((1 : ℝ) / 4) • hopfAdj x.1 u)).2 (by rw [mfderiv_eq_fderiv]; exact hv)
  have hs' : mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) x s =
      ((1 : ℝ) / 4) • hopfAdj x.1 u := hs
  refine ⟨s, injective_mfderiv_val (sphS 2) (hopfMap x) ?_⟩
  have h4 : mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1)) (hopfMap x)
      (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap x s) = fderiv ℝ hopfPoly x.1
        (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 (3 + 1)) (Subtype.val : Sph 3 → 𝔼 (3 + 1)) x s) :=
    DFunLike.congr_fun (mfd_val_comp_hopfMap x) s
  have key : mfd 𝓘(ℝ, 𝔼 2) 𝓘(ℝ, 𝔼 (2 + 1)) (Subtype.val : Sph 2 → 𝔼 (2 + 1)) (hopfMap x)
      (mfd 𝓘(ℝ, 𝔼 3) 𝓘(ℝ, 𝔼 2) hopfMap x s) = u := by
    rw [h4, hs', map_smul, fderiv_hopfAdj, (mem_iff_norm).1 x.2, smul_smul]
    norm_num
  exact key.trans hu_def.symm

/-! ### Two fibres -/

/-- The fibres over `(1, 0, 0)` and `(−1, 0, 0)`: `z₁ = z₂` and `z₁ = −z₂`. -/
theorem hopfMap_eq_e0_iff (x : Sph 3) :
    (hopfMap x).1 = !₂[1, 0, 0] ↔ x.1 2 = x.1 0 ∧ x.1 3 = x.1 1 := by
  have hs := sph3 x
  rw [hopfMap_val]
  constructor
  · intro h
    have h0 : 2 * (x.1 0 * x.1 2 + x.1 1 * x.1 3) = 1 := by
      have := congrArg (fun v : 𝔼 3 => v 0) h
      simpa [hopfPoly] using this
    have ha : (x.1 0 - x.1 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x.1 0 - x.1 2), sq_nonneg (x.1 1 - x.1 3)]
    have hb : (x.1 1 - x.1 3) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x.1 0 - x.1 2), sq_nonneg (x.1 1 - x.1 3)]
    constructor
    · linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 ha]
    · linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 hb]
  · rintro ⟨h2, h3⟩
    rw [h2, h3] at hs
    ext i
    fin_cases i
    · simp only [hopfPoly]
      vec_simp
      rw [h2, h3]
      linear_combination hs
    · simp only [hopfPoly]
      vec_simp
      rw [h2, h3]
      ring
    · simp only [hopfPoly]
      vec_simp
      rw [h2, h3]
      ring

theorem hopfMap_eq_neg_e0_iff (x : Sph 3) :
    (hopfMap x).1 = !₂[-1, 0, 0] ↔ x.1 2 = -x.1 0 ∧ x.1 3 = -x.1 1 := by
  have hs := sph3 x
  rw [hopfMap_val]
  constructor
  · intro h
    have h0 : 2 * (x.1 0 * x.1 2 + x.1 1 * x.1 3) = -1 := by
      have := congrArg (fun v : 𝔼 3 => v 0) h
      simpa [hopfPoly] using this
    have ha : (x.1 0 + x.1 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x.1 0 + x.1 2), sq_nonneg (x.1 1 + x.1 3)]
    have hb : (x.1 1 + x.1 3) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x.1 0 + x.1 2), sq_nonneg (x.1 1 + x.1 3)]
    constructor
    · linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 ha]
    · linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 hb]
  · rintro ⟨h2, h3⟩
    rw [h2, h3] at hs
    ext i
    fin_cases i
    · simp only [hopfPoly]
      vec_simp
      rw [h2, h3]
      linear_combination -hs
    · simp only [hopfPoly]
      vec_simp
      rw [h2, h3]
      ring
    · simp only [hopfPoly]
      vec_simp
      rw [h2, h3]
      ring

/-! ### Stereographic projection from `e₃` and the linking pair -/

/-- Stereographic projection from `e₃ = (0,0,0,1)` onto the first three coordinates. -/
def stereoTop (x : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 3) :=
  (1 - x 3)⁻¹ • !₂[x 0, x 1, x 2]

theorem contDiffAt_stereoTop {x : EuclideanSpace ℝ (Fin 4)} (hx : x 3 ≠ 1) :
    ContDiffAt ℝ ∞ stereoTop x := by
  have h : ∀ j : Fin 4, ContDiff ℝ ∞ fun x : 𝔼 4 => x j := fun j =>
    contDiff_piLp_apply (p := 2)
  have h1 : ContDiffAt ℝ ∞ (fun y : 𝔼 4 => (1 - y 3)⁻¹) x :=
    (contDiffAt_const.sub (h 3).contDiffAt).inv (sub_ne_zero.2 (Ne.symm hx))
  have h2 : ContDiff ℝ ∞ (fun y : 𝔼 4 => (!₂[y 0, y 1, y 2] : 𝔼 3)) := by
    refine contDiff_piLp' (p := 2) fun i => ?_
    fin_cases i
    · exact h 0
    · exact h 1
    · exact h 2
  exact h1.smul h2.contDiffAt

/-- The derivative of `stereoTop` where `x 3 ≠ 1`. -/
theorem stereoTop_fderiv_apply {x : EuclideanSpace ℝ (Fin 4)} (hx : x 3 ≠ 1)
    (v : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ stereoTop x v =
      (1 - x 3)⁻¹ • !₂[v 0, v 1, v 2] + (v 3 / (1 - x 3) ^ 2) • !₂[x 0, x 1, x 2] := by
  have h : ∀ j : Fin 4, HasFDerivAt (fun y : 𝔼 4 => y j)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) j) x :=
    fun j => PiLp.hasFDerivAt_apply 2 x j
  have hne : (1 - x 3) ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hf : stereoTop = fun y : 𝔼 4 =>
      (1 - y 3)⁻¹ • (y 0 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
        y 1 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) +
        y 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by
    funext y
    ext i
    fin_cases i <;> simp [stereoTop]
  have hc := (hasFDerivAt_inv hne).comp x ((hasFDerivAt_const (1 : ℝ) x).sub (h 3))
  have hd := hc.smul ((((h 0).smul_const (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))).add
    ((h 1).smul_const (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)))).add
    ((h 2).smul_const (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))))
  have hd' := hd.congr_of_eventuallyEq (f₁ := stereoTop)
    (by rw [hf]; exact Filter.EventuallyEq.rfl)
  rw [hd'.fderiv]
  ext i
  fin_cases i <;> simp [div_eq_mul_inv]

private theorem sqrt2_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

private theorem sqrt2_ne_zero : Real.sqrt 2 ≠ 0 := by positivity

private theorem inv_sqrt2_mul_self : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
  rw [← mul_inv, sqrt2_mul_self, one_div]

private theorem two_mul_inv_sqrt2 : 2 * (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by
  rw [← div_eq_mul_inv, div_eq_iff sqrt2_ne_zero, sqrt2_mul_self]

private theorem inv_one_add_inv_sqrt2 :
    (1 + (Real.sqrt 2)⁻¹)⁻¹ * (Real.sqrt 2)⁻¹ = Real.sqrt 2 - 1 := by
  have h1 : (1 + (Real.sqrt 2)⁻¹) ≠ 0 := by positivity
  rw [inv_mul_eq_iff_eq_mul₀ h1]
  have h2 : Real.sqrt 2 * (Real.sqrt 2)⁻¹ = 1 := mul_inv_cancel₀ sqrt2_ne_zero
  linear_combination two_mul_inv_sqrt2 - h2

/-- **The unique pair realizing the direction `(0, −1, 0)`.** For `x` in the fibre over `(1,0,0)`
and `x'` in the fibre over `(−1,0,0)`, `stereoTop x − stereoTop x'` is a positive multiple of
`(0, −1, 0)` exactly when `x = (0, −1, 0, −1)/√2` and `x' = (0, 1, 0, −1)/√2`. -/
theorem hopf_link_pair_iff (x x' : Sph 3) (hx : (hopfMap x).1 = !₂[1, 0, 0])
    (hx' : (hopfMap x').1 = !₂[-1, 0, 0]) :
    (∃ c : ℝ, 0 < c ∧ stereoTop x.1 - stereoTop x'.1 = c • !₂[0, -1, 0]) ↔
      x.1 = (Real.sqrt 2)⁻¹ • !₂[0, -1, 0, -1] ∧ x'.1 = (Real.sqrt 2)⁻¹ • !₂[0, 1, 0, -1] := by
  rw [hopfMap_eq_e0_iff] at hx
  rw [hopfMap_eq_neg_e0_iff] at hx'
  obtain ⟨h2, h3⟩ := hx
  obtain ⟨h2', h3'⟩ := hx'
  have hs := sph3 x
  have hs' := sph3 x'
  rw [h2, h3] at hs
  rw [h2', h3'] at hs'
  have hr2 : ((Real.sqrt 2)⁻¹) ^ 2 = 1 / 2 := by rw [sq, inv_sqrt2_mul_self]
  have hrpos : 0 < (Real.sqrt 2)⁻¹ := by positivity
  have hb : x.1 1 < 1 := by nlinarith
  have he : -1 < x'.1 1 := by nlinarith
  constructor
  · rintro ⟨c, hc, hdiff⟩
    -- the three coordinates of `stereoTop x − stereoTop x' = c • (0, −1, 0)`
    have e0 : (1 - x.1 1)⁻¹ * x.1 0 - (1 + x'.1 1)⁻¹ * x'.1 0 = 0 := by
      have := congrArg (fun v : 𝔼 3 => v 0) hdiff
      simp only [stereoTop, h3, h3'] at this
      vec_simp at this
      linear_combination this
    have e1 : (1 - x.1 1)⁻¹ * x.1 1 - (1 + x'.1 1)⁻¹ * x'.1 1 = -c := by
      have := congrArg (fun v : 𝔼 3 => v 1) hdiff
      simp only [stereoTop, h3, h3'] at this
      vec_simp at this
      linear_combination this
    have e2 : (1 - x.1 1)⁻¹ * x.1 0 + (1 + x'.1 1)⁻¹ * x'.1 0 = 0 := by
      have := congrArg (fun v : 𝔼 3 => v 2) hdiff
      simp only [stereoTop, h2, h3, h2', h3'] at this
      vec_simp at this
      linear_combination this
    have hp : (1 - x.1 1)⁻¹ * (1 - x.1 1) = 1 := inv_mul_cancel₀ (by linarith)
    have hq : (1 + x'.1 1)⁻¹ * (1 + x'.1 1) = 1 := inv_mul_cancel₀ (by linarith)
    have hx0 : x.1 0 = 0 := by
      have : (1 - x.1 1)⁻¹ * x.1 0 = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left (inv_ne_zero (by linarith))
    have hx0' : x'.1 0 = 0 := by
      have : (1 + x'.1 1)⁻¹ * x'.1 0 = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left (inv_ne_zero (by linarith))
    -- the sign condition, cleared of denominators
    have hineq : x.1 1 - x'.1 1 + 2 * x.1 1 * x'.1 1 < 0 := by
      have hneg : ((1 - x.1 1)⁻¹ * x.1 1 - (1 + x'.1 1)⁻¹ * x'.1 1) *
          ((1 - x.1 1) * (1 + x'.1 1)) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) (mul_pos (by linarith) (by linarith))
      have : ((1 - x.1 1)⁻¹ * x.1 1 - (1 + x'.1 1)⁻¹ * x'.1 1) *
          ((1 - x.1 1) * (1 + x'.1 1)) = x.1 1 - x'.1 1 + 2 * x.1 1 * x'.1 1 := by
        linear_combination (x.1 1 * (1 + x'.1 1)) * hp - (x'.1 1 * (1 - x.1 1)) * hq
      linarith
    have hx1 : x.1 1 = (Real.sqrt 2)⁻¹ ∨ x.1 1 = -(Real.sqrt 2)⁻¹ := by
      apply sq_eq_sq_iff_eq_or_eq_neg.1
      rw [hr2]; rw [hx0] at hs; linarith
    have hx1' : x'.1 1 = (Real.sqrt 2)⁻¹ ∨ x'.1 1 = -(Real.sqrt 2)⁻¹ := by
      apply sq_eq_sq_iff_eq_or_eq_neg.1
      rw [hr2]; rw [hx0'] at hs'; linarith
    have hfin : x.1 1 = -(Real.sqrt 2)⁻¹ ∧ x'.1 1 = (Real.sqrt 2)⁻¹ := by
      rcases hx1 with h | h <;> rcases hx1' with h' | h' <;> rw [h, h'] at hineq
      · nlinarith
      · nlinarith
      · exact ⟨h, h'⟩
      · nlinarith
    constructor
    · ext i
      fin_cases i
      · vec_simp; rw [hx0]; ring
      · vec_simp; rw [hfin.1]; ring
      · vec_simp; rw [h2, hx0]; ring
      · vec_simp; rw [h3, hfin.1]; ring
    · ext i
      fin_cases i
      · vec_simp; rw [hx0']; ring
      · vec_simp; rw [hfin.2]; ring
      · vec_simp; rw [h2', hx0']; ring
      · vec_simp; rw [h3', hfin.2]; ring
  · rintro ⟨ha, ha'⟩
    refine ⟨2 * (Real.sqrt 2 - 1), by nlinarith [sqrt2_mul_self, two_mul_inv_sqrt2], ?_⟩
    rw [ha, ha']
    ext i
    fin_cases i
    · simp only [stereoTop]
      vec_simp
      ring
    · simp only [stereoTop]
      vec_simp
      linear_combination (-2) * inv_one_add_inv_sqrt2
    · simp only [stereoTop]
      vec_simp
      ring

/-! ### Tangent data at the linking pair -/

theorem mem_sph_hopfA : (Real.sqrt 2)⁻¹ • !₂[0, -1, 0, -1] ∈ Sph 3 := by
  rw [mem_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, normSq4]
  vec_simp
  linear_combination 2 * inv_sqrt2_mul_self

theorem mem_sph_hopfA' : (Real.sqrt 2)⁻¹ • !₂[0, 1, 0, -1] ∈ Sph 3 := by
  rw [mem_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, normSq4]
  vec_simp
  linear_combination 2 * inv_sqrt2_mul_self

theorem hopfPoly_hopfA : hopfPoly ((Real.sqrt 2)⁻¹ • !₂[0, -1, 0, -1]) = !₂[1, 0, 0] := by
  ext i
  fin_cases i
  · simp only [hopfPoly]; vec_simp; linear_combination 2 * inv_sqrt2_mul_self
  · simp only [hopfPoly]; vec_simp; ring
  · simp only [hopfPoly]; vec_simp; ring

theorem hopfPoly_hopfA' : hopfPoly ((Real.sqrt 2)⁻¹ • !₂[0, 1, 0, -1]) = !₂[-1, 0, 0] := by
  ext i
  fin_cases i
  · simp only [hopfPoly]; vec_simp; linear_combination (-2) * inv_sqrt2_mul_self
  · simp only [hopfPoly]; vec_simp; ring
  · simp only [hopfPoly]; vec_simp; ring

/-- At `a = (0,−1,0,−1)/√2`: the fibre tangent `t = (1,0,1,0)/√2` is tangent to `S³`. -/
theorem hopfA_inner_t :
    ⟪((Real.sqrt 2)⁻¹ • !₂[0, -1, 0, -1] : EuclideanSpace ℝ (Fin 4)),
      (Real.sqrt 2)⁻¹ • !₂[1, 0, 1, 0]⟫ = 0 := by
  rw [inner4]; vec_simp; ring

theorem hopfA_fderiv_t :
    fderiv ℝ hopfPoly ((Real.sqrt 2)⁻¹ • !₂[0, -1, 0, -1]) ((Real.sqrt 2)⁻¹ • !₂[1, 0, 1, 0]) =
      0 := by
  rw [hopfPoly_fderiv_apply]
  ext i
  fin_cases i <;> (vec_simp; ring)

theorem hopfA_inner_u₁ :
    ⟪((Real.sqrt 2)⁻¹ • !₂[0, -1, 0, -1] : EuclideanSpace ℝ (Fin 4)), !₂[1, 0, -1, 0]⟫ = 0 := by
  rw [inner4]; vec_simp; ring

theorem hopfA_inner_u₂ :
    ⟪((Real.sqrt 2)⁻¹ • !₂[0, -1, 0, -1] : EuclideanSpace ℝ (Fin 4)), !₂[0, -1, 0, 1]⟫ = 0 := by
  rw [inner4]; vec_simp; ring

theorem hopfA_fderiv_u₁ :
    fderiv ℝ hopfPoly ((Real.sqrt 2)⁻¹ • !₂[0, -1, 0, -1]) !₂[1, 0, -1, 0] =
      (2 * Real.sqrt 2) • !₂[0, 1, 0] := by
  rw [hopfPoly_fderiv_apply]
  ext i
  fin_cases i
  · vec_simp; ring
  · vec_simp; linear_combination 2 * two_mul_inv_sqrt2
  · vec_simp; ring

theorem hopfA_fderiv_u₂ :
    fderiv ℝ hopfPoly ((Real.sqrt 2)⁻¹ • !₂[0, -1, 0, -1]) !₂[0, -1, 0, 1] =
      (2 * Real.sqrt 2) • !₂[0, 0, 1] := by
  rw [hopfPoly_fderiv_apply]
  ext i
  fin_cases i
  · vec_simp; ring
  · vec_simp; ring
  · vec_simp; linear_combination 2 * two_mul_inv_sqrt2

/-- At `a' = (0,1,0,−1)/√2`: the fibre tangent `t' = (−1,0,1,0)/√2` is tangent to `S³`. -/
theorem hopfA'_inner_t' :
    ⟪((Real.sqrt 2)⁻¹ • !₂[0, 1, 0, -1] : EuclideanSpace ℝ (Fin 4)),
      (Real.sqrt 2)⁻¹ • !₂[-1, 0, 1, 0]⟫ = 0 := by
  rw [inner4]; vec_simp; ring

theorem hopfA'_fderiv_t' :
    fderiv ℝ hopfPoly ((Real.sqrt 2)⁻¹ • !₂[0, 1, 0, -1]) ((Real.sqrt 2)⁻¹ • !₂[-1, 0, 1, 0]) =
      0 := by
  rw [hopfPoly_fderiv_apply]
  ext i
  fin_cases i <;> (vec_simp; ring)

theorem hopfA'_inner_w₁ :
    ⟪((Real.sqrt 2)⁻¹ • !₂[0, 1, 0, -1] : EuclideanSpace ℝ (Fin 4)), !₂[0, 1, 0, 1]⟫ = 0 := by
  rw [inner4]; vec_simp; ring

theorem hopfA'_inner_w₂ :
    ⟪((Real.sqrt 2)⁻¹ • !₂[0, 1, 0, -1] : EuclideanSpace ℝ (Fin 4)), !₂[1, 0, 1, 0]⟫ = 0 := by
  rw [inner4]; vec_simp; ring

theorem hopfA'_fderiv_w₁ :
    fderiv ℝ hopfPoly ((Real.sqrt 2)⁻¹ • !₂[0, 1, 0, -1]) !₂[0, 1, 0, 1] =
      (2 * Real.sqrt 2) • !₂[0, 0, 1] := by
  rw [hopfPoly_fderiv_apply]
  ext i
  fin_cases i
  · vec_simp; ring
  · vec_simp; ring
  · vec_simp; linear_combination 2 * two_mul_inv_sqrt2

theorem hopfA'_fderiv_w₂ :
    fderiv ℝ hopfPoly ((Real.sqrt 2)⁻¹ • !₂[0, 1, 0, -1]) !₂[1, 0, 1, 0] =
      (2 * Real.sqrt 2) • !₂[0, 1, 0] := by
  rw [hopfPoly_fderiv_apply]
  ext i
  fin_cases i
  · vec_simp; ring
  · vec_simp; linear_combination 2 * two_mul_inv_sqrt2
  · vec_simp; ring

theorem stereoTop_hopfA :
    stereoTop ((Real.sqrt 2)⁻¹ • !₂[0, -1, 0, -1]) = !₂[0, -(Real.sqrt 2 - 1), 0] := by
  ext i
  fin_cases i
  · simp only [stereoTop]; vec_simp; ring
  · simp only [stereoTop]; vec_simp; linear_combination (-1) * inv_one_add_inv_sqrt2
  · simp only [stereoTop]; vec_simp; ring

theorem stereoTop_hopfA' :
    stereoTop ((Real.sqrt 2)⁻¹ • !₂[0, 1, 0, -1]) = !₂[0, Real.sqrt 2 - 1, 0] := by
  ext i
  fin_cases i
  · simp only [stereoTop]; vec_simp; ring
  · simp only [stereoTop]; vec_simp; linear_combination inv_one_add_inv_sqrt2
  · simp only [stereoTop]; vec_simp; ring

private theorem hopfA_three_ne_one :
    ((Real.sqrt 2)⁻¹ • !₂[(0 : ℝ), -1, 0, -1] : 𝔼 4) 3 ≠ 1 := by
  vec_simp
  have : 0 < (Real.sqrt 2)⁻¹ := by positivity
  linarith

private theorem hopfA'_three_ne_one :
    ((Real.sqrt 2)⁻¹ • !₂[(0 : ℝ), 1, 0, -1] : 𝔼 4) 3 ≠ 1 := by
  vec_simp
  have : 0 < (Real.sqrt 2)⁻¹ := by positivity
  linarith

theorem stereoTop_fderiv_hopfA_t :
    fderiv ℝ stereoTop ((Real.sqrt 2)⁻¹ • !₂[0, -1, 0, -1]) ((Real.sqrt 2)⁻¹ • !₂[1, 0, 1, 0]) =
      (Real.sqrt 2 - 1) • !₂[1, 0, 1] := by
  rw [stereoTop_fderiv_apply hopfA_three_ne_one]
  ext i
  fin_cases i
  · vec_simp; linear_combination inv_one_add_inv_sqrt2
  · vec_simp; ring
  · vec_simp; linear_combination inv_one_add_inv_sqrt2

theorem stereoTop_fderiv_hopfA'_t' :
    fderiv ℝ stereoTop ((Real.sqrt 2)⁻¹ • !₂[0, 1, 0, -1]) ((Real.sqrt 2)⁻¹ • !₂[-1, 0, 1, 0]) =
      (Real.sqrt 2 - 1) • !₂[-1, 0, 1] := by
  rw [stereoTop_fderiv_apply hopfA'_three_ne_one]
  ext i
  fin_cases i
  · vec_simp; linear_combination (-1) * inv_one_add_inv_sqrt2
  · vec_simp; ring
  · vec_simp; linear_combination inv_one_add_inv_sqrt2

/-! ### The quaternionic vector fields -/

/-- Left multiplication by the quaternion `i`: `(−x₁, x₀, −x₃, x₂)`, tangent to the fibres. -/
def hopfI (x : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) := !₂[-x 1, x 0, -x 3, x 2]

/-- Left multiplication by the quaternion `j`: `(−x₂, x₃, x₀, −x₁)`. -/
def hopfJ (x : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) := !₂[-x 2, x 3, x 0, -x 1]

/-- Left multiplication by the quaternion `k`: `(−x₃, −x₂, x₁, x₀)`. -/
def hopfK (x : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) := !₂[-x 3, -x 2, x 1, x 0]

theorem inner_hopfI (x : EuclideanSpace ℝ (Fin 4)) : ⟪x, hopfI x⟫ = 0 := by
  rw [inner4]; simp only [hopfI]; vec_simp; ring

theorem inner_hopfJ (x : EuclideanSpace ℝ (Fin 4)) : ⟪x, hopfJ x⟫ = 0 := by
  rw [inner4]; simp only [hopfJ]; vec_simp; ring

theorem inner_hopfK (x : EuclideanSpace ℝ (Fin 4)) : ⟪x, hopfK x⟫ = 0 := by
  rw [inner4]; simp only [hopfK]; vec_simp; ring

theorem hopfPoly_fderiv_hopfI (x : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ hopfPoly x (hopfI x) = 0 := by
  rw [hopfPoly_fderiv_apply]
  ext i
  fin_cases i <;> (simp only [hopfI]; vec_simp; ring)

theorem hopfPoly_fderiv_hopfJ (x : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ hopfPoly x (hopfJ x) =
      (2 : ℝ) • !₂[x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 + x 3 ^ 2, 2 * (x 0 * x 1 + x 2 * x 3),
        2 * (x 1 * x 3 - x 0 * x 2)] := by
  rw [hopfPoly_fderiv_apply]
  ext i
  fin_cases i <;> (simp only [hopfJ]; vec_simp; ring)

theorem hopfPoly_fderiv_hopfK (x : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ hopfPoly x (hopfK x) =
      (2 : ℝ) • !₂[2 * (x 0 * x 1 - x 2 * x 3), -x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 + x 3 ^ 2,
        -2 * (x 0 * x 3 + x 1 * x 2)] := by
  rw [hopfPoly_fderiv_apply]
  ext i
  fin_cases i <;> (simp only [hopfK]; vec_simp; ring)

theorem inner_hopfPoly_fderiv_hopfJ (x : EuclideanSpace ℝ (Fin 4)) :
    ⟪hopfPoly x, fderiv ℝ hopfPoly x (hopfJ x)⟫ = 0 := by
  rw [hopfPoly_fderiv_hopfJ, inner3]; simp only [hopfPoly]; vec_simp; ring

theorem inner_hopfPoly_fderiv_hopfK (x : EuclideanSpace ℝ (Fin 4)) :
    ⟪hopfPoly x, fderiv ℝ hopfPoly x (hopfK x)⟫ = 0 := by
  rw [hopfPoly_fderiv_hopfK, inner3]; simp only [hopfPoly]; vec_simp; ring

theorem inner_fderiv_hopfJ_hopfK (x : EuclideanSpace ℝ (Fin 4)) :
    ⟪fderiv ℝ hopfPoly x (hopfJ x), fderiv ℝ hopfPoly x (hopfK x)⟫ = 0 := by
  rw [hopfPoly_fderiv_hopfJ, hopfPoly_fderiv_hopfK, inner3]; vec_simp; ring

theorem norm_fderiv_hopfJ (x : EuclideanSpace ℝ (Fin 4)) :
    ‖fderiv ℝ hopfPoly x (hopfJ x)‖ = 2 * ‖x‖ ^ 2 := by
  have h : ‖fderiv ℝ hopfPoly x (hopfJ x)‖ ^ 2 = (2 * ‖x‖ ^ 2) ^ 2 := by
    rw [hopfPoly_fderiv_hopfJ, normSq3, mul_pow, normSq4]
    vec_simp
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

theorem norm_fderiv_hopfK (x : EuclideanSpace ℝ (Fin 4)) :
    ‖fderiv ℝ hopfPoly x (hopfK x)‖ = 2 * ‖x‖ ^ 2 := by
  have h : ‖fderiv ℝ hopfPoly x (hopfK x)‖ ^ 2 = (2 * ‖x‖ ^ 2) ^ 2 := by
    rw [hopfPoly_fderiv_hopfK, normSq3, mul_pow, normSq4]
    vec_simp
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

theorem norm_fderiv_hopfJ_of_mem (x : Sph 3) : ‖fderiv ℝ hopfPoly x.1 (hopfJ x.1)‖ = 2 := by
  rw [norm_fderiv_hopfJ, (mem_iff_norm).1 x.2]; norm_num

theorem norm_fderiv_hopfK_of_mem (x : Sph 3) : ‖fderiv ℝ hopfPoly x.1 (hopfK x.1)‖ = 2 := by
  rw [norm_fderiv_hopfK, (mem_iff_norm).1 x.2]; norm_num

end Problems

end Milnor
