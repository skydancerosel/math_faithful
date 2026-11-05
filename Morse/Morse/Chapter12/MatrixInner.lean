import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Lie.OfAssociative

/-!
Milnor, *Morse Theory*, §21 (p. 112) and §23 (p. 125): the Euclidean space of matrices.

# The Frobenius inner product on `Mₙ(𝕜)` and the calculus of the matrix exponential

## Milnor's text, paraphrased

* p. 125: the unitary group is a subset of the space of `n × n` complex matrices, "a real vector
  space of dimension `2n²`", and the left- and right-invariant metric on it is
  `⟨A, B⟩ = Re tr(AB*)` on the tangent space at the identity.  The orthogonal group is treated in
  the same way inside the real matrices (§24).
* p. 125, (1)–(4): `exp(A*) = (exp A)*`, `exp(A + B) = exp A exp B` for commuting `A`, `B`, and
  "the exponential is smooth".

## What is formalized

Mathlib does not put a norm on `Matrix ι ι 𝕜`, because there are several natural ones.  Here the
Frobenius norm `‖A‖ = (Σ |a_ij|²)^{1/2}` is made into a *real* inner product space structure with
`⟪A, B⟫ = Re tr(Aᴴ B)`, which is Milnor's `Re tr(AB*)` up to the order of the factors.  The
instances are **scoped** (`open scoped Morse.MatrixInner`).

* `Morse.MatrixInner.normedAddCommGroup`: the Frobenius norm, with the uniform structure of
  `Matrix` *substituted* (`MetricSpace.replaceUniformity`), so that the topology is reducibly the
  usual topology of matrices.  Without this, the Frobenius structure of Mathlib
  (`Matrix.frobeniusNormedAddCommGroup`) has a topology which is only propositionally equal to the
  product topology, and the charted space structure `ChartedSpace (Matrix ι ι 𝕜) (Matrix ι ι 𝕜)`
  needed for `Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι 𝕜) …` cannot be found.
* `Morse.MatrixInner.innerProductSpace`, `Morse.inner_def`: `⟪A, B⟫ = Re tr(Aᴴ B)`;
  `Morse.MatrixInner.normedRing`, `Morse.MatrixInner.normedAlgebra`: the Frobenius norm is
  submultiplicative, so the matrix exponential has Mathlib's calculus (`hasDerivAt_exp_smul_const`);
  the commutator Lie ring structure (`LieRing.ofAssociativeRing`) is also made a scoped instance.
* Isometries: `Morse.inner_mul_left_of_unitary`, `Morse.inner_mul_right_of_unitary`,
  `Morse.mulLeftIso`, `Morse.mulRightIso` (left and right multiplication by a unitary matrix are
  linear isometries of `Mₙ(𝕜)`), and `Morse.inner_eq_zero_of_hermitian_of_skew` (Hermitian and
  skew-Hermitian matrices are orthogonal).
* The exponential: `Morse.contDiff_exp_matrix`, `Morse.exp_conjTranspose_mul_exp_of_skew`
  (`exp X` is unitary for skew-Hermitian `X`), `Morse.exp_half_mul_exp_half`.
* The determinant: `Morse.contDiff_det`, `Morse.fderiv_det_mul` (`d(det)_A(AX) = det A · tr X`,
  from the first two terms of the expansion of `det(1 + sX)`), `Morse.det_exp_smul_of_trace_eq_zero`
  (`det(exp tX) = 1` when `tr X = 0`).

## Gaps in Milnor's text

* p. 125: "the exponential is smooth" and the formula for its derivative along a line,
  `d/dt exp(tA) = exp(tA) A`, are quoted; here they are Mathlib's (`NormedSpace.exp_analytic`,
  `hasDerivAt_exp_smul_const`), for the Frobenius norm.
* p. 126, "`det(exp A) = e^{tr A}`" (used for `SU(n)`): not in Mathlib.  Only the consequence that
  `exp` maps traceless matrices into `det = 1` is needed, and it follows from Jacobi's formula
  `d(det)_A(AX) = det A · tr X` (`Morse.fderiv_det_mul`): `t ↦ det(exp tX)` has derivative
  `det(exp tX) · tr X = 0`.
-/

open Matrix

noncomputable section

namespace Morse

namespace MatrixInner

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-- The Frobenius norm `(Σ |a_ij|²)^{1/2}` on square matrices, with the uniformity of `Matrix`
(so that its topology is reducibly the usual topology of matrices). -/
@[instance_reducible]
def normedAddCommGroup : NormedAddCommGroup (Matrix ι ι 𝕜) :=
  let F : NormedAddCommGroup (Matrix ι ι 𝕜) := Matrix.frobeniusNormedAddCommGroup
  { toNorm := F.toNorm
    toAddCommGroup := Matrix.addCommGroup
    toMetricSpace := F.toMetricSpace.replaceUniformity rfl
    dist_eq := F.dist_eq }

attribute [scoped instance] normedAddCommGroup

theorem norm_def (A : Matrix ι ι 𝕜) : ‖A‖ = (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
  Matrix.frobenius_norm_def A

/-- The Frobenius norm is a real normed space structure. -/
@[instance_reducible]
def normedSpace : NormedSpace ℝ (Matrix ι ι 𝕜) where
  norm_smul_le r A :=
    (Matrix.frobeniusNormedSpace (R := ℝ) (m := ι) (n := ι) (α := 𝕜)).norm_smul_le r A

attribute [scoped instance] normedSpace

theorem norm_sq_eq (A : Matrix ι ι 𝕜) : ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp only [Real.rpow_two]

theorem re_trace_conjTranspose_mul_self (A : Matrix ι ι 𝕜) :
    RCLike.re (trace (Aᴴ * A)) = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, RCLike.conj_mul]
  norm_cast

/-- **The Frobenius inner product** `⟪A, B⟫ = Re tr(Aᴴ B)` (Milnor's `Re tr(AB*)`, p. 125), a real
inner product on `Mₙ(𝕜)` whose norm is the Frobenius norm. -/
@[instance_reducible]
def innerProductSpace : InnerProductSpace ℝ (Matrix ι ι 𝕜) where
  inner A B := RCLike.re (trace (Aᴴ * B))
  norm_sq_eq_re_inner A := by
    rw [norm_sq_eq, ← re_trace_conjTranspose_mul_self]
    rfl
  conj_inner_symm A B := by
    simp only [conj_trivial]
    have h : (Bᴴ * A)ᴴ = Aᴴ * B := by simp
    rw [← h, trace_conjTranspose, RCLike.star_def, RCLike.conj_re]
  add_left A B C := by
    simp [conjTranspose_add, add_mul, trace_add]
  smul_left A B r := by
    simp only [conj_trivial]
    rw [show (r • A)ᴴ = (r : 𝕜) • Aᴴ by
      ext i j; simp [RCLike.real_smul_eq_coe_mul]]
    rw [Matrix.smul_mul, trace_smul, smul_eq_mul, RCLike.re_ofReal_mul]

attribute [scoped instance] innerProductSpace

omit [Fintype ι] in
/-- A shortcut: `Mₙ(𝕜)` is finite-dimensional over `ℝ`. -/
scoped instance (priority := high) finiteDimensional [Finite ι] :
    FiniteDimensional ℝ (Matrix ι ι 𝕜) :=
  inferInstance

omit [Fintype ι] in
/-- A shortcut: the real subspaces of `Mₙ(𝕜)` are finite-dimensional. -/
scoped instance (priority := high) finiteDimensional_submodule [Finite ι]
    (S : Submodule ℝ (Matrix ι ι 𝕜)) : FiniteDimensional ℝ S :=
  FiniteDimensional.finiteDimensional_submodule S

variable [DecidableEq ι]

/-- The Frobenius norm is submultiplicative: a normed ring structure on `Mₙ(𝕜)`. -/
@[instance_reducible]
def normedRing : NormedRing (Matrix ι ι 𝕜) :=
  { (normedAddCommGroup : NormedAddCommGroup (Matrix ι ι 𝕜)), Matrix.instRing with
    norm_mul_le := Matrix.frobenius_norm_mul
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

attribute [scoped instance] normedRing

/-- `Mₙ(𝕜)` with the Frobenius norm is a normed `ℝ`-algebra. -/
@[instance_reducible]
def normedAlgebra : NormedAlgebra ℝ (Matrix ι ι 𝕜) :=
  { (normedSpace : NormedSpace ℝ (Matrix ι ι 𝕜)), Matrix.instAlgebra with }

attribute [scoped instance] normedAlgebra

-- The commutator `[A, B] = AB − BA` makes `Mₙ(𝕜)` a Lie ring (Mathlib's
-- `LieRing.ofAssociativeRing`, not a global instance).
attribute [scoped instance 100] LieRing.ofAssociativeRing

end MatrixInner

open scoped MatrixInner RealInnerProductSpace ContDiff

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-! ### The inner product -/

/-- `⟪A, B⟫ = Re tr(Aᴴ B)`. -/
theorem inner_def (A B : Matrix ι ι 𝕜) : ⟪A, B⟫ = RCLike.re (trace (Aᴴ * B)) := rfl

theorem inner_conjTranspose (A B : Matrix ι ι 𝕜) : ⟪Aᴴ, Bᴴ⟫ = ⟪A, B⟫ := by
  rw [inner_def, inner_def, conjTranspose_conjTranspose, trace_mul_comm, ← RCLike.conj_re,
    ← RCLike.star_def, ← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

/-- **Hermitian and skew-Hermitian matrices are orthogonal**: for `Aᴴ = A` and `Bᴴ = −B`,
`tr(AB)` is purely imaginary. -/
theorem inner_eq_zero_of_hermitian_of_skew {A B : Matrix ι ι 𝕜} (hA : Aᴴ = A) (hB : Bᴴ = -B) :
    ⟪A, B⟫ = 0 := by
  have h := inner_conjTranspose A B
  rw [hA, hB, inner_neg_right] at h
  linarith

variable [DecidableEq ι]

/-- **Left multiplication by a unitary matrix preserves the inner product.** -/
theorem inner_mul_left_of_unitary {U : Matrix ι ι 𝕜} (hU : Uᴴ * U = 1) (A B : Matrix ι ι 𝕜) :
    ⟪U * A, U * B⟫ = ⟪A, B⟫ := by
  rw [inner_def, inner_def, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU,
    Matrix.one_mul]

/-- **Right multiplication by a unitary matrix preserves the inner product.** -/
theorem inner_mul_right_of_unitary {U : Matrix ι ι 𝕜} (hU : U * Uᴴ = 1) (A B : Matrix ι ι 𝕜) :
    ⟪A * U, B * U⟫ = ⟪A, B⟫ := by
  rw [inner_def, inner_def, conjTranspose_mul, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, hU, Matrix.mul_one, trace_mul_comm]

theorem mul_conjTranspose_eq_one {U : Matrix ι ι 𝕜} (hU : Uᴴ * U = 1) : U * Uᴴ = 1 :=
  mul_eq_one_comm.1 hU

/-- **Left multiplication by a unitary matrix** `U` (`Uᴴ U = 1`), as a linear isometry of
`Mₙ(𝕜)`. -/
def mulLeftIso (U : Matrix ι ι 𝕜) (hU : Uᴴ * U = 1) : Matrix ι ι 𝕜 ≃ₗᵢ[ℝ] Matrix ι ι 𝕜 where
  toFun A := U * A
  invFun A := Uᴴ * A
  map_add' A B := Matrix.mul_add U A B
  map_smul' r A := Matrix.mul_smul U r A
  left_inv A := by simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
  right_inv A := by simp only [← Matrix.mul_assoc, mul_conjTranspose_eq_one hU, Matrix.one_mul]
  norm_map' A := by
    have h := inner_mul_left_of_unitary hU A A
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

@[simp] theorem mulLeftIso_apply (U : Matrix ι ι 𝕜) (hU : Uᴴ * U = 1) (A : Matrix ι ι 𝕜) :
    mulLeftIso U hU A = U * A := rfl

@[simp] theorem mulLeftIso_symm_apply (U : Matrix ι ι 𝕜) (hU : Uᴴ * U = 1) (A : Matrix ι ι 𝕜) :
    (mulLeftIso U hU).symm A = Uᴴ * A := rfl

/-- **Right multiplication by a unitary matrix**, as a linear isometry of `Mₙ(𝕜)`. -/
def mulRightIso (U : Matrix ι ι 𝕜) (hU : Uᴴ * U = 1) : Matrix ι ι 𝕜 ≃ₗᵢ[ℝ] Matrix ι ι 𝕜 where
  toFun A := A * U
  invFun A := A * Uᴴ
  map_add' A B := Matrix.add_mul A B U
  map_smul' r A := Matrix.smul_mul r A U
  left_inv A := by simp only [Matrix.mul_assoc, mul_conjTranspose_eq_one hU, Matrix.mul_one]
  right_inv A := by simp only [Matrix.mul_assoc, hU, Matrix.mul_one]
  norm_map' A := by
    have h := inner_mul_right_of_unitary (mul_conjTranspose_eq_one hU) A A
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

@[simp] theorem mulRightIso_apply (U : Matrix ι ι 𝕜) (hU : Uᴴ * U = 1) (A : Matrix ι ι 𝕜) :
    mulRightIso U hU A = A * U := rfl

/-! ### The exponential -/

open NormedSpace in
/-- **The matrix exponential is smooth** (Milnor p. 125): it is analytic. -/
theorem contDiff_exp_matrix : ContDiff ℝ ∞ (exp : Matrix ι ι 𝕜 → Matrix ι ι 𝕜) := by
  have h : AnalyticOnNhd ℝ (exp : Matrix ι ι 𝕜 → Matrix ι ι 𝕜) Set.univ :=
    fun x _ => NormedSpace.exp_analytic x
  exact contDiffOn_univ.1 h.contDiffOn_of_completeSpace

open NormedSpace in
theorem contDiff_exp_smul (X : Matrix ι ι 𝕜) : ContDiff ℝ ∞ fun t : ℝ => exp (t • X) :=
  contDiff_exp_matrix.comp (contDiff_id.smul contDiff_const)

open NormedSpace in
/-- `exp(sX) exp(tX) = exp((s + t)X)`. -/
theorem exp_smul_mul_exp_smul (X : Matrix ι ι 𝕜) (s t : ℝ) :
    exp (s • X) * exp (t • X) = exp ((s + t) • X) := by
  rw [add_smul, Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left s |>.smul_right t)]

open NormedSpace in
/-- `exp(tX) = exp(tX/2)²`. -/
theorem exp_half_mul_exp_half (X : Matrix ι ι 𝕜) (t : ℝ) :
    exp ((t / 2) • X) * exp ((t / 2) • X) = exp (t • X) := by
  rw [exp_smul_mul_exp_smul, add_halves]

open NormedSpace in
/-- `exp(tX)` commutes with `X`. -/
theorem exp_smul_mul_self (X : Matrix ι ι 𝕜) (t : ℝ) : exp (t • X) * X = X * exp (t • X) :=
  (((Commute.refl X).smul_left t).exp_left).eq

open NormedSpace in
/-- **`exp X` is unitary for skew-Hermitian `X`** (Milnor p. 125, from (1) and (3)). -/
theorem exp_conjTranspose_mul_exp_of_skew {X : Matrix ι ι 𝕜} (hX : Xᴴ = -X) :
    (exp X)ᴴ * exp X = 1 := by
  rw [← Matrix.exp_conjTranspose, hX, ← Matrix.exp_add_of_commute _ _ (Commute.neg_left
    (Commute.refl X)), neg_add_cancel, exp_zero]

open NormedSpace in
theorem exp_mul_exp_neg (X : Matrix ι ι 𝕜) : exp X * exp (-X) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl X)), add_neg_cancel,
    exp_zero]

/-! ### The determinant -/

omit [DecidableEq ι] in
/-- An entry of a matrix, as a continuous real-linear map. -/
theorem contDiff_entry (i j : ι) : ContDiff ℝ ∞ fun A : Matrix ι ι 𝕜 => A i j := by
  let L : Matrix ι ι 𝕜 →ₗ[ℝ] 𝕜 :=
    { toFun := fun A => A i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).contDiff

/-- **The determinant is smooth**: a polynomial in the entries. -/
theorem contDiff_det : ContDiff ℝ ∞ (det : Matrix ι ι 𝕜 → 𝕜) := by
  have h : (det : Matrix ι ι 𝕜 → 𝕜) =
      fun A => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : 𝕜) * ∏ i, A (σ i) i := by
    funext A
    rw [det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [h]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => contDiff_entry _ _)

/-- `det(1 + sX) = 1 + s · tr X + O(s²)`: the derivative at `s = 0` is `tr X`. -/
theorem hasDerivAt_det_one_add_smul (X : Matrix ι ι 𝕜) :
    HasDerivAt (fun s : ℝ => det (1 + s • X)) (trace X) 0 := by
  set p := (det (1 + (Polynomial.X : Polynomial 𝕜) • X.map Polynomial.C)).divX.divX
  have h : (fun s : ℝ => det (1 + s • X)) =
      fun s : ℝ => 1 + trace X * (s : 𝕜) + p.eval (s : 𝕜) * (s : 𝕜) ^ 2 := by
    funext s
    rw [show (s • X : Matrix ι ι 𝕜) = (s : 𝕜) • X by ext; simp [RCLike.real_smul_eq_coe_mul]]
    exact det_one_add_smul (s : 𝕜) X
  rw [h]
  have hc : HasDerivAt (fun s : ℝ => (s : 𝕜)) 1 0 := by
    simpa using (RCLike.ofRealCLM (K := 𝕜)).hasDerivAt (x := (0 : ℝ))
  have h1 : HasDerivAt (fun s : ℝ => trace X * (s : 𝕜)) (trace X * 1) 0 := hc.const_mul _
  have hp : HasDerivAt (fun s : ℝ => p.eval (s : 𝕜)) (p.derivative.eval ((0 : ℝ) : 𝕜) * 1) 0 :=
    (p.hasDerivAt ((0 : ℝ) : 𝕜)).comp (0 : ℝ) hc
  have hsq : HasDerivAt (fun s : ℝ => (s : 𝕜) ^ 2) ((2 : ℕ) * ((0 : ℝ) : 𝕜) ^ (2 - 1) * 1) 0 :=
    hc.pow 2
  refine ((h1.const_add 1).add (hp.fun_mul hsq)).congr_deriv ?_
  simp

/-- **Jacobi's formula** along `A·𝔤`: `d(det)_A(AX) = det A · tr X`. -/
theorem fderiv_det_mul (A X : Matrix ι ι 𝕜) :
    fderiv ℝ det A (A * X) = det A * trace X := by
  have hd : HasFDerivAt det (fderiv ℝ det A) A :=
    (contDiff_det.differentiable (by simp) A).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => A + s • (A * X)) (A * X) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (A * X)).const_add A
  have h1 := hd.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have h2 : HasDerivAt (fun s : ℝ => det (A + s • (A * X))) (det A * trace X) 0 := by
    have : (fun s : ℝ => det (A + s • (A * X))) = fun s => det A * det (1 + s • X) := by
      funext s
      rw [← det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    rw [this]
    exact (hasDerivAt_det_one_add_smul X).const_mul _
  exact h1.unique h2

open NormedSpace in
/-- `d/dt det(exp tX) = det(exp tX) · tr X`. -/
theorem hasDerivAt_det_exp_smul (X : Matrix ι ι 𝕜) (t : ℝ) :
    HasDerivAt (fun s : ℝ => det (exp (s • X))) (det (exp (t • X)) * trace X) t := by
  have hd : HasFDerivAt det (fderiv ℝ det (exp (t • X))) (exp (t • X)) :=
    (contDiff_det.differentiable (by simp) _).hasFDerivAt
  have h := hd.comp_hasDerivAt t (hasDerivAt_exp_smul_const X t)
  rwa [fderiv_det_mul] at h

open NormedSpace in
/-- **`exp` maps traceless matrices into `det = 1`.** -/
theorem det_exp_smul_of_trace_eq_zero {X : Matrix ι ι 𝕜} (hX : trace X = 0) (t : ℝ) :
    det (exp (t • X)) = 1 := by
  have hconst : ∀ s, HasDerivAt (fun s : ℝ => det (exp (s • X))) 0 s := fun s => by
    simpa [hX] using hasDerivAt_det_exp_smul X s
  have h := is_const_of_deriv_eq_zero (fun s => (hconst s).differentiableAt)
    (fun s => (hconst s).deriv) t 0
  rw [h, zero_smul, exp_zero, det_one]

end Morse
