import Morse.Chapter12.GroupGeodesics
import Morse.Chapter9.JacobiSpace

/-!
Milnor, *Morse Theory*, §20 (Theorem 20.5, pp. 110–111) and the proof of Theorem 21.7
(pp. 116–117): Jacobi fields along a geodesic `t ↦ exp(tA)` of a matrix group.

# Jacobi fields along one-parameter subgroups

## Milnor's text, paraphrased

* **Theorem 20.5** (p. 110), in a locally symmetric space: with `K_V(W) = R(V,W)V` on `T_pM`
  (`V = γ'(0)`) and its eigenvalues `e_1, …, e_n`, the conjugate points to `p` along `γ` are the
  `γ(πk/√e_i)`, `k ≠ 0`, `e_i > 0`, and the multiplicity of `γ(t)` is the number of `e_i` with
  `t` a multiple of `π/√e_i`.  *Proof*: in a parallel orthonormal eigenframe `U_i`,
  `R(V, U_i)V = e_i U_i` along `γ` (local symmetry), so the Jacobi equation becomes
  `w_i'' + e_i w_i = 0`.
* For a Lie group with a bi-invariant metric (p. 116), `K_V = −¼ (ad V)²`.

## What is formalized

For a matrix group `G` with Lie algebra `𝔤` (`Morse.IsMatrixGroup`) and `A ∈ 𝔤`, along
`γ(t) = exp(tA)` (a geodesic, `Morse/Chapter12/GroupGeodesics.lean`):

* **The parallel frame**: a field along `γ` is written `J(t) = h(t) U(t) h(t)` with
  `h(t) = exp(tA/2)` (`Morse.halfExp`) and `U(t) ∈ 𝔤`; the parallel fields are those with `U`
  constant.  **The covariant derivative** is `D/dt (hUh) = h U' h`
  (`Morse.IsMatrixGroup.covD_conj`), because `γᴴ (hUh)' = hᴴ(½(AU + UA) + U')h` and the first term
  is Hermitian.  **The curvature term** is `R(γ', hUh)γ' = h K_A(U) h`
  (`Morse.IsMatrixGroup.curvR_conj`), with `K_A(U) = ¼[[A,U],A]` (`Morse.jacK`), because `h`
  commutes with `A`.
* **Theorem 20.5 for `G`, the Jacobi equation** (`Morse.IsMatrixGroup.isJacobiField_conj`):
  `hUh` is a Jacobi field if `U'' + K_A(U) = 0`, an equation with *constant* coefficients
  (Milnor's `w_i'' + e_i w_i = 0` in an eigenbasis of `K_A`).
  `Morse.IsMatrixGroup.covAlong_conj_zero`: its covariant derivative at `0` is `U'(0)`.

The explicit solutions, the conjugate points and their multiplicities for `SU(n)` are in
`Morse/Chapter12/SUJacobi.lean`.

## Gaps in Milnor's text

* p. 110, "extend the `U_i` to vector fields along `γ` by parallel translation; since `M` is
  locally symmetric, `R(V, U_i)V = e_iU_i` remains true everywhere": the parallel transport along
  `exp(tA)` is not computed in the text.  For `G` it is explicit: `U ↦ hUh` (Milnor's `U_i` are
  `h(t) U_i h(t)`), and `R(γ', hUh)γ' = h K_A(U) h` needs that `h(t) = exp(tA/2)` commutes with `A`.
* The parameter of a conjugate point is a *time*, and `K_V` must be computed for the velocity `V`
  of the geodesic actually used (here `A`, the velocity of `exp(tA)` on `[0, 1]`).
-/

open Matrix Set Filter Topology Module
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### `exp(tA/2)` -/

/-- `h(t) = exp(tA/2)`, the square root of `exp(tA)` used to write fields along `exp(tA)`. -/
def halfExp (A : Matrix ι ι 𝕜) (t : ℝ) : Matrix ι ι 𝕜 := NormedSpace.exp (t • ((1 / 2 : ℝ) • A))

theorem halfExp_mul_halfExp (A : Matrix ι ι 𝕜) (t : ℝ) :
    halfExp A t * halfExp A t = NormedSpace.exp (t • A) := by
  rw [halfExp, exp_smul_mul_exp_smul, smul_smul]
  congr 2
  ring

theorem halfExp_zero (A : Matrix ι ι 𝕜) : halfExp A 0 = 1 := by
  simp [halfExp]

theorem hasDerivAt_halfExp (A : Matrix ι ι 𝕜) (t : ℝ) :
    HasDerivAt (halfExp A) (halfExp A t * ((1 / 2 : ℝ) • A)) t :=
  hasDerivAt_exp_smul_const _ t

theorem halfExp_mul_comm (A : Matrix ι ι 𝕜) (t : ℝ) : halfExp A t * A = A * halfExp A t :=
  ((((Commute.refl A).smul_left (1 / 2 : ℝ)).smul_left t).exp_left).eq

theorem contDiff_halfExp (A : Matrix ι ι 𝕜) : ContDiff ℝ ∞ (halfExp A) :=
  contDiff_exp_smul _

theorem hasDerivAt_exp_smul' (A : Matrix ι ι 𝕜) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A)) (NormedSpace.exp (t • A) * A) t :=
  hasDerivAt_exp_smul_const A t

theorem deriv_exp_smul (A : Matrix ι ι 𝕜) :
    deriv (fun s : ℝ => NormedSpace.exp (s • A)) = fun t => NormedSpace.exp (t • A) * A :=
  funext fun t => (hasDerivAt_exp_smul' A t).deriv

/-- The derivative of `t ↦ h(t) U(t) h(t)`: `h(½(AU + UA) + U')h`. -/
theorem hasDerivAt_conj (A : Matrix ι ι 𝕜) {U : ℝ → Matrix ι ι 𝕜} {U' : Matrix ι ι 𝕜} {t : ℝ}
    (hU : HasDerivAt U U' t) :
    HasDerivAt (fun s => halfExp A s * U s * halfExp A s)
      (halfExp A t * ((1 / 2 : ℝ) • (A * U t + U t * A) + U') * halfExp A t) t := by
  have h1 := ((hasDerivAt_halfExp A t).fun_mul hU).fun_mul (hasDerivAt_halfExp A t)
  refine h1.congr_deriv ?_
  have hc := halfExp_mul_comm A t
  set h := halfExp A t
  have r1 : ∀ X : Matrix ι ι 𝕜, h * (A * X) = A * (h * X) := fun X => by
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    hc, r1]
  module

/-- The derivative of a curve in a subspace `𝔤` lies in `𝔤`. -/
theorem deriv_mem_of_forall_mem {𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)} {U : ℝ → Matrix ι ι 𝕜}
    (hU𝔤 : ∀ s, U s ∈ 𝔤) (hU : Differentiable ℝ U) (t : ℝ) : deriv U t ∈ 𝔤 := by
  have h1 : HasDerivAt (fun s => algProj 𝔤 (U s)) (algProj 𝔤 (deriv U t)) t :=
    (algProj 𝔤).hasFDerivAt.comp_hasDerivAt t (hU t).hasDerivAt
  have h2 : (fun s => algProj 𝔤 (U s)) = U := funext fun s => algProj_of_mem (hU𝔤 s)
  rw [h2] at h1
  rw [h1.deriv]
  exact algProj_mem 𝔤 _

/-! ### The Jacobi operator `K_A` -/

/-- **Milnor's `K_A(U) = R(A, U)A = ¼[[A,U],A]`** (p. 116), as a matrix expression. -/
def jacK (A U : Matrix ι ι 𝕜) : Matrix ι ι 𝕜 :=
  (1 / 4 : ℝ) • ((A * U - U * A) * A - A * (A * U - U * A))

omit [DecidableEq ι] in
theorem smul_mul_eq_mul_jacK (q A U : Matrix ι ι 𝕜) :
    (1 / 4 : ℝ) • (q * ((A * U - U * A) * A - A * (A * U - U * A))) = q * jacK A U := by
  rw [jacK, Matrix.mul_smul]

section Group

variable {Z W : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {G : Set (Matrix ι ι 𝕜)} {hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι 𝕜) Z W G}
  {𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)}

namespace IsMatrixGroup

variable (h : IsMatrixGroup hG 𝔤)
include h

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem halfExp_mem {A : Matrix ι ι 𝕜} (hA : A ∈ 𝔤) (t : ℝ) : halfExp A t ∈ G :=
  h.exp_smul_mem (𝔤.smul_mem _ hA) t

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem conjTranspose_halfExp_mul_comm {A : Matrix ι ι 𝕜} (hA : A ∈ 𝔤) (t : ℝ) :
    (halfExp A t)ᴴ * A = A * (halfExp A t)ᴴ := by
  have h1 := congrArg conjTranspose (halfExp_mul_comm A t)
  rw [conjTranspose_mul, conjTranspose_mul, h.skew A hA, Matrix.neg_mul, Matrix.mul_neg] at h1
  exact (neg_inj.1 h1).symm

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- `exp(tA) ∈ G`. -/
theorem exp_smul_mem' {A : Matrix ι ι 𝕜} (hA : A ∈ 𝔤) (t : ℝ) :
    NormedSpace.exp (t • A) ∈ G :=
  h.exp_smul_mem hA t

/-- **The covariant derivative along `exp(tA)` in the frame `U ↦ hUh`**:
`D/dt (h U h) = h U' h` for a differentiable `𝔤`-valued `U`. -/
theorem covD_conj {A : Matrix ι ι 𝕜} (hA : A ∈ 𝔤) {U : ℝ → Matrix ι ι 𝕜} (hU𝔤 : ∀ s, U s ∈ 𝔤)
    (hU : Differentiable ℝ U) (t : ℝ) :
    covD hG (fun s => NormedSpace.exp (s • A)) (fun s => halfExp A s * U s * halfExp A s) t =
      halfExp A t * deriv U t * halfExp A t := by
  have hd := (hasDerivAt_conj A (hU t).hasDerivAt).deriv
  have hγ := h.exp_smul_mem hA t
  rw [covD, hd, h.prj_eq hγ, ← halfExp_mul_halfExp]
  have hh := h.halfExp_mem hA t
  have hu : (halfExp A t)ᴴ * halfExp A t = 1 := h.unitary _ hh
  set k := halfExp A t
  have hU' := deriv_mem_of_forall_mem hU𝔤 hU t
  have hkk : ∀ X : Matrix ι ι 𝕜, k * (kᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, mul_conjTranspose_eq_one hu, Matrix.one_mul]
  have hkk' : ∀ X : Matrix ι ι 𝕜, kᴴ * (k * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  -- `γᴴ (hMh) = hᴴ M h`
  have e1 : (k * k)ᴴ * (k * ((1 / 2 : ℝ) • (A * U t + U t * A) + deriv U t) * k) =
      kᴴ * deriv U t * k + kᴴ * ((1 / 2 : ℝ) • (A * U t + U t * A)) * k := by
    simp only [conjTranspose_mul, Matrix.mul_assoc, hkk', Matrix.mul_add, Matrix.add_mul]
    abel
  have hherm : (kᴴ * ((1 / 2 : ℝ) • (A * U t + U t * A)) * k)ᴴ =
      kᴴ * ((1 / 2 : ℝ) • (A * U t + U t * A)) * k := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_smul,
      star_trivial, conjTranspose_anticomm (h.skew A hA) (h.skew _ (hU𝔤 t)), Matrix.mul_assoc]
  rw [e1, algProj_add_hermitian h.skew (h.conj_mem' hh hU') hherm]
  simp only [Matrix.mul_assoc, hkk]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- `[[A, hᴴMh], A] = hᴴ[[A,M],A]h` when `h` is unitary and commutes with `A`. -/
theorem jacK_conj {A : Matrix ι ι 𝕜} (hA : A ∈ 𝔤) (t : ℝ) (M : Matrix ι ι 𝕜) :
    jacK A ((halfExp A t)ᴴ * M * halfExp A t) =
      (halfExp A t)ᴴ * jacK A M * halfExp A t := by
  have hc := halfExp_mul_comm A t
  have hc' := h.conjTranspose_halfExp_mul_comm hA t
  set k := halfExp A t
  have r2 : ∀ X : Matrix ι ι 𝕜, A * (kᴴ * X) = kᴴ * (A * X) := fun X => by
    rw [← Matrix.mul_assoc, ← hc', Matrix.mul_assoc]
  simp only [jacK, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc, hc, r2]

/-- **The curvature term along `exp(tA)`**: `R(γ', hMh)γ' = h K_A(M) h` for `M ∈ 𝔤`. -/
theorem curvR_conj {A : Matrix ι ι 𝕜} (hA : A ∈ 𝔤) {M : Matrix ι ι 𝕜} (hM : M ∈ 𝔤) (t : ℝ) :
    curvR hG (NormedSpace.exp (t • A)) (deriv (fun s => NormedSpace.exp (s • A)) t)
      (halfExp A t * M * halfExp A t) (deriv (fun s => NormedSpace.exp (s • A)) t) =
      halfExp A t * jacK A M * halfExp A t := by
  have hγ := h.exp_smul_mem hA t
  have hh := h.halfExp_mem hA t
  have hu : (halfExp A t)ᴴ * halfExp A t = 1 := h.unitary _ hh
  have hM' : (halfExp A t)ᴴ * M * halfExp A t ∈ 𝔤 := h.conj_mem' hh hM
  have hkk : ∀ X : Matrix ι ι 𝕜, halfExp A t * ((halfExp A t)ᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, mul_conjTranspose_eq_one hu, Matrix.one_mul]
  have hJ : halfExp A t * M * halfExp A t =
      NormedSpace.exp (t • A) * ((halfExp A t)ᴴ * M * halfExp A t) := by
    rw [← halfExp_mul_halfExp]
    simp only [Matrix.mul_assoc, hkk]
  rw [deriv_exp_smul, hJ, curvR_of_mem hG hγ]
  have := h.curvOp_mul ⟨_, hγ⟩ hA hM' hA
  simp only at this
  rw [this, smul_mul_eq_mul_jacK, h.jacK_conj hA t, ← halfExp_mul_halfExp]
  simp only [Matrix.mul_assoc, hkk]

/-- **Theorem 20.5 for matrix groups, the Jacobi equation**: along `γ(t) = exp(tA)`, the field
`J(t) = exp(tA/2) U(t) exp(tA/2)`, `U` a smooth `𝔤`-valued curve, is a Jacobi field as soon as
`U'' + K_A(U) = 0` with `K_A(U) = ¼[[A,U],A]` (constant coefficients: Milnor's
`w_i'' + e_i w_i = 0`). -/
theorem isJacobiField_conj {A : Matrix ι ι 𝕜} (hA : A ∈ 𝔤) {U : ℝ → Matrix ι ι 𝕜}
    (hU𝔤 : ∀ s, U s ∈ 𝔤) (hU : ContDiff ℝ ∞ U)
    (hODE : ∀ s, deriv (deriv U) s + jacK A (U s) = 0) :
    IsJacobiField hG (fun s => NormedSpace.exp (s • A))
      (fun s => halfExp A s * U s * halfExp A s) := by
  have hUd : Differentiable ℝ U := hU.differentiable (by simp)
  have hU'𝔤 : ∀ s, deriv U s ∈ 𝔤 := deriv_mem_of_forall_mem hU𝔤 hUd
  have hU'd : Differentiable ℝ (deriv U) :=
    (hU.iterate_deriv 1).differentiable (by simp)
  refine ⟨((contDiff_halfExp A).mul hU |>.mul (contDiff_halfExp A)).contDiffOn,
    fun t _ => ?_, fun t _ => ?_⟩
  · have hγ := h.exp_smul_mem hA t
    have hh := h.halfExp_mem hA t
    have hu : (halfExp A t)ᴴ * halfExp A t = 1 := h.unitary _ hh
    have hkk : ∀ X : Matrix ι ι 𝕜, halfExp A t * ((halfExp A t)ᴴ * X) = X := fun X => by
      rw [← Matrix.mul_assoc, mul_conjTranspose_eq_one hu, Matrix.one_mul]
    have hkk' : ∀ X : Matrix ι ι 𝕜, (halfExp A t)ᴴ * (halfExp A t * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
    rw [h.prj_eq hγ, ← halfExp_mul_halfExp]
    have e : (halfExp A t * halfExp A t)ᴴ * (halfExp A t * U t * halfExp A t) =
        (halfExp A t)ᴴ * U t * halfExp A t := by
      simp only [conjTranspose_mul, Matrix.mul_assoc, hkk']
    rw [e, algProj_of_mem (h.conj_mem' hh (hU𝔤 t))]
    simp only [Matrix.mul_assoc, hkk]
  · have hcov : covD hG (fun s => NormedSpace.exp (s • A))
        (fun s => halfExp A s * U s * halfExp A s) =
        fun s => halfExp A s * deriv U s * halfExp A s :=
      funext (h.covD_conj hA hU𝔤 hUd)
    rw [jacobiExpr, hcov, h.covD_conj hA hU'𝔤 hU'd, h.curvR_conj hA (hU𝔤 t), ← Matrix.add_mul,
      ← Matrix.mul_add, hODE t, Matrix.mul_zero, Matrix.zero_mul]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- `γ(t) = exp(tA)` is a smooth curve in `G` (on `[0, 1]`). -/
theorem isSmoothCurveIn_exp_smul {A : Matrix ι ι 𝕜} (hA : A ∈ 𝔤) :
    IsSmoothCurveIn hG (fun s => NormedSpace.exp (s • A)) :=
  ⟨(contDiff_exp_smul A).contDiffOn, fun t _ => h.exp_smul_mem hA t⟩

/-- The covariant derivative at `0` of `t ↦ h(t)U(t)h(t)` is `U'(0)`. -/
theorem covAlong_conj_zero {A : Matrix ι ι 𝕜} (hA : A ∈ 𝔤) {U : ℝ → Matrix ι ι 𝕜}
    (hU𝔤 : ∀ s, U s ∈ 𝔤) (hU : Differentiable ℝ U) :
    covAlong hG (fun s => NormedSpace.exp (s • A)) (fun s => halfExp A s * U s * halfExp A s) 0 =
      deriv U 0 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hd := hasDerivAt_conj A (hU 0).hasDerivAt
  rw [covAlong, hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one 0 h0), ← hd.deriv]
  have := h.covD_conj hA hU𝔤 hU 0
  rw [covD] at this
  rw [this, halfExp_zero, Matrix.one_mul, Matrix.mul_one]

end IsMatrixGroup

end Group

end Morse
