import Morse.Chapter12.GroupJacobi
import Morse.Chapter14.SUMatrices

/-!
Milnor, *Morse Theory*, Theorem 20.5 (pp. 110–111) and §23 (pp. 130–131): the Jacobi fields
along `t ↦ exp(tA)` in `SU(n)`, for `A` conjugate to a diagonal matrix.

# Explicit Jacobi fields in `SU(n)`

## Milnor's text, paraphrased

* p. 111 (proof of 20.5): in an eigenbasis `U_i` of `K_V` (eigenvalue `e_i`), the Jacobi fields
  vanishing at `0` are `Σ c_i s_i(t) U_i(t)` with `s_i(t) = sin(√e_i t)/√e_i` (`= t` if `e_i = 0`).
* p. 131: for `A = diag(iπk_1, …, iπk_n)`, `K_A(W) = (π²/4 (k_j − k_l)² w_{jl})`: the eigenvectors
  of `K_A` are the matrix units (suitably combined into skew-Hermitian matrices).

## What is formalized

Let `A = T D Tᴴ` with `T` unitary and `D = diag(ia_1, …, ia_n)` (`Morse.diagI`), and put
`b_{jl} = (a_j − a_l)/2` (so `K_D` multiplies the `(j,l)` entry by `b_{jl}²`,
`Morse.jacK_diagI_apply`, and `K_A(TMTᴴ) = T K_D(M) Tᴴ`, `Morse.jacK_conj_unitary`).

* `Morse.jacSin b t = sin(bt)/b` (`= t` for `b = 0`): Milnor's `s_i`.
* `Morse.hadSin a W t`: the matrix with entries `s_{b_{jl}}(t) w_{jl}` (the Hadamard product
  `S(t) ⊙ W`), and `Morse.suSol a T C t = T (S(t) ⊙ TᴴCT) Tᴴ`: the solution of
  `U'' + K_A(U) = 0`, `U(0) = 0`, `U'(0) = C` (`Morse.suSol_ode`, `Morse.suSol_zero`,
  `Morse.deriv_suSol_zero`).  It stays in `𝔰𝔲(n)` for `C ∈ 𝔰𝔲(n)` (`Morse.suSol_mem`).
* `Morse.isJacobiField_suJac`: **`J_C(t) = exp(tA/2) U_C(t) exp(tA/2)` is a Jacobi field along
  `exp(tA)` in `SU(n)`**, with `J_C(0) = 0` and `DJ_C/dt(0) = C`, and
  `Morse.suJac_eq_zero_iff`: `J_C(t) = 0` iff `s_{b_{jl}}(t) (TᴴCT)_{jl} = 0` for all `j, l`.

## Gaps in Milnor's text

* p. 131: Milnor reads the spectrum of `K_A` off the matrix units, which are not skew-Hermitian;
  the eigenvectors in `𝔰𝔲(n)` are his `E_{jl}`, `E'_{jl}`.  Here no eigenbasis is needed: the
  Jacobi equation is solved entrywise, `U(t) = S(t) ⊙ U'(0)` in the basis where `A` is diagonal.
-/

open Matrix Set Filter Topology Module
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

/-! ### `sin(bt)/b` -/

/-- **Milnor's `s(t) = sin(bt)/b`** (`= t` for `b = 0`): the solution of `w'' + b²w = 0` with
`w(0) = 0`, `w'(0) = 1`. -/
def jacSin (b t : ℝ) : ℝ := if b = 0 then t else Real.sin (b * t) / b

theorem jacSin_of_eq_zero (t : ℝ) : jacSin 0 t = t := if_pos rfl

theorem jacSin_of_ne {b : ℝ} (hb : b ≠ 0) (t : ℝ) : jacSin b t = Real.sin (b * t) / b :=
  if_neg hb

@[simp] theorem jacSin_zero (b : ℝ) : jacSin b 0 = 0 := by
  unfold jacSin; split_ifs <;> simp

theorem jacSin_neg (b t : ℝ) : jacSin (-b) t = jacSin b t := by
  unfold jacSin
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (neg_eq_zero.1 h1) h2
  · exact absurd (by rw [h2, neg_zero]) h1
  · rw [neg_mul, Real.sin_neg, neg_div_neg_eq]

theorem hasDerivAt_jacSin (b t : ℝ) : HasDerivAt (jacSin b) (Real.cos (b * t)) t := by
  by_cases hb : b = 0
  · subst hb
    have e : jacSin 0 = id := funext jacSin_of_eq_zero
    rw [e, zero_mul, Real.cos_zero]
    exact hasDerivAt_id t
  · have e : jacSin b = fun s => Real.sin (b * s) / b := funext (jacSin_of_ne hb)
    rw [e]
    have h1 : HasDerivAt (fun s => b * s) b t := by simpa using (hasDerivAt_id t).const_mul b
    have h2 : HasDerivAt (fun s => Real.sin (b * s)) (Real.cos (b * t) * b) t :=
      (Real.hasDerivAt_sin (b * t)).comp t h1
    have h3 := h2.div_const b
    rwa [mul_div_assoc, div_self hb, mul_one] at h3

theorem hasDerivAt_cos_mul_jacSin (b t : ℝ) :
    HasDerivAt (fun s => Real.cos (b * s)) (-(b ^ 2 * jacSin b t)) t := by
  have h1 : HasDerivAt (fun s => b * s) b t := by simpa using (hasDerivAt_id t).const_mul b
  have h2 : HasDerivAt (fun s => Real.cos (b * s)) (-Real.sin (b * t) * b) t :=
    (Real.hasDerivAt_cos (b * t)).comp t h1
  refine h2.congr_deriv ?_
  by_cases hb : b = 0
  · subst hb; simp
  · rw [jacSin_of_ne hb]
    field_simp

theorem contDiff_jacSin (b : ℝ) : ContDiff ℝ ∞ (jacSin b) := by
  by_cases hb : b = 0
  · subst hb
    have : jacSin 0 = id := funext jacSin_of_eq_zero
    rw [this]
    exact contDiff_id
  · have : jacSin b = fun s => Real.sin (b * s) / b := funext (jacSin_of_ne hb)
    rw [this]
    exact (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).div_const b

/-- For `b ≠ 0`, `sin(bt)/b = 0` iff `bt ∈ πℤ`. -/
theorem jacSin_eq_zero_iff {b : ℝ} (hb : b ≠ 0) (t : ℝ) :
    jacSin b t = 0 ↔ ∃ s : ℤ, b * t = Real.pi * s := by
  rw [jacSin_of_ne hb, div_eq_zero_iff, or_iff_left hb, Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by rw [← hn]; ring⟩
  · rintro ⟨n, hn⟩; exact ⟨n, by rw [hn]; ring⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Hadamard products with `S(t)` -/

/-- `S(t) ⊙ W`: the matrix with entries `s_{b_{jl}}(t) w_{jl}`, `b_{jl} = (a_j − a_l)/2`. -/
def hadSin (a : ι → ℝ) (W : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  of fun j l => (jacSin ((a j - a l) / 2) t : ℂ) * W j l

/-- `S'(t) ⊙ W`, entries `cos(b_{jl} t) w_{jl}`. -/
def hadCos (a : ι → ℝ) (W : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  of fun j l => (Real.cos ((a j - a l) / 2 * t) : ℂ) * W j l

/-- `−S''(t) ⊙ W`, entries `b_{jl}² s_{b_{jl}}(t) w_{jl}`. -/
def hadSin2 (a : ι → ℝ) (W : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  of fun j l => (((a j - a l) / 2) ^ 2 * jacSin ((a j - a l) / 2) t : ℝ) * W j l

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem hadSin_apply (a : ι → ℝ) (W : Matrix ι ι ℂ) (t : ℝ) (j l : ι) :
    hadSin a W t j l = (jacSin ((a j - a l) / 2) t : ℂ) * W j l := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem hadCos_apply (a : ι → ℝ) (W : Matrix ι ι ℂ) (t : ℝ) (j l : ι) :
    hadCos a W t j l = (Real.cos ((a j - a l) / 2 * t) : ℂ) * W j l := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem hadSin2_apply (a : ι → ℝ) (W : Matrix ι ι ℂ) (t : ℝ) (j l : ι) :
    hadSin2 a W t j l = (((a j - a l) / 2) ^ 2 * jacSin ((a j - a l) / 2) t : ℝ) * W j l := rfl

/-- `f ⊙ W = Σ_{j,l} f_{jl} E_{jl}(w_{jl})`, a real combination of constant matrices. -/
theorem of_mul_eq_sum (f : ι → ι → ℝ) (W : Matrix ι ι ℂ) :
    (of fun j l => (f j l : ℂ) * W j l : Matrix ι ι ℂ) = ∑ j, ∑ l, f j l • single j l (W j l) := by
  conv_lhs => rw [matrix_eq_sum_single (of fun j l => (f j l : ℂ) * W j l)]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [of_apply, smul_single, Complex.real_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem hasDerivAt_hadSin [Finite ι] (a : ι → ℝ) (W : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (hadSin a W) (hadCos a W t) t := by
  classical
  have := Fintype.ofFinite ι
  have e1 : hadSin a W = fun s => ∑ j, ∑ l, jacSin ((a j - a l) / 2) s • single j l (W j l) :=
    funext fun s => of_mul_eq_sum (fun j l => jacSin ((a j - a l) / 2) s) W
  rw [e1, hadCos, of_mul_eq_sum (fun j l => Real.cos ((a j - a l) / 2 * t)) W]
  exact HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun l _ =>
    (hasDerivAt_jacSin _ t).smul_const _

omit [Fintype ι] [DecidableEq ι] in
theorem hasDerivAt_hadCos [Finite ι] (a : ι → ℝ) (W : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (hadCos a W) (-hadSin2 a W t) t := by
  classical
  have := Fintype.ofFinite ι
  have e1 : hadCos a W = fun s => ∑ j, ∑ l, Real.cos ((a j - a l) / 2 * s) • single j l (W j l) :=
    funext fun s => of_mul_eq_sum (fun j l => Real.cos ((a j - a l) / 2 * s)) W
  have e2 : -hadSin2 a W t = ∑ j, ∑ l, (-(((a j - a l) / 2) ^ 2 * jacSin ((a j - a l) / 2) t)) •
      single j l (W j l) := by
    rw [hadSin2, of_mul_eq_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => (neg_smul _ _).symm
  rw [e1, e2]
  exact HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun l _ =>
    (hasDerivAt_cos_mul_jacSin _ t).smul_const _

omit [DecidableEq ι] in
theorem contDiff_hadSin (a : ι → ℝ) (W : Matrix ι ι ℂ) : ContDiff ℝ ∞ (hadSin a W) := by
  classical
  have e1 : hadSin a W = fun s => ∑ j, ∑ l, jacSin ((a j - a l) / 2) s • single j l (W j l) :=
    funext fun s => of_mul_eq_sum (fun j l => jacSin ((a j - a l) / 2) s) W
  rw [e1]
  exact ContDiff.sum fun j _ => ContDiff.sum fun l _ => (contDiff_jacSin _).smul contDiff_const

omit [Fintype ι] [DecidableEq ι] in
theorem hadSin_zero (a : ι → ℝ) (W : Matrix ι ι ℂ) : hadSin a W 0 = 0 := by
  ext j l; simp

omit [Fintype ι] [DecidableEq ι] in
theorem hadCos_zero (a : ι → ℝ) (W : Matrix ι ι ℂ) : hadCos a W 0 = W := by
  ext j l; simp

/-! ### `K_D` and `K_A` -/

/-- `D_a = diag(ia_1, …, ia_n)`. -/
def diagI (a : ι → ℝ) : Matrix ι ι ℂ := diagonal fun j => (a j : ℂ) * Complex.I

/-- **Milnor's computation** (p. 131), for `D = diag(ia_j)`: `K_D` multiplies the `(j,l)` entry by
`((a_j − a_l)/2)²`. -/
theorem jacK_diagI_apply (a : ι → ℝ) (M : Matrix ι ι ℂ) (j l : ι) :
    jacK (diagI a) M j l = ((((a j - a l) / 2) ^ 2 : ℝ) : ℂ) * M j l := by
  simp only [jacK, diagI, Matrix.smul_apply, Matrix.sub_apply, mul_diagonal, diagonal_mul,
    Complex.real_smul]
  push_cast
  linear_combination (-(1 / 4 : ℂ) * ((a j : ℂ) - a l) ^ 2 * M j l) * Complex.I_sq

theorem jacK_diagI_hadSin (a : ι → ℝ) (W : Matrix ι ι ℂ) (t : ℝ) :
    jacK (diagI a) (hadSin a W t) = hadSin2 a W t := by
  ext j l
  rw [jacK_diagI_apply, hadSin_apply, hadSin2_apply]
  push_cast
  ring

/-- `K_{TDTᴴ}(TMTᴴ) = T K_D(M) Tᴴ` for unitary `T`. -/
theorem jacK_conj_unitary {T : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) (D M : Matrix ι ι ℂ) :
    jacK (T * D * Tᴴ) (T * M * Tᴴ) = T * jacK D M * Tᴴ := by
  have r : ∀ X : Matrix ι ι ℂ, Tᴴ * (T * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hT, Matrix.one_mul]
  simp only [jacK, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc, r]

omit [Fintype ι] in
/-- `suDiag k = diag(iπk_j)` is `D_a` for `a = πk`. -/
theorem suDiag_eq_diagI (k : ι → ℤ) : suDiag k = diagI fun j => Real.pi * k j := by
  ext j l
  simp only [suDiag, diagI, diagonal_apply]
  split_ifs <;> push_cast <;> rfl

/-! ### The solutions `U_C(t) = T (S(t) ⊙ TᴴCT) Tᴴ` -/

/-- **The solution of `U'' + K_A(U) = 0`, `U(0) = 0`, `U'(0) = C`**, for `A = T D_a Tᴴ`:
`U_C(t) = T (S(t) ⊙ TᴴCT) Tᴴ`. -/
def suSol (a : ι → ℝ) (T C : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  T * hadSin a (Tᴴ * C * T) t * Tᴴ

omit [DecidableEq ι] in
theorem hasDerivAt_suSol (a : ι → ℝ) (T C : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (suSol a T C) (T * hadCos a (Tᴴ * C * T) t * Tᴴ) t := by
  classical
  exact ((hasDerivAt_hadSin a _ t).const_mul T).mul_const Tᴴ

omit [DecidableEq ι] in
theorem deriv_suSol (a : ι → ℝ) (T C : Matrix ι ι ℂ) :
    deriv (suSol a T C) = fun t => T * hadCos a (Tᴴ * C * T) t * Tᴴ :=
  funext fun t => (hasDerivAt_suSol a T C t).deriv

omit [DecidableEq ι] in
theorem deriv_deriv_suSol (a : ι → ℝ) (T C : Matrix ι ι ℂ) (t : ℝ) :
    deriv (deriv (suSol a T C)) t = -(T * hadSin2 a (Tᴴ * C * T) t * Tᴴ) := by
  classical
  rw [deriv_suSol]
  have h := ((hasDerivAt_hadCos a (Tᴴ * C * T) t).const_mul T).mul_const Tᴴ
  rw [h.deriv, Matrix.mul_neg, Matrix.neg_mul]

omit [DecidableEq ι] in
theorem contDiff_suSol (a : ι → ℝ) (T C : Matrix ι ι ℂ) : ContDiff ℝ ∞ (suSol a T C) := by
  classical
  exact (contDiff_const.mul (contDiff_hadSin a _)).mul contDiff_const

/-- **`U_C'' + K_A(U_C) = 0`** for `A = T D_a Tᴴ`, `T` unitary. -/
theorem suSol_ode {T : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) (a : ι → ℝ) (C : Matrix ι ι ℂ) (t : ℝ) :
    deriv (deriv (suSol a T C)) t + jacK (T * diagI a * Tᴴ) (suSol a T C t) = 0 := by
  rw [deriv_deriv_suSol, suSol, jacK_conj_unitary hT, jacK_diagI_hadSin, neg_add_cancel]

omit [DecidableEq ι] in
theorem suSol_zero (a : ι → ℝ) (T C : Matrix ι ι ℂ) : suSol a T C 0 = 0 := by
  simp [suSol, hadSin_zero]

theorem deriv_suSol_zero {T : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) (a : ι → ℝ) (C : Matrix ι ι ℂ) :
    deriv (suSol a T C) 0 = C := by
  have hT' : T * Tᴴ = 1 := mul_conjTranspose_eq_one hT
  rw [deriv_suSol]
  dsimp only
  rw [hadCos_zero, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hT', Matrix.one_mul,
    Matrix.mul_assoc, hT', Matrix.mul_one]

/-! ### `𝔰𝔲(n)` is preserved -/

/-- Conjugation by a unitary `T` preserves `𝔰𝔲(n)`. -/
theorem conj_mem_specialSkewHermitian {T : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) {M : Matrix ι ι ℂ}
    (hM : M ∈ specialSkewHermitian ι) : T * M * Tᴴ ∈ specialSkewHermitian ι := by
  obtain ⟨h1, h2⟩ := hM
  refine ⟨?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, h1, Matrix.neg_mul,
      Matrix.mul_neg, Matrix.mul_assoc]
  · rw [trace_mul_comm, ← Matrix.mul_assoc, hT, Matrix.one_mul, h2]

theorem conj_mem_specialSkewHermitian' {T : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) {M : Matrix ι ι ℂ}
    (hM : M ∈ specialSkewHermitian ι) : Tᴴ * M * T ∈ specialSkewHermitian ι := by
  have := conj_mem_specialSkewHermitian (T := Tᴴ) (by
    rw [conjTranspose_conjTranspose]; exact mul_conjTranspose_eq_one hT) hM
  rwa [conjTranspose_conjTranspose] at this

/-- `S(t) ⊙ W ∈ 𝔰𝔲(n)` for `W ∈ 𝔰𝔲(n)`: `S(t)` is real and symmetric, with diagonal `t`. -/
theorem hadSin_mem (a : ι → ℝ) {W : Matrix ι ι ℂ} (hW : W ∈ specialSkewHermitian ι) (t : ℝ) :
    hadSin a W t ∈ specialSkewHermitian ι := by
  obtain ⟨h1, h2⟩ := hW
  refine ⟨?_, ?_⟩
  · ext j l
    have hW' : star (W l j) = -W j l := by
      have := congrFun (congrFun h1 j) l
      simpa using this
    rw [conjTranspose_apply, hadSin_apply, Matrix.neg_apply, hadSin_apply, star_mul',
      hW', show (a l - a j) / 2 = -((a j - a l) / 2) by ring, jacSin_neg, Complex.star_def,
      Complex.conj_ofReal, mul_neg]
  · have : trace (hadSin a W t) = (t : ℂ) * trace W := by
      simp only [trace, diag_apply, hadSin_apply, sub_self, zero_div, jacSin_of_eq_zero,
        Finset.mul_sum]
    rw [this, h2, mul_zero]

theorem suSol_mem {T : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) (a : ι → ℝ) {C : Matrix ι ι ℂ}
    (hC : C ∈ specialSkewHermitian ι) (t : ℝ) : suSol a T C t ∈ specialSkewHermitian ι :=
  conj_mem_specialSkewHermitian hT (hadSin_mem a (conj_mem_specialSkewHermitian' hT hC) t)

/-! ### The Jacobi fields `J_C` in `SU(n)` -/

/-- **The Jacobi field `J_C(t) = exp(tA/2) U_C(t) exp(tA/2)`** along `exp(tA)`,
`A = T D_a Tᴴ`. -/
def suJac (a : ι → ℝ) (T C : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  halfExp (T * diagI a * Tᴴ) t * suSol a T C t * halfExp (T * diagI a * Tᴴ) t

theorem suJac_zero (a : ι → ℝ) (T C : Matrix ι ι ℂ) : suJac a T C 0 = 0 := by
  simp [suJac, suSol_zero]

variable [Nonempty ι]

/-- **`J_C` is a Jacobi field along `t ↦ exp(tA)` in `SU(n)`** (Theorem 20.5, for `SU(n)`), for
`A = T D_a Tᴴ ∈ 𝔰𝔲(n)` and `C ∈ 𝔰𝔲(n)`. -/
theorem isJacobiField_suJac {T : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) {a : ι → ℝ}
    (hA : T * diagI a * Tᴴ ∈ specialSkewHermitian ι) {C : Matrix ι ι ℂ}
    (hC : C ∈ specialSkewHermitian ι) :
    IsJacobiField isSliceSubmanifold_specialUnitaryGroup
      (fun s => NormedSpace.exp (s • (T * diagI a * Tᴴ))) (suJac a T C) :=
  isMatrixGroup_specialUnitaryGroup.isJacobiField_conj hA (suSol_mem hT a hC)
    (contDiff_suSol a T C) (suSol_ode hT a C)

/-- `DJ_C/dt(0) = C`. -/
theorem covAlong_suJac_zero {T : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) {a : ι → ℝ}
    (hA : T * diagI a * Tᴴ ∈ specialSkewHermitian ι) {C : Matrix ι ι ℂ}
    (hC : C ∈ specialSkewHermitian ι) :
    covAlong isSliceSubmanifold_specialUnitaryGroup
      (fun s => NormedSpace.exp (s • (T * diagI a * Tᴴ))) (suJac a T C) 0 = C := by
  have e : suJac a T C = fun t => halfExp (T * diagI a * Tᴴ) t * suSol a T C t *
      halfExp (T * diagI a * Tᴴ) t := rfl
  rw [e, isMatrixGroup_specialUnitaryGroup.covAlong_conj_zero hA (suSol_mem hT a hC)
    ((contDiff_suSol a T C).differentiable (by simp)), deriv_suSol_zero hT]

/-- **The zeros of `J_C`**: `J_C(t) = 0` iff `s_{ω_{jl}}(t) (TᴴCT)_{jl} = 0` for all `j, l`. -/
theorem suJac_eq_zero_iff {T : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) {a : ι → ℝ}
    (hA : T * diagI a * Tᴴ ∈ specialSkewHermitian ι) (C : Matrix ι ι ℂ) (t : ℝ) :
    suJac a T C t = 0 ↔ hadSin a (Tᴴ * C * T) t = 0 := by
  have hh := isMatrixGroup_specialUnitaryGroup.halfExp_mem hA t
  have hu := isMatrixGroup_specialUnitaryGroup.unitary _ hh
  have hu' := mul_conjTranspose_eq_one hu
  have hT' := mul_conjTranspose_eq_one hT
  set k := halfExp (T * diagI a * Tᴴ) t
  have r1 : ∀ Y : Matrix ι ι ℂ, kᴴ * (k * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have r2 : ∀ Y : Matrix ι ι ℂ, Tᴴ * (T * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hT, Matrix.one_mul]
  have r3 : ∀ Y : Matrix ι ι ℂ, k * (kᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hu', Matrix.one_mul]
  have hJ : suJac a T C t = k * (T * hadSin a (Tᴴ * C * T) t * Tᴴ) * k := rfl
  constructor
  · intro h0
    have h1 : Tᴴ * (kᴴ * (suJac a T C t * (kᴴ * T))) = hadSin a (Tᴴ * C * T) t := by
      rw [hJ]
      simp only [Matrix.mul_assoc, r1, r2, r3, hT, Matrix.mul_one]
    rw [← h1, h0, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
  · intro h0
    simp only [suJac, suSol, h0, Matrix.mul_zero, Matrix.zero_mul]

end Morse
