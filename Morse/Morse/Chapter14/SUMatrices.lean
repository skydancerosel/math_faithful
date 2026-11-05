import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Module

/-!
Milnor, *Morse Theory*, §23, pp. 124–131: the matrix computations.

# Geodesics from `I` to `−I` in `SU(n)` and the operator `K_A`

## Milnor's text, paraphrased

* p. 125: the left- and right-invariant metric on `U(n)` is `⟨A,B⟩ = Re tr(AB*)` on the
  skew-Hermitian matrices.
* p. 127: for `A = diag(ia_1, …, ia_n)`, `exp A = diag(e^{ia_1}, …, e^{ia_n})`, so `exp A = −I`
  iff `A = diag(k_1iπ, …, k_niπ)` with the `k_j` odd; the geodesic `t ↦ exp tA` has length
  `|A| = (tr AA*)^{1/2} = π(Σ k_j²)^{1/2}`.  A minimal `A` (all `k_j = ±1`) is completely
  determined by `Eigen(iπ)`, an arbitrary subspace of `ℂⁿ`; in `SU(2m)`, where
  `tr A = 0`, an arbitrary `m`-dimensional one (Lemma 23.1).
* pp. 130–131: `K_A(W) = R(A,W)A = ¼[[A,W],A]`; for `A = diag(iπk_1, …, iπk_n)` "a short
  computation shows" `[A,W] = (iπ(k_j − k_l)w_{jl})`, `[A,[A,W]] = (−π²(k_j − k_l)²w_{jl})`,
  `K_A(W) = (π²/4 (k_j − k_l)² w_{jl})`; a basis of eigenvectors of `K_A` on `𝔤'`: `E_{jl}`
  (`+1` at `(j,l)`, `−1` at `(l,j)`) and `E'_{jl}` (`+i` at both), `j < l`, with eigenvalue
  `π²(k_j − k_l)²/4`, and the diagonal matrices of `𝔤'`, with eigenvalue `0`.

## What is formalized

* `Morse.exp_diagonal_eq_neg_one_iff`: `exp diag(ia_j) = −I` iff every `a_j` is an odd
  multiple of `π`.  `Morse.trace_suDiag_mul_conjTranspose`: `|A|² = tr AA* = π² Σ k_j²`;
  `Morse.trace_suDiag`: `tr A = iπ Σ k_j`.
* `Morse.sq_eq_neg_pi_sq_iff` and `Morse.trace_pi_smul_projection` (Lemma 23.1, as a set): a
  skew-Hermitian `A` has `A² = −π²I` (all eigenvalues `±iπ`, i.e. the minimal geodesics, by
  `Morse.sum_sq_eq_card_iff`) iff `A = iπ(2P − I)` for a Hermitian projection `P` (onto
  `Eigen(iπ)`), and then `tr A = iπ(2 tr P − n)`, which vanishes iff `tr P = n/2`.
* `Morse.jacobiMat_suDiag_apply` (the entrywise formula), `Morse.jacobiMat_eReal`,
  `Morse.jacobiMat_eImag`, `Morse.jacobiMat_diagonal` (the eigenvectors),
  `Morse.eReal_conjTranspose`, `Morse.eImag_conjTranspose`, `Morse.trace_eReal`,
  `Morse.trace_eImag` (they lie in `𝔰𝔲(n)`), and `Morse.eq_diagonal_add_sum_eReal_eImag` (they
  span the skew-Hermitian matrices).

Not formalized here: the reduction to diagonal `A` (spectral theorem, and invariance of the index
under conjugation), the linear independence count `n(n−1) + (n−1) = dim 𝔰𝔲(n)`, `tr P = dim E`,
and the topology of the identification with the Grassmannian.  The reduction is
`Morse.exists_unitary_suDiag` (`Morse/Chapter12/SUIndex.lean`, where the index is computed without
an eigenbasis count), and the identification of the minimal geodesics with the Hermitian
projections of trace `m` is `Morse.lemma_23_1` (`Morse/Chapter12/SUMinimal.lean`).

## Gaps in Milnor's text

* p. 127, "`A` is completely determined by `Eigen(iπ)`": this is `A = iπ(2P − I)`, `P` the
  orthogonal projection onto `Eigen(iπ)`, which uses that a skew-Hermitian matrix is normal, so
  that its eigenspaces are orthogonal (`Morse.sq_eq_neg_pi_sq_iff` gives it without the spectral
  theorem).
* p. 131: Milnor does not say why his eigenvectors span `𝔤'`
  (`Morse.eq_diagonal_add_sum_eReal_eImag`).
-/

open Finset Real

noncomputable section

namespace Morse

section Matrices

open Matrix Complex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Milnor's velocity `A = diag(iπk_1, …, iπk_n)` (p. 130). -/
def suDiag (k : ι → ℤ) : Matrix ι ι ℂ := diagonal fun j => (π * k j : ℂ) * I

/-- `K_A(W) = R(A,W)A = ¼[[A,W],A]` (p. 130, by Theorem 21.3(b)). -/
def jacobiMat (A W : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 4 : ℂ) • ((A * W - W * A) * A - A * (A * W - W * A))

omit [Fintype ι] in
/-- `[A, W]` for diagonal `A = diag(d)`: entry `(j,l)` is `(d_j − d_l) w_{jl}`. -/
theorem commutator_diagonal_apply [Fintype ι] (d : ι → ℂ) (W : Matrix ι ι ℂ) (j l : ι) :
    (diagonal d * W - W * diagonal d) j l = (d j - d l) * W j l := by
  simp only [Matrix.sub_apply, diagonal_mul, mul_diagonal]
  ring

/-- **Milnor's computation** (p. 131): `K_A(W) = (π²/4 (k_j − k_l)² w_{jl})`. -/
theorem jacobiMat_suDiag_apply (k : ι → ℤ) (W : Matrix ι ι ℂ) (j l : ι) :
    jacobiMat (suDiag k) W j l = ((π ^ 2 / 4 * ((k j : ℝ) - k l) ^ 2 : ℝ) : ℂ) * W j l := by
  simp only [jacobiMat, suDiag, Matrix.smul_apply, Matrix.sub_apply, mul_diagonal, diagonal_mul,
    smul_eq_mul]
  push_cast
  linear_combination (-(1 / 4 : ℂ) * π ^ 2 * ((k j : ℂ) - k l) ^ 2 * W j l) * I_sq

/-- Milnor's `E_{jl}`: `+1` at `(j,l)`, `−1` at `(l,j)`. -/
def eReal (j l : ι) : Matrix ι ι ℂ := single j l 1 - single l j 1

/-- Milnor's `E'_{jl}`: `+i` at `(j,l)` and at `(l,j)`. -/
def eImag (j l : ι) : Matrix ι ι ℂ := single j l I + single l j I

/-- `E_{jl}` is an eigenvector of `K_A` with eigenvalue `π²(k_j − k_l)²/4`. -/
theorem jacobiMat_eReal (k : ι → ℤ) (j l : ι) :
    jacobiMat (suDiag k) (eReal j l) =
      ((π ^ 2 / 4 * ((k j : ℝ) - k l) ^ 2 : ℝ) : ℂ) • eReal j l := by
  ext a b
  rw [jacobiMat_suDiag_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [eReal, Matrix.sub_apply, single_apply]
  by_cases h1 : j = a ∧ l = b
  · obtain ⟨rfl, rfl⟩ := h1; simp
  · by_cases h2 : l = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h2
      simp only [and_self, if_true]
      split_ifs
      push_cast
      ring
    · rw [if_neg h1, if_neg h2]; simp

/-- `E'_{jl}` is an eigenvector of `K_A` with eigenvalue `π²(k_j − k_l)²/4`. -/
theorem jacobiMat_eImag (k : ι → ℤ) (j l : ι) :
    jacobiMat (suDiag k) (eImag j l) =
      ((π ^ 2 / 4 * ((k j : ℝ) - k l) ^ 2 : ℝ) : ℂ) • eImag j l := by
  ext a b
  rw [jacobiMat_suDiag_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [eImag, Matrix.add_apply, single_apply]
  by_cases h1 : j = a ∧ l = b
  · obtain ⟨rfl, rfl⟩ := h1; simp
  · by_cases h2 : l = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h2
      simp only [and_self, if_true]
      split_ifs
      push_cast
      ring
    · rw [if_neg h1, if_neg h2]; simp

/-- Diagonal matrices are eigenvectors of `K_A` with eigenvalue `0`. -/
theorem jacobiMat_diagonal (k : ι → ℤ) (d : ι → ℂ) : jacobiMat (suDiag k) (diagonal d) = 0 := by
  ext a b
  rw [jacobiMat_suDiag_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [diagonal_apply_ne _ h]

omit [Fintype ι] in
theorem eReal_conjTranspose (j l : ι) : (eReal j l)ᴴ = -eReal j l := by
  rw [eReal, conjTranspose_sub, conjTranspose_single, conjTranspose_single, star_one, neg_sub]

omit [Fintype ι] in
theorem eImag_conjTranspose (j l : ι) : (eImag j l)ᴴ = -eImag j l := by
  rw [eImag, conjTranspose_add, conjTranspose_single, conjTranspose_single, RCLike.star_def, conj_I,
    ← single_neg, ← single_neg, neg_add, add_comm]

theorem trace_eReal {j l : ι} (h : j ≠ l) : trace (eReal j l) = 0 := by
  simp [eReal, trace_sub, trace_single_eq_of_ne _ _ _ h, trace_single_eq_of_ne _ _ _ (Ne.symm h)]

theorem trace_eImag {j l : ι} (h : j ≠ l) : trace (eImag j l) = 0 := by
  simp [eImag, trace_add, trace_single_eq_of_ne _ _ _ h, trace_single_eq_of_ne _ _ _ (Ne.symm h)]

/-- **The eigenvectors span** (the step behind Milnor's "a basis for `𝔤'` consisting of
eigenvectors of `K_A`", p. 131): every skew-Hermitian `W` is its diagonal part plus
`Σ_{j<l} (Re w_{jl} E_{jl} + Im w_{jl} E'_{jl})`. -/
theorem eq_diagonal_add_sum_eReal_eImag [LinearOrder ι] (W : Matrix ι ι ℂ) (hW : Wᴴ = -W) :
    W = diagonal (fun j => W j j) + ∑ j, ∑ l,
      if j < l then (((W j l).re : ℂ) • eReal j l + ((W j l).im : ℂ) • eImag j l) else 0 := by
  have hskew : ∀ a b, W a b = -(starRingEnd ℂ) (W b a) := by
    intro a b
    have := congrFun (congrFun hW a) b
    simp only [conjTranspose_apply, Matrix.neg_apply, RCLike.star_def] at this
    rw [this, neg_neg]
  ext a b
  simp only [Matrix.add_apply, Matrix.sum_apply]
  have hterm : ∀ j l, (if j < l then (((W j l).re : ℂ) • eReal j l + ((W j l).im : ℂ) • eImag j l)
      else 0) a b = if j < l ∧ ((j = a ∧ l = b) ∨ (l = a ∧ j = b)) then W a b else 0 := by
    intro j l
    by_cases h1 : j < l
    · rw [if_pos h1]
      simp only [Matrix.add_apply, Matrix.smul_apply, eReal, eImag, Matrix.sub_apply,
        single_apply, smul_eq_mul]
      by_cases h2 : j = a ∧ l = b
      · obtain ⟨rfl, rfl⟩ := h2
        simp only [h1, h1.ne, h1.ne', and_self, true_or, if_true, if_false, sub_zero,
          add_zero, mul_one]
        conv_rhs => rw [← Complex.re_add_im (W j l)]
      · by_cases h3 : l = a ∧ j = b
        · obtain ⟨rfl, rfl⟩ := h3
          simp only [h1, h1.ne, h1.ne', and_self, or_true, if_true, if_false,
            zero_sub, zero_add, mul_neg, mul_one]
          rw [hskew l j]
          conv_rhs => rw [← Complex.re_add_im (W j l)]
          simp only [map_add, map_mul, conj_ofReal, conj_I]
          ring
        · simp [h2, h3]
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]; rfl
  simp_rw [hterm]
  rcases lt_trichotomy a b with hab | rfl | hab
  · rw [diagonal_apply_ne _ hab.ne, zero_add, Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp [hab]
    · intro l _ hl
      rw [if_neg]
      rintro ⟨h0, ⟨-, h⟩ | ⟨h1, h2⟩⟩
      · exact hl h
      · subst h1; subst h2; exact absurd hab (not_lt.2 h0.le)
    · simp
    · intro j _ hj
      refine sum_eq_zero fun l _ => ?_
      rw [if_neg]
      rintro ⟨h0, ⟨h, -⟩ | ⟨h1, h2⟩⟩
      · exact hj h
      · subst h1; subst h2; exact absurd hab (not_lt.2 h0.le)
    · simp
  · simp only [diagonal_apply_eq]
    rw [Finset.sum_eq_zero, add_zero]
    intro j _
    refine sum_eq_zero fun l _ => ?_
    rw [if_neg]
    rintro ⟨h0, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;> subst h1 <;> subst h2 <;> exact lt_irrefl _ h0
  · rw [diagonal_apply_ne _ hab.ne', zero_add, Finset.sum_eq_single b, Finset.sum_eq_single a]
    · simp [hab]
    · intro l _ hl
      rw [if_neg]
      rintro ⟨h0, ⟨h1, h2⟩ | ⟨h, -⟩⟩
      · subst h1; subst h2; exact absurd hab (not_lt.2 h0.le)
      · exact hl h
    · simp
    · intro j _ hj
      refine sum_eq_zero fun l _ => ?_
      rw [if_neg]
      rintro ⟨h0, ⟨h1, h2⟩ | ⟨-, h⟩⟩
      · subst h1; subst h2; exact absurd hab (not_lt.2 h0.le)
      · exact hj h
    · simp

/-- `|A|² = tr(AA*) = π² Σ k_j²` (p. 127). -/
theorem trace_suDiag_mul_conjTranspose (k : ι → ℤ) :
    trace (suDiag k * (suDiag k)ᴴ) = ((π ^ 2 * ∑ j, (k j : ℝ) ^ 2 : ℝ) : ℂ) := by
  simp only [suDiag, diagonal_conjTranspose, diagonal_mul_diagonal, trace_diagonal]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, star_mul', RCLike.star_def, conj_ofReal, conj_I, map_intCast]
  linear_combination (-(π : ℂ) ^ 2 * (k j : ℂ) ^ 2) * I_sq

/-- `tr A = iπ Σ k_j`: `A ∈ 𝔰𝔲(n)` iff `Σ k_j = 0` (p. 130). -/
theorem trace_suDiag (k : ι → ℤ) : trace (suDiag k) = (π : ℂ) * I * ∑ j, (k j : ℂ) := by
  simp only [suDiag, trace_diagonal, mul_sum]
  exact sum_congr rfl fun j _ => by ring

theorem exp_ofReal_mul_I_eq_neg_one_iff (a : ℝ) :
    Complex.exp (a * I) = -1 ↔ ∃ k : ℤ, Odd k ∧ a = π * k := by
  have h : Complex.exp (a * I) = -Complex.exp (((a - π : ℝ) : ℂ) * I) := by
    rw [show ((a - π : ℝ) : ℂ) * I = a * I - π * I by push_cast; ring, Complex.exp_sub,
      Complex.exp_pi_mul_I]
    field_simp
  rw [h, neg_inj, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have := congrArg Complex.im hn
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero,
      intCast_re, intCast_im, zero_mul, re_ofNat, im_ofNat] at this
    refine ⟨2 * n + 1, odd_two_mul_add_one n, ?_⟩
    push_cast
    simp at this
    linarith
  · rintro ⟨k, ⟨n, rfl⟩, rfl⟩
    refine ⟨n, ?_⟩
    push_cast
    ring

theorem exp_diagonal_mul_I (a : ι → ℝ) :
    NormedSpace.exp (diagonal fun j => (a j : ℂ) * I) =
      diagonal fun j => Complex.exp (a j * I) := by
  rw [Matrix.exp_diagonal]
  congr 1
  ext j
  rw [Pi.coe_exp, Complex.exp_eq_exp_ℂ]

/-- **`exp A = −I`** (p. 127): for `A = diag(i a_1, …, i a_n)`, `exp A = −I` iff every `a_j` is
an odd multiple of `π`, i.e. `A = diag(iπk_1, …, iπk_n)` with the `k_j` odd. -/
theorem exp_diagonal_eq_neg_one_iff (a : ι → ℝ) :
    NormedSpace.exp (diagonal fun j => (a j : ℂ) * I) = -1 ↔
      ∀ j, ∃ k : ℤ, Odd k ∧ a j = π * k := by
  rw [exp_diagonal_mul_I, ← diagonal_one, diagonal_neg, diagonal_eq_diagonal_iff]
  exact forall_congr' fun j => exp_ofReal_mul_I_eq_neg_one_iff (a j)

/-- **Lemma 23.1, as a set** (pp. 127–128): a skew-Hermitian `A` satisfies `A² = −π²I` iff
`A = iπ(2P − I)` for a Hermitian projection `P` (`P` is the projection onto `Eigen(iπ)`). -/
theorem sq_eq_neg_pi_sq_iff (A : Matrix ι ι ℂ) (hA : Aᴴ = -A) :
    A * A = -((π : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) ↔
      ∃ P : Matrix ι ι ℂ, Pᴴ = P ∧ P * P = P ∧ A = ((π : ℂ) * I) • ((2 : ℂ) • P - 1) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 pi_ne_zero
  constructor
  · intro h2
    refine ⟨(1 / 2 : ℂ) • (1 - (I / π) • A), ?_, ?_, ?_⟩
    · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hA]
      simp only [star_div₀, star_one, RCLike.star_def, conj_I, conj_ofReal, smul_neg,
        neg_div, neg_smul, neg_neg, map_ofNat]
    · simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc,
        mul_smul_comm, smul_smul, h2]
      match_scalars <;> field_simp
      all_goals ((try simp only [I_sq]); ring1)
    · match_scalars <;> field_simp
      all_goals ((try simp only [I_sq]); ring1)
  · rintro ⟨P, -, hP, rfl⟩
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm, smul_smul, hP]
    match_scalars
    · ring
    · linear_combination (π : ℂ) ^ 2 * I_sq


/-- `tr(iπ(2P − I)) = iπ(2 tr P − n)`: in `SU(2m)` the condition `tr A = 0` is `tr P = m`
(p. 127). -/
theorem trace_pi_smul_projection (P : Matrix ι ι ℂ) :
    trace (((π : ℂ) * I) • ((2 : ℂ) • P - 1)) =
      (π : ℂ) * I * (2 * trace P - Fintype.card ι) := by
  rw [trace_smul, trace_sub, trace_smul, trace_one, smul_eq_mul, smul_eq_mul]

end Matrices

end Morse
