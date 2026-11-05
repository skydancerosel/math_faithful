import Morse
/-! Layer-2 blind definition of Morse_MatrixInner_innerProductSpace. Textbook: Milnor, *Morse
Theory*, §21, p. 125 (Part IV): the space of `n × n` matrices over `𝕜 = ℝ` or `ℂ` (and over the
quaternions in Milnor) with the Euclidean inner product `⟨A, B⟩ = Re tr(A B*)` (the
Frobenius / Hilbert–Schmidt product `Σᵢⱼ Re(aᵢⱼ conj bᵢⱼ)`), which restricts to the bi-invariant
metric on `U(n)`, `SU(n)`, `O(n)`.
Choices: `B*` is the conjugate transpose `Bᴴ`, `Re` is `RCLike.re`. The result type is an
`InnerProductSpace` over the normed group carried by the signature (the project's matrix norm
instance `Morse.MatrixInner.normedAddCommGroup`, made a local instance here as the setting; it is
definitionally Mathlib's Frobenius norm `‖A‖ = (Σᵢⱼ ‖aᵢⱼ‖²)^{1/2}`, which is used, through
`Matrix.frobeniusNormedSpace`, only to prove the norm conditions `‖A‖² = ⟨A, A⟩` and
`‖r • A‖ ≤ |r| ‖A‖`). The data are Mathlib's `ℝ`-module structure on matrices and the inner
product `Re tr(A Bᴴ)`. -/
namespace RoundTrip.L2.Morse_MatrixInner_innerProductSpace

open scoped Matrix ComplexConjugate

section Aux
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-- Milnor's inner product `⟨A, B⟩ = Re tr(A B*)`. -/
noncomputable def ip (A B : Matrix ι ι 𝕜) : ℝ := RCLike.re (Matrix.trace (A * Bᴴ))

lemma ip_self (A : Matrix ι ι 𝕜) : ip A A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold ip
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, map_sum, RCLike.mul_conj]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← RCLike.ofReal_pow, RCLike.ofReal_re]

lemma ip_comm (A B : Matrix ι ι 𝕜) : ip B A = ip A B := by
  unfold ip
  rw [← Matrix.conjTranspose_conjTranspose A, ← Matrix.conjTranspose_mul,
    Matrix.trace_conjTranspose, Matrix.conjTranspose_conjTranspose, RCLike.star_def,
    RCLike.conj_re]

section Frob
open scoped Matrix.Norms.Frobenius

lemma frob_sq (A : Matrix ι ι 𝕜) : ‖A‖ ^ 2 = ip A A := by
  have h : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖A i j‖
  rw [ip_self, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  try simp only [Real.rpow_two]
  exact Real.sq_sqrt h

lemma frob_smul (r : ℝ) (A : Matrix ι ι 𝕜) : ‖r • A‖ ≤ ‖r‖ * ‖A‖ := norm_smul_le r A

end Frob
end Aux

attribute [local instance] Morse.MatrixInner.normedAddCommGroup

/-- The textbook notion: matrices with the inner product `⟨A, B⟩ = Re tr(A B*)`. -/
@[instance_reducible]
noncomputable def T {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] :
    InnerProductSpace ℝ (Matrix ι ι 𝕜) where
  toNormedSpace := { norm_smul_le := frob_smul (𝕜 := 𝕜) (ι := ι) }
  inner A B := ip A B
  norm_sq_eq_re_inner A := frob_sq (𝕜 := 𝕜) A
  conj_inner_symm A B := by rw [conj_trivial]; exact ip_comm A B
  add_left A A' B := by
    change RCLike.re (Matrix.trace ((A + A') * Bᴴ)) = RCLike.re (Matrix.trace (A * Bᴴ)) +
      RCLike.re (Matrix.trace (A' * Bᴴ))
    rw [Matrix.add_mul, Matrix.trace_add, map_add]
  smul_left A B r := by
    change RCLike.re (Matrix.trace ((r • A) * Bᴴ)) = conj r * RCLike.re (Matrix.trace (A * Bᴴ))
    rw [Matrix.smul_mul, Matrix.trace_smul, RCLike.smul_re, conj_trivial]

end RoundTrip.L2.Morse_MatrixInner_innerProductSpace
