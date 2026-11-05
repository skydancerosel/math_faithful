import Morse
/-! Layer-2 blind definition of Morse_specialSkewHermitian. Textbook: Milnor, *Morse Theory*,
p. 126 (Part IV, §§22–23): the Lie algebra `𝔰𝔲(n)` of the special unitary group `SU(n)`: the
real vector space of complex `n × n` matrices `X` with `X* = −X` (skew-Hermitian) and
`tr X = 0`, with the commutator bracket `[X, Y] = XY − YX`.
Choices: `n × n` matrices indexed by a finite type `ι`; `X*` is the conjugate transpose `Xᴴ`; the
bracket is Mathlib's ring commutator on `Matrix ι ι ℂ` (`LieRing.ofAssociativeRing`, made a local
instance as in Mathlib; a real Lie algebra via `LieAlgebra.ofAssociativeAlgebra` and `ℝ → ℂ`). -/
namespace RoundTrip.L2.Morse_specialSkewHermitian

open scoped Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The textbook notion: skew-Hermitian, trace-zero complex matrices, as a real Lie subalgebra. -/
def T (ι : Type*) [Fintype ι] [DecidableEq ι] : LieSubalgebra ℝ (Matrix ι ι ℂ) where
  carrier := {X | Xᴴ = -X ∧ Matrix.trace X = 0}
  add_mem' := by
    rintro A B ⟨hA, tA⟩ ⟨hB, tB⟩
    exact ⟨by rw [Matrix.conjTranspose_add, hA, hB, neg_add],
      by rw [Matrix.trace_add, tA, tB, add_zero]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := by
    rintro r A ⟨hA, tA⟩
    exact ⟨by rw [Matrix.conjTranspose_smul, hA, star_trivial, smul_neg],
      by rw [Matrix.trace_smul, tA, smul_zero]⟩
  lie_mem' := by
    rintro A B ⟨hA, -⟩ ⟨hB, -⟩
    refine ⟨?_, ?_⟩
    · rw [Ring.lie_def, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_mul, hA, hB, neg_mul_neg, neg_mul_neg, neg_sub]
    · rw [Ring.lie_def, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

end RoundTrip.L2.Morse_specialSkewHermitian
