import Morse
import RoundTrip.L2.Blind.Morse_grassmannian

/-! Layer-2 check of `Morse.grassmannian` (Hermitian idempotents `P` with `tr P = m`) against the
blind textbook definition (Hermitian idempotents of rank `m`, i.e. orthogonal projections onto
`m`-dimensional subspaces of `ℂⁿ`). For an idempotent, `rank = trace` (the trace of a projection
is the dimension of its range), so the two sets are equal. -/

namespace RoundTrip.L2.Morse_grassmannian

/-- For an idempotent matrix, `rank = trace` (as complex numbers). -/
theorem rank_eq_trace {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ} (hP : P * P = P) :
    ((P.rank : ℕ) : ℂ) = P.trace := by
  have he : IsIdempotentElem (Matrix.toLin' P) := by
    change Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  have h := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
  rw [Matrix.trace_toLin'_eq] at h
  rw [h, Matrix.rank, Matrix.toLin'_apply']

theorem agree (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ) :
    Morse.grassmannian ι m = T ι m := by
  ext P
  simp only [Morse.grassmannian, T, Set.mem_ofPred_eq]
  refine and_congr Iff.rfl (and_congr_right fun h2 => ?_)
  rw [← rank_eq_trace h2]
  exact Nat.cast_inj

end RoundTrip.L2.Morse_grassmannian
