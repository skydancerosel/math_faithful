import Morse
import RoundTrip.L2.Blind.Morse_MatrixInner_innerProductSpace

/-! Layer-2 check of `Morse.MatrixInner.innerProductSpace` (`⟪A, B⟫ = Re tr(Aᴴ B)` on `Mₙ(𝕜)`)
against the blind textbook definition (Milnor's `⟨A, B⟩ = Re tr(A B*)`). The two formulas differ in
the order of the factors, but `Re tr(Aᴴ B) = Re tr(B Aᴴ) = Re conj tr(A Bᴴ) = Re tr(A Bᴴ)`; the
normed-space parts are the same (the Frobenius norm, Mathlib's `ℝ`-module structure), so the two
inner product space structures are equal. -/

namespace RoundTrip.L2.Morse_MatrixInner_innerProductSpace

open scoped Matrix

attribute [local instance] Morse.MatrixInner.normedAddCommGroup

/-- The project's `Re tr(Aᴴ B)` is Milnor's `Re tr(A Bᴴ)`. -/
theorem re_trace_conjTranspose_mul {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι 𝕜) : RCLike.re (Matrix.trace (Aᴴ * B)) = ip A B := by
  rw [Matrix.trace_mul_comm, ← ip_comm]
  rfl

theorem agree {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] :
    (Morse.MatrixInner.innerProductSpace : InnerProductSpace ℝ (Matrix ι ι 𝕜)) = T := by
  unfold Morse.MatrixInner.innerProductSpace T
  congr 1
  congr 1
  funext A B
  exact re_trace_conjTranspose_mul A B

end RoundTrip.L2.Morse_MatrixInner_innerProductSpace
