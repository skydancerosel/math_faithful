import Morse
import RoundTrip.L2.Blind.Morse_nullity

/-! Layer-2 check of `Morse.nullity` against the blind textbook definition: both are the
`Module.finrank` of the same subspace `{v | ∀ w, H v w = 0}` (the project writes it as the kernel
of `v ↦ H v`). -/

namespace RoundTrip.L2.Morse_nullity

theorem nullSpace_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E →L[ℝ] E →L[ℝ] ℝ) : Morse.nullSpace H = nullSpace H := by
  ext v
  rw [Morse.mem_nullSpace]
  rfl

theorem agree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (H : E →L[ℝ] E →L[ℝ] ℝ) :
    Morse.nullity H = T H := by
  unfold Morse.nullity T
  rw [nullSpace_eq]

end RoundTrip.L2.Morse_nullity
