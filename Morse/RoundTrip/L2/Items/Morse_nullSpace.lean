import Morse
import RoundTrip.L2.Blind.Morse_nullSpace
namespace RoundTrip.L2.Morse_nullSpace

/-- The project's null space (kernel of `H` as a linear map into `E →L ℝ`) is the textbook one. -/
theorem agree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (H : E →L[ℝ] E →L[ℝ] ℝ) :
    Morse.nullSpace H = T H := by
  ext v
  rw [Morse.mem_nullSpace]
  rfl

end RoundTrip.L2.Morse_nullSpace
