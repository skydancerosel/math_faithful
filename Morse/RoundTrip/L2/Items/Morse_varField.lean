import Morse
import RoundTrip.L2.Blind.Morse_varField

/-! Layer-2 check of `Morse.varField` (`W_t = ∂α/∂u (0, t)` as `deriv (fun u => α u t) 0`) against
the blind textbook definition: the same formula, definitionally equal. -/

namespace RoundTrip.L2.Morse_varField

/-- **Agreement**: definitionally equal. -/
theorem agree {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (α : ℝ → ℝ → V)
    (t : ℝ) : Morse.varField α t = T α t := rfl

end RoundTrip.L2.Morse_varField
