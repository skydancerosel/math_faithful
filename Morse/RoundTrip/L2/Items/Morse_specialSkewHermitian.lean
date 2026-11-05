import Morse
import RoundTrip.L2.Blind.Morse_specialSkewHermitian

/-! Layer-2 check of `Morse.specialSkewHermitian` (`𝔰𝔲(n)`: skew-Hermitian complex matrices of
trace `0`, a real Lie subalgebra of `Mₙ(ℂ)` for the commutator) against the blind textbook
definition: the same carrier, hence the same Lie subalgebra. -/

namespace RoundTrip.L2.Morse_specialSkewHermitian

-- the commutator Lie ring on matrices (needed to find `LieSubalgebra.ext`)
open scoped Morse.MatrixInner

theorem agree (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Morse.specialSkewHermitian ι = T ι := by
  ext X
  exact Iff.rfl

end RoundTrip.L2.Morse_specialSkewHermitian
