import Morse
import RoundTrip.L2.Blind.Morse_telescope

/-! Layer-2 check of `Morse.telescope` (`⋃ n, A n ×ˢ Icc n (n + 1)`) against the blind textbook
definition (the same set, written with a set-builder). Equal as subsets of `X × ℝ`, for every
sequence `A` (monotone or not). -/

namespace RoundTrip.L2.Morse_telescope

theorem agree {X : Type} (A : ℕ → Set X) : Morse.telescope A = T A := by
  ext z
  exact Morse.mem_telescope

end RoundTrip.L2.Morse_telescope
