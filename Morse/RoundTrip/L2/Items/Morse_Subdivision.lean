import Morse
import RoundTrip.L2.Blind.Morse_Subdivision

/-! Layer-2 check of `Morse.Subdivision m` (a structure: `t : Fin (m + 2) → ℝ`, strictly
increasing, `t 0 = 0`, `t (m + 1) = 1`) against the blind textbook definition (the subtype of
such `t`). The blind file discloses that its indexing `k = m + 1` was chosen after seeing the
project's fields (not blind). The two types are equivalent by repackaging the fields. -/

namespace RoundTrip.L2.Morse_Subdivision

/-- **Agreement**: the structure and the subtype are equivalent (same data, same conditions). -/
def agree (m : ℕ) : Morse.Subdivision m ≃ T m where
  toFun s := ⟨s.t, s.strictMono, s.t_zero, s.t_last⟩
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem agree_nonempty (m : ℕ) : Nonempty (Morse.Subdivision m ≃ T m) := ⟨agree m⟩

end RoundTrip.L2.Morse_Subdivision
