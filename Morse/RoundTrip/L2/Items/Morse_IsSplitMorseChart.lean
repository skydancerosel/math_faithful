import Morse
import RoundTrip.L2.Blind.Morse_IsSplitMorseChart

/-! Layer-2 check of `Morse.IsSplitMorseChart` against the blind textbook definition (a smooth
Morse coordinate chart `φ = (x, y)` centred at `p`, `C^∞` both ways, with
`f = f(p) − ‖x‖² + ‖y‖²` on the source): the same five conditions, in a different order;
`Morse.morseQuad c v = c - ‖v.1‖² + ‖v.2‖²` by definition. Equal for all arguments. -/

namespace RoundTrip.L2.Morse_IsSplitMorseChart

theorem agree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (f : E → ℝ) (p : E) (φ : OpenPartialHomeomorph E (X × Y)) :
    Morse.IsSplitMorseChart f p φ ↔ T f p φ :=
  ⟨fun h => ⟨h.contDiffOn, h.contDiffOn_symm, h.mem_source, h.apply_self, h.apply_eq⟩,
    fun h => ⟨h.2.2.1, h.2.2.2.1, h.1, h.2.1, h.2.2.2.2⟩⟩

end RoundTrip.L2.Morse_IsSplitMorseChart
