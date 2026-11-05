import Morse
import RoundTrip.L2.Blind.Morse_IsMorsePatch

/-! Layer-2 check of `Morse.IsMorsePatch` against the blind textbook definition (a topological
Morse chart centred at `p`): the same three conditions; `Morse.morseQuad c v = c - ‖v.1‖² + ‖v.2‖²`
by definition. Equal for all arguments. -/

namespace RoundTrip.L2.Morse_IsMorsePatch

theorem agree {M : Type*} [TopologicalSpace M] {X : Type*} {Y : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup Y] (f : M → ℝ) (p : M) (φ : OpenPartialHomeomorph M (X × Y)) :
    Morse.IsMorsePatch f p φ ↔ T f p φ :=
  ⟨fun h => ⟨h.mem_source, h.apply_self, h.apply_eq⟩,
    fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

end RoundTrip.L2.Morse_IsMorsePatch
