import Morse
/-! Layer-2 blind definition of Morse_nullSpace. Textbook: Milnor, *Morse Theory*, §2, p. 5: the
null space of a (symmetric) bilinear form `H` on a vector space `E` is the subspace of all
`v ∈ E` with `H(v, w) = 0` for every `w ∈ E`.
Choices: the null space in the first argument (for a symmetric `H` the two sides agree; no
symmetry is assumed). Continuity of `H` plays no role. -/
namespace RoundTrip.L2.Morse_nullSpace

/-- The textbook notion: `{v | ∀ w, H v w = 0}`. -/
def T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (H : E →L[ℝ] E →L[ℝ] ℝ) :
    Submodule ℝ E where
  carrier := {v | ∀ w, H v w = 0}
  add_mem' {a b} ha hb w := by
    have h1 : H a w = 0 := ha w
    have h2 : H b w = 0 := hb w
    simp [h1, h2]
  zero_mem' w := by simp
  smul_mem' c v hv w := by
    have h : H v w = 0 := hv w
    simp [h]

end RoundTrip.L2.Morse_nullSpace
