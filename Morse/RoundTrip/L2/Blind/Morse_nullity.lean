import Morse
/-! Layer-2 blind definition of Morse_nullity. Textbook: Milnor, *Morse Theory*, §2, p. 5
(nullity = dimension of the null space `{v : H(v,w) = 0 ∀ w}`).
Choices: null space with `v` in the first slot (as in Milnor; irrelevant for symmetric `H`).
Encoding: the dimension is `Module.finrank`, so an infinite-dimensional null space (possible only
for infinite-dimensional `E`, outside §2's finite-dimensional setting) is encoded as `0`. -/
namespace RoundTrip.L2.Morse_nullity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The null space `{v | ∀ w, H v w = 0}` of a bilinear form. -/
def nullSpace (H : E →L[ℝ] E →L[ℝ] ℝ) : Submodule ℝ E where
  carrier := {v | ∀ w, H v w = 0}
  add_mem' := by
    intro a b ha hb w
    simp [ha w, hb w]
  zero_mem' := by
    intro w
    simp
  smul_mem' := by
    intro c v hv w
    simp [hv w]

/-- The textbook notion: the dimension of the null space of `H`. -/
noncomputable def T (H : E →L[ℝ] E →L[ℝ] ℝ) : ℕ :=
  Module.finrank ℝ (nullSpace H)

end RoundTrip.L2.Morse_nullity
