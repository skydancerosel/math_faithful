import Morse
/-! Layer-2 blind definition of Morse_sublevel. Textbook: Milnor, *Morse Theory*, §3, p. 12
(`Mᵃ = f⁻¹(−∞, a] = {p ∈ M : f(p) ≤ a}`).
Choices: no hypothesis on `F` or on the space (the formula makes sense for any real function);
the non-strict inequality `≤` as in Milnor. -/
namespace RoundTrip.L2.Morse_sublevel

/-- The textbook notion: the sublevel set `F⁻¹(−∞, c]`. -/
def T {T : Type*} (F : T → ℝ) (c : ℝ) : Set T :=
  {p | F p ≤ c}

end RoundTrip.L2.Morse_sublevel
