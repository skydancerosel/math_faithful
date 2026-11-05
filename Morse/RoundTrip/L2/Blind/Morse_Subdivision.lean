import Morse
/-! Layer-2 blind definition of Morse_Subdivision. Textbook: Milnor, *Morse Theory*, §16, p. 88:
a subdivision of `[0, 1]` is a finite sequence `0 = t₀ < t₁ < ⋯ < t_k = 1`.
Choices: the parameter `m` has no textbook meaning; it is encoded as `k = m + 1` (i.e. `m` interior
points, `m + 2` points `t₀, …, t_{m+1}`), so that every `m` gives a non-empty type (`m = 0` is the
trivial subdivision `0 < 1`); `k = 0` (impossible for `[0, 1]`, as `0 ≠ 1`) is excluded. A
subdivision is a strictly increasing `t : Fin (m + 2) → ℝ` with `t 0 = 0` and `t (m + 1) = 1`, as
a subtype. Disclosure: the permitted `#print Morse.BrokenSetup` (an argument type of
`Morse_BrokenSetup_IsBroken`) displayed the fields this structure inherits, so the choice of
`k = m + 1` here was made after seeing the project's indexing. -/
namespace RoundTrip.L2.Morse_Subdivision

/-- The textbook notion: subdivisions `0 = t₀ < ⋯ < t_{m+1} = 1` of `[0, 1]`. -/
def T (m : ℕ) : Type :=
  {t : Fin (m + 2) → ℝ // StrictMono t ∧ t 0 = 0 ∧ t (Fin.last (m + 1)) = 1}

end RoundTrip.L2.Morse_Subdivision
