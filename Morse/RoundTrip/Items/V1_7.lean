import Morse
import RoundTrip.Check
import RoundTrip.Blind.V1_7

namespace RoundTrip.V1_7

/-- The project's statement: the conjunction of the types of the four listed theorems, universes
instantiated at `0`. -/
def A : Prop :=
  (type_of% @Morse.exists_hadamard_coord) ∧
  (type_of% @Morse.exists_hadamard_on.{0, 0}) ∧
  (type_of% @Morse.exists_hadamard_two_on.{0, 0}) ∧
  (type_of% @Morse.contDiffOn_intervalIntegral.{0, 0})

theorem A_holds : A :=
  ⟨@Morse.exists_hadamard_coord, @Morse.exists_hadamard_on.{0, 0},
    @Morse.exists_hadamard_two_on.{0, 0}, @Morse.contDiffOn_intervalIntegral.{0, 0}⟩

/-- `B` is literally the first conjunct of `A`. -/
theorem A_to_B : A → B := by
  intro hA n V hV hc h0 f hf hf0
  exact hA.1 hV hc h0 hf hf0

#rt_check RoundTrip.V1_7.A_to_B [Morse.exists_hadamard_coord, Morse.exists_hadamard_on,
  Morse.exists_hadamard_two_on, Morse.contDiffOn_intervalIntegral]

end RoundTrip.V1_7
