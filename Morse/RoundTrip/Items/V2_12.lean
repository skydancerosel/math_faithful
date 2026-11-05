import Morse
import RoundTrip.Check
import RoundTrip.Blind.V2_12

namespace RoundTrip.V2_12

/-- The project's statement: the types of the listed theorems, universes instantiated at `0`. -/
def A : Prop :=
  (type_of% @Morse.theorem_3_5'.{0, 0, 0}) ∧ (type_of% @Morse.theorem_3_5_count'.{0, 0, 0}) ∧
  (type_of% @Morse.theorem_3_5.{0, 0, 0}) ∧ (type_of% @Morse.theorem_3_5_count.{0, 0, 0}) ∧
  (type_of% @Morse.isCriticalPointM_of_forall_le.{0, 0})

theorem A_holds : A :=
  ⟨@Morse.theorem_3_5'.{0, 0, 0}, @Morse.theorem_3_5_count'.{0, 0, 0}, @Morse.theorem_3_5.{0, 0, 0},
    @Morse.theorem_3_5_count.{0, 0, 0}, @Morse.isCriticalPointM_of_forall_le.{0, 0}⟩

/-! Neither direction is proved. `A ⇒ B` fails: `A` concludes `IsFiniteCellComplexType` (homotopy
equivalent to an iterated adjunction space with *arbitrary* attaching maps), `B` a Mathlib
`CWComplex`; passing from one to the other is cellular approximation, which is not in Mathlib.
Moreover `A` covers compact slice submanifolds only, `B` any manifold with compact sublevel sets.
That includes non-compact `M` (infinitely many cells, direct limit and Whitehead's theorem).
`B ⇒ A` fails: a CW-complex in `B` does not give an iterated adjunction space whose cells are
attached in order of critical value (`theorem_3_5`'s list `ps`), and `isCriticalPointM_of_forall_le`
is a general lemma `B` does not state. -/

end RoundTrip.V2_12
