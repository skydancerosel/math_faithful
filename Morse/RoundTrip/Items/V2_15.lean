import Morse
import RoundTrip.Check
import RoundTrip.Blind.V2_15

namespace RoundTrip.V2_15

/-- The project's statement: the types of the listed theorems, universes instantiated at `0`. -/
def A : Prop :=
  (type_of% @Morse.isFiniteCellComplexType_sublevel'.{0, 0, 0}) ∧
  (type_of% @Morse.isFiniteCellComplexType_sublevel.{0, 0, 0})

theorem A_holds : A :=
  ⟨@Morse.isFiniteCellComplexType_sublevel'.{0, 0, 0}, @Morse.isFiniteCellComplexType_sublevel.{0, 0, 0}⟩

/-! Neither direction is proved. `A ⇒ B` fails: `A` is for compact slice submanifolds and regular
values `a` only (hypothesis: no critical point on the level `a`). It concludes an iterated
adjunction space (`IsFiniteCellComplexType`, arbitrary attaching maps). `B` asks for every `a`,
critical values included, on any manifold with compact sublevel sets, and for a Mathlib
`CWComplex` (cellular approximation, not in Mathlib). `B ⇒ A` fails: a CW-complex does not give
`A`'s ordered iterated adjunction space (cells attached in order of critical value, listed by `ps`
with `ps.Nodup` and the pairwise order). -/

end RoundTrip.V2_15
