import Morse
import RoundTrip.Check
import RoundTrip.Blind.V8_2

namespace RoundTrip.«V8_2»

/-- The project's statement (universes instantiated at 0; `IsVariation N U α B` and `varField`
are definitions): each path `α u` of a variation lies in `Ω(N; α 0 0, α 0 1)`; a variation
reparametrised by a smooth `φ : P' → P` with `φ 0 ∈ U` is a variation with the same break
points; and the variation field of a `1`-parameter variation lies in `TΩ_{α 0}`. -/
def A : Prop :=
  type_of% @Morse.IsVariation.mem_pathSpace.{0,0} ∧
    type_of% @Morse.IsVariation.comp.{0,0,0} ∧
    type_of% @Morse.IsVariation.varField_mem.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.IsVariation.mem_pathSpace, @Morse.IsVariation.comp, @Morse.IsVariation.varField_mem⟩

/-! No direction is proved; see `V8_2.json`. -/

end RoundTrip.«V8_2»
