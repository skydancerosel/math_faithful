import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_5

namespace RoundTrip.V6_5

/-- The project's statement (universes instantiated at 0; `velocity`, `IsFieldAlong`, `covDeriv`
are definitions): for a curve `c` in a slice submanifold `N ⊆ V`, the velocity is tangent, and
`DX/dt = P_{c(t)} X'(t)` satisfies Milnor's axioms (a), (b), (c). -/
def A : Prop :=
  type_of% @Morse.deriv_mem_tangentSubspace.{0,0,0} ∧ type_of% @Morse.covDeriv_add.{0,0,0} ∧
    type_of% @Morse.covDeriv_smul.{0,0,0} ∧ type_of% @Morse.covDeriv_comp.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.deriv_mem_tangentSubspace, @Morse.covDeriv_add, @Morse.covDeriv_smul,
    @Morse.covDeriv_comp⟩

end RoundTrip.V6_5
