import Morse
import RoundTrip.Check
import RoundTrip.Blind.V1_14

namespace RoundTrip.V1_14

/-- The project's statement: the types of the listed theorems (`IsBddLipschitz`, `flow`,
`flowHomeomorph`, `flowDiffeomorph` are definitions, i.e. vocabulary), universes instantiated
at `0`. -/
def A : Prop :=
  (type_of% @Morse.IsBddLipschitz.isIntegralCurve_flow.{0}) ∧
  (type_of% @Morse.IsBddLipschitz.eq_flow.{0}) ∧
  (type_of% @Morse.IsBddLipschitz.flow_add.{0}) ∧
  (type_of% @Morse.contDiff_flow_uncurry.{0})

theorem A_holds : A :=
  ⟨@Morse.IsBddLipschitz.isIntegralCurve_flow.{0}, @Morse.IsBddLipschitz.eq_flow.{0},
    @Morse.IsBddLipschitz.flow_add.{0}, @Morse.contDiff_flow_uncurry.{0}⟩

/-! Neither direction is proved. `A` is the global flow of a bounded Lipschitz field on a
Banach space `E` (built directly, by Picard iteration, not by Milnor's patching of local
solutions), with smooth dependence for compactly supported smooth fields. `B` is about an
abstract finite-dimensional manifold: local flows (Graves), local uniqueness of integral curves,
and the global flow of a compactly supported field. `A ⇒ B` would need all the manifold
machinery (charts, patching, uniqueness on a Hausdorff manifold); `B ⇒ A` fails since `B` only
speaks of smooth fields on finite-dimensional manifolds and says nothing about `Morse.flow` of a
Lipschitz field on a possibly infinite-dimensional Banach space. -/

end RoundTrip.V1_14
