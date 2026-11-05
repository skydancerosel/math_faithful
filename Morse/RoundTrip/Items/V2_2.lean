import Morse
import RoundTrip.Check
import RoundTrip.Blind.V2_2

namespace RoundTrip.V2_2

/-- The project's statement: the types of the listed theorems (Theorem 3.1 for `M = E` a
finite-dimensional inner product space, and its lemmas), universes instantiated at `0`. -/
def A : Prop :=
  (type_of% @Morse.theorem_3_1.{0}) ∧
  (type_of% @Morse.exists_diffeomorph_image_sublevel_eq.{0}) ∧
  (type_of% @Morse.exists_cutoff.{0}) ∧
  (type_of% @Morse.IsSlabFlow.image_sublevel.{0}) ∧
  (type_of% @Morse.IsSlabFlow.isStrongDeformationRetract.{0})

theorem A_holds : A :=
  ⟨@Morse.theorem_3_1.{0}, @Morse.exists_diffeomorph_image_sublevel_eq.{0},
    @Morse.exists_cutoff.{0}, @Morse.IsSlabFlow.image_sublevel.{0},
    @Morse.IsSlabFlow.isStrongDeformationRetract.{0}⟩

/-! Neither direction is proved. `A ⇒ B` fails: `A` covers only `M = E` (a Euclidean space),
`B` an arbitrary smooth manifold. `B ⇒ A` fails: `A` concludes an ambient diffeomorphism
`Φ : E ≃ E` with `Φ '' E^a = E^b`, while `B` only gives mutually inverse maps between the
sublevel sets that are smooth on them; and `A` also contains the cut-off lemma and the abstract
`IsSlabFlow` lemmas, which `B` does not state. -/

end RoundTrip.V2_2
