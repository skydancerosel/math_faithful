import Morse
import RoundTrip.Check
import RoundTrip.Blind.V1_1

namespace RoundTrip.V1_1

/-- The project's statement: the types of the listed theorems about the embedded torus
`Morse.torus R r ⊆ ℝ³` with its height function (`Morse.torus` is vocabulary). No universe
parameters. -/
def A : Prop :=
  (type_of% @Morse.Torus.isCriticalPointM_height_iff) ∧
  (type_of% @Morse.Torus.pointP_spec) ∧
  (type_of% @Morse.Torus.pointQ_spec) ∧
  (type_of% @Morse.Torus.pointR_spec) ∧
  (type_of% @Morse.Torus.pointS_spec) ∧
  (type_of% @Morse.Torus.sublevel_height_eq_empty) ∧
  (type_of% @Morse.Torus.sublevel_height_eq_univ) ∧
  (type_of% @Morse.theorem_3_1_torus)

theorem A_holds : A :=
  ⟨@Morse.Torus.isCriticalPointM_height_iff, @Morse.Torus.pointP_spec, @Morse.Torus.pointQ_spec,
    @Morse.Torus.pointR_spec, @Morse.Torus.pointS_spec, @Morse.Torus.sublevel_height_eq_empty,
    @Morse.Torus.sublevel_height_eq_univ, @Morse.theorem_3_1_torus⟩

/-! Neither direction is proved. `A ⇒ B` would need (besides a diffeomorphism
`S¹ × S¹ ≃ Morse.torus R r` carrying `ht` to `height`) the stage homeomorphisms
`M^a ≃ₜ D²` (`0 < a < 2r`) and `M^a ≃ₜ S¹ × [0,1]` (`2r < a < 2R`) and the four cell
attachments `M^{c+ε} ≃ₕ M^{c-ε} ∪ e^λ`, none of which is in `A`. `B ⇒ A` fails since `B` has no
analogue of `theorem_3_1_torus` (diffeomorphism and strong deformation retraction between
sublevel sets away from the critical values). -/

end RoundTrip.V1_1
