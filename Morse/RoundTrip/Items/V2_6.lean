import Morse
import RoundTrip.Check
import RoundTrip.Blind.V2_6

namespace RoundTrip.V2_6

/-- The project's statement: the types of the listed theorems, universes instantiated at `0`. -/
def A : Prop :=
  (type_of% @Morse.theorem_3_2.{0}) ∧ (type_of% @Morse.theorem_3_2_homotopyEquiv.{0}) ∧
  (type_of% @Morse.theorem_3_2_attach.{0}) ∧ (type_of% @Morse.isMilnorMu_milnorMu) ∧
  (type_of% @Morse.isStrongDeformationRetract_handle.{0, 0, 0})

theorem A_holds : A :=
  ⟨@Morse.theorem_3_2.{0}, @Morse.theorem_3_2_homotopyEquiv.{0}, @Morse.theorem_3_2_attach.{0},
    @Morse.isMilnorMu_milnorMu, @Morse.isStrongDeformationRetract_handle.{0, 0, 0}⟩

/-! Neither direction is proved (`Morse.milnorMu`, `Morse.CellModel.retractModel` are definitions:
vocabulary). `A ⇒ B` fails: `A` proves Theorem 3.2 only for `f : E → ℝ` on a finite-dimensional
inner-product space `E`; `B` is for an abstract (possibly non-compact) manifold, which no embedding
theorem of the project reduces to `E`. `B ⇒ A` fails: `A` also contains the analytic facts about
the specific function `milnorMu` (`IsMilnorMu ε (milnorMu ε)`) and the handle lemma
`isStrongDeformationRetract_handle`, valid for every split Morse chart whose target contains the
ellipsoid `ξ + η ≤ 2ε` and every Milnor function `μ`, whereas `B` only asserts the deformation
retraction for *some* chart and *small* `ε`. (The three `theorem_3_2*` conjuncts would follow from
`B` at `M = ℝⁿ` after transporting along a linear isometry `E ≃ ℝⁿ`, a cell parametrisation of
`eCell` and `exists_homotopyEquiv_pushout_of_cell`; this glue is not done since `A` as a whole is
out of reach.) -/

end RoundTrip.V2_6
