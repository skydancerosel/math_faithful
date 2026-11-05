import Morse
import RoundTrip.Check
import RoundTrip.Blind.V2_10

namespace RoundTrip.V2_10

/-- The project's statement: the types of the listed theorems, universes instantiated at `0`. -/
def A : Prop :=
  (type_of% @Morse.remark_3_4.{0}) ∧ (type_of% @Morse.IsStrongDeformationRetract.of_retract.{0})

theorem A_holds : A :=
  ⟨@Morse.remark_3_4.{0}, @Morse.IsStrongDeformationRetract.of_retract.{0}⟩

/-! Neither direction is proved. `A ⇒ B` fails: `remark_3_4` is for `f : E → ℝ` on a
finite-dimensional inner-product space; `B` is for an abstract (possibly non-compact) manifold.
`B ⇒ A` is believed true but not done: `of_retract` (`A ⊆ B ⊆ C`, `A` and `B` SDRs of `C` ⇒ `A`
an SDR of `B`) is elementary topology to be proved from scratch. `remark_3_4` would follow from `B`
at `M = ℝⁿ`, but only after transport along a linear isometry `E ≃ ℝⁿ` (critical points,
non-degeneracy and index of `f ∘ e⁻¹`), shrinking `ε` so that the disk `ξ ≤ ε` lies in the chart's
target, and parametrising `eCell` by the closed ball of `ℝ^λ`. -/

end RoundTrip.V2_10
