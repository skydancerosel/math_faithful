import Morse
import RoundTrip.Check
import RoundTrip.Blind.V2_8

namespace RoundTrip.V2_8

/-- The project's statement: the types of the listed theorems, universes instantiated at `0`. -/
def A : Prop :=
  (type_of% @Morse.patch_theorem_3_2.{0, 0, 0}) ∧ (type_of% @Morse.theorem_3_2_submanifold.{0, 0, 0}) ∧
  (type_of% @Morse.theorem_3_2_attach_submanifold.{0, 0, 0}) ∧
  (type_of% @Morse.exists_contDiff_comp_val_eq_of_chart.{0, 0, 0})

theorem A_holds : A :=
  ⟨@Morse.patch_theorem_3_2.{0, 0, 0}, @Morse.theorem_3_2_submanifold.{0, 0, 0},
    @Morse.theorem_3_2_attach_submanifold.{0, 0, 0}, @Morse.exists_contDiff_comp_val_eq_of_chart.{0, 0, 0}⟩

/-! Neither direction is proved (`IsMorsePatch`, `IsMilnorMu` are definitions: vocabulary).
`A ⇒ B` fails: `A` proves Theorem 3.2 for `F|N`, `N` a slice submanifold of a finite-dimensional
`V`, and, for an arbitrary Hausdorff space, only the patch part (`patch_theorem_3_2` *assumes*
Assertion 3, the deformation retraction of `M^{c+ε}` onto `F⁻¹(-∞, c-ε]`). `B` is Theorem 3.2 and
Assertion 3 on an abstract, possibly non-compact manifold. Assertion 3 there is Theorem 3.1 for
`F` on an abstract manifold, which the project does not have. `B ⇒ A` fails: `patch_theorem_3_2`
is about any T2 space and any Morse patch with the SDR hypothesis, and
`exists_contDiff_comp_val_eq_of_chart` is an extension lemma; `B` implies neither. -/

end RoundTrip.V2_8
