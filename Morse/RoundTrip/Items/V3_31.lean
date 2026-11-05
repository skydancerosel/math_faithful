import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_31

open CategoryTheory Morse.Homology
open scoped ContDiff Manifold

namespace RoundTrip.V3_31

/-- The project's statement: the five listed theorems (`relHomologyCellAttachTopIso` is a
definition, of an isomorphism), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.Homology.isIso_relHomology_map_cellPair.{0, 0} ∧
  type_of% @Morse.Homology.relHomology_cellAttach_iso.{0} ∧
  type_of% @Morse.Homology.isZero_relHomology_cellAttach.{0} ∧
  type_of% @Morse.Homology.finrank_relHomology_cellsAttach.{0, 0} ∧
  type_of% @Morse.Homology.relHomology_cellsAttach_iso.{0, 0}

theorem A_holds : A :=
  ⟨@Morse.Homology.isIso_relHomology_map_cellPair.{0, 0},
    @Morse.Homology.relHomology_cellAttach_iso.{0},
    @Morse.Homology.isZero_relHomology_cellAttach.{0},
    @Morse.Homology.finrank_relHomology_cellsAttach.{0, 0},
    @Morse.Homology.relHomology_cellsAttach_iso.{0, 0}⟩

/-! Neither direction is proved; see the `.json` diagnosis. A's cells are *embedded*: subsets
`X = Y ∪ χ(Dᵏ)` of a space with `Y` closed and `χ` continuous and **injective on the closed ball**,
with `χ z ∈ Y ↔ ‖z‖ = 1`. B's cells are attached along an arbitrary continuous `g : Sᵏ⁻¹ → Y`
in the quotient `Y ∪_g eᵏ`. Its characteristic map is injective on the boundary sphere only when
`g` is, so A's hypotheses fail for B's general attachment. -/

end RoundTrip.V3_31
