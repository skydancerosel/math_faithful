import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_33

open CategoryTheory Morse.Homology
open scoped ContDiff Manifold

namespace RoundTrip.V3_33

/-- The project's statement: the three listed theorems (`spaceHomology`, `bettiNumber`,
`subsetHomologyEquivOfIsSDRBottom`, `CellAttachHomology` are definitions), universes at `0`. -/
def A : Prop :=
  type_of% @Morse.Homology.bettiNumber_eq_of_homeomorph.{0} ∧
  type_of% @Morse.Homology.finrank_subsetHomology_eq_bettiNumber.{0} ∧
  type_of% @Morse.Homology.finrank_subsetHomology_of_cells.{0}

theorem A_holds : A :=
  ⟨@Morse.Homology.bettiNumber_eq_of_homeomorph.{0},
    @Morse.Homology.finrank_subsetHomology_eq_bettiNumber.{0},
    @Morse.Homology.finrank_subsetHomology_of_cells.{0}⟩

/-- B's first clause (Milnor's `R_λ` is the rank) holds outright. -/
theorem B_first : ∀ (F : Type) [Field F] (E : Type) [TopologicalSpace E] (A B : Set E)
    (h : A ⊆ B) (i : ℕ), Module.Finite F (Hom F h i) →
    ((R F h i : ℕ) : Cardinal) = Module.rank F (Hom F h i) :=
  fun _ _ _ _ _ _ _ _ _ ↦ Module.finrank_eq_rank _ _

/-! Neither direction is proved; see the `.json` diagnosis. B's second clause compares the slab
homology with that of an abstract adjunction space `M^{a_i} ∪_g e^λ` (a quotient); the project
computes relative homology only for cells *embedded* in a Hausdorff space
(`CellAttachHomology`, `finrank_subsetHomology_of_cells`), not for quotients. -/

end RoundTrip.V3_33
