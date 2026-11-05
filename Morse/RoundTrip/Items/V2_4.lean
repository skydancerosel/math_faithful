import Morse
import RoundTrip.Check
import RoundTrip.Blind.V2_4

namespace RoundTrip.V2_4

/-- The project's statement: the types of the listed theorems (Theorem 3.1 for a compact
manifold, the embedding theorem it rests on, and the extension lemma), universes instantiated at
`0`. -/
def A : Prop :=
  (type_of% @Morse.theorem_3_1_of_compactSpace.{0, 0}) ∧
  (type_of% @Morse.exists_diffeomorph_sliceSubmanifold.{0, 0}) ∧
  (type_of% @Morse.exists_contDiff_comp_val_eq)

theorem A_holds : A :=
  ⟨@Morse.theorem_3_1_of_compactSpace.{0, 0}, @Morse.exists_diffeomorph_sliceSubmanifold.{0, 0},
    @Morse.exists_contDiff_comp_val_eq⟩

/-! Neither direction is proved. `A ⇒ B` fails: `A` assumes `M` compact (`CompactSpace M`),
`B` only that `f⁻¹[a, b]` is compact (e.g. `M = ℝⁿ` is not covered by `A`). `B ⇒ A` fails: `A`
concludes an ambient diffeomorphism `Ψ : M ≃ M` with `Ψ '' M^a = M^b`, `B` only maps between
sublevel sets smooth on them; and `A` also contains Whitney-type embedding of a compact manifold
as a slice submanifold of some `ℝᴷ⁺¹` and the smooth extension lemma, which `B` does not state. -/

end RoundTrip.V2_4
