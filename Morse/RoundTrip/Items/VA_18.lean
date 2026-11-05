import Morse
import RoundTrip.Check
import RoundTrip.Blind.VA_18

/-! # Round trip for VA_18 (Milnor, Appendix pp. 149–150: countable cell complexes)

The item lists three definitions (`Morse.IsRelCellAttachment`, `Morse.CellTower`,
`Morse.IsCountableCellComplexType`: `X` is homotopy equivalent to the mapping telescope of a tower
`K₀ → K₁ → ⋯` of iterated adjunction spaces, `K_{n+1}` obtained from `K_n` by attaching the cells
`cells (n+1)` along arbitrary maps) and one theorem, `Morse.IsCountableCellComplexType.of_homotopyEquiv`
(the notion is invariant under homotopy equivalence). `A` is the type of that theorem, universe `0`.

`B` (abstract Riemannian manifold `M`, complete, `p, q` not conjugate along any geodesic,
admissible levels `a_i`): each `Ω^{a_i}` and `Ω` have the homotopy type of a Hausdorff Mathlib
`CWComplex`, and there is one CW complex `Y` with subcomplexes `K_0 ⊆ K_1 ⊆ ⋯` exhausting it and a
commutative diagram of homotopy equivalences `Ω^{a_i} → K_i`.

* `B ⇒ A`: vacuous; `A` is a three-line transport lemma, proved outright.
* `A ⇒ B`: fails genuinely. `A` says nothing about path spaces; `B` is the existence part of
  Theorem 17.3 (Theorems 16.3/17.3 on an abstract manifold), plus Mathlib CW complexes, which the
  project's `IsCountableCellComplexType` does not provide (cellular approximation and the CW
  structure of a telescope, as in VA_17). Vocabulary: `IsCountableCellComplexType X cells` and the
  blind `HasCWType X` are not comparable without cellular approximation (the project's towers
  have non-cellular attaching maps and a telescope instead of a union with the weak topology);
  no dictionary is proved. -/

namespace RoundTrip.VA_18

/-- `A`: the listed theorem, universe `0`. -/
def A : Prop := type_of% @Morse.IsCountableCellComplexType.of_homotopyEquiv.{0}

/-- `A` outright (the project's proof is the same three lines). -/
theorem A_holds' : A := by
  intro X Y _ _ cells h e
  obtain ⟨T, ⟨e'⟩⟩ := h
  exact ⟨T, ⟨e.trans e'⟩⟩

/-- `B ⇒ A`: vacuous. -/
theorem B_to_A : B → A := fun _ => A_holds'

#rt_check RoundTrip.VA_18.B_to_A [Morse.IsCountableCellComplexType.of_homotopyEquiv]
#rt_overlap RoundTrip.VA_18.B_to_A [Morse.IsCountableCellComplexType.of_homotopyEquiv]

end RoundTrip.VA_18
