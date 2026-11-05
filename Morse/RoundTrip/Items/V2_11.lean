import Morse
import RoundTrip.Check
import RoundTrip.Blind.V2_11

namespace RoundTrip.V2_11

/-- The declarations of this item (`Morse.IsCellAttachment`, `Morse.IsFiniteCellComplexType`) are
definitions: there is no listed theorem, so the project's formal statement is the empty
conjunction. -/
def A : Prop := True

theorem A_holds : A := trivial

theorem B_to_A : B → A := fun _ => trivial

/-! `A ⇒ B` (i.e. proving `B`) is not done. `B` is the cellular approximation theorem for maps
`S^{λ-1} → X` into a Mathlib CW-complex, together with the fact that attaching a cell along a
cellular map gives a CW-complex. Neither is in Mathlib or the project. This is precisely what the
project avoids: its `IsFiniteCellComplexType X cells` ("`X` is homotopy equivalent to a space
obtained from `∅` by attaching cells of the listed dimensions one at a time, along arbitrary
continuous maps") replaces "homotopy equivalent to a finite CW-complex". The two notions agree
only via cellular approximation plus Lemmas 3.6/3.7. Neither implication between them is proved
here: CW ⇒ iterated adjunction needs a cell-by-cell decomposition of a Mathlib `CWComplex` as
pushouts, and iterated adjunction ⇒ CW needs `B`. -/

#rt_check RoundTrip.V2_11.B_to_A [Morse.IsCellAttachment, Morse.IsFiniteCellComplexType]
#rt_overlap RoundTrip.V2_11.B_to_A [Morse.IsCellAttachment, Morse.IsFiniteCellComplexType]

end RoundTrip.V2_11
