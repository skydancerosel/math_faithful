import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_12

open CategoryTheory Morse.Homology

namespace RoundTrip.V3_12

/-- The project's statement (three algebraic lemmas), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.finrank_range_eq_altSum.{0, 0} ∧
  type_of% @Morse.LongExactSeq.altSum_le.{0, 0, 0, 0} ∧
  type_of% @Morse.FiltrationHomology.isSubadditive_altSum.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.finrank_range_eq_altSum.{0, 0}, @Morse.LongExactSeq.altSum_le.{0, 0, 0, 0},
    @Morse.FiltrationHomology.isSubadditive_altSum.{0, 0, 0}⟩

theorem A_to_B : A → B := by
  intro hA F _ E _ X Y Z hZY hYX l h1 h2 h3
  have h := hA.2.1 (subsetTripleLongExactSeq F hZY hYX) l
  have e : ∀ {P Q : Set E} (hPQ : P ⊆ Q), S F hPQ l =
      Morse.altSum (fun i => (Module.finrank F (subsetHomology F i hPQ) : ℤ)) l := fun _ => rfl
  rw [e, e, e]
  linarith

#rt_check RoundTrip.V3_12.A_to_B [Morse.finrank_range_eq_altSum, Morse.LongExactSeq.altSum_le,
  Morse.FiltrationHomology.isSubadditive_altSum]

end RoundTrip.V3_12
