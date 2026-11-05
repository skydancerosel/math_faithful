import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_43

open Set Function Module
open scoped ContDiff Manifold Morse.MatrixInner

namespace RoundTrip.V3_43

/-- The project's statement: (1) Theorem 3.5 for `ℂPⁿ` (the Hermitian projections of trace one in
`Mₙ₊₁(ℂ)`): it is of the project's finite cell type (homotopy equivalent to an iterated adjunction
space) with one cell in each even dimension `≤ 2n` and no others; (2), (3) its Betti numbers over
every field are `1` in even degrees `≤ 2n` and `0` otherwise. -/
def A : Prop :=
  type_of% @Morse.CP.exists_cells ∧ type_of% @Morse.CP.bettiNumber_eq ∧
    type_of% @Morse.bettiNumber_complexProjectiveSpace

theorem A_holds : A :=
  ⟨@Morse.CP.exists_cells, @Morse.CP.bettiNumber_eq, @Morse.bettiNumber_complexProjectiveSpace⟩

/-- `A` re-proved outright from the project's lemmas outside the item (Milnor's function on
`ℂPⁿ` is Morse with `C_λ = 1` for `λ = 0, 2, …, 2n`, Theorem 3.5 and the lacunary principle). -/
theorem betti {n : ℕ} {c : Fin (n + 1) → ℝ} (hc : Injective c) {𝕜 : Type} [Field 𝕜] (l : ℕ) :
    Morse.Homology.bettiNumber 𝕜 (Morse.grassmannian (Fin (n + 1)) 1) l =
      if Even l ∧ l ≤ 2 * n then 1 else 0 := by
  let _ := (Morse.CP.isSliceSubmanifold (n := n)).chartedSpace
  rw [Morse.Homology.bettiNumber_eq_critCount_of_lacunary Morse.CP.isSliceSubmanifold
    Morse.CP.isCompact (Morse.CP.contDiff_height c) (Morse.CP.isNondegenerate_of_isCriticalPointM hc)
    (Homeomorph.refl _) (Morse.CP.lacunary hc) l, Morse.CP.critCount_height hc]

/-- B ⇒ A holds only vacuously: A is re-proved outright (above); B (integral homology, a Mathlib
CW complex, on the quotient model of `ℂPⁿ`) is not used. -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, fun hc => betti hc, fun n => betti (c := fun j : Fin (n + 1) => (j : ℝ))
    (Nat.cast_injective.comp Fin.val_injective)⟩
  intro n c hc
  let _ := (Morse.CP.isSliceSubmanifold (n := n)).chartedSpace
  obtain ⟨cells, hcell, hcount⟩ := Morse.theorem_3_5_count' Morse.CP.isSliceSubmanifold
    Morse.CP.isCompact (Morse.CP.contDiff_height c) (Morse.CP.isNondegenerate_of_isCriticalPointM hc)
  exact ⟨cells, hcell, fun l => (hcount l).trans (Morse.CP.critCount_height hc l)⟩

#rt_check RoundTrip.V3_43.B_to_A [Morse.CP.exists_cells, Morse.CP.bettiNumber_eq, Morse.bettiNumber_complexProjectiveSpace]
#rt_overlap RoundTrip.V3_43.B_to_A [Morse.CP.exists_cells, Morse.CP.bettiNumber_eq, Morse.bettiNumber_complexProjectiveSpace]

/-! A ⇒ B is not proved: A gives the project's `IsFiniteCellComplexType` (an iterated adjunction
space with arbitrary attaching maps) and Betti numbers over fields; B asks for a Mathlib
`CWComplex` (needs cellular approximation, absent) and integral homology (needs the universal
coefficient theorem plus finite generation, absent), on the quotient model (bridgeable by the
homeomorphism `z ↦ z zᴴ`, built in Items/V3_41.lean). -/

end RoundTrip.V3_43
