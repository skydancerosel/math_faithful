import Morse
import RoundTrip.L2.Blind.Morse_IsStrongDeformationRetract

/-! Layer-2 check of `Morse.IsStrongDeformationRetract` (a retraction-valued `r : X → X` with values
in `A` and a `HomotopyRel` from the identity to `r` rel `A`) against the blind textbook definition
(a homotopy `[0,1] × X → X` from the identity, ending in `A`, fixing `A` at all times). The
homotopy of the project is the blind one, and `r = r₁`. -/

namespace RoundTrip.L2.Morse_IsStrongDeformationRetract

open scoped unitInterval

theorem agree {X : Type} [TopologicalSpace X] (A : Set X) :
    Morse.IsStrongDeformationRetract A ↔ T A := by
  constructor
  · rintro ⟨r, hrA, ⟨H⟩⟩
    refine ⟨H.toContinuousMap, fun x => H.apply_zero x, fun x => ?_, fun t a ha => ?_⟩
    · change H (1, x) ∈ A
      rw [H.apply_one]
      exact hrA x
    · change H (t, a) = a
      exact H.eq_fst t ha
  · rintro ⟨r, h0, h1, hA⟩
    let r₁ : C(X, X) := r.comp ((ContinuousMap.const X (1 : I)).prodMk (ContinuousMap.id X))
    let H : (ContinuousMap.id X).HomotopyRel r₁ A :=
      { toContinuousMap := r
        map_zero_left := h0
        map_one_left := fun _ => rfl
        prop' := fun t a ha => hA t a ha }
    exact ⟨r₁, h1, ⟨H⟩⟩

end RoundTrip.L2.Morse_IsStrongDeformationRetract
