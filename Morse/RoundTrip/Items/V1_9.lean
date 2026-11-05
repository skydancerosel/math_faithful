import Morse
import RoundTrip.Check
import RoundTrip.Blind.V1_9

open scoped ContDiff Manifold

namespace RoundTrip.V1_9

/-- The project's statement: the types of the three listed theorems, universes instantiated at
`0`. -/
def A : Prop :=
  (type_of% @Morse.index_eq_of_morse_chart.{0}) ∧
  (type_of% @Morse.isNondegenerateCriticalPointM_of_morse_chart.{0, 0}) ∧
  (type_of% @Morse.indexM_eq_of_morse_chart.{0, 0})

theorem A_holds : A :=
  ⟨@Morse.index_eq_of_morse_chart.{0}, @Morse.isNondegenerateCriticalPointM_of_morse_chart.{0, 0},
    @Morse.indexM_eq_of_morse_chart.{0, 0}⟩

/-! ### Glue: a `PartialDiffeomorph` into `EuclideanSpace ℝ (Fin n)` gives a project
`IsSmoothCoord` with values in `Fin n → ℝ`. -/

section Glue

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- `ℝⁿ` (Euclidean) `≃ Fin n → ℝ` as an open partial homeomorphism. -/
noncomputable def eucl (n : ℕ) : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.toOpenPartialHomeomorph

/-- The coordinate system `z` read in `Fin n → ℝ`. -/
noncomputable def toCoord
    (z : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M
      (EuclideanSpace ℝ (Fin n)) ∞) : OpenPartialHomeomorph M (Fin n → ℝ) :=
  z.toOpenPartialHomeomorph.trans (eucl n)

theorem toCoord_isSmoothCoord
    (z : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M
      (EuclideanSpace ℝ (Fin n)) ∞) :
    Morse.IsSmoothCoord (EuclideanSpace ℝ (Fin n)) (toCoord z) :=
  (Morse.isSmoothCoord_toOpenPartialHomeomorph z).trans
    (EuclideanSpace.equiv (Fin n) ℝ).contDiff.contDiffOn
    (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.contDiffOn

theorem toCoord_source
    (z : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M
      (EuclideanSpace ℝ (Fin n)) ∞) : (toCoord z).source = z.source := by
  simp [toCoord, eucl]

theorem toCoord_apply
    (z : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M
      (EuclideanSpace ℝ (Fin n)) ∞) (x : M) (i : Fin n) : toCoord z x i = z x i := rfl

end Glue

theorem A_to_B : A → B := by
  intro hA n M _ _ _ _ f p l _ hl z hp hz0 hform
  have hs := toCoord_source z
  have h := hA.2.1 (E := EuclideanSpace ℝ (Fin n)) (M := M) (f := f) (p := p) (toCoord z)
    (toCoord_isSmoothCoord z) (by rw [hs]; exact hp)
    (by funext i; exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hz0) hl
    (by rw [hs]; exact hform)
  exact ⟨h.1, h.2.symm⟩

#rt_check RoundTrip.V1_9.A_to_B [Morse.index_eq_of_morse_chart,
  Morse.isNondegenerateCriticalPointM_of_morse_chart, Morse.indexM_eq_of_morse_chart]

end RoundTrip.V1_9
