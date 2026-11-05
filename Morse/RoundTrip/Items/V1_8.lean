import Morse
import RoundTrip.Check
import RoundTrip.Blind.V1_8

open scoped ContDiff Manifold

namespace RoundTrip.V1_8

/-- The project's statement: the types of the six listed theorems, universes instantiated at
`0`. -/
def A : Prop :=
  (type_of% @Morse.morse_lemma.{0}) ∧
  (type_of% @Morse.exists_morse_chart.{0}) ∧
  (type_of% @Morse.morse_lemmaM.{0, 0}) ∧
  (type_of% @Morse.exists_morse_chartM.{0, 0}) ∧
  (type_of% @Morse.exists_sqrt_family.{0}) ∧
  (type_of% @Morse.exists_linearEquiv_diagForm.{0})

theorem A_holds : A :=
  ⟨@Morse.morse_lemma.{0}, @Morse.exists_morse_chart.{0}, @Morse.morse_lemmaM.{0, 0},
    @Morse.exists_morse_chartM.{0, 0}, @Morse.exists_sqrt_family.{0},
    @Morse.exists_linearEquiv_diagForm.{0}⟩

/-! ### Glue: a project coordinate system with values in `Fin k → ℝ`, `k = n`, gives a
`PartialDiffeomorph` into `EuclideanSpace ℝ (Fin n)` with the same coordinates. -/

/-- `Fin n → ℝ ≃ ℝⁿ` (Euclidean) as an open partial homeomorphism. -/
noncomputable def ofPi (n : ℕ) : OpenPartialHomeomorph (Fin n → ℝ) (EuclideanSpace ℝ (Fin n)) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph.toOpenPartialHomeomorph

theorem transport {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (f : M → ℝ) (p : M) (lam : ℕ) (k : ℕ)
    (hk : k = n) (y : OpenPartialHomeomorph M (Fin k → ℝ))
    (hy : Morse.IsSmoothCoord (EuclideanSpace ℝ (Fin n)) y) (hp : p ∈ y.source) (hy0 : y p = 0)
    (hform : ∀ x ∈ y.source, f x = f p - ∑ i : Fin k with i.val < lam, y x i ^ 2
      + ∑ i : Fin k with lam ≤ i.val, y x i ^ 2) :
    ∃ z : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M
        (EuclideanSpace ℝ (Fin n)) ∞,
      p ∈ z.source ∧ z p = 0 ∧
      ∀ q ∈ z.source, f q = f p - ∑ i : Fin n with i.val < lam, (z q i) ^ 2
        + ∑ i : Fin n with lam ≤ i.val, (z q i) ^ 2 := by
  subst hk
  have hz := hy.trans (φ := ofPi k) (EuclideanSpace.equiv (Fin k) ℝ).symm.contDiff.contDiffOn
    (EuclideanSpace.equiv (Fin k) ℝ).contDiff.contDiffOn
  have hsrc : (y.trans (ofPi k)).source = y.source := by simp [ofPi]
  refine ⟨hz.toPartialDiffeomorph, ?_, ?_, fun q hq => ?_⟩
  · change p ∈ (y.trans (ofPi k)).source
    rw [hsrc]; exact hp
  · change (EuclideanSpace.equiv (Fin k) ℝ).symm (y p) = 0
    rw [hy0, map_zero]
  · change q ∈ (y.trans (ofPi k)).source at hq
    rw [hsrc] at hq
    exact hform q hq

theorem A_to_B : A → B := by
  intro hA n M _ _ _ _ f p hf hnd
  obtain ⟨y, hy, hp, -, hy0, hform⟩ :=
    hA.2.2.1 (E := EuclideanSpace ℝ (Fin n)) (M := M) (f := f) (p := p) (U := Set.univ)
      isOpen_univ trivial hf.contMDiffOn hnd
  exact transport f p _ _ finrank_euclideanSpace_fin y hy hp hy0 hform

#rt_check RoundTrip.V1_8.A_to_B [Morse.morse_lemma, Morse.exists_morse_chart, Morse.morse_lemmaM,
  Morse.exists_morse_chartM, Morse.exists_sqrt_family, Morse.exists_linearEquiv_diagForm]

end RoundTrip.V1_8
