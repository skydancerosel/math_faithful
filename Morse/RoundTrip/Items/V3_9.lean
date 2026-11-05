import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_9

open CategoryTheory Morse.Homology

namespace RoundTrip.V3_9

/-- The declarations of this item (`Morse.LongExactSeq`, `Morse.FiltrationHomology`,
`Morse.morseNumber`, `Morse.altSum`, `Morse.FiltrationHomology.ofSteps`) are all definitions:
there is no listed theorem, so the project's formal statement is the empty conjunction. -/
def A : Prop := True

theorem A_holds : A := trivial

/-! ### Vocabulary check: B's exactness conditions are exactly the fields of `Morse.LongExactSeq`. -/

section Vocab

variable {F : Type} [Field F] {P Q R : ℕ → Type} [∀ i, AddCommGroup (P i)] [∀ i, Module F (P i)]
  [∀ i, AddCommGroup (Q i)] [∀ i, Module F (Q i)] [∀ i, AddCommGroup (R i)] [∀ i, Module F (R i)]

/-- The exactness conditions of B, for arbitrary maps `f, g, δ`. -/
def BExact (f : ∀ i, P i →ₗ[F] Q i) (g : ∀ i, Q i →ₗ[F] R i) (δ : ∀ i, R (i + 1) →ₗ[F] P i) :
    Prop :=
  (∀ n, LinearMap.range (δ n) = LinearMap.ker (f n)) ∧
  (∀ n, LinearMap.range (f n) = LinearMap.ker (g n)) ∧
  (∀ n, LinearMap.range (g (n + 1)) = LinearMap.ker (δ n)) ∧
  LinearMap.range (g 0) = ⊤

/-- A project `LongExactSeq` satisfies B's conditions. -/
theorem bExact_of_les (L : Morse.LongExactSeq F P Q R) : BExact L.f L.g L.δ :=
  ⟨fun n => (L.exact_δ_f n).linearMap_ker_eq.symm, fun n => (L.exact_f_g n).linearMap_ker_eq.symm,
    fun n => (L.exact_g_δ n).linearMap_ker_eq.symm, LinearMap.range_eq_top.2 L.surjective_g_zero⟩

/-- Conversely, maps satisfying B's conditions form a project `LongExactSeq`. -/
def lesOfBExact (f : ∀ i, P i →ₗ[F] Q i) (g : ∀ i, Q i →ₗ[F] R i) (δ : ∀ i, R (i + 1) →ₗ[F] P i)
    (h : BExact f g δ) : Morse.LongExactSeq F P Q R where
  f := f
  g := g
  δ := δ
  exact_f_g i := LinearMap.exact_iff.2 (h.2.1 i).symm
  exact_g_δ i := LinearMap.exact_iff.2 (h.2.2.1 i).symm
  exact_δ_f i := LinearMap.exact_iff.2 (h.1 i).symm
  surjective_g_zero := LinearMap.range_eq_top.1 h.2.2.2

end Vocab

/-- `B` holds outright: the rank statement is `Module.finrank_eq_rank`, and the exactness of the
sequence of a triple of subsets comes from the project's exactness of the singular homology
sequence of a triple (`TopTriple.exact₁/₂/₃`, `TopTriple.epi_map₂_zero`), read in `ModuleCat` as
`Function.Exact`. (The proof does not go through `Morse.LongExactSeq`, which is one of this item's
declarations.) -/
theorem B_holds : B := by
  refine ⟨fun F _ E _ A B h i hfin => Module.finrank_eq_rank F _, fun F _ E _ A B D hAB hBD => ?_⟩
  intro T
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_, ?_⟩
  · exact ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (T.exact₁ (ModuleCat.of F F) n)).linearMap_ker_eq.symm
  · exact ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (T.exact₂ (ModuleCat.of F F) n)).linearMap_ker_eq.symm
  · exact ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (T.exact₃ (ModuleCat.of F F) n)).linearMap_ker_eq.symm
  · exact LinearMap.range_eq_top.2
      ((ModuleCat.epi_iff_surjective _).1 (T.epi_map₂_zero (ModuleCat.of F F)))

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V3_9.A_to_B [Morse.LongExactSeq, Morse.FiltrationHomology, Morse.morseNumber,
  Morse.altSum, Morse.FiltrationHomology.ofSteps]
#rt_check RoundTrip.V3_9.B_to_A [Morse.LongExactSeq, Morse.FiltrationHomology, Morse.morseNumber,
  Morse.altSum, Morse.FiltrationHomology.ofSteps]
#rt_overlap RoundTrip.V3_9.B_to_A [Morse.LongExactSeq, Morse.FiltrationHomology,
  Morse.morseNumber, Morse.altSum, Morse.FiltrationHomology.ofSteps]

end RoundTrip.V3_9
