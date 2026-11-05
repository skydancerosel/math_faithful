import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_6

open Matrix

namespace RoundTrip.V15_6

/-- The project's statement (universes instantiated at `0`): the "if" halves of Assertions 1 and 2,
for every skew `A` (Assertion 1) and for arbitrary `J, J_α, A` (Assertion 2). -/
def A : Prop :=
  type_of% @Morse.isComplexStructure_mul_exp.{0} ∧ type_of% @Morse.anticomm_mul_exp.{0}

theorem A_holds : A := ⟨@Morse.isComplexStructure_mul_exp.{0}, @Morse.anticomm_mul_exp.{0}⟩

theorem flip_neg {ι : Type} [Fintype ι] {a b : Mat ι} (h : a = -b) : b = -a := by
  rw [h, neg_neg]

/-- A ⇒ B: the implications hold for every skew `A`, so in particular near `0`. -/
theorem A_to_B : A → B := by
  rintro ⟨h1, h2⟩ n k Js hk _ J hJ
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hJc, hJa⟩ := hJ
  refine Filter.Eventually.of_forall fun A hA => ⟨fun hAJ => h1 hJc hA hAJ, ?_⟩
  intro hcomm α hα1 hα2
  have hα2' : α ≤ j := by omega
  exact flip_neg (h2 (flip_neg (hJa α hα1 hα2')) (hcomm α hα1 hα2))

/-- B ⇒ A, only vacuously: `A` is proved outright (B gives the implications only for small skew
`A`, `J ∈ Ω_k` and `J_α` in an anticommuting family of complex structures, while A's Assertion 2
assumes nothing on `J`, `J_α`, `A` beyond the (anti)commutation relations). -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨@fun n _ _ J A hJ hA hAJ => ?_, @fun n _ _ J A Jα hJα hA => ?_⟩
  · have e1 := Morse.mul_exp_eq_exp_neg_mul hAJ
    have hAJ' : -A * J = -(J * -A) := by rw [neg_mul, hAJ, mul_neg]
    have e2 := Morse.mul_exp_eq_exp_neg_mul hAJ'
    rw [neg_neg] at e2
    refine ⟨?_, ?_⟩
    · rw [mem_orthogonalGroup_iff', transpose_mul, ← Matrix.exp_transpose, hA, Matrix.mul_assoc,
        ← Matrix.mul_assoc Jᵀ, (show Jᵀ * J = 1 by simpa [mem_orthogonalGroup_iff'] using hJ.1),
        Matrix.one_mul, Morse.exp_neg_mul_exp]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (NormedSpace.exp A), ← e2, Matrix.mul_assoc,
        ← Matrix.mul_assoc J J, hJ.2, Matrix.neg_mul, Matrix.one_mul, Morse.exp_neg_mul_exp]
  · have h : Commute (NormedSpace.exp A) Jα := by
      open scoped Matrix.Norms.Operator in exact hA.exp_left
    rw [← Matrix.mul_assoc, hJα, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, h.eq]

#rt_check RoundTrip.V15_6.A_to_B [Morse.isComplexStructure_mul_exp, Morse.anticomm_mul_exp]
#rt_check RoundTrip.V15_6.B_to_A [Morse.isComplexStructure_mul_exp, Morse.anticomm_mul_exp]
#rt_overlap RoundTrip.V15_6.B_to_A [Morse.isComplexStructure_mul_exp, Morse.anticomm_mul_exp]

end RoundTrip.V15_6
