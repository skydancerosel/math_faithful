import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_5

open Matrix

namespace RoundTrip.V14_5

/-- The project's statement (universes of `ι` instantiated at `0`): `[diag(d), W]_{jl} =
(d_j − d_l) w_{jl}` and, for `A = suDiag k = diag(iπk_j)` (any finite index type, any integers
`k_j`, ANY complex matrix `W`), `K_A(W)_{jl} = (π²/4)(k_j − k_l)² w_{jl}`. (`suDiag`, `jacobiMat`
are vocabulary.) -/
def A : Prop :=
  type_of% @Morse.commutator_diagonal_apply.{0} ∧ type_of% @Morse.jacobiMat_suDiag_apply.{0}

theorem A_holds : A := ⟨@Morse.commutator_diagonal_apply.{0}, @Morse.jacobiMat_suDiag_apply.{0}⟩

section Vocab

variable {n : ℕ}

/-- The blind `milnorA` is the project's `suDiag`. -/
theorem milnorA_eq_suDiag (k : Fin n → ℤ) : milnorA k = Morse.suDiag k := by
  unfold milnorA diagI Morse.suDiag
  congr 1
  funext j
  push_cast
  rfl

/-- The blind `Kop` (scalar `(1/4 : ℝ)`) is the project's `jacobiMat` (scalar `(1/4 : ℂ)`). -/
theorem Kop_eq_jacobiMat (A W : Mat n) : Kop A W = Morse.jacobiMat A W := by
  unfold Kop Morse.jacobiMat
  rw [← Complex.coe_smul]
  push_cast
  rfl

end Vocab

theorem A_to_B : A → B := by
  rintro ⟨-, hA2⟩ n k _ _ W _
  ext j l
  rw [Kop_eq_jacobiMat, milnorA_eq_suDiag, hA2, Matrix.of_apply]

/-- `A` is proved outright: `B` only covers `W ∈ 𝔰𝔲(n)` and odd `k_j` with `Σ k_j = 0`, which
cannot give the entry formula when `k_j − k_l` is odd (nor the general commutator formula). -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_⟩
  · intro ι _ _ d W j l
    simp only [Matrix.sub_apply, diagonal_mul, mul_diagonal]
    ring
  · intro ι _ _ k W j l
    simp only [Morse.jacobiMat, Morse.suDiag, Matrix.smul_apply, Matrix.sub_apply, mul_diagonal,
      diagonal_mul, smul_eq_mul]
    push_cast
    linear_combination (-(1 / 4 : ℂ) * Real.pi ^ 2 * ((k j : ℂ) - k l) ^ 2 * W j l) * Complex.I_sq

#rt_check RoundTrip.V14_5.A_to_B [Morse.commutator_diagonal_apply, Morse.jacobiMat_suDiag_apply]
#rt_check RoundTrip.V14_5.B_to_A [Morse.commutator_diagonal_apply, Morse.jacobiMat_suDiag_apply]
#rt_overlap RoundTrip.V14_5.B_to_A [Morse.commutator_diagonal_apply, Morse.jacobiMat_suDiag_apply]
#rt_overlap RoundTrip.V14_5.A_to_B [Morse.commutator_diagonal_apply, Morse.jacobiMat_suDiag_apply]

end RoundTrip.V14_5
