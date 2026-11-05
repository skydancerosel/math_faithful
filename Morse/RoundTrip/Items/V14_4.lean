import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_4

open Matrix Complex

namespace RoundTrip.V14_4

/-- The project's statement (universes of `ι` instantiated at `0`): a skew-Hermitian `A` satisfies
`A² = −π²I` iff `A = iπ(2P − I)` for a Hermitian projection `P`, and
`tr(iπ(2P − I)) = iπ(2 tr P − n)`. Pure matrix algebra: no `exp`, no minimality, no `Eigen(iπ)`. -/
def A : Prop :=
  type_of% @Morse.sq_eq_neg_pi_sq_iff.{0} ∧ type_of% @Morse.trace_pi_smul_projection.{0}

theorem A_holds : A := ⟨@Morse.sq_eq_neg_pi_sq_iff.{0}, @Morse.trace_pi_smul_projection.{0}⟩

/-! `A_to_B` is not proved. `B` is about `minVelIn`, the velocities of the MINIMAL geodesics from
`I` to `−I` (among all piecewise smooth paths in `U(n)`, resp. `SU(2m)`): to use `A` one must know
that these are exactly the skew-Hermitian `A` with `A² = −π²I` (all `k_j = ±1`), which needs the
lower bound `π√n` for the length of every path from `I` to `−I` in the group — absent from `A` (the
project proves it only for `SU(2m)`, outside the item, via Hopf–Rinow: `riemDist_one_neg_one`,
`isMinimalGeodesic_exp_iff`; nothing for `U(n)`). Further glue `A` lacks: `P` is the orthogonal
projection onto `Eigen(iπ)` (so `A ↦ Eigen(iπ)` is injective), every subspace `V` has a Hermitian
projection `P_V` (surjectivity), and `tr P_V = dim V` (the `SU(2m)` image is the `m`-dimensional
subspaces). -/

/-- `A` is matrix algebra and is proved outright (the hypothesis `B` is not used). -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_⟩
  · intro ι _ _ A hA
    have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    constructor
    · intro h2
      refine ⟨(1 / 2 : ℂ) • (1 - (I / Real.pi) • A), ?_, ?_, ?_⟩
      · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hA]
        simp only [star_div₀, star_one, RCLike.star_def, conj_I, conj_ofReal, smul_neg,
          neg_div, neg_smul, neg_neg, map_ofNat]
      · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc,
          mul_smul_comm, smul_smul, h2]
        match_scalars <;> field_simp
        all_goals ((try simp only [I_sq]); ring1)
      · match_scalars <;> field_simp
        all_goals ((try simp only [I_sq]); ring1)
    · rintro ⟨P, -, hP, rfl⟩
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc,
        mul_smul_comm, smul_smul, hP]
      match_scalars
      · ring
      · linear_combination (Real.pi : ℂ) ^ 2 * I_sq
  · intro ι _ _ P
    rw [trace_smul, trace_sub, trace_smul, trace_one, smul_eq_mul, smul_eq_mul]

#rt_check RoundTrip.V14_4.B_to_A [Morse.sq_eq_neg_pi_sq_iff, Morse.trace_pi_smul_projection]
#rt_overlap RoundTrip.V14_4.B_to_A [Morse.sq_eq_neg_pi_sq_iff, Morse.trace_pi_smul_projection]

end RoundTrip.V14_4
