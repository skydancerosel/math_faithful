import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_29

namespace RoundTrip.V15_29

/-- The project's statement (universe instantiated at `0`). Abstract operator theory on a
finite-dimensional real inner product space `E` (later `ℝⁿ = EuclideanSpace`), operators as
continuous linear maps: (1) `exists_minInvar_decomp`: for ANY star-signed family `𝒢`, every
invariant `U` splits into a list of mutually orthogonal minimal invariant pieces; (2)
`IsMinInvar.exists_scalar`: a self-adjoint operator commuting with `𝒢` and preserving a minimal
piece is a scalar there; for Milnor's operators (`IsOmegaOps k a q j`: `a = A` skew, `q = J`, `j α
= J_α`, `α < k`, with Milnor's relations): (3) `exists_sq_eq`: `A² = −c` on each minimal piece;
(4) `one_le_of_minInvar` (matrices on `EuclideanSpace ℝ ι`): `exp(πA) = −I`, `A² = −c` on
`M ≠ 0` ⇒ `c ≥ 1`; (5) `isClifford_cliffFam`, `isMinimal_cliffFam`: on a minimal piece,
`J_1, …, J_{k−1}, J, s·JA` (`s²c = 1`) satisfy the Clifford relations and form a MINIMAL Clifford
module; (6) `exists_inter` (`k + 1 ≤ 8`, `k + 1 ≢ 3 mod 4`): Lemma 24.8 between two pieces, a
LINEAR isomorphism `T : M₀ ≃ M₁` intertwining `cliffFam … a₀⁻¹` with `cliffFam … (−b⁻¹)`;
(7) `exists_piece_gt`: if `A² ≠ −1` (and `c ≥ 1` on all pieces) some piece has `c > 1`;
(8) `exists_omegaPieceData` (`k + 1 ≤ 8`, `k + 1 ≢ 3 mod 4`, `A² ≠ −1`): the data for the index
bound and `(s + 1)·m_{k+1} = dim E` for a splitting into `s + 1` pieces. -/
def A : Prop :=
  type_of% @Morse.exists_minInvar_decomp.{0} ∧ type_of% @Morse.IsMinInvar.exists_scalar.{0} ∧
    type_of% @Morse.IsOmegaOps.exists_sq_eq.{0} ∧ type_of% @Morse.one_le_of_minInvar.{0} ∧
    type_of% @Morse.IsOmegaOps.isClifford_cliffFam.{0} ∧
    type_of% @Morse.IsOmegaOps.isMinimal_cliffFam.{0} ∧
    type_of% @Morse.IsOmegaOps.exists_inter.{0} ∧ type_of% @Morse.IsOmegaOps.exists_piece_gt.{0} ∧
    type_of% @Morse.IsOmegaOps.exists_omegaPieceData.{0}

theorem A_holds : A :=
  ⟨@Morse.exists_minInvar_decomp.{0}, @Morse.IsMinInvar.exists_scalar.{0},
    @Morse.IsOmegaOps.exists_sq_eq.{0}, @Morse.one_le_of_minInvar.{0},
    @Morse.IsOmegaOps.isClifford_cliffFam.{0}, @Morse.IsOmegaOps.isMinimal_cliffFam.{0},
    @Morse.IsOmegaOps.exists_inter.{0}, @Morse.IsOmegaOps.exists_piece_gt.{0},
    @Morse.IsOmegaOps.exists_omegaPieceData.{0}⟩

/-- Vocabulary: B's `mK` is the project's `milnorM` (Milnor's table, with `m_{k+8} = 16 m_k`). -/
theorem mK_eq_milnorM : ∀ k, mK k = Morse.milnorM k
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | k + 8 => by rw [mK, mK_eq_milnorM k]; rfl

/-! Neither direction is proved (see `Items/V15_29.json`).

* A ⇒ B fails genuinely: (i) B asserts `A² = −a²` on each minimal piece with `a` an ODD integer;
  A only has `A² = −c`, `c ≥ 1` (`one_le_of_minInvar`; the project notes that oddness is never
  used). (ii) B asserts `dim M = m_{k+1}` for every minimal piece and `s · m_{k+1} = n` for every
  splitting, for ALL `k ≥ 1`; A has the dimension only inside `exists_omegaPieceData`, only for
  `k + 1 ≤ 8` and only when `A² ≠ −1` (non-minimal geodesics). (iii) B's Lemma 24.8 gives an
  ISOMETRY `M_h → M̄_j` for all `k ≢ 2 (mod 4)`; A's `exists_inter` gives only a linear
  intertwiner and only for `k + 1 ≤ 8`. The splitting (B's (1)), the Clifford/minimality facts for
  `J' = a⁻¹JA` (B's (2) minus oddness and dimension) are in A (after transport from
  `EuclideanSpace`/continuous linear maps to `Fin n → ℝ`/matrices and B's `famA`).
* B ⇒ A fails: A's lemmas are general (splitting for ANY star-signed family, Schur's lemma for
  self-adjoint commuting operators, `c ≥ 1` for any nonzero `A²`-eigenspace, the Clifford data on
  any minimal piece of abstract operators); B speaks only of Milnor's specific family
  `{J_1, …, J_{k−1}, J, A}` on `ℝⁿ`; A could only be re-proved outright (vacuously). -/

end RoundTrip.V15_29
