import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_28

namespace RoundTrip.V15_28

/-- The project's statement (universe instantiated at `0`, arbitrary finite `ι`,
`IsAnticommFamily J k` (any `k ≥ 0`), `p ∈ Ω_k = Morse.Omega J k`, `V ∈ tanAlg J k p`, ANY `V`
(no `exp V = −p`-type hypothesis)): (1) `isJacobiField_killing`: for `X ∈ isoAlg J k p` (skew,
commuting with `p` and `J_1, …, J_{k−1}`), the Killing field `t ↦ Xγ(t) − γ(t)X` is a Jacobi
field (`IsJacobiField` of the slice submanifold `omegaStratum J k p`) along `γ(t) = p exp(tV)`;
(2) `finrank_le_conjMultiplicity`: for a subspace `𝒳 ⊆ isoAlg` commuting with `exp(τV)` on which
`X ↦ [X, V]` is injective, `dim 𝒳 ≤ conjMultiplicity … τ` (the project's multiplicity of
`γ(τ)` as a conjugate point); (3) `sum_finrank_le_formIndex`: for finitely many `τ ∈ (0,1)` and
such `𝒳_τ`, `Σ_τ dim 𝒳_τ ≤ formIndex (energyHessian …)` (the project's index, via Theorem
15.1). -/
def A : Prop :=
  type_of% @Morse.isJacobiField_killing.{0} ∧ type_of% @Morse.finrank_le_conjMultiplicity.{0} ∧
    type_of% @Morse.sum_finrank_le_formIndex.{0}

theorem A_holds : A :=
  ⟨@Morse.isJacobiField_killing.{0}, @Morse.finrank_le_conjMultiplicity.{0},
    @Morse.sum_finrank_le_formIndex.{0}⟩

/-! Neither direction is proved (see `Items/V15_28.json`).

* A ⇒ B: B's conclusions are in the blind subset vocabulary: `conjDim` (dimension of spaces of
  variation fields of variations through blind geodesics `IsGeodOn` of the SUBSET `Ω_k(n)`,
  vanishing at `0`, `b`) and `idxIn` (Milnor's variational index via `HessNeg`). A's are the
  project's `IsJacobiField`/`conjMultiplicity`/`formIndex (energyHessian …)` on the slice
  submanifold `omegaStratum`. The dictionary between them (`conjMultiplicity ≤ conjDim`,
  `formIndex ≤ idxIn`; the subset analogue of `LamEq` of `Items/V9_23.lean`) is not available.
  Modulo the dictionary the remaining glue is elementary Lie algebra, not in A: an eigenvector
  `B ∈ T` of `K_A` with eigenvalue `μ > 0` gives `X = [A, B] ∈ isoAlg` (skew, commuting with `J`
  and the `J_α`), `ad_A X = −4μB ≠ 0` (injectivity), `ad_A² X = −4μX` so `exp(τπA)` commutes with
  `X` at `τ = j/√μ`; eigenspaces for different `μ` give independent `𝒳_τ`, so
  `Σ_τ dim 𝒳_τ = Σ_μ mult(μ) · #{j ≥ 1 | j² < μ}`. B's first claim (`K_A` preserves `T`) is not in
  A (elementary). (B's second claim could even be proved directly with the explicit Killing
  variation `u ↦ e^{uX}γe^{−uX}` through blind geodesics, bypassing A.)
* B ⇒ A: A's statements are in the project's vocabulary and for arbitrary `V ∈ tanAlg` and
  arbitrary Killing spaces `𝒳 ⊆ isoAlg`; B only bounds the blind `conjDim`/`idxIn` of the
  specific geodesics `J exp(πtA)` with `exp(πA) = −I` by eigenvalue counts of `K_A`. A could
  only be re-proved outright (vacuously). -/

end RoundTrip.V15_28
