import Morse
/-! Layer-2 blind definition of Morse_IsMatrixGroup. Textbook: Milnor, *Morse Theory*, §21
(pp. 121–125) and Part IV: a compact Lie group `G` and its Lie algebra `𝔤`, realised as a compact
matrix group: `G` is a closed subgroup of the unitary group `U(n)` (`O(n)` for `𝕜 = ℝ`), and its
Lie algebra is `𝔤 = {X : X* = −X, exp(tX) ∈ G for all t ∈ ℝ}` with the commutator bracket.
Choices: `hG` (`G` is a smooth slice submanifold of `M_n(𝕜)`, modelled on `Z` with normal model
`W`) is the setting and is not used. `U(n)` is Mathlib's `Matrix.unitaryGroup ι 𝕜`; "subgroup":
`1 ∈ G`, closed under products and (matrix) inverses; "closed": `IsClosed G` in `M_n(𝕜)`
(compactness then follows from `G ⊆ U(n)`). `X*` is `Xᴴ`; `exp` is Mathlib's matrix exponential
`NormedSpace.exp`, `t • X` the real scalar multiple. Only the carrier of `𝔤` is constrained (the
bracket of a `LieSubalgebra` is the commutator already). That `𝔤` is also the tangent space
`T_I G` and that `dim G = dim 𝔤` (`= dim Z`) are theorems for closed subgroups (Cartan / von
Neumann), not conjuncts. Instances: the matrix norm of the signature is the project's
`Morse.MatrixInner` normed group / normed space (setting; local instances), the Lie ring is
Mathlib's `LieRing.ofAssociativeRing` (commutator; local instance as in Mathlib). -/
namespace RoundTrip.L2.Morse_IsMatrixGroup

open scoped Matrix

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Morse.MatrixInner.normedAddCommGroup Morse.MatrixInner.normedSpace

/-- The textbook notion: `G` is a closed subgroup of `U(n)` and
`𝔤 = {X skew-Hermitian : exp(tX) ∈ G ∀ t ∈ ℝ}`. -/
def T {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {G : Set (Matrix ι ι 𝕜)}
    (_hG : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ (Matrix ι ι 𝕜)) Z W G)
    (𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)) : Prop :=
  (G ⊆ (Matrix.unitaryGroup ι 𝕜 : Set (Matrix ι ι 𝕜)) ∧ (1 : Matrix ι ι 𝕜) ∈ G ∧
    (∀ A ∈ G, ∀ B ∈ G, A * B ∈ G) ∧ (∀ A ∈ G, A⁻¹ ∈ G) ∧ IsClosed G) ∧
  ∀ X : Matrix ι ι 𝕜, X ∈ 𝔤 ↔ (Xᴴ = -X ∧ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)

end RoundTrip.L2.Morse_IsMatrixGroup
