import Morse
/-! Layer-2 blind definition of Morse_IsComplexSubmanifold. Textbook: Milnor, *Morse Theory*, §7,
p. 39 ff.: a smooth (real) submanifold `N` of `ℂᵐ = ℝ²ᵐ` is a complex submanifold when each
tangent space `T_xN` is a complex subspace, i.e. `J(T_xN) ⊆ T_xN`, `J` = multiplication by `i`.
Choices: `hN` (`N` a smooth slice submanifold of `V`) is the setting and is not used. `T_xN` is
defined from scratch as the span of the velocities `γ'(0)` of smooth curves `γ : (−ε, ε) → N`
with `γ(0) = x`. The textbook takes `J` to be the complex structure (`J² = −1`); no condition on
`J` is imposed here: for an arbitrary continuous linear `J`, `T` is `J`-invariance of all tangent
spaces. The inner product of `V` is not used. -/
namespace RoundTrip.L2.Morse_IsComplexSubmanifold

open scoped ContDiff

section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `v` is the velocity `γ'(0)` of a smooth curve `γ : (−ε, ε) → N` with `γ(0) = q`. -/
def IsVelocity (N : Set V) (q v : V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V, ContDiffOn ℝ ∞ γ (Set.Ioo (-ε) ε) ∧
    Set.MapsTo γ (Set.Ioo (-ε) ε) N ∧ γ 0 = q ∧ HasDerivAt γ v 0

/-- The tangent space `T_qN ⊆ V` of a subset `N ⊆ V` at `q`: span of the velocities. -/
def tangentSpace (N : Set V) (q : V) : Submodule ℝ V :=
  Submodule.span ℝ {v | IsVelocity N q v}
end

/-- The textbook notion: every tangent space of `N` is `J`-invariant (a complex subspace). -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {N : Set V} (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    (J : V →L[ℝ] V) : Prop :=
  ∀ x ∈ N, ∀ v ∈ tangentSpace N x, J v ∈ tangentSpace N x

end RoundTrip.L2.Morse_IsComplexSubmanifold
