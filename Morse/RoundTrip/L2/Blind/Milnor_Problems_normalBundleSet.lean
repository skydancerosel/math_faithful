import Morse
/-! Layer-2 blind definition of Milnor_Problems_normalBundleSet. Textbook: Milnor, *Morse
Theory*, §6, p. 32 (normal bundle `N ⊂ M × ℝᵏ`, tubular neighbourhoods; standard): the total
space `N = {(x, v) ∈ M × ℝᵏ : v ⊥ T_xM}` of the normal bundle of a smooth submanifold `M ⊆ ℝᵏ`,
as a subset of `ℝᵏ × ℝᵏ`.
Choices: `hM` (`M` is a smooth slice submanifold of `ℝᵏ` modelled on `ℝᵐ × ℝʷ`) is only the
setting and is not used. The tangent space `T_xM ⊆ ℝᵏ` is defined from scratch as the span of
the velocities `γ'(0)` of smooth curves `γ : (−ε, ε) → M` with `γ(0) = x` (for a submanifold
the velocities already form the usual tangent space). "Orthogonal" is for the Euclidean inner
product of `EuclideanSpace ℝ (Fin k)`. -/
namespace RoundTrip.L2.Milnor_Problems_normalBundleSet

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

/-- The textbook notion: the total space `{(x, v) : x ∈ M, v ⊥ T_xM}` of the normal bundle. -/
def T {k m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin k))}
    (_hM : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
      (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin w)) M) :
    Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) :=
  {p | p.1 ∈ M ∧ ∀ u ∈ tangentSpace M p.1, inner ℝ p.2 u = 0}

end RoundTrip.L2.Milnor_Problems_normalBundleSet
