import Morse
/-! Layer-2 blind definition of Morse_focalSet. Textbook: Milnor, *Morse Theory*, §6, p. 32: the
set of focal points of `M ⊂ ℝⁿ`, i.e. the points `e` that are focal points of `(M, q)` for some
`q ∈ M`: `e = q + v`, `(q, v) ∈ N` (normal bundle), and the Jacobian of the endpoint map
`E(q, v) = q + v`, `E : N → ℝⁿ`, at `(q, v)` has positive nullity.
Choices: `hM` (`M` a smooth slice submanifold of `ℝⁿ` modelled on `ℝᵏ × ℝʷ`) and `hkw`
(`k + w = n`) are the setting and are not used. Tangent spaces (of `M ⊆ ℝⁿ` and of
`N ⊆ ℝⁿ × ℝⁿ`) are defined from scratch as spans of velocities `γ'(0)` of smooth curves
`γ : (−ε, ε) → M` (resp. `N`) through the point; the manifold `N` is the normal bundle
`{(q, v) : q ∈ M, v ⊥ T_qM} ⊆ ℝⁿ × ℝⁿ` with that tangent space (Milnor: `N` is a smooth
`n`-manifold). `E : N → ℝⁿ` is the restriction of the linear map `(a, b) ↦ a + b`, so its
Jacobian at `x ∈ N` is `(a, b) ↦ a + b` on `T_xN`; nullity = `finrank` of its kernel (all spaces
are finite-dimensional). `e = q + v` is encoded as `v = e − q`. -/
namespace RoundTrip.L2.Morse_focalSet

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

section
variable {n : ℕ}

/-- The normal bundle `N = {(q, v) : q ∈ M, v ⊥ T_qM} ⊆ ℝⁿ × ℝⁿ`. -/
def normalBundle (M : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  {p | p.1 ∈ M ∧ ∀ u ∈ tangentSpace M p.1, inner ℝ p.2 u = 0}

/-- The differential of the endpoint map `E(q, v) = q + v` of `ℝⁿ × ℝⁿ` (a linear map, so its
differential at every point is `(a, b) ↦ a + b`). -/
def dEndpoint : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin n) :=
  LinearMap.fst ℝ _ _ + LinearMap.snd ℝ _ _

/-- Nullity of the Jacobian of `E|_N : N → ℝⁿ` at `x ∈ N`: the dimension of the kernel of
`dE_x` restricted to the tangent space `T_xN ⊆ ℝⁿ × ℝⁿ`. -/
noncomputable def nullity (M : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : ℕ :=
  Module.finrank ℝ (LinearMap.ker ((dEndpoint (n := n)).domRestrict
    (tangentSpace (normalBundle M) x)))
end

/-- The textbook notion: the set of focal points `{e : ∃ q ∈ M, e focal point of (M, q)}`. -/
def T {n k w : ℕ} {M : Set (EuclideanSpace ℝ (Fin n))}
    (_hM : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin w)) M)
    (_hkw : k + w = n) : Set (EuclideanSpace ℝ (Fin n)) :=
  {e | ∃ q ∈ M, (q, e - q) ∈ normalBundle M ∧ 0 < nullity M (q, e - q)}

end RoundTrip.L2.Morse_focalSet
