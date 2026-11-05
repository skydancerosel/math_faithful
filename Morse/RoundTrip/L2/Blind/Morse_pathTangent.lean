import Morse
/-! Layer-2 blind definition of Morse_pathTangent. Textbook: Milnor, *Morse Theory*, §12,
pp. 67-68: the tangent space `TΩ_ω` of the path space at `ω` is the vector space of piecewise
smooth vector fields `W` along `ω` (`W_t ∈ T_{ω(t)}M`) with `W_0 = 0` and `W_1 = 0`.
Choices: `hN` (`N` a smooth slice submanifold of `V`) is the setting and is not used. A vector
field along `c` is a map `X : ℝ → V`; only its values on `[0, 1]` are constrained (values off
`[0, 1]` are arbitrary). Piecewise smooth: continuous on `[0, 1]` and `C^∞` (`ContDiffOn`) on each
closed piece of some subdivision `0 = t₀ < ⋯ < t_k = 1` (its own subdivision, not necessarily
that of `c`). Tangent: `X t ∈ T_{c(t)}N` for `t ∈ [0, 1]`, the tangent space defined from scratch
as the span of the velocities `γ'(0)` of smooth curves `γ : (−ε, ε) → N` through the point (if
`c t ∉ N` this is `{0}`). `T` is the `Submodule.span` of this set of fields; the set is already a
linear subspace (common refinement of subdivisions), so the span adds nothing — it only spares
proving closure here. No requirement that `c ∈ Ω` (textbook hypothesis). -/
namespace RoundTrip.L2.Morse_pathTangent

open scoped ContDiff
open Set

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `v` is the velocity `γ'(0)` of a smooth curve `γ : (−ε, ε) → N` with `γ(0) = q`. -/
def IsVelocity (N : Set V) (q v : V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V, ContDiffOn ℝ ∞ γ (Ioo (-ε) ε) ∧
    MapsTo γ (Ioo (-ε) ε) N ∧ γ 0 = q ∧ HasDerivAt γ v 0

/-- The tangent space `T_qN ⊆ V` (span of the velocities at `q`). -/
def tangentSpace (N : Set V) (q : V) : Submodule ℝ V :=
  Submodule.span ℝ {v | IsVelocity N q v}

/-- `X` is piecewise smooth on `[a, b]`. -/
def IsPiecewiseSmooth (X : ℝ → V) (a b : ℝ) : Prop :=
  ContinuousOn X (Icc a b) ∧
    ∃ k : ℕ, ∃ t : Fin (k + 1) → ℝ, StrictMono t ∧ t 0 = a ∧ t (Fin.last k) = b ∧
      ∀ i : Fin k, ContDiffOn ℝ ∞ X (Icc (t i.castSucc) (t i.succ))

end

/-- The textbook notion: `TΩ_c`, piecewise smooth fields along `c`, tangent to `N`, vanishing at
`0` and `1`. -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {N : Set V} (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    (c : ℝ → V) : Submodule ℝ (ℝ → V) :=
  Submodule.span ℝ
    {X | IsPiecewiseSmooth X 0 1 ∧ (∀ t ∈ Icc (0 : ℝ) 1, X t ∈ tangentSpace N (c t)) ∧
      X 0 = 0 ∧ X 1 = 0}

end RoundTrip.L2.Morse_pathTangent
