import Morse
/-! Layer-2 blind definition of Morse_IsMinimalGeodesic. Textbook: Milnor, *Morse Theory*, §10,
p. 61-62: a geodesic segment `γ : [a, b] → N` is minimal if its length `∫_a^b ‖γ'(t)‖ dt` is
`≤` the length of every piecewise smooth path in `N` with the same end points (i.e. equals the
Riemannian distance `ρ(γ(a), γ(b))`).
Choices: `hN` (`N` a smooth slice submanifold of `V`) is the setting and is not used. Tangent
spaces from scratch (span of velocities of smooth curves in `N`). Geodesic on `[a, b]` (induced
metric): `C^∞` on `[a, b]`, values in `N`, acceleration (derivatives within `[a,b]`) orthogonal
to `T_{γ(t)}N`. Comparison paths: piecewise smooth paths `c` in `N` parametrised by `[0, 1]`
(continuous, `c([0,1]) ⊆ N`, `C^∞` on the closed pieces of a subdivision) with `c(0) = γ(a)`,
`c(1) = γ(b)`; lengths `∫⁻ ‖·'‖` in `ℝ≥0∞`. The textbook has `a < b`; for `a = b` the constant
segment is minimal iff `γ(a) ∈ N`, and for `b < a` (empty interval, length `0`) `T` holds. -/
namespace RoundTrip.L2.Morse_IsMinimalGeodesic

open scoped ContDiff
open MeasureTheory Set

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `v` is the velocity `c'(0)` of a smooth curve `c : (−ε, ε) → N` with `c(0) = q`. -/
def IsVelocity (N : Set V) (q v : V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ → V, ContDiffOn ℝ ∞ c (Ioo (-ε) ε) ∧
    MapsTo c (Ioo (-ε) ε) N ∧ c 0 = q ∧ HasDerivAt c v 0

/-- The tangent space `T_qN ⊆ V` (span of the velocities at `q`). -/
def tangentSpace (N : Set V) (q : V) : Submodule ℝ V :=
  Submodule.span ℝ {v | IsVelocity N q v}

/-- `γ` is a geodesic of `N` on `s`: `C^∞` on `s`, `γ(s) ⊆ N`, and the acceleration `γ''(t)` is
orthogonal to `T_{γ(t)}N` for `t ∈ s` (derivatives within `s`). -/
def IsGeo (N : Set V) (γ : ℝ → V) (s : Set ℝ) : Prop :=
  ContDiffOn ℝ ∞ γ s ∧ MapsTo γ s N ∧
    ∀ t ∈ s, ∀ w ∈ tangentSpace N (γ t), inner ℝ (derivWithin (derivWithin γ s) s t) w = 0

/-- `γ` is a geodesic of `N` on `[0, 1]` with `γ(0) = q`, `γ'(0) = v` (right derivative). -/
def IsGeoFrom (N : Set V) (q v : V) (γ : ℝ → V) : Prop :=
  IsGeo N γ (Icc 0 1) ∧ γ 0 = q ∧ HasDerivWithinAt γ v (Icc 0 1) 0

/-- `c` is a piecewise smooth path in `N`, parametrised by `[a, b]`. -/
def IsPSPath (N : Set V) (c : ℝ → V) (a b : ℝ) : Prop :=
  ContinuousOn c (Icc a b) ∧ MapsTo c (Icc a b) N ∧
    ∃ (k : ℕ) (τ : Fin (k + 1) → ℝ), τ 0 = a ∧ τ (Fin.last k) = b ∧ StrictMono τ ∧
      ∀ i : Fin k, ContDiffOn ℝ ∞ c (Icc (τ i.castSucc) (τ i.succ))

/-- Arc length `∫_a^b ‖c'(t)‖ dt` (in `ℝ≥0∞`). -/
noncomputable def len (c : ℝ → V) (a b : ℝ) : ENNReal :=
  ∫⁻ t in Icc a b, ENNReal.ofReal ‖deriv c t‖

end

/-- The textbook notion: `γ` is a geodesic on `[a, b]` no longer than any piecewise smooth path
in `N` with the same end points. -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {N : Set V} (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    (γ : ℝ → V) (a b : ℝ) : Prop :=
  IsGeo N γ (Icc a b) ∧
    ∀ c : ℝ → V, IsPSPath N c 0 1 → c 0 = γ a → c 1 = γ b → len γ a b ≤ len c 0 1

end RoundTrip.L2.Morse_IsMinimalGeodesic
