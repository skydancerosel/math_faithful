import Morse
/-! Layer-2 blind definition of Morse_conjLocus. Textbook: Milnor, *Morse Theory*, §14 (p. 70,
Jacobi fields and conjugate points), §15 p. 77, §19 p. 99: the conjugate locus of `p` is the set
of points `q` conjugate to `p` along some geodesic `γ` from `p` to `q`; `q = γ(1)` is conjugate to
`p = γ(0)` along `γ` if some Jacobi field `J` along `γ`, not identically zero, vanishes at
`t = 0` and `t = 1`. A Jacobi field is a smooth vector field along `γ` with
`D²J/dt² + R(V, J)V = 0`, `V = dγ/dt`, `R` in Milnor's sign convention
(`⟨R(X,Y)X, Y⟩` = sectional curvature).
Choices: `hN` (`N` a smooth slice submanifold of `V`) is the setting and is not used. All for
`N ⊆ V` with the induced metric. Tangent spaces from scratch (span of velocities of smooth curves
in `N`); `P_x` = orthogonal projection onto `T_xN` (`starProjection`; `0` off `N`). Geodesics:
`C^∞` on `[0,1]`, values in `N`, acceleration orthogonal to `T_{γ(t)}N` (all geodesics from `p`,
parametrised by `[0, 1]`, affine reparametrisation changing nothing). Covariant derivative of a
field `Y` along `γ`: `DY/dt = P_{γ(t)}(Y'(t))` (derivatives within `[0,1]`). Second fundamental
form `II_x(a, b) = (1 − P_x)((dP_x a) b)`, `dP_x` the derivative within `N` of `x ↦ P_x` (Gauss
formula for the tangent field `y ↦ P_y b`). Curvature by the Gauss equation, Milnor's sign:
`⟨R(X,Y)Z, U⟩ = ⟨II(X,Z), II(Y,U)⟩ − ⟨II(Y,Z), II(X,U)⟩`; the Jacobi equation (whose terms are
tangent) is imposed by pairing with every `U ∈ T_{γ(t)}N`:
`⟨D²J, U⟩ + ⟨II(V,V), II(J,U)⟩ − ⟨II(J,V), II(V,U)⟩ = 0`. `J` is `C^∞` on `[0,1]` and tangent to
`N` along `γ`; "non-trivial" = `J(t) ≠ 0` for some `t ∈ [0,1]`. `p ∉ N` gives `∅`. -/
namespace RoundTrip.L2.Morse_conjLocus

open scoped ContDiff
open Set

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

variable [FiniteDimensional ℝ V]

/-- The orthogonal projection `P_x` onto `T_xN`. -/
noncomputable def P (N : Set V) (x : V) : V →L[ℝ] V :=
  (tangentSpace N x).starProjection

/-- Second fundamental form `II_x(a, b) = (1 − P_x)((dP_x a) b)`. -/
noncomputable def II (N : Set V) (x a b : V) : V :=
  fderivWithin ℝ (P N) N x a b - P N x (fderivWithin ℝ (P N) N x a b)

/-- Velocity `γ'(t)` (within `[0, 1]`). -/
noncomputable def vel (γ : ℝ → V) (t : ℝ) : V :=
  derivWithin γ (Icc 0 1) t

/-- Covariant derivative `DY/dt = P_{γ(t)}(Y'(t))` of a field `Y` along `γ`. -/
noncomputable def covD (N : Set V) (γ Y : ℝ → V) (t : ℝ) : V :=
  P N (γ t) (derivWithin Y (Icc 0 1) t)

/-- `J` is a Jacobi field along `γ` on `[0, 1]`: `D²J/dt² + R(V, J)V = 0` (Milnor's sign),
the curvature term given by the Gauss equation. -/
def IsJacobi (N : Set V) (γ J : ℝ → V) : Prop :=
  ContDiffOn ℝ ∞ J (Icc 0 1) ∧ (∀ t ∈ Icc (0 : ℝ) 1, J t ∈ tangentSpace N (γ t)) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ tangentSpace N (γ t),
      inner ℝ (covD N γ (covD N γ J) t) u
        + inner ℝ (II N (γ t) (vel γ t) (vel γ t)) (II N (γ t) (J t) u)
        - inner ℝ (II N (γ t) (J t) (vel γ t)) (II N (γ t) (vel γ t) u) = 0

end

/-- The textbook notion: the points `q = γ(1)` conjugate to `p = γ(0)` along some geodesic `γ`. -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {N : Set V} (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    (p : V) : Set V :=
  {q | ∃ γ : ℝ → V, IsGeo N γ (Icc 0 1) ∧ γ 0 = p ∧ γ 1 = q ∧
    ∃ J : ℝ → V, IsJacobi N γ J ∧ J 0 = 0 ∧ J 1 = 0 ∧ ∃ t ∈ Icc (0 : ℝ) 1, J t ≠ 0}

end RoundTrip.L2.Morse_conjLocus
