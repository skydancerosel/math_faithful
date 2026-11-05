import Morse
/-! Layer-2 blind definition of Morse_IsConjugate. Textbook:
Milnor, *Morse Theory*, §14, p. 77: for a geodesic `γ` and `a ≠ b`, `γ(a)` and `γ(b)` are conjugate
along `γ` if some Jacobi field along `γ`, not identically zero, vanishes at `t = a` and `t = b`.
Choices:
Setting and from-scratch geometry: `N ⊆ V` is a smooth submanifold of the Euclidean space `V`
(`hN`, opaque, unused) with the induced metric. `T_xN` = span of the velocities `c'(0)` of smooth
curves `c` in `N` with `c(0) = x` (`⊥` for `x ∉ N`); `P_x` = orthogonal projection of `V` onto it;
covariant derivative along a curve `DX/dt = P_{γ(t)}(dX/dt)` (Milnor §8); second fundamental form
`II_x(v, w) = (1 − P_x)((dP_x v) w)`, `dP_x` the derivative within `N` (`fderivWithin`) of
`y ↦ P_y` (for tangent `v, w` the normal part of `D_v W`, `W(y) = P_y w`); curvature in MILNOR'S
SIGN (`⟨R(X,Y)X, Y⟩` = sectional curvature, `> 0` on spheres), by the Gauss equation
`⟨R(X,Y)Z, U⟩ = ⟨II(X,Z), II(Y,U)⟩ − ⟨II(Y,Z), II(X,U)⟩` (`U ∈ T_xN`), i.e.
`R(X,Y)Z = P_x(II(Y,·)*(II(X,Z)) − II(X,·)*(II(Y,Z)))` (adjoints in `V`). Only tangent first
arguments of `II` occur, so the non-unique (normal-direction) part of `fderivWithin` is
irrelevant.
Jacobi fields: `γ` is a path on `[0,1]` (Milnor's geodesics in `Ω` are parametrised by
`[0,1]`); a Jacobi field along `γ|[u,v]` is a `J : ℝ → V` that on `[u,v]` is `C^∞`, tangent
(`J t ∈ T_{γ(t)}N`) and satisfies `D²J/dt² + R(V, J)V = 0`, `V = dγ/dt`, all derivatives being
`derivWithin` on `[u,v]` (one-sided at the ends); values of `J` off `[u,v]` are unconstrained.
That `γ` is a geodesic (textbook hypothesis) is not part of the predicate.
Jacobi fields are taken on the whole domain `[0,1]` of `γ`, and `a, b` must lie in `[0,1]` (for a
geodesic, a Jacobi field on `[min a b, max a b]` extends uniquely to `[0,1]`, and it is zero on
one interval iff on the other, so this is the same as using `γ|[a,b]`). `a ≠ b` and
`a, b ∈ [0,1]` are made conjuncts (value `False` otherwise). "Not identically zero" = nonzero at
some `t ∈ [0,1]`. -/
namespace RoundTrip.L2.Morse_IsConjugate

open scoped ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `v` is the velocity `c'(0)` of a smooth curve `c : (−ε, ε) → N` with `c(0) = x`. -/
def IsVelocity (N : Set V) (x v : V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ → V, ContDiffOn ℝ ∞ c (Set.Ioo (-ε) ε) ∧
    Set.MapsTo c (Set.Ioo (-ε) ε) N ∧ c 0 = x ∧ HasDerivAt c v 0

/-- The tangent space `T_xN ⊆ V`: span of the velocities at `x` (`⊥` for `x ∉ N`). -/
def tan (N : Set V) (x : V) : Submodule ℝ V :=
  Submodule.span ℝ {v | IsVelocity N x v}

variable [FiniteDimensional ℝ V]

/-- The orthogonal projection `P_x` of `V` onto `T_xN`. -/
noncomputable def P (N : Set V) (x : V) : V →L[ℝ] V := (tan N x).starProjection

/-- Second fundamental form `II_x(v, w) = (1 − P_x)((dP_x v) w)`, `dP_x` the derivative within
`N` of `y ↦ P_y`. -/
noncomputable def II (N : Set V) (x : V) : V →L[ℝ] V →L[ℝ] V :=
  (ContinuousLinearMap.compL ℝ V V V (1 - P N x)).comp (fderivWithin ℝ (P N) N x)

/-- Milnor's curvature tensor `R_x(X, Y)Z ∈ T_xN` (Gauss equation, Milnor's sign):
`⟨R(X,Y)Z, U⟩ = ⟨II(X,Z), II(Y,U)⟩ − ⟨II(Y,Z), II(X,U)⟩` for `U ∈ T_xN`. -/
noncomputable def R (N : Set V) (x X Y Z : V) : V :=
  P N x (ContinuousLinearMap.adjoint (II N x Y) (II N x X Z) -
    ContinuousLinearMap.adjoint (II N x X) (II N x Y Z))

/-- Covariant derivative along `γ` on the interval `s`: `DX/dt = P_{γ(t)}(dX/dt)`. -/
noncomputable def covD (N : Set V) (s : Set ℝ) (γ X : ℝ → V) (t : ℝ) : V :=
  P N (γ t) (derivWithin X s t)

/-- `J` is a Jacobi field along `γ|s`: smooth on `s`, tangent to `N` along `γ`, and
`D²J/dt² + R(V, J)V = 0` on `s`, where `V = dγ/dt` (derivatives within `s`). -/
def IsJacobiOn (N : Set V) (γ : ℝ → V) (s : Set ℝ) (J : ℝ → V) : Prop :=
  ContDiffOn ℝ ∞ J s ∧ (∀ t ∈ s, J t ∈ tan N (γ t)) ∧
    ∀ t ∈ s, covD N s γ (covD N s γ J) t +
      R N (γ t) (derivWithin γ s t) (J t) (derivWithin γ s t) = 0

/-- The textbook notion: `γ(a)` and `γ(b)` are conjugate along `γ`. -/
def T {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (γ : ℝ → V)
    (a b : ℝ) : Prop :=
  a ≠ b ∧ a ∈ Set.Icc (0 : ℝ) 1 ∧ b ∈ Set.Icc (0 : ℝ) 1 ∧
    ∃ J : ℝ → V, IsJacobiOn N γ (Set.Icc 0 1) J ∧ J a = 0 ∧ J b = 0 ∧
      ∃ t ∈ Set.Icc (0 : ℝ) 1, J t ≠ 0

end RoundTrip.L2.Morse_IsConjugate
