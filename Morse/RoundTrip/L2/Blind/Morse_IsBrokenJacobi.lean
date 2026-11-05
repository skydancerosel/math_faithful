import Morse
/-! Layer-2 blind definition of Morse_IsBrokenJacobi. Textbook:
Milnor, *Morse Theory*, §15, pp. 83–85: given a subdivision
`0 = t₀ < t₁ < … < t_k` of the parameter interval, a broken Jacobi field along `γ` is a continuous
piecewise smooth vector field along `γ` whose restriction to each `[t_{i-1}, t_i]` is a Jacobi
field along `γ|[t_{i-1}, t_i]`. In the proof of the index theorem it is used along
`γ_τ = γ|[0, τ]` (`0 < τ ≤ 1`) with the subdivision of `[0, τ]` by the `t_i < τ` and `τ`.
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
Reading of the arguments: `B` = the subdivision points, `τ` = the right end of the parameter
interval `[0, τ]`; the subdivision of `[0, τ]` is `{0, τ} ∪ {t ∈ B | 0 < t < τ}` (points of `B`
outside `(0, τ)`, e.g. `0, 1`, are ignored). `X` must be continuous on `[0, τ]` and a Jacobi
field along `γ` on each closed segment `[u, v]` between consecutive subdivision points
(derivatives within `[u, v]`, so one-sided at the breaks); it is NOT required to vanish at `0`
or `τ` (that is condition (2) of Milnor's space `TΩ(t₀, …, t_k)`, not part of "broken Jacobi").
Values off `[0, τ]` are free. Outside the textbook hypotheses (`τ ∉ (0, 1]`, `γ` not a geodesic)
the same formula is used. `hc` is unused. -/
namespace RoundTrip.L2.Morse_IsBrokenJacobi

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

/-- The subdivision of `[0, τ]` determined by `B`. -/
def pts (B : Finset ℝ) (τ : ℝ) : Set ℝ := {0, τ} ∪ {t | t ∈ B ∧ 0 < t ∧ t < τ}

/-- The textbook notion: `X` is a broken Jacobi field along `γ|[0, τ]` for the subdivision `B`. -/
def T {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {N : Set V}
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (γ : ℝ → V)
    (_hc : Morse.IsSmoothCurveIn hN γ) (B : Finset ℝ) (τ : ℝ) (X : ℝ → V) : Prop :=
  ContinuousOn X (Set.Icc 0 τ) ∧
    ∀ u ∈ pts B τ, ∀ v ∈ pts B τ, u < v → (∀ w ∈ pts B τ, w ∉ Set.Ioo u v) →
      IsJacobiOn N γ (Set.Icc u v) X

end RoundTrip.L2.Morse_IsBrokenJacobi
