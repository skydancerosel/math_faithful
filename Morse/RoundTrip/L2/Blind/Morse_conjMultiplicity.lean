import Morse
/-! Layer-2 blind definition of Morse_conjMultiplicity. Textbook:
Milnor, *Morse Theory*, §14, p. 77: the multiplicity of the conjugate points `γ(a)`, `γ(b)` is the
dimension of the vector space of Jacobi fields along `γ` vanishing at `t = a` and `t = b`.
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
Jacobi fields on the whole domain `[0,1]` of `γ` (same as on `[a, b]` for a geodesic, by unique
extension). The space is encoded by the restrictions `J|[0,1] : Icc 0 1 → V` (so values off
`[0,1]` do not create spurious dimensions); its dimension is `Module.finrank` of the SPAN of
this set (under the textbook hypotheses the set is already a subspace, the Jacobi equation being
linear; the span avoids proving linearity of `D/dt` without the setting). Values: `finrank` is
`0` if the span were infinite-dimensional (it is `≤ 2·dim N` under the hypotheses). Outside the
textbook hypotheses (`a = b`, or `a`/`b` not conjugate, or off `[0,1]`): the same formula, where
a condition `J a = 0` with `a ∉ [0,1]` constrains nothing on `[0,1]`. `_hc` is unused. -/
namespace RoundTrip.L2.Morse_conjMultiplicity

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

/-- The textbook notion: the dimension of the space of Jacobi fields along `γ` vanishing at
`a` and `b`. -/
noncomputable def T {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {N : Set V}
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (γ : ℝ → V)
    (_hc : Morse.IsSmoothCurveIn hN γ) (a b : ℝ) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ {K : Set.Icc (0 : ℝ) 1 → V | ∃ J : ℝ → V,
    IsJacobiOn N γ (Set.Icc 0 1) J ∧ J a = 0 ∧ J b = 0 ∧ K = fun t => J t.1})

end RoundTrip.L2.Morse_conjMultiplicity
