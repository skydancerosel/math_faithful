import Morse
/-! Layer-2 blind definition of Morse_energyHessian. Textbook:
Milnor, *Morse Theory*, §13, pp. 74–76 (Theorem 13.1): the Hessian `E_**` of the energy
`E(ω) = ∫₀¹ ‖dω/dt‖² dt` at a geodesic `γ ∈ Ω(M; p, q)`, a symmetric bilinear form on `TΩ_γ`.
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
`E_**`: Milnor defines `E_**(W₁, W₂) = ∂²E(α(u₁,u₂))/∂u₁∂u₂ (0,0)` for a 2-parameter
variation `α` with variation fields `W₁, W₂`, at a geodesic `γ`; Theorem 13.1 computes it:
`½E_** = −Σ_t ⟨W₂, Δ_t DW₁/dt⟩ − ∫₀¹ ⟨W₂, D²W₁/dt² + R(V,W₁)V⟩`, which, integrating by parts
(`W₂(0) = W₂(1) = 0`), is `∫₀¹ (⟨DW₁/dt, DW₂/dt⟩ − ⟨R(V,W₁)V, W₂⟩) dt`. We DEFINE `E_**` by this
formula, with MILNOR'S NORMALISATION `E = ∫‖dω/dt‖²` (no ½), hence the factor `2`:
`E_**(W₁,W₂) = 2∫₀¹ (⟨P(W₁'), P(W₂')⟩ − ⟨R(γ', W₁)γ', W₂⟩)`, derivatives `deriv` (the finitely
many break points and `0, 1` are null sets). It is evaluated for any `γ` (no geodesic hypothesis;
outside it there is no textbook value). The result is packaged as a bilinear form by `bilinOf`:
the formula when it is bilinear on the domain (true under the textbook hypotheses: piecewise
smooth fields along a smooth `γ` in `N`), else `0`.
`TΩ_γ` is the setting's `Morse.pathTangent hN γ` (it is the result type; used as is). `hγ`
(`γ ∈ Ω`) is unused. -/
namespace RoundTrip.L2.Morse_energyHessian

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

/-- Milnor's `E_**(W₁, W₂)` (second variation formula 13.1, integrated by parts):
`2 ∫₀¹ (⟨DW₁/dt, DW₂/dt⟩ − ⟨R(V, W₁)V, W₂⟩) dt`, `V = dγ/dt`, `DW/dt = P_{γ(t)}(dW/dt)`. -/
noncomputable def hessVal (N : Set V) (γ W₁ W₂ : ℝ → V) : ℝ :=
  2 * ∫ t in (0 : ℝ)..1,
    (inner ℝ (P N (γ t) (deriv W₁ t)) (P N (γ t) (deriv W₂ t)) -
      inner ℝ (R N (γ t) (deriv γ t) (W₁ t) (deriv γ t)) (W₂ t))

/-- The bilinear form with values `f` when `f` is bilinear (the case under the textbook
hypotheses), `0` otherwise. -/
noncomputable def bilinOf {M : Type*} [AddCommGroup M] [Module ℝ M] (f : M → M → ℝ) :
    LinearMap.BilinForm ℝ M :=
  open Classical in
  if h : (∀ x x' y, f (x + x') y = f x y + f x' y) ∧ (∀ (c : ℝ) x y, f (c • x) y = c • f x y) ∧
      (∀ x y y', f x (y + y') = f x y + f x y') ∧ (∀ (c : ℝ) x y, f x (c • y) = c • f x y) then
    LinearMap.mk₂ ℝ f h.1 h.2.1 h.2.2.1 h.2.2.2
  else 0

/-- The textbook notion: Milnor's `E_**` at `γ` on `TΩ_γ`. -/
noncomputable def T {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {N : Set V}
    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) {γ : ℝ → V} {p q : V}
    (_hγ : γ ∈ Morse.pathSpace N p q) : LinearMap.BilinForm ℝ ↥(Morse.pathTangent hN γ) :=
  bilinOf fun W₁ W₂ => hessVal N γ W₁ W₂

end RoundTrip.L2.Morse_energyHessian
