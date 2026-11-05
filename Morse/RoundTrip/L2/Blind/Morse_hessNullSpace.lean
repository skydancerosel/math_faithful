import Morse
/-! Layer-2 blind definition of Morse_hessNullSpace. Textbook:
Milnor, *Morse Theory*, §14, p. 77 (with §13): the null space of
the Hessian `E_**` at a geodesic `γ`: all `W₁ ∈ TΩ_γ` with `E_**(W₁, W₂) = 0` for every
`W₂ ∈ TΩ_γ`.
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
`TΩ_γ` (from scratch): fields `W : ℝ → V` piecewise smooth on `[0,1]` (`C^∞` on each closed
piece of a finite subdivision), `W t ∈ T_{γ(t)}N` for `t ∈ [0,1]`, `W 0 = W 1 = 0`; the values off
`[0,1]` are left free (a field along `γ : [0,1] → M` is encoded by any extension to `ℝ`).
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
The result is the null space as a set of functions `ℝ → V` (image of the kernel under the
inclusion `TΩ_γ ⊆ (ℝ → V)`); since `E_**` only sees `[0,1]`, it contains, with each `W₁`, all
its modifications off `[0,1]` that stay in `TΩ_γ`. `hγ` is unused. -/
namespace RoundTrip.L2.Morse_hessNullSpace

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

/-- Piecewise smooth on `[0,1]`: `C^∞` on every closed subinterval of `[0,1]` whose interior avoids
a finite break set `S` (⇔ smooth on each piece of a subdivision `0 = t₀ < … < t_k = 1`). -/
def IsPWS (X : ℝ → V) : Prop :=
  ∃ S : Finset ℝ, ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → (∀ s ∈ S, s ∉ Set.Ioo a b) →
    ContDiffOn ℝ ∞ X (Set.Icc a b)

/-- The tangent space `TΩ_γ`: piecewise smooth fields `W` along `γ` (`W t ∈ T_{γ(t)}N` on
`[0,1]`) vanishing at `t = 0, 1`; values off `[0,1]` are free. -/
def TOm (N : Set V) (γ : ℝ → V) : Submodule ℝ (ℝ → V) where
  carrier := {X | IsPWS X ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, X t ∈ tan N (γ t)) ∧ X 0 = 0 ∧ X 1 = 0}
  add_mem' := by
    rintro X Y ⟨⟨S₁, h₁⟩, t₁, a₁, b₁⟩ ⟨⟨S₂, h₂⟩, t₂, a₂, b₂⟩
    refine ⟨⟨S₁ ∪ S₂, fun a b ha hab hb hS => ?_⟩, fun t ht => ?_, ?_, ?_⟩
    · exact (h₁ a b ha hab hb fun s hs => hS s (Finset.mem_union_left _ hs)).add
        (h₂ a b ha hab hb fun s hs => hS s (Finset.mem_union_right _ hs))
    · exact Submodule.add_mem _ (t₁ t ht) (t₂ t ht)
    · simp [a₁, a₂]
    · simp [b₁, b₂]
  zero_mem' := ⟨⟨∅, fun _ _ _ _ _ _ => contDiffOn_const⟩, fun _ _ => Submodule.zero_mem _,
    rfl, rfl⟩
  smul_mem' := by
    rintro c X ⟨⟨S, h⟩, t₁, a₁, b₁⟩
    refine ⟨⟨S, fun a b ha hab hb hS => (h a b ha hab hb hS).const_smul c⟩,
      fun t ht => Submodule.smul_mem _ c (t₁ t ht), ?_, ?_⟩
    · simp [a₁]
    · simp [b₁]

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

/-- The Hessian `E_**` on `TΩ_γ`. -/
noncomputable def Ess (N : Set V) (γ : ℝ → V) : LinearMap.BilinForm ℝ (TOm N γ) :=
  bilinOf fun W₁ W₂ => hessVal N γ W₁ W₂

/-- The textbook notion: the null space of `E_**` at `γ`. -/
noncomputable def T {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {N : Set V}
    (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) {γ : ℝ → V} {p q : V}
    (_hγ : γ ∈ Morse.pathSpace N p q) : Submodule ℝ (ℝ → V) :=
  Submodule.map (TOm N γ).subtype (LinearMap.ker (Ess N γ))

end RoundTrip.L2.Morse_hessNullSpace
