import Morse
/-! Blind formalization of V6_20 (Milnor §9, Lemma 9.3 (1)-(3)). Choices:
- Setting (all items): `M : Type` an abstract smooth (`C^∞`) Hausdorff manifold without boundary modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)` (`IsManifold 𝓘(ℝ,ℝⁿ) ∞ M`),
  with a smooth Riemannian metric: Mathlib's `Bundle.RiemannianBundle (fun x => TangentSpace 𝓘(ℝ,ℝⁿ) x)` + `IsContMDiffRiemannianBundle`; `⟨·,·⟩ = inner ℝ`, `‖·‖` the fibre norm. Vector fields are sections `p ↦ X p ∈ T_pM`, smooth iff `p ↦ (p, X p) ∈ TM` is `C^∞`.
- Connections: Mathlib's `CovariantDerivative`, `X ⊢ Y = p ↦ cov Y p (X p)`, required `C^∞` (`IsGlobalConn`). `D/dt` along a curve `c` on an interval `s`: Milnor's axioms (a),(b),(c) (p. 46) for an operation `D` on smooth fields along `c`
  (derivatives within `s`); `DV/dt = W` means `∃ D` with these axioms and `D V = W` on `s` (`HasCovDeriv`); parallel = `DV/dt = 0`. Symmetric (`IsSymm`): `X ⊢ Y - Y ⊢ X = [X,Y]` (Mathlib `VectorField.mlieBracket`). Compatible (`IsCompat`): parallel transport preserves inner products (⟨P,P'⟩ constant for parallel P,P'). Levi-Civita: smooth, symmetric, compatible (`IsLC`).
- Intervals: `IsIntv s` = order-connected with `UniqueDiffOn` (nondegenerate interval, any type of endpoints); geodesic `IsGeodesic cov c s`: `c` smooth on `s` and the velocity field `dc/dt` (derivative within `s`) has `D/dt = 0`.
- B: for the Levi-Civita connection of a Riemannian manifold, all smooth fields `X,Y,Z,W` and all points `p`: (1) `R(X,Y)Z + R(Y,X)Z = 0`; (2) `R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0`; (3) `⟨R(X,Y)Z,W⟩ + ⟨R(X,Y)W,Z⟩ = 0`. (The reduction to vanishing brackets is proof content.) -/
namespace RoundTrip.V6_20

open scoped ContDiff Manifold unitInterval
open Bundle

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

section Prelude
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]

/-- Vector fields on `M`: sections `p ↦ X p ∈ T_pM` of the tangent bundle (no regularity). -/
abbrev VF (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Rn n) M] := (p : M) → TangentSpace 𝓘(ℝ, Rn n) p

/-- Smooth (`C^∞`) vector field: `p ↦ (p, X p)` is a `C^∞` map `M → TM`. -/
def IsSmoothVF (X : VF n M) : Prop :=
  ContMDiff 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent ∞ (fun p => (⟨p, X p⟩ : TangentBundle 𝓘(ℝ, Rn n) M))

/-- Affine connections: Mathlib's covariant derivative on the tangent bundle; `X ⊢ Y = p ↦ cov Y p (X p)`. -/
abbrev Conn (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M] :=
  CovariantDerivative 𝓘(ℝ, Rn n) (Rn n) (TangentSpace 𝓘(ℝ, Rn n) : M → Type)

/-- A (`C^∞`) connection: the covariant derivative is smooth. -/
def IsGlobalConn (cov : Conn n M) : Prop :=
  ContMDiffCovariantDerivativeOn (Rn n) ∞ cov.toFun Set.univ

/-- Milnor's definition 8.5: `X ⊢ Y - Y ⊢ X = [X, Y]` for smooth fields. -/
def IsSymm (cov : Conn n M) : Prop :=
  ∀ X Y : VF n M, IsSmoothVF X → IsSmoothVF Y → ∀ p : M,
    cov Y p (X p) - cov X p (Y p) = VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y p

/-- A (nondegenerate) interval of `ℝ`. -/
def IsIntv (s : Set ℝ) : Prop := s.OrdConnected ∧ UniqueDiffOn ℝ s

/-- Vector field along `c`. -/
abbrev FA (n : ℕ) {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] (c : ℝ → M) := (t : ℝ) → TangentSpace 𝓘(ℝ, Rn n) (c t)

/-- `V` is smooth along `c` on `s`: `t ↦ (c t, V t) ∈ TM` is `C^∞` on `s`. -/
def IsSmoothAlong (c : ℝ → M) (s : Set ℝ) (V : FA n c) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, Rn n)).tangent ∞ (fun t => (⟨c t, V t⟩ : TangentBundle 𝓘(ℝ, Rn n) M)) s

/-- Velocity `dc/dt` (derivative within `s`). -/
noncomputable def vel (c : ℝ → M) (s : Set ℝ) (t : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (c t) :=
  mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c s t (1 : ℝ)

/-- Milnor's axioms (a), (b), (c) (p. 46) for `D : V ↦ DV/dt` on fields along `c`, on the interval `s`. -/
def IsCovDerivAlong (cov : Conn n M) (c : ℝ → M) (s : Set ℝ) (D : FA n c → FA n c) : Prop :=
  (∀ V W, IsSmoothAlong c s V → IsSmoothAlong c s W → ∀ t ∈ s, D (fun t => V t + W t) t = D V t + D W t) ∧
  (∀ f : ℝ → ℝ, ContDiffOn ℝ ∞ f s → ∀ V, IsSmoothAlong c s V → ∀ t ∈ s,
      D (fun t => f t • V t) t = derivWithin f s t • V t + f t • D V t) ∧
  (∀ Y : VF n M, IsSmoothVF Y → ∀ t ∈ s, D (fun t => Y (c t)) t = cov Y (c t) (vel c s t))

/-- `W = DV/dt` on `s`: `V` smooth along `c` and `W` is `D V` for a covariant-derivative operation `D`. -/
def HasCovDeriv (cov : Conn n M) (c : ℝ → M) (s : Set ℝ) (V W : FA n c) : Prop :=
  IsSmoothAlong c s V ∧ ∃ D, IsCovDerivAlong cov c s D ∧ ∀ t ∈ s, D V t = W t

/-- Parallel field along `c` on `s`: smooth with `DV/dt = 0`. -/
def IsParallel (cov : Conn n M) (c : ℝ → M) (s : Set ℝ) (V : FA n c) : Prop :=
  HasCovDeriv cov c s V (fun _ => 0)

/-- Smooth curve on the interval `s`. -/
def IsSmoothCurve (c : ℝ → M) (s : Set ℝ) : Prop := ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) ∞ c s

variable [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- Compatibility with the metric (Milnor p. 47): parallel translation preserves inner products,
i.e. `⟨P, P'⟩` is constant along any smooth curve for parallel fields `P, P'`. -/
def IsCompat (cov : Conn n M) : Prop :=
  ∀ (s : Set ℝ), IsIntv s → ∀ c : ℝ → M, IsSmoothCurve (n := n) c s → ∀ P P' : FA n c,
    IsParallel cov c s P → IsParallel cov c s P' → ∀ t ∈ s, ∀ t' ∈ s, inner ℝ (P t) (P' t) = inner ℝ (P t') (P' t')

/-- The Levi-Civita connection: smooth, symmetric and compatible with the metric. -/
def IsLC (cov : Conn n M) : Prop := IsGlobalConn cov ∧ IsSymm cov ∧ IsCompat cov

/-- Geodesic on an interval `s` (Milnor p. 55): smooth `c` with `D/dt (dc/dt) = 0`. -/
def IsGeodesic (cov : Conn n M) (c : ℝ → M) (s : Set ℝ) : Prop :=
  IsIntv s ∧ IsSmoothCurve (n := n) c s ∧ IsSmoothAlong c s (vel (n := n) c s) ∧ HasCovDeriv cov c s (vel (n := n) c s) (fun _ => 0)
end Prelude

section Curv
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]

/-- Milnor's curvature (p. 51): `R(X,Y)Z = -X ⊢ (Y ⊢ Z) + Y ⊢ (X ⊢ Z) + [X,Y] ⊢ Z`. -/
noncomputable def curv (cov : Conn n M) (X Y Z : VF n M) : VF n M := fun x =>
  -(cov (fun y => cov Z y (Y y)) x (X x)) + cov (fun y => cov Z y (X y)) x (Y x)
    + cov Z x (VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y x)

/-- Nomizu's curvature: `∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z`. -/
noncomputable def nomizuCurv (cov : Conn n M) (X Y Z : VF n M) : VF n M := fun x =>
  cov (fun y => cov Z y (Y y)) x (X x) - cov (fun y => cov Z y (X y)) x (Y x)
    - cov Z x (VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y x)
end Curv

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)], ∀ cov : Conn n M, IsLC cov →
    ∀ X Y Z W : VF n M, IsSmoothVF X → IsSmoothVF Y → IsSmoothVF Z → IsSmoothVF W → ∀ p : M,
      curv cov X Y Z p + curv cov Y X Z p = 0 ∧
      curv cov X Y Z p + curv cov Y Z X p + curv cov Z X Y p = 0 ∧
      inner ℝ (curv cov X Y Z p) (W p) + inner ℝ (curv cov X Y W p) (Z p) = 0
end RoundTrip.V6_20
