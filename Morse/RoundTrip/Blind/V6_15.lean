import Morse
/-! Blind formalization of V6_15 (Milnor §8, Lemma 8.7). Choices:
- Setting (all items): `M : Type` an abstract smooth (`C^∞`) Hausdorff manifold without boundary modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)` (`IsManifold 𝓘(ℝ,ℝⁿ) ∞ M`),
  with a smooth Riemannian metric: Mathlib's `Bundle.RiemannianBundle (fun x => TangentSpace 𝓘(ℝ,ℝⁿ) x)` + `IsContMDiffRiemannianBundle`; `⟨·,·⟩ = inner ℝ`, `‖·‖` the fibre norm. Vector fields are sections `p ↦ X p ∈ T_pM`, smooth iff `p ↦ (p, X p) ∈ TM` is `C^∞`.
- Connections: Mathlib's `CovariantDerivative`, `X ⊢ Y = p ↦ cov Y p (X p)`, required `C^∞` (`IsGlobalConn`). `D/dt` along a curve `c` on an interval `s`: Milnor's axioms (a),(b),(c) (p. 46) for an operation `D` on smooth fields along `c`
  (derivatives within `s`); `DV/dt = W` means `∃ D` with these axioms and `D V = W` on `s` (`HasCovDeriv`); parallel = `DV/dt = 0`. Symmetric (`IsSymm`): `X ⊢ Y - Y ⊢ X = [X,Y]` (Mathlib `VectorField.mlieBracket`). Compatible (`IsCompat`): parallel transport preserves inner products (⟨P,P'⟩ constant for parallel P,P'). Levi-Civita: smooth, symmetric, compatible (`IsLC`).
- Intervals: `IsIntv s` = order-connected with `UniqueDiffOn` (nondegenerate interval, any type of endpoints); geodesic `IsGeodesic cov c s`: `c` smooth on `s` and the velocity field `dc/dt` (derivative within `s`) has `D/dt = 0`.
- Surface `s : ℝ × ℝ → M` smooth (`𝓘(ℝ, ℝ×ℝ)`), `∂s/∂x = ds(1,0)`, `∂s/∂y = ds(0,1)`. `DV/∂x` at `(x₀,y₀)` is the covariant derivative of `x ↦ V(x,y₀)` along `x ↦ s(x,y₀)` (on all of ℝ; `CovDerivAt`).
- B: for a smooth symmetric connection, `D/∂x (∂s/∂y)` and `D/∂y (∂s/∂x)` exist at each `(x₀,y₀)` and are equal (`∃ u` satisfying both). -/
namespace RoundTrip.V6_15

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

section Surf
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]

/-- `∂s/∂x = s_*(∂/∂x)` of a parametrized surface `s : ℝ² → M`. -/
noncomputable def sx (s : ℝ × ℝ → M) (p : ℝ × ℝ) : TangentSpace 𝓘(ℝ, Rn n) (s p) :=
  mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Rn n) s p ((1 : ℝ), (0 : ℝ))

/-- `∂s/∂y = s_*(∂/∂y)`. -/
noncomputable def sy (s : ℝ × ℝ → M) (p : ℝ × ℝ) : TangentSpace 𝓘(ℝ, Rn n) (s p) :=
  mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Rn n) s p ((0 : ℝ), (1 : ℝ))

/-- `DV/dt = w` at the time `t₀` along the curve `c` (on all of `ℝ`). -/
def CovDerivAt (cov : Conn n M) (c : ℝ → M) (V : FA n c) (t₀ : ℝ) (w : TangentSpace 𝓘(ℝ, Rn n) (c t₀)) : Prop :=
  ∃ W : FA n c, HasCovDeriv cov c Set.univ V W ∧ W t₀ = w

/-- `V` is a smooth vector field along the surface `s`. -/
def IsSmoothSurfField (s : ℝ × ℝ → M) (V : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, Rn n) (s p)) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, Rn n)).tangent ∞ (fun p => (⟨s p, V p⟩ : TangentBundle 𝓘(ℝ, Rn n) M))

/-- `A = DV/∂x` along `s`: for each `y`, the covariant derivative along `x ↦ s(x,y)`. -/
def IsDx (cov : Conn n M) (s : ℝ × ℝ → M) (V A : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, Rn n) (s p)) : Prop :=
  ∀ x y : ℝ, HasCovDeriv cov (fun x' => s (x', y)) Set.univ (fun x' => V (x', y)) (fun x' => A (x', y))

/-- `A = DV/∂y` along `s`. -/
def IsDy (cov : Conn n M) (s : ℝ × ℝ → M) (V A : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, Rn n) (s p)) : Prop :=
  ∀ x y : ℝ, HasCovDeriv cov (fun y' => s (x, y')) Set.univ (fun y' => V (x, y')) (fun y' => A (x, y'))
end Surf

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)], ∀ cov : Conn n M, IsGlobalConn cov → IsSymm cov →
    ∀ s : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Rn n) ∞ s → ∀ x₀ y₀ : ℝ,
      ∃ u : TangentSpace 𝓘(ℝ, Rn n) (s (x₀, y₀)),
        CovDerivAt cov (fun x => s (x, y₀)) (fun x => sy s (x, y₀)) x₀ u ∧
        CovDerivAt cov (fun y => s (x₀, y)) (fun y => sx s (x₀, y)) y₀ u
end RoundTrip.V6_15
