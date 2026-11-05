import Morse
/-! Blind formalization of V7_4 (Milnor §10, Theorem 10.1). Choices:
- Setting (all items): `M : Type` an abstract smooth (`C^∞`) Hausdorff manifold without boundary modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)` (`IsManifold 𝓘(ℝ,ℝⁿ) ∞ M`),
  with a smooth Riemannian metric: Mathlib's `Bundle.RiemannianBundle (fun x => TangentSpace 𝓘(ℝ,ℝⁿ) x)` + `IsContMDiffRiemannianBundle`; `⟨·,·⟩ = inner ℝ`, `‖·‖` the fibre norm. Vector fields are sections `p ↦ X p ∈ T_pM`, smooth iff `p ↦ (p, X p) ∈ TM` is `C^∞`.
- Connections: Mathlib's `CovariantDerivative`, `X ⊢ Y = p ↦ cov Y p (X p)`, required `C^∞` (`IsGlobalConn`). `D/dt` along a curve `c` on an interval `s`: Milnor's axioms (a),(b),(c) (p. 46) for an operation `D` on smooth fields along `c`
  (derivatives within `s`); `DV/dt = W` means `∃ D` with these axioms and `D V = W` on `s` (`HasCovDeriv`); parallel = `DV/dt = 0`. Symmetric (`IsSymm`): `X ⊢ Y - Y ⊢ X = [X,Y]` (Mathlib `VectorField.mlieBracket`). Compatible (`IsCompat`): parallel transport preserves inner products (⟨P,P'⟩ constant for parallel P,P'). Levi-Civita: smooth, symmetric, compatible (`IsLC`).
- Intervals: `IsIntv s` = order-connected with `UniqueDiffOn` (nondegenerate interval, any type of endpoints); geodesic `IsGeodesic cov c s`: `c` smooth on `s` and the velocity field `dc/dt` (derivative within `s`) has `D/dt = 0`.
- Pure ODE statement (no manifold): `U ⊆ ℝⁿ × ℝⁿ` open (functions "defined near" `(u₁,v₁)`), `F : ℝⁿ×ℝⁿ → ℝⁿ` `C^∞` on `U`. `ℝⁿ = EuclideanSpace ℝ (Fin n)`.
- `IsODESol U F ε u₀ v₀ u`: `u(0)=u₀`, `u'(0)=v₀`, and for `|t| < ε`, `u` is differentiable, `(u,u') ∈ U`, `u'` has derivative `F(u,u')` (so `u'' = F(u,u')`).
- B: there are a neighbourhood `W` of `(u₁,v₁)`, `ε > 0` and a family `sol (u₀,v₀)` such that for `(u₀,v₀) ∈ W` `sol` is a solution on `(-ε,ε)`, any solution on `(-ε,ε)` with the same data agrees with it (uniqueness), and `(u₀,v₀,t) ↦ sol (u₀,v₀) t` is `C^∞` on `W × (-ε,ε)`. The first-order reduction is proof content. -/
namespace RoundTrip.V7_4

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

/-- `u` solves `u'' = F(u, u')` on `(-ε, ε)` with `u(0) = u₀`, `u'(0) = v₀`, staying in `U`. -/
def IsODESol {n : ℕ} (U : Set (Rn n × Rn n)) (F : Rn n × Rn n → Rn n) (ε : ℝ) (u₀ v₀ : Rn n) (u : ℝ → Rn n) : Prop :=
  u 0 = u₀ ∧ deriv u 0 = v₀ ∧ ∀ t ∈ Set.Ioo (-ε) ε, DifferentiableAt ℝ u t ∧ (u t, deriv u t) ∈ U ∧
    HasDerivAt (deriv u) (F (u t, deriv u t)) t

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (U : Set (Rn n × Rn n)) (F : Rn n × Rn n → Rn n), IsOpen U → ContDiffOn ℝ ∞ F U →
    ∀ z₁ ∈ U, ∃ W ∈ nhds z₁, ∃ ε > 0, ∃ sol : Rn n × Rn n → ℝ → Rn n,
      ContDiffOn ℝ ∞ (fun q : (Rn n × Rn n) × ℝ => sol q.1 q.2) (W ×ˢ Set.Ioo (-ε) ε) ∧
      ∀ z ∈ W, IsODESol U F ε z.1 z.2 (sol z) ∧
        ∀ u : ℝ → Rn n, IsODESol U F ε z.1 z.2 u → Set.EqOn u (sol z) (Set.Ioo (-ε) ε)
end RoundTrip.V7_4
