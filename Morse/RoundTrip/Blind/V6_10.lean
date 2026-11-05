import Morse
/-! Blind formalization of V6_10 (Milnor §8, Lemma 8.3). Choices:
- Abstract smooth manifold `M : Type` modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)` (`C^∞`, `IsManifold 𝓘(ℝ,ℝⁿ) ∞`, without boundary), tangent space `TangentSpace 𝓘(ℝ,ℝⁿ) p`, smooth vector fields (`IsSmoothVF`), smooth curves `c : ℝ → M`,
  fields `V : (t : ℝ) → TangentSpace 𝓘(ℝ,ℝⁿ) (c t)` along `c` (`IsSmoothAlong`: `t ↦ (c t, V t)` is a `C^∞` map to `TM`), velocity `mfderiv c t 1`.
- Connection: Mathlib's `CovariantDerivative 𝓘(ℝ,ℝⁿ) ℝⁿ (TangentSpace 𝓘(ℝ,ℝⁿ))` with `ContMDiffCovariantDerivativeOn ℝⁿ ∞ cov Set.univ` (`IsGlobalConn`); `X ⊢ Y = p ↦ cov Y p (X p)`.
  Covariant derivative `D` along `c`: operation on fields along `c` with Milnor's axioms (a), (b), (c) (`IsCovDerivAlong`); parallel field: smooth with `DV/dt = 0` (`IsParallel`).
- Riemannian metric: Mathlib's `Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,ℝⁿ) x)`, smooth (`IsContMDiffRiemannianBundle 𝓘(ℝ,ℝⁿ) ∞ ℝⁿ _`); `⟨·,·⟩` = `inner ℝ` on the fibre `T_pM`.
- B: for a global connection compatible with the metric (`IsCompatibleMetric`), every smooth curve `c`, every covariant-derivative operation `D` along `c` (`IsCovDerivAlong`) and smooth fields `V, W` along `c`:
  `t ↦ ⟨V_t, W_t⟩` is differentiable with derivative `⟨DV/dt, W⟩ + ⟨V, DW/dt⟩` at every `t` (`HasDerivAt`). The parallel-frame proof is not part of B. -/
namespace RoundTrip.V6_10
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

open Bundle

section Conn
open Bundle
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]

/-- A smooth (`C^∞`) vector field `X` on `M`: a section of the tangent bundle, smooth as a map `M → TM`. -/
def IsSmoothVF (X : (p : M) → TangentSpace 𝓘(ℝ, Rn n) p) : Prop :=
  ContMDiff 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent ∞ (fun p => (⟨p, X p⟩ : TangentBundle 𝓘(ℝ, Rn n) M))

/-- The directional derivative `X f` of a real function `f` along a vector field `X`: `p ↦ X_p f = df_p(X_p)`. -/
noncomputable def dirDeriv (X : (p : M) → TangentSpace 𝓘(ℝ, Rn n) p) (f : M → ℝ) (p : M) : ℝ :=
  mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ) f p (X p)

/-- Milnor's rules (1)-(4) for an operation `(X, Y) ↦ X ⊢ Y` on smooth vector fields. -/
def IsMilnorRules (D : ((p : M) → TangentSpace 𝓘(ℝ, Rn n) p) → ((p : M) → TangentSpace 𝓘(ℝ, Rn n) p) →
    ((p : M) → TangentSpace 𝓘(ℝ, Rn n) p)) : Prop :=
  (∀ X Y, IsSmoothVF X → IsSmoothVF Y → IsSmoothVF (D X Y)) ∧
  (∀ X X' Y, IsSmoothVF X → IsSmoothVF X' → IsSmoothVF Y → D (fun p => X p + X' p) Y = fun p => D X Y p + D X' Y p) ∧
  (∀ (a : ℝ) X Y, IsSmoothVF X → IsSmoothVF Y → D (fun p => a • X p) Y = fun p => a • D X Y p) ∧
  (∀ X Y Y', IsSmoothVF X → IsSmoothVF Y → IsSmoothVF Y' → D X (fun p => Y p + Y' p) = fun p => D X Y p + D X Y' p) ∧
  (∀ (a : ℝ) X Y, IsSmoothVF X → IsSmoothVF Y → D X (fun p => a • Y p) = fun p => a • D X Y p) ∧
  (∀ (f : M → ℝ) X Y, ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ f → IsSmoothVF X → IsSmoothVF Y →
      D (fun p => f p • X p) Y = fun p => f p • D X Y p) ∧
  (∀ (f : M → ℝ) X Y, ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ f → IsSmoothVF X → IsSmoothVF Y →
      D X (fun p => f p • Y p) = fun p => dirDeriv X f p • Y p + f p • D X Y p)

/-- A global affine connection: Mathlib's covariant derivative on the tangent bundle whose `∇_X Y` is smooth
for smooth `X`, `Y` (Milnor's smoothness condition (1)). `X ⊢ Y` is `p ↦ cov Y p (X p)`. -/
def IsGlobalConn (cov : CovariantDerivative 𝓘(ℝ, Rn n) (Rn n) (TangentSpace 𝓘(ℝ, Rn n) : M → Type)) : Prop :=
  ContMDiffCovariantDerivativeOn (Rn n) ∞ cov.toFun Set.univ

/-- `X ⊢ Y` for a connection `cov`. -/
noncomputable def nab (cov : CovariantDerivative 𝓘(ℝ, Rn n) (Rn n) (TangentSpace 𝓘(ℝ, Rn n) : M → Type))
    (X Y : (p : M) → TangentSpace 𝓘(ℝ, Rn n) p) : (p : M) → TangentSpace 𝓘(ℝ, Rn n) p :=
  fun p => cov Y p (X p)
end Conn

section Curve
open Bundle
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]

/-- A smooth parametrized curve `c : ℝ → M`. -/
def IsSmoothCurve (c : ℝ → M) : Prop := ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) ∞ c

/-- A vector field along `c`: to each `t` a tangent vector `V_t ∈ T_{c(t)}M`. -/
abbrev FieldAlong (c : ℝ → M) := (t : ℝ) → TangentSpace 𝓘(ℝ, Rn n) (c t)

/-- `V` is a smooth vector field along `c`: `t ↦ (c t, V t)` is a `C^∞` map `ℝ → TM`. -/
def IsSmoothAlong (c : ℝ → M) (V : FieldAlong (n := n) c) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, Rn n)).tangent ∞ (fun t => (⟨c t, V t⟩ : TangentBundle 𝓘(ℝ, Rn n) M))

/-- The velocity field `dc/dt = c_*(d/dt)`. -/
noncomputable def velocity (c : ℝ → M) (t : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (c t) :=
  mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c t (1 : ℝ)

/-- Milnor's axioms (a), (b), (c) for an operation `D : V ↦ DV/dt` on vector fields along `c`
(with the requirement that `D` takes smooth fields along `c` to smooth fields along `c`). -/
def IsCovDerivAlong (cov : CovariantDerivative 𝓘(ℝ, Rn n) (Rn n) (TangentSpace 𝓘(ℝ, Rn n) : M → Type))
    (c : ℝ → M) (D : FieldAlong (n := n) c → FieldAlong (n := n) c) : Prop :=
  (∀ V, IsSmoothAlong c V → IsSmoothAlong c (D V)) ∧
  (∀ V W, IsSmoothAlong c V → IsSmoothAlong c W → D (fun t => V t + W t) = fun t => D V t + D W t) ∧
  (∀ (f : ℝ → ℝ), ContDiff ℝ ∞ f → ∀ V, IsSmoothAlong c V →
      D (fun t => f t • V t) = fun t => deriv f t • V t + f t • D V t) ∧
  (∀ Y : (p : M) → TangentSpace 𝓘(ℝ, Rn n) p, IsSmoothVF Y →
      D (fun t => Y (c t)) = fun t => cov Y (c t) (velocity c t))

/-- A parallel field along `c`: a smooth field with `DV/dt = 0` identically. -/
def IsParallel (cov : CovariantDerivative 𝓘(ℝ, Rn n) (Rn n) (TangentSpace 𝓘(ℝ, Rn n) : M → Type))
    (c : ℝ → M) (V : FieldAlong (n := n) c) : Prop :=
  IsSmoothAlong c V ∧ ∃ D, IsCovDerivAlong cov c D ∧ D V = fun _ => 0
end Curve

section Compat
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- Milnor's compatibility with the metric: parallel translation preserves inner products, i.e. `⟨P, P'⟩` is
constant along every smooth curve `c` for any two parallel fields `P`, `P'` along `c`. -/
def IsCompatibleMetric (cov : CovariantDerivative 𝓘(ℝ, Rn n) (Rn n) (TangentSpace 𝓘(ℝ, Rn n) : M → Type)) : Prop :=
  ∀ c : ℝ → M, IsSmoothCurve (n := n) c → ∀ P P' : FieldAlong (n := n) c, IsParallel cov c P → IsParallel cov c P' →
    ∃ r : ℝ, ∀ t, inner ℝ (P t) (P' t) = r
end Compat

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]
    (cov : CovariantDerivative 𝓘(ℝ, Rn n) (Rn n) (TangentSpace 𝓘(ℝ, Rn n) : M → Type)), IsGlobalConn cov →
    IsCompatibleMetric cov →
    ∀ c : ℝ → M, IsSmoothCurve (n := n) c → ∀ D, IsCovDerivAlong cov c D →
      ∀ V W : FieldAlong (n := n) c, IsSmoothAlong (n := n) c V → IsSmoothAlong (n := n) c W → ∀ t : ℝ,
        HasDerivAt (fun s => inner ℝ (V s) (W s)) (inner ℝ (D V t) (W t) + inner ℝ (V t) (D W t)) t
end RoundTrip.V6_10
