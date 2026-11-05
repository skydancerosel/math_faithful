import Morse
/-! Blind formalization of V6_6 (Milnor §8, Lemma 8.1). Choices:
- Abstract smooth manifold `M : Type` modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)` (`C^∞`, `IsManifold 𝓘(ℝ,ℝⁿ) ∞`, without boundary; Hausdorff/second countable are not needed for these local statements and are not assumed).
  Tangent space at `p`: Mathlib's `TangentSpace 𝓘(ℝ,ℝⁿ) p`. A vector field is a section `p ↦ X p ∈ T_pM`; it is smooth if `p ↦ (p, X p)` is a `C^∞` map `M → TM` (`IsSmoothVF`).
  Directional derivative `X_p f = mfderiv f p (X p)` (`dirDeriv`).
- Connection: Mathlib's `CovariantDerivative 𝓘(ℝ,ℝⁿ) ℝⁿ (TangentSpace 𝓘(ℝ,ℝⁿ))` with the smoothness condition `ContMDiffCovariantDerivativeOn ℝⁿ ∞ cov Set.univ` (`IsGlobalConn`);
  Milnor's `X ⊢ Y` is `p ↦ cov Y p (X p)` (`nab`; note Mathlib's argument order: the section first, the tangent vector at the point second).
- Milnor's rules (1)-(4) (`IsMilnorRules`) for an operation `D` on smooth fields: (1) `D X Y` smooth for smooth `X, Y`; (2) `ℝ`-bilinear (additive and homogeneous in each slot); (3) `D (fX) Y = f D X Y`;
  (4) `D X (fY) = (Xf) Y + f D X Y`, for smooth `f`.
- Curves `c : ℝ → M` are smooth (`C^∞`, `IsSmoothCurve`; Milnor's interval is all of `ℝ`). A vector field along `c`: `V : (t : ℝ) → TangentSpace 𝓘(ℝ,ℝⁿ) (c t)`, smooth iff `t ↦ (c t, V t) ∈ TM` is `C^∞` (`IsSmoothAlong`).
  Velocity `dc/dt = mfderiv c t 1` (`velocity`).
- Covariant derivative along `c`: an operation `D` on fields along `c` satisfying Milnor's axioms (a) additivity, (b) `D(fV)/dt = (df/dt)V + f DV/dt` for smooth `f : ℝ → ℝ`, (c) for `V_t = Y_{c(t)}` induced by a smooth vector field `Y`,
  `DV/dt = ∇_{c'(t)} Y` (here `cov Y (c t) (velocity c t)`), all for smooth fields; plus that `D` carries smooth fields to smooth fields (`IsCovDerivAlong`). The connection is as in V6_3 (`IsGlobalConn`).
- B: for every global connection and smooth curve `c`, there is exactly one operation `V ↦ DV/dt` satisfying (a), (b), (c): existence (`∃ D, IsCovDerivAlong cov c D`) and uniqueness on smooth fields
  (any other such `D'` agrees with `D` on every smooth field along `c`; values of `D'` on non-smooth fields are unconstrained). The coordinate formula in the proof is not part of B. -/
namespace RoundTrip.V6_6
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

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

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
    (cov : CovariantDerivative 𝓘(ℝ, Rn n) (Rn n) (TangentSpace 𝓘(ℝ, Rn n) : M → Type)), IsGlobalConn cov →
    ∀ c : ℝ → M, IsSmoothCurve (n := n) c →
      ∃ D, IsCovDerivAlong cov c D ∧
        ∀ D', IsCovDerivAlong cov c D' → ∀ V, IsSmoothAlong (n := n) c V → D' V = D V
end RoundTrip.V6_6
