import Morse
/-! Blind formalization of V6_3 (Milnor §8, pp. 43-44: affine connections on an abstract manifold). Choices:
- Abstract smooth manifold `M : Type` modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)` (`C^∞`, `IsManifold 𝓘(ℝ,ℝⁿ) ∞`, without boundary; Hausdorff/second countable are not needed for these local statements and are not assumed).
  Tangent space at `p`: Mathlib's `TangentSpace 𝓘(ℝ,ℝⁿ) p`. A vector field is a section `p ↦ X p ∈ T_pM`; it is smooth if `p ↦ (p, X p)` is a `C^∞` map `M → TM` (`IsSmoothVF`).
  Directional derivative `X_p f = mfderiv f p (X p)` (`dirDeriv`).
- Connection: Mathlib's `CovariantDerivative 𝓘(ℝ,ℝⁿ) ℝⁿ (TangentSpace 𝓘(ℝ,ℝⁿ))` with the smoothness condition `ContMDiffCovariantDerivativeOn ℝⁿ ∞ cov Set.univ` (`IsGlobalConn`);
  Milnor's `X ⊢ Y` is `p ↦ cov Y p (X p)` (`nab`; note Mathlib's argument order: the section first, the tangent vector at the point second).
- Milnor's rules (1)-(4) (`IsMilnorRules`) for an operation `D` on smooth fields: (1) `D X Y` smooth for smooth `X, Y`; (2) `ℝ`-bilinear (additive and homogeneous in each slot); (3) `D (fX) Y = f D X Y`;
  (4) `D X (fY) = (Xf) Y + f D X Y`, for smooth `f`.
- Definition item. A global affine connection is `cov` as above (`IsGlobalConn`). B asserts what Milnor states about it: (i) at every point `p` the rule `(X_p, Y) ↦ X_p ⊢ Y = cov Y p X_p` (on smooth `Y`) is additive in `Y`
  and satisfies the Leibniz rule `X_p ⊢ (fY) = (X_p f) Y_p + f(p) X_p ⊢ Y` (bilinearity in `X_p` is built into `cov Y p` being linear); (ii) a global connection satisfies (1)-(4); (iii) conversely, any operation on smooth fields
  satisfying (1)-(4) is the `⊢` of a global connection (agreeing on smooth fields), i.e. (1)-(4) may serve as the definition. -/
namespace RoundTrip.V6_3
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

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M],
    (∀ cov : CovariantDerivative 𝓘(ℝ, Rn n) (Rn n) (TangentSpace 𝓘(ℝ, Rn n) : M → Type), IsGlobalConn cov →
      (∀ (p : M) (Xp : TangentSpace 𝓘(ℝ, Rn n) p) (Y Y' : (q : M) → TangentSpace 𝓘(ℝ, Rn n) q) (f : M → ℝ),
        IsSmoothVF Y → IsSmoothVF Y' → ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ f →
        cov (fun q => Y q + Y' q) p Xp = cov Y p Xp + cov Y' p Xp ∧
        cov (fun q => f q • Y q) p Xp = dirDeriv (fun _ => Xp) f p • Y p + f p • cov Y p Xp) ∧
      IsMilnorRules (nab cov)) ∧
    (∀ D : ((p : M) → TangentSpace 𝓘(ℝ, Rn n) p) → ((p : M) → TangentSpace 𝓘(ℝ, Rn n) p) →
        ((p : M) → TangentSpace 𝓘(ℝ, Rn n) p), IsMilnorRules D →
      ∃ cov : CovariantDerivative 𝓘(ℝ, Rn n) (Rn n) (TangentSpace 𝓘(ℝ, Rn n) : M → Type), IsGlobalConn cov ∧
        ∀ X Y, IsSmoothVF X → IsSmoothVF Y → nab cov X Y = D X Y)
end RoundTrip.V6_3
