import Morse
/-! Blind formalization of V6_4 (Milnor §8, p. 44: rules (1)-(4) and Christoffel symbols). Choices:
- Abstract smooth manifold `M : Type` modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)` (`C^∞`, `IsManifold 𝓘(ℝ,ℝⁿ) ∞`, without boundary; Hausdorff/second countable are not needed for these local statements and are not assumed).
  Tangent space at `p`: Mathlib's `TangentSpace 𝓘(ℝ,ℝⁿ) p`. A vector field is a section `p ↦ X p ∈ T_pM`; it is smooth if `p ↦ (p, X p)` is a `C^∞` map `M → TM` (`IsSmoothVF`).
  Directional derivative `X_p f = mfderiv f p (X p)` (`dirDeriv`).
- Connection: Mathlib's `CovariantDerivative 𝓘(ℝ,ℝⁿ) ℝⁿ (TangentSpace 𝓘(ℝ,ℝⁿ))` with the smoothness condition `ContMDiffCovariantDerivativeOn ℝⁿ ∞ cov Set.univ` (`IsGlobalConn`);
  Milnor's `X ⊢ Y` is `p ↦ cov Y p (X p)` (`nab`; note Mathlib's argument order: the section first, the tangent vector at the point second).
- Milnor's rules (1)-(4) (`IsMilnorRules`) for an operation `D` on smooth fields: (1) `D X Y` smooth for smooth `X, Y`; (2) `ℝ`-bilinear (additive and homogeneous in each slot); (3) `D (fX) Y = f D X Y`;
  (4) `D X (fY) = (Xf) Y + f D X Y`, for smooth `f`.
- Local coordinates: a chart `e` of the maximal smooth atlas (`IsManifold.maximalAtlas 𝓘(ℝ,ℝⁿ) ∞ M`), coordinates `u = e(p)`. Components of a tangent vector `ξ ∈ T_pM` in `e`: `(mfderiv e p ξ) i`; coordinate fields `∂_i`
  are not formed (they are only local); instead the statement "determined by the Christoffel symbols `Γ^k_ij`, `∂_i ⊢ ∂_j = Σ_k Γ^k_ij ∂_k`" is expressed by the coordinate formula for all global smooth `X, Y`:
  `(X ⊢ Y)^k = Σ_i X^i ∂_i Y^k + Σ_{i,j} Γ^k_ij X^i Y^j` at every point of the chart domain, for some functions `Γ^k_ij` smooth on the chart image `e.target`.
- B: for every global connection: (a) rules (1)-(4); (b) in every chart such Christoffel symbols exist. -/
namespace RoundTrip.V6_4
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

/-- Components `(ξ^i)` of a tangent vector `ξ ∈ T_pM` in the chart `e`. -/
noncomputable def comp {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
    (e : OpenPartialHomeomorph M (Rn n)) (p : M) (ξ : TangentSpace 𝓘(ℝ, Rn n) p) (k : Fin n) : ℝ :=
  (show Rn n from mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (e : M → Rn n) p ξ) k

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
    (cov : CovariantDerivative 𝓘(ℝ, Rn n) (Rn n) (TangentSpace 𝓘(ℝ, Rn n) : M → Type)), IsGlobalConn cov →
    IsMilnorRules (nab cov) ∧
    ∀ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Rn n) ∞ M,
      ∃ Γ : Rn n → Fin n → Fin n → Fin n → ℝ,
        (∀ k i j, ContDiffOn ℝ ∞ (fun u => Γ u k i j) e.target) ∧
        ∀ (X Y : (p : M) → TangentSpace 𝓘(ℝ, Rn n) p), IsSmoothVF X → IsSmoothVF Y →
          ∀ p ∈ e.source, ∀ k : Fin n,
            comp e p (nab cov X Y p) k =
              ∑ i, comp e p (X p) i *
                fderiv ℝ (fun u => comp e (e.symm u) (Y (e.symm u)) k) (e p) (EuclideanSpace.single i 1) +
              ∑ i, ∑ j, Γ (e p) k i j * comp e p (X p) i * comp e p (Y p) j
end RoundTrip.V6_4
