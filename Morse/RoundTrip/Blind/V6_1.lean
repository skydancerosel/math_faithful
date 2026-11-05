import Morse
/-! Blind formalization of V6_1 (Milnor §8, pp. 43-44: tangent spaces, the projection P_q, vector fields). Choices:
- Abstract smooth manifold `M : Type` modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)` (`C^∞`, `IsManifold 𝓘(ℝ,ℝⁿ) ∞`, without boundary; Hausdorff/second countable are not needed for these local statements and are not assumed).
  Tangent space at `p`: Mathlib's `TangentSpace 𝓘(ℝ,ℝⁿ) p`. A vector field is a section `p ↦ X p ∈ T_pM`; it is smooth if `p ↦ (p, X p)` is a `C^∞` map `M → TM` (`IsSmoothVF`).
  Directional derivative `X_p f = mfderiv f p (X p)` (`dirDeriv`).
- Definition-type item. B asserts the basic properties Milnor uses: smooth vector fields are closed under sum, real scalar multiple and multiplication by smooth functions; the directional derivative `X f` of a smooth
  function along a smooth field is smooth; `X_p` is linear and a derivation: `X_p(f+g) = X_p f + X_p g`, `X_p(fg) = (X_p f) g(p) + f(p) X_p g`.
- `P_q` (Milnor's projection of `ℝⁿ` onto `TM_q` for `M ⊆ ℝⁿ`): for `M` a slice submanifold of `ℝ^{K+1}` (project's `Milnor.IsSliceSubmanifold`, tangent space `Milnor.Tub.tanN`), `P_q` = orthogonal projection onto `T_qM` (`Submodule.starProjection`);
  asserted: `P_q v ∈ T_qM` and `v - P_q v ⊥ T_qM`. -/
namespace RoundTrip.V6_1
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
  (∀ (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M],
    (∀ (X X' : (p : M) → TangentSpace 𝓘(ℝ, Rn n) p) (a : ℝ) (f : M → ℝ), IsSmoothVF X → IsSmoothVF X' →
      ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ f →
      IsSmoothVF (fun p => X p + X' p) ∧ IsSmoothVF (fun p => a • X p) ∧ IsSmoothVF (fun p => f p • X p) ∧
      ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ (dirDeriv X f)) ∧
    (∀ (X : (p : M) → TangentSpace 𝓘(ℝ, Rn n) p) (f g : M → ℝ) (p : M),
      ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ f → ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ g →
      dirDeriv X (fun q => f q + g q) p = dirDeriv X f p + dirDeriv X g p ∧
      dirDeriv X (fun q => f q * g q) p = dirDeriv X f p * g p + f p * dirDeriv X g p)) ∧
  ∀ (K d m : ℕ) (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M) (q : M) (v : Rn (K + 1)),
    (Milnor.Tub.tanN hM q).starProjection v ∈ Milnor.Tub.tanN hM q ∧
    v - (Milnor.Tub.tanN hM q).starProjection v ∈ (Milnor.Tub.tanN hM q)ᗮ
end RoundTrip.V6_1
