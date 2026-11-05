import Morse
/-! Blind formalization of V1_13 (Milnor §2, pp. 9-10: 1-parameter groups of diffeomorphisms). Choices:
- Setting: smooth Hausdorff finite-dim manifold `M` on `E`; vector field = section `X : Π x, TangentSpace x` smooth as a map
  into the tangent bundle.
- 1-parameter group: `φ : ℝ → M → M`, `(t,x) ↦ φ t x` C^∞, each `φ t` a diffeomorphism (`Diffeomorph`, as a function),
  `φ (s+t) = φ s ∘ φ t`.
- Claim: (i) there is a smooth vector field `X` with `X_q(g) = lim_{h→0} (g(φ_h q) - g q)/h` for all smooth `g`
  (`X_q(g) = mfderiv g q (X q)`; limit over `h ≠ 0`); (ii) for any `X` generating `φ` in this sense, each orbit
  `t ↦ φ t q` is an integral curve of `X` (Mathlib `IsMIntegralCurve`: `d/dt φ_t(q) = X_{φ_t q}`) and `φ 0 q = q`. -/
open scoped ContDiff Manifold Topology
namespace RoundTrip.V1_13

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (φ : ℝ → M → M),
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun z : ℝ × M => φ z.1 z.2) →
    (∀ t, ∃ ψ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ⇑ψ = φ t) →
    (∀ s t x, φ (s + t) x = φ s (φ t x)) →
    (∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun x : M => (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g → ∀ q : M,
        Filter.Tendsto (fun h : ℝ => (g (φ h q) - g q) / h) (𝓝[≠] 0)
          (𝓝 (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) g q (X q)))) ∧
    (∀ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      (∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g → ∀ q : M,
        Filter.Tendsto (fun h : ℝ => (g (φ h q) - g q) / h) (𝓝[≠] 0)
          (𝓝 (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) g q (X q)))) →
      ∀ q, IsMIntegralCurve (fun t => φ t q) X ∧ φ 0 q = q)

end RoundTrip.V1_13
