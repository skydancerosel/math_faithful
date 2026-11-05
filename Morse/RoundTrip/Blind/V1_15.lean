import Morse
/-! Blind formalization of V1_15 (Milnor Lemma 2.4). Choices:
- Setting: smooth (C^∞) finite-dimensional real manifold `M`, Hausdorff; smooth vector field = section
  `X : Π x, TangentSpace 𝓘(ℝ,E) x` with `x ↦ ⟨x, X x⟩` `ContMDiff` into the tangent bundle.
- "vanishes outside compact K": ∃ compact K, ∀ x ∉ K, X x = 0.
- 1-parameter group of diffeomorphisms: `φ : ℝ → M → M`, `(t,x) ↦ φ t x` smooth on ℝ×M, φ 0 = id,
  φ (s+t) = φ s ∘ φ t (each φ t is then a diffeomorphism with inverse φ (-t)).
- "X generates φ" in Milnor's sense: for every smooth g : M → ℝ and q, d/dt g(φ_t q)|_{t=0} = dg_q(X_q)
  (i.e. X_q(g)).  "exactly one": `∃!` over such φ. -/
open scoped ContDiff Manifold
namespace RoundTrip.V1_15

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (X : (x : M) → TangentSpace 𝓘(ℝ, E) x),
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun x : M => (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) →
    (∃ K : Set M, IsCompact K ∧ ∀ x, x ∉ K → X x = 0) →
    ∃! φ : ℝ → M → M,
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun z : ℝ × M => φ z.1 z.2) ∧
      (∀ x, φ 0 x = x) ∧ (∀ s t x, φ (s + t) x = φ s (φ t x)) ∧
      (∀ (g : M → ℝ), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g → ∀ q : M,
        deriv (fun t : ℝ => g (φ t q)) 0 = mfderiv 𝓘(ℝ, E) 𝓘(ℝ) g q (X q))

end RoundTrip.V1_15
