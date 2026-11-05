import Morse
/-! Blind formalization of V1_14 (Milnor §2, pp. 10-11, proof of Lemma 2.4: global flows). Choices:
- Setting: smooth Hausdorff finite-dim manifold, smooth vector field `X` (section smooth into tangent bundle);
  solution of `dφ_t(q)/dt = X_{φ_t(q)}` = Mathlib `IsMIntegralCurve(On)`.
- B₁ (quoted well-known fact, Graves): for every `q` there is a nbhd `U`, `ε > 0` and a map `ψ`, jointly smooth on
  `(-ε,ε) × U`, with `ψ(0,x) = x` and `t ↦ ψ(t,x)` an integral curve on `(-ε,ε)` for `x ∈ U`; and solutions are locally unique
  (two integral curves on a common interval around 0 with the same initial point agree there).
- B₂ (covering by finitely many neighbourhoods): if `X` vanishes outside a compact `K`, there is `ε₀ > 0` and `ψ` jointly
  smooth on `(-ε₀, ε₀) × M` with these properties for all `x ∈ M`.
- B₃ (iteration): for such `X` there is a global `φ : ℝ → M → M` with (t,x) ↦ φ t x smooth, `φ 0 = id`, `φ(t+s) = φ t ∘ φ s`,
  integral curves of `X`, extending `ψ` on `|t| < ε₀`... (extension to ψ is not asserted; only that φ is well defined, smooth,
  a group, integral).
- B = B₁ ∧ B₂ ∧ B₃. -/
open scoped ContDiff Manifold
namespace RoundTrip.V1_14

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (X : (x : M) → TangentSpace 𝓘(ℝ, E) x),
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun x : M => (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) →
    (∀ q : M, ∃ U ∈ nhds q, ∃ ε : ℝ, 0 < ε ∧ ∃ ψ : ℝ × M → M,
        ContMDiffOn (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ ψ (Set.Ioo (-ε) ε ×ˢ U) ∧
        ∀ x ∈ U, ψ (0, x) = x ∧ IsMIntegralCurveOn (fun t => ψ (t, x)) X (Set.Ioo (-ε) ε)) ∧
    (∀ (x : M) (γ₁ γ₂ : ℝ → M) (s : Set ℝ), Set.OrdConnected s → (0 : ℝ) ∈ s →
        IsMIntegralCurveOn γ₁ X s → IsMIntegralCurveOn γ₂ X s → γ₁ 0 = x → γ₂ 0 = x →
        ∀ t ∈ s, γ₁ t = γ₂ t) ∧
    ((∃ K : Set M, IsCompact K ∧ ∀ x, x ∉ K → X x = 0) →
      (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ ψ : ℝ × M → M,
        ContMDiffOn (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ ψ (Set.Ioo (-ε₀) ε₀ ×ˢ Set.univ) ∧
        ∀ x : M, ψ (0, x) = x ∧ IsMIntegralCurveOn (fun t => ψ (t, x)) X (Set.Ioo (-ε₀) ε₀)) ∧
      (∃ φ : ℝ → M → M,
        ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun z : ℝ × M => φ z.1 z.2) ∧
        (∀ x, φ 0 x = x) ∧ (∀ s t x, φ (s + t) x = φ s (φ t x)) ∧
        ∀ x, IsMIntegralCurve (fun t => φ t x) X))

end RoundTrip.V1_14
