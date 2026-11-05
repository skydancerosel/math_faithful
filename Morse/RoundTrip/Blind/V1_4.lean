import Morse
/-! Blind formalization of V1_4 (Milnor §2, pp. 4-5: Hessian on a manifold). Choices:
- Setting: smooth (C^∞) Hausdorff finite-dim real manifold `M` modelled on `E`; `TM_p = TangentSpace 𝓘(ℝ,E) p` (= `E`).
- Hessian: project's `Morse.hessianM E f p` (continuous bilinear form on `E`). Milnor's definition `f_**(v,w) = ṽ_p(w̃ f)`
  is expressed as a claim: for every critical point `p` and all smooth vector fields `X, Y` with `X p = v`, `Y p = w`,
  `mfderiv (x ↦ df_x(Y x)) p (X p) = hessianM v w`  (so in particular independent of extensions).
- Symmetric: `hessianM v w = hessianM w v`.
- Coordinates: for the preferred chart `extChartAt p`, with `D = mfderiv` of the chart at `p`, `f_**(v,w)` equals the
  second derivative of `f ∘ chart⁻¹` at `chart p` applied to `(D v, D w)` (i.e. the matrix in the coordinate basis
  `∂/∂x^i` is `(∂²f/∂x^i∂x^j)`).
- Index of `f` at `p` = index of `f_**`: my own `idx` (max dim of negative definite subspace) compared with `Morse.indexM`.
- "Morse functions subject of Thm 3.5": a pointer only, not formalized.
- Vector field = section `x ↦ TangentSpace x`, smooth as map into tangent bundle. -/
open scoped ContDiff Manifold
namespace RoundTrip.V1_4

/-- index of a bilinear functional. -/
noncomputable def idx {V : Type} [AddCommGroup V] [Module ℝ V] (H : V → V → ℝ) : ℕ :=
  sSup {k | ∃ W : Submodule ℝ V, Module.finrank ℝ W = k ∧ ∀ w ∈ W, w ≠ 0 → H w w < 0}

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : M → ℝ) (p : M), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f → Morse.IsCriticalPointM E f p →
    (∀ v w : E, ∀ X Y : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun x : M => (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) →
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun x : M => (⟨x, Y x⟩ : TangentBundle 𝓘(ℝ, E) M)) →
      X p = v → Y p = w →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (fun x => mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x (Y x)) p (X p) = Morse.hessianM E f p v w) ∧
    (∀ v w : E, Morse.hessianM E f p v w = Morse.hessianM E f p w v) ∧
    (∀ v w : E,
      Morse.hessianM E f p v w =
        fderiv ℝ (fun x => fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm) x
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) p v))
          (extChartAt 𝓘(ℝ, E) p p) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) p w)) ∧
    Morse.indexM E f p = idx (fun v w : E => Morse.hessianM E f p v w)

end RoundTrip.V1_4
