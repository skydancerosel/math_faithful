import Morse
/-! Blind formalization of V2_5 (Milnor §3, Remark after Thm 3.1: compactness cannot be omitted). Choices:
- Milnor's claim is that the compactness hypothesis of Theorem 3.1 is essential, illustrated by Diagram 3 (a surface with a
  point removed). Formalized as an existence statement: there is a smooth Hausdorff surface `M` (modelled on
  `EuclideanSpace ℝ (Fin 2)`), smooth `f : M → ℝ`, `a < b`, with `f⁻¹[a,b]` free of critical points and NOT compact, such that
  `M^a` is not a deformation retract of `M^b` (my `DefRetract`, as in V2_1; sublevel sets as subtypes).
- The specific picture is not encoded (any counterexample surface is accepted). -/
open scoped ContDiff Manifold unitInterval
namespace RoundTrip.V2_5

/-- `A` is a deformation retract of `X`: a continuous family `r t : X → X`, `r 0 = id`, `r 1` maps into `A`,
and each `r t` fixes `A` pointwise (as in Milnor's `r_t`). -/
def DefRetract {X : Type} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ r : unitInterval → X → X, Continuous (fun z : unitInterval × X => r z.1 z.2) ∧
    (∀ x, r 0 x = x) ∧ (∀ x, r 1 x ∈ A) ∧ ∀ a ∈ A, ∀ t, r t a = a

/-- Milnor's claim. -/
def B : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : T2Space M)
    (_ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) M) (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ M)
    (f : M → ℝ) (a b : ℝ), ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ) ∞ f ∧ a < b ∧
    (∀ x, f x ∈ Set.Icc a b → ¬ Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin 2)) f x) ∧
    ¬ IsCompact (f ⁻¹' Set.Icc a b) ∧
    ¬ DefRetract {x : {x : M | f x ≤ b} | f x.1 ≤ a}

end RoundTrip.V2_5
