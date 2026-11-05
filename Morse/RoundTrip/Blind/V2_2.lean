import Morse
/-! Blind formalization of V2_2 (Milnor Theorem 3.1; item titled "Euclidean space title; text is general"). Choices:
- Setting follows the stated text: an arbitrary smooth (C^∞) Hausdorff finite-dim manifold `M` (abstract, modelled on `E`),
  `f` smooth, `a < b`, `M^c = {x | f x ≤ c}` (subtype), hypotheses: `f⁻¹[a,b]` compact and containing no critical
  point (project def `Morse.IsCriticalPointM`).
- "M^a diffeomorphic to M^b": these are manifolds with boundary, so: mutually inverse maps `h : M^a → M^b`, `g : M^b → M^a`
  that are smooth on the closed sets (`ContMDiffOn` on the set, i.e. locally restrictions of smooth maps).
- "deformation retract": my `DefRetract` (homotopy `r_t` from id of `M^b` to a retraction onto `M^a`, fixing `M^a`
  pointwise); "inclusion is a homotopy equivalence": a `HomotopyEquiv` whose underlying map is the inclusion.
- The proof via the flow of `ρ grad f` (and `φ_{b-a}` carrying `M^a` onto `M^b`) is not asserted. -/
open scoped ContDiff Manifold unitInterval
namespace RoundTrip.V2_2

/-- `A` is a deformation retract of `X`: a continuous family `r t : X → X`, `r 0 = id`, `r 1` maps into `A`,
and each `r t` fixes `A` pointwise (as in Milnor's `r_t`). -/
def DefRetract {X : Type} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ r : unitInterval → X → X, Continuous (fun z : unitInterval × X => r z.1 z.2) ∧
    (∀ x, r 0 x = x) ∧ (∀ x, r 1 x ∈ A) ∧ ∀ a ∈ A, ∀ t, r t a = a

/-- Theorem 3.1 (conclusion for fixed `a < b`). -/
def Thm31 : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : M → ℝ) (a b : ℝ), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f → a < b →
    IsCompact (f ⁻¹' Set.Icc a b) → (∀ x, f x ∈ Set.Icc a b → ¬ Morse.IsCriticalPointM E f x) →
    (∃ h g : M → M, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ h {x | f x ≤ a} ∧ ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ g {x | f x ≤ b} ∧
        Set.MapsTo h {x | f x ≤ a} {x | f x ≤ b} ∧ Set.MapsTo g {x | f x ≤ b} {x | f x ≤ a} ∧
        (∀ x, f x ≤ a → g (h x) = x) ∧ (∀ x, f x ≤ b → h (g x) = x)) ∧
    DefRetract {x : {x : M | f x ≤ b} | f x.1 ≤ a} ∧
    ∃ h : ContinuousMap.HomotopyEquiv {x : M | f x ≤ a} {x : M | f x ≤ b}, ∀ x, (h x).1 = x.1

/-- Milnor's claim. -/
def B : Prop := Thm31

end RoundTrip.V2_2
