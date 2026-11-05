import Morse
/-! Blind formalization of V6_7 (Milnor §8, proof of Lemma 8.2: global solutions of the linear equations). Choices:
- Local coordinates: `u : ℝ → ℝⁿ` a smooth curve (`ℝⁿ = Fin n → ℝ`) with `u(t)` in an open set `Ω` (the chart image) for `t ∈ [a,b]`; Christoffel symbols `Γ^k_ij : ℝⁿ → ℝ` smooth on `Ω` (`ContDiffOn ℝ ∞`).
  "All relevant values of t": the compact interval `[a,b]` on which the curve is defined and stays in the chart.
- The equations `dv^k/dt + Σ_{i,j} (du^i/dt) Γ^k_ij v^j = 0` for `v : ℝ → ℝⁿ`; a solution on `[a,b]` means `v` has derivative (within `[a,b]`) satisfying the equation at every `t ∈ [a,b]`.
- B: for every `t₀ ∈ [a,b]` and initial value `v₀`, there is a solution on `[a,b]` with `v(t₀) = v₀`, and any two solutions with the same initial value agree on `[a,b]`. -/
namespace RoundTrip.V6_7
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- `v` solves `dv^k/dt + Σ (du^i/dt) Γ^k_ij v^j = 0` on `[a,b]`. -/
def IsSol {n : ℕ} (Γ : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ) (u : ℝ → Fin n → ℝ) (a b : ℝ)
    (v : ℝ → Fin n → ℝ) : Prop :=
  ∀ t ∈ Set.Icc a b, HasDerivWithinAt v
    (fun k => -∑ i, ∑ j, deriv (fun s => u s i) t * Γ (u t) k i j * v t j) (Set.Icc a b) t

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (Ω : Set (Fin n → ℝ)) (Γ : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ) (u : ℝ → Fin n → ℝ) (a b : ℝ),
    IsOpen Ω → (∀ k i j, ContDiffOn ℝ ∞ (fun x => Γ x k i j) Ω) → ContDiff ℝ ∞ u → (∀ t ∈ Set.Icc a b, u t ∈ Ω) →
    ∀ t₀ ∈ Set.Icc a b, ∀ v₀ : Fin n → ℝ,
      ∃ v : ℝ → Fin n → ℝ, IsSol Γ u a b v ∧ v t₀ = v₀ ∧
        ∀ v' : ℝ → Fin n → ℝ, IsSol Γ u a b v' → v' t₀ = v₀ → ∀ t ∈ Set.Icc a b, v' t = v t
end RoundTrip.V6_7
