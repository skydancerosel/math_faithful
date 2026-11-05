import Morse
/-! Layer-2 blind definition of Morse_IsHomotopyDirectLimit. Textbook: Milnor, *Morse Theory*,
Appendix, p. 149 (for subspaces `X₀ ⊆ X₁ ⊆ ⋯` of `X`, let `X_Σ = X₀ × [0,1] ∪ X₁ × [1,2] ∪ ⋯
⊆ X × ℝ`; `X` is the homotopy direct limit of `{Xᵢ}` if the projection `p : X_Σ → X`,
`p(x, τ) = x`, is a homotopy equivalence).
Choices: the increasing condition `X₀ ⊆ X₁ ⊆ ⋯` (not carried by the signature) is made part of
`T` (`Monotone A`), so `T` is false for non-increasing sequences. `X_Σ` carries the subspace
topology of `X × ℝ`; "homotopy equivalence" = has a continuous homotopy inverse (Mathlib
`ContinuousMap.Homotopic`). `⋃ Xᵢ = X` is not required (Milnor does not require it). -/
namespace RoundTrip.L2.Morse_IsHomotopyDirectLimit

variable {X : Type} [TopologicalSpace X]

/-- The telescope `X_Σ = ⋃ₙ Xₙ × [n, n+1] ⊆ X × ℝ`. -/
def tele (A : ℕ → Set X) : Set (X × ℝ) :=
  {z | ∃ n : ℕ, z.1 ∈ A n ∧ (n : ℝ) ≤ z.2 ∧ z.2 ≤ (n : ℝ) + 1}

/-- The projection `p : X_Σ → X`, `(x, τ) ↦ x` (subspace topology on `X_Σ`). -/
def proj (A : ℕ → Set X) : C(tele A, X) :=
  ⟨fun z => z.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- `f` is a homotopy equivalence: it has a continuous homotopy inverse. -/
def IsHE {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] (f : C(P, Q)) : Prop :=
  ∃ g : C(Q, P), (g.comp f).Homotopic (ContinuousMap.id P) ∧
    (f.comp g).Homotopic (ContinuousMap.id Q)

/-- The textbook notion: `A` is increasing and the projection `X_Σ → X` is a homotopy
equivalence. -/
def T (A : ℕ → Set X) : Prop :=
  Monotone A ∧ IsHE (proj A)

end RoundTrip.L2.Morse_IsHomotopyDirectLimit
