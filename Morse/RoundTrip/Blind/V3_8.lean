import Morse
/-! Blind formalization of V3_8 (Milnor Lemma 5.1). Choices:
- Spaces = subsets of an ambient type `α`; `S : Set α → Set α → ℤ` with domain predicate `dom` of defined pairs (as in V3_7).
- Chain `X_0 ⊆ X_1 ⊆ … ⊆ X_n` given as `X : ℕ → Set α` with `X i ⊆ X j` for `i ≤ j ≤ n`; hypothesis: all pairs `(X_j, X_i)`
  (`i ≤ j ≤ n`) lie in `dom` (needed for the statement, and for the induction).
- Claims: `S(X_n, X_0) ≤ Σ_{i=1}^n S(X_i, X_{i-1})` for subadditive `S`; equality for additive `S`;
  and with `X_0 = ∅`, `S(X_n) = S(X_n, ∅) ≤ Σ S(X_i,X_{i-1})` (inequality (1)).  The induction is not asserted. -/
namespace RoundTrip.V3_8

/-- subadditive. -/
def Subadditive {α : Type} (dom : Set α → Set α → Prop) (S : Set α → Set α → ℤ) : Prop :=
  ∀ X Y Z : Set α, Z ⊆ Y → Y ⊆ X → dom X Z → dom X Y → dom Y Z → S X Z ≤ S X Y + S Y Z

/-- additive. -/
def Additive {α : Type} (dom : Set α → Set α → Prop) (S : Set α → Set α → ℤ) : Prop :=
  ∀ X Y Z : Set α, Z ⊆ Y → Y ⊆ X → dom X Z → dom X Y → dom Y Z → S X Z = S X Y + S Y Z

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (α : Type) (dom : Set α → Set α → Prop) (S : Set α → Set α → ℤ) (X : ℕ → Set α) (n : ℕ),
    (∀ i j, i ≤ j → j ≤ n → X i ⊆ X j) → (∀ i j, i ≤ j → j ≤ n → dom (X j) (X i)) →
    (Subadditive dom S → S (X n) (X 0) ≤ ∑ i ∈ Finset.Icc 1 n, S (X i) (X (i - 1))) ∧
    (Additive dom S → S (X n) (X 0) = ∑ i ∈ Finset.Icc 1 n, S (X i) (X (i - 1))) ∧
    (X 0 = ∅ → Subadditive dom S → S (X n) ∅ ≤ ∑ i ∈ Finset.Icc 1 n, S (X i) (X (i - 1)))

end RoundTrip.V3_8
