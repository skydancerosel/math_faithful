import Morse
/-! Blind formalization of V3_14 (Milnor §5, p. 30: strong inequalities contain the weak ones). Choices:
- Purely arithmetic claim about sequences `R, C : ℕ → ℕ` with `R_λ = C_λ = 0` for `λ > n` (as for Betti/Morse numbers of an n-manifold),
  `alt` the alternating sums `a_λ - a_{λ-1} + ... ± a_0`.
- Hypothesis: all strong inequalities `(4_λ)`. Claims: (a) the weak inequality `R_λ ≤ C_λ` (sum of `(4_λ)` and `(4_{λ-1})`);
  (b) the equality (3) `Σ_{λ≤n} (-1)^λ R_λ = Σ_{λ≤n} (-1)^λ C_λ` (comparing `(4_λ)`, `(4_{λ-1})` for λ>n);
  (c) if `C_{λ+1} = 0` then `R_{λ+1} = 0` and `(4_λ)` is an equality `alt R λ = alt C λ`. -/
namespace RoundTrip.V3_14
def alt (a : ℕ → ℤ) (l : ℕ) : ℤ := ∑ i ∈ Finset.range (l + 1), (-1 : ℤ) ^ (l - i) * a i

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (R C : ℕ → ℕ) (n : ℕ), (∀ i, n < i → R i = 0 ∧ C i = 0) →
    (∀ l, alt (fun i => (R i : ℤ)) l ≤ alt (fun i => (C i : ℤ)) l) →
    (∀ l, R l ≤ C l) ∧
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (R i : ℤ) = ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (C i : ℤ) ∧
    (∀ l, C (l + 1) = 0 → R (l + 1) = 0 ∧ alt (fun i => (R i : ℤ)) l = alt (fun i => (C i : ℤ)) l)
end RoundTrip.V3_14
