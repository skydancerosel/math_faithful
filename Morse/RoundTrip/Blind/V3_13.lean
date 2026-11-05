import Morse
/-! Blind formalization of V3_13 (Milnor §5, the strong Morse inequalities (4_λ)). Choices:
- Abstract filtration version (Lemma 5.1 applied): a space `X : Type`, a chain of subsets `∅ = X_0 ⊆ ... ⊆ X_k = univ`
  (`Xs : Fin (k+1) → Set X`), numbers `λ_i : Fin k → ℕ` with `H_n(X_{i+1}, X_i; F)` finite-dimensional of dimension `1`
  (the coefficient group `F`) if `n = λ_i` and `0` otherwise (project's `relHomology` on `subsetPair`).
- `C_λ` := number of `i` with `λ_i = λ`; `R_λ(X) = finrank H_λ(X, ∅; F)`; `F` an arbitrary field.
- B: for all λ, `R_λ - R_{λ-1} + ... ± R_0 ≤ C_λ - C_{λ-1} + ... ± C_0` (in ℤ, `alt`). -/
namespace RoundTrip.V3_13
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

/-- `H_n(X, Y; F)` for `Y ⊆ X` subsets of a space (project's relative singular homology). -/
noncomputable def Hom (F : Type) [Field F] {E : Type} [TopologicalSpace E] {A B : Set E} (h : A ⊆ B) (n : ℕ) :
    ModuleCat F := (relHomology (ModuleCat.of F F) n).obj (subsetPair h)

/-- `R_i(X, Y) = rank H_i(X, Y; F)`. -/
noncomputable def R (F : Type) [Field F] {E : Type} [TopologicalSpace E] {A B : Set E} (h : A ⊆ B) (i : ℕ) : ℕ :=
  Module.finrank F (Hom F h i)

/-- `R_i(X) = R_i(X, ∅)`. -/
noncomputable def Rabs (F : Type) [Field F] (E : Type) [TopologicalSpace E] (i : ℕ) : ℕ :=
  R F (Set.empty_subset (Set.univ : Set E)) i

/-- `a_λ - a_{λ-1} + ... ± a_0`. -/
def alt (a : ℕ → ℤ) (l : ℕ) : ℤ := ∑ i ∈ Finset.range (l + 1), (-1 : ℤ) ^ (l - i) * a i

/-- `C_λ`: number of critical points of index `λ`. -/
noncomputable def Cnum (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type} [TopologicalSpace M]
    [ChartedSpace E M] (f : M → ℝ) (l : ℕ) : ℕ :=
  {p : M | Morse.IsCriticalPointM E f p ∧ Morse.indexM E f p = l}.ncard

/-- `C_λ` for an abstract filtration: number of `i` with `λ_i = λ`. -/
def Cabs {k : ℕ} (lam : Fin k → ℕ) (l : ℕ) : ℕ := (Finset.univ.filter fun i => lam i = l).card

/-- Chain `∅ = X_0 ⊆ X_1 ⊆ ... ⊆ X_k = X` with `H_*(X_i, X_{i-1}; F)` equal to the coefficient group `F` in dimension `λ_i`
and `0` otherwise. -/
def FiltHyp (F : Type) [Field F] {X : Type} [TopologicalSpace X] {k : ℕ} (Xs : Fin (k + 1) → Set X)
    (lam : Fin k → ℕ) : Prop :=
  Xs 0 = ∅ ∧ Xs (Fin.last k) = Set.univ ∧
  ∀ i : Fin k, ∃ h : Xs i.castSucc ⊆ Xs i.succ, ∀ n,
    Module.Finite F (Hom F h n) ∧ Module.finrank F (Hom F h n) = if n = lam i then 1 else 0

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (F : Type) [Field F] (X : Type) [TopologicalSpace X] (k : ℕ) (Xs : Fin (k + 1) → Set X) (lam : Fin k → ℕ),
    FiltHyp F Xs lam →
    ∀ l, alt (fun i => (Rabs F X i : ℤ)) l ≤ alt (fun i => (Cabs lam i : ℤ)) l
end RoundTrip.V3_13
