import Morse
/-! Blind formalization of V3_10 (Milnor §5, p. 28: R_λ subadditive, χ additive). Choices:
- Triples `Z ⊆ Y ⊆ X` of subsets of a space `E : Type`; homology: project's `relHomology` over a field `F`; `R_i(X,Y)=finrank`.
- Subadditivity: `R_λ(X,Z) ≤ R_λ(X,Y) + R_λ(Y,Z)` for every λ, assuming all `H_i` of the three pairs are finite-dimensional
  (Milnor's tacit finiteness; `finrank` of an infinite-dimensional space is 0).
- `χ(X,Y) = ∑ᶠ λ, (-1)^λ R_λ(X,Y)` (ℤ, finsum). Additivity `χ(X,Z) = χ(X,Y) + χ(Y,Z)` assumed under finite-dimensionality
  and vanishing of `H_i` (R_i = 0) for large `i` in all three pairs (tacit finiteness for the sums to make sense).
- The exact-sequence argument is a proof sketch and is not part of B. -/
namespace RoundTrip.V3_10
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

/-- `χ(X, Y) = Σ (-1)^λ R_λ(X, Y)`. -/
noncomputable def chi (F : Type) [Field F] {E : Type} [TopologicalSpace E] {A B : Set E} (h : A ⊆ B) : ℤ :=
  ∑ᶠ l : ℕ, (-1 : ℤ) ^ l * (R F h l : ℤ)

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (F : Type) [Field F] (E : Type) [TopologicalSpace E] (X Y Z : Set E) (hZY : Z ⊆ Y) (hYX : Y ⊆ X),
    (∀ i, Module.Finite F (Hom F hZY i)) → (∀ i, Module.Finite F (Hom F hYX i)) →
    (∀ i, Module.Finite F (Hom F (hZY.trans hYX) i)) →
    (∀ l, R F (hZY.trans hYX) l ≤ R F hYX l + R F hZY l) ∧
    ((∃ N, ∀ i, N ≤ i → R F hZY i = 0) → (∃ N, ∀ i, N ≤ i → R F hYX i = 0) →
      (∃ N, ∀ i, N ≤ i → R F (hZY.trans hYX) i = 0) →
      chi F (hZY.trans hYX) = chi F hYX + chi F hZY)
end RoundTrip.V3_10
