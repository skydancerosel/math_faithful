import Morse
/-! Blind formalization of V3_11 (Milnor §5, Theorem 5.2 (weak Morse inequalities)). Choices:
- Setting (Milnor §5): `M` a compact smooth (C^∞) Hausdorff manifold modelled on a finite-dimensional real normed space `E`
  (`n = finrank ℝ E`), `f : M → ℝ` smooth with only non-degenerate critical points (isolated follows); critical point,
  non-degenerate and index are the project's `Morse.IsCriticalPointM`, `Morse.IsNondegenerateCriticalPointM`, `Morse.indexM`.
- `C_λ = Cnum` = `Set.ncard` of critical points of index λ; `R_λ(M) = rank H_λ(M; F)` = `finrank` of the project's relative
  singular homology `relHomology` of the pair `(univ, ∅)`, `F` an arbitrary field (quantified, `Type`). Sums `Σ_{λ=0}^n`.
- B = (2) `R_λ(M) ≤ C_λ` for all λ, and (3) `Σ (-1)^λ R_λ(M) = Σ (-1)^λ C_λ`. The proof's chain `a_1<...<a_k` is not part of B.
- "Abstractly": expressed in singular homology (the only theory in the project), over every field. -/
namespace RoundTrip.V3_11
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

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (F : Type) [Field F] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : M → ℝ), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f →
    (∀ p, Morse.IsCriticalPointM E f p → Morse.IsNondegenerateCriticalPointM E f p) →
    (∀ l, Rabs F M l ≤ Cnum E f l) ∧
      ∑ l ∈ Finset.range (Module.finrank ℝ E + 1), (-1 : ℤ) ^ l * (Rabs F M l : ℤ) =
        ∑ l ∈ Finset.range (Module.finrank ℝ E + 1), (-1 : ℤ) ^ l * (Cnum E f l : ℤ)
end RoundTrip.V3_11
