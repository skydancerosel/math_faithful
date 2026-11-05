import Morse
/-! Blind formalization of V3_16 (Milnor §5, p. 29: the numbers C_λ). Choices:
- Setting (Milnor §5): `M` a compact smooth (C^∞) Hausdorff manifold modelled on a finite-dimensional real normed space `E`
  (`n = finrank ℝ E`), `f : M → ℝ` smooth with only non-degenerate critical points (isolated follows); critical point,
  non-degenerate and index are the project's `Morse.IsCriticalPointM`, `Morse.IsNondegenerateCriticalPointM`, `Morse.indexM`.
- `C_λ = Cnum` = `Set.ncard` of critical points of index λ; `R_λ(M) = rank H_λ(M; F)` = `finrank` of the project's relative
  singular homology `relHomology` of the pair `(univ, ∅)`, `F` an arbitrary field (quantified, `Type`). Sums `Σ_{λ=0}^n`.
- Definition item: `Cnum` is the definition of `C_λ`. B asserts what is implicit: the critical set is finite (so `C_λ` is the honest
  number, not a truncated `ncard`), and `C_λ = 0` for `λ > n` (so the alternating sums end with `± C_n`). -/
namespace RoundTrip.V3_16
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
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : M → ℝ), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f →
    (∀ p, Morse.IsCriticalPointM E f p → Morse.IsNondegenerateCriticalPointM E f p) →
    {p : M | Morse.IsCriticalPointM E f p}.Finite ∧
    (∀ l, {p : M | Morse.IsCriticalPointM E f p ∧ Morse.indexM E f p = l}.Finite) ∧
    ∀ l, Module.finrank ℝ E < l → Cnum E f l = 0
end RoundTrip.V3_16
