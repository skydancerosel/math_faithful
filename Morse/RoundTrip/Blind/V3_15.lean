import Morse
/-! Blind formalization of V3_15 (Milnor §5, Corollary 5.4 (lacunary principle)). Choices:
- Setting (Milnor §5): `M` a compact smooth (C^∞) Hausdorff manifold modelled on a finite-dimensional real normed space `E`
  (`n = finrank ℝ E`), `f : M → ℝ` smooth with only non-degenerate critical points (isolated follows); critical point,
  non-degenerate and index are the project's `Morse.IsCriticalPointM`, `Morse.IsNondegenerateCriticalPointM`, `Morse.indexM`.
- `C_λ = Cnum` = `Set.ncard` of critical points of index λ; `R_λ(M) = rank H_λ(M; F)` = `finrank` of the project's relative
  singular homology `relHomology` of the pair `(univ, ∅)`, `F` an arbitrary field (quantified, `Type`). Sums `Σ_{λ=0}^n`.
- B = Corollary 5.4: if `C_{λ+1} = C_{λ-1} = 0` then `R_λ = C_λ` and `R_{λ+1} = R_{λ-1} = 0`; for `λ = 0` the term `λ-1` is vacuous
  (hypothesis `l = 0 ∨ C_{l-1} = 0`, conclusion `l = 0 ∨ R_{l-1} = 0`; `l-1` is truncated subtraction, only used when `l ≥ 1`).
- NOT expressed: the remarks (follows from Thm 3.5; gives homology of CP^n without Thm 3.5) -- they concern other results/§4 examples. -/
namespace RoundTrip.V3_15
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
    ∀ l, Cnum E f (l + 1) = 0 → (l = 0 ∨ Cnum E f (l - 1) = 0) →
      Rabs F M l = Cnum E f l ∧ Rabs F M (l + 1) = 0 ∧ (l = 0 ∨ Rabs F M (l - 1) = 0)
end RoundTrip.V3_15
