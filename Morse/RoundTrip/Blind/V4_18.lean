import Morse
/-! Blind formalization of V4_18 (Milnor §5, formula (3): χ(M) = C_0 - C_1 + ... ± C_n). Choices:
- Abstract compact manifold `M : Type`, Hausdorff, smooth, modelled on `ℝⁿ` (`n = dim M`), without boundary; `f : M → ℝ` smooth with isolated non-degenerate critical points,
  formalized as: every critical point is non-degenerate (`Morse.IsNondegenerateCriticalPointM`; isolatedness follows).
- `C_λ` = number of critical points of index `λ` (`Set.ncard` of `{p | critical ∧ Morse.indexM = λ}`; project's `Morse.IsCriticalPointM`, `Morse.indexM`).
- `χ(M)` = `Σ_λ (-1)^λ R_λ(M)` (`λ = 0..n`), the Euler characteristic defined from the Betti numbers `R_λ(M) = rank H_λ(M; ℚ)`: the project's relative singular homology `Morse.Homology.relHomology`
  applied to the pair `(M, ∅)` (`Rabs`) with coefficients in the field `ℚ` (rank of integral homology = dimension of rational homology), `Module.finrank`.
- B: `χ(M) = Σ_{λ=0}^n (-1)^λ C_λ`. -/
namespace RoundTrip.V4_18
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- `R_i(X, Y) = rank H_i(X, Y; ℚ)`. -/
noncomputable def Rbetti {E : Type} [TopologicalSpace E] {A B : Set E} (h : A ⊆ B) (i : ℕ) : ℕ :=
  Module.finrank ℚ ((relHomology (ModuleCat.of ℚ ℚ) i).obj (subsetPair h))

/-- `R_i(X) = R_i(X, ∅)`. -/
noncomputable def Rabs (E : Type) [TopologicalSpace E] (i : ℕ) : ℕ :=
  Rbetti (Set.empty_subset (Set.univ : Set E)) i

/-- `C_λ`: number of critical points of index `λ`. -/
noncomputable def Cnum (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type} [TopologicalSpace M]
    [ChartedSpace E M] (f : M → ℝ) (l : ℕ) : ℕ :=
  {p : M | Morse.IsCriticalPointM E f p ∧ Morse.indexM E f p = l}.ncard

/-- Euler characteristic from the Betti numbers, `Σ_{λ=0}^n (-1)^λ R_λ(M)`. -/
noncomputable def chiBetti (n : ℕ) (M : Type) [TopologicalSpace M] : ℤ :=
  ∑ l ∈ Finset.range (n + 1), (-1 : ℤ) ^ l * (Rabs M l : ℤ)

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
    (f : M → ℝ), ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ f →
    (∀ q, Morse.IsCriticalPointM (Rn n) f q → Morse.IsNondegenerateCriticalPointM (Rn n) f q) →
    chiBetti n M = ∑ l ∈ Finset.range (n + 1), (-1 : ℤ) ^ l * (Cnum (Rn n) f l : ℤ)
end RoundTrip.V4_18
