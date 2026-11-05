import Morse
/-! Blind formalization of V3_34 (Milnor §5, p. 29: homology of the Morse filtration). Choices:
- Setting of §5: `M` compact smooth Hausdorff manifold modelled on finite-dimensional `E`, `f` smooth with only non-degenerate critical points
  (project's `Morse.IsCriticalPointM`, `Morse.IsNondegenerateCriticalPointM`, `Morse.indexM`), `F` an arbitrary field, homology = project's `relHomology` on `subsetPair`.
- Filtration: `MorseFilt` = Milnor's `a_1 < ... < a_k` with exactly `i` critical points in `M^{a_i}` and `M^{a_k} = M`, plus `M^{a_0} = ∅` (convention of the chain `∅ ⊂ M^{a_1} ⊂ ...`);
  the critical points are `p : Fin k → M` injective listed in order (so the hypothesis forces distinct critical values). B is stated for every such choice of `a`, `p` (existence of the choice is not claimed).
- B: for each `i`, `H_n(M^{a_i}, M^{a_{i-1}}; F)` is finite-dimensional of dimension 1 (the coefficient group `F`) if `n = λ_i = index p_i`, and `0` for every other `n`. -/
namespace RoundTrip.V3_34
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

/-- `M^a`. -/
def sub {M : Type} (f : M → ℝ) (a : ℝ) : Set M := {x | f x ≤ a}

/-- Milnor's choice `a_0 < a_1 < ... < a_k`, `p_1, ..., p_k` the critical points: `M^{a_0} = ∅`, `M^{a_i}` contains exactly
the critical points `p_1..p_i`, `M^{a_k} = M`. (Here `a : Fin (k+1) → ℝ` and `p : Fin k → M`; `p i` is Milnor's `p_{i+1}`.) -/
def MorseFilt (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
    (f : M → ℝ) (k : ℕ) (p : Fin k → M) (a : Fin (k + 1) → ℝ) : Prop :=
  StrictMono a ∧ Function.Injective p ∧ sub f (a 0) = ∅ ∧ sub f (a (Fin.last k)) = Set.univ ∧
  ∀ i : Fin (k + 1), {x | Morse.IsCriticalPointM E f x ∧ f x ≤ a i} = p '' {j | j.val < i.val}

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (F : Type) [Field F] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : M → ℝ), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f →
    (∀ p, Morse.IsCriticalPointM E f p → Morse.IsNondegenerateCriticalPointM E f p) →
    ∀ (k : ℕ) (p : Fin k → M) (a : Fin (k + 1) → ℝ), MorseFilt E f k p a →
    ∀ (i : Fin k) (h : sub f (a i.castSucc) ⊆ sub f (a i.succ)),
    ∀ n, Module.Finite F (Hom F h n) ∧
      Module.finrank F (Hom F h n) = if n = Morse.indexM E f (p i) then 1 else 0
end RoundTrip.V3_34
