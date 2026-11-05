import Morse
/-! Blind formalization of V3_17 (Milnor §5 p. 28, §6 Application 2: the Poincaré–Hopf integer). Choices:
- Setting for vector-field index sums (project's definitions, since Mathlib has no index of a vector field): `N` a nonempty compact
  smooth submanifold of `ℝ^{K+1}` of dimension `d+1` (project's `Milnor.IsSliceSubmanifold` with model `ℝ^{d+1}`, complement `ℝ^m`,
  with its charted-space structure `hN.chartedSpace`), as in Milnor's embedded manifolds. Dimension ≥ 1; `N` nonempty
  (both forced by the signature of the project's `Milnor.Tub.indexN`). A vector field is a smooth `v : N → ℝ^{K+1}` tangent to `N`
  (`v q ∈ Milnor.Tub.tanN hN q`); its index at a zero is `Milnor.Tub.indexN` (Milnor p. 38); the index sum is a `finsum` over the
  zero set, and the zero set is assumed finite.
- `χ(N) = Σ_{λ ≤ d+1} (-1)^λ R_λ(N)` with `R_λ` the rank of singular homology over a field `F` (quantified: every field).
- B: for every field `F`, the sum of the indices of any (smooth tangent) vector field with finitely many zeros equals Milnor's `χ(N)`.
  The "topological invariance" of the index sum (Steenrod) is used as a known fact, not restated; it is implied by B. -/
namespace RoundTrip.V3_17
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

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

/-- `χ(N) = Σ_{λ=0}^{d+1} (-1)^λ R_λ(N)` for `N` of dimension `d+1` (Betti numbers over the field `F`). -/
noncomputable def chiN (F : Type) [Field F] {K : ℕ} (d : ℕ) (N : Set (Rn (K + 1))) : ℤ :=
  ∑ l ∈ Finset.range (d + 2), (-1 : ℤ) ^ l * (Rabs F N l : ℤ)

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (F : Type) [Field F], ∀ (K d m : ℕ) (N : Set (Rn (K + 1)))
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) N) (hc : IsCompact N) (hne : N.Nonempty),
    letI := hN.chartedSpace
    ∀ (v : N → Rn (K + 1)) (hv : ContMDiff 𝓘(ℝ, Rn (d + 1)) 𝓘(ℝ, Rn (K + 1)) ∞ v),
      (∀ q, v q ∈ Milnor.Tub.tanN hN q) → {q : N | v q = 0}.Finite →
      ∑ᶠ q ∈ {q : N | v q = 0}, Milnor.Tub.indexN hN hc hne v hv q = chiN F d N
end RoundTrip.V3_17
