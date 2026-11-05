import Morse
/-! Blind formalization of V3_19 (Milnor §6, Application 2: index of grad f is (-1)^λ). Choices:
- Setting for vector-field index sums (project's definitions, since Mathlib has no index of a vector field): `N` a nonempty compact
  smooth submanifold of `ℝ^{K+1}` of dimension `d+1` (project's `Milnor.IsSliceSubmanifold` with model `ℝ^{d+1}`, complement `ℝ^m`,
  with its charted-space structure `hN.chartedSpace`), as in Milnor's embedded manifolds. Dimension ≥ 1; `N` nonempty
  (both forced by the signature of the project's `Milnor.Tub.indexN`). A vector field is a smooth `v : N → ℝ^{K+1}` tangent to `N`
  (`v q ∈ Milnor.Tub.tanN hN q`); its index at a zero is `Milnor.Tub.indexN` (Milnor p. 38); the index sum is a `finsum` over the
  zero set, and the zero set is assumed finite.
- `χ(N) = Σ_{λ ≤ d+1} (-1)^λ R_λ(N)` with `R_λ` the rank of singular homology over a field `F` (quantified: every field).
- `f = Φ|N` for a smooth `Φ : ℝ^{K+1} → ℝ` (every smooth function on N is of this form); grad f = project's `Morse.tangentialGradient hN Φ`
  (projection of the ambient gradient to `T_qN`, the gradient for the induced metric); `q` a non-degenerate critical point of `f`
  (project's `Morse.IsNondegenerateCriticalPointM` for `fun x : N => Φ x`) of index `Morse.indexM`; claim `indexN (grad f) q = (-1)^index`.
  Smoothness of `grad f` is a hypothesis argument `hv` needed to apply `indexN` (it is true). -/
namespace RoundTrip.V3_19
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
  ∀ (K d m : ℕ) (N : Set (Rn (K + 1)))
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) N) (hc : IsCompact N) (hne : N.Nonempty),
    letI := hN.chartedSpace
    ∀ (Φ : Rn (K + 1) → ℝ), ContMDiff 𝓘(ℝ, Rn (K + 1)) 𝓘(ℝ) ∞ Φ →
    ∀ (hv : ContMDiff 𝓘(ℝ, Rn (d + 1)) 𝓘(ℝ, Rn (K + 1)) ∞ (Morse.tangentialGradient hN Φ)) (q : N),
      Morse.IsNondegenerateCriticalPointM (Rn (d + 1)) (fun x : N => Φ x) q →
      Milnor.Tub.indexN hN hc hne (Morse.tangentialGradient hN Φ) hv q =
        (-1 : ℤ) ^ Morse.indexM (Rn (d + 1)) (fun x : N => Φ x) q
end RoundTrip.V3_19
