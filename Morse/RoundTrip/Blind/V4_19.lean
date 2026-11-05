import Morse
/-! Blind formalization of V4_19 (Milnor §6, Application 2). Choices:
- Setting for vector-field index sums (project's definitions, since Mathlib has no index of a vector field): `N` a nonempty compact smooth submanifold of `ℝ^{K+1}` of dimension `d+1`
  (project's `Milnor.IsSliceSubmanifold`, chart structure `hN.chartedSpace`), dimension ≥ 1 and `N` nonempty (forced by the signature of `Milnor.Tub.indexN`). A vector field is a smooth `v : N → ℝ^{K+1}`
  tangent to `N` (`v q ∈ Milnor.Tub.tanN hN q`); index at a zero = `Milnor.Tub.indexN`; index sum = `finsum` over the zero set, which is assumed finite.
- `χ(N) = Σ_{λ≤d+1} (-1)^λ R_λ(N)`, `R_λ` = rank of singular homology over `ℚ` (project's `relHomology`).
- `f = Φ|N` for smooth `Φ : ℝ^{K+1} → ℝ`; `grad f` = project's `Morse.tangentialGradient hN Φ` (gradient for the induced metric); `C_λ` = number of critical points of index `λ`.
- B = conjunction of Milnor's four assertions: (a) formula (3): `χ(N) = Σ (-1)^λ C_λ` for `f` with only non-degenerate critical points; (b) `grad f` (smooth, as hypothesis `hv`) has index `(-1)^λ`
  at a non-degenerate critical point of index `λ`; (c) some tangent vector field with finitely many zeros has index sum `χ(N)`; (d) every smooth tangent vector field with finitely many zeros has index sum `χ(N)`.
  (Topological invariance of the index sum, Steenrod, is Milnor's reason for (d); only the conclusion is stated.) -/
namespace RoundTrip.V4_19
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

/-- `χ(N) = Σ_{λ=0}^{d+1} (-1)^λ R_λ(N)` for `N` of dimension `d+1`. -/
noncomputable def chiN {K : ℕ} (d : ℕ) (N : Set (Rn (K + 1))) : ℤ :=
  ∑ l ∈ Finset.range (d + 2), (-1 : ℤ) ^ l * (Rabs N l : ℤ)

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (K d m : ℕ) (N : Set (Rn (K + 1)))
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) N) (hc : IsCompact N) (hne : N.Nonempty),
    letI := hN.chartedSpace
    (∀ Φ : Rn (K + 1) → ℝ, ContMDiff 𝓘(ℝ, Rn (K + 1)) 𝓘(ℝ) ∞ Φ →
      (∀ q : N, Morse.IsCriticalPointM (Rn (d + 1)) (fun x : N => Φ x) q →
        Morse.IsNondegenerateCriticalPointM (Rn (d + 1)) (fun x : N => Φ x) q) →
      chiN d N = ∑ l ∈ Finset.range (d + 2), (-1 : ℤ) ^ l * (Cnum (Rn (d + 1)) (fun x : N => Φ x) l : ℤ)) ∧
    (∀ (Φ : Rn (K + 1) → ℝ), ContMDiff 𝓘(ℝ, Rn (K + 1)) 𝓘(ℝ) ∞ Φ →
      ∀ (hv : ContMDiff 𝓘(ℝ, Rn (d + 1)) 𝓘(ℝ, Rn (K + 1)) ∞ (Morse.tangentialGradient hN Φ)) (q : N),
        Morse.IsNondegenerateCriticalPointM (Rn (d + 1)) (fun x : N => Φ x) q →
        Milnor.Tub.indexN hN hc hne (Morse.tangentialGradient hN Φ) hv q =
          (-1 : ℤ) ^ Morse.indexM (Rn (d + 1)) (fun x : N => Φ x) q) ∧
    (∃ (v : N → Rn (K + 1)) (hv : ContMDiff 𝓘(ℝ, Rn (d + 1)) 𝓘(ℝ, Rn (K + 1)) ∞ v),
      (∀ q, v q ∈ Milnor.Tub.tanN hN q) ∧ {q : N | v q = 0}.Finite ∧
      ∑ᶠ q ∈ {q : N | v q = 0}, Milnor.Tub.indexN hN hc hne v hv q = chiN d N) ∧
    ∀ (v : N → Rn (K + 1)) (hv : ContMDiff 𝓘(ℝ, Rn (d + 1)) 𝓘(ℝ, Rn (K + 1)) ∞ v),
      (∀ q, v q ∈ Milnor.Tub.tanN hN q) → {q : N | v q = 0}.Finite →
      ∑ᶠ q ∈ {q : N | v q = 0}, Milnor.Tub.indexN hN hc hne v hv q = chiN d N
end RoundTrip.V4_19
