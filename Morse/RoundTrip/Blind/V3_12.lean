import Morse
/-! Blind formalization of V3_12 (Milnor Lemma 5.3: S_λ is subadditive). Choices:
- Homology: project's relative singular homology `Morse.Homology.relHomology` in `ModuleCat F` with coefficient `F` itself
  (F a field), pairs from subsets `A ⊆ B` of a topological space `E` (`Morse.Homology.subsetPair`). Rank = `Module.finrank F`.
- Triples `X ⊇ Y ⊇ Z` are subsets of one ambient space `E : Type`.
- `R_i(X,Y) = rank H_i(X,Y;F)`; `S_λ(X,Y) = Σ_{i≤λ} (-1)^{λ-i} R_i(X,Y)` (ℤ-valued).
- Subadditive: `S_λ(X,Z) ≤ S_λ(X,Y) + S_λ(Y,Z)`.
- Milnor's standing assumption that ranks are finite: hypothesis that `H_i` of the three pairs is finite-dimensional for all i
  (Lean's `finrank` of an infinite-dimensional space is 0, so some finiteness hypothesis is needed). The ω-exact-sequence
  rank computation in the proof is not stated separately. -/
open CategoryTheory Morse.Homology
namespace RoundTrip.V3_12

variable (F : Type) [Field F] {E : Type} [TopologicalSpace E]

/-- `R_i(X, Y) = rank H_i(X, Y; F)`. -/
noncomputable def R {A B : Set E} (h : A ⊆ B) (i : ℕ) : ℕ :=
  Module.finrank F ((relHomology (ModuleCat.of F F) i).obj (subsetPair h))

/-- `S_λ(X, Y) = R_λ - R_{λ-1} + ... ± R_0`. -/
noncomputable def S {A B : Set E} (h : A ⊆ B) (l : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (l + 1), (-1 : ℤ) ^ (l - i) * (R F h i : ℤ)

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (F : Type) [Field F] (E : Type) [TopologicalSpace E] (X Y Z : Set E) (hZY : Z ⊆ Y) (hYX : Y ⊆ X) (l : ℕ),
    (∀ i, Module.Finite F ((relHomology (ModuleCat.of F F) i).obj (subsetPair hZY))) →
    (∀ i, Module.Finite F ((relHomology (ModuleCat.of F F) i).obj (subsetPair hYX))) →
    (∀ i, Module.Finite F ((relHomology (ModuleCat.of F F) i).obj (subsetPair (hZY.trans hYX)))) →
    S F (hZY.trans hYX) l ≤ S F hYX l + S F hZY l

end RoundTrip.V3_12
