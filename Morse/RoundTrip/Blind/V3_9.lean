import Morse
/-! Blind formalization of V3_9 (Milnor §5, pp. 28-30: homology of a filtration, Morse numbers). Choices (definitions item):
- Homology: project's relative singular homology `Morse.Homology.relHomology (ModuleCat.of F F) i` on `subsetPair` (pairs `A ⊆ B` of
  subsets of a space `E : Type`), `F` a field.
- `R i h` = `Module.finrank F H_i(B, A; F)` (the Betti number `R_i(X,Y)`); claim: whenever `H_i` is finite-dimensional, `R` equals
  its rank (`Module.rank`).
- `C l` = number of critical points of index `l` of `f` (`Set.ncard` of `{p | critical ∧ indexM = l}`; project defs).
- Asserted (the exact sequence of a triple `Z ⊆ Y ⊆ X` with its final `→ 0`, using the project's triple `TopTriple.ofSubsets`,
  inclusion pairs `map₁, map₂` and connecting map `δ`): exactness at `H_n(Y,Z)`, `H_n(X,Z)`, `H_{n+1}(X,Y)`, and surjectivity of
  `H_0(X,Z) → H_0(X,Y)` (the final `→ 0`), as `range = ker` of linear maps.
- B = (rank statement) ∧ (exactness). `C_λ`'s role in the Morse inequalities is not part of this item. -/
open CategoryTheory Morse.Homology
namespace RoundTrip.V3_9

variable {F : Type} [Field F] {E : Type} [TopologicalSpace E]

/-- `R_i(X,Y) = rank H_i(X,Y;F)`. -/
noncomputable def R (F : Type) [Field F] {A B : Set E} (h : A ⊆ B) (i : ℕ) : ℕ :=
  Module.finrank F ((relHomology (ModuleCat.of F F) i).obj (subsetPair h))

/-- `C_λ` = number of critical points of index `λ`. -/
noncomputable def Cnum {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {M : Type} [TopologicalSpace M]
    [ChartedSpace E' M] (f : M → ℝ) (l : ℕ) : ℕ :=
  {p : M | Morse.IsCriticalPointM E' f p ∧ Morse.indexM E' f p = l}.ncard

/-- Milnor's claim. -/
def B : Prop :=
  (∀ (F : Type) [Field F] (E : Type) [TopologicalSpace E] (A B : Set E) (h : A ⊆ B) (i : ℕ),
      Module.Finite F ((relHomology (ModuleCat.of F F) i).obj (subsetPair h)) →
      ((R F h i : ℕ) : Cardinal) = Module.rank F ((relHomology (ModuleCat.of F F) i).obj (subsetPair h))) ∧
  ∀ (F : Type) [Field F] (E : Type) [TopologicalSpace E] (A B D : Set E) (hAB : A ⊆ B) (hBD : B ⊆ D),
    let T := Morse.Homology.TopTriple.ofSubsets hAB hBD
    (∀ n : ℕ, LinearMap.range (T.δ (ModuleCat.of F F) n).hom =
        LinearMap.ker ((relHomology (ModuleCat.of F F) n).map T.map₁).hom) ∧
    (∀ n : ℕ, LinearMap.range ((relHomology (ModuleCat.of F F) n).map T.map₁).hom =
        LinearMap.ker ((relHomology (ModuleCat.of F F) n).map T.map₂).hom) ∧
    (∀ n : ℕ, LinearMap.range ((relHomology (ModuleCat.of F F) (n + 1)).map T.map₂).hom =
        LinearMap.ker (T.δ (ModuleCat.of F F) n).hom) ∧
    LinearMap.range ((relHomology (ModuleCat.of F F) 0).map T.map₂).hom = ⊤

end RoundTrip.V3_9
