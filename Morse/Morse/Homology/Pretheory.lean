import Morse.Homology.RelativeHomotopy
import Mathlib.AlgebraicTopology.EilenbergSteenrod
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Singular homology as an Eilenberg–Steenrod homology pretheory

Mathlib's `TopPair.HomologyPretheory C c` packages the data of an Eilenberg–Steenrod homology
theory: relative homology functors `Hₚ i : TopPair ⥤ C`, absolute homology functors
`H i : TopCat ⥤ C`, a natural isomorphism `H i ≅ incl ⋙ Hₚ i` (absolute homology is the homology
of the pair `(X, ∅)`), and natural boundary maps `δ i j : Hₚ i ⟶ proj₂ ⋙ H j`, zero unless
`c.Rel i j`.  The first axiom, homotopy invariance, is the class
`TopPair.HomologyPretheory.IsHomotopyInvariant`.  Mathlib has no instance yet.

This file provides the singular instance, for coefficients `R` in an abelian category `C` with
coproducts, indexed by `ComplexShape.down ℕ` (so `c.Rel i j ↔ j + 1 = i`):

* `Morse.Homology.singularHomologyPretheory C R`: `Hₚ n = relHomology R n` (relative singular
  homology, `Morse/Homology/Relative.lean`), `H n = (singularHomologyFunctor C n).obj R`, the
  isomorphism `H_n(X) ≅ H_n(X, ∅)` (`Morse.Homology.relHomologyInclIso`), and `δ (n + 1) n` the
  connecting morphism of the pair (`Morse.Homology.relδNatTrans`);
* the instance `IsHomotopyInvariant` (`Morse.Homology.relHomology_map_eq_of_homotopy`).

The exactness of the long exact sequence of a pair is `Morse.Homology.relHomology_exact₁`,
`relHomology_exact₂` and `relHomology_exact₃`; excision is not part of this file.
-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

namespace Morse.Homology

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C)

/-- **Singular homology** with coefficients in `R : C`, as an Eilenberg–Steenrod homology
pretheory (relative homology, absolute homology, `H_n(X) ≅ H_n(X, ∅)` and the boundary maps of
the pairs). -/
def singularHomologyPretheory : TopPair.HomologyPretheory.{w} C (ComplexShape.down ℕ) where
  Hₚ n := relHomology R n
  H n := (singularHomologyFunctor C n).obj R
  iso n := relHomologyInclIso R n
  δ i j := if h : (ComplexShape.down ℕ).Rel i j then relδNatTrans R i j h else 0
  shape_δ _ _ h := dif_neg h

@[simp]
lemma singularHomologyPretheory_Hₚ (n : ℕ) :
    (singularHomologyPretheory C R).Hₚ n = relHomology R n := rfl

@[simp]
lemma singularHomologyPretheory_H (n : ℕ) :
    (singularHomologyPretheory C R).H n = (singularHomologyFunctor C n).obj R := rfl

@[simp]
lemma singularHomologyPretheory_iso (n : ℕ) :
    (singularHomologyPretheory C R).iso n = relHomologyInclIso R n := rfl

/-- The boundary map `H_{n+1}(X, A) ⟶ H_n(A)` of the pretheory is the connecting morphism of the
long exact sequence of the pair. -/
lemma singularHomologyPretheory_δ_app (n : ℕ) (X : TopPair.{w}) :
    ((singularHomologyPretheory C R).δ (n + 1) n).app X = relδ R X n := by
  simp only [singularHomologyPretheory, dif_pos (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)]
  rfl

/-- **Homotopy invariance** of singular homology, as an Eilenberg–Steenrod axiom. -/
instance isHomotopyInvariant_singularHomologyPretheory :
    (singularHomologyPretheory C R).IsHomotopyInvariant where
  map_eq_of_homotopy F i := relHomology_map_eq_of_homotopy R F i

/- For instance: singular homology with coefficients in a commutative ring `R`, as an object of
`ModuleCat R`, is a homotopy-invariant homology pretheory on pairs of spaces in the same
universe. -/
example (R : Type u) [CommRing R] :
    (singularHomologyPretheory (ModuleCat.{u} R) (ModuleCat.of R R)).IsHomotopyInvariant :=
  inferInstance

end Morse.Homology
