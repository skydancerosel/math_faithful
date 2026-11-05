import Morse.Homology.RelativeHomotopy
import Morse.Chapter2.Crossing

/-!
# Strong deformation retracts and relative singular homology

Milnor (§3, Theorem 3.1 and Remark 3.3) shows that `M^a` is a deformation retract of `M^b` when
`f⁻¹[a, b]` contains no critical point, and that `M^{c-ε} ∪ e^λ` is a deformation retract of
`M^{c+ε}`; in §5 these are used through singular homology.  This file records the homological
consequences, for the project's notion `Morse.IsStrongDeformationRetract`
(`Morse/Chapter2/Crossing.lean`), for subsets `A ⊆ B ⊆ X` of a space `E`, `B` being a strong
deformation retract of `X` (inside the subspace `X`):

* `Morse.Homology.isIso_homologyMap_of_isStrongDeformationRetract`: `H_n(B) ≅ H_n(X)` via the
  inclusion;
* `Morse.Homology.isIso_relHomology_map_of_isStrongDeformationRetract`: `H_n(B, A) ≅ H_n(X, A)`
  via the inclusion of pairs;
* `Morse.Homology.isZero_relHomology_of_isStrongDeformationRetract`: `H_n(X, B) = 0`.

The proofs combine `Morse.IsStrongDeformationRetract.exists_homotopyEquiv` (the inclusion is a
homotopy equivalence) with the homotopy invariance of singular homology and the five lemma
(`Morse/Homology/RelativeHomotopy.lean`).
-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

universe w v u

namespace Morse.Homology

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C)
  {E : Type w} [TopologicalSpace E]

/-- If `B ⊆ X` is a strong deformation retract of `X`, the inclusion induces isomorphisms
`H_n(B) ≅ H_n(X)`. -/
theorem isIso_homologyMap_of_isStrongDeformationRetract {B X : Set E} (hBX : B ⊆ X)
    (h : IsStrongDeformationRetract ((↑) ⁻¹' B : Set X)) (n : ℕ) :
    IsIso (homologyMap ((singularChains R).map (subsetInclusion hBX)) n) := by
  obtain ⟨e, he⟩ := h.exists_homotopyEquiv hBX
  refine isIso_homologyMap_of_homotopyEquiv R (X := TopCat.of B) (Y := TopCat.of X)
    (subsetInclusion hBX) e ?_ n
  rw [he]
  rfl

/-- If `A ⊆ B ⊆ X` and `B` is a strong deformation retract of `X`, the inclusion of pairs
`(B, A) ⟶ (X, A)` induces isomorphisms `H_n(B, A) ≅ H_n(X, A)`. -/
theorem isIso_relHomology_map_of_isStrongDeformationRetract {A B X : Set E} (hAB : A ⊆ B)
    (hBX : B ⊆ X) (h : IsStrongDeformationRetract ((↑) ⁻¹' B : Set X)) (n : ℕ) :
    IsIso ((relHomology R n).map
      (subsetPairHom hAB (hAB.trans hBX) (subset_refl A) hBX)) :=
  have : IsIso (TopPair.Hom.snd (subsetPairHom hAB (hAB.trans hBX) (subset_refl A) hBX)) := by
    change IsIso (𝟙 (TopCat.of A))
    infer_instance
  isIso_relHomology_map R (subsetPairHom hAB (hAB.trans hBX) (subset_refl A) hBX)
    (fun _ ↦ inferInstance) (fun m ↦ isIso_homologyMap_of_isStrongDeformationRetract R hBX h m) n

/-- The isomorphism `H_n(B, A) ≅ H_n(X, A)` for a strong deformation retract `B` of `X`
containing `A`. -/
def relHomologyIsoOfIsStrongDeformationRetract {A B X : Set E} (hAB : A ⊆ B) (hBX : B ⊆ X)
    (h : IsStrongDeformationRetract ((↑) ⁻¹' B : Set X)) (n : ℕ) :
    (relHomology R n).obj (subsetPair hAB) ≅ (relHomology R n).obj (subsetPair (hAB.trans hBX)) :=
  have := isIso_relHomology_map_of_isStrongDeformationRetract R hAB hBX h n
  asIso ((relHomology R n).map (subsetPairHom hAB (hAB.trans hBX) (subset_refl A) hBX))

/-- If `B ⊆ X` is a strong deformation retract of `X`, then `H_n(X, B) = 0`. -/
theorem isZero_relHomology_of_isStrongDeformationRetract {B X : Set E} (hBX : B ⊆ X)
    (h : IsStrongDeformationRetract ((↑) ⁻¹' B : Set X)) (n : ℕ) :
    IsZero ((relHomology R n).obj (subsetPair hBX)) :=
  isZero_relHomology_of_isIso_homologyMap R (subsetPair hBX)
    (isIso_homologyMap_of_isStrongDeformationRetract R hBX h) n

end Morse.Homology
