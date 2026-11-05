import Morse.Homology.MorseHomologyBasic
import Morse.Homology.CellAttach

/-!
Milnor, *Morse Theory*, §5, p. 29 ("`H_*(M^{c+ε}, M^{c-ε}) ≅ H_*(e^λ, ė^λ)` … by excision"), with
Remark 3.3 (p. 19): the homology of several cells attached at once.

# The cell computation used by the Morse inequalities

`Morse/Homology/MorseHomology.lean` needs the homology of the cells attached at a critical level,
in the form of the property `Morse.Homology.CellAttachHomology 𝕜`
(`Morse/Homology/MorseHomologyBasic.lean`): for a closed subset `Y` of a Hausdorff space and
pairwise disjoint cells `e_j = χ_j(D^{k_j})`, `j < m`, each meeting `Y` exactly in its boundary
sphere, `H_i(Y ∪ e_1 ∪ ⋯ ∪ e_m, Y; 𝕜)` is finite-dimensional, of dimension the number of cells of
dimension `i`.

This is the cell-attachment lemma of `Morse/Homology/CellAttach.lean`
(`Morse.Homology.finrank_relHomology_cellsAttach_univ`,
`Morse.Homology.finiteDimensional_relHomology_cellsAttach`), proved there from excision for an
attached cell (`Morse/Homology/CellExcision.lean`) and the homology of `(Dᵏ, Sᵏ⁻¹)`
(`Morse/Homology/Spheres.lean`); this file only restates it as
`Morse.Homology.cellAttachHomology`.

## What Milnor leaves implicit

* **Several cells at once.**  Milnor's computation on p. 29 attaches one cell per slab (distinct
  critical values).  With Remark 3.3 several disjoint cells are attached on the same level, and
  the homology of the slab is the direct sum of their contributions.  The exact sequence of a
  triple alone only gives an inequality of dimensions; additivity uses that the cells are
  disjoint, so that each one is attached to `Y` itself (see the proof in
  `Morse/Homology/CellAttach.lean`).
* **"By excision"**: excision does not apply to the pair `(M^{c-ε} ∪ e^λ, M^{c-ε})` directly,
  since `M^{c-ε}` is closed and the closure of the excised set is not inside its interior; one
  first deforms `M^{c-ε} ∪ e^λ` minus an interior point of the cell onto `M^{c-ε}`
  (`Morse/Homology/CellExcision.lean`).
-/

open Set Metric

universe u

namespace Morse.Homology

/-- **The homology of finitely many disjoint cells attached to a closed set** (Milnor p. 29, with
Remark 3.3): the property `Morse.Homology.CellAttachHomology` holds for every field, by the
cell-attachment lemma `Morse.Homology.finrank_relHomology_cellsAttach_univ`. -/
theorem cellAttachHomology (𝕜 : Type u) [Field 𝕜] : CellAttachHomology 𝕜 := by
  intro T _ _ m k χ Y hY hχ hdisj i
  have hX : Y ∪ ⋃ j, χ j '' closedBall 0 1 =
      Y ∪ ⋃ j ∈ (Finset.univ : Finset (Fin m)), χ j '' closedBall 0 1 := by
    simp
  exact ⟨finiteDimensional_relHomology_cellsAttach 𝕜 subset_union_left hY Finset.univ
      (fun j _ ↦ (hχ j).1) (fun j _ ↦ (hχ j).2.1) (fun j _ ↦ (hχ j).2.2)
      (fun _ _ _ _ h ↦ hdisj h) hX i,
    finrank_relHomology_cellsAttach_univ 𝕜 subset_union_left hY (fun j ↦ (hχ j).1)
      (fun j ↦ (hχ j).2.1) (fun j ↦ (hχ j).2.2) hdisj rfl i⟩

end Morse.Homology
