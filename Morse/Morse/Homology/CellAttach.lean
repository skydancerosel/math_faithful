import Morse.Homology.Spheres

/-!
# The homology of a space with cells attached

Milnor (§3, Theorem 3.2 and Remark 3.3) shows that crossing a level which contains non-degenerate
critical points `p₁, …, p_m` of indices `λ₁, …, λ_m` attaches cells: `M^{c+ε}` deformation
retracts onto `M^{c-ε} ∪ e^{λ₁} ∪ ⋯ ∪ e^{λ_m}`.  In §5 (p. 29) he uses the homological
consequence: `H_i(M^{c+ε}, M^{c-ε}; F)` has dimension the number of `p_j` of index `i`.  This file
proves that consequence for cells attached to a closed subset of a Hausdorff space: **the
cell-attachment lemma**.

## One cell

Let `E` be a Hausdorff space and `Y ⊆ X ⊆ E` with `Y` closed, and let `χ : ℝᵏ → E` be continuous
and injective on the closed unit ball `Dᵏ`, with `χ(z) ∈ Y ↔ ‖z‖ = 1` and `X = Y ∪ χ(Dᵏ)` (the
form of the cell in `Morse.theorem_3_2`).  With coefficients in a commutative ring `R` in the
universe of `E` (as for excision):

* `relHomology_cellAttach_iso`: the characteristic map `χ : (Dᵏ, Sᵏ⁻¹) ⟶ (X, Y)` induces
  isomorphisms `H_i(Dᵏ, Sᵏ⁻¹; R) ≅ H_i(X, Y; R)` in all degrees; here `(Dᵏ, Sᵏ⁻¹)` is Mathlib's disk
  pair `(𝔻 k, ∂𝔻 k)` in the universe of `E` (`Morse.Homology.topDiskPair`), and
  `relHomologyCellAttachIso` is the isomorphism `H_i(X, Y; R) ≅ H_i(Dᵏ, Sᵏ⁻¹; R)`;
* `relHomologyCellAttachTopIso`: `H_k(X, Y; R) ≅ R`; `isZero_relHomology_cellAttach`:
  `H_i(X, Y; R) = 0` for `i ≠ k`;
* `finrank_relHomology_cellAttach`: over a field, `dim H_i(X, Y; 𝕜)` is `1` for `i = k` and `0`
  otherwise (and `finite_and_finrank_relHomology_cellAttach`: `H_i(X, Y; 𝕜)` is
  finite-dimensional).

## Several disjoint cells

If `X = Y ∪ ⋃_{j ∈ s} χ_j(D^{k_j})` for a finite family of such cells with pairwise disjoint
images (Milnor's Remark 3.3), then over a field `dim H_i(X, Y; 𝕜) = #{j ∈ s | k_j = i}`
(`finrank_relHomology_cellsAttach`; `finrank_relHomology_cellsAttach_univ` for cells indexed by a
finite type; `finiteDimensional_relHomology_cellsAttach`); for any `R`, `H_i(X, Y; R) ≅ Rᵐ` with
`m` the number of cells of dimension `i`, that is `H_i(X, Y; R) ≅ ⊕_j H_i(D^{k_j}, S^{k_j-1}; R)`
(`relHomology_cellsAttach_iso`), in particular `H_i(X, Y; R) = 0` if no cell has dimension `i`
(`isZero_relHomology_cellsAttach`).

## Proof

For one cell: `(χ(Dᵏ), χ(Sᵏ⁻¹)) ⟶ (X, Y)` is an isomorphism in homology by excision for an
attached cell (`Morse.Homology.isIso_relHomology_map_cellPair`,
`Morse/Homology/CellExcision.lean`), `(𝔻ᵏ, ∂𝔻ᵏ) ⟶ (χ(Dᵏ), χ(Sᵏ⁻¹))` is a homeomorphism of pairs
(`Morse.Homology.isIso_relHomology_map_diskToCell`), and the homology of `(𝔻ᵏ, ∂𝔻ᵏ)` is computed
in `Morse/Homology/Spheres.lean`.

For several cells, by induction on `s`.  Let `X_s = Y ∪ ⋃_{j ∈ s} e_j` (`cellsUnion`) and
`a ∉ s`.  Attaching `e_a` to the closed set `X_s` is a one-cell attachment, so
`H_*(X_{s ∪ {a}}, X_s)` is known.  The long exact sequence of the triple
`Y ⊆ X_s ⊆ X_{s ∪ {a}}` splits (`relHomologyCellsUnionInsertIso`,
`Morse.Homology.TopTriple.isoBiprodOfRetraction`): the composite
`(X_s, Y) ⟶ (X_{s ∪ {a}}, Y) ⟶ (X_{s ∪ {a}}, Y ∪ e_a)` is the excision of the open cell `e_a ∖ Y`,
whose closure `e_a` does not meet the other cells, hence an isomorphism, so that
`H_i(X_s, Y) ⟶ H_i(X_{s ∪ {a}}, Y)` has a retraction.  Hence
`H_i(X_{s ∪ {a}}, Y) ≅ H_i(X_s, Y) ⊞ H_i(X_{s ∪ {a}}, X_s)`.  This is where the disjointness of
the cells is used: it makes the connecting maps of the triple vanish, so that dimensions add up
instead of only satisfying the inequality given by exactness.
-/

noncomputable section

open CategoryTheory Limits Set Metric Function HomologicalComplex Module
open scoped Finset

universe w v u

namespace Morse.Homology

/-! ### A triple whose first map has a retraction -/

section TripleSplitting

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C)

/-- If, in a triple `Z ⊆ Y ⊆ X`, the maps `H_n(Y, Z) ⟶ H_n(X, Z)` have retractions in all
degrees, the long exact sequence of the triple splits into split short exact sequences, and
`H_n(X, Z) ≅ H_n(Y, Z) ⊞ H_n(X, Y)`. -/
def TopTriple.isoBiprodOfRetraction (T : TopTriple.{w})
    (r : ∀ n, (relHomology R n).obj T.pairXZ ⟶ (relHomology R n).obj T.pairYZ)
    (hr : ∀ n, (relHomology R n).map T.map₁ ≫ r n = 𝟙 _) (n : ℕ) :
    (relHomology R n).obj T.pairXZ ≅
      (relHomology R n).obj T.pairYZ ⊞ (relHomology R n).obj T.pairXY := by
  have hg : Epi ((relHomology R n).map T.map₂) := by
    cases n with
    | zero => exact T.epi_map₂_zero R
    | succ m =>
      have : Mono ((relHomology R m).map T.map₁) := mono_of_mono_fac (hr m)
      have hδ : T.δ R m = 0 :=
        (cancel_mono ((relHomology R m).map T.map₁)).1 (by rw [T.δ_comp, zero_comp])
      exact (T.exact₃ R m).epi_f hδ
  exact (ShortComplex.Splitting.ofExactOfRetraction _ (T.exact₂ R n) (r n) (hr n)
    hg).isoBinaryBiproduct

end TripleSplitting

/-! ### Attaching one cell -/

section OneCell

variable {E : Type u} [TopologicalSpace E] [T2Space E] {X Y : Set E} {k : ℕ}
  {χ : EuclideanSpace ℝ (Fin k) → E}

omit [T2Space E] in
/-- The inclusion of pairs `(χ(Dᵏ), χ(Sᵏ⁻¹)) ⟶ (X, Y)` of a cell attached to `Y`. -/
abbrev cellPairHom (hYX : Y ⊆ X) (hχY : ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1,
    χ z ∈ Y ↔ ‖z‖ = 1) (hX : X = Y ∪ χ '' closedBall 0 1) : cellPair χ ⟶ subsetPair hYX :=
  subsetPairHom (image_mono (f := χ) sphere_subset_closedBall) hYX (image_sphere_subset hχY)
    (subset_union_right.trans hX.symm.subset)

omit [T2Space E] in
/-- The characteristic map `χ : (𝔻ᵏ, ∂𝔻ᵏ) ⟶ (X, Y)` of a cell attached to `Y`, from Mathlib's
disk pair (`TopCat.disk`, `TopCat.diskBoundary`). -/
abbrev cellAttachMap (hYX : Y ⊆ X) (hχ : ContinuousOn χ (closedBall 0 1))
    (hχY : ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1, χ z ∈ Y ↔ ‖z‖ = 1)
    (hX : X = Y ∪ χ '' closedBall 0 1) : topDiskPair.{u} k ⟶ subsetPair hYX :=
  diskToCell hχ ≫ cellPairHom hYX hχY hX

variable (R : Type u) [CommRing R]

/-- **The cell-attachment lemma.** Let `X = Y ∪ χ(Dᵏ)` (subsets of a Hausdorff space `E`), where
`Y` is closed, `χ : ℝᵏ → E` is continuous and injective on the closed unit ball `Dᵏ`, and
`χ(z) ∈ Y` exactly when `‖z‖ = 1`.  Then the characteristic map `χ : (Dᵏ, Sᵏ⁻¹) ⟶ (X, Y)` induces
isomorphisms `H_i(Dᵏ, Sᵏ⁻¹; R) ≅ H_i(X, Y; R)` in all degrees (`Dᵏ, Sᵏ⁻¹` as Mathlib's
`𝔻 k, ∂𝔻 k`, in the universe of `E`). -/
theorem relHomology_cellAttach_iso (hYX : Y ⊆ X) (hY : IsClosed Y)
    (hχ : ContinuousOn χ (closedBall 0 1)) (hinj : InjOn χ (closedBall 0 1))
    (hχY : ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1, χ z ∈ Y ↔ ‖z‖ = 1)
    (hX : X = Y ∪ χ '' closedBall 0 1) (i : ℕ) :
    IsIso ((relHomology (ModuleCat.of R R) i).map (cellAttachMap hYX hχ hχY hX)) := by
  have := isIso_relHomology_map_diskToCell (ModuleCat.of R R) hχ hinj i
  have := isIso_relHomology_map_cellPair R hYX (hY.preimage continuous_subtype_val) hχ hinj hχY
    hX i
  rw [Functor.map_comp]
  infer_instance

/-- **The cell-attachment lemma**, as an isomorphism `H_i(X, Y; R) ≅ H_i(Dᵏ, Sᵏ⁻¹; R)`
(`relHomology_cellAttach_iso`). -/
def relHomologyCellAttachIso (hYX : Y ⊆ X) (hY : IsClosed Y)
    (hχ : ContinuousOn χ (closedBall 0 1)) (hinj : InjOn χ (closedBall 0 1))
    (hχY : ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1, χ z ∈ Y ↔ ‖z‖ = 1)
    (hX : X = Y ∪ χ '' closedBall 0 1) (i : ℕ) :
    (relHomology (ModuleCat.of R R) i).obj (subsetPair hYX) ≅
      (relHomology (ModuleCat.of R R) i).obj (topDiskPair.{u} k) :=
  have := relHomology_cellAttach_iso R hYX hY hχ hinj hχY hX i
  (asIso ((relHomology (ModuleCat.of R R) i).map (cellAttachMap hYX hχ hχY hX))).symm

/-- **Attaching a `k`-cell, in degree `k`**: `H_k(X, Y; R) ≅ R`. -/
def relHomologyCellAttachTopIso (hYX : Y ⊆ X) (hY : IsClosed Y)
    (hχ : ContinuousOn χ (closedBall 0 1)) (hinj : InjOn χ (closedBall 0 1))
    (hχY : ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1, χ z ∈ Y ↔ ‖z‖ = 1)
    (hX : X = Y ∪ χ '' closedBall 0 1) :
    (relHomology (ModuleCat.of R R) k).obj (subsetPair hYX) ≅ ModuleCat.of R R :=
  relHomologyCellAttachIso R hYX hY hχ hinj hχY hX k ≪≫ relHomologyTopDiskPairIso R k

/-- **Attaching a `k`-cell, outside degree `k`**: `H_i(X, Y; R) = 0` for `i ≠ k`. -/
theorem isZero_relHomology_cellAttach (hYX : Y ⊆ X) (hY : IsClosed Y)
    (hχ : ContinuousOn χ (closedBall 0 1)) (hinj : InjOn χ (closedBall 0 1))
    (hχY : ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1, χ z ∈ Y ↔ ‖z‖ = 1)
    (hX : X = Y ∪ χ '' closedBall 0 1) {i : ℕ} (hi : i ≠ k) :
    IsZero ((relHomology (ModuleCat.of R R) i).obj (subsetPair hYX)) :=
  (isZero_relHomology_topDiskPair R hi).of_iso (relHomologyCellAttachIso R hYX hY hχ hinj hχY hX i)

/-- **The cell-attachment lemma over a field**: `dim H_i(X, Y; 𝕜)` is `1` for `i = k` and `0`
otherwise, and `H_i(X, Y; 𝕜)` is finite-dimensional. -/
theorem finite_and_finrank_relHomology_cellAttach (𝕜 : Type u) [Field 𝕜] (hYX : Y ⊆ X)
    (hY : IsClosed Y) (hχ : ContinuousOn χ (closedBall 0 1)) (hinj : InjOn χ (closedBall 0 1))
    (hχY : ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1, χ z ∈ Y ↔ ‖z‖ = 1)
    (hX : X = Y ∪ χ '' closedBall 0 1) (i : ℕ) :
    Module.Finite 𝕜 ((relHomology (ModuleCat.of 𝕜 𝕜) i).obj (subsetPair hYX)) ∧
      finrank 𝕜 ((relHomology (ModuleCat.of 𝕜 𝕜) i).obj (subsetPair hYX)) =
        if i = k then 1 else 0 :=
  finite_and_finrank_eq_ite
    (fun h ↦ by subst h; exact relHomologyCellAttachTopIso 𝕜 hYX hY hχ hinj hχY hX)
    (fun h ↦ isZero_relHomology_cellAttach 𝕜 hYX hY hχ hinj hχY hX h)

/-- **The cell-attachment lemma over a field**: if `X = Y ∪ χ(Dᵏ)` is obtained from the closed
set `Y` by attaching a `k`-cell, then `dim H_i(X, Y; 𝕜)` is `1` for `i = k` and `0` otherwise. -/
theorem finrank_relHomology_cellAttach (𝕜 : Type u) [Field 𝕜] (hYX : Y ⊆ X) (hY : IsClosed Y)
    (hχ : ContinuousOn χ (closedBall 0 1)) (hinj : InjOn χ (closedBall 0 1))
    (hχY : ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1, χ z ∈ Y ↔ ‖z‖ = 1)
    (hX : X = Y ∪ χ '' closedBall 0 1) (i : ℕ) :
    finrank 𝕜 ((relHomology (ModuleCat.of 𝕜 𝕜) i).obj (subsetPair hYX)) =
      if i = k then 1 else 0 :=
  (finite_and_finrank_relHomology_cellAttach 𝕜 hYX hY hχ hinj hχY hX i).2

end OneCell

/-! ### Attaching several disjoint cells -/

section SeveralCells

variable {E : Type u} [TopologicalSpace E] [T2Space E] {Y : Set E} {α : Type*}
  {k : α → ℕ} {χ : (j : α) → EuclideanSpace ℝ (Fin (k j)) → E}

/-- `Y` with the cells `χ_j(D^{k_j})`, `j ∈ s`, attached. -/
abbrev cellsUnion (Y : Set E) (s : Finset α) (χ : (j : α) → EuclideanSpace ℝ (Fin (k j)) → E) :
    Set E :=
  Y ∪ ⋃ j ∈ s, χ j '' closedBall 0 1

omit [TopologicalSpace E] [T2Space E] in
lemma cellsUnion_insert [DecidableEq α] (s : Finset α) (a : α) :
    cellsUnion Y (insert a s) χ = cellsUnion Y s χ ∪ χ a '' closedBall 0 1 := by
  rw [cellsUnion, cellsUnion, Finset.set_biUnion_insert]
  ext x
  simp only [mem_union]
  tauto

/-- `Y ∪ ⋃_{j ∈ s} e_j` is closed: the cells are compact. -/
lemma isClosed_cellsUnion (hY : IsClosed Y) (s : Finset α)
    (hχ : ∀ j ∈ s, ContinuousOn (χ j) (closedBall 0 1)) : IsClosed (cellsUnion Y s χ) :=
  hY.union (isClosed_biUnion_finset fun j hj ↦
    ((isCompact_closedBall _ 1).image_of_continuousOn (hχ j hj)).isClosed)

omit [TopologicalSpace E] [T2Space E] in
/-- A cell disjoint from the others meets `Y ∪ ⋃_{j ∈ s} e_j` only in `Y`. -/
lemma inter_cellsUnion_subset {s : Finset α} {Z : Set E}
    (hdisj : ∀ j ∈ s, Disjoint Z (χ j '' closedBall 0 1)) :
    Z ∩ cellsUnion Y s χ ⊆ Y := by
  rintro x ⟨hxZ, hxY | hx⟩
  · exact hxY
  · simp only [mem_iUnion] at hx
    obtain ⟨j, hj, hxj⟩ := hx
    exact absurd hxj (Set.disjoint_left.1 (hdisj j hj) hxZ)

omit [TopologicalSpace E] [T2Space E] in
lemma cellsUnion_subset_insert [DecidableEq α] (s : Finset α) (a : α) :
    cellsUnion Y s χ ⊆ cellsUnion Y (insert a s) χ :=
  subset_union_left.trans (cellsUnion_insert s a).symm.subset

variable (R : Type u) [CommRing R]

/-- **Attaching one more cell, disjoint from the others, splits off its homology**: for `a ∉ s`,
`H_i(X_{s ∪ {a}}, Y) ≅ H_i(X_s, Y) ⊞ H_i(X_{s ∪ {a}}, X_s)`, where `X_s = Y ∪ ⋃_{j ∈ s} e_j`.
The long exact sequence of the triple `Y ⊆ X_s ⊆ X_{s ∪ {a}}` splits, because
`(X_s, Y) ⟶ (X_{s ∪ {a}}, Y) ⟶ (X_{s ∪ {a}}, Y ∪ e_a)` is the excision of the open cell
`e_a ∖ Y`, an isomorphism. -/
def relHomologyCellsUnionInsertIso [DecidableEq α] (s : Finset α) (a : α)
    (hχ : ContinuousOn (χ a) (closedBall 0 1))
    (hdisj : ∀ j ∈ s, Disjoint (χ a '' closedBall 0 1) (χ j '' closedBall 0 1))
    (hs : ∀ j ∈ s, ContinuousOn (χ j) (closedBall 0 1)) (i : ℕ) :
    (relHomology (ModuleCat.of R R) i).obj
        (subsetPair (subset_union_left : Y ⊆ cellsUnion Y (insert a s) χ)) ≅
      (relHomology (ModuleCat.of R R) i).obj
          (subsetPair (subset_union_left : Y ⊆ cellsUnion Y s χ)) ⊞
        (relHomology (ModuleCat.of R R) i).obj
          (subsetPair (cellsUnion_subset_insert (Y := Y) (χ := χ) s a)) := by
  set Xs := cellsUnion Y s χ with hXs_def
  set X := cellsUnion Y (insert a s) χ with hX_def
  set ea := χ a '' closedBall (0 : EuclideanSpace ℝ (Fin (k a))) 1 with hea_def
  have hXeq : X = Xs ∪ ea := cellsUnion_insert s a
  have hYXs : Y ⊆ Xs := subset_union_left
  have hXsX : Xs ⊆ X := cellsUnion_subset_insert s a
  have hYeX : Y ∪ ea ⊆ X := by
    rw [hXeq]
    exact union_subset_union_left ea hYXs
  have hea : IsClosed ea := ((isCompact_closedBall _ 1).image_of_continuousOn hχ).isClosed
  have hinter : ea ∩ Xs ⊆ Y := inter_cellsUnion_subset hdisj
  -- the excision `(X_s, Y) ⟶ (X, Y ∪ e_a)`
  have hexc : ∀ n, IsIso ((relHomology (ModuleCat.of R R) n).map
      (subsetPairHom hYXs hYeX subset_union_left hXsX)) := by
    intro n
    refine excision_of_eq R (Z := ea \ Y) hYeX hYXs subset_union_left hXsX ?_ ?_ ?_ n
    · ext x
      rw [hXeq]
      simp only [mem_union, mem_sdiff]
      constructor
      · intro hx
        refine ⟨Or.inl hx, fun h ↦ h.2 (hinter ⟨h.1, hx⟩)⟩
      · rintro ⟨hx | hx, h⟩
        · exact hx
        · exact hYXs (not_and_not_right.1 h hx)
    · ext x
      simp only [mem_union, mem_sdiff]
      tauto
    · have hU : IsOpen ((↑) ⁻¹' (⋃ j ∈ s, χ j '' closedBall 0 1)ᶜ : Set X) :=
        (isClosed_biUnion_finset fun j hj ↦ ((isCompact_closedBall _ 1).image_of_continuousOn
          (hs j hj)).isClosed).isOpen_compl.preimage continuous_subtype_val
      have hUsub : ((↑) ⁻¹' (⋃ j ∈ s, χ j '' closedBall 0 1)ᶜ : Set X) ⊆ (↑) ⁻¹' (Y ∪ ea) := by
        intro x hx
        rcases hXeq.subset x.2 with (h | h) | h
        · exact Or.inl h
        · exact absurd h hx
        · exact Or.inr h
      have heU : ((↑) ⁻¹' ea : Set X) ⊆ (↑) ⁻¹' (⋃ j ∈ s, χ j '' closedBall 0 1)ᶜ := by
        intro x hx h
        simp only [mem_iUnion] at h
        obtain ⟨j, hj, hxj⟩ := h
        exact Set.disjoint_left.1 (hdisj j hj) hx hxj
      exact (closure_minimal (fun x hx ↦ hx.1) (hea.preimage continuous_subtype_val)).trans
        (heU.trans (interior_maximal hUsub hU))
  -- the retraction of `H(X_s, Y) ⟶ H(X, Y)`
  let T := TopTriple.ofSubsets hYXs hXsX
  let π : T.pairXZ ⟶ subsetPair hYeX :=
    subsetPairHom (hYXs.trans hXsX) hYeX subset_union_left (subset_refl X)
  let ε : T.pairYZ ⟶ subsetPair hYeX := subsetPairHom hYXs hYeX subset_union_left hXsX
  have hcomp : T.map₁ ≫ π = ε := MorphismProperty.Arrow.Hom.ext rfl rfl
  let r : ∀ n, (relHomology (ModuleCat.of R R) n).obj T.pairXZ ⟶
      (relHomology (ModuleCat.of R R) n).obj T.pairYZ := fun n ↦
    (relHomology (ModuleCat.of R R) n).map π ≫
      @inv _ _ _ _ ((relHomology (ModuleCat.of R R) n).map ε) (hexc n)
  have hr : ∀ n, (relHomology (ModuleCat.of R R) n).map T.map₁ ≫ r n = 𝟙 _ := by
    intro n
    simp only [r]
    rw [← Category.assoc, ← Functor.map_comp, hcomp]
    exact @IsIso.hom_inv_id _ _ _ _ _ (hexc n)
  exact TopTriple.isoBiprodOfRetraction (ModuleCat.of R R) T r hr i

omit [TopologicalSpace E] [T2Space E] in
lemma mem_cellsUnion_iff {s : Finset α} {a : α}
    (hχY : ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin (k a))) 1, χ a z ∈ Y ↔ ‖z‖ = 1)
    (hdisj : ∀ j ∈ s, Disjoint (χ a '' closedBall 0 1) (χ j '' closedBall 0 1)) :
    ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin (k a))) 1,
      χ a z ∈ cellsUnion Y s χ ↔ ‖z‖ = 1 := by
  intro z hz
  refine ⟨fun h ↦ (hχY z hz).1 (inter_cellsUnion_subset hdisj ⟨mem_image_of_mem _ hz, h⟩),
    fun h ↦ Or.inl ((hχY z hz).2 h)⟩

omit [T2Space E] in
/-- With no cells attached, `H_i(Y, Y) = 0`. -/
lemma isZero_relHomology_cellsUnion_empty (i : ℕ) :
    IsZero ((relHomology (ModuleCat.of R R) i).obj
      (subsetPair (subset_union_left : Y ⊆ cellsUnion Y (∅ : Finset α) χ))) :=
  (isZero_relHomology_of_isIso _ (subsetPair (subset_refl Y)) i).of_iso
    ((relHomology (ModuleCat.of R R) i).mapIso (subsetPairIsoOfEq _ _ rfl (by simp)))

/-- **Attaching several disjoint cells, over a field**: `H_i(Y ∪ ⋃_{j ∈ s} e_j, Y; 𝕜)` is
finite-dimensional, of dimension the number of cells of dimension `i`. -/
theorem finite_and_finrank_relHomology_cellsUnion (𝕜 : Type u) [Field 𝕜] (hY : IsClosed Y)
    (s : Finset α) (hχ : ∀ j ∈ s, ContinuousOn (χ j) (closedBall 0 1))
    (hinj : ∀ j ∈ s, InjOn (χ j) (closedBall 0 1))
    (hχY : ∀ j ∈ s, ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin (k j))) 1, χ j z ∈ Y ↔ ‖z‖ = 1)
    (hdisj : (s : Set α).Pairwise fun j j' ↦
      Disjoint (χ j '' closedBall 0 1) (χ j' '' closedBall 0 1)) (i : ℕ) :
    Module.Finite 𝕜 ((relHomology (ModuleCat.of 𝕜 𝕜) i).obj
        (subsetPair (subset_union_left : Y ⊆ cellsUnion Y s χ))) ∧
      finrank 𝕜 ((relHomology (ModuleCat.of 𝕜 𝕜) i).obj
        (subsetPair (subset_union_left : Y ⊆ cellsUnion Y s χ))) = #{j ∈ s | k j = i} := by
  classical
  induction s using Finset.induction_on generalizing i with
  | empty =>
    have hz := isZero_relHomology_cellsUnion_empty (Y := Y) (χ := χ) 𝕜 i
    rw [Finset.filter_empty, Finset.card_empty]
    exact ⟨finite_of_isZero hz, finrank_eq_zero_of_isZero hz⟩
  | insert a s ha ih =>
    have ha' : a ∈ insert a s := Finset.mem_insert_self a s
    have hs : ∀ j ∈ s, ContinuousOn (χ j) (closedBall 0 1) :=
      fun j hj ↦ hχ j (Finset.mem_insert_of_mem hj)
    obtain ⟨hfin₁, hrank₁⟩ := ih hs (fun j hj ↦ hinj j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ hχY j (Finset.mem_insert_of_mem hj))
      (hdisj.mono (Finset.coe_subset.2 (Finset.subset_insert a s))) i
    have hdisj' : ∀ j ∈ s, Disjoint (χ a '' closedBall 0 1) (χ j '' closedBall 0 1) :=
      fun j hj ↦ hdisj ha' (Finset.mem_insert_of_mem hj) (fun h ↦ ha (by rw [h]; exact hj))
    obtain ⟨hfin₂, hrank₂⟩ := finite_and_finrank_relHomology_cellAttach 𝕜
      (cellsUnion_subset_insert s a) (isClosed_cellsUnion hY s hs) (hχ a ha') (hinj a ha')
      (mem_cellsUnion_iff (hχY a ha') hdisj') (cellsUnion_insert s a) i
    let e := relHomologyCellsUnionInsertIso 𝕜 (Y := Y) s a (hχ a ha') hdisj' hs i
    have := finite_biprod ((relHomology (ModuleCat.of 𝕜 𝕜) i).obj
      (subsetPair (subset_union_left : Y ⊆ cellsUnion Y s χ)))
      ((relHomology (ModuleCat.of 𝕜 𝕜) i).obj (subsetPair (cellsUnion_subset_insert (Y := Y)
        (χ := χ) s a)))
    refine ⟨Module.Finite.equiv e.symm.toLinearEquiv, ?_⟩
    rw [e.toLinearEquiv.finrank_eq, finrank_biprod, hrank₁, hrank₂, Finset.filter_insert]
    by_cases h : k a = i
    · rw [if_pos h, if_pos h.symm,
        Finset.card_insert_of_notMem (fun h' ↦ ha (Finset.mem_filter.1 h').1)]
    · rw [if_neg h, if_neg (Ne.symm h), add_zero]

/-- **Attaching several disjoint cells** (Milnor's Remark 3.3 situation): if
`X = Y ∪ ⋃_{j ∈ s} χ_j(D^{k_j})`, where `Y` is closed, each `χ_j` is continuous and injective on
the closed unit ball with `χ_j(z) ∈ Y ↔ ‖z‖ = 1`, and the cells are pairwise disjoint, then over a
field `dim H_i(X, Y; 𝕜)` is the number of cells of dimension `i`. -/
theorem finrank_relHomology_cellsAttach (𝕜 : Type u) [Field 𝕜] {X : Set E} (hYX : Y ⊆ X)
    (hY : IsClosed Y) (s : Finset α) (hχ : ∀ j ∈ s, ContinuousOn (χ j) (closedBall 0 1))
    (hinj : ∀ j ∈ s, InjOn (χ j) (closedBall 0 1))
    (hχY : ∀ j ∈ s, ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin (k j))) 1, χ j z ∈ Y ↔ ‖z‖ = 1)
    (hdisj : (s : Set α).Pairwise fun j j' ↦
      Disjoint (χ j '' closedBall 0 1) (χ j' '' closedBall 0 1))
    (hX : X = Y ∪ ⋃ j ∈ s, χ j '' closedBall 0 1) (i : ℕ) :
    finrank 𝕜 ((relHomology (ModuleCat.of 𝕜 𝕜) i).obj (subsetPair hYX)) = #{j ∈ s | k j = i} := by
  subst hX
  exact (finite_and_finrank_relHomology_cellsUnion 𝕜 hY s hχ hinj hχY hdisj i).2

/-- Attaching several disjoint cells: `H_i(X, Y; 𝕜)` is finite-dimensional. -/
theorem finiteDimensional_relHomology_cellsAttach (𝕜 : Type u) [Field 𝕜] {X : Set E}
    (hYX : Y ⊆ X) (hY : IsClosed Y) (s : Finset α)
    (hχ : ∀ j ∈ s, ContinuousOn (χ j) (closedBall 0 1))
    (hinj : ∀ j ∈ s, InjOn (χ j) (closedBall 0 1))
    (hχY : ∀ j ∈ s, ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin (k j))) 1, χ j z ∈ Y ↔ ‖z‖ = 1)
    (hdisj : (s : Set α).Pairwise fun j j' ↦
      Disjoint (χ j '' closedBall 0 1) (χ j' '' closedBall 0 1))
    (hX : X = Y ∪ ⋃ j ∈ s, χ j '' closedBall 0 1) (i : ℕ) :
    FiniteDimensional 𝕜 ((relHomology (ModuleCat.of 𝕜 𝕜) i).obj (subsetPair hYX)) := by
  subst hX
  exact (finite_and_finrank_relHomology_cellsUnion 𝕜 hY s hχ hinj hχY hdisj i).1

/-- **Attaching several disjoint cells, indexed by a finite type**: `dim H_i(X, Y; 𝕜)` is the
number of cells of dimension `i`. -/
theorem finrank_relHomology_cellsAttach_univ (𝕜 : Type u) [Field 𝕜] {ι : Type*} [Fintype ι]
    {k : ι → ℕ} {χ : (j : ι) → EuclideanSpace ℝ (Fin (k j)) → E} {X : Set E} (hYX : Y ⊆ X)
    (hY : IsClosed Y) (hχ : ∀ j, ContinuousOn (χ j) (closedBall 0 1))
    (hinj : ∀ j, InjOn (χ j) (closedBall 0 1))
    (hχY : ∀ j, ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin (k j))) 1, χ j z ∈ Y ↔ ‖z‖ = 1)
    (hdisj : Pairwise fun j j' ↦ Disjoint (χ j '' closedBall 0 1) (χ j' '' closedBall 0 1))
    (hX : X = Y ∪ ⋃ j, χ j '' closedBall 0 1) (i : ℕ) :
    finrank 𝕜 ((relHomology (ModuleCat.of 𝕜 𝕜) i).obj (subsetPair hYX)) = #{j | k j = i} :=
  finrank_relHomology_cellsAttach 𝕜 hYX hY Finset.univ (fun j _ ↦ hχ j) (fun j _ ↦ hinj j)
    (fun j _ ↦ hχY j) (fun _ _ _ _ h ↦ hdisj h) (by rw [hX]; simp) i

/-- If no cell has dimension `i`, then `H_i(Y ∪ ⋃_{j ∈ s} e_j, Y; R) = 0`. -/
theorem isZero_relHomology_cellsUnion (hY : IsClosed Y) (s : Finset α)
    (hχ : ∀ j ∈ s, ContinuousOn (χ j) (closedBall 0 1))
    (hinj : ∀ j ∈ s, InjOn (χ j) (closedBall 0 1))
    (hχY : ∀ j ∈ s, ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin (k j))) 1, χ j z ∈ Y ↔ ‖z‖ = 1)
    (hdisj : (s : Set α).Pairwise fun j j' ↦
      Disjoint (χ j '' closedBall 0 1) (χ j' '' closedBall 0 1)) {i : ℕ}
    (hi : ∀ j ∈ s, k j ≠ i) :
    IsZero ((relHomology (ModuleCat.of R R) i).obj
      (subsetPair (subset_union_left : Y ⊆ cellsUnion Y s χ))) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isZero_relHomology_cellsUnion_empty R i
  | insert a s ha ih =>
    have ha' : a ∈ insert a s := Finset.mem_insert_self a s
    have hs : ∀ j ∈ s, ContinuousOn (χ j) (closedBall 0 1) :=
      fun j hj ↦ hχ j (Finset.mem_insert_of_mem hj)
    have hdisj' : ∀ j ∈ s, Disjoint (χ a '' closedBall 0 1) (χ j '' closedBall 0 1) :=
      fun j hj ↦ hdisj ha' (Finset.mem_insert_of_mem hj) (fun h ↦ ha (by rw [h]; exact hj))
    have h₁ := ih hs (fun j hj ↦ hinj j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ hχY j (Finset.mem_insert_of_mem hj))
      (hdisj.mono (Finset.coe_subset.2 (Finset.subset_insert a s)))
      (fun j hj ↦ hi j (Finset.mem_insert_of_mem hj))
    have h₂ := isZero_relHomology_cellAttach R (cellsUnion_subset_insert s a)
      (isClosed_cellsUnion hY s hs) (hχ a ha') (hinj a ha')
      (mem_cellsUnion_iff (hχY a ha') hdisj') (cellsUnion_insert s a) (Ne.symm (hi a ha'))
    exact ((biprod_isZero_iff _ _).2 ⟨h₁, h₂⟩).of_iso
      (relHomologyCellsUnionInsertIso R (Y := Y) s a (hχ a ha') hdisj' hs i)

/-- **Attaching several disjoint cells, outside their dimensions**: if no cell has dimension `i`,
then `H_i(X, Y; R) = 0`. -/
theorem isZero_relHomology_cellsAttach {X : Set E} (hYX : Y ⊆ X) (hY : IsClosed Y)
    (s : Finset α) (hχ : ∀ j ∈ s, ContinuousOn (χ j) (closedBall 0 1))
    (hinj : ∀ j ∈ s, InjOn (χ j) (closedBall 0 1))
    (hχY : ∀ j ∈ s, ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin (k j))) 1, χ j z ∈ Y ↔ ‖z‖ = 1)
    (hdisj : (s : Set α).Pairwise fun j j' ↦
      Disjoint (χ j '' closedBall 0 1) (χ j' '' closedBall 0 1))
    (hX : X = Y ∪ ⋃ j ∈ s, χ j '' closedBall 0 1) {i : ℕ} (hi : ∀ j ∈ s, k j ≠ i) :
    IsZero ((relHomology (ModuleCat.of R R) i).obj (subsetPair hYX)) := by
  subst hX
  exact isZero_relHomology_cellsUnion R hY s hχ hinj hχY hdisj hi

/-- **Attaching several disjoint cells, with any coefficients**: `H_i(Y ∪ ⋃_{j ∈ s} e_j, Y; R)` is
free of rank the number of cells of dimension `i`. -/
theorem nonempty_relHomology_cellsUnion_iso (hY : IsClosed Y) (s : Finset α)
    (hχ : ∀ j ∈ s, ContinuousOn (χ j) (closedBall 0 1))
    (hinj : ∀ j ∈ s, InjOn (χ j) (closedBall 0 1))
    (hχY : ∀ j ∈ s, ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin (k j))) 1, χ j z ∈ Y ↔ ‖z‖ = 1)
    (hdisj : (s : Set α).Pairwise fun j j' ↦
      Disjoint (χ j '' closedBall 0 1) (χ j' '' closedBall 0 1)) (i : ℕ) :
    Nonempty ((relHomology (ModuleCat.of R R) i).obj
      (subsetPair (subset_union_left : Y ⊆ cellsUnion Y s χ)) ≅
        ModuleCat.of R (Fin #{j ∈ s | k j = i} → R)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : #{j ∈ (∅ : Finset α) | k j = i} = 0 := by simp
    have : Subsingleton (Fin #{j ∈ (∅ : Finset α) | k j = i} → R) := by
      rw [h0]
      infer_instance
    exact ⟨(isZero_relHomology_cellsUnion_empty R i).iso (ModuleCat.isZero_of_subsingleton _)⟩
  | insert a s ha ih =>
    have ha' : a ∈ insert a s := Finset.mem_insert_self a s
    have hs : ∀ j ∈ s, ContinuousOn (χ j) (closedBall 0 1) :=
      fun j hj ↦ hχ j (Finset.mem_insert_of_mem hj)
    have hdisj' : ∀ j ∈ s, Disjoint (χ a '' closedBall 0 1) (χ j '' closedBall 0 1) :=
      fun j hj ↦ hdisj ha' (Finset.mem_insert_of_mem hj) (fun h ↦ ha (by rw [h]; exact hj))
    obtain ⟨e₁⟩ := ih hs (fun j hj ↦ hinj j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ hχY j (Finset.mem_insert_of_mem hj))
      (hdisj.mono (Finset.coe_subset.2 (Finset.subset_insert a s)))
    let e := relHomologyCellsUnionInsertIso R (Y := Y) s a (hχ a ha') hdisj' hs i
    have hnot : a ∉ ({j ∈ s | k j = i} : Finset α) := fun h ↦ ha (Finset.mem_filter.1 h).1
    by_cases h : k a = i
    · have e₂ : (relHomology (ModuleCat.of R R) i).obj
          (subsetPair (cellsUnion_subset_insert (Y := Y) (χ := χ) s a)) ≅ ModuleCat.of R R := by
        subst h
        exact relHomologyCellAttachTopIso R (cellsUnion_subset_insert s a)
          (isClosed_cellsUnion hY s hs) (hχ a ha') (hinj a ha')
          (mem_cellsUnion_iff (hχY a ha') hdisj') (cellsUnion_insert s a)
      have hcard : #{j ∈ insert a s | k j = i} = #{j ∈ s | k j = i} + 1 := by
        rw [Finset.filter_insert, if_pos h, Finset.card_insert_of_notMem hnot]
      exact ⟨e ≪≫ biprod.mapIso e₁ e₂ ≪≫ ModuleCat.biprodIsoProd _ _ ≪≫
        ((LinearEquiv.prodComm R _ _).trans ((Fin.consLinearEquiv R fun _ ↦ R).trans
          (LinearEquiv.funCongrLeft R R (finCongr hcard)))).toModuleIso⟩
    · have h₂ := isZero_relHomology_cellAttach R (cellsUnion_subset_insert s a)
        (isClosed_cellsUnion hY s hs) (hχ a ha') (hinj a ha')
        (mem_cellsUnion_iff (hχY a ha') hdisj') (cellsUnion_insert s a) (Ne.symm h)
      have hcard : #{j ∈ insert a s | k j = i} = #{j ∈ s | k j = i} := by
        rw [Finset.filter_insert, if_neg h]
      exact ⟨e ≪≫ (isoBiprodZero h₂).symm ≪≫ e₁ ≪≫
        (LinearEquiv.funCongrLeft R R (finCongr hcard)).toModuleIso⟩

/-- **Attaching several disjoint cells, with any coefficients** (Milnor's Remark 3.3 situation):
if `X = Y ∪ ⋃_{j ∈ s} χ_j(D^{k_j})` with pairwise disjoint cells attached to the closed set `Y`,
then `H_i(X, Y; R) ≅ Rᵐ`, where `m` is the number of cells of dimension `i`, i.e.
`H_i(X, Y; R) ≅ ⊕_j H_i(D^{k_j}, S^{k_j - 1}; R)`. -/
theorem relHomology_cellsAttach_iso {X : Set E} (hYX : Y ⊆ X) (hY : IsClosed Y) (s : Finset α)
    (hχ : ∀ j ∈ s, ContinuousOn (χ j) (closedBall 0 1))
    (hinj : ∀ j ∈ s, InjOn (χ j) (closedBall 0 1))
    (hχY : ∀ j ∈ s, ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin (k j))) 1, χ j z ∈ Y ↔ ‖z‖ = 1)
    (hdisj : (s : Set α).Pairwise fun j j' ↦
      Disjoint (χ j '' closedBall 0 1) (χ j' '' closedBall 0 1))
    (hX : X = Y ∪ ⋃ j ∈ s, χ j '' closedBall 0 1) (i : ℕ) :
    Nonempty ((relHomology (ModuleCat.of R R) i).obj (subsetPair hYX) ≅
      ModuleCat.of R (Fin #{j ∈ s | k j = i} → R)) := by
  subst hX
  exact nonempty_relHomology_cellsUnion_iso R hY s hχ hinj hχY hdisj i

end SeveralCells

end Morse.Homology
