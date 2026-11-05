import Morse.Chapter2.CellAdjunction

/-!
Milnor, *Morse Theory*, §3, pp. 15–19 and p. 16 ("`e^λ` is attached to `M^{c-ε}` as required"),
in one coordinate patch of a Hausdorff space.

# The proof of Theorem 3.2 inside a coordinate patch

Milnor's proof of Theorem 3.2 (p. 14) has two kinds of steps. Assertions 2 and 3 use the smooth
structure of `M` (critical points of `F`, and Theorem 3.1 applied to `F`). Everything else —
the definition of `F = f - μ(ξ + 2η)` (p. 16), Assertion 1, the cell `e^λ = {ξ ≤ ε, η = 0}`, the
deformation `r_t` of Assertion 4 (pp. 18–19, Diagram 7), which is "the identity outside of `U`",
and the identification of `M^{c-ε} ∪ e^λ` with `M^{c-ε}` with a `λ`-cell attached — takes place in
the coordinate neighbourhood `U` of the critical point `p`, in which `f = c - ξ + η`, and uses only
the topology of `M`.

`Morse/Chapter2/CellAttach.lean` carries this out for `M = ℝⁿ`. This file redoes the topological
part for an arbitrary Hausdorff space `M` and an open partial homeomorphism `φ : M → X × Y` in
which `f = c - ‖x‖² + ‖y‖²` (a *Morse patch*, `Morse.IsMorsePatch`), so that it applies to manifolds
which are not open subsets of `ℝⁿ`, such as the submanifolds of Euclidean space of
`Morse/Chapter2/CellAttachSubmanifold.lean`. The computations in Morse coordinates are those of
`Morse/Chapter2/CellModel.lean`, reused as they are; the proofs below are those of
`CellAttach.lean` with `ℝⁿ` replaced by `M`. Assertion 3 (Theorem 3.1 for `F`) is a hypothesis of
the final statement `Morse.patch_theorem_3_2`.

## What Milnor's text leaves implicit (beyond what `CellAttach.lean` records)

* **Hausdorffness of `M`** is used twice: for the ellipsoid `ξ + 2η ≤ 2ε` (compact, as the image of
  a compact set under `φ⁻¹`) to be closed in `M`, which makes "`r_t` is the identity outside of
  `U`" continuous (`Morse.continuous_patchRetract`), and, in Lemma D, for the cell `e^λ` to be
  closed. A manifold in Milnor's sense (a subset of some `ℝᴷ`) is Hausdorff.
* **Lemma D** (`Exposition/Chapter2.md`, §2) for a Hausdorff space:
  `Morse.exists_isPushout_union_cell_of_t2`, the proof of `Morse.exists_isPushout_union_cell` with
  the normed space replaced by `M`.

## Main definitions and results

* `Morse.IsMorsePatch f p φ`: `p ∈ φ.source`, `φ p = 0`, `f = f(p) - ‖x‖² + ‖y‖²` on the source.
* `Morse.patchBump`, `Morse.patchF` (Milnor's `F`), `Morse.patchEllipsoid`, `Morse.patchCell`
  (Milnor's `e^λ`), `Morse.patchRetract` (Milnor's `r_t`).
* Assertion 1: `Morse.sublevel_patchF_add`. Assertion 4:
  `Morse.isStrongDeformationRetract_patch_handle`.
* `Morse.patch_theorem_3_2`: the conclusion of Theorem 3.2, given Assertion 3.
* `Morse.exists_homotopyEquiv_pushout_of_cell`: from a strong deformation retraction of `M^b` onto
  `M^a ∪ e^λ` to a homotopy equivalence of `M^b` with the pushout `D^λ ⊔_{S^{λ-1}} M^a`.
-/

open Set Filter Topology Function CategoryTheory Limits TopCat
open scoped unitInterval

universe u

noncomputable section

namespace Morse

open CellModel

section Patch

variable {M : Type u} [TopologicalSpace M]
  {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- A **Morse patch** at `p` (Lemma 2.2 as used on p. 15, for a function on a topological space):
an open partial homeomorphism `φ : M → X × Y` with `p` in its source, `φ p = 0`, and
`f = f(p) - ‖x‖² + ‖y‖²` throughout the source. -/
structure IsMorsePatch (f : M → ℝ) (p : M) (φ : OpenPartialHomeomorph M (X × Y)) : Prop where
  mem_source : p ∈ φ.source
  apply_self : φ p = 0
  apply_eq : ∀ q ∈ φ.source, f q = morseQuad (f p) (φ q)

/-- The correction term `μ(ξ + 2η)` of Milnor's `F` (p. 16), transported by the patch and extended
by `0` outside its source. -/
def patchBump (φ : OpenPartialHomeomorph M (X × Y)) (μ : ℝ → ℝ) : M → ℝ :=
  φ.source.indicator fun q => μ (xi (φ q) + 2 * eta (φ q))

/-- **Milnor's `F`** (p. 16): `f - μ(ξ + 2η)` within the patch, `f` outside it. -/
def patchF (f : M → ℝ) (φ : OpenPartialHomeomorph M (X × Y)) (μ : ℝ → ℝ) (q : M) : ℝ :=
  f q - patchBump φ μ q

/-- The ellipsoid `ξ + 2η ≤ 2ε` in `M`, outside of which `F = f`. -/
def patchEllipsoid (φ : OpenPartialHomeomorph M (X × Y)) (ε : ℝ) : Set M :=
  φ.symm '' ellipsoid ε

/-- **Milnor's cell** `e^λ = {ξ ≤ ε, η = 0}` in `M` (p. 15). -/
def patchCell (φ : OpenPartialHomeomorph M (X × Y)) (ε : ℝ) : Set M :=
  φ.symm '' cellModel ε

variable {f : M → ℝ} {p : M} {φ : OpenPartialHomeomorph M (X × Y)} {ε : ℝ} {μ : ℝ → ℝ}

omit [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
theorem patchEllipsoid_subset_source (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target) :
    patchEllipsoid φ ε ⊆ φ.source := by
  rintro _ ⟨v, hv, rfl⟩
  exact φ.map_target (hball (ellipsoid_subset_ball ε hv))

omit [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
theorem mem_patchEllipsoid_iff (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target) {q : M}
    (hq : q ∈ φ.source) : q ∈ patchEllipsoid φ ε ↔ φ q ∈ ellipsoid ε := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rwa [φ.right_inv (hball (ellipsoid_subset_ball ε hv))]
  · exact fun h => ⟨φ q, h, φ.left_inv hq⟩

theorem isCompact_patchEllipsoid [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target) : IsCompact (patchEllipsoid φ ε) :=
  (isCompact_ellipsoid ε).image_of_continuousOn
    (φ.continuousOn_symm.mono fun _ hv => hball (ellipsoid_subset_ball ε hv))

/-- The ellipsoid is closed in `M` (compact, and `M` is Hausdorff). -/
theorem isClosed_patchEllipsoid [T2Space M] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target) : IsClosed (patchEllipsoid φ ε) :=
  (isCompact_patchEllipsoid hball).isClosed

omit [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
theorem patchBump_eq_zero (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target)
    (hμ : IsMilnorMu ε μ) {q : M} (hq : q ∉ patchEllipsoid φ ε) : patchBump φ μ q = 0 := by
  by_cases hs : q ∈ φ.source
  · have h : φ q ∉ ellipsoid ε := fun h => hq ((mem_patchEllipsoid_iff hball hs).2 h)
    rw [patchBump, indicator_of_mem hs, hμ.eq_zero _ (le_of_lt (not_le.1 h))]
  · rw [patchBump, indicator_of_notMem hs]

omit [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
theorem patchF_eq (hφ : IsMorsePatch f p φ) {q : M} (hq : q ∈ φ.source) :
    patchF f φ μ q = morseF μ (f p) (φ q) := by
  rw [patchF, patchBump, indicator_of_mem hq, hφ.apply_eq q hq]
  rfl

omit [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
theorem patchF_eq_of_notMem (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target)
    (hμ : IsMilnorMu ε μ) {q : M} (hq : q ∉ patchEllipsoid φ ε) : patchF f φ μ q = f q := by
  rw [patchF, patchBump_eq_zero hball hμ hq, sub_zero]

omit [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
theorem patchF_le (hμ : IsMilnorMu ε μ) (q : M) : patchF f φ μ q ≤ f q :=
  sub_le_self _ (indicator_nonneg (fun _ _ => hμ.nonneg _) _)

omit [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
/-- `F(p) = c - μ(0)`. -/
theorem patchF_apply_self (hφ : IsMorsePatch f p φ) : patchF f φ μ p = f p - μ 0 := by
  rw [patchF_eq hφ hφ.mem_source, hφ.apply_self]
  simp [morseF, xi, eta]

omit [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
/-- **Assertion 1** (p. 16): `F⁻¹(-∞, c+ε] = M^{c+ε}`. -/
theorem sublevel_patchF_add (hφ : IsMorsePatch f p φ) (hμ : IsMilnorMu ε μ) :
    sublevel (patchF f φ μ) (f p + ε) = sublevel f (f p + ε) := by
  ext q
  by_cases hs : q ∈ φ.source
  · rw [mem_sublevel, mem_sublevel, patchF_eq hφ hs, hφ.apply_eq q hs]
    exact morseF_le_iff hμ _ _
  · rw [mem_sublevel, mem_sublevel, patchF, patchBump, indicator_of_notMem hs, sub_zero]

omit [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
/-- The cell lies in `F⁻¹(-∞, c-ε]` (p. 18). -/
theorem patchCell_subset_sublevel_patchF (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target)
    (hφ : IsMorsePatch f p φ) (hμ : IsMilnorMu ε μ) :
    patchCell φ ε ⊆ sublevel (patchF f φ μ) (f p - ε) := by
  rintro _ ⟨v, hv, rfl⟩
  have hvt : v ∈ φ.target := hball (ellipsoid_subset_ball ε (cellModel_subset_ellipsoid hv))
  rw [mem_sublevel, patchF_eq hφ (φ.map_target hvt), φ.right_inv hvt]
  exact (morseF_lt_of_mem_cellModel hμ _ hv).le

/-! ### Milnor's deformation `r_t` in the patch (Assertion 4) -/

open Classical in
/-- **Milnor's deformation `r_t`** (Assertion 4, p. 18): `φ⁻¹ ∘ r_t ∘ φ` within the patch, the
identity outside it. The level `δ` is `ε` for Assertion 4. -/
def patchRetract (φ : OpenPartialHomeomorph M (X × Y)) (δ t : ℝ) (q : M) : M :=
  if q ∈ φ.source then φ.symm (retractModel δ t (φ q)) else q

omit [InnerProductSpace ℝ X] in
theorem patchRetract_of_mem {δ t : ℝ} {q : M} (hq : q ∈ φ.source) :
    patchRetract φ δ t q = φ.symm (retractModel δ t (φ q)) :=
  if_pos hq

omit [InnerProductSpace ℝ X] in
theorem patchRetract_of_notMem {δ t : ℝ} {q : M} (hq : q ∉ φ.source) :
    patchRetract φ δ t q = q :=
  if_neg hq

omit [InnerProductSpace ℝ X] in
/-- On `F⁻¹(-∞, c-δ]`, `r_t` does not leave the patch: it moves only points of the ellipsoid, and
keeps them there. -/
theorem retractModel_mem_target_of_patchF_le
    (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target) (hφ : IsMorsePatch f p φ)
    (hμ : IsMilnorMu ε μ) {δ t : ℝ} {q : M} (hq : q ∈ φ.source)
    (hF : patchF f φ μ q ≤ f p - δ) (ht : t ∈ Icc (0 : ℝ) 1) :
    retractModel δ t (φ q) ∈ φ.target := by
  by_cases hE : φ q ∈ ellipsoid ε
  · exact hball (ellipsoid_subset_ball ε (retractModel_mem_ellipsoid ht hE))
  · rw [retractModel_of_notMem_ellipsoid hμ t (by rwa [← patchF_eq hφ hq]) hE]
    exact φ.map_source hq

omit [InnerProductSpace ℝ X] in
/-- `r_t` maps `F⁻¹(-∞, c-δ]` into itself (p. 19). -/
theorem patchF_patchRetract_le (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target)
    (hφ : IsMorsePatch f p φ) (hμ : IsMilnorMu ε μ) {δ t : ℝ} {q : M}
    (hF : patchF f φ μ q ≤ f p - δ) (ht : t ∈ Icc (0 : ℝ) 1) :
    patchF f φ μ (patchRetract φ δ t q) ≤ patchF f φ μ q := by
  by_cases hs : q ∈ φ.source
  · rw [patchRetract_of_mem hs]
    have hw := retractModel_mem_target_of_patchF_le hball hφ hμ hs hF ht
    rw [patchF_eq hφ (φ.map_target hw), φ.right_inv hw, patchF_eq hφ hs]
    exact morseF_retractModel_le hμ _ ht _
  · rw [patchRetract_of_notMem hs]

omit [InnerProductSpace ℝ X] in
/-- `r_0 = id`. -/
theorem patchRetract_zero (δ : ℝ) (q : M) : patchRetract φ δ 0 q = q := by
  by_cases hs : q ∈ φ.source
  · rw [patchRetract_of_mem hs, retractModel_zero, φ.left_inv hs]
  · rw [patchRetract_of_notMem hs]

omit [InnerProductSpace ℝ X] in
/-- `r_t` fixes `M^{c-δ}`. -/
theorem patchRetract_of_mem_sublevel (hφ : IsMorsePatch f p φ) {δ : ℝ} {q : M}
    (hq : f q ≤ f p - δ) (t : ℝ) : patchRetract φ δ t q = q := by
  by_cases hs : q ∈ φ.source
  · rw [patchRetract_of_mem hs, retractModel_of_morseQuad_le t (by rwa [← hφ.apply_eq q hs]),
      φ.left_inv hs]
  · rw [patchRetract_of_notMem hs]

omit [InnerProductSpace ℝ X] in
/-- `r_t` fixes `e^λ`. -/
theorem patchRetract_of_mem_patchCell (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target)
    {δ : ℝ} {q : M} (hq : q ∈ patchCell φ ε) (t : ℝ) : patchRetract φ δ t q = q := by
  obtain ⟨v, hv, rfl⟩ := hq
  have hvt : v ∈ φ.target := hball (ellipsoid_subset_ball ε (cellModel_subset_ellipsoid hv))
  rw [patchRetract_of_mem (φ.map_target hvt), φ.right_inv hvt,
    retractModel_of_snd_eq_zero δ t hv.2]

omit [InnerProductSpace ℝ X] in
/-- On `F⁻¹(-∞, c-δ]`, `r_t` is the identity outside the ellipsoid. -/
theorem patchRetract_of_notMem_patchEllipsoid
    (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target) (hφ : IsMorsePatch f p φ)
    (hμ : IsMilnorMu ε μ) {δ : ℝ} {q : M} (hF : patchF f φ μ q ≤ f p - δ)
    (hq : q ∉ patchEllipsoid φ ε) (t : ℝ) : patchRetract φ δ t q = q := by
  by_cases hs : q ∈ φ.source
  · have hE : φ q ∉ ellipsoid ε := fun h => hq ((mem_patchEllipsoid_iff hball hs).2 h)
    rw [patchRetract_of_mem hs,
      retractModel_of_notMem_ellipsoid hμ t (by rwa [← patchF_eq hφ hs]) hE, φ.left_inv hs]
  · rw [patchRetract_of_notMem hs]

omit [InnerProductSpace ℝ X] in
/-- `r_1` maps `F⁻¹(-∞, c-δ]` into `M^{c-δ} ∪ e^λ_δ` (p. 19: Case 1 goes into the cell, Case 2 into
`f⁻¹(c - δ)`, Case 3 is in `M^{c-δ}`). -/
theorem patchRetract_one_mem (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target)
    (hφ : IsMorsePatch f p φ) (hμ : IsMilnorMu ε μ) {δ : ℝ} {q : M}
    (hF : patchF f φ μ q ≤ f p - δ) :
    patchRetract φ δ 1 q ∈ sublevel f (f p - δ) ∪ patchCell φ δ := by
  by_cases hs : q ∈ φ.source
  · rw [patchRetract_of_mem hs]
    have hw := retractModel_mem_target_of_patchF_le hball hφ hμ hs hF ⟨zero_le_one, le_rfl⟩
    rcases retractModel_one_mem (f p) (φ q) with h | h
    · left
      rw [mem_sublevel, hφ.apply_eq _ (φ.map_target hw), φ.right_inv hw]
      exact h
    · exact Or.inr ⟨_, h, rfl⟩
  · left
    rw [patchRetract_of_notMem hs, mem_sublevel,
      ← patchF_eq_of_notMem (f := f) hball hμ
        (fun h => hs (patchEllipsoid_subset_source hball h))]
    exact hF

/-- **The continuity of `r_t`** on `[0, 1] × F⁻¹(-∞, c-δ]` ("let `r_t` be the identity outside of
`U`", p. 18): near a point of the patch it is `φ⁻¹ ∘ r_t ∘ φ`; near a point outside the patch,
which lies outside the closed ellipsoid, it is the identity. -/
theorem continuous_patchRetract [T2Space M] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target) (hφ : IsMorsePatch f p φ)
    (hμ : IsMilnorMu ε μ) (δ : ℝ) :
    Continuous fun z : I × sublevel (patchF f φ μ) (f p - δ) => patchRetract φ δ z.1 z.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, ⟨q₀, hq₀⟩⟩
  by_cases hs : q₀ ∈ φ.source
  · have hev : (fun z : I × sublevel (patchF f φ μ) (f p - δ) => patchRetract φ δ z.1 z.2)
        =ᶠ[𝓝 (t₀, ⟨q₀, hq₀⟩)] fun z => φ.symm (retractModel δ z.1 (φ z.2)) := by
      have ho : IsOpen {z : I × sublevel (patchF f φ μ) (f p - δ) | (z.2 : M) ∈ φ.source} :=
        φ.open_source.preimage (continuous_subtype_val.comp continuous_snd)
      filter_upwards [ho.mem_nhds hs] with z hz
      exact patchRetract_of_mem hz
    refine ContinuousAt.congr ?_ hev.symm
    have hw := retractModel_mem_target_of_patchF_le hball hφ hμ hs hq₀ t₀.2
    have h1 : ContinuousAt (fun z : I × sublevel (patchF f φ μ) (f p - δ) => (z.1, φ z.2))
        (t₀, ⟨q₀, hq₀⟩) :=
      continuousAt_fst.prodMk
        ((φ.continuousAt hs).comp (continuous_subtype_val.comp continuous_snd).continuousAt)
    have h2 : ContinuousAt
        (fun z : I × sublevel (patchF f φ μ) (f p - δ) => retractModel δ z.1 (φ z.2))
        (t₀, ⟨q₀, hq₀⟩) :=
      (continuous_retractModel δ).continuousAt.comp h1
    exact ContinuousAt.comp
      (f := fun z : I × sublevel (patchF f φ μ) (f p - δ) => retractModel δ z.1 (φ z.2))
      (φ.continuousAt_symm hw) h2
  · have hq : q₀ ∉ patchEllipsoid φ ε := fun h => hs (patchEllipsoid_subset_source hball h)
    have hev : (fun z : I × sublevel (patchF f φ μ) (f p - δ) => patchRetract φ δ z.1 z.2)
        =ᶠ[𝓝 (t₀, ⟨q₀, hq₀⟩)] fun z => (z.2 : M) := by
      have ho : IsOpen
          {z : I × sublevel (patchF f φ μ) (f p - δ) | (z.2 : M) ∉ patchEllipsoid φ ε} :=
        (isClosed_patchEllipsoid hball).isOpen_compl.preimage
          (continuous_subtype_val.comp continuous_snd)
      filter_upwards [ho.mem_nhds hq] with z hz
      exact patchRetract_of_notMem_patchEllipsoid hball hφ hμ z.2.2 hz z.1
    exact ContinuousAt.congr (continuous_subtype_val.comp continuous_snd).continuousAt hev.symm

omit [InnerProductSpace ℝ X] in
theorem patchRetract_mem (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target)
    (hφ : IsMorsePatch f p φ) (hμ : IsMilnorMu ε μ) {δ t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (q : sublevel (patchF f φ μ) (f p - δ)) :
    patchRetract φ δ t q ∈ sublevel (patchF f φ μ) (f p - δ) :=
  (patchF_patchRetract_le hball hφ hμ q.2 ht).trans q.2

/-- **Assertion 4** (pp. 18–19) in the patch: `M^{c-ε} ∪ e^λ` is a strong deformation retract of
`M^{c-ε} ∪ H = F⁻¹(-∞, c-ε]`, by Milnor's `r_t`. -/
theorem isStrongDeformationRetract_patch_handle [T2Space M] [FiniteDimensional ℝ X]
    [FiniteDimensional ℝ Y] (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target)
    (hφ : IsMorsePatch f p φ) (hμ : IsMilnorMu ε μ) :
    IsStrongDeformationRetract
      ((↑) ⁻¹' (sublevel f (f p - ε) ∪ patchCell φ ε) :
        Set (sublevel (patchF f φ μ) (f p - ε))) := by
  have hc := continuous_patchRetract hball hφ hμ ε
  let r : C(sublevel (patchF f φ μ) (f p - ε), sublevel (patchF f φ μ) (f p - ε)) :=
    ⟨fun q => ⟨patchRetract φ ε 1 q, patchRetract_mem hball hφ hμ ⟨zero_le_one, le_rfl⟩ q⟩,
      (hc.comp ((continuous_const : Continuous fun _ : sublevel (patchF f φ μ) (f p - ε) =>
        (1 : I)).prodMk continuous_id)).subtype_mk _⟩
  refine ⟨r, fun q => patchRetract_one_mem hball hφ hμ q.2, ⟨?_⟩⟩
  exact
    { toFun := fun z => ⟨patchRetract φ ε z.1 z.2, patchRetract_mem hball hφ hμ z.1.2 z.2⟩
      continuous_toFun := hc.subtype_mk _
      map_zero_left := fun q => Subtype.ext (patchRetract_zero ε (q : M))
      map_one_left := fun _ => rfl
      prop' := fun t q hq => Subtype.ext <| by
        rcases hq with hq | hq
        · exact patchRetract_of_mem_sublevel hφ hq t
        · exact patchRetract_of_mem_patchCell hball hq t }

/-! ### The cell as an embedded disk, and the conclusion -/

omit [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
/-- The ball `ξ + η ≤ 2ε` lies in the target of the patch for all small `ε` (Milnor's condition
(2), p. 15). -/
theorem exists_forall_ball_subset_patch_target (h0 : (0 : X × Y) ∈ φ.target) :
    ∃ ε₁ > 0, ∀ ε ≤ ε₁, {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target := by
  obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.1 φ.open_target 0 h0
  refine ⟨r ^ 2 / 4, by positivity, fun ε hε v hv => hrt ?_⟩
  simp only [mem_ofPred_eq, xi, eta] at hv
  have h1 : ‖v.1‖ ^ 2 < r ^ 2 := by nlinarith [sq_nonneg ‖v.2‖, sq_nonneg r]
  have h2 : ‖v.2‖ ^ 2 < r ^ 2 := by nlinarith [sq_nonneg ‖v.1‖, sq_nonneg r]
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff]
  exact ⟨lt_of_pow_lt_pow_left₀ 2 hr.le h1, lt_of_pow_lt_pow_left₀ 2 hr.le h2⟩

omit [InnerProductSpace ℝ Y] in
/-- A parametrization of Milnor's cell by the closed unit ball of `Z ≅ X`:
`χ(z) = φ⁻¹(√ε z, 0)`, with `f(χ(z)) = c - ε‖z‖²`. -/
theorem patchCell_parametrization (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target)
    (hφ : IsMorsePatch f p φ) (hε : 0 < ε) {Z : Type*} [NormedAddCommGroup Z]
    [InnerProductSpace ℝ Z] (ι : X ≃ₗᵢ[ℝ] Z) :
    let χ : Z → M := fun z => φ.symm (Real.sqrt ε • ι.symm z, 0)
    χ '' Metric.closedBall 0 1 = patchCell φ ε ∧ ContinuousOn χ (Metric.closedBall 0 1) ∧
      InjOn χ (Metric.closedBall 0 1) ∧
      (∀ z ∈ Metric.closedBall (0 : Z) 1, f (χ z) = f p - ε * ‖z‖ ^ 2) := by
  intro χ
  have hs : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.2 hε).ne'
  have hss : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hxi : ∀ z : Z, xi ((Real.sqrt ε • ι.symm z, (0 : Y)) : X × Y) = ε * ‖z‖ ^ 2 := by
    intro z
    simp only [xi, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hss,
      LinearIsometryEquiv.norm_map]
  have hmem : ∀ z ∈ Metric.closedBall (0 : Z) 1,
      ((Real.sqrt ε • ι.symm z, (0 : Y)) : X × Y) ∈ cellModel ε := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    refine ⟨?_, rfl⟩
    rw [hxi]
    have : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    nlinarith
  have htgt : ∀ z ∈ Metric.closedBall (0 : Z) 1,
      ((Real.sqrt ε • ι.symm z, (0 : Y)) : X × Y) ∈ φ.target := fun z hz =>
    hball (ellipsoid_subset_ball ε (cellModel_subset_ellipsoid (hmem z hz)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, hmem z hz, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨ι ((Real.sqrt ε)⁻¹ • v.1), ?_, ?_⟩
      · rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map, norm_smul, norm_inv,
          Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 hε), inv_mul_le_iff₀ (Real.sqrt_pos.2 hε),
          mul_one]
        have h1 : ‖v.1‖ ^ 2 ≤ ε := hv.1
        rw [← Real.sqrt_sq (norm_nonneg v.1)]
        exact Real.sqrt_le_sqrt h1
      · simp only [χ, LinearIsometryEquiv.symm_apply_apply, smul_smul, mul_inv_cancel₀ hs,
          one_smul]
        rw [show ((v.1, (0 : Y)) : X × Y) = v from Prod.ext rfl hv.2.symm]
  · exact φ.continuousOn_symm.comp (Continuous.continuousOn (by fun_prop)) htgt
  · intro z hz z' hz' h
    have h1 := φ.symm.injOn (htgt z hz) (htgt z' hz') h
    simp only [Prod.mk.injEq, and_true] at h1
    exact ι.symm.injective (smul_right_injective X hs h1)
  · intro z hz
    rw [hφ.apply_eq _ (φ.map_target (htgt z hz)), φ.right_inv (htgt z hz), morseQuad, hxi]
    simp [eta]

/-- **Theorem 3.2 in a Morse patch, given Assertion 3.** Let `M` be Hausdorff, `φ` a Morse patch
at `p` whose target contains the ball `ξ + η ≤ 2ε`, `μ` a function satisfying Milnor's conditions,
and suppose that `F⁻¹(-∞, c-ε]` is a strong deformation retract of `M^{c+ε}` (Assertion 3, which
Milnor obtains from Theorem 3.1 for `F`). Then the cell `e^λ = χ(D^λ)`, `χ(z) = φ⁻¹(√ε ι⁻¹ z, 0)`,
is continuous and injective on `D^λ`, meets `M^{c-ε}` exactly in `χ(S^{λ-1})`, lies in `M^{c+ε}`,
and `M^{c-ε} ∪ e^λ` is a strong deformation retract of `M^{c+ε}`. -/
theorem patch_theorem_3_2 [T2Space M] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] {k : ℕ}
    (ι : X ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k))
    (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target) (hφ : IsMorsePatch f p φ)
    (hμ : IsMilnorMu ε μ) (hε : 0 < ε)
    (h3 : IsStrongDeformationRetract
      ((↑) ⁻¹' sublevel (patchF f φ μ) (f p - ε) : Set (sublevel f (f p + ε)))) :
    ∃ χ : EuclideanSpace ℝ (Fin k) → M,
      ContinuousOn χ (Metric.closedBall 0 1) ∧ InjOn χ (Metric.closedBall 0 1) ∧
      (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1,
        χ z ∈ sublevel f (f p - ε) ↔ ‖z‖ = 1) ∧
      χ '' Metric.closedBall 0 1 ⊆ sublevel f (f p + ε) ∧
      IsStrongDeformationRetract
        ((↑) ⁻¹' (sublevel f (f p - ε) ∪ χ '' Metric.closedBall 0 1) :
          Set (sublevel f (f p + ε))) := by
  obtain ⟨himage, hcont, hinj, hval⟩ := patchCell_parametrization hball hφ hε ι
  refine ⟨_, hcont, hinj, fun z hz => ?_, ?_, ?_⟩
  · rw [mem_sublevel, hval z hz]
    rw [mem_closedBall_zero_iff] at hz
    constructor
    · intro h
      have : 1 ≤ ‖z‖ ^ 2 := by
        by_contra h'
        nlinarith
      nlinarith [norm_nonneg z]
    · intro h
      rw [h]
      linarith
  · rintro _ ⟨z, hz, rfl⟩
    rw [mem_sublevel, hval z hz]
    nlinarith [sq_nonneg ‖z‖]
  · rw [himage]
    have h1 : sublevel f (f p - ε) ∪ patchCell φ ε ⊆ sublevel (patchF f φ μ) (f p - ε) :=
      union_subset (fun q hq => (patchF_le hμ q).trans hq)
        (patchCell_subset_sublevel_patchF hball hφ hμ)
    have h2 : sublevel (patchF f φ μ) (f p - ε) ⊆ sublevel f (f p + ε) := by
      rw [← sublevel_patchF_add hφ hμ]
      exact sublevel_mono _ (by linarith)
    exact IsStrongDeformationRetract.trans h1 h2
      (isStrongDeformationRetract_patch_handle hball hφ hμ) h3

end Patch

/-! ### Lemma D in a Hausdorff space -/

section LemmaD

variable {M : Type u} [TopologicalSpace M] [T2Space M]

/-- **Lemma D for a cell in a Hausdorff space** (p. 16, "`e^λ` is attached to `M^{c-ε}` as
required"). Let `A ⊆ M` be closed and `χ : ℝⁿ → M` continuous and injective on the closed unit
ball `D^n`, with `χ(z) ∈ A ⟺ ‖z‖ = 1` for `z ∈ D^n`. Then `A ∪ χ(D^n)` is the pushout in `TopCat`
of `φ = χ|S^{n-1} : ∂𝔻 n → A` and `∂𝔻 n ⟶ 𝔻 n`. (The proof of `Morse.exists_isPushout_union_cell`,
which is the case of a normed space.) -/
theorem exists_isPushout_union_cell_of_t2 {A : Set M} (hA : IsClosed A) {n : ℕ}
    {χ : EuclideanSpace ℝ (Fin n) → M} (hcont : ContinuousOn χ (Metric.closedBall 0 1))
    (hinj : InjOn χ (Metric.closedBall 0 1))
    (hbdry : ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, χ z ∈ A ↔ ‖z‖ = 1) :
    ∃ (φ : ∂𝔻 n ⟶ TopCat.of A) (χ' : 𝔻 n ⟶ TopCat.of ↥(A ∪ χ '' Metric.closedBall 0 1)),
      Function.Injective φ ∧ (∀ s, (φ s : M) = χ s.down) ∧
      IsPushout φ (diskBoundaryInclusion n)
        (TopCat.ofHom ⟨inclusion subset_union_left, continuous_inclusion subset_union_left⟩)
        χ' := by
  set W := ↥(A ∪ χ '' Metric.closedBall 0 1)
  have hsub : A ⊆ A ∪ χ '' Metric.closedBall 0 1 := subset_union_left
  let j : C(A, W) := ⟨inclusion hsub, continuous_inclusion hsub⟩
  have hj : IsClosedEmbedding j :=
    ⟨IsEmbedding.inclusion hsub, by
      change IsClosed (range (inclusion hsub))
      rw [range_inclusion]
      exact hA.preimage continuous_subtype_val⟩
  let χ' : C(𝔻 n, W) :=
    ⟨fun d => ⟨χ d.down, Or.inr ⟨d.down, d.down.2, rfl⟩⟩,
      (hcont.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
        fun d => d.down.2).subtype_mk _⟩
  have hχ' : Function.Injective χ' := by
    intro d d' h
    have h' : χ d.down = χ d'.down := congrArg Subtype.val h
    exact ULift.ext _ _ (Subtype.ext (hinj d.down.2 d'.down.2 h'))
  have hmemA : ∀ s : ∂𝔻 n, χ s.down ∈ A := fun s =>
    (hbdry _ (Metric.sphere_subset_closedBall s.down.2)).2 (mem_sphere_zero_iff_norm.1 s.down.2)
  let φ : C(∂𝔻 n, A) :=
    ⟨fun s => ⟨χ s.down, hmemA s⟩,
      ((hcont.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
        fun s => Metric.sphere_subset_closedBall s.down.2)).subtype_mk _⟩
  have hφ : ∀ s, j (φ s) = χ' ((diskBoundaryInclusion n).hom s) := fun s => rfl
  have hcover : ∀ w, w ∉ range j → w ∈ range χ' := by
    rintro ⟨w, hw⟩ hw'
    rcases hw with hw | ⟨z, hz, rfl⟩
    · exact absurd ⟨⟨w, hw⟩, rfl⟩ hw'
    · exact ⟨ULift.up ⟨z, hz⟩, rfl⟩
  have hpre : ∀ d, χ' d ∈ range j → d ∈ range (diskBoundaryInclusion n).hom := by
    rintro d ⟨a, ha⟩
    have h1 : χ d.down ∈ A := by
      have := congrArg Subtype.val ha
      change (a : M) = χ d.down at this
      rw [← this]
      exact a.2
    have h2 : ‖(d.down : EuclideanSpace ℝ (Fin n))‖ = 1 := (hbdry _ d.down.2).1 h1
    exact ⟨ULift.up ⟨d.down, mem_sphere_zero_iff_norm.2 h2⟩, rfl⟩
  refine ⟨TopCat.ofHom φ, TopCat.ofHom χ', fun s s' h => ?_, fun s => rfl,
    isPushout_of_cell j hj χ' hχ' (diskBoundaryInclusion n).hom φ hφ hcover hpre⟩
  have h' : χ s.down = χ s'.down := congrArg Subtype.val h
  exact ULift.ext _ _ (Subtype.ext (hinj (Metric.sphere_subset_closedBall s.down.2)
    (Metric.sphere_subset_closedBall s'.down.2) h'))

/-- **From the cell to the attaching space** (Theorem 3.2 in Milnor's words, p. 14): if
`M^a ∪ χ(D^n)` is a strong deformation retract of `M^b` for a cell `χ(D^n) ⊆ M^b` meeting `M^a`
exactly in `χ(S^{n-1})`, then `M^b` is homotopy equivalent to the pushout of
`D^n ← S^{n-1} → M^a`, for an embedding `S^{n-1} → M^a`. -/
theorem exists_homotopyEquiv_pushout_of_cell {f : M → ℝ} (hf : Continuous f) {a b : ℝ}
    (hab : a ≤ b) {n : ℕ} {χ : EuclideanSpace ℝ (Fin n) → M}
    (hcont : ContinuousOn χ (Metric.closedBall 0 1)) (hinj : InjOn χ (Metric.closedBall 0 1))
    (hbdry : ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      χ z ∈ sublevel f a ↔ ‖z‖ = 1)
    (hsub : χ '' Metric.closedBall 0 1 ⊆ sublevel f b)
    (hsdr : IsStrongDeformationRetract
      ((↑) ⁻¹' (sublevel f a ∪ χ '' Metric.closedBall 0 1) : Set (sublevel f b))) :
    ∃ φ : ∂𝔻 n ⟶ TopCat.of (sublevel f a), Function.Injective φ ∧
      Nonempty (ContinuousMap.HomotopyEquiv (sublevel f b)
        ((pushout φ (diskBoundaryInclusion n) : TopCat.{u}) : Type u)) := by
  have h : sublevel f a ∪ χ '' Metric.closedBall 0 1 ⊆ sublevel f b :=
    union_subset (sublevel_mono f hab) hsub
  obtain ⟨e, -⟩ := hsdr.exists_homotopyEquiv h
  obtain ⟨φ, χ', hφ, -, hpo⟩ :=
    exists_isPushout_union_cell_of_t2 (isClosed_le hf continuous_const) hcont hinj hbdry
  exact ⟨φ, hφ, ⟨e.symm.trans (homeoOfIso hpo.isoPushout).toHomotopyEquiv⟩⟩

end LemmaD

end Morse
