import Milnor.Chapter8.LinkDegree
import Milnor.Chapter8.LinkingSphere
import Milnor.Chapter8.Generic
import Milnor.Chapter8.NearMaps

/-!
# The Hopf invariant (Milnor §8, Problem 14)

For a smooth map `f : S^{2p−1} → S^p` and distinct regular values `y ≠ z`, the preimages
`f⁻¹(y)`, `f⁻¹(z)` are oriented as in §5, so their linking number in the sphere is defined.
Problem 14 asks to show: a) it is locally constant in `y`; b) if `y, z` are also regular values of
`g` and `‖f(x) − g(x)‖ < ‖y − z‖` for all `x`, then
`l(f⁻¹(y), f⁻¹(z)) = l(g⁻¹(y), f⁻¹(z)) = l(g⁻¹(y), g⁻¹(z))`; c) it depends neither on `y, z`
nor on the homotopy class of `f`.  This integer is the Hopf invariant `H(f)`.

Here `p = d + 1` with `d ≥ 1`, and `S^{2d+1}` is `Sph (d + (d + 1))`.

* `linkPre hg hy hf hz`: the linking number in the sphere (`linkingNumberSph`, Problem 13) of
  `g⁻¹(y)` and `f⁻¹(z)`, with the preimage orientations `preimOr` for the positive bases `posB`
  (Milnor's §5 orientation: the sign `(-1)^(d p)` of `PreimOrient.lean` is `+1` for `p = d + 1`).
* `linkPre_eq_linkingNumberRot`: the bridge to `LinkDegree.lean` (any admissible rotation).
* `linkPre_comp_posDiffeo`, `linkPre_rotS_left`, `linkPre_rotS_right`: transport by
  orientation-preserving diffeomorphisms (rotations) of the target.
* `linkPre_eq_of_homotopy`: the engine `linkingNumberRot_eq_of_homotopy` stated for `linkPre`.
* `linkPre_move`, `linkPre_move_left`, `linkPre_move_right`: moving the values along rotation arcs.
* **a)** `linkPre_self_eventually_eq` (Milnor's statement), with the mixed forms
  `linkPre_eventually_eq`, `linkPre_eventually_eq_right` for two maps `g, f`.
* **b)** `linkPre_eq_of_norm_lt`.
* **c)** `hopfInvariant`, `linkPre_eq_hopfInvariant` (independence of `y, z`),
  `hopfInvariant_eq_of_smoothHomotopic` (homotopy invariance).

## Proofs

0. **Engine** (`LinkDegree.lean`): along smooth homotopies `G, F : S × ℝ → S^{d+1}` the linking
   number of `G_t⁻¹(y)` and `F_t⁻¹(z)` is constant if for `t ∈ [0, 1]` these preimages are
   disjoint and avoid `R⁻¹(north)`.  We take `R` with `R q = north` for a base point `q`
   (`exists_rotation_to_north`), so avoidance means `G_t q ≠ y`, `F_t q ≠ z`.
1. **Transport**: both linking numbers are local degrees of `Φ = phiR` at `((y, z), e)` for a
   common regular value `e` of the two linking maps, and `Φ' = ((ρ₁ × ρ₂) × id) ∘ Φ` where the
   outer map is a bijection of constant sign `1` (`degAt_comp_bij_left`).
2. **Moves**: the engine with `G_t = ρ₁(−t θ₁) ∘ g`, `F_t = ρ₂(−t θ₂) ∘ f` and fixed values, then
   transport by `ρ₁(θ₁) × ρ₂(θ₂)`.
3. **a)**: a point `q` outside both preimages (they are meagre) and short rotation arcs
   (`exists_rotation_path`) staying away from `g(q)` and from the compact set `g(f⁻¹(z))`.
4. **b)**: the normalized chord `C_t = (f + σ(t)(g − f))/|…|` is no farther from `f(x)` or `g(x)`
   than `‖f(x) − g(x)‖`, so the engine applies with `G = C`, `F = f` (resp. `G = g`, `F = C`) at a
   value `y'` near `y` (resp. `z'` near `z`) which is regular for `f` and `g`, keeps the strict
   inequality and avoids the curve `t ↦ C_t(q)` (nowhere dense); a) brings `y'` back to `y`.
   Regular values of maps from compact manifolds are open (`HopfInv.isOpen_setOf_isRegularValue`,
   proved here in any dimensions via tangent coordinates).
5. **c), independence**: the pairs `y ≠ z` form a connected set in which the regular pairs are
   dense (`eq_of_locallyConst_on_dense`); near `(y₀, z₀)` two regular pairs are joined by
   simultaneous moves avoiding `f(q)` with `f(q) ∉ {y₀, z₀}` (for constant `f` everything
   vanishes).
6. **c), homotopy invariance**: for a smooth homotopy `H` and any `q`, take distinct common regular
   values of `f` and `g` off the curve `t ↦ H(q, t)`; the engine with `G = F = H`.

## Remarks on the statements

* The mixed forms of a) and the moves need `g⁻¹(y) ∩ f⁻¹(z) = ∅` along the way (for `g ≠ f` this
  does not follow from `y ≠ z`, and without it the linking number can jump); for `g = f` it
  follows from `y ≠ z`.
* `hopfInvariant f` is `0` when `f` is not smooth.  Homotopy invariance is stated for smooth
  homotopies (`SmoothHomotopic`).

Auxiliary definitions and lemmas live in the namespace `Milnor.Problems.HopfInv`.
-/

open Set Filter Topology Function Module TopologicalSpace Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Problems

open Sphere Framed

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

namespace HopfInv

section regOpen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

/-- **The regular points of a smooth map form an open set** (any dimensions): in tangent
coordinates the derivative is continuous, the chart changes are invertible, and surjectivity is
an open condition. -/
theorem isOpen_setOf_isRegularPoint {f : M → N} (hf : ContMDiff I J ∞ f) :
    IsOpen {x | IsRegularPoint I J f x} := by
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  have hc : ContinuousAt (inTangentCoordinates I J id f (mfderiv I J f) x₀) x₀ :=
    ((hf x₀).mfderiv_const (m := 1) (WithTop.coe_le_coe.2 le_top)).continuousAt
  have h1 : ∀ᶠ x in 𝓝 x₀, x ∈ (chartAt H x₀).source :=
    (chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀)
  have h2 : ∀ᶠ x in 𝓝 x₀, f x ∈ (chartAt G (f x₀)).source :=
    hf.continuous.continuousAt.preimage_mem_nhds
      ((chartAt G (f x₀)).open_source.mem_nhds (mem_chart_source G (f x₀)))
  -- surjectivity of the coordinate expression is equivalent to regularity
  have key : ∀ x, x ∈ (chartAt H x₀).source → f x ∈ (chartAt G (f x₀)).source →
      (Surjective (inTangentCoordinates I J id f (mfderiv I J f) x₀ x) ↔
        IsRegularPoint I J f x) := by
    intro x hx hfx
    rw [inTangentCoordinates_eq_mfderiv_comp (I := I) (I' := J) (f := id) (g := f) hx hfx]
    simp only [id_eq]
    obtain ⟨A, hA⟩ := _root_.isInvertible_mfderiv_extChartAt (I := J) (x := f x₀) (y := f x)
      (by rwa [extChartAt_source])
    obtain ⟨C, hC⟩ := isInvertible_mfderivWithin_extChartAt_symm (I := I) (x := x₀)
      (y := extChartAt I x₀ x) ((extChartAt I x₀).map_source (by rwa [extChartAt_source]))
    rw [← hA, ← hC]
    unfold IsRegularPoint
    constructor
    · intro hs w
      obtain ⟨v, hv⟩ := hs (A w)
      refine ⟨C v, A.injective ?_⟩
      exact hv
    · intro hs w
      obtain ⟨v, hv⟩ := hs (A.symm w)
      obtain ⟨u, hu⟩ := C.surjective v
      refine ⟨u, ?_⟩
      show A (mfderiv I J f x (C u)) = w
      rw [hu, hv]
      exact A.apply_symm_apply w
  have h3 : ∀ᶠ x in 𝓝 x₀, Surjective (inTangentCoordinates I J id f (mfderiv I J f) x₀ x) :=
    hc.preimage_mem_nhds (Sard.isOpen_setOf_surjective.mem_nhds
      ((key x₀ (mem_chart_source H x₀) (mem_chart_source G (f x₀))).2 hx₀))
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  exact (key x hx1 hx2).1 hx3

/-- **The regular values of a smooth map from a compact manifold form an open set.** -/
theorem isOpen_setOf_isRegularValue [CompactSpace M] [T2Space N] {f : M → N}
    (hf : ContMDiff I J ∞ f) : IsOpen {y | IsRegularValue I J f y} := by
  have hc : IsClosed {x | IsRegularPoint I J f x}ᶜ := (isOpen_setOf_isRegularPoint hf).isClosed_compl
  have heq : {y | IsRegularValue I J f y} = (f '' {x | IsRegularPoint I J f x}ᶜ)ᶜ := by
    ext y
    simp only [mem_ofPred_eq, mem_compl_iff, mem_image, not_exists, not_and, IsRegularValue]
    constructor
    · intro h x hx hfx
      exact hx (h x hfx)
    · intro h x hfx
      by_contra hc
      exact h x hc hfx
  rw [heq]
  exact ((hc.isCompact.image hf.continuous).isClosed).isOpen_compl

end regOpen

end HopfInv

variable {d : ℕ}

/-! ### The linking number of two preimages -/

/-- A positive basis of `T_y S^{d+1}` for Milnor's orientation `sphOrStd` (any positive basis gives
the same preimage orientation, `preimOr_eq_of_orientation_eq`). -/
def posB (y : Sph (d + 1)) : Basis (Fin (d + 1)) ℝ (𝔼 (d + 1)) :=
  Classical.choose (exists_basis_orientation_sphOrStd (Nat.le_add_left 1 d) y)

theorem posB_orientation (y : Sph (d + 1)) : (posB y).orientation = (sphOrStd (d + 1)).or y :=
  Classical.choose_spec (exists_basis_orientation_sphOrStd (Nat.le_add_left 1 d) y)

/-- **`l(g⁻¹(y), f⁻¹(z))`**: the linking number in the sphere `S^{2d+1}` (Problem 13) of the
preimages of regular values `y` of `g` and `z` of `f`, oriented as in §5 (`preimOr`). -/
def linkPre {g f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {z : Sph (d + 1)}
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z) : ℤ :=
  letI := (isSliceSubmanifold_preim hg hy).chartedSpace
  haveI := (isSliceSubmanifold_preim hg hy).isManifold
  letI := (isSliceSubmanifold_preim hf hz).chartedSpace
  haveI := (isSliceSubmanifold_preim hf hz).isManifold
  linkingNumberSph rfl (preimOr hg hy (posB y) (posB_orientation y))
    (preimOr hf hz (posB z) (posB_orientation z)) Subtype.val Subtype.val

/-- `linkPre` only depends on the maps and the values. -/
theorem linkPre_congr {g g' f f' : Sph (d + (d + 1)) → Sph (d + 1)} {y y' z z' : Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g)
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f)
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z)
    (hg' : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g')
    (hy' : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g' y')
    (hf' : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f')
    (hz' : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f' z')
    (h₁ : g = g') (h₂ : y = y') (h₃ : f = f') (h₄ : z = z') :
    linkPre hg hy hf hz = linkPre hg' hy' hf' hz' := by
  subst h₁ h₂ h₃ h₄
  rfl

/-- A rotation of `ℝ^{k+2}` sending a given point of `S^{k+1}` to the north pole. -/
theorem exists_rotation_to_north {k : ℕ} (q : Sph (k + 1)) :
    ∃ R : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2), IsRotation R ∧ R q.1 = (north : Sph (k + 1)).1 := by
  obtain ⟨u, v, θ₀, hu, hv, huv, -, -, hrot, -⟩ :=
    exists_rotation_path (by omega : 1 ≤ k + 1) q north
  exact ⟨LinkSph.rotLIE hu hv huv θ₀, LinkSph.isRotation_rotLIE hu hv huv θ₀, hrot⟩

namespace HopfInv

/-- The preimage of a regular value is meagre (a submanifold of smaller dimension). -/
theorem isMeagre_preim {g : Sph (d + (d + 1)) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y) : IsMeagre (g ⁻¹' {y}) := by
  let _ := (isSliceSubmanifold_preim hg hy).chartedSpace
  have _ := (isSliceSubmanifold_preim hg hy).isManifold
  have h := isMeagre_image_of_finrank_lt (I := 𝓘(ℝ, 𝔼 d)) (J := 𝓘(ℝ, 𝔼 (d + (d + 1))))
    (P := g ⁻¹' {y}) (g := Subtype.val)
    (by rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]; omega) isOpen_univ
    (isSliceSubmanifold_preim hg hy).contMDiff_val.contMDiffOn
  rwa [image_univ, Subtype.range_coe] at h

/-- A point outside two preimages of regular values. -/
theorem exists_ne_ne {g f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {z : Sph (d + 1)}
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z) :
    ∃ q, g q ≠ y ∧ f q ≠ z := by
  obtain ⟨q, -, hq⟩ := exists_mem_open_not_mem_of_isMeagre isOpen_univ univ_nonempty
    ((isMeagre_preim hg hy).union (isMeagre_preim hf hz))
  simp only [mem_union, mem_preimage, mem_singleton_iff, not_or] at hq
  exact ⟨q, hq⟩

end HopfInv

/-- **Bridge to `LinkDegree.lean`**: for any rotation `R` moving the preimages off the north pole,
`linkPre` is the linking number `linkingNumberRot` computed with `R`. -/
theorem linkPre_eq_linkingNumberRot (hd : 1 ≤ d) {g f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {z : Sph (d + 1)}
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z)
    {R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2)} (hR : IsRotation R)
    (hRy : ∀ x, g x = y → R x.1 ≠ (north : Sph (d + d + 1)).1)
    (hRz : ∀ x, f x = z → R x.1 ≠ (north : Sph (d + d + 1)).1)
    (hdisj : ∀ x, g x = y → f x ≠ z) :
    letI := (isSliceSubmanifold_preim hg hy).chartedSpace
    haveI := (isSliceSubmanifold_preim hg hy).isManifold
    letI := (isSliceSubmanifold_preim hf hz).chartedSpace
    haveI := (isSliceSubmanifold_preim hf hz).isManifold
    linkPre hg hy hf hz = linkingNumberRot rfl (preimOr hg hy (posB y) (posB_orientation y))
      (preimOr hf hz (posB z) (posB_orientation z)) Subtype.val Subtype.val R := by
  let _ := (isSliceSubmanifold_preim hg hy).chartedSpace
  have _ := (isSliceSubmanifold_preim hg hy).isManifold
  let _ := (isSliceSubmanifold_preim hf hz).chartedSpace
  have _ := (isSliceSubmanifold_preim hf hz).isManifold
  have : CompactSpace (g ⁻¹' {y}) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hg.continuous).isCompact
  have : CompactSpace (f ⁻¹' {z}) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hf.continuous).isCompact
  exact linkingNumberSph_eq rfl hd hd (isSliceSubmanifold_preim hg hy).contMDiff_val
    (isSliceSubmanifold_preim hf hz).contMDiff_val
    (fun a b h => hdisj a.1 a.2 (by rw [h]; exact b.2)) hR
    (fun a b => ⟨hRy a.1 a.2, hRz b.1 b.2⟩)

/-- `linkPre` vanishes when the first preimage is empty. -/
theorem linkPre_eq_zero_of_forall_ne {g f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {z : Sph (d + 1)}
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z) (h : ∀ x, g x ≠ y) :
    linkPre hg hy hf hz = 0 := by
  let _ := (isSliceSubmanifold_preim hg hy).chartedSpace
  have _ := (isSliceSubmanifold_preim hg hy).isManifold
  let _ := (isSliceSubmanifold_preim hf hz).chartedSpace
  have _ := (isSliceSubmanifold_preim hf hz).isManifold
  have : IsEmpty (g ⁻¹' {y} × f ⁻¹' {z}) := ⟨fun p => h p.1.1 p.1.2⟩
  show linkingNumberSph rfl (preimOr hg hy (posB y) (posB_orientation y))
    (preimOr hf hz (posB z) (posB_orientation z)) Subtype.val Subtype.val = 0
  unfold linkingNumberSph
  split_ifs with hR
  · unfold linkingNumberRot linkingNumber deg
    split_ifs with he
    · unfold degAt
      exact finsum_of_isEmpty _
    · rfl
  · rfl

/-! ### Transport by orientation-preserving diffeomorphisms of the target -/

namespace HopfInv

/-- Postcomposition with a rotation of the target preserves regular values. -/
theorem isRegularValue_rotS_comp {u v : 𝔼 (d + 1 + 1)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫ = 0) (θ : ℝ) {g : Sph (d + (d + 1)) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {w : Sph (d + 1)}
    (hw : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g w) :
    IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (fun x => rotS u v θ (g x))
      (rotS u v θ w) := by
  intro x hx
  have hgx : g x = w := by
    have h := congrArg (rotS u v (-θ)) hx
    simpa only [rotS_neg_rotS hu hv huv] using h
  have h1 := hasMFDerivAt_mfd (I := 𝓘(ℝ, 𝔼 (d + 1))) (J := 𝓘(ℝ, 𝔼 (d + 1)))
    ((contMDiff_rotS hu hv huv θ).mdifferentiableAt (by simp) :
      MDifferentiableAt _ _ (rotS u v θ) (g x))
  have h2 := hasMFDerivAt_mfd (I := 𝓘(ℝ, 𝔼 (d + (d + 1)))) (J := 𝓘(ℝ, 𝔼 (d + 1)))
    (hg.mdifferentiableAt (by simp) : MDifferentiableAt _ _ g x)
  have h3 := HasMFDerivAt.mfd_eq (h1.comp x h2)
  have h4 : (rotS u v θ ∘ g) = fun x => rotS u v θ (g x) := rfl
  rw [h4] at h3
  show Surjective (mfd 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (fun x => rotS u v θ (g x)) x)
  rw [h3]
  intro c
  obtain ⟨a, ha⟩ := (mfd_rotS_bijective hu hv huv θ (g x)).2 c
  obtain ⟨b, hb⟩ := hw x hgx a
  exact ⟨b, (congrArg (mfd 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) (rotS u v θ) (g x)) hb).trans ha⟩

/-- An orientation-preserving diffeomorphism of `S^{d+1}` (for `sphOrStd`), in the form needed for
`degAt_comp_bij_left`. -/
structure IsPosDiffeo (ρ : Sph (d + 1) → Sph (d + 1)) : Prop where
  smooth : ContMDiff 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) ∞ ρ
  bij : Bijective ρ
  sign : ∀ w, signAt (sphOrStd (d + 1)) (sphOrStd (d + 1)) ρ w = 1

theorem isPosDiffeo_id : IsPosDiffeo (d := d) id :=
  ⟨contMDiff_id, bijective_id, fun w => signAt_id _ w⟩

theorem isPosDiffeo_rotS {u v : 𝔼 (d + 1 + 1)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫ = 0) (θ : ℝ) : IsPosDiffeo (rotS u v θ) where
  smooth := contMDiff_rotS hu hv huv θ
  bij := ⟨fun a b h => by
      have h' := congrArg (rotS u v (-θ)) h
      simpa only [rotS_neg_rotS hu hv huv] using h',
    fun b => ⟨rotS u v (-θ) b, rotS_rotS_neg hu hv huv θ b⟩⟩
  sign w := by
    rcases sphOrStd_eq_or_neg (Nat.succ_pos d) with h | h
    · rw [h]; exact signAt_rotS hu hv huv θ w
    · rw [h, signAt_neg_left hZ, signAt_neg_right hZ hZ, neg_neg]
      exact signAt_rotS hu hv huv θ w

end HopfInv

/-- **Transport**: composing both maps with orientation-preserving diffeomorphisms `ρ₁, ρ₂` of
`S^{d+1}` and moving the values accordingly does not change the linking number.  Both sides are
local degrees of `Φ = phiR` at `((y, z), e)` (`degAt_phiR_eq_linkingNumberRot`), and
`Φ' = ((ρ₁ × ρ₂) × id) ∘ Φ`. -/
theorem linkPre_comp_posDiffeo (hd : 1 ≤ d) {g f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {z : Sph (d + 1)}
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z)
    {ρ₁ ρ₂ : Sph (d + 1) → Sph (d + 1)} (h₁ : HopfInv.IsPosDiffeo ρ₁)
    (h₂ : HopfInv.IsPosDiffeo ρ₂)
    (hg' : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (ρ₁ ∘ g))
    (hy' : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (ρ₁ ∘ g) (ρ₁ y))
    (hf' : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (ρ₂ ∘ f))
    (hz' : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (ρ₂ ∘ f) (ρ₂ z))
    (hdisj : ∀ x, g x = y → f x ≠ z) :
    linkPre hg' hy' hf' hz' = linkPre hg hy hf hz := by
  have hiff₁ : ∀ x, (ρ₁ ∘ g) x = ρ₁ y ↔ g x = y := fun x => h₁.bij.1.eq_iff
  have hiff₂ : ∀ x, (ρ₂ ∘ f) x = ρ₂ z ↔ f x = z := fun x => h₂.bij.1.eq_iff
  -- a rotation `R` moving a point outside both preimages to the north pole
  obtain ⟨q, hqg, hqf⟩ := HopfInv.exists_ne_ne hg hy hf hz
  obtain ⟨R, hR, hRq⟩ := exists_rotation_to_north q
  have hRN : ∀ x : Sph (d + (d + 1)), R x.1 = (north : Sph (d + d + 1)).1 → x = q := fun x h =>
    Subtype.ext (R.injective (h.trans hRq.symm))
  have hRy : ∀ x, g x = y → R x.1 ≠ (north : Sph (d + d + 1)).1 := fun x hx h =>
    hqg (hRN x h ▸ hx)
  have hRz : ∀ x, f x = z → R x.1 ≠ (north : Sph (d + d + 1)).1 := fun x hx h =>
    hqf (hRN x h ▸ hx)
  have hRy' : ∀ x, (ρ₁ ∘ g) x = ρ₁ y → R x.1 ≠ (north : Sph (d + d + 1)).1 := fun x hx =>
    hRy x ((hiff₁ x).1 hx)
  have hRz' : ∀ x, (ρ₂ ∘ f) x = ρ₂ z → R x.1 ≠ (north : Sph (d + d + 1)).1 := fun x hx =>
    hRz x ((hiff₂ x).1 hx)
  have hdisj' : ∀ x, (ρ₁ ∘ g) x = ρ₁ y → (ρ₂ ∘ f) x ≠ ρ₂ z := fun x hx h =>
    hdisj x ((hiff₁ x).1 hx) ((hiff₂ x).1 h)
  rw [linkPre_eq_linkingNumberRot hd hg' hy' hf' hz' hR hRy' hRz' hdisj',
    linkPre_eq_linkingNumberRot hd hg hy hf hz hR hRy hRz hdisj]
  let _ := (isSliceSubmanifold_preim hg hy).chartedSpace
  have _ := (isSliceSubmanifold_preim hg hy).isManifold
  let _ := (isSliceSubmanifold_preim hf hz).chartedSpace
  have _ := (isSliceSubmanifold_preim hf hz).isManifold
  let _ := (isSliceSubmanifold_preim hg' hy').chartedSpace
  have _ := (isSliceSubmanifold_preim hg' hy').isManifold
  let _ := (isSliceSubmanifold_preim hf' hz').chartedSpace
  have _ := (isSliceSubmanifold_preim hf' hz').isManifold
  have : CompactSpace (g ⁻¹' {y}) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hg.continuous).isCompact
  have : CompactSpace (f ⁻¹' {z}) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hf.continuous).isCompact
  have : CompactSpace ((ρ₁ ∘ g) ⁻¹' {ρ₁ y}) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hg'.continuous).isCompact
  have : CompactSpace ((ρ₂ ∘ f) ⁻¹' {ρ₂ z}) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hf'.continuous).isCompact
  have hd1 : ∀ x x', g x = y → f x' = z → x ≠ x' := fun x x' hx hx' h =>
    hdisj x hx (h ▸ hx')
  have hd2 : ∀ x x', (ρ₁ ∘ g) x = ρ₁ y → (ρ₂ ∘ f) x' = ρ₂ z → x ≠ x' := fun x x' hx hx' h =>
    hdisj' x hx (h ▸ hx')
  -- a common regular value `e` of the two linking maps
  have hr1 := dense_isOpen_regularValues (finrank_prod_eq hZ hZ) hZ
    (((preimOr hg hy (posB y) (posB_orientation y)).prod hZ hZ
      (preimOr hf hz (posB z) (posB_orientation z))).cast rfl)
    (sphOrStd (d + d)) (LinkDeg.contMDiff_linkMap_preim hg hf hy hz hd1 R hRy hRz)
  have hr2 := dense_isOpen_regularValues (finrank_prod_eq hZ hZ) hZ
    (((preimOr hg' hy' (posB (ρ₁ y)) (posB_orientation _)).prod hZ hZ
      (preimOr hf' hz' (posB (ρ₂ z)) (posB_orientation _))).cast rfl)
    (sphOrStd (d + d)) (LinkDeg.contMDiff_linkMap_preim hg' hf' hy' hz' hd2 R hRy' hRz')
  obtain ⟨e, he1, he2⟩ := (hr1.1.inter_of_isOpen_left hr2.1 hr1.2).nonempty
  rw [← degAt_phiR_eq_linkingNumberRot hd hf' hg' hy' hz' (posB (ρ₁ y)) (posB_orientation _)
      (posB (ρ₂ z)) (posB_orientation _) hd2 hR hRy' hRz' he2,
    ← degAt_phiR_eq_linkingNumberRot hd hf hg hy hz (posB y) (posB_orientation y)
      (posB z) (posB_orientation z) hd1 hR hRy hRz he1]
  -- `Φ' = h ∘ Φ` for `h = (ρ₁ × ρ₂) × id`, a bijection of constant sign `1`
  have hh : ContMDiff ((𝓘(ℝ, 𝔼 (d + 1)).prod 𝓘(ℝ, 𝔼 (d + 1))).prod 𝓘(ℝ, 𝔼 (d + d)))
      ((𝓘(ℝ, 𝔼 (d + 1)).prod 𝓘(ℝ, 𝔼 (d + 1))).prod 𝓘(ℝ, 𝔼 (d + d))) ∞
      (Prod.map (Prod.map ρ₁ ρ₂) (id : Sph (d + d) → Sph (d + d))) :=
    (h₁.smooth.prodMap h₂.smooth).prodMap contMDiff_id
  have hρd : ∀ w : Sph (d + 1) × Sph (d + 1),
      MDifferentiableAt ((𝓘(ℝ, 𝔼 (d + 1))).prod 𝓘(ℝ, 𝔼 (d + 1)))
        ((𝓘(ℝ, 𝔼 (d + 1))).prod 𝓘(ℝ, 𝔼 (d + 1))) (Prod.map ρ₁ ρ₂) w := fun w =>
    (h₁.smooth.prodMap h₂.smooth).mdifferentiableAt (by simp)
  have hρ₁d : ∀ w, MDifferentiableAt 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) ρ₁ w := fun w =>
    h₁.smooth.mdifferentiableAt (by simp)
  have hρ₂d : ∀ w, MDifferentiableAt 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) ρ₂ w := fun w =>
    h₂.smooth.mdifferentiableAt (by simp)
  have hidd : ∀ w : Sph (d + d), MDifferentiableAt 𝓘(ℝ, 𝔼 (d + d)) 𝓘(ℝ, 𝔼 (d + d)) id w :=
    fun w => mdifferentiableAt_id
  have hsign : ∀ w, signAt (orTarget (d := d)) orTarget
      (Prod.map (Prod.map ρ₁ ρ₂) (id : Sph (d + d) → Sph (d + d))) w = 1 := by
    intro w
    unfold orTarget
    rw [signAt_prodMap (finrank_prod_eq hZ hZ) hZ (finrank_prod_eq hZ hZ) hZ _ _ _ _
        (hρd w.1) (hidd w.2),
      signAt_prodMap hZ hZ hZ hZ _ _ _ _ (hρ₁d w.1.1) (hρ₂d w.1.2), h₁.sign, h₂.sign, signAt_id]
    norm_num
  have hΦd : ∀ w : domR R,
      MDifferentiableAt ((𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, 𝔼 (d + (d + 1))))
        ((𝓘(ℝ, 𝔼 (d + 1)).prod 𝓘(ℝ, 𝔼 (d + 1))).prod 𝓘(ℝ, 𝔼 (d + d)))
        (phiR g f R ∘ Subtype.val) w := fun w =>
    ((contMDiffAt_phiR hg hf w.1 w.2).comp w contMDiff_subtype_val.contMDiffAt).mdifferentiableAt
      (by simp)
  have hcomp := degAt_comp_bij_left ((finrank_prod_eq hZ hZ).trans (by omega))
    (finrank_prod_eq (finrank_prod_eq hZ hZ) hZ) (orDomR R) orTarget orTarget
    ((h₁.bij.prodMap h₂.bij).prodMap bijective_id) (fun w => hh.mdifferentiableAt (by simp))
    (Or.inl rfl) hsign hΦd (y := ((y, z), e)) (z := ((ρ₁ y, ρ₂ z), e)) rfl
  rw [one_mul] at hcomp
  exact hcomp

/-- Transport by a rotation of the target in the first slot. -/
theorem linkPre_rotS_left (hd : 1 ≤ d) {g f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {z : Sph (d + 1)}
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z)
    {u v : 𝔼 (d + 1 + 1)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0) (θ : ℝ)
    (hρg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (rotS u v θ ∘ g))
    (hρy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (rotS u v θ ∘ g)
      (rotS u v θ y))
    (hdisj : ∀ x, g x = y → f x ≠ z) :
    linkPre hρg hρy hf hz = linkPre hg hy hf hz :=
  linkPre_comp_posDiffeo hd hg hy hf hz (HopfInv.isPosDiffeo_rotS hu hv huv θ)
    HopfInv.isPosDiffeo_id hρg hρy hf hz hdisj

/-- Transport by a rotation of the target in the second slot. -/
theorem linkPre_rotS_right (hd : 1 ≤ d) {g f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {z : Sph (d + 1)}
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z)
    {u v : 𝔼 (d + 1 + 1)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0) (θ : ℝ)
    (hρf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (rotS u v θ ∘ f))
    (hρz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (rotS u v θ ∘ f)
      (rotS u v θ z))
    (hdisj : ∀ x, g x = y → f x ≠ z) :
    linkPre hg hy hρf hρz = linkPre hg hy hf hz :=
  linkPre_comp_posDiffeo hd hg hy hf hz HopfInv.isPosDiffeo_id
    (HopfInv.isPosDiffeo_rotS hu hv huv θ) hg hy hρf hρz hdisj

/-! ### Homotopies and moves -/

/-- **The engine** (`linkingNumberRot_eq_of_homotopy`, stated for `linkPre`): along smooth
homotopies `G, F` whose preimages of `y` and `z` stay disjoint for `t ∈ [0, 1]` and avoid a common
base point `q`, the linking number of the preimages does not change (`y`, `z` regular only at the
ends). -/
theorem linkPre_eq_of_homotopy (hd : 1 ≤ d) {G F : Sph (d + (d + 1)) × ℝ → Sph (d + 1)}
    (hG : ContMDiff (𝓘(ℝ, 𝔼 (d + (d + 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼 (d + 1)) ∞ G)
    (hF : ContMDiff (𝓘(ℝ, 𝔼 (d + (d + 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼 (d + 1)) ∞ F)
    (hG0 : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (fun x => G (x, 0)))
    (hG1 : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (fun x => G (x, 1)))
    (hF0 : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (fun x => F (x, 0)))
    (hF1 : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (fun x => F (x, 1)))
    {y z : Sph (d + 1)}
    (hy0 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (fun x => G (x, 0)) y)
    (hy1 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (fun x => G (x, 1)) y)
    (hz0 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (fun x => F (x, 0)) z)
    (hz1 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (fun x => F (x, 1)) z)
    (hdisj : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, G (x, t) = y → F (x, t) ≠ z)
    (q : Sph (d + (d + 1))) (hq : ∀ t ∈ Icc (0 : ℝ) 1, G (q, t) ≠ y ∧ F (q, t) ≠ z) :
    linkPre hG0 hy0 hF0 hz0 = linkPre hG1 hy1 hF1 hz1 := by
  obtain ⟨R, hR, hRq⟩ := exists_rotation_to_north q
  have hRN : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, (G (x, t) = y ∨ F (x, t) = z) →
      R x.1 ≠ (north : Sph (d + d + 1)).1 := by
    intro t ht x hx h
    have hxq : x = q := Subtype.ext (R.injective (h.trans hRq.symm))
    subst hxq
    rcases hx with hx | hx
    · exact (hq t ht).1 hx
    · exact (hq t ht).2 hx
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have key := linkingNumberRot_eq_of_homotopy hd hG hF hG0 hG1 hF0 hF1 hy0 hy1 hz0 hz1
    (posB y) (posB_orientation y) (posB z) (posB_orientation z)
    (fun t ht x x' hx hx' h => hdisj t ht x hx (h ▸ hx')) hR hRN
  rw [linkPre_eq_linkingNumberRot hd hG0 hy0 hF0 hz0 hR (fun x hx => hRN 0 h0 x (Or.inl hx))
      (fun x hx => hRN 0 h0 x (Or.inr hx)) (hdisj 0 h0),
    linkPre_eq_linkingNumberRot hd hG1 hy1 hF1 hz1 hR (fun x hx => hRN 1 h1 x (Or.inl hx))
      (fun x hx => hRN 1 h1 x (Or.inr hx)) (hdisj 1 h1)]
  exact key

namespace HopfInv

/-- The rotation homotopy `G_t = ρ(-t θ) ∘ g` with `ρ(θ) = rotS u v θ`. -/
def rotHom (u v : 𝔼 (d + 1 + 1)) (θ : ℝ) (g : Sph (d + (d + 1)) → Sph (d + 1))
    (w : Sph (d + (d + 1)) × ℝ) : Sph (d + 1) :=
  rotS u v (-(w.2 * θ)) (g w.1)

theorem rotHom_apply (u v : 𝔼 (d + 1 + 1)) (θ : ℝ) (g : Sph (d + (d + 1)) → Sph (d + 1))
    (x : Sph (d + (d + 1))) (t : ℝ) : rotHom u v θ g (x, t) = rotS u v (-(t * θ)) (g x) := rfl

section rotHom

variable {u v : 𝔼 (d + 1 + 1)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0)

include hu hv huv in
theorem contMDiff_rotHom (θ : ℝ) {g : Sph (d + (d + 1)) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) :
    ContMDiff (𝓘(ℝ, 𝔼 (d + (d + 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (rotHom u v θ g) := by
  have hfam : ContMDiff (𝓘(ℝ, 𝔼 (d + 1)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼 (d + 1)) ∞
      (fun w : Sph (d + 1) × ℝ => rotS u v (-(w.2 * θ)) w.1) :=
    contMDiff_rotS_family hu hv huv (ρ := fun t => -(t * θ)) (contDiff_id.mul contDiff_const).neg
  have hΨ : ContMDiff (𝓘(ℝ, 𝔼 (d + (d + 1))).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, 𝔼 (d + 1)).prod 𝓘(ℝ, ℝ)) ∞
      (fun w : Sph (d + (d + 1)) × ℝ => (g w.1, w.2)) :=
    (hg.comp contMDiff_fst).prodMk contMDiff_snd
  have h := hfam.comp hΨ
  have heq : ((fun w : Sph (d + 1) × ℝ => rotS u v (-(w.2 * θ)) w.1) ∘
      fun w : Sph (d + (d + 1)) × ℝ => (g w.1, w.2)) = rotHom u v θ g := by
    funext w; rfl
  rw [heq] at h
  exact h

include hu hv huv in
theorem rotHom_eq_iff (θ : ℝ) (g : Sph (d + (d + 1)) → Sph (d + 1)) (x : Sph (d + (d + 1)))
    (t : ℝ) (y : Sph (d + 1)) :
    rotHom u v θ g (x, t) = y ↔ (g x).1 = rotCLM u v (t * θ) y.1 := by
  rw [rotHom_apply, ← rotS_val hu hv huv (t * θ) y, ← Subtype.ext_iff]
  constructor
  · intro h; rw [← h, rotS_rotS_neg hu hv huv]
  · intro h; rw [h, rotS_neg_rotS hu hv huv]

include hu hv huv in
theorem rotHom_zero (θ : ℝ) (g : Sph (d + (d + 1)) → Sph (d + 1)) :
    (fun x => rotHom u v θ g (x, 0)) = g := funext fun x => by
  rw [rotHom_apply, zero_mul, neg_zero, rotS_zero hu hv huv]

theorem rotHom_one (θ : ℝ) (g : Sph (d + (d + 1)) → Sph (d + 1)) :
    (fun x => rotHom u v θ g (x, 1)) = fun x => rotS u v (-θ) (g x) := funext fun x => by
  rw [rotHom_apply, one_mul]

include hu hv huv in
theorem rotS_comp_rotHom_one (θ : ℝ) (g : Sph (d + (d + 1)) → Sph (d + 1)) :
    (rotS u v θ ∘ fun x => rotHom u v θ g (x, 1)) = g := by
  rw [rotHom_one]
  funext x
  exact rotS_rotS_neg hu hv huv θ (g x)

end rotHom

end HopfInv

open HopfInv in
/-- **Moving both values along rotation arcs.**  `y` moves to `y'` along `t ↦ ρ₁(t θ₁) y` and `z`
to `z'` along `t ↦ ρ₂(t θ₂) z` (`ρᵢ(θ) = rotCLM uᵢ vᵢ θ`); if the moving preimages stay disjoint
and avoid a base point `q`, the linking number does not change.  Proof: the engine with
`G_t = ρ₁(-t θ₁) ∘ g`, `F_t = ρ₂(-t θ₂) ∘ f` and fixed values `y, z`, followed by the transport
by `ρ₁(θ₁) × ρ₂(θ₂)`. -/
theorem linkPre_move (hd : 1 ≤ d) {g f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {z : Sph (d + 1)}
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z)
    {u₁ v₁ u₂ v₂ : 𝔼 (d + 1 + 1)} (hu₁ : ‖u₁‖ = 1) (hv₁ : ‖v₁‖ = 1) (huv₁ : ⟪u₁, v₁⟫ = 0)
    (hu₂ : ‖u₂‖ = 1) (hv₂ : ‖v₂‖ = 1) (huv₂ : ⟪u₂, v₂⟫ = 0) {θ₁ θ₂ : ℝ}
    (q : Sph (d + (d + 1)))
    (hqg : ∀ t ∈ Icc (0 : ℝ) 1, (g q).1 ≠ rotCLM u₁ v₁ (t * θ₁) y.1)
    (hqf : ∀ t ∈ Icc (0 : ℝ) 1, (f q).1 ≠ rotCLM u₂ v₂ (t * θ₂) z.1)
    (hdisj : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, (g x).1 = rotCLM u₁ v₁ (t * θ₁) y.1 →
      (f x).1 ≠ rotCLM u₂ v₂ (t * θ₂) z.1)
    {y' z' : Sph (d + 1)}
    (hy' : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y')
    (hz' : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z')
    (hyy' : y'.1 = rotCLM u₁ v₁ θ₁ y.1) (hzz' : z'.1 = rotCLM u₂ v₂ θ₂ z.1) :
    linkPre hg hy hf hz = linkPre hg hy' hf hz' := by
  have hGs := contMDiff_rotHom hu₁ hv₁ huv₁ θ₁ hg
  have hFs := contMDiff_rotHom hu₂ hv₂ huv₂ θ₂ hf
  have hyρ : rotS u₁ v₁ θ₁ y = y' := Subtype.ext (by rw [rotS_val hu₁ hv₁ huv₁, hyy'])
  have hzρ : rotS u₂ v₂ θ₂ z = z' := Subtype.ext (by rw [rotS_val hu₂ hv₂ huv₂, hzz'])
  have hG0s : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞
      (fun x => rotHom u₁ v₁ θ₁ g (x, 0)) := hGs.comp (contMDiff_inl 0)
  have hG1s : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞
      (fun x => rotHom u₁ v₁ θ₁ g (x, 1)) := hGs.comp (contMDiff_inl 1)
  have hF0s : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞
      (fun x => rotHom u₂ v₂ θ₂ f (x, 0)) := hFs.comp (contMDiff_inl 0)
  have hF1s : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞
      (fun x => rotHom u₂ v₂ θ₂ f (x, 1)) := hFs.comp (contMDiff_inl 1)
  have hy0 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1))
      (fun x => rotHom u₁ v₁ θ₁ g (x, 0)) y := by
    rw [rotHom_zero hu₁ hv₁ huv₁]; exact hy
  have hz0 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1))
      (fun x => rotHom u₂ v₂ θ₂ f (x, 0)) z := by
    rw [rotHom_zero hu₂ hv₂ huv₂]; exact hz
  have hy1 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1))
      (fun x => rotHom u₁ v₁ θ₁ g (x, 1)) y := by
    rw [rotHom_one]
    have h := isRegularValue_rotS_comp hu₁ hv₁ huv₁ (-θ₁) hg hy'
    rwa [← hyρ, rotS_neg_rotS hu₁ hv₁ huv₁] at h
  have hz1 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1))
      (fun x => rotHom u₂ v₂ θ₂ f (x, 1)) z := by
    rw [rotHom_one]
    have h := isRegularValue_rotS_comp hu₂ hv₂ huv₂ (-θ₂) hf hz'
    rwa [← hzρ, rotS_neg_rotS hu₂ hv₂ huv₂] at h
  -- the engine
  have key := linkPre_eq_of_homotopy hd hGs hFs hG0s hG1s hF0s hF1s hy0 hy1 hz0 hz1
    (fun t ht x hx hx' => hdisj t ht x ((rotHom_eq_iff hu₁ hv₁ huv₁ θ₁ g x t y).1 hx)
      ((rotHom_eq_iff hu₂ hv₂ huv₂ θ₂ f x t z).1 hx')) q
    (fun t ht => ⟨fun h => hqg t ht ((rotHom_eq_iff hu₁ hv₁ huv₁ θ₁ g q t y).1 h),
      fun h => hqf t ht ((rotHom_eq_iff hu₂ hv₂ huv₂ θ₂ f q t z).1 h)⟩)
  -- the transport by `ρ₁(θ₁) × ρ₂(θ₂)`
  have hdisj1 : ∀ x, rotHom u₁ v₁ θ₁ g (x, 1) = y → rotHom u₂ v₂ θ₂ f (x, 1) ≠ z :=
    fun x hx hx' => hdisj 1 ⟨zero_le_one, le_rfl⟩ x
      ((rotHom_eq_iff hu₁ hv₁ huv₁ θ₁ g x 1 y).1 hx) ((rotHom_eq_iff hu₂ hv₂ huv₂ θ₂ f x 1 z).1 hx')
  have hGgs : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞
      (rotS u₁ v₁ θ₁ ∘ fun x => rotHom u₁ v₁ θ₁ g (x, 1)) := by
    rw [rotS_comp_rotHom_one hu₁ hv₁ huv₁]; exact hg
  have hFfs : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞
      (rotS u₂ v₂ θ₂ ∘ fun x => rotHom u₂ v₂ θ₂ f (x, 1)) := by
    rw [rotS_comp_rotHom_one hu₂ hv₂ huv₂]; exact hf
  have hGgy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1))
      (rotS u₁ v₁ θ₁ ∘ fun x => rotHom u₁ v₁ θ₁ g (x, 1)) (rotS u₁ v₁ θ₁ y) := by
    rw [rotS_comp_rotHom_one hu₁ hv₁ huv₁, hyρ]; exact hy'
  have hFfz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1))
      (rotS u₂ v₂ θ₂ ∘ fun x => rotHom u₂ v₂ θ₂ f (x, 1)) (rotS u₂ v₂ θ₂ z) := by
    rw [rotS_comp_rotHom_one hu₂ hv₂ huv₂, hzρ]; exact hz'
  have htr := linkPre_comp_posDiffeo hd hG1s hy1 hF1s hz1
    (isPosDiffeo_rotS hu₁ hv₁ huv₁ θ₁) (isPosDiffeo_rotS hu₂ hv₂ huv₂ θ₂)
    hGgs hGgy hFfs hFfz hdisj1
  calc linkPre hg hy hf hz = linkPre hG0s hy0 hF0s hz0 :=
        linkPre_congr _ _ _ _ _ _ _ _ (rotHom_zero hu₁ hv₁ huv₁ θ₁ g).symm rfl
          (rotHom_zero hu₂ hv₂ huv₂ θ₂ f).symm rfl
    _ = linkPre hG1s hy1 hF1s hz1 := key
    _ = linkPre hGgs hGgy hFfs hFfz := htr.symm
    _ = linkPre hg hy' hf hz' := linkPre_congr _ _ _ _ _ _ _ _
        (rotS_comp_rotHom_one hu₁ hv₁ huv₁ θ₁ g) hyρ (rotS_comp_rotHom_one hu₂ hv₂ huv₂ θ₂ f) hzρ

/-- **Moving the first value along a rotation arc** (`y' = ρ(θ₀) y`), with a base point `q` kept
off the moving preimages. -/
theorem linkPre_move_left (hd : 1 ≤ d) {g f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {z : Sph (d + 1)}
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z)
    {u v : 𝔼 (d + 1 + 1)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0) {θ₀ : ℝ}
    (q : Sph (d + (d + 1)))
    (hqg : ∀ t ∈ Icc (0 : ℝ) 1, (g q).1 ≠ rotCLM u v (t * θ₀) y.1) (hqf : f q ≠ z)
    (hdisj : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, (g x).1 = rotCLM u v (t * θ₀) y.1 → f x ≠ z)
    {y' : Sph (d + 1)} (hy' : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y')
    (hyy' : y'.1 = rotCLM u v θ₀ y.1) :
    linkPre hg hy hf hz = linkPre hg hy' hf hz := by
  obtain ⟨u₂, v₂, -, hu₂, hv₂, huv₂, -⟩ := exists_rotation_path (Nat.le_add_left 1 d) z z
  have hrot0 : ∀ t : ℝ, rotCLM u₂ v₂ (t * 0) z.1 = z.1 := fun t => by
    rw [mul_zero, rotCLM_zero]; rfl
  exact linkPre_move hd hg hy hf hz hu hv huv hu₂ hv₂ huv₂ (θ₂ := 0) q hqg
    (fun t _ h => hqf (Subtype.ext (h.trans (hrot0 t))))
    (fun t ht x hx h => hdisj t ht x hx (Subtype.ext (h.trans (hrot0 t)))) hy' hz hyy'
    (by rw [rotCLM_zero]; rfl)

/-- **Moving the second value along a rotation arc** (`z' = ρ(θ₀) z`). -/
theorem linkPre_move_right (hd : 1 ≤ d) {g f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {z : Sph (d + 1)}
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z)
    {u v : 𝔼 (d + 1 + 1)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0) {θ₀ : ℝ}
    (q : Sph (d + (d + 1))) (hqg : g q ≠ y)
    (hqf : ∀ t ∈ Icc (0 : ℝ) 1, (f q).1 ≠ rotCLM u v (t * θ₀) z.1)
    (hdisj : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, g x = y → (f x).1 ≠ rotCLM u v (t * θ₀) z.1)
    {z' : Sph (d + 1)} (hz' : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z')
    (hzz' : z'.1 = rotCLM u v θ₀ z.1) :
    linkPre hg hy hf hz = linkPre hg hy hf hz' := by
  obtain ⟨u₁, v₁, -, hu₁, hv₁, huv₁, -⟩ := exists_rotation_path (Nat.le_add_left 1 d) y y
  have hrot0 : ∀ t : ℝ, rotCLM u₁ v₁ (t * 0) y.1 = y.1 := fun t => by
    rw [mul_zero, rotCLM_zero]; rfl
  exact linkPre_move hd hg hy hf hz hu₁ hv₁ huv₁ hu hv huv (θ₁ := 0) q
    (fun t _ h => hqg (Subtype.ext (h.trans (hrot0 t)))) hqf
    (fun t ht x hx => hdisj t ht x (Subtype.ext (hx.trans (hrot0 t)))) hy hz'
    (by rw [rotCLM_zero]; rfl) hzz'

/-! ### Problem 14 a): local constancy -/

/-- **Problem 14 a), first value** (mixed form): if `g⁻¹(y)` and `f⁻¹(z)` are disjoint, then
`l(g⁻¹(y'), f⁻¹(z)) = l(g⁻¹(y), f⁻¹(z))` for every regular value `y'` of `g` near `y`. -/
theorem linkPre_eventually_eq (hd : 1 ≤ d) {g f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {z : Sph (d + 1)}
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z)
    (hdisj : ∀ x, g x = y → f x ≠ z) :
    ∀ᶠ y' in 𝓝 y, ∀ hy' : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y',
      linkPre hg hy' hf hz = linkPre hg hy hf hz := by
  obtain ⟨q, hqg, hqf⟩ := HopfInv.exists_ne_ne hg hy hf hz
  -- the compact set of values of `g` on `f⁻¹(z)` misses `y`
  have hK : IsClosed (g '' (f ⁻¹' {z})) :=
    ((isClosed_singleton.preimage hf.continuous).isCompact.image hg.continuous).isClosed
  have hyK : y ∉ g '' (f ⁻¹' {z}) := by
    rintro ⟨x, hx, hxy⟩
    exact hdisj x hxy hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hK.isOpen_compl y hyK
  have hq : 0 < dist (g q) y := dist_pos.2 hqg
  filter_upwards [Metric.ball_mem_nhds y (lt_min hε hq)] with y' hy'r hy'
  obtain ⟨u, v, θ₀, hu, hv, huv, -, -, hrot, hdist⟩ :=
    exists_rotation_path (Nat.le_add_left 1 d) y y'
  have hr : dist y' y < min ε (dist (g q) y) := hy'r
  have harc : ∀ t ∈ Icc (0 : ℝ) 1,
      dist (rotCLM u v (t * θ₀) y.1) y.1 < min ε (dist (g q) y) := fun t ht =>
    (hdist t ht.1 ht.2).trans_lt (by rwa [← Subtype.dist_eq])
  refine (linkPre_move_left hd hg hy hf hz hu hv huv q ?_ hqf ?_ hy' hrot.symm).symm
  · intro t ht h
    have h1 := harc t ht
    rw [← h, ← Subtype.dist_eq] at h1
    exact lt_irrefl _ (h1.trans_le (min_le_right _ _))
  · intro t ht x hx hfx
    have hmem : g x ∈ ball y ε := by
      rw [mem_ball, Subtype.dist_eq, hx]
      exact (harc t ht).trans_le (min_le_left _ _)
    exact hball hmem ⟨x, hfx, rfl⟩

/-- **Problem 14 a), second value** (mixed form). -/
theorem linkPre_eventually_eq_right (hd : 1 ≤ d) {g f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {z : Sph (d + 1)}
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z)
    (hdisj : ∀ x, g x = y → f x ≠ z) :
    ∀ᶠ z' in 𝓝 z, ∀ hz' : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z',
      linkPre hg hy hf hz' = linkPre hg hy hf hz := by
  obtain ⟨q, hqg, hqf⟩ := HopfInv.exists_ne_ne hg hy hf hz
  have hK : IsClosed (f '' (g ⁻¹' {y})) :=
    ((isClosed_singleton.preimage hg.continuous).isCompact.image hf.continuous).isClosed
  have hzK : z ∉ f '' (g ⁻¹' {y}) := by
    rintro ⟨x, hx, hxz⟩
    exact hdisj x hx hxz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hK.isOpen_compl z hzK
  have hq : 0 < dist (f q) z := dist_pos.2 hqf
  filter_upwards [Metric.ball_mem_nhds z (lt_min hε hq)] with z' hz'r hz'
  obtain ⟨u, v, θ₀, hu, hv, huv, -, -, hrot, hdist⟩ :=
    exists_rotation_path (Nat.le_add_left 1 d) z z'
  have hr : dist z' z < min ε (dist (f q) z) := hz'r
  have harc : ∀ t ∈ Icc (0 : ℝ) 1,
      dist (rotCLM u v (t * θ₀) z.1) z.1 < min ε (dist (f q) z) := fun t ht =>
    (hdist t ht.1 ht.2).trans_lt (by rwa [← Subtype.dist_eq])
  refine (linkPre_move_right hd hg hy hf hz hu hv huv q hqg ?_ ?_ hz' hrot.symm).symm
  · intro t ht h
    have h1 := harc t ht
    rw [← h, ← Subtype.dist_eq] at h1
    exact lt_irrefl _ (h1.trans_le (min_le_right _ _))
  · intro t ht x hx h
    have hmem : f x ∈ ball z ε := by
      rw [mem_ball, Subtype.dist_eq, h]
      exact (harc t ht).trans_le (min_le_left _ _)
    exact hball hmem ⟨x, hx, rfl⟩

/-- **Problem 14 a)** (Milnor's case `g = f`): `y ↦ l(f⁻¹(y), f⁻¹(z))` is locally constant. -/
theorem linkPre_self_eventually_eq (hd : 1 ≤ d) {f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {y z : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f y)
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z) (hyz : y ≠ z) :
    ∀ᶠ y' in 𝓝 y, ∀ hy' : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f y',
      linkPre hf hy' hf hz = linkPre hf hy hf hz :=
  linkPre_eventually_eq hd hf hy hf hz fun _ hx h => hyz (hx.symm.trans h)

/-- **Problem 14 a)** (Milnor's case `g = f`), in the second value. -/
theorem linkPre_self_eventually_eq_right (hd : 1 ≤ d) {f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {y z : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f y)
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z) (hyz : y ≠ z) :
    ∀ᶠ z' in 𝓝 z, ∀ hz' : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z',
      linkPre hf hy hf hz' = linkPre hf hy hf hz :=
  linkPre_eventually_eq_right hd hf hy hf hz fun _ hx h => hyz (hx.symm.trans h)

/-! ### Problem 14 b): nearby maps -/

namespace HopfInv

/-- The normalized chord homotopy from `f` to `g` (time reparametrized by `smoothTransition`). -/
def chord (f g : Sph (d + (d + 1)) → Sph (d + 1)) (w : Sph (d + (d + 1)) × ℝ) : Sph (d + 1) :=
  nv0 ((1 - Real.smoothTransition w.2) • (f w.1).1 + Real.smoothTransition w.2 • (g w.1).1)

theorem chord_apply (f g : Sph (d + (d + 1)) → Sph (d + 1)) (x : Sph (d + (d + 1))) (t : ℝ) :
    chord f g (x, t) =
      nv0 ((1 - Real.smoothTransition t) • (f x).1 + Real.smoothTransition t • (g x).1) := rfl

theorem contMDiff_chord {f g : Sph (d + (d + 1)) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g)
    (hfg : ∀ x, ‖(f x).1 - (g x).1‖ < 2) :
    ContMDiff (𝓘(ℝ, 𝔼 (d + (d + 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (chord f g) := by
  have hσs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hfv : ContMDiff (𝓘(ℝ, 𝔼 (d + (d + 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼 (d + 1 + 1)) ∞
      (fun w : Sph (d + (d + 1)) × ℝ => (f w.1).1) := contMDiff_val.comp (hf.comp contMDiff_fst)
  have hgv : ContMDiff (𝓘(ℝ, 𝔼 (d + (d + 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼 (d + 1 + 1)) ∞
      (fun w : Sph (d + (d + 1)) × ℝ => (g w.1).1) := contMDiff_val.comp (hg.comp contMDiff_fst)
  have hσq : ContMDiff (𝓘(ℝ, 𝔼 (d + (d + 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun w : Sph (d + (d + 1)) × ℝ => Real.smoothTransition w.2) :=
    hσs.contMDiff.comp contMDiff_snd
  have hwc : ContMDiff (𝓘(ℝ, 𝔼 (d + (d + 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼 (d + 1 + 1)) ∞
      (fun w : Sph (d + (d + 1)) × ℝ =>
        (1 - Real.smoothTransition w.2) • (f w.1).1 + Real.smoothTransition w.2 • (g w.1).1) :=
    ((contMDiff_const.sub hσq).smul hfv).add (hσq.smul hgv)
  exact contMDiff_nv0_comp hwc fun w => chord_ne_zero (hfg w.1)
    (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

theorem chord_zero (f g : Sph (d + (d + 1)) → Sph (d + 1)) :
    (fun x => chord f g (x, 0)) = f := funext fun x => by
  rw [chord_apply, Real.smoothTransition.zero, sub_zero, one_smul, zero_smul, add_zero, nv0_sph]

theorem chord_one (f g : Sph (d + (d + 1)) → Sph (d + 1)) :
    (fun x => chord f g (x, 1)) = g := funext fun x => by
  rw [chord_apply, Real.smoothTransition.one, sub_self, zero_smul, one_smul, zero_add, nv0_sph]

/-- A normalized chord point is no farther from either end than the ends are from each other. -/
theorem norm_nv0_chord_sub {p : ℕ} {a b : Sph p} (hab : ‖a.1 - b.1‖ < 2) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    ‖(nv0 ((1 - s) • a.1 + s • b.1)).1 - a.1‖ ≤ ‖a.1 - b.1‖ ∧
      ‖(nv0 ((1 - s) • a.1 + s • b.1)).1 - b.1‖ ≤ ‖a.1 - b.1‖ := by
  obtain ⟨w, hw⟩ : ∃ w, w = (1 - s) • a.1 + s • b.1 := ⟨_, rfl⟩
  rw [← hw]
  have hw0 : w ≠ 0 := hw ▸ chord_ne_zero hab hs0 hs1
  have ha : ‖a.1‖ = 1 := norm_sph a
  have hb : ‖b.1‖ = 1 := norm_sph b
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hwle : ‖w‖ ≤ 1 := by
    calc ‖w‖ ≤ ‖(1 - s) • a.1‖ + ‖s • b.1‖ := by rw [hw]; exact norm_add_le _ _
      _ = (1 - s) + s := by
        rw [norm_smul, norm_smul, ha, hb, Real.norm_of_nonneg (by linarith),
          Real.norm_of_nonneg hs0, mul_one, mul_one]
      _ = 1 := by ring
  have hnw : ‖(nv0 w).1 - w‖ = 1 - ‖w‖ := by
    rw [nv0_val hw0, Sphere.normalize]
    have h1 : ‖w‖⁻¹ • w - w = (‖w‖⁻¹ - 1) • w := by rw [sub_smul, one_smul]
    have h2 : 0 ≤ ‖w‖⁻¹ - 1 := sub_nonneg.2 ((one_le_inv₀ hwpos).2 hwle)
    rw [h1, norm_smul, Real.norm_of_nonneg h2, sub_mul, inv_mul_cancel₀ hwpos.ne', one_mul]
  have hwa : ‖w - a.1‖ = s * ‖a.1 - b.1‖ := by
    have : w - a.1 = s • (b.1 - a.1) := by rw [hw]; module
    rw [this, norm_smul, Real.norm_of_nonneg hs0, norm_sub_rev]
  have hwb : ‖w - b.1‖ = (1 - s) * ‖a.1 - b.1‖ := by
    have : w - b.1 = (1 - s) • (a.1 - b.1) := by rw [hw]; module
    rw [this, norm_smul, Real.norm_of_nonneg (by linarith)]
  have hna := norm_sub_le_norm_sub_add_norm_sub (nv0 w).1 w a.1
  have hnb := norm_sub_le_norm_sub_add_norm_sub (nv0 w).1 w b.1
  have h1 : 1 - ‖w‖ ≤ ‖w - b.1‖ := by
    have := norm_sub_norm_le b.1 w
    rw [hb, norm_sub_rev] at this
    exact this
  have h2 : 1 - ‖w‖ ≤ ‖w - a.1‖ := by
    have := norm_sub_norm_le a.1 w
    rw [ha, norm_sub_rev] at this
    exact this
  constructor <;> nlinarith

theorem norm_chord_sub_left {f g : Sph (d + (d + 1)) → Sph (d + 1)} {x : Sph (d + (d + 1))}
    (hfg : ‖(f x).1 - (g x).1‖ < 2) (t : ℝ) :
    ‖(chord f g (x, t)).1 - (f x).1‖ ≤ ‖(f x).1 - (g x).1‖ :=
  (norm_nv0_chord_sub hfg (Real.smoothTransition.nonneg t) (Real.smoothTransition.le_one t)).1

theorem norm_chord_sub_right {f g : Sph (d + (d + 1)) → Sph (d + 1)} {x : Sph (d + (d + 1))}
    (hfg : ‖(f x).1 - (g x).1‖ < 2) (t : ℝ) :
    ‖(chord f g (x, t)).1 - (g x).1‖ ≤ ‖(f x).1 - (g x).1‖ :=
  (norm_nv0_chord_sub hfg (Real.smoothTransition.nonneg t) (Real.smoothTransition.le_one t)).2

/-- **Choice of a good value**: near any point there is a common regular value of `f` and `g`
which avoids a given smooth curve on `[0, 1]` and a given point (regular values are open and dense,
the curve is nowhere dense, points are meagre). -/
theorem exists_regular_off (hd : 1 ≤ d) {f g : Sph (d + (d + 1)) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y₀ : Sph (d + 1)}
    {W : Set (Sph (d + 1))} (hW : W ∈ 𝓝 y₀) {γ : ℝ → Sph (d + 1)}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, 𝔼 (d + 1)) ∞ γ) (p : Sph (d + 1)) :
    ∃ y ∈ W, IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f y ∧
      IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ y) ∧ y ≠ p := by
  have ho : IsOpen (interior W ∩ {y | IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f y} ∩
      {y | IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y}) :=
    (isOpen_interior.inter (isOpen_setOf_isRegularValue hf)).inter
      (isOpen_setOf_isRegularValue hg)
  have hne : (interior W ∩ {y | IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f y} ∩
      {y | IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y}).Nonempty := by
    obtain ⟨y, hy1, hy2⟩ := (dense_regularValues hf).inter_open_nonempty _ isOpen_interior
      ⟨y₀, mem_interior_iff_mem_nhds.2 hW⟩
    obtain ⟨y', hy'1, hy'2⟩ := (dense_regularValues hg).inter_open_nonempty _
      (isOpen_interior.inter (isOpen_setOf_isRegularValue hf)) ⟨y, hy1, hy2⟩
    exact ⟨y', hy'1, hy'2⟩
  have hγm : IsMeagre (γ '' Icc (0 : ℝ) 1) :=
    (isNowhereDense_image_of_finrank_lt (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, 𝔼 (d + 1)))
      (by rw [Module.finrank_self, finrank_euclideanSpace_fin]; omega) isOpen_univ
      (subset_univ _) isCompact_Icc hγ.contMDiffOn).2.isMeagre
  have hpm : IsMeagre ({p} : Set (Sph (d + 1))) := by
    have h := isMeagre_image_of_finrank_lt (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, 𝔼 (d + 1)))
      (g := fun _ : ℝ => p) (U := univ)
      (by rw [Module.finrank_self, finrank_euclideanSpace_fin]; omega) isOpen_univ
      contMDiffOn_const
    rwa [univ_nonempty.image_const] at h
  obtain ⟨y, ⟨⟨hyW, hyf⟩, hyg⟩, hy⟩ := exists_mem_open_not_mem_of_isMeagre ho hne (hγm.union hpm)
  simp only [mem_union, mem_image, mem_singleton_iff, not_or, not_exists, not_and] at hy
  exact ⟨y, interior_subset hyW, hyf, hyg, fun t ht h => hy.1 t ht h, hy.2⟩

end HopfInv

open HopfInv in
/-- **Problem 14 b).**  If `y ≠ z` are regular values of `f` and of `g` and
`‖f(x) − g(x)‖ < ‖y − z‖` for all `x`, then
`l(f⁻¹(y), f⁻¹(z)) = l(g⁻¹(y), f⁻¹(z)) = l(g⁻¹(y), g⁻¹(z))`. -/
theorem linkPre_eq_of_norm_lt (hd : 1 ≤ d) {f g : Sph (d + (d + 1)) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y z : Sph (d + 1)}
    (hyf : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f y)
    (hzf : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z)
    (hyg : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hzg : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g z) (hyz : y ≠ z)
    (hclose : ∀ x, ‖(f x).1 - (g x).1‖ < ‖y.1 - z.1‖) :
    linkPre hf hyf hf hzf = linkPre hg hyg hf hzf ∧
      linkPre hg hyg hf hzf = linkPre hg hyg hg hzg := by
  -- the maximal distance `m` between `f` and `g`
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
    ((continuous_subtype_val.comp hf.continuous).sub
      (continuous_subtype_val.comp hg.continuous)).norm.continuousOn
  have hm : ∀ x, ‖(f x).1 - (g x).1‖ ≤ ‖(f x₀).1 - (g x₀).1‖ := fun x => hx₀ (mem_univ x)
  have hyz2 : ‖y.1 - z.1‖ ≤ 2 := by
    calc ‖y.1 - z.1‖ ≤ ‖y.1‖ + ‖z.1‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_sph, norm_sph]; norm_num
  have hfg2 : ∀ x, ‖(f x).1 - (g x).1‖ < 2 := fun x => (hclose x).trans_le hyz2
  have hC := contMDiff_chord hf hg hfg2
  have hdisj_gf : ∀ x, g x = y → f x ≠ z := fun x hx h => by
    have h1 := hclose x
    rw [hx, h, norm_sub_rev] at h1
    exact lt_irrefl _ h1
  have hC0s : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞
      (fun x => chord f g (x, 0)) := hC.comp (contMDiff_inl 0)
  have hC1s : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞
      (fun x => chord f g (x, 1)) := hC.comp (contMDiff_inl 1)
  constructor
  · -- deform `f` to `g` in the first slot, at a good value `y'` near `y`
    obtain ⟨q, -, hqf⟩ := exists_ne_ne hf hzf hf hzf
    have hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (fun t => chord f g (q, t)) :=
      hC.comp (contMDiff_const.prodMk contMDiff_id)
    have hN3 : {y' : Sph (d + 1) | ‖(f x₀).1 - (g x₀).1‖ < ‖y'.1 - z.1‖} ∈ 𝓝 y :=
      (isOpen_lt continuous_const ((continuous_subtype_val.sub continuous_const).norm)).mem_nhds
        (hclose x₀)
    obtain ⟨y', ⟨⟨h1, h2⟩, h3⟩, hy'f, hy'g, hy'γ, -⟩ := exists_regular_off hd hf hg
      (inter_mem (inter_mem (linkPre_self_eventually_eq hd hf hyf hzf hyz)
        (linkPre_eventually_eq hd hg hyg hf hzf hdisj_gf)) hN3) hγ z
    have h3' : ‖(f x₀).1 - (g x₀).1‖ < ‖y'.1 - z.1‖ := h3
    have hy0 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1))
        (fun x => chord f g (x, 0)) y' := by rw [chord_zero]; exact hy'f
    have hy1 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1))
        (fun x => chord f g (x, 1)) y' := by rw [chord_one]; exact hy'g
    have key := linkPre_eq_of_homotopy hd (G := chord f g) (F := fun w => f w.1) hC
      (hf.comp contMDiff_fst) hC0s hC1s hf hf hy0 hy1 hzf hzf
      (fun t _ x hx h => by
        have hle := norm_chord_sub_left (hfg2 x) t
        rw [hx] at hle
        have hle' : ‖y'.1 - z.1‖ ≤ ‖(f x).1 - (g x).1‖ := by
          have h' : f x = z := h
          rw [← h']; exact hle
        exact absurd (hle'.trans (hm x)) (not_le.2 h3'))
      q (fun t ht => ⟨hy'γ t ht, hqf⟩)
    calc linkPre hf hyf hf hzf = linkPre hf hy'f hf hzf := (h1 hy'f).symm
      _ = linkPre hC0s hy0 hf hzf := linkPre_congr _ _ _ _ _ _ _ _ (chord_zero f g).symm rfl rfl rfl
      _ = linkPre hC1s hy1 hf hzf := key
      _ = linkPre hg hy'g hf hzf := linkPre_congr _ _ _ _ _ _ _ _ (chord_one f g) rfl rfl rfl
      _ = linkPre hg hyg hf hzf := h2 hy'g
  · -- deform `f` to `g` in the second slot, at a good value `z'` near `z`
    obtain ⟨q, hqg, -⟩ := exists_ne_ne hg hyg hg hyg
    have hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (fun t => chord f g (q, t)) :=
      hC.comp (contMDiff_const.prodMk contMDiff_id)
    have hN3 : {z' : Sph (d + 1) | ‖(f x₀).1 - (g x₀).1‖ < ‖y.1 - z'.1‖} ∈ 𝓝 z :=
      (isOpen_lt continuous_const ((continuous_const.sub continuous_subtype_val).norm)).mem_nhds
        (hclose x₀)
    obtain ⟨z', ⟨⟨h1, h2⟩, h3⟩, hz'f, hz'g, hz'γ, -⟩ := exists_regular_off hd hf hg
      (inter_mem (inter_mem (linkPre_eventually_eq_right hd hg hyg hf hzf hdisj_gf)
        (linkPre_self_eventually_eq_right hd hg hyg hzg hyz)) hN3) hγ y
    have h3' : ‖(f x₀).1 - (g x₀).1‖ < ‖y.1 - z'.1‖ := h3
    have hz0 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1))
        (fun x => chord f g (x, 0)) z' := by rw [chord_zero]; exact hz'f
    have hz1 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1))
        (fun x => chord f g (x, 1)) z' := by rw [chord_one]; exact hz'g
    have key := linkPre_eq_of_homotopy hd (G := fun w => g w.1) (F := chord f g)
      (hg.comp contMDiff_fst) hC hg hg hC0s hC1s hyg hyg hz0 hz1
      (fun t _ x hx h => by
        have hle := norm_chord_sub_right (hfg2 x) t
        rw [h] at hle
        have hle' : ‖y.1 - z'.1‖ ≤ ‖(f x).1 - (g x).1‖ := by
          have h' : g x = y := hx
          rw [norm_sub_rev, ← h']; exact hle
        exact absurd (hle'.trans (hm x)) (not_le.2 h3'))
      q (fun t ht => ⟨hqg, hz'γ t ht⟩)
    calc linkPre hg hyg hf hzf = linkPre hg hyg hf hz'f := (h1 hz'f).symm
      _ = linkPre hg hyg hC0s hz0 := linkPre_congr _ _ _ _ _ _ _ _ rfl rfl (chord_zero f g).symm rfl
      _ = linkPre hg hyg hC1s hz1 := key
      _ = linkPre hg hyg hg hz'g := linkPre_congr _ _ _ _ _ _ _ _ rfl rfl (chord_one f g) rfl
      _ = linkPre hg hyg hg hzg := h2 hz'g

/-! ### Problem 14 c): the Hopf invariant -/

namespace HopfInv

/-- A constant map has no regular value in its image. -/
theorem not_isRegularValue_const (x₀ : Sph (d + (d + 1))) (c : Sph (d + 1)) :
    ¬ IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1))
      (fun _ : Sph (d + (d + 1)) => c) c := by
  intro h
  have hs := h x₀ rfl
  unfold IsRegularPoint at hs
  rw [mfderiv_const] at hs
  have h0 : ∀ w : 𝔼 (d + 1), w = 0 := fun w => by
    obtain ⟨v, hv⟩ := hs w
    rw [← hv]
    rfl
  have h2 := congrArg (fun w : 𝔼 (d + 1) => w (0 : Fin (d + 1)))
    (h0 (EuclideanSpace.single (0 : Fin (d + 1)) (1 : ℝ)))
  simp at h2

/-- Two distinct regular values exist. -/
theorem exists_regular_pair (hd : 1 ≤ d) {f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) :
    ∃ y z : Sph (d + 1), y ≠ z ∧ IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f y ∧
      IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z := by
  obtain ⟨p⟩ := (inferInstance : Nonempty (Sph (d + 1)))
  have hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (fun _ : ℝ => p) := contMDiff_const
  obtain ⟨y, -, hy, -, -, -⟩ := exists_regular_off hd hf hf (y₀ := p) univ_mem hγ p
  obtain ⟨z, -, hz, -, -, hzy⟩ := exists_regular_off hd hf hf (y₀ := p) univ_mem hγ y
  exact ⟨y, z, Ne.symm hzy, hy, hz⟩

end HopfInv

open HopfInv in
/-- **Independence of the values**: `l(f⁻¹(y), f⁻¹(z))` is the same for all pairs `y ≠ z` of
regular values.  The pairs `y ≠ z` form a connected set in which the regular pairs are dense, and
near every pair `(y₀, z₀)` any two regular pairs are joined by moving both values along short
rotation arcs which avoid `f(q)` for a point `q` with `f(q) ∉ {y₀, z₀}` (for constant `f` all
linking numbers vanish). -/
theorem linkPre_eq_linkPre_of_ne (hd : 1 ≤ d) {f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {y z y' z' : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f y)
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z)
    (hy' : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f y')
    (hz' : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z') (hyz : y ≠ z)
    (hyz' : y' ≠ z') :
    linkPre hf hy hf hz = linkPre hf hy' hf hz' := by
  have hp : 1 ≤ d + 1 := Nat.le_add_left 1 d
  obtain ⟨φ, hφ⟩ : ∃ φ : Sph (d + 1) × Sph (d + 1) → ℤ, ∀ p : Sph (d + 1) × Sph (d + 1),
      ∀ (h : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.1 ∧
        IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.2),
      φ p = linkPre hf h.1 hf h.2 := by
    classical
    exact ⟨fun p => if h : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.1 ∧
      IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.2 then linkPre hf h.1 hf h.2
      else 0, fun p h => dif_pos h⟩
  have hXo : IsOpen {p : Sph (d + 1) × Sph (d + 1) | p.1 ≠ p.2} :=
    isOpen_ne_fun continuous_fst continuous_snd
  -- the regular pairs are dense among the pairs of distinct points
  have hdense : {p : Sph (d + 1) × Sph (d + 1) | p.1 ≠ p.2} ⊆
      closure ({p : Sph (d + 1) × Sph (d + 1) |
        IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.1 ∧
          IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.2} ∩ {p | p.1 ≠ p.2}) := by
    rintro ⟨p1, p2⟩ hp12
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 (inter_mem ht (hXo.mem_nhds hp12))
    obtain ⟨a, ha, haU⟩ := (dense_regularValues hf).inter_nhds_nonempty hU
    obtain ⟨b, hb, hbV⟩ := (dense_regularValues hf).inter_nhds_nonempty hV
    have hab := hUV (mk_mem_prod haU hbV)
    exact ⟨(a, b), hab.1, ⟨ha, hb⟩, hab.2⟩
  -- local constancy on the regular pairs
  have hloc : ∀ p ∈ {p : Sph (d + 1) × Sph (d + 1) | p.1 ≠ p.2}, ∃ V ∈ 𝓝 p,
      ∀ a ∈ V ∩ ({p : Sph (d + 1) × Sph (d + 1) |
        IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.1 ∧
          IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.2} ∩ {p | p.1 ≠ p.2}),
      ∀ b ∈ V ∩ ({p : Sph (d + 1) × Sph (d + 1) |
        IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.1 ∧
          IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.2} ∩ {p | p.1 ≠ p.2}),
      φ a = φ b := by
    intro p hp12
    have hp12' : p.1 ≠ p.2 := hp12
    by_cases hc : ∃ c, ∀ x, f x = c
    · -- constant maps: all preimages of regular values are empty
      obtain ⟨c, hc⟩ := hc
      have hne : ∀ w, IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f w → ∀ x, f x ≠ w := by
        intro w hw x hx
        have hfc : f = fun _ => c := funext hc
        have hcw : c = w := (hc x).symm.trans hx
        subst hcw
        rw [hfc] at hw
        exact not_isRegularValue_const x _ hw
      refine ⟨univ, univ_mem, fun a ha b hb => ?_⟩
      rw [hφ a ha.2.1, hφ b hb.2.1, linkPre_eq_zero_of_forall_ne _ _ _ _ (hne _ ha.2.1.1),
        linkPre_eq_zero_of_forall_ne _ _ _ _ (hne _ hb.2.1.1)]
    · push Not at hc
      -- a point `q` with `f q ∉ {p.1, p.2}`
      obtain ⟨q, hq1, hq2⟩ : ∃ q, f q ≠ p.1 ∧ f q ≠ p.2 := by
        by_contra hne
        push Not at hne
        have := preconnectedSpace (n := d + (d + 1)) (by omega)
        have hclopen : IsClopen (f ⁻¹' {p.1}) := by
          refine ⟨isClosed_singleton.preimage hf.continuous, ?_⟩
          have heq : f ⁻¹' {p.1} = (f ⁻¹' {p.2})ᶜ := by
            ext x
            simp only [mem_preimage, mem_singleton_iff, mem_compl_iff]
            exact ⟨fun h1 h2 => hp12' (h1.symm.trans h2),
              fun h2 => by_contra fun h1 => h2 (hne x h1)⟩
          rw [heq]
          exact (isClosed_singleton.preimage hf.continuous).isOpen_compl
        rcases isClopen_iff.1 hclopen with h | h
        · obtain ⟨x, hx⟩ := hc p.2
          refine hx (hne x fun h1 => ?_)
          have hmem : x ∈ f ⁻¹' {p.1} := h1
          rw [h] at hmem
          exact hmem
        · obtain ⟨x, hx⟩ := hc p.1
          have hmem : x ∈ f ⁻¹' {p.1} := by rw [h]; exact mem_univ x
          exact hx hmem
      obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min (dist p.1 p.2) (min (dist (f q) p.1) (dist (f q) p.2)) / 8 :=
        ⟨_, rfl⟩
      have hr0 : 0 < r := by
        rw [hr]
        exact div_pos (lt_min (dist_pos.2 hp12') (lt_min (dist_pos.2 hq1) (dist_pos.2 hq2)))
          (by norm_num)
      have hr1 : 8 * r ≤ dist p.1.1 p.2.1 := by
        rw [← Subtype.dist_eq, hr]
        linarith [min_le_left (dist p.1 p.2) (min (dist (f q) p.1) (dist (f q) p.2))]
      have hr2 : 8 * r ≤ dist (f q).1 p.1.1 := by
        rw [← Subtype.dist_eq, hr]
        linarith [min_le_right (dist p.1 p.2) (min (dist (f q) p.1) (dist (f q) p.2)),
          min_le_left (dist (f q) p.1) (dist (f q) p.2)]
      have hr3 : 8 * r ≤ dist (f q).1 p.2.1 := by
        rw [← Subtype.dist_eq, hr]
        linarith [min_le_right (dist p.1 p.2) (min (dist (f q) p.1) (dist (f q) p.2)),
          min_le_right (dist (f q) p.1) (dist (f q) p.2)]
      refine ⟨ball p.1 r ×ˢ ball p.2 r, prod_mem_nhds (ball_mem_nhds _ hr0) (ball_mem_nhds _ hr0),
        ?_⟩
      rintro ⟨a1, a2⟩ ⟨⟨ha1, ha2⟩, ⟨hra1, hra2⟩, -⟩ ⟨b1, b2⟩ ⟨⟨hb1, hb2⟩, ⟨hrb1, hrb2⟩, -⟩
      rw [hφ _ ⟨hra1, hra2⟩, hφ _ ⟨hrb1, hrb2⟩]
      have ha1' : dist a1.1 p.1.1 < r := by rw [← Subtype.dist_eq]; exact ha1
      have ha2' : dist a2.1 p.2.1 < r := by rw [← Subtype.dist_eq]; exact ha2
      have hb1' : dist b1.1 p.1.1 < r := by rw [← Subtype.dist_eq]; exact hb1
      have hb2' : dist b2.1 p.2.1 < r := by rw [← Subtype.dist_eq]; exact hb2
      obtain ⟨u₁, v₁, θ₁, hu₁, hv₁, huv₁, -, -, hrot₁, hdist₁⟩ := exists_rotation_path hp a1 b1
      obtain ⟨u₂, v₂, θ₂, hu₂, hv₂, huv₂, -, -, hrot₂, hdist₂⟩ := exists_rotation_path hp a2 b2
      -- the arcs stay within `3r` of the centres
      have harc₁ : ∀ t ∈ Icc (0 : ℝ) 1, dist (rotCLM u₁ v₁ (t * θ₁) a1.1) p.1.1 < 3 * r := by
        intro t ht
        have h1 := hdist₁ t ht.1 ht.2
        have h2 := dist_triangle (rotCLM u₁ v₁ (t * θ₁) a1.1) a1.1 p.1.1
        have h3 := dist_triangle b1.1 p.1.1 a1.1
        rw [dist_comm p.1.1 a1.1] at h3
        linarith
      have harc₂ : ∀ t ∈ Icc (0 : ℝ) 1, dist (rotCLM u₂ v₂ (t * θ₂) a2.1) p.2.1 < 3 * r := by
        intro t ht
        have h1 := hdist₂ t ht.1 ht.2
        have h2 := dist_triangle (rotCLM u₂ v₂ (t * θ₂) a2.1) a2.1 p.2.1
        have h3 := dist_triangle b2.1 p.2.1 a2.1
        rw [dist_comm p.2.1 a2.1] at h3
        linarith
      refine linkPre_move hd hf hra1 hf hra2 hu₁ hv₁ huv₁ hu₂ hv₂ huv₂ q ?_ ?_ ?_ hrb1 hrb2
        hrot₁.symm hrot₂.symm
      · intro t ht h
        have h1 := harc₁ t ht
        rw [← h] at h1
        linarith
      · intro t ht h
        have h1 := harc₂ t ht
        rw [← h] at h1
        linarith
      · intro t ht x hx h
        have h1 := harc₁ t ht
        have h2 := harc₂ t ht
        rw [← hx] at h1
        rw [← h] at h2
        have h3 := dist_triangle p.1.1 (f x).1 p.2.1
        rw [dist_comm p.1.1 (f x).1] at h3
        linarith
  have key := eq_of_locallyConst_on_dense (isConnected_offDiag_sph hp).isPreconnected hdense φ hloc
    (y, z) ⟨⟨hy, hz⟩, hyz⟩ (y', z') ⟨⟨hy', hz'⟩, hyz'⟩
  rwa [hφ (y, z) ⟨hy, hz⟩, hφ (y', z') ⟨hy', hz'⟩] at key

open Classical in
/-- **The Hopf invariant** `H(f) = l(f⁻¹(y), f⁻¹(z))` of a smooth map `f : S^{2d+1} → S^{d+1}`,
computed with a chosen pair of distinct regular values (`0` if `f` is not smooth). -/
def hopfInvariant (f : Sph (d + (d + 1)) → Sph (d + 1)) : ℤ :=
  if h : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f ∧
      ∃ p : Sph (d + 1) × Sph (d + 1), p.1 ≠ p.2 ∧
        IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.1 ∧
        IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.2 then
    linkPre h.1 h.2.choose_spec.2.1 h.1 h.2.choose_spec.2.2
  else 0

/-- **Problem 14 c), independence of `y` and `z`**: for all distinct regular values `y ≠ z`,
`l(f⁻¹(y), f⁻¹(z)) = H(f)`. -/
theorem linkPre_eq_hopfInvariant (hd : 1 ≤ d) {f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {y z : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f y)
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z) (hyz : y ≠ z) :
    linkPre hf hy hf hz = hopfInvariant f := by
  have h : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f ∧
      ∃ p : Sph (d + 1) × Sph (d + 1), p.1 ≠ p.2 ∧
        IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.1 ∧
        IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.2 :=
    ⟨hf, (y, z), hyz, hy, hz⟩
  rw [hopfInvariant, dif_pos h]
  exact linkPre_eq_linkPre_of_ne hd hf hy hz _ _ hyz h.2.choose_spec.1

open HopfInv in
/-- **Problem 14 c), homotopy invariance**: smoothly homotopic maps have the same Hopf invariant.
Proof: for a homotopy `H` and a base point `q`, choose distinct common regular values `y, z` of
`f` and `g` off the curve `t ↦ H(q, t)`; the engine with `G = F = H` gives
`l(f⁻¹(y), f⁻¹(z)) = l(g⁻¹(y), g⁻¹(z))`. -/
theorem hopfInvariant_eq_of_smoothHomotopic (hd : 1 ≤ d) {f g : Sph (d + (d + 1)) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g)
    (h : SmoothHomotopic 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f g) :
    hopfInvariant f = hopfInvariant g := by
  obtain ⟨H, hH, h0, h1⟩ := h
  have hH0 : (fun x => H (x, 0)) = f := funext h0
  have hH1 : (fun x => H (x, 1)) = g := funext h1
  obtain ⟨q⟩ := (inferInstance : Nonempty (Sph (d + (d + 1))))
  have hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (fun t => H (q, t)) :=
    hH.comp (contMDiff_const.prodMk contMDiff_id)
  obtain ⟨y, -, hyf, hyg, hyγ, -⟩ := exists_regular_off hd hf hg (y₀ := f q) univ_mem hγ (f q)
  obtain ⟨z, -, hzf, hzg, hzγ, hzy⟩ := exists_regular_off hd hf hg (y₀ := f q) univ_mem hγ y
  have hH0s : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (fun x => H (x, 0)) :=
    hH.comp (contMDiff_inl 0)
  have hH1s : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (fun x => H (x, 1)) :=
    hH.comp (contMDiff_inl 1)
  have hy0 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (fun x => H (x, 0)) y := by
    rw [hH0]; exact hyf
  have hy1 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (fun x => H (x, 1)) y := by
    rw [hH1]; exact hyg
  have hz0 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (fun x => H (x, 0)) z := by
    rw [hH0]; exact hzf
  have hz1 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (fun x => H (x, 1)) z := by
    rw [hH1]; exact hzg
  have key := linkPre_eq_of_homotopy hd hH hH hH0s hH1s hH0s hH1s hy0 hy1 hz0 hz1
    (fun t _ x hx h => hzy (h.symm.trans hx)) q (fun t ht => ⟨hyγ t ht, hzγ t ht⟩)
  rw [← linkPre_eq_hopfInvariant hd hf hyf hzf (Ne.symm hzy),
    ← linkPre_eq_hopfInvariant hd hg hyg hzg (Ne.symm hzy)]
  calc linkPre hf hyf hf hzf = linkPre hH0s hy0 hH0s hz0 :=
        linkPre_congr _ _ _ _ _ _ _ _ hH0.symm rfl hH0.symm rfl
    _ = linkPre hH1s hy1 hH1s hz1 := key
    _ = linkPre hg hyg hg hzg := linkPre_congr _ _ _ _ _ _ _ _ hH1 rfl hH1 rfl

end Problems

end Milnor
