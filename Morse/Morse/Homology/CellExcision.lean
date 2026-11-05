import Morse.Homology.Excision
import Morse.Homology.RelativeRetract

/-!
# Excision for an attached cell

Let `X = Y ∪ e` be obtained from a space `Y` by attaching a closed cell `e = χ(D)`: `D` is the
closed unit ball of a (finite-dimensional) real normed space, `χ` is continuous and injective on
`D`, and `χ(z) ∈ Y` exactly when `‖z‖ = 1`, so that `e` meets `Y` in its boundary sphere
`∂e = χ(S)`.  This file proves the basic computation behind Milnor's use of homology in §5:

**Theorem** (`Morse.Homology.isIso_relHomology_map_cellPair`).  If `Y` is closed in `X` (all
subsets of a Hausdorff space `E`), the inclusion of pairs `(e, ∂e) ⟶ (X, Y)` induces isomorphisms
`H_n(e, ∂e) ≅ H_n(X, Y)` in all degrees.

The homology of `(e, ∂e)` itself, which is that of `(Dᵏ, Sᵏ⁻¹)`, is computed in
`Morse/Homology/Spheres.lean`, by induction on `k` using this theorem for the upper hemisphere of
`Sᵏ⁻¹` attached to the lower one.

## Proof

Let `p = χ(0)` be the centre of the cell.

1. `Y` is a strong deformation retract of `X ∖ {p}` (`isStrongDeformationRetract_sdiff_center`):
   the punctured cell is pushed radially onto its boundary, `χ(z) ↦ χ(ρ_t(z))` with
   `ρ_t(z) = ((1 - t) + t / ‖z‖) z` (`Morse.Homology.radialPush`), and `Y` is kept fixed.  The
   two formulas agree on `Y ∩ e = ∂e`; they are pasted along the closed sets `Y` and `e` (compact,
   hence closed in the Hausdorff space `E`); and `χ⁻¹` is continuous on `e` because a continuous
   injection of a compact space into a Hausdorff space is an embedding
   (`continuousOn_invFunOn_image`).  Hence `(X, Y) ⟶ (X, X ∖ {p})` is an isomorphism in homology
   (five lemma, `isIso_relHomology_map_of_isStrongDeformationRetract_snd`).
2. Excision of `X ∖ e`, whose closure lies in `Y ⊆ X ∖ {p}`, an open subset of `X`:
   `(e, e ∖ {p}) ⟶ (X, X ∖ {p})` is an isomorphism (`excision_of_eq`).
3. Step 1 for the cell alone (`X = e`, `Y = ∂e`): `(e, ∂e) ⟶ (e, e ∖ {p})` is an isomorphism.
4. The square of inclusions `(e, ∂e) ⟶ (X, Y) ⟶ (X, X ∖ {p})`,
   `(e, ∂e) ⟶ (e, e ∖ {p}) ⟶ (X, X ∖ {p})` commutes, and three of its four sides are
   isomorphisms.

Neither the domain of `χ` nor its universe plays a role in the homology: only subsets of `E`
appear.  The same radial and straight-line deformations show that a cell contracts onto any of
its points (`isStrongDeformationRetract_singleton_image`), which is used in
`Morse/Homology/Spheres.lean`.

## Main results

* `Morse.Homology.continuousOn_invFunOn_image`: the inverse of a map continuous and injective on a
  compact set is continuous on its image.
* `Morse.Homology.isStrongDeformationRetract_sdiff_center`: `Y` is a strong deformation retract of
  `X ∖ {χ(0)}`.
* `Morse.Homology.isStrongDeformationRetract_singleton_image`: `{χ(z₀)}` is a strong deformation
  retract of the cell `χ(D)`.
* `Morse.Homology.isIso_relHomology_map_of_isStrongDeformationRetract_snd`: for `A ⊆ B ⊆ X` with
  `A` a strong deformation retract of `B`, `H_n(X, A) ≅ H_n(X, B)`.
* `Morse.Homology.excision_of_eq`: excision, with the excised pair given up to equality.
* `Morse.Homology.cellPair χ`: the pair `(χ(D), χ(S))`.
* `Morse.Homology.isIso_relHomology_map_cellPair`: **excision for an attached cell**.
-/

noncomputable section

open CategoryTheory Limits Set Topology Metric Function HomologicalComplex
open scoped unitInterval

universe w v u

namespace Morse.Homology

/-! ### Continuity of the inverse of a parametrization -/

section Topology

variable {V E : Type*} [TopologicalSpace V] [TopologicalSpace E]

/-- If `f` is continuous and injective on a compact set `s`, with values in a Hausdorff space, then
its inverse `Function.invFunOn f s` is continuous on `f '' s` (a continuous bijection from a
compact space to a Hausdorff space is a homeomorphism). -/
theorem continuousOn_invFunOn_image [T2Space E] [Nonempty V] {f : V → E} {s : Set V}
    (hs : IsCompact s) (hf : ContinuousOn f s) (hinj : InjOn f s) :
    ContinuousOn (invFunOn f s) (f '' s) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨f '' (s ∩ t), ((hs.inter_right ht).image_of_continuousOn
    (hf.mono inter_subset_left)).isClosed, ?_⟩
  ext y
  simp only [mem_inter_iff, mem_preimage, mem_image]
  constructor
  · rintro ⟨hyt, x, hx, rfl⟩
    rw [hinj.leftInvOn_invFunOn hx] at hyt
    exact ⟨⟨x, ⟨hx, hyt⟩, rfl⟩, x, hx, rfl⟩
  · rintro ⟨⟨x, ⟨hx, hxt⟩, rfl⟩, -⟩
    refine ⟨?_, x, hx, rfl⟩
    rwa [hinj.leftInvOn_invFunOn hx]

end Topology

/-! ### The radial deformation of the punctured ball onto the sphere -/

section Radial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The radial deformation `ρ_t(z) = ((1 - t) + t / ‖z‖) z` of the punctured unit ball onto the
unit sphere: `ρ_0 = id`, `ρ_1(z) = z / ‖z‖`, and `ρ_t` fixes the sphere. -/
def radialPush (t : ℝ) (z : V) : V := ((1 - t) + t * ‖z‖⁻¹) • z

lemma radialPush_zero (z : V) : radialPush 0 z = z := by simp [radialPush]

lemma radialPush_of_norm_eq_one {z : V} (hz : ‖z‖ = 1) (t : ℝ) : radialPush t z = z := by
  simp [radialPush, hz]

/-- `‖ρ_t(z)‖ = (1 - t) ‖z‖ + t` for `z ≠ 0` and `0 ≤ t ≤ 1`. -/
lemma norm_radialPush {t : ℝ} {z : V} (hz : z ≠ 0) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    ‖radialPush t z‖ = (1 - t) * ‖z‖ + t := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hc : 0 ≤ (1 - t) + t * ‖z‖⁻¹ :=
    add_nonneg (sub_nonneg.2 ht₁) (mul_nonneg ht₀ (inv_nonneg.2 hz'.le))
  rw [radialPush, norm_smul, Real.norm_of_nonneg hc, add_mul, mul_assoc, inv_mul_cancel₀ hz'.ne',
    mul_one]

lemma radialPush_ne_zero {t : ℝ} {z : V} (hz : z ≠ 0) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    radialPush t z ≠ 0 := by
  rw [← norm_pos_iff, norm_radialPush hz ht₀ ht₁]
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  rcases eq_or_lt_of_le ht₀ with rfl | ht
  · simpa using hz'
  · nlinarith [mul_nonneg (sub_nonneg.2 ht₁) hz'.le]

/-- `ρ_t` maps the punctured closed unit ball into itself. -/
lemma radialPush_mem_closedBall {t : ℝ} {z : V} (hz : z ∈ closedBall (0 : V) 1) (hz0 : z ≠ 0)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : radialPush t z ∈ closedBall (0 : V) 1 := by
  rw [mem_closedBall_zero_iff] at hz ⊢
  rw [norm_radialPush hz0 ht₀ ht₁]
  nlinarith [mul_le_mul_of_nonneg_left hz (sub_nonneg.2 ht₁)]

lemma norm_radialPush_one {z : V} (hz : z ≠ 0) : ‖radialPush 1 z‖ = 1 := by
  rw [norm_radialPush hz zero_le_one le_rfl]
  ring

/-- `(t, z) ↦ ρ_t(z)` is continuous away from `z = 0`. -/
lemma continuousOn_radialPush :
    ContinuousOn (fun q : ℝ × V ↦ radialPush q.1 q.2) {q | q.2 ≠ 0} := by
  refine ContinuousOn.smul ?_ continuous_snd.continuousOn
  refine (continuous_const.sub continuous_fst).continuousOn.add
    (continuous_fst.continuousOn.mul ?_)
  exact (continuous_norm.comp continuous_snd).continuousOn.inv₀ fun q hq ↦ norm_ne_zero_iff.2 hq

end Radial

/-! ### Deformation retractions of a cell -/

section Deformation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
  {E : Type*} [TopologicalSpace E] [T2Space E]

/-- **The space minus the centre of the cell retracts onto `Y`.** Let `X = Y ∪ χ(D)`, where `D` is
the closed unit ball of a normed space, `χ` is continuous and injective on `D`, `Y` is closed in
`X` and `χ(z) ∈ Y` exactly when `‖z‖ = 1`. Then `Y` is a strong deformation retract of
`X ∖ {χ(0)}`: push the punctured cell radially onto its boundary, `χ(z) ↦ χ(ρ_t(z))`, and keep `Y`
fixed. The two formulas agree on `Y ∩ χ(D) = χ(S)`, and are pasted along the closed sets `Y` and
`χ(D)` (compact, hence closed); `χ⁻¹` is continuous on `χ(D)` by compactness. -/
theorem isStrongDeformationRetract_sdiff_center {X Y : Set E}
    (hY : IsClosed ((↑) ⁻¹' Y : Set X)) {χ : V → E} (hχ : ContinuousOn χ (closedBall 0 1))
    (hinj : InjOn χ (closedBall 0 1)) (hχY : ∀ z ∈ closedBall (0 : V) 1, χ z ∈ Y ↔ ‖z‖ = 1)
    (hX : X = Y ∪ χ '' closedBall 0 1) :
    IsStrongDeformationRetract ((↑) ⁻¹' Y : Set ↥(X \ {χ 0})) := by
  classical
  set D := closedBall (0 : V) 1 with hD
  set p := χ 0 with hp
  set g := invFunOn χ D with hg
  have hDc : IsCompact D := isCompact_closedBall 0 1
  have he : IsClosed (χ '' D) := (hDc.image_of_continuousOn hχ).isClosed
  have hgc : ContinuousOn g (χ '' D) := continuousOn_invFunOn_image hDc hχ hinj
  have hgD : MapsTo g (χ '' D) D := (surjOn_image χ D).mapsTo_invFunOn
  have hχg : ∀ x ∈ χ '' D, χ (g x) = x := (surjOn_image χ D).rightInvOn_invFunOn
  have h0D : (0 : V) ∈ D := mem_closedBall_self zero_le_one
  have hg0 : ∀ x : ↥(X \ {p}), (x : E) ∈ χ '' D → g x ≠ 0 := by
    intro x hx h
    apply x.2.2
    rw [mem_singleton_iff, ← hχg x hx, h]
  have hXsub : X ⊆ Y ∪ χ '' D := hX.subset
  have heX : χ '' D ⊆ X := hX.symm.subset.trans' subset_union_right
  have hcell : ∀ x : ↥(X \ {p}), (x : E) ∉ Y → (x : E) ∈ χ '' D :=
    fun x hx ↦ (hXsub x.2.1).resolve_left hx
  -- the deformation, as a map into `E`
  let k : I × ↥(X \ {p}) → E := fun q ↦
    if (q.2 : E) ∈ Y then q.2 else χ (radialPush (q.1 : ℝ) (g q.2))
  have hkY : ∀ (t : I) (x : ↥(X \ {p})), (x : E) ∈ Y → k (t, x) = x := fun t x hx ↦ if_pos hx
  have hk0 : ∀ x : ↥(X \ {p}), k (0, x) = x := by
    intro x
    by_cases hx : (x : E) ∈ Y
    · exact hkY 0 x hx
    · simp only [k, if_neg hx, Set.Icc.coe_zero, radialPush_zero]
      exact hχg x (hcell x hx)
  have hk1 : ∀ x : ↥(X \ {p}), k (1, x) ∈ Y := by
    intro x
    by_cases hx : (x : E) ∈ Y
    · rw [hkY 1 x hx]
      exact hx
    · simp only [k, if_neg hx, Set.Icc.coe_one]
      have hgx := hgD (hcell x hx)
      have hg0x := hg0 x (hcell x hx)
      exact (hχY _ (radialPush_mem_closedBall hgx hg0x zero_le_one le_rfl)).2
        (norm_radialPush_one hg0x)
  have hkmem : ∀ q : I × ↥(X \ {p}), k q ∈ X \ {p} := by
    rintro ⟨t, x⟩
    by_cases hx : (x : E) ∈ Y
    · rw [hkY t x hx]
      exact x.2
    · simp only [k, if_neg hx]
      have hgx := hgD (hcell x hx)
      have hg0x := hg0 x (hcell x hx)
      have hmem := radialPush_mem_closedBall hgx hg0x t.2.1 t.2.2
      exact ⟨heX (mem_image_of_mem χ hmem),
        fun h ↦ radialPush_ne_zero hg0x t.2.1 t.2.2 (hinj hmem h0D h)⟩
  have hc2 : Continuous fun q : I × ↥(X \ {p}) ↦ (q.2 : E) :=
    continuous_subtype_val.comp continuous_snd
  have hs₁ : IsClosed {q : I × ↥(X \ {p}) | (q.2 : E) ∈ Y} :=
    hY.preimage (hc2.subtype_mk fun q ↦ q.2.2.1)
  have hs₂ : IsClosed {q : I × ↥(X \ {p}) | (q.2 : E) ∈ χ '' D} := he.preimage hc2
  have hcover : {q : I × ↥(X \ {p}) | (q.2 : E) ∈ Y} ∪ {q | (q.2 : E) ∈ χ '' D} = univ := by
    refine eq_univ_of_forall fun q ↦ ?_
    by_cases hq : (q.2 : E) ∈ Y
    · exact Or.inl hq
    · exact Or.inr (hcell q.2 hq)
  have hkc : Continuous k := by
    rw [← continuousOn_univ, ← hcover]
    refine ContinuousOn.union_of_isClosed ?_ ?_ hs₁ hs₂
    · exact hc2.continuousOn.congr fun q hq ↦ if_pos hq
    · have hG : ContinuousOn (fun q : I × ↥(X \ {p}) ↦ g q.2) {q | (q.2 : E) ∈ χ '' D} :=
        hgc.comp hc2.continuousOn fun q hq ↦ hq
      have hρ : ContinuousOn (fun q : I × ↥(X \ {p}) ↦ radialPush (q.1 : ℝ) (g q.2))
          {q | (q.2 : E) ∈ χ '' D} :=
        continuousOn_radialPush.comp
          ((continuous_subtype_val.comp continuous_fst).continuousOn.prodMk hG)
          fun q hq ↦ hg0 q.2 hq
      have hk' : ContinuousOn (fun q : I × ↥(X \ {p}) ↦ χ (radialPush (q.1 : ℝ) (g q.2)))
          {q | (q.2 : E) ∈ χ '' D} :=
        hχ.comp hρ fun q hq ↦ radialPush_mem_closedBall (hgD hq) (hg0 q.2 hq) q.1.2.1 q.1.2.2
      refine hk'.congr fun q hq ↦ ?_
      by_cases hqY : (q.2 : E) ∈ Y
      · rw [show q = (q.1, q.2) from rfl, hkY q.1 q.2 hqY]
        have hn : ‖g q.2‖ = 1 := (hχY _ (hgD hq)).1 (by rw [hχg _ hq]; exact hqY)
        change (q.2 : E) = χ (radialPush (q.1 : ℝ) (g q.2))
        rw [radialPush_of_norm_eq_one hn, hχg _ hq]
      · exact if_neg hqY
  let K : I × ↥(X \ {p}) → ↥(X \ {p}) := fun q ↦ ⟨k q, hkmem q⟩
  have hK : Continuous K := hkc.subtype_mk _
  refine ⟨⟨fun x ↦ K (1, x), hK.comp (continuous_const.prodMk continuous_id)⟩, fun x ↦ hk1 x,
    ⟨?_⟩⟩
  exact
    { toFun := K
      continuous_toFun := hK
      map_zero_left := fun x ↦ Subtype.ext (hk0 x)
      map_one_left := fun _ ↦ rfl
      prop' := fun t x hx ↦ Subtype.ext (hkY t x hx) }

/-- **A cell contracts onto any of its points**: if `χ` is continuous and injective on the closed
unit ball `D` of a normed space and `z₀ ∈ D`, then `{χ(z₀)}` is a strong deformation retract of
`χ(D)`, by the straight-line contraction of `D` onto `z₀`. -/
theorem isStrongDeformationRetract_singleton_image {χ : V → E}
    (hχ : ContinuousOn χ (closedBall 0 1)) (hinj : InjOn χ (closedBall 0 1)) {z₀ : V}
    (hz₀ : z₀ ∈ closedBall (0 : V) 1) :
    IsStrongDeformationRetract ((↑) ⁻¹' {χ z₀} : Set ↥(χ '' closedBall 0 1)) := by
  set D := closedBall (0 : V) 1 with hD
  set g := invFunOn χ D with hg
  have hDc : IsCompact D := isCompact_closedBall 0 1
  have hgc : ContinuousOn g (χ '' D) := continuousOn_invFunOn_image hDc hχ hinj
  have hgD : MapsTo g (χ '' D) D := (surjOn_image χ D).mapsTo_invFunOn
  have hχg : ∀ x ∈ χ '' D, χ (g x) = x := (surjOn_image χ D).rightInvOn_invFunOn
  have hgz₀ : g (χ z₀) = z₀ := hinj.leftInvOn_invFunOn hz₀
  have hcomb : ∀ (t : I) (x : ↥(χ '' D)), (1 - (t : ℝ)) • g x + (t : ℝ) • z₀ ∈ D :=
    fun t x ↦ convex_closedBall (0 : V) 1 (hgD x.2) hz₀ (sub_nonneg.2 t.2.2) t.2.1 (by ring)
  let K : I × ↥(χ '' D) → ↥(χ '' D) := fun q ↦
    ⟨χ ((1 - (q.1 : ℝ)) • g q.2 + (q.1 : ℝ) • z₀), mem_image_of_mem χ (hcomb q.1 q.2)⟩
  have hK : Continuous K := by
    refine Continuous.subtype_mk ?_ _
    rw [← continuousOn_univ]
    have hG : ContinuousOn (fun q : I × ↥(χ '' D) ↦ g q.2) univ :=
      hgc.comp (continuous_subtype_val.comp continuous_snd).continuousOn fun q _ ↦ q.2.2
    have ht : Continuous fun q : I × ↥(χ '' D) ↦ (q.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    refine hχ.comp (((continuous_const.sub ht).continuousOn.smul hG).add
      (ht.continuousOn.smul continuousOn_const)) fun q _ ↦ hcomb q.1 q.2
  have hK1 : ∀ x : ↥(χ '' D), (K (1, x) : E) = χ z₀ := fun x ↦ by
    simp [K]
  refine ⟨⟨fun x ↦ K (1, x), hK.comp (continuous_const.prodMk continuous_id)⟩,
    fun x ↦ hK1 x, ⟨?_⟩⟩
  exact
    { toFun := K
      continuous_toFun := hK
      map_zero_left := fun x ↦ Subtype.ext (by simp [K, hχg x x.2])
      map_one_left := fun _ ↦ rfl
      prop' := fun t x hx ↦ Subtype.ext (by
        have hx' : (x : E) = χ z₀ := hx
        change χ ((1 - (t : ℝ)) • g x + (t : ℝ) • z₀) = (x : E)
        rw [hx', hgz₀, ← add_smul, sub_add_cancel, one_smul]) }

end Deformation

/-! ### Homological consequences -/

section Homology

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C)
  {E : Type w} [TopologicalSpace E]

/-- If `A ⊆ B ⊆ X` and `A` is a strong deformation retract of `B`, the inclusion of pairs
`(X, A) ⟶ (X, B)` induces isomorphisms `H_n(X, A) ≅ H_n(X, B)` (the five lemma). -/
theorem isIso_relHomology_map_of_isStrongDeformationRetract_snd {A B X : Set E} (hAB : A ⊆ B)
    (hBX : B ⊆ X) (h : IsStrongDeformationRetract ((↑) ⁻¹' A : Set B)) (n : ℕ) :
    IsIso ((relHomology R n).map (subsetPairHom (hAB.trans hBX) hBX hAB (subset_refl X))) :=
  isIso_relHomology_map R (subsetPairHom (hAB.trans hBX) hBX hAB (subset_refl X))
    (fun m ↦ isIso_homologyMap_of_isStrongDeformationRetract R hAB h m)
    (fun m ↦ by
      have : IsIso (homologyMap ((singularChains R).map (𝟙 (TopCat.of X))) m) := by
        rw [CategoryTheory.Functor.map_id, homologyMap_id]
        infer_instance
      exact this) n

/-- Inclusions of pairs of subsets compose. -/
@[reassoc]
lemma subsetPairHom_comp {A B A' B' A'' B'' : Set E} (h : A ⊆ B) (h' : A' ⊆ B') (h'' : A'' ⊆ B'')
    (hA : A ⊆ A') (hB : B ⊆ B') (hA' : A' ⊆ A'') (hB' : B' ⊆ B'') :
    subsetPairHom h h' hA hB ≫ subsetPairHom h' h'' hA' hB' =
      subsetPairHom h h'' (hA.trans hA') (hB.trans hB') :=
  MorphismProperty.Arrow.Hom.ext rfl rfl

end Homology

section Excision

variable (R : Type u) [CommRing R] {E : Type u} [TopologicalSpace E]

/-- **Excision**, with the excised pair given up to equality: if `Z ⊆ A ⊆ X`, the closure of `Z` in
`X` lies in the interior of `A` in `X`, `X' = X ∖ Z` and `A' = A ∖ Z`, then `(X', A') ⟶ (X, A)`
induces isomorphisms in relative homology. -/
theorem excision_of_eq {X A Z X' A' : Set E} (hAX : A ⊆ X) (hA'X' : A' ⊆ X') (hA'A : A' ⊆ A)
    (hX'X : X' ⊆ X) (hX' : X' = X \ Z) (hA' : A' = A \ Z)
    (h : closure ((↑) ⁻¹' Z : Set X) ⊆ interior ((↑) ⁻¹' A : Set X)) (n : ℕ) :
    IsIso ((relHomology (ModuleCat.of R R) n).map (subsetPairHom hA'X' hAX hA'A hX'X)) := by
  subst hX' hA'
  exact excision R hAX h n

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The pair `(χ(D), χ(S))` of the images of the closed unit ball `D` and the unit sphere `S` of a
normed space under a map `χ`: for `χ` continuous and injective on `D`, a closed cell and its
boundary sphere. -/
abbrev cellPair (χ : V → E) : TopPair.{u} :=
  subsetPair (image_mono (f := χ) sphere_subset_closedBall :
    χ '' sphere (0 : V) 1 ⊆ χ '' closedBall 0 1)

omit [TopologicalSpace E] [NormedSpace ℝ V] in
lemma image_sphere_subset {Y : Set E} {χ : V → E}
    (hχY : ∀ z ∈ closedBall (0 : V) 1, χ z ∈ Y ↔ ‖z‖ = 1) : χ '' sphere (0 : V) 1 ⊆ Y := by
  rintro _ ⟨z, hz, rfl⟩
  exact (hχY z (sphere_subset_closedBall hz)).2 (mem_sphere_zero_iff_norm.1 hz)

variable [ProperSpace V] [T2Space E]

/-- **Excision for an attached cell.** Let `X = Y ∪ χ(D)`, where `D` is the closed unit ball of a
finite-dimensional normed space, `χ` is continuous and injective on `D`, `Y` is closed in `X` and
`χ(z) ∈ Y` exactly when `‖z‖ = 1`. Then the inclusion of pairs `(χ(D), χ(S)) ⟶ (X, Y)` induces
isomorphisms `H_n(χ(D), χ(S)) ≅ H_n(X, Y)` in all degrees. -/
theorem isIso_relHomology_map_cellPair {X Y : Set E} (hYX : Y ⊆ X)
    (hY : IsClosed ((↑) ⁻¹' Y : Set X)) {χ : V → E} (hχ : ContinuousOn χ (closedBall 0 1))
    (hinj : InjOn χ (closedBall 0 1)) (hχY : ∀ z ∈ closedBall (0 : V) 1, χ z ∈ Y ↔ ‖z‖ = 1)
    (hX : X = Y ∪ χ '' closedBall 0 1) (n : ℕ) :
    IsIso ((relHomology (ModuleCat.of R R) n).map
      (subsetPairHom (image_mono (f := χ) sphere_subset_closedBall) hYX (image_sphere_subset hχY)
        (subset_union_right.trans hX.symm.subset))) := by
  set p := χ 0 with hp
  set e := χ '' closedBall (0 : V) 1 with he_def
  have h0 : (0 : V) ∈ closedBall (0 : V) 1 := mem_closedBall_self zero_le_one
  have hpY : p ∉ Y := fun h ↦ by simpa using (hχY 0 h0).1 h
  have hY' : Y ⊆ X \ {p} := fun y hy ↦ ⟨hYX hy, fun h ↦ hpY (by rwa [mem_singleton_iff.1 h] at hy)⟩
  have heX : e ⊆ X := subset_union_right.trans hX.symm.subset
  have hSe : χ '' sphere (0 : V) 1 ⊆ e := image_mono (f := χ) sphere_subset_closedBall
  have hS' : χ '' sphere (0 : V) 1 ⊆ e \ {p} := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hSe ⟨z, hz, rfl⟩, fun h ↦ ?_⟩
    have := hinj (sphere_subset_closedBall hz) h0 (mem_singleton_iff.1 h)
    rw [this, mem_sphere_zero_iff_norm, norm_zero] at hz
    exact zero_ne_one hz
  -- `(X, Y) ⟶ (X, X ∖ {p})`
  have i₁ := isIso_relHomology_map_of_isStrongDeformationRetract_snd (ModuleCat.of R R) hY'
    sdiff_subset (isStrongDeformationRetract_sdiff_center hY hχ hinj hχY hX) n
  -- `(e, e ∖ {p}) ⟶ (X, X ∖ {p})`, by excision of `X ∖ e`
  have hopen : IsOpen ((↑) ⁻¹' (X \ {p}) : Set X) := by
    have : ((↑) ⁻¹' (X \ {p}) : Set X) = (↑) ⁻¹' {p}ᶜ := by
      ext x
      simp
    rw [this]
    exact isOpen_compl_singleton.preimage continuous_subtype_val
  have i₂ : IsIso ((relHomology (ModuleCat.of R R) n).map
      (subsetPairHom (sdiff_subset : e \ {p} ⊆ e) (sdiff_subset : X \ {p} ⊆ X)
        (sdiff_subset_sdiff_left heX) heX)) := by
    refine excision_of_eq R (Z := X \ e) sdiff_subset _ _ _ (sdiff_sdiff_cancel_left heX).symm
      ?_ ?_ n
    · ext x
      simp only [mem_sdiff, mem_singleton_iff, not_and, not_not]
      exact ⟨fun h ↦ ⟨⟨heX h.1, h.2⟩, fun _ ↦ h.1⟩, fun h ↦ ⟨h.2 h.1.1, h.1.2⟩⟩
    · have hZY : ((↑) ⁻¹' (X \ e) : Set X) ⊆ (↑) ⁻¹' Y :=
        fun x hx ↦ (hX.subset x.2).resolve_right hx.2
      calc closure ((↑) ⁻¹' (X \ e) : Set X) ⊆ (↑) ⁻¹' Y := closure_minimal hZY hY
        _ ⊆ (↑) ⁻¹' (X \ {p}) := preimage_mono hY'
        _ = interior _ := hopen.interior_eq.symm
  -- `(e, χ(S)) ⟶ (e, e ∖ {p})`
  have hSc : IsClosed ((↑) ⁻¹' (χ '' sphere (0 : V) 1) : Set e) :=
    ((isCompact_sphere (0 : V) 1).image_of_continuousOn
      (hχ.mono sphere_subset_closedBall)).isClosed.preimage continuous_subtype_val
  have hχS : ∀ z ∈ closedBall (0 : V) 1, χ z ∈ χ '' sphere (0 : V) 1 ↔ ‖z‖ = 1 := by
    intro z hz
    constructor
    · rintro ⟨w, hw, hwz⟩
      rw [← hinj (sphere_subset_closedBall hw) hz hwz]
      exact mem_sphere_zero_iff_norm.1 hw
    · exact fun h ↦ ⟨z, mem_sphere_zero_iff_norm.2 h, rfl⟩
  have i₃ := isIso_relHomology_map_of_isStrongDeformationRetract_snd (ModuleCat.of R R) hS'
    sdiff_subset (isStrongDeformationRetract_sdiff_center hSc hχ hinj hχS
      (union_eq_right.2 hSe).symm) n
  -- the square of inclusions
  have hsq := congrArg (relHomology (ModuleCat.of R R) n).map
    ((subsetPairHom_comp (image_mono (f := χ) sphere_subset_closedBall) hYX sdiff_subset
      (image_sphere_subset hχY) heX hY' (subset_refl X)).trans
    (subsetPairHom_comp (image_mono (f := χ) sphere_subset_closedBall) sdiff_subset sdiff_subset
      hS' (subset_refl e) (sdiff_subset_sdiff_left heX) heX).symm)
  rw [Functor.map_comp, Functor.map_comp] at hsq
  have : IsIso ((relHomology (ModuleCat.of R R) n).map
      (subsetPairHom (image_mono (f := χ) sphere_subset_closedBall) hYX (image_sphere_subset hχY)
        heX) ≫ (relHomology (ModuleCat.of R R) n).map
      (subsetPairHom hYX sdiff_subset hY' (subset_refl X))) := by
    rw [hsq]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((relHomology (ModuleCat.of R R) n).map (subsetPairHom hYX sdiff_subset hY' (subset_refl X)))

end Excision

end Morse.Homology
