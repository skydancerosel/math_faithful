import Mathlib
import Morse.Homotopy.ChangeOfBase
import Morse.Homotopy.PushOff
import Morse.Chapter2.CellPatch
import Morse.Appendix.MonotoneUnion

/-!
# The homotopy groups of a space with cells attached

Milnor's Theorem 22.1 and both Bott periodicity theorems rest on the fact that attaching cells of
dimension `λ` to a space `Y` does not change `π_i` for `i ≤ λ - 2`, and is onto on `π_{λ-1}`. This
file proves it for the adjunction spaces of the project: `X = Y ∪_φ e^λ` is the pushout in
`TopCat` of `Y ← S^{λ-1} → D^λ` (`Morse.AttachCell φ`), and iterated adjunction spaces are
`Morse.IsRelCellAttachment`.

## Main results

* `Morse.Homotopy.exists_homotopicRel_avoid_ball`: **the push-off lemma** (Hatcher, Lemma 4.10).
  If `P` is compact and embeds continuously in a real vector space of dimension `< λ` (for
  instance a cube `I^N` with `|N| < λ`), every map `f : P → Y ∪_φ e^λ` is homotopic, relative to
  the part of `P` mapped outside the closed ball of radius `3/4` of the cell, to a map missing a
  ball about the centre of the cell.
* `Morse.Homotopy.exists_homotopicRel_into_range`: **the radial push**: a map missing a ball about
  the centre is homotopic, relative to the preimage of `Y`, to a map into `Y`.
* `Morse.Homotopy.compresses_cellInl`: the two together: every map `f : P → Y ∪_φ e^λ` is
  homotopic, relative to `f⁻¹(Y)`, to a map into `Y`.
* `Morse.Homotopy.bijective_homotopyGroupMap_cellInl`,
  `Morse.Homotopy.surjective_homotopyGroupMap_cellInl`: for any basepoint `y ∈ Y`, the inclusion
  `Y → Y ∪_φ e^λ` induces a bijection on `π_i` for `i ≤ λ - 2` and a surjection for `i = λ - 1`
  (`π_i` is Mathlib's `HomotopyGroup N` with `|N| = i`, for instance `π_ i`).
* `Morse.Homotopy.bijective_homotopyGroupMap_of_isRelCellAttachment`, `…surjective…`: the same
  for finitely many cells, all of dimension `≥ λ`, attached one at a time.
* `Morse.Homotopy.bijective_homotopyGroupMap_of_isPushout`: for any pushout square of the shape of
  an attached cell, and `Morse.Homotopy.bijective_homotopyGroupMap_union_cell`: for a cell embedded
  in a Hausdorff space and meeting a closed set `A` exactly in its boundary (the cells of Milnor's
  Theorem 3.2), the inclusion `A → A ∪ e^λ`. The push-off itself in these forms:
  `Morse.Homotopy.compresses_of_isPushout`, `Morse.Homotopy.compresses_union_cell`.

## Proof

**Point-set topology of `X = Y ∪_φ e^λ`.** The maps `Y → X` and `D^λ → X` are jointly onto, and
`inl` is injective and meets `inr(d)` only for `d ∈ S^{λ-1}` (the pushout in `Type`, preserved by
the forgetful functor); a set is closed iff its preimages in `Y` and `D^λ` are (the colimit
topology), so `inl` is a closed embedding (`Morse.Homotopy.isClosedEmbedding_cellInl`). The
**probe** `X → ℝ^λ × ℝ`, `0` on `Y` and `((1 - ‖z‖) z, 1 - ‖z‖)` at the point `z` of the cell
(`Morse.Homotopy.cellProbe`), is continuous by the universal property; its second coordinate, the
**height** `1 - ‖z‖` (`Morse.Homotopy.cellHeight`), vanishes exactly on `Y`, and on the open cell
`{height > 0}` the **coordinate** `z = (first coordinate) / height` (`Morse.Homotopy.cellCoord`)
is continuous. So the open cell is open, its coordinate is continuous, and
`{‖z‖ ≤ r} = {height ≥ 1 - r}` is closed in `X` for `r < 1`: everything the push-off needs,
without any separation axiom on `Y`.

**The push-off.** On `W = f⁻¹(open cell)` the coordinate `h = z ∘ f` is deformed, by
`Morse.Homotopy.exists_pushOff`, relative to `{‖h‖ ≥ 3/4}`, to a map missing a ball `‖z‖ < ε`; the
deformation, read in the cell, pastes with the constant homotopy of `f` outside
`f⁻¹{‖z‖ ≤ 3/4}`. Then the **radial push** `z ↦ clamp((1 + t(ε⁻¹ - 1)) z)` of the cell, which is
the identity on `S^{λ-1}`, extends by the identity of `Y` to a homotopy of `X`
(`Morse.Homotopy.cellRadial`: a map out of `X` into `C(I, X)`, by the universal property, then
uncurried); at time `1` it maps `{‖z‖ ≥ ε}` into `S^{λ-1} ⊆ Y`. No puncture is needed: the radial
push expands the small ball onto the whole cell instead of removing its centre.

**Homotopy groups.** Compression of maps from `I^N` gives surjectivity on `π_N` and compression of
maps from `I × I^N` injectivity (`Morse/Homotopy/Basic.lean`); `I^N` embeds in `ℝ^N` and
`I × I^N` in `ℝ × ℝ^N`.
-/

open Set Metric Function Module Topology CategoryTheory CategoryTheory.Limits TopCat
open scoped unitInterval Topology.Homotopy

universe u

noncomputable section

namespace Morse.Homotopy

open Morse (AttachCell cellInl cellInr cellDesc cellDesc_inl cellDesc_inr dvec svec diskPt
  norm_dvec_le norm_svec continuous_dvec cellInl_apply_eq disk_ext dvec_diskPt dvec_inclusion
  IsRelCellAttachment)

/-! ### Clamping to the closed unit ball -/

section Clamp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial retraction `z ↦ z / max(1, ‖z‖)` of `E` onto its closed unit ball. -/
def clampBall (z : E) : E :=
  (max 1 ‖z‖)⁻¹ • z

theorem continuous_clampBall : Continuous (clampBall (E := E)) :=
  ((continuous_const.max continuous_norm).inv₀ fun _ => (lt_max_of_lt_left one_pos).ne').smul
    continuous_id

theorem norm_clampBall (z : E) : ‖clampBall z‖ = min 1 ‖z‖ := by
  have hm : 0 < max 1 ‖z‖ := lt_max_of_lt_left one_pos
  rw [clampBall, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hm]
  rcases le_total ‖z‖ 1 with h | h
  · rw [max_eq_left h, min_eq_right h, inv_one, one_mul]
  · rw [max_eq_right h, min_eq_left h, inv_mul_cancel₀ (by linarith)]

theorem norm_clampBall_le (z : E) : ‖clampBall z‖ ≤ 1 := by
  rw [norm_clampBall]
  exact min_le_left _ _

theorem clampBall_of_norm_le {z : E} (h : ‖z‖ ≤ 1) : clampBall z = z := by
  rw [clampBall, max_eq_left h, inv_one, one_smul]

/-- **The radial push** `σ_t(z) = clamp((1 + t(ε⁻¹ - 1)) z)`: the identity at `t = 0` and on the
unit sphere; at `t = 1` it maps `{‖z‖ ≥ ε}` to the unit sphere. -/
def radialPush (ε : ℝ) (t : I) (z : E) : E :=
  clampBall ((1 + (t : ℝ) * (ε⁻¹ - 1)) • z)

theorem continuous_radialPush (ε : ℝ) :
    Continuous fun q : I × E => radialPush ε q.1 q.2 :=
  continuous_clampBall.comp ((continuous_const.add ((continuous_subtype_val.comp continuous_fst).mul
    continuous_const)).smul continuous_snd)

theorem radialPush_zero (ε : ℝ) {z : E} (h : ‖z‖ ≤ 1) : radialPush ε 0 z = z := by
  rw [radialPush, Set.Icc.coe_zero, zero_mul, add_zero, one_smul, clampBall_of_norm_le h]

theorem radialPush_of_norm_eq_one {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (t : I) {z : E}
    (h : ‖z‖ = 1) : radialPush ε t z = z := by
  have hc : 1 ≤ 1 + (t : ℝ) * (ε⁻¹ - 1) := by
    have : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.2 hε1
    nlinarith [t.2.1]
  rw [radialPush, clampBall, norm_smul, h, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith),
    max_eq_right hc, smul_smul, inv_mul_cancel₀ (by linarith), one_smul]

theorem norm_radialPush_one {ε : ℝ} (hε : 0 < ε) {z : E} (h : ε ≤ ‖z‖) :
    ‖radialPush ε 1 z‖ = 1 := by
  rw [radialPush, norm_clampBall, Set.Icc.coe_one, one_mul, add_sub_cancel, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε)]
  exact min_eq_left ((one_le_inv_mul₀ hε).2 h)

theorem norm_radialPush_le (ε : ℝ) (t : I) (z : E) : ‖radialPush ε t z‖ ≤ 1 :=
  norm_clampBall_le _

end Clamp

/-! ### Point-set topology of `Y ∪_φ e^n` -/

variable {n : ℕ} {Y : TopCat.{u}} (φ : ∂𝔻 n ⟶ Y)

instance : T2Space (𝔻 n) :=
  inferInstanceAs (T2Space (ULift (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)))

instance : CompactSpace (∂𝔻 n) :=
  inferInstanceAs (CompactSpace (ULift (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))

theorem injective_diskBoundaryInclusion : Function.Injective (diskBoundaryInclusion n) :=
  fun _ _ hab =>
    ULift.ext _ _ (Subtype.ext (congrArg (fun d : 𝔻 n => (d.down : EuclideanSpace ℝ (Fin n))) hab))

/-- The pushout square of `Y ∪_φ e^n`, flipped and forgotten to `Type`. -/
theorem isPushout_forget : IsPushout ((forget TopCat).map (diskBoundaryInclusion n))
    ((forget TopCat).map φ) ((forget TopCat).map (cellInr φ)) ((forget TopCat).map (cellInl φ)) :=
  (IsPushout.of_hasPushout φ (diskBoundaryInclusion n)).flip.map (forget TopCat)

/-- `Y ∪_φ e^n` is the union of the images of `Y` and of the disk. -/
theorem exists_eq_cellInl_or_cellInr (x : AttachCell φ) :
    (∃ y, cellInl φ y = x) ∨ ∃ d, cellInr φ d = x :=
  Types.eq_or_eq_of_isPushout
    ((IsPushout.of_hasPushout φ (diskBoundaryInclusion n)).map (forget TopCat)) x

theorem cellInl_injective : Function.Injective (cellInl φ) :=
  Types.pushoutCocone_inr_injective_of_isColimit (isPushout_forget φ).isColimit
    injective_diskBoundaryInclusion

/-- A point of the disk and a point of `Y` are identified only along the attaching map. -/
theorem cellInr_eq_cellInl_iff (d : 𝔻 n) (y : Y) :
    cellInr φ d = cellInl φ y ↔ ∃ s, diskBoundaryInclusion n s = d ∧ φ s = y :=
  Types.pushoutCocone_inl_eq_inr_iff_of_isColimit (isPushout_forget φ).isColimit
    injective_diskBoundaryInclusion d y

/-- **The colimit topology**: a set is closed iff its preimages in `Y` and in the disk are. -/
theorem isClosed_attachCell_iff (S : Set (AttachCell φ)) :
    IsClosed S ↔ IsClosed (cellInl φ ⁻¹' S) ∧ IsClosed (cellInr φ ⁻¹' S) := by
  refine ⟨fun h => ⟨h.preimage (cellInl φ).hom.continuous, h.preimage (cellInr φ).hom.continuous⟩,
    fun ⟨h1, h2⟩ => ?_⟩
  refine (TopCat.isClosed_iff_of_isColimit _ (pushoutIsPushout φ (diskBoundaryInclusion n)) S).2 ?_
  rintro (_ | _ | _)
  · exact h1.preimage φ.hom.continuous
  · exact h1
  · exact h2

/-- **`Y → Y ∪_φ e^n` is a closed embedding.** -/
theorem isClosedEmbedding_cellInl : IsClosedEmbedding (cellInl φ) := by
  refine .of_continuous_injective_isClosedMap (cellInl φ).hom.continuous (cellInl_injective φ)
    fun C hC => ?_
  rw [isClosed_attachCell_iff]
  refine ⟨by rwa [preimage_image_eq _ (cellInl_injective φ)], ?_⟩
  have : cellInr φ ⁻¹' (cellInl φ '' C) = diskBoundaryInclusion n '' (φ ⁻¹' C) := by
    ext d
    simp only [mem_preimage, mem_image]
    constructor
    · rintro ⟨y, hy, hyd⟩
      obtain ⟨s, hs, rfl⟩ := (cellInr_eq_cellInl_iff φ d y).1 hyd.symm
      exact ⟨s, hy, hs⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨φ s, hs, (cellInl_apply_eq φ s)⟩
  rw [this]
  exact ((hC.preimage φ.hom.continuous).isCompact.image
    (diskBoundaryInclusion n).hom.continuous).isClosed

/-! ### The probe: height and coordinate in the cell -/

/-- **The probe** `Y ∪_φ e^n → ℝⁿ × ℝ`: `0` on `Y`, `((1 - ‖z‖) z, 1 - ‖z‖)` at the point `z` of
the cell. -/
def cellProbe : AttachCell φ ⟶ TopCat.of (ULift.{u} (EuclideanSpace ℝ (Fin n) × ℝ)) :=
  cellDesc φ (ContinuousMap.const _ (ULift.up (0, 0)))
    ⟨fun d => ULift.up ((1 - ‖dvec d‖) • dvec d, 1 - ‖dvec d‖),
      continuous_uliftUp.comp
        (((continuous_const.sub (continuous_norm.comp continuous_dvec)).smul continuous_dvec).prodMk
          (continuous_const.sub (continuous_norm.comp continuous_dvec)))⟩
    (fun s => by
      change ULift.up ((0 : EuclideanSpace ℝ (Fin n)), (0 : ℝ)) =
        ULift.up ((1 - ‖svec s‖) • svec s, 1 - ‖svec s‖)
      rw [norm_svec, sub_self, zero_smul])

/-- The height `1 - ‖z‖` of the point `z` of the cell; `0` on `Y`. -/
def cellHeight (x : AttachCell φ) : ℝ :=
  (cellProbe φ x).down.2

/-- The coordinate `z` of a point of the open cell (`0` on `Y`). -/
def cellCoord (x : AttachCell φ) : EuclideanSpace ℝ (Fin n) :=
  (cellHeight φ x)⁻¹ • (cellProbe φ x).down.1

theorem continuous_cellHeight : Continuous (cellHeight φ) :=
  continuous_snd.comp (continuous_uliftDown.comp (cellProbe φ).hom.continuous)

theorem continuousOn_cellCoord : ContinuousOn (cellCoord φ) {x | 0 < cellHeight φ x} :=
  ((continuous_cellHeight φ).continuousOn.inv₀ fun _ hx => (ne_of_gt hx)).smul
    (continuous_fst.comp (continuous_uliftDown.comp (cellProbe φ).hom.continuous)).continuousOn

theorem cellProbe_inl (y : Y) : cellProbe φ (cellInl φ y) = ULift.up (0, 0) := by
  rw [cellProbe, cellDesc_inl]
  rfl

theorem cellProbe_inr (d : 𝔻 n) :
    cellProbe φ (cellInr φ d) = ULift.up ((1 - ‖dvec d‖) • dvec d, 1 - ‖dvec d‖) := by
  rw [cellProbe, cellDesc_inr]
  rfl

theorem cellHeight_inl (y : Y) : cellHeight φ (cellInl φ y) = 0 := by
  rw [cellHeight, cellProbe_inl]

theorem cellHeight_inr (d : 𝔻 n) : cellHeight φ (cellInr φ d) = 1 - ‖dvec d‖ := by
  rw [cellHeight, cellProbe_inr]

theorem cellCoord_inr {d : 𝔻 n} (hd : ‖dvec d‖ < 1) : cellCoord φ (cellInr φ d) = dvec d := by
  have h : (1 : ℝ) - ‖dvec d‖ ≠ 0 := by linarith
  rw [cellCoord, cellHeight_inr, cellProbe_inr, smul_smul, inv_mul_cancel₀ h, one_smul]

theorem cellHeight_nonneg (x : AttachCell φ) : 0 ≤ cellHeight φ x := by
  rcases exists_eq_cellInl_or_cellInr φ x with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · rw [cellHeight_inl]
  · rw [cellHeight_inr]
    linarith [norm_dvec_le d]

theorem cellInr_mem_range_of_norm_eq_one {d : 𝔻 n} (hd : ‖dvec d‖ = 1) :
    cellInr φ d ∈ range (cellInl φ) := by
  refine ⟨φ (Morse.spherePt (dvec d) hd), ?_⟩
  rw [cellInl_apply_eq]
  exact congrArg (cellInr φ) (disk_ext rfl)

/-- `Y` is the zero set of the height. -/
theorem mem_range_cellInl_iff (x : AttachCell φ) :
    x ∈ range (cellInl φ) ↔ cellHeight φ x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact cellHeight_inl φ y
  · intro hx
    rcases exists_eq_cellInl_or_cellInr φ x with ⟨y, rfl⟩ | ⟨d, rfl⟩
    · exact ⟨y, rfl⟩
    · rw [cellHeight_inr] at hx
      exact cellInr_mem_range_of_norm_eq_one φ (by linarith)

/-- A point of positive height is a point of the open cell. -/
theorem exists_cellInr_of_cellHeight_pos {x : AttachCell φ} (hx : 0 < cellHeight φ x) :
    ∃ d, ‖dvec d‖ < 1 ∧ cellInr φ d = x := by
  rcases exists_eq_cellInl_or_cellInr φ x with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · rw [cellHeight_inl] at hx
    exact absurd hx (lt_irrefl 0)
  · rw [cellHeight_inr] at hx
    exact ⟨d, by linarith, rfl⟩

theorem norm_cellCoord {x : AttachCell φ} (hx : 0 < cellHeight φ x) :
    ‖cellCoord φ x‖ = 1 - cellHeight φ x := by
  obtain ⟨d, hd, rfl⟩ := exists_cellInr_of_cellHeight_pos φ hx
  rw [cellCoord_inr φ hd, cellHeight_inr]
  ring

/-- The characteristic map of the cell, on all of `ℝⁿ` (clamped to the closed ball). -/
def cellChar (z : EuclideanSpace ℝ (Fin n)) : AttachCell φ :=
  cellInr φ (diskPt (clampBall z) (norm_clampBall_le z))

theorem continuous_cellChar : Continuous (cellChar φ) :=
  (cellInr φ).hom.continuous.comp (continuous_uliftUp.comp
    ((continuous_clampBall).subtype_mk _))

theorem cellChar_of_norm_le {z : EuclideanSpace ℝ (Fin n)} (hz : ‖z‖ ≤ 1) :
    cellChar φ z = cellInr φ (diskPt z hz) :=
  congrArg (cellInr φ) (disk_ext (by simp [clampBall_of_norm_le hz]))

theorem cellChar_cellCoord {x : AttachCell φ} (hx : 0 < cellHeight φ x) :
    cellChar φ (cellCoord φ x) = x := by
  obtain ⟨d, hd, rfl⟩ := exists_cellInr_of_cellHeight_pos φ hx
  rw [cellChar_of_norm_le φ (by rw [cellCoord_inr φ hd]; exact hd.le)]
  exact congrArg (cellInr φ) (disk_ext (by simp [cellCoord_inr φ hd]))

theorem cellCoord_cellChar {z : EuclideanSpace ℝ (Fin n)} (hz : ‖z‖ < 1) :
    cellCoord φ (cellChar φ z) = z := by
  rw [cellChar_of_norm_le φ hz.le, cellCoord_inr φ (by simpa using hz), dvec_diskPt]

theorem cellHeight_cellChar {z : EuclideanSpace ℝ (Fin n)} (hz : ‖z‖ ≤ 1) :
    cellHeight φ (cellChar φ z) = 1 - ‖z‖ := by
  rw [cellChar_of_norm_le φ hz, cellHeight_inr, dvec_diskPt]

/-! ### The radial push of the cell -/

section Radial

variable {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)

/-- The radial push on the disk, as a map `D^n → C(I, Y ∪_φ e^n)`. -/
def radialDisk (ε : ℝ) : C(𝔻 n, C(I, AttachCell φ)) :=
  ContinuousMap.curry
    ⟨fun q : 𝔻 n × I => cellInr φ (diskPt (radialPush ε q.2 (dvec q.1))
      (norm_radialPush_le ε q.2 (dvec q.1))),
      (cellInr φ).hom.continuous.comp (continuous_uliftUp.comp (((continuous_radialPush ε).comp
        (continuous_snd.prodMk (continuous_dvec.comp continuous_fst))).subtype_mk _))⟩

include hε hε1 in
theorem radialDisk_compat (s : ∂𝔻 n) :
    ContinuousMap.curry ((cellInl φ).hom.comp ContinuousMap.fst) (φ s) =
      radialDisk φ ε (diskBoundaryInclusion n s) := by
  ext t
  change cellInl φ (φ s) = cellInr φ (diskPt (radialPush ε t (dvec (diskBoundaryInclusion n s))) _)
  rw [cellInl_apply_eq]
  exact congrArg (cellInr φ) (disk_ext (by
    rw [dvec_diskPt, dvec_inclusion, radialPush_of_norm_eq_one hε hε1 t (norm_svec s)]))

/-- **The radial push of `Y ∪_φ e^n`**: the identity on `Y`, and `σ_t` on the cell
(`Morse.Homotopy.radialPush`). A map `Y ∪_φ e^n → C(I, Y ∪_φ e^n)` by the universal property,
uncurried (`I` is locally compact). -/
def cellRadial : C(I × AttachCell φ, AttachCell φ) :=
  (ContinuousMap.uncurry (cellDesc φ (Z := TopCat.of C(I, AttachCell φ))
    (ContinuousMap.curry ((cellInl φ).hom.comp ContinuousMap.fst))
    (radialDisk φ ε) (radialDisk_compat φ hε hε1)).hom).comp ContinuousMap.prodSwap

theorem cellRadial_inl (t : I) (y : Y) : cellRadial φ hε hε1 (t, cellInl φ y) = cellInl φ y := by
  change (cellDesc φ (Z := TopCat.of C(I, AttachCell φ))
    (ContinuousMap.curry ((cellInl φ).hom.comp ContinuousMap.fst))
    (radialDisk φ ε) (radialDisk_compat φ hε hε1)) (cellInl φ y) t = _
  rw [cellDesc_inl]
  rfl

theorem cellRadial_inr (t : I) (d : 𝔻 n) : cellRadial φ hε hε1 (t, cellInr φ d) =
    cellInr φ (diskPt (radialPush ε t (dvec d)) (norm_radialPush_le ε t (dvec d))) := by
  change (cellDesc φ (Z := TopCat.of C(I, AttachCell φ))
    (ContinuousMap.curry ((cellInl φ).hom.comp ContinuousMap.fst))
    (radialDisk φ ε) (radialDisk_compat φ hε hε1)) (cellInr φ d) t = _
  rw [cellDesc_inr]
  rfl

theorem cellRadial_zero (x : AttachCell φ) : cellRadial φ hε hε1 (0, x) = x := by
  rcases exists_eq_cellInl_or_cellInr φ x with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · exact cellRadial_inl φ hε hε1 0 y
  · rw [cellRadial_inr]
    exact congrArg (cellInr φ) (disk_ext (by rw [dvec_diskPt, radialPush_zero ε (norm_dvec_le d)]))

theorem cellRadial_of_mem_range {x : AttachCell φ} (hx : x ∈ range (cellInl φ)) (t : I) :
    cellRadial φ hε hε1 (t, x) = x := by
  obtain ⟨y, rfl⟩ := hx
  exact cellRadial_inl φ hε hε1 t y

theorem cellRadial_one_mem {x : AttachCell φ} (hx : 0 < cellHeight φ x → ε ≤ ‖cellCoord φ x‖) :
    cellRadial φ hε hε1 (1, x) ∈ range (cellInl φ) := by
  rcases exists_eq_cellInl_or_cellInr φ x with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · rw [cellRadial_inl]
    exact mem_range_self y
  · rw [cellRadial_inr]
    apply cellInr_mem_range_of_norm_eq_one
    rw [dvec_diskPt]
    rcases (norm_dvec_le d).lt_or_eq with hd | hd
    · have hpos : 0 < cellHeight φ (cellInr φ d) := by rw [cellHeight_inr]; linarith
      have := hx hpos
      rw [cellCoord_inr φ hd] at this
      exact norm_radialPush_one hε this
    · exact (radialPush_of_norm_eq_one hε hε1 1 hd).symm ▸ hd

end Radial

/-! ### The push-off lemma for an attached cell -/

/-- A homotopy relative to `S`, from its values. -/
def homotopyRelOfFun {P Z : Type*} [TopologicalSpace P] [TopologicalSpace Z] {f g : C(P, Z)}
    {S : Set P} (F : C(I × P, Z)) (h0 : ∀ p, F (0, p) = f p) (h1 : ∀ p, F (1, p) = g p)
    (hS : ∀ t, ∀ p ∈ S, F (t, p) = f p) : f.HomotopyRel g S where
  toFun := F
  continuous_toFun := F.continuous
  map_zero_left := h0
  map_one_left := h1
  prop' t p hp := hS t p hp

/-- **The push-off lemma** (Hatcher, Lemma 4.10): if `P` is compact and embeds continuously in a
real vector space `V` with `dim V < n`, every map `f : P → Y ∪_φ e^n` is homotopic, relative to
the part `{height < 1/4}` of `P` mapped into `Y` or outside the closed ball of radius `3/4` of the
cell, to a map which misses a whole ball `{‖z‖ < ε}` about the centre of the cell. -/
theorem exists_homotopicRel_avoid_ball {P : Type*} [TopologicalSpace P] [CompactSpace P]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hV : finrank ℝ V < n) {ι : P → V} (hι : Continuous ι) (hinj : Function.Injective ι)
    (f : C(P, AttachCell φ)) :
    ∃ g : C(P, AttachCell φ), ∃ ε > 0, (∀ p, 0 < cellHeight φ (g p) → ε ≤ ‖cellCoord φ (g p)‖) ∧
      f.HomotopicRel g {p | cellHeight φ (f p) < 1 / 4} := by
  set W : Set P := {p | 0 < cellHeight φ (f p)}
  have hfh : Continuous fun p => cellHeight φ (f p) := (continuous_cellHeight φ).comp f.continuous
  have hW : IsOpen W := isOpen_lt continuous_const hfh
  set h : P → EuclideanSpace ℝ (Fin n) := fun p => cellCoord φ (f p)
  have hh : ContinuousOn h W :=
    (continuousOn_cellCoord φ).comp f.continuous.continuousOn fun p hp => hp
  have hlt : ∀ p ∈ W, ‖h p‖ < 1 := fun p hp => by
    change ‖cellCoord φ (f p)‖ < 1
    rw [norm_cellCoord φ hp]
    linarith [show 0 < cellHeight φ (f p) from hp]
  have hC : IsClosed {p | p ∈ W ∧ ‖h p‖ ≤ 3 / 4} := by
    have : {p | p ∈ W ∧ ‖h p‖ ≤ 3 / 4} = {p | 1 / 4 ≤ cellHeight φ (f p)} := by
      ext p
      simp only [Set.mem_ofPred_eq, W, h]
      constructor
      · rintro ⟨hp, hle⟩
        rw [norm_cellCoord φ hp] at hle
        linarith
      · intro hp
        have hp' : 0 < cellHeight φ (f p) := by linarith
        exact ⟨hp', by rw [norm_cellCoord φ hp']; linarith⟩
    rw [this]
    exact isClosed_le continuous_const hfh
  obtain ⟨H, hHc, hH0, hHfar, hHlt, ε, hε, hHε⟩ :=
    exists_pushOff (by rwa [finrank_euclideanSpace_fin]) hι hinj hh hlt hC
  -- the push-off, read in the cell, and constant outside `f⁻¹{‖z‖ ≤ 3/4}`
  let F : I × P → AttachCell φ := fun q =>
    if 0 < cellHeight φ (f q.2) then cellChar φ (H q) else f q.2
  have hFf : ∀ q : I × P, cellHeight φ (f q.2) < 1 / 4 → F q = f q.2 := by
    intro q hq
    simp only [F]
    split_ifs with hpos
    · have h34 : 3 / 4 ≤ ‖h q.2‖ := by
        change 3 / 4 ≤ ‖cellCoord φ (f q.2)‖
        rw [norm_cellCoord φ hpos]
        linarith
      rw [show H q = H (q.1, q.2) from rfl, hHfar q.1 q.2 h34]
      exact cellChar_cellCoord φ hpos
    · rfl
  have hFc : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro q
    by_cases hq : 0 < cellHeight φ (f q.2)
    · have hU : {q : I × P | 0 < cellHeight φ (f q.2)} ∈ 𝓝 q :=
        (isOpen_lt continuous_const (hfh.comp continuous_snd)).mem_nhds hq
      have hcont : ContinuousAt (fun q => cellChar φ (H q)) q :=
        (continuous_cellChar φ).continuousAt.comp
          (hHc.continuousAt (prod_mem_nhds Filter.univ_mem (hW.mem_nhds hq)))
      refine hcont.congr (Filter.eventually_of_mem hU fun q' hq' => ?_)
      simp only [F, if_pos (show 0 < cellHeight φ (f q'.2) from hq')]
    · have hq0 : cellHeight φ (f q.2) < 1 / 4 := by
        linarith [not_lt.1 hq, cellHeight_nonneg φ (f q.2)]
      have hU : {q : I × P | cellHeight φ (f q.2) < 1 / 4} ∈ 𝓝 q :=
        (isOpen_lt (hfh.comp continuous_snd) continuous_const).mem_nhds hq0
      exact (f.continuous.comp continuous_snd).continuousAt.congr
        (Filter.eventually_of_mem hU fun q' hq' => (hFf q' hq').symm)
  let g : C(P, AttachCell φ) := ⟨fun p => F (1, p), hFc.comp (continuous_const.prodMk
    continuous_id)⟩
  refine ⟨g, ε, hε, fun p hpos => ?_, ⟨homotopyRelOfFun ⟨F, hFc⟩ (fun p => ?_) (fun p => rfl)
    fun t p hp => hFf (t, p) hp⟩⟩
  · change 0 < cellHeight φ (F (1, p)) at hpos
    change ε ≤ ‖cellCoord φ (F (1, p))‖
    by_cases hp : 0 < cellHeight φ (f p)
    · have hF : F (1, p) = cellChar φ (H (1, p)) := if_pos hp
      rw [hF, cellCoord_cellChar φ (hHlt 1 p hp)]
      exact hHε p hp
    · have hF : F (1, p) = f p := if_neg hp
      rw [hF] at hpos
      exact absurd hpos hp
  · change F (0, p) = f p
    simp only [F]
    split_ifs with hpos
    · rw [hH0]
      exact cellChar_cellCoord φ hpos
    · rfl

/-- **The radial push into `Y`**: a map `g : P → Y ∪_φ e^n` missing the ball `{‖z‖ < ε}` of the
cell is homotopic, relative to `g⁻¹(Y)`, to a map into `Y` (Milnor's and Hatcher's radial
deformation of the punctured cell onto its boundary, here an expansion of the small ball). -/
theorem exists_homotopicRel_into_range {P : Type*} [TopologicalSpace P] (g : C(P, AttachCell φ))
    {ε : ℝ} (hε : 0 < ε) (hg : ∀ p, 0 < cellHeight φ (g p) → ε ≤ ‖cellCoord φ (g p)‖) :
    ∃ g' : C(P, AttachCell φ), (∀ p, g' p ∈ range (cellInl φ)) ∧
      g.HomotopicRel g' (g ⁻¹' range (cellInl φ).hom) := by
  have hε1 : min ε (1 / 4) ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hε' : 0 < min ε (1 / 4) := lt_min hε (by norm_num)
  let R := cellRadial φ hε' hε1
  let g' : C(P, AttachCell φ) := ⟨fun p => R (1, g p), R.continuous.comp
    (continuous_const.prodMk g.continuous)⟩
  refine ⟨g', fun p => cellRadial_one_mem φ hε' hε1 fun hpos => (min_le_left _ _).trans
    (hg p hpos), ⟨homotopyRelOfFun (R.comp ((ContinuousMap.id I).prodMap g)) (fun p => ?_)
      (fun p => rfl) fun t p hp => cellRadial_of_mem_range φ hε' hε1 hp t⟩⟩
  exact cellRadial_zero φ hε' hε1 (g p)

/-- **Compression into `Y`** (the push-off lemma followed by the radial push): if `P` is compact
and embeds continuously in a real vector space `V` with `dim V < n`, every map
`f : P → Y ∪_φ e^n` is homotopic, relative to `f⁻¹(Y)`, to a map into `Y`. -/
theorem compresses_cellInl {P : Type*} [TopologicalSpace P] [CompactSpace P]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hV : finrank ℝ V < n) {ι : P → V} (hι : Continuous ι) (hinj : Function.Injective ι) :
    Compresses (cellInl φ).hom P := by
  intro f
  obtain ⟨g, ε, hε, hg, ⟨F⟩⟩ := exists_homotopicRel_avoid_ball φ hV hι hinj f
  have hS : f ⁻¹' range (cellInl φ).hom ⊆ {p | cellHeight φ (f p) < 1 / 4} := fun p hp => by
    change cellHeight φ (f p) < 1 / 4
    rw [(mem_range_cellInl_iff φ (f p)).1 hp]
    norm_num
  obtain ⟨g', hg', ⟨G⟩⟩ := exists_homotopicRel_into_range φ g hε hg
  have hS' : f ⁻¹' range (cellInl φ).hom ⊆ g ⁻¹' range (cellInl φ).hom := fun p hp => by
    change g p ∈ range (cellInl φ)
    rw [← F.fst_eq_snd (hS hp)]
    exact hp
  exact ⟨g', hg', ⟨(homotopyRelMono F hS).trans (homotopyRelMono G hS')⟩⟩

/-- Compressions are transported by homeomorphisms of the target. -/
theorem Compresses.comp_homeomorph {Y' X X' P : Type*} [TopologicalSpace Y'] [TopologicalSpace X]
    [TopologicalSpace X'] [TopologicalSpace P] {j : C(Y', X)} (h : Compresses j P) (e : X ≃ₜ X') :
    Compresses ((e : C(X, X')).comp j) P := by
  intro f
  obtain ⟨g, hg, ⟨F⟩⟩ := h ((e.symm : C(X', X)).comp f)
  refine ⟨(e : C(X, X')).comp g, fun p => ?_, ⟨?_⟩⟩
  · obtain ⟨y, hy⟩ := hg p
    exact ⟨y, by simp [hy]⟩
  · have hS : f ⁻¹' range ((e : C(X, X')).comp j) ⊆
        ((e.symm : C(X', X)).comp f) ⁻¹' range j := by
      rintro p ⟨y, hy⟩
      exact ⟨y, by simp [← hy]⟩
    exact ((homotopyRelMono F hS).compContinuousMap (e : C(X, X'))).cast
      (ContinuousMap.ext fun p => by simp) rfl

/-- **The push-off for any pushout square of the shape of an attached cell**: if `j : A → Q` and
`χ : D^n → Q` make a pushout square with `S^{n-1} → A` and `S^{n-1} → D^n`, then `j` compresses
maps from any compact `P` embedded in a real vector space of dimension `< n`. -/
theorem compresses_of_isPushout {A Q : TopCat.{u}} {ψ : ∂𝔻 n ⟶ A} {j : A ⟶ Q} {χ : 𝔻 n ⟶ Q}
    (hpo : IsPushout ψ (diskBoundaryInclusion n) j χ) {P : Type*} [TopologicalSpace P]
    [CompactSpace P] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hV : finrank ℝ V < n) {ι : P → V} (hι : Continuous ι) (hinj : Function.Injective ι) :
    Compresses j.hom P := by
  have heq : j.hom = ((homeoOfIso hpo.isoPushout.symm : _ ≃ₜ _) : C(_, _)).comp (cellInl ψ).hom :=
    ContinuousMap.ext fun a => (ConcreteCategory.congr_hom hpo.inl_isoPushout_inv a).symm
  rw [heq]
  exact (compresses_cellInl ψ hV hι hinj).comp_homeomorph _

/-- **The push-off for an embedded cell**: let `M` be Hausdorff, `A ⊆ M` closed, and
`χ : ℝⁿ → M` continuous and injective on the closed unit ball, with `χ(z) ∈ A` exactly for
`‖z‖ = 1`. Then every map from a compact `P` embedded in a real vector space of dimension `< n`
into `A ∪ χ(Dⁿ)` is homotopic, relative to the preimage of `A`, to a map into `A`. -/
theorem compresses_union_cell {M : Type u} [TopologicalSpace M] [T2Space M] {A : Set M}
    {χ : EuclideanSpace ℝ (Fin n) → M} (hA : IsClosed A) (hcont : ContinuousOn χ (closedBall 0 1))
    (hinj : InjOn χ (closedBall 0 1))
    (hbdry : ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, χ z ∈ A ↔ ‖z‖ = 1)
    {P : Type*} [TopologicalSpace P] [CompactSpace P] {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (hV : finrank ℝ V < n) {ι : P → V}
    (hι : Continuous ι) (hιinj : Function.Injective ι) :
    Compresses (⟨inclusion subset_union_left, continuous_inclusion subset_union_left⟩ :
      C(A, ↥(A ∪ χ '' closedBall 0 1))) P := by
  obtain ⟨ψ, χ', -, -, hpo⟩ := Morse.exists_isPushout_union_cell_of_t2 hA hcont hinj hbdry
  exact compresses_of_isPushout hpo hV hι hιinj

/-! ### Homotopy groups -/

section HomotopyGroups

variable {N : Type*} [Fintype N]

/-- The cube `I^N` as a subset of `ℝ^N`. -/
def cubeEmb (y : I^N) : N → ℝ :=
  fun j => (y j : ℝ)

omit [Fintype N] in
theorem continuous_cubeEmb : Continuous (cubeEmb (N := N)) :=
  continuous_pi fun j => continuous_subtype_val.comp (continuous_apply j)

omit [Fintype N] in
theorem injective_cubeEmb : Function.Injective (cubeEmb (N := N)) := fun _ _ h =>
  funext fun j => Subtype.ext (congrFun h j)

/-- The cylinder `I × I^N` as a subset of `ℝ × ℝ^N`. -/
def cylEmb (q : I × (I^N)) : ℝ × (N → ℝ) :=
  ((q.1 : ℝ), cubeEmb q.2)

omit [Fintype N] in
theorem continuous_cylEmb : Continuous (cylEmb (N := N)) :=
  (continuous_subtype_val.comp continuous_fst).prodMk (continuous_cubeEmb.comp continuous_snd)

omit [Fintype N] in
theorem injective_cylEmb : Function.Injective (cylEmb (N := N)) := fun q q' h =>
  Prod.ext (Subtype.ext (show (q.1 : ℝ) = q'.1 from congrArg Prod.fst h))
    (injective_cubeEmb (congrArg Prod.snd h))

theorem compresses_cellInl_cube (hN : Fintype.card N < n) : Compresses (cellInl φ).hom (I^N) :=
  compresses_cellInl φ (V := N → ℝ) (by rwa [Module.finrank_fintype_fun_eq_card])
    continuous_cubeEmb injective_cubeEmb

theorem compresses_cellInl_cyl (hN : Fintype.card N + 1 < n) :
    Compresses (cellInl φ).hom (I × (I^N)) :=
  compresses_cellInl φ (V := ℝ × (N → ℝ))
    (by rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card]; omega)
    continuous_cylEmb injective_cylEmb

/-- **Attaching an `n`-cell is onto on `π_i` for `i < n`**: the inclusion `Y → Y ∪_φ e^n`
induces a surjection `π_N(Y, y) → π_N(Y ∪_φ e^n, y)` when `|N| < n`. -/
theorem surjective_homotopyGroupMap_cellInl (hN : Fintype.card N < n) (y : Y) :
    Surjective (homotopyGroupMap (N := N) (cellInl φ).hom y) :=
  surjective_homotopyGroupMap_of_compresses (isClosedEmbedding_cellInl φ).isEmbedding
    (compresses_cellInl_cube φ hN) y

/-- **Attaching an `n`-cell is one-to-one on `π_i` for `i < n - 1`.** -/
theorem injective_homotopyGroupMap_cellInl (hN : Fintype.card N + 1 < n) (y : Y) :
    Function.Injective (homotopyGroupMap (N := N) (cellInl φ).hom y) :=
  injective_homotopyGroupMap_of_compresses (isClosedEmbedding_cellInl φ).isEmbedding
    (compresses_cellInl_cyl φ hN) y

/-- **Attaching an `n`-cell does not change `π_i` for `i ≤ n - 2`**: the inclusion
`Y → Y ∪_φ e^n` induces a bijection `π_N(Y, y) → π_N(Y ∪_φ e^n, y)` when `|N| + 2 ≤ n`, for any
basepoint `y ∈ Y`. -/
theorem bijective_homotopyGroupMap_cellInl (hN : Fintype.card N + 2 ≤ n) (y : Y) :
    Bijective (homotopyGroupMap (N := N) (cellInl φ).hom y) :=
  ⟨injective_homotopyGroupMap_cellInl φ (by omega) y,
    surjective_homotopyGroupMap_cellInl φ (by omega) y⟩

/-- **Finitely many cells of dimension `≥ λ`, attached one at a time, do not change `π_i` for
`i ≤ λ - 2`**: if `K` is obtained from `L` by attaching cells of dimensions `cells`
(`Morse.IsRelCellAttachment`), all `≥ |N| + 2`, the inclusion induces bijections on `π_N`. -/
theorem bijective_homotopyGroupMap_of_isRelCellAttachment {L K : TopCat.{u}} {j : L ⟶ K}
    {cells : List ℕ} (h : IsRelCellAttachment L K j cells)
    (hcells : ∀ c ∈ cells, Fintype.card N + 2 ≤ c) (x : L) :
    Bijective (homotopyGroupMap (N := N) j.hom x) := by
  induction h with
  | refl =>
    rw [TopCat.hom_id, homotopyGroupMap_id]
    exact bijective_id
  | @attach K₁ j₁ c₁ h m ψ ih =>
    rw [TopCat.hom_comp, homotopyGroupMap_comp]
    exact (bijective_homotopyGroupMap_cellInl ψ (hcells m (by simp)) _).comp
      (ih fun c hc => hcells c (by simp [hc]))

/-- **Finitely many cells of dimension `≥ λ` are onto on `π_i` for `i ≤ λ - 1`.** -/
theorem surjective_homotopyGroupMap_of_isRelCellAttachment {L K : TopCat.{u}} {j : L ⟶ K}
    {cells : List ℕ} (h : IsRelCellAttachment L K j cells)
    (hcells : ∀ c ∈ cells, Fintype.card N < c) (x : L) :
    Surjective (homotopyGroupMap (N := N) j.hom x) := by
  induction h with
  | refl =>
    rw [TopCat.hom_id, homotopyGroupMap_id]
    exact surjective_id
  | @attach K₁ j₁ c₁ h m ψ ih =>
    rw [TopCat.hom_comp, homotopyGroupMap_comp]
    exact (surjective_homotopyGroupMap_cellInl ψ (hcells m (by simp)) _).comp
      (ih fun c hc => hcells c (by simp [hc]))

/-! ### Other pushout squares, and embedded cells -/

omit [Fintype N] in
/-- A homeomorphism induces bijections on homotopy groups. -/
theorem bijective_homotopyGroupMap_homeomorph [Finite N] {X Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Z] (e : X ≃ₜ Z) (x : X) :
    Bijective (homotopyGroupMap (N := N) (e : C(X, Z)) x) :=
  bijective_homotopyGroupMap_of_homotopyEquiv e.toHomotopyEquiv x

/-- **Any pushout square of the shape of an attached cell**: if `j : A → P` and `χ : D^n → P`
make `S^{n-1} → A`, `S^{n-1} → D^n` a pushout square in `TopCat`, then `j` induces bijections on
`π_N` for `|N| + 2 ≤ n` (and surjections for `|N| < n`,
`Morse.Homotopy.surjective_homotopyGroupMap_of_isPushout`). -/
theorem bijective_homotopyGroupMap_of_isPushout {A P : TopCat.{u}} {ψ : ∂𝔻 n ⟶ A} {j : A ⟶ P}
    {χ : 𝔻 n ⟶ P} (hpo : IsPushout ψ (diskBoundaryInclusion n) j χ)
    (hN : Fintype.card N + 2 ≤ n) (a : A) : Bijective (homotopyGroupMap (N := N) j.hom a) := by
  have heq : (cellInl ψ).hom = (hpo.isoPushout.hom).hom.comp j.hom := by
    rw [← TopCat.hom_comp, hpo.inl_isoPushout_hom]
  have h := bijective_homotopyGroupMap_cellInl ψ hN a (N := N)
  rw [heq, homotopyGroupMap_comp] at h
  exact (EquivLike.comp_bijective _ (Equiv.ofBijective _
    (bijective_homotopyGroupMap_homeomorph (N := N) (homeoOfIso hpo.isoPushout) (j a)))).1 h

theorem surjective_homotopyGroupMap_of_isPushout {A P : TopCat.{u}} {ψ : ∂𝔻 n ⟶ A} {j : A ⟶ P}
    {χ : 𝔻 n ⟶ P} (hpo : IsPushout ψ (diskBoundaryInclusion n) j χ)
    (hN : Fintype.card N < n) (a : A) : Surjective (homotopyGroupMap (N := N) j.hom a) := by
  have heq : (cellInl ψ).hom = (hpo.isoPushout.hom).hom.comp j.hom := by
    rw [← TopCat.hom_comp, hpo.inl_isoPushout_hom]
  have h := surjective_homotopyGroupMap_cellInl ψ hN a (N := N)
  rw [heq, homotopyGroupMap_comp] at h
  exact (EquivLike.comp_surjective _ (Equiv.ofBijective _
    (bijective_homotopyGroupMap_homeomorph (N := N) (homeoOfIso hpo.isoPushout) (j a)))).1 h

variable {M : Type u} [TopologicalSpace M] [T2Space M] {A : Set M}
  {χ : EuclideanSpace ℝ (Fin n) → M}

/-- **An embedded cell** (the form of Milnor's Theorem 3.2 and Remark 3.3): let `M` be Hausdorff,
`A ⊆ M` closed, and `χ : ℝⁿ → M` continuous and injective on the closed unit ball `Dⁿ`, with
`χ(z) ∈ A` exactly for `‖z‖ = 1`. Then the inclusion `A → A ∪ χ(Dⁿ)` induces bijections on `π_N`
for `|N| ≤ n - 2`, at every basepoint. -/
theorem bijective_homotopyGroupMap_union_cell (hA : IsClosed A)
    (hcont : ContinuousOn χ (closedBall 0 1)) (hinj : InjOn χ (closedBall 0 1))
    (hbdry : ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, χ z ∈ A ↔ ‖z‖ = 1)
    (hN : Fintype.card N + 2 ≤ n) (a : A) :
    Bijective (homotopyGroupMap (N := N)
      (⟨inclusion subset_union_left, continuous_inclusion subset_union_left⟩ :
        C(A, ↥(A ∪ χ '' closedBall 0 1))) a) := by
  obtain ⟨ψ, χ', -, -, hpo⟩ := Morse.exists_isPushout_union_cell_of_t2 hA hcont hinj hbdry
  exact bijective_homotopyGroupMap_of_isPushout hpo hN a

/-- An embedded cell is onto on `π_N` for `|N| ≤ n - 1`. -/
theorem surjective_homotopyGroupMap_union_cell (hA : IsClosed A)
    (hcont : ContinuousOn χ (closedBall 0 1)) (hinj : InjOn χ (closedBall 0 1))
    (hbdry : ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, χ z ∈ A ↔ ‖z‖ = 1)
    (hN : Fintype.card N < n) (a : A) :
    Surjective (homotopyGroupMap (N := N)
      (⟨inclusion subset_union_left, continuous_inclusion subset_union_left⟩ :
        C(A, ↥(A ∪ χ '' closedBall 0 1))) a) := by
  obtain ⟨ψ, χ', -, -, hpo⟩ := Morse.exists_isPushout_union_cell_of_t2 hA hcont hinj hbdry
  exact surjective_homotopyGroupMap_of_isPushout hpo hN a

end HomotopyGroups

end Morse.Homotopy
