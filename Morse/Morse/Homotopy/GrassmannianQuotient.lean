import Morse.Homotopy.Grassmannian
import Morse.Chapter12.SUMinimal

/-!
Milnor, *Morse Theory*, §23, p. 129 ("the complex Grassmann manifold `G_m(ℂ^{2m})`"), and Lemma
23.1 (p. 127); Exposition/Chapter14.md, §2.

# The Grassmannian of projections is the Grassmannian of subspaces

## Milnor's text, paraphrased

(p. 127) "The space of minimal geodesics from `I` to `−I` in `SU(2m)` is homeomorphic to the
complex Grassmann manifold `G_m(ℂ^{2m})`", the space of `m`-dimensional subspaces of `ℂ^{2m}`;
(p. 129) "`G_m(ℂ^{2m})` can be identified with the coset space `U(2m)/U(m) × U(m)`".  The
topology of the space of subspaces is not specified; the standard one (Steenrod, §7) is the
quotient topology from the Stiefel manifold of orthonormal frames, `F ↦ span F`.

## What is formalized

The project's model of the Grassmannian is the space of Hermitian projections of trace `m`
(`Morse.Homotopy.Grassmannian 𝕜 ι m`, and `Morse.grassmannian ι m` for `𝕜 = ℂ`).  Here:

* `Morse.Homotopy.isCompact_stiefel`: the Stiefel manifold `V_κ(𝕜^ι)` is compact (closed, with
  entries of norm `≤ 1`).
* `Morse.Homotopy.frameSpan_eq_iff`: **the fibres of `F ↦ F Fᴴ` are the `U(m)`-orbits**:
  `F Fᴴ = F' F'ᴴ` iff `F' = F S` for some `S ∈ U(m)` (namely `S = Fᴴ F'`).
* `Morse.Homotopy.isQuotientMap_frameSpan`: **`F ↦ F Fᴴ` is a quotient map** (continuous, onto,
  from a compact space to a Hausdorff one).
* **`Morse.Homotopy.stiefelQuotientHomeomorph`**: `V_m(𝕜^ι)/U(m) ≃ₜ G_m(𝕜^ι)`, the quotient by
  the right action `F ↦ F S` (`Morse.Homotopy.frameSetoid`), and
  `Morse.stiefelQuotientHomeomorph'` for `Morse.grassmannian ι m`.
* `Morse.Homotopy.fixSubmodule_colMatrix`, `Morse.Homotopy.grassmannianEquivSubmodule_frameSpan`:
  the range of `F Fᴴ` is the span of the columns of `F`.
* **`Morse.Homotopy.grassmannianEquivSubmodule`**: `G_m(𝕜^ι) ≃ {W ≤ EuclideanSpace 𝕜 ι //
  dim W = m}`, `P ↦ range P`; `Morse.Homotopy.grassmannianEquivSubmodule'`: the same with
  subspaces of `ι → 𝕜`, where `range P = {x | P x = x}`
  (`Morse.Homotopy.mem_grassmannianEquivSubmodule'`); `Morse.grassmannianSubmoduleEquiv` for
  `Morse.grassmannian ι m` and `ι → ℂ`.

So the Grassmannian of projections, with the subspace topology of the matrices, is homeomorphic
to the space of `m`-dimensional subspaces with the quotient topology from the Stiefel manifold,
by `P ↦ range P`.
-/

open Matrix Set Function Topology Module

noncomputable section

namespace Morse.Homotopy

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Compactness of the Stiefel manifold -/

section Compact

variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]

omit [Fintype ι] in
theorem norm_entry_le_one_of_mem_stiefel [Fintype ι] {F : Matrix ι κ 𝕜}
    (hF : F ∈ Stiefel 𝕜 ι κ) (i : ι) (j : κ) : ‖F i j‖ ≤ 1 := by
  have h := (orthonormal_cols hF).1 j
  calc ‖F i j‖ = ‖(WithLp.toLp 2 (fun i => F i j) : EuclideanSpace 𝕜 ι) i‖ := rfl
    _ ≤ ‖(WithLp.toLp 2 (fun i => F i j) : EuclideanSpace 𝕜 ι)‖ := PiLp.norm_apply_le _ i
    _ = 1 := h

/-- **The Stiefel manifold is compact.** -/
theorem isCompact_stiefel : IsCompact (Stiefel 𝕜 ι κ) := by
  have hK : IsCompact (Set.pi univ fun _ : ι => Set.pi univ fun _ : κ =>
      Metric.closedBall (0 : 𝕜) 1 : Set (Matrix ι κ 𝕜)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hK.of_isClosed_subset ?_ fun F hF => ?_
  · exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)
      continuous_const
  · simp only [Set.mem_pi, mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    exact fun i j => norm_entry_le_one_of_mem_stiefel hF i j

instance : CompactSpace (Stiefel 𝕜 ι κ) :=
  isCompact_iff_compactSpace.1 isCompact_stiefel

end Compact

/-! ### The frame-to-span map as a quotient map -/

section Quotient

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

omit [DecidableEq ι] in
/-- **The fibres of the frame-to-span map are the `U(m)`-orbits**: `F Fᴴ = F' F'ᴴ` iff
`F' = F S` with `S ∈ U(m)` (`S = Fᴴ F'`). -/
theorem frameSpan_eq_iff {F F' : Stiefel 𝕜 ι (Fin m)} :
    frameSpan 𝕜 ι m F = frameSpan 𝕜 ι m F' ↔
      ∃ S : unitaryGroup (Fin m) 𝕜, F'.1 = F.1 * (S : Matrix (Fin m) (Fin m) 𝕜) := by
  have hF := mem_stiefel.1 F.2
  have hF' := mem_stiefel.1 F'.2
  constructor
  · intro h
    have hP : F.1 * F.1ᴴ = F'.1 * F'.1ᴴ := congrArg Subtype.val h
    refine ⟨⟨F.1ᴴ * F'.1, ?_⟩, ?_⟩
    · rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_mul,
        conjTranspose_conjTranspose]
      calc F'.1ᴴ * F.1 * (F.1ᴴ * F'.1) = F'.1ᴴ * (F.1 * F.1ᴴ) * F'.1 := by
            simp only [Matrix.mul_assoc]
        _ = F'.1ᴴ * (F'.1 * F'.1ᴴ) * F'.1 := by rw [hP]
        _ = (F'.1ᴴ * F'.1) * (F'.1ᴴ * F'.1) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hF', Matrix.one_mul]
    · change F'.1 = F.1 * (F.1ᴴ * F'.1)
      rw [← Matrix.mul_assoc, hP, Matrix.mul_assoc, hF', Matrix.mul_one]
  · rintro ⟨S, hS⟩
    apply Subtype.ext
    change F.1 * F.1ᴴ = F'.1 * F'.1ᴴ
    have hS' : (S : Matrix (Fin m) (Fin m) 𝕜) * (S : Matrix (Fin m) (Fin m) 𝕜)ᴴ = 1 := by
      rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.1 S.2
    rw [hS, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc S.1, hS', Matrix.one_mul]

omit [DecidableEq ι] in
theorem surjective_frameSpan : Surjective (frameSpan 𝕜 ι m) := fun P => by
  obtain ⟨F, hF, hFP⟩ := exists_frame_of_mem_grassmannian P.2
  exact ⟨⟨F, hF⟩, Subtype.ext hFP⟩

omit [DecidableEq ι] in
/-- **`F ↦ F Fᴴ` is a quotient map** `V_m(𝕜^ι) → G_m(𝕜^ι)`. -/
theorem isQuotientMap_frameSpan : IsQuotientMap (frameSpan 𝕜 ι m) :=
  IsQuotientMap.of_surjective_continuous surjective_frameSpan continuous_frameSpan

variable (𝕜 ι m) in
/-- The orbit relation of the right action of `U(m)` on `m`-frames, `F ∼ F S`. -/
def frameSetoid : Setoid (Stiefel 𝕜 ι (Fin m)) where
  r F F' := ∃ S : unitaryGroup (Fin m) 𝕜, F'.1 = F.1 * (S : Matrix (Fin m) (Fin m) 𝕜)
  iseqv :=
    { refl := fun _ => frameSpan_eq_iff.1 rfl
      symm := fun h => frameSpan_eq_iff.1 (frameSpan_eq_iff.2 h).symm
      trans := fun h h' => frameSpan_eq_iff.1 ((frameSpan_eq_iff.2 h).trans
        (frameSpan_eq_iff.2 h')) }

omit [DecidableEq ι] in
theorem frameSetoid_eq_ker : frameSetoid 𝕜 ι m = Setoid.ker (frameSpan 𝕜 ι m) :=
  Setoid.ext fun _ _ => frameSpan_eq_iff.symm

variable (𝕜 ι m) in
/-- **`V_m(𝕜^ι)/U(m) ≃ₜ G_m(𝕜^ι)`**: the Grassmannian of Hermitian projections of trace `m` is
the quotient of the Stiefel manifold of orthonormal `m`-frames by `U(m)`, via `[F] ↦ F Fᴴ`. -/
def stiefelQuotientHomeomorph : Quotient (frameSetoid 𝕜 ι m) ≃ₜ Grassmannian 𝕜 ι m :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (Quotient.lift (frameSpan 𝕜 ι m) fun _ _ h => frameSpan_eq_iff.2 h)
      ⟨fun x y => Quotient.inductionOn₂ x y fun _ _ h => Quotient.sound (frameSpan_eq_iff.1 h),
        fun P => let ⟨F, h⟩ := surjective_frameSpan P; ⟨Quotient.mk _ F, h⟩⟩)
    (continuous_quot_lift _ continuous_frameSpan)

omit [DecidableEq ι] in
theorem stiefelQuotientHomeomorph_mk (F : Stiefel 𝕜 ι (Fin m)) :
    stiefelQuotientHomeomorph 𝕜 ι m (Quotient.mk _ F) = frameSpan 𝕜 ι m F :=
  rfl

end Quotient

/-! ### Projections and subspaces -/

section Subspaces

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

omit [DecidableEq ι] in
/-- The vectors fixed by `F Fᴴ` are the span of the columns of `F`. -/
theorem fixSubmodule_colMatrix {κ : Type*} [Fintype κ]
    {v : κ → EuclideanSpace 𝕜 ι} (hv : Orthonormal 𝕜 v) :
    fixSubmodule 𝕜 (colMatrix v * (colMatrix v)ᴴ) = Submodule.span 𝕜 (range v) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [mem_fixSubmodule, ← mulVec_mulVec, conjTranspose_colMatrix_mulVec,
      colMatrix_mulVec] at hx
    rw [← WithLp.ofLp_injective 2 hx]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, mem_fixSubmodule, ← mulVec_mulVec, conjTranspose_colMatrix_mulVec,
      colMatrix_mulVec]
    rw [orthonormal_iff_ite] at hv
    simp [hv]

omit [DecidableEq ι] in
theorem finrank_fixSubmodule {P : Matrix ι ι 𝕜} (hP : P ∈ Grassmannian 𝕜 ι m) :
    finrank 𝕜 (fixSubmodule 𝕜 P) = m := by
  obtain ⟨F, hF, rfl⟩ := exists_frame_of_mem_grassmannian hP
  have hv := orthonormal_cols hF
  have hc : colMatrix (fun k => WithLp.toLp 2 (fun i => F i k)) = F := by ext; rfl
  rw [← hc, fixSubmodule_colMatrix hv, finrank_span_eq_card hv.linearIndependent,
    Fintype.card_fin]

omit [DecidableEq ι] in
/-- **A Hermitian projection of trace `m` is determined by its range.** -/
theorem eq_of_fixSubmodule_eq {P Q : Matrix ι ι 𝕜} (hP : P ∈ Grassmannian 𝕜 ι m)
    (hQ : Q ∈ Grassmannian 𝕜 ι m) (h : fixSubmodule 𝕜 P = fixSubmodule 𝕜 Q) : P = Q := by
  obtain ⟨hP1, hP2, hP3⟩ := hP
  obtain ⟨hQ1, hQ2, hQ3⟩ := hQ
  refine eq_of_mul_eq_of_trace_eq hP1 hP2 hQ1 hQ2 ?_ (by rw [hP3, hQ3])
  ext i j
  have hcol : (WithLp.toLp 2 (fun l => Q l j) : EuclideanSpace 𝕜 ι) ∈ fixSubmodule 𝕜 Q := by
    change Q *ᵥ (fun l => Q l j) = fun l => Q l j
    ext l
    have := congrFun (congrFun hQ2 l) j
    simpa [mulVec, dotProduct, mul_apply] using this
  rw [← h] at hcol
  have := congrFun hcol i
  simpa [mulVec, dotProduct, mul_apply] using this

omit [DecidableEq ι] in
/-- **Every `m`-dimensional subspace is the range of a projection of trace `m`**: the projection
`F Fᴴ` onto the span of an orthonormal basis. -/
theorem exists_fixSubmodule_eq (W : Submodule 𝕜 (EuclideanSpace 𝕜 ι)) (hW : finrank 𝕜 W = m) :
    ∃ P ∈ Grassmannian 𝕜 ι m, fixSubmodule 𝕜 P = W := by
  let b := (stdOrthonormalBasis 𝕜 W).reindex (finCongr hW)
  let v : Fin m → EuclideanSpace 𝕜 ι := W.subtype ∘ b
  have hv : Orthonormal 𝕜 v := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  refine ⟨_, mul_conjTranspose_mem_grassmannian (colMatrix_mem_stiefel hv), ?_⟩
  rw [fixSubmodule_colMatrix hv, Set.range_comp, Submodule.span_image, ← b.coe_toBasis,
    b.toBasis.span_eq, Submodule.map_top, Submodule.range_subtype]

variable (𝕜 ι m) in
/-- **`G_m(𝕜^ι)` is the set of `m`-dimensional subspaces**, `P ↦ range P`. -/
def grassmannianEquivSubmodule :
    Grassmannian 𝕜 ι m ≃ {W : Submodule 𝕜 (EuclideanSpace 𝕜 ι) // finrank 𝕜 W = m} :=
  Equiv.ofBijective (fun P => ⟨fixSubmodule 𝕜 P, finrank_fixSubmodule P.2⟩)
    ⟨fun P Q h => Subtype.ext (eq_of_fixSubmodule_eq P.2 Q.2 (congrArg Subtype.val h)),
      fun W => by
        obtain ⟨P, hP, hPW⟩ := exists_fixSubmodule_eq W.1 W.2
        exact ⟨⟨P, hP⟩, Subtype.ext hPW⟩⟩

omit [DecidableEq ι] in
theorem coe_grassmannianEquivSubmodule (P : Grassmannian 𝕜 ι m) :
    (grassmannianEquivSubmodule 𝕜 ι m P : Submodule 𝕜 (EuclideanSpace 𝕜 ι)) =
      fixSubmodule 𝕜 P :=
  rfl

omit [DecidableEq ι] in
/-- **The composite `V_m(𝕜^ι) → G_m(𝕜^ι) → {subspaces}` is `F ↦ span F`**: so the quotient
topology of `Morse.Homotopy.stiefelQuotientHomeomorph` is the quotient topology of the span map. -/
theorem grassmannianEquivSubmodule_frameSpan (F : Stiefel 𝕜 ι (Fin m)) :
    (grassmannianEquivSubmodule 𝕜 ι m (frameSpan 𝕜 ι m F) :
        Submodule 𝕜 (EuclideanSpace 𝕜 ι)) =
      Submodule.span 𝕜 (range fun k => WithLp.toLp 2 (fun i => F.1 i k)) := by
  have hc : colMatrix (fun k => WithLp.toLp 2 (fun i => F.1 i k)) = F.1 := by ext; rfl
  rw [coe_grassmannianEquivSubmodule, ← fixSubmodule_colMatrix (orthonormal_cols F.2)]
  change fixSubmodule 𝕜 (F.1 * F.1ᴴ) = _
  rw [hc]

variable (𝕜 ι) in
/-- `EuclideanSpace 𝕜 ι ≃ₗ ι → 𝕜`. -/
abbrev euclidLinearEquiv : EuclideanSpace 𝕜 ι ≃ₗ[𝕜] (ι → 𝕜) :=
  (EuclideanSpace.equiv ι 𝕜).toLinearEquiv

variable (𝕜 ι m) in
/-- **`G_m(𝕜^ι)` is the set of `m`-dimensional subspaces of `ι → 𝕜`**, `P ↦ {x | P x = x}`. -/
def grassmannianEquivSubmodule' :
    Grassmannian 𝕜 ι m ≃ {W : Submodule 𝕜 (ι → 𝕜) // finrank 𝕜 W = m} :=
  (grassmannianEquivSubmodule 𝕜 ι m).trans
    { toFun := fun W => ⟨W.1.map (euclidLinearEquiv 𝕜 ι : EuclideanSpace 𝕜 ι →ₗ[𝕜] ι → 𝕜), by
        rw [LinearEquiv.finrank_map_eq]; exact W.2⟩
      invFun := fun W => ⟨W.1.map ((euclidLinearEquiv 𝕜 ι).symm : (ι → 𝕜) →ₗ[𝕜] EuclideanSpace 𝕜 ι),
        by rw [LinearEquiv.finrank_map_eq]; exact W.2⟩
      left_inv := fun W => Subtype.ext ((Submodule.map_symm_eq_iff _).2 rfl)
      right_inv := fun W => Subtype.ext (Submodule.ext fun x => by
        simp only [Submodule.mem_map_equiv, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]) }

omit [DecidableEq ι] in
theorem mem_grassmannianEquivSubmodule' (P : Grassmannian 𝕜 ι m) (x : ι → 𝕜) :
    x ∈ (grassmannianEquivSubmodule' 𝕜 ι m P : Submodule 𝕜 (ι → 𝕜)) ↔
      (P : Matrix ι ι 𝕜) *ᵥ x = x := by
  change x ∈ (fixSubmodule 𝕜 (P : Matrix ι ι 𝕜)).map
    (euclidLinearEquiv 𝕜 ι : EuclideanSpace 𝕜 ι →ₗ[𝕜] ι → 𝕜) ↔ _
  rw [Submodule.mem_map_equiv]
  rfl

end Subspaces

end Morse.Homotopy

namespace Morse

open Morse.Homotopy

variable (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ)

theorem grassmannian_eq : grassmannian ι m = Grassmannian ℂ ι m :=
  rfl

/-- **Milnor's `G_m(ℂ^ι)` is the quotient `V_m(ℂ^ι)/U(m)`** of the Stiefel manifold. -/
def stiefelQuotientHomeomorph' : Quotient (frameSetoid ℂ ι m) ≃ₜ grassmannian ι m :=
  stiefelQuotientHomeomorph ℂ ι m

/-- **Milnor's `G_m(ℂ^ι)` is the set of `m`-dimensional subspaces of `ℂ^ι`**,
`P ↦ {x | P x = x}` (`Morse.Homotopy.mem_grassmannianEquivSubmodule'`). -/
def grassmannianSubmoduleEquiv :
    grassmannian ι m ≃ {W : Submodule ℂ (ι → ℂ) // finrank ℂ W = m} :=
  grassmannianEquivSubmodule' ℂ ι m

end Morse
