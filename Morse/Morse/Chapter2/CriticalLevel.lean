import Morse.Chapter2.CellAttach

/-!
Milnor, *Morse Theory*, §3, p. 20: Remark 3.4 and Diagram 8.

# The critical level `M^c` itself

**Remark 3.4** (p. 20), paraphrased: a simple modification of the proof of Theorem 3.2 shows that
`M^c` is also a deformation retract of `M^{c+ε}`: `M^c` is a deformation retract of
`F⁻¹(-∞, c]`, which is a deformation retract of `M^{c+ε}`. Combining this with Theorem 3.2,
`M^{c-ε} ∪ e^λ` is a deformation retract of `M^c`. (The book prints "Remark 2.4".)

This file proves both statements for `M = E` a finite-dimensional real inner product space, with
the function `F`, the chart and the cell of `Morse/Chapter2/CellAttach.lean`.

## What Milnor's text leaves implicit

Neither half is written out in the book (Diagram 8 only shows the picture).

* **`F⁻¹(-∞, c]` is a strong deformation retract of `M^{c+ε}`**: Theorem 3.1 for `F` on the slab
  `F⁻¹[c, c+ε]`, a closed subset of the compact, critical-point-free `F⁻¹[c-ε, c+ε]` used in
  Assertion 3 (`Morse.isStrongDeformationRetract_milnorF_level`).
* **The "simple modification"** is Milnor's deformation of Assertion 4 with `ε` replaced by `0`:
  `(x, y) ↦ (x, s y)` with `s = 1 - t + t (ξ/η)^{1/2}` where `ξ ≤ η`, the identity where
  `η ≤ ξ`, that is on `M^c` (`CellModel.isStrongDeformationRetract_model_level` in Morse
  coordinates). On `F⁻¹(-∞, c]` it moves only points of the ellipsoid `ξ + 2η ≤ 2ε` (outside it
  `F = f ≤ c`, i.e. `η ≤ ξ`), so it is again the identity outside the chart; `r_1` maps
  everything into `f⁻¹(-∞, c]`, since the points with `ξ ≤ η` go to `η = ξ`, i.e. to `f = c`
  (`Morse.isStrongDeformationRetract_level`).
* **"We see easily that `M^{c-ε} ∪ e^λ` is a deformation retract of `M^c`"** needs a lemma that
  Milnor does not state (Lemma A(ii) of the exposition): if `A ⊆ B ⊆ C`, `A` is a strong
  deformation retract of `C` and `B` is a retract of `C`, then `A` is a strong deformation
  retract of `B`, by composing the deformation of `C` with the retraction onto `B`
  (`Morse.IsStrongDeformationRetract.of_retract`). Here `A = M^{c-ε} ∪ e^λ` (Theorem 3.2),
  `B = M^c` (first half), `C = M^{c+ε}`; `e^λ ⊆ M^c` because `f = c - ξ` on the cell.

## Main results

* `Morse.IsStrongDeformationRetract.of_retract`: Lemma A(ii).
* `Morse.isStrongDeformationRetract_sublevel_crit`: `M^c` is a strong deformation retract of
  `M^{c+ε}`.
* `Morse.isStrongDeformationRetract_union_cellE_crit`: `M^{c-ε} ∪ e^λ` is a strong deformation
  retract of `M^c`.
* `Morse.remark_3_4`: both, for all sufficiently small `ε`, from the hypotheses of Theorem 3.2.
-/

open Set Filter Topology Function Module
open scoped ContDiff unitInterval

noncomputable section

namespace Morse

open CellModel

/-- **Lemma A(ii) of the exposition**: if `A ⊆ B ⊆ C`, `A` is a strong deformation retract of
`C` and `B` is a retract of `C` (here: a strong deformation retract), then `A` is a strong
deformation retract of `B`: follow the deformation of `C` onto `A`, then retract onto `B`. -/
theorem IsStrongDeformationRetract.of_retract {T : Type*} [TopologicalSpace T] {A B C : Set T}
    (hAB : A ⊆ B) (hBC : B ⊆ C) (hA : IsStrongDeformationRetract ((↑) ⁻¹' A : Set C))
    (hB : IsStrongDeformationRetract ((↑) ⁻¹' B : Set C)) :
    IsStrongDeformationRetract ((↑) ⁻¹' A : Set B) := by
  obtain ⟨r, hr, ⟨H⟩⟩ := hA
  obtain ⟨s, hs, ⟨G⟩⟩ := hB
  let κ : C(C, B) := ⟨fun x => ⟨s x, hs x⟩, (s.continuous.subtype_val).subtype_mk _⟩
  let i : C(B, C) := ⟨Set.inclusion hBC, continuous_inclusion hBC⟩
  have hκ : ∀ x : C, (x : T) ∈ B → (κ x : T) = x := fun x hx =>
    congrArg Subtype.val (G.fst_eq_snd (x := x) hx).symm
  have hκi : ∀ b : B, κ (i b) = b := fun b => Subtype.ext (hκ (i b) b.2)
  let K : (ContinuousMap.id B).HomotopyRel (κ.comp (r.comp i)) ((↑) ⁻¹' A) :=
    { toFun := fun z => κ (H (z.1, i z.2))
      continuous_toFun := κ.continuous.comp (H.continuous.comp
        (continuous_fst.prodMk (i.continuous.comp continuous_snd)))
      map_zero_left := fun b => by simp [hκi]
      map_one_left := fun b => by simp
      prop' := fun t b hb => by
        change κ (H (t, i b)) = b
        rw [H.eq_fst t (show ((i b : C) : T) ∈ A from hb)]
        exact hκi b }
  refine ⟨κ.comp (r.comp i), fun b => ?_, ⟨K⟩⟩
  change ((κ (r (i b)) : B) : T) ∈ A
  rw [hκ _ (hAB (hr (i b)))]
  exact hr (i b)

section Level

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  {f : E → ℝ} {p : E} {φ : OpenPartialHomeomorph E (X × Y)} {ε : ℝ} {μ : ℝ → ℝ}
  (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target)
include hball

omit [FiniteDimensional ℝ E] in
/-- **Remark 3.4, the modified deformation**: `M^c` is a strong deformation retract of
`F⁻¹(-∞, c]` (Milnor's `r_t` with `ε` replaced by `0`, Diagram 8). -/
theorem isStrongDeformationRetract_level (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ)
    (hε : 0 < ε) :
    IsStrongDeformationRetract
      ((↑) ⁻¹' sublevel f (f p) : Set (sublevel (milnorF f φ μ) (f p))) := by
  have h : IsStrongDeformationRetract
      ((↑) ⁻¹' sublevel f (f p - 0) : Set (sublevel (milnorF f φ μ) (f p - 0))) := by
    refine ⟨handleRetractOne hball hφ hμ 0, fun q => ?_,
      ⟨handleHomotopy hball hφ hμ 0 _ fun q hq t => handleRetract_of_mem_sublevel hφ hq t⟩⟩
    rcases handleRetract_one_mem hball hφ hμ q.2 with h | ⟨v, hv, hq⟩
    · exact h
    · -- the cell of radius `0` is the point `p`
      have hv' : v ∈ cellModel ε := ⟨hv.1.trans hε.le, hv.2⟩
      have hvt : v ∈ φ.target := ellipsoid_subset_target hball (cellModel_subset_ellipsoid hv')
      change f (handleRetractOne hball hφ hμ 0 q) ≤ f p - 0
      change f (handleRetract φ 0 1 q) ≤ f p - 0
      rw [← hq, hφ.apply_eq _ (φ.map_target hvt), φ.right_inv hvt]
      have h1 : xi v ≤ 0 := hv.1
      have h2 := eta_eq_zero_iff.2 hv.2
      unfold morseQuad
      linarith [xi_nonneg v]
  rwa [sub_zero] at h

/-- **Remark 3.4, first step**: `F⁻¹(-∞, c]` is a strong deformation retract of `M^{c+ε}`
(Theorem 3.1 for `F` on `F⁻¹[c, c+ε]`). -/
theorem isStrongDeformationRetract_milnorF_level (hf : ContDiff ℝ ∞ f)
    (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ) (hε : 0 < ε)
    (hK : IsCompact (f ⁻¹' Icc (f p - ε) (f p + ε)))
    (honly : ∀ q ∈ f ⁻¹' Icc (f p - ε) (f p + ε), IsCriticalPoint f q → q = p) :
    IsStrongDeformationRetract
      ((↑) ⁻¹' sublevel (milnorF f φ μ) (f p) : Set (sublevel f (f p + ε))) := by
  have hF := contDiff_milnorF hball hf hφ hμ
  have hsub : milnorF f φ μ ⁻¹' Icc (f p) (f p + ε) ⊆ f ⁻¹' Icc (f p - ε) (f p + ε) :=
    fun q hq => ⟨by linarith [hq.1, milnorF_le (f := f) (φ := φ) hμ q],
      show q ∈ sublevel f (f p + ε) from sublevel_milnorF_add hφ hμ ▸ hq.2⟩
  have hK' : IsCompact (milnorF f φ μ ⁻¹' Icc (f p) (f p + ε)) :=
    hK.of_isClosed_subset (isClosed_Icc.preimage hF.continuous) hsub
  have hcrit : ∀ q ∈ milnorF f φ μ ⁻¹' Icc (f p) (f p + ε),
      ¬IsCriticalPoint (milnorF f φ μ) q := by
    intro q hq hc
    have hqp := honly q (hsub hq) ((isCriticalPoint_milnorF_iff hball hφ hμ q).1 hc)
    subst hqp
    have := hq.1
    rw [milnorF_apply_self hφ] at this
    linarith [hμ.lt_apply_zero]
  have h := (theorem_3_1 hF (by linarith) hK' hcrit).2.1
  rwa [sublevel_milnorF_add hφ hμ] at h

/-- **Remark 3.4** (p. 20): `M^c` is a strong deformation retract of `M^{c+ε}`. -/
theorem isStrongDeformationRetract_sublevel_crit (hf : ContDiff ℝ ∞ f)
    (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ) (hε : 0 < ε)
    (hK : IsCompact (f ⁻¹' Icc (f p - ε) (f p + ε)))
    (honly : ∀ q ∈ f ⁻¹' Icc (f p - ε) (f p + ε), IsCriticalPoint f q → q = p) :
    IsStrongDeformationRetract ((↑) ⁻¹' sublevel f (f p) : Set (sublevel f (f p + ε))) := by
  have h1 : sublevel f (f p) ⊆ sublevel (milnorF f φ μ) (f p) :=
    fun q hq => (milnorF_le hμ q).trans hq
  have h2 : sublevel (milnorF f φ μ) (f p) ⊆ sublevel f (f p + ε) := by
    rw [← sublevel_milnorF_add hφ hμ]
    exact sublevel_mono _ (by linarith)
  exact IsStrongDeformationRetract.trans h1 h2 (isStrongDeformationRetract_level hball hφ hμ hε)
    (isStrongDeformationRetract_milnorF_level hball hf hφ hμ hε hK honly)

/-- **Remark 3.4** (p. 20): `M^{c-ε} ∪ e^λ` is a strong deformation retract of `M^c`. -/
theorem isStrongDeformationRetract_union_cellE_crit (hf : ContDiff ℝ ∞ f)
    (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ) (hε : 0 < ε)
    (hK : IsCompact (f ⁻¹' Icc (f p - ε) (f p + ε)))
    (honly : ∀ q ∈ f ⁻¹' Icc (f p - ε) (f p + ε), IsCriticalPoint f q → q = p) :
    IsStrongDeformationRetract
      ((↑) ⁻¹' (sublevel f (f p - ε) ∪ cellE φ ε) : Set (sublevel f (f p))) := by
  have hAB : sublevel f (f p - ε) ∪ cellE φ ε ⊆ sublevel f (f p) := by
    refine union_subset (sublevel_mono f (by linarith)) ?_
    rintro _ ⟨v, hv, rfl⟩
    have hvt : v ∈ φ.target := ellipsoid_subset_target hball (cellModel_subset_ellipsoid hv)
    rw [mem_sublevel, hφ.apply_eq _ (φ.map_target hvt), φ.right_inv hvt]
    have h2 := eta_eq_zero_iff.2 hv.2
    unfold morseQuad
    linarith [xi_nonneg v]
  exact IsStrongDeformationRetract.of_retract hAB (sublevel_mono f (by linarith))
    (isStrongDeformationRetract_union_cellE hball hf hφ hμ hε hK honly)
    (isStrongDeformationRetract_sublevel_crit hball hf hφ hμ hε hK honly)

end Level

section Remark34

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Remark 3.4** (Milnor, p. 20), under the hypotheses of Theorem 3.2: for all sufficiently
small `ε > 0`, `M^c` is a strong deformation retract of `M^{c+ε}`, and `M^{c-ε} ∪ e^λ` is a strong
deformation retract of `M^c`, where `e^λ = χ(D^λ)` is a `λ`-cell meeting `M^{c-ε}` exactly in
`χ(S^{λ-1})` (the cell of `Morse.theorem_3_2`). -/
theorem remark_3_4 {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {p : E} (hcrit : IsCriticalPoint f p)
    (hnd : IsNondegenerate (hessian f p)) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hK : IsCompact (f ⁻¹' Icc (f p - ε₀) (f p + ε₀)))
    (honly : ∀ q ∈ f ⁻¹' Icc (f p - ε₀) (f p + ε₀), IsCriticalPoint f q → q = p) :
    ∃ ε₁ > 0, ∀ ε, 0 < ε → ε ≤ ε₁ →
      IsStrongDeformationRetract ((↑) ⁻¹' sublevel f (f p) : Set (sublevel f (f p + ε))) ∧
      ∃ χ : EuclideanSpace ℝ (Fin (index (hessian f p))) → E,
        ContinuousOn χ (Metric.closedBall 0 1) ∧ InjOn χ (Metric.closedBall 0 1) ∧
        (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (index (hessian f p)))) 1,
          χ z ∈ sublevel f (f p - ε) ↔ ‖z‖ = 1) ∧
        IsStrongDeformationRetract
          ((↑) ⁻¹' (sublevel f (f p - ε) ∪ χ '' Metric.closedBall 0 1) :
            Set (sublevel f (f p))) := by
  obtain ⟨φ, hφ, ε₁, hε₁, H⟩ := exists_morseChart_forall_small hf hcrit hnd hε₀ hK honly
  have hk : index (hessian f p) ≤ finrank ℝ E := sigPos_le_finrank _
  refine ⟨ε₁, hε₁, fun ε hε hεε₁ => ?_⟩
  obtain ⟨hball, hKε, honlyε⟩ := H ε hε hεε₁
  have hμ := isMilnorMu_milnorMu hε
  obtain ⟨himage, hcont, hinj, hval⟩ := cellE_parametrization hball hφ hε
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (negIdxEquiv hk))
  refine ⟨isStrongDeformationRetract_sublevel_crit hball hf hφ hμ hε hKε honlyε, _, hcont, hinj,
    fun z hz => ?_, ?_⟩
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
  · rw [himage]
    exact isStrongDeformationRetract_union_cellE_crit hball hf hφ hμ hε hKε honlyε

end Remark34

end Morse
