import Milnor.Chapter7.AdjXR
import Milnor.Chapter7.Reparam

/-!
# Homotopic maps have framed cobordant Pontryagin manifolds (Milnor §7, Lemma 3)

Let `F' : M × ℝ → Sᵖ` be a smooth homotopy which is `f` for `t ≤ ε` and `g` for `t ≥ 1 - ε`,
and let `z` be a regular value of `F'`.  Then `S = F'⁻¹(z) ⊆ M × ℝ` is an `(n+1)`-dimensional
submanifold with product ends `f⁻¹(z) × (-∞, ε)` and `g⁻¹(z) × (1 - ε, ∞)`, and the framing
pulled back from a basis `b` at `z` through the extension `F̃' = c ∘ F' ∘ (r × id)` restricts to
the Pontryagin framings of `f` and `g` at the ends.  So `(F'⁻¹(z), F'^*b)` is a framed
cobordism between the Pontryagin manifolds of `f` and `g`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) (hMc : IsCompact M) (hne : M.Nonempty)
  {p n : ℕ}

section hom

variable {F' : M × ℝ → Sph p}
  (hF' : letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ F')
  {z : Sph p}
  (hz : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) F' z)

/-- The dimension count for the level set in `M × ℝ`. -/
theorem levelDimXR (hnp : n + p = m) :
    finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) + finrank ℝ (EuclideanSpace ℝ (Fin p)) =
      finrank ℝ (EuclideanSpace ℝ (Fin m) × ℝ) := by
  simp only [finrank_euclideanSpace_fin, Module.finrank_prod, Module.finrank_self]
  omega

include hF' hz in
/-- `F'⁻¹(z)` is an `(n+1)`-dimensional submanifold of `M × ℝ`. -/
theorem isSliceSubmanifold_levelXR (hnp : n + p = m) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)) (F' ⁻¹' {z}) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  exact isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin (n + 1))) (levelDimXR hnp) hF' hz

/-- The extension `F̃' (y, t) = c (F' (r y, t))`. -/
def Fh (F' : M × ℝ → Sph p) (z : Sph p) (q : EuclideanSpace ℝ (Fin (K + 1)) × ℝ) :
    EuclideanSpace ℝ (Fin p) :=
  extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z (F' (Tub.tubr hM hMc hne q.1, q.2))

/-- The open set on which `F̃'` is smooth. -/
def Wh (F' : M × ℝ → Sph p) (z : Sph p) : Set (EuclideanSpace ℝ (Fin (K + 1)) × ℝ) :=
  {q | infDist q.1 M < Tub.tubε hM hMc hne ∧
    F' (Tub.tubr hM hMc hne q.1, q.2) ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z).source}

/-- `(y, t) ↦ (r y, t)` is smooth on `N_ε × ℝ`. -/
theorem contMDiff_tubr_prod :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : (⟨Tub.Nε hM hMc hne ×ˢ univ, (Tub.isOpen_Nε hM hMc hne).prod isOpen_univ⟩ :
        TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (K + 1)) × ℝ)) =>
        (Tub.tubr hM hMc hne q.1.1, q.1.2)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (K + 1))) :=
    ⟨Tub.Nε hM hMc hne, Tub.isOpen_Nε hM hMc hne⟩ with hU
  set U' : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (K + 1)) × ℝ) :=
    ⟨Tub.Nε hM hMc hne ×ˢ univ, (Tub.isOpen_Nε hM hMc hne).prod isOpen_univ⟩ with hU'
  -- the projection `U' → U`
  have hpr : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞
      (fun q : U' => (⟨q.1.1, q.2.1⟩ : U)) := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact (contMDiff_iff_contDiff.2 contDiff_fst).comp
      (contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)))
  refine ContMDiff.prodMk ?_ ?_
  · exact (contMDiff_tubr_opens hM hMc hne).comp hpr
  · exact (contMDiff_iff_contDiff.2 contDiff_snd).comp
      (contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)))

include hF' in
theorem isOpen_Wh : IsOpen (Wh hM hMc hne F' z) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set U' : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (K + 1)) × ℝ) :=
    ⟨Tub.Nε hM hMc hne ×ˢ univ, (Tub.isOpen_Nε hM hMc hne).prod isOpen_univ⟩ with hU'
  have hc : ContinuousOn (fun q : EuclideanSpace ℝ (Fin (K + 1)) × ℝ =>
      F' (Tub.tubr hM hMc hne q.1, q.2)) U'.1 := by
    rw [continuousOn_iff_continuous_restrict]
    exact hF'.continuous.comp (contMDiff_tubr_prod hM hMc hne).continuous
  have : Wh hM hMc hne F' z = U'.1 ∩ (fun q : EuclideanSpace ℝ (Fin (K + 1)) × ℝ =>
      F' (Tub.tubr hM hMc hne q.1, q.2)) ⁻¹' (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z).source := by
    ext q
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, mem_univ _⟩, h2⟩
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  rw [this]
  exact hc.isOpen_inter_preimage U'.2 (isOpen_extChartAt_source z)

include hF' in
theorem contDiffOn_Fh : ContDiffOn ℝ ∞ (Fh hM hMc hne F' z) (Wh hM hMc hne F' z) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set U' : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (K + 1)) × ℝ) :=
    ⟨Tub.Nε hM hMc hne ×ˢ univ, (Tub.isOpen_Nε hM hMc hne).prod isOpen_univ⟩ with hU'
  have hfr : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun q : U' => F' (Tub.tubr hM hMc hne q.1.1, q.1.2)) :=
    hF'.comp (contMDiff_tubr_prod hM hMc hne)
  intro q hq
  have hqU : q ∈ U'.1 := ⟨hq.1, mem_univ _⟩
  have h1 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun q : EuclideanSpace ℝ (Fin (K + 1)) × ℝ => F' (Tub.tubr hM hMc hne q.1, q.2)) q :=
    (contMDiffAt_subtype_iff (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (n := ∞) (U := U')
      (f := fun q : EuclideanSpace ℝ (Fin (K + 1)) × ℝ => F' (Tub.tubr hM hMc hne q.1, q.2))
      (x := ⟨q, hqU⟩)).1 (hfr ⟨q, hqU⟩)
  have h2 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z) (F' (Tub.tubr hM hMc hne q.1, q.2)) :=
    contMDiffAt_extChartAt' (n := ∞)
      (by rw [← extChartAt_source 𝓘(ℝ, EuclideanSpace ℝ (Fin p))]; exact hq.2)
  have := h2.comp q h1
  rw [contMDiffAt_iff_contDiffAt] at this
  exact this.contDiffWithinAt

/-- `F̃' = c ∘ F'` on `M × ℝ`. -/
theorem Fh_of_mem {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M) (t : ℝ) :
    Fh hM hMc hne F' z (x, t) = extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z (F' (⟨x, hx⟩, t)) := by
  unfold Fh; rw [tubr_mem_of_mem hM hMc hne hx]

theorem mem_Wh_of_mem {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M) (t : ℝ)
    (hfx : F' (⟨x, hx⟩, t) ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z).source) :
    (x, t) ∈ Wh hM hMc hne F' z := by
  refine ⟨?_, ?_⟩
  · show infDist x M < _
    rw [infDist_zero_of_mem hx]; exact Tub.tubε_pos hM hMc hne
  · show F' (Tub.tubr hM hMc hne x, t) ∈ _
    rw [tubr_mem_of_mem hM hMc hne hx]; exact hfx

/-- `A q = dF̃'_q`. -/
def Ah (F' : M × ℝ → Sph p) (z : Sph p) (q : EuclideanSpace ℝ (Fin (K + 1)) × ℝ) :
    EuclideanSpace ℝ (Fin (K + 1)) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  fderiv ℝ (Fh hM hMc hne F' z) q

include hF' in
theorem hasFDerivAt_Fh {q : EuclideanSpace ℝ (Fin (K + 1)) × ℝ} (hq : q ∈ Wh hM hMc hne F' z) :
    HasFDerivAt (Fh hM hMc hne F' z) (Ah hM hMc hne F' z q) q :=
  (((contDiffOn_Fh hM hMc hne hF').differentiableOn (by simp)) q hq).differentiableAt
    ((isOpen_Wh hM hMc hne hF').mem_nhds hq) |>.hasFDerivAt

include hF' in
theorem contDiffOn_Ah : ContDiffOn ℝ ∞ (Ah hM hMc hne F' z) (Wh hM hMc hne F' z) :=
  (contDiffOn_Fh hM hMc hne hF').fderiv_of_isOpen (isOpen_Wh hM hMc hne hF') (by simp)

/-- The embedding `M × ℝ → ℝᴷ⁺¹ × ℝ` is smooth. -/
theorem contMDiff_embXR :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) ∞ (embXR (M := M)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact (hM.contMDiff_val.comp (contMDiff_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    (J := 𝓘(ℝ, ℝ)) (M := M) (N := ℝ))).prodMk
    (contMDiff_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (J := 𝓘(ℝ, ℝ)) (M := M) (N := ℝ))

include hF' in
/-- The chain rule along `M × ℝ`. -/
theorem Ah_comp_mfd_embXR (q : M × ℝ)
    (hfq : F' q ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z).source) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    (Ah hM hMc hne F' z (embXR q)).comp (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (embXR (M := M)) q) =
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z) (F' q)).comp
        (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) F' q) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have h1 : Fh hM hMc hne F' z ∘ (embXR (M := M)) =
      fun q => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z (F' q) := by
    funext q
    simp only [Function.comp, embXR]
    rw [Fh_of_mem hM hMc hne q.1.2]
  have hd := (hasFDerivAt_Fh hM hMc hne hF' (mem_Wh_of_mem hM hMc hne q.1.2 q.2 hfq)).hasMFDerivAt
  have h2 := hd.comp q (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)) ((contMDiff_embXR hM).mdifferentiableAt (by simp)))
  rw [h1] at h2
  have h3 := (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    (mdifferentiableAt_extChartAt (by rwa [← extChartAt_source 𝓘(ℝ, EuclideanSpace ℝ (Fin p))]))).comp
    q (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (hF'.mdifferentiableAt (by simp)))
  exact hasMFDerivAt_unique h2 h3

include hF' hz in
theorem surjective_Ah (q : M × ℝ) (hq : F' q = z) : Surjective (Ah hM hMc hne F' z (embXR q)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hsrc : F' q ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z).source := by
    rw [hq]; exact mem_extChartAt_source z
  have h := Ah_comp_mfd_embXR hM hMc hne hF' q hsrc
  have hs1 : Surjective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) F' q) := hz q hq
  have hs2 : Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z) (F' q)) := by
    obtain ⟨D, hD⟩ := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) hsrc
    show Surjective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z) (F' q))
    rw [← hD]; exact D.surjective
  have : Surjective ((Ah hM hMc hne F' z (embXR q)).comp
      (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (embXR (M := M)) q)) := by
    rw [h]; exact hs2.comp hs1
  exact Surjective.of_comp this

include hF' in
/-- Normal vectors of `M` (paired with `0`) lie in the kernel of `dF̃'`. -/
theorem Ah_normal_eq_zero {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M) (t : ℝ)
    (hfx : F' (⟨x, hx⟩, t) ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z).source)
    {v : EuclideanSpace ℝ (Fin (K + 1))} (hv : ∀ w ∈ tangentM hM ⟨x, hx⟩, ⟪v, w⟫ = 0) :
    Ah hM hMc hne F' z (x, t) (v, 0) = 0 := by
  have hev := (Tub.tubr_spec hM hMc hne).2.2.2.2.2.2 x hx v hv
  have hd : HasDerivAt (fun s : ℝ => Fh hM hMc hne F' z (x + s • v, t))
      (Ah hM hMc hne F' z (x, t) (v, 0)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => (x + s • v, t)) (v, 0) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
      simpa using this.prodMk (hasDerivAt_const (0 : ℝ) t)
    have h2 : HasFDerivAt (Fh hM hMc hne F' z) (Ah hM hMc hne F' z (x, t)) (x + (0 : ℝ) • v, t) := by
      rw [zero_smul, add_zero]
      exact hasFDerivAt_Fh hM hMc hne hF' (mem_Wh_of_mem hM hMc hne hx t hfx)
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have hconst : (fun s : ℝ => Fh hM hMc hne F' z (x + s • v, t)) =ᶠ[𝓝 (0 : ℝ)]
      fun _ => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z (F' (⟨x, hx⟩, t)) := by
    filter_upwards [hev] with s hs
    unfold Fh
    have : Tub.tubr hM hMc hne (x + s • v) = ⟨x, hx⟩ := Subtype.ext hs
    simp only [this]
  have hd0 : HasDerivAt (fun s : ℝ => Fh hM hMc hne F' z (x + s • v, t)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) _).congr_of_eventuallyEq hconst
  exact hd.unique hd0

/-! ### The framing of `F'⁻¹(z)` -/

/-- The pulled-back framing on the level set. -/
def uh (F' : M × ℝ → Sph p) (z : Sph p) (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p)
    (q : F' ⁻¹' {z}) : EuclideanSpace ℝ (Fin (K + 1)) × ℝ :=
  pinvXR (Ah hM hMc hne F' z (embXR q.1)) (b i)

include hF' hz in
theorem Ah_uh (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p) (q : F' ⁻¹' {z}) :
    Ah hM hMc hne F' z (embXR q.1) (uh hM hMc hne F' z b i q) = b i :=
  comp_pinvXR (surjective_Ah hM hMc hne hF' hz q.1 q.2) (b i)

include hF' hz in
/-- The tangent space of the level set lies in the kernel of `dF̃'`. -/
theorem Ah_tangentS_eq_zero (hnp : n + p = m) (q : F' ⁻¹' {z})
    {w : EuclideanSpace ℝ (Fin (K + 1)) × ℝ}
    (hw : w ∈ tangentS hM (isSliceSubmanifold_levelXR hM hF' hz hnp) q) :
    Ah hM hMc hne F' z (embXR q.1) w = 0 := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hS := isSliceSubmanifold_levelXR hM hF' hz hnp
  letI := hS.chartedSpace
  haveI := hS.isManifold
  obtain ⟨a, rfl⟩ := hw
  have hfq : F' q.1 = z := q.2
  have hsrc : F' q.1 ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z).source := by
    rw [hfq]; exact mem_extChartAt_source z
  have hconst : (Fh hM hMc hne F' z ∘ fun r : F' ⁻¹' {z} => embXR r.1) =
      fun _ => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z z := by
    funext r
    simp only [Function.comp, embXR]
    rw [Fh_of_mem hM hMc hne r.1.1.2]
    have : F' r.1 = z := r.2
    rw [Subtype.coe_eta, this]
  have hemb : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (fun r : F' ⁻¹' {z} => embXR r.1) q :=
    ((contMDiff_embXR hM).comp hS.contMDiff_val).mdifferentiableAt (by simp)
  have hd := (hasFDerivAt_Fh hM hMc hne hF' (mem_Wh_of_mem hM hMc hne q.1.1.2 q.1.2
    (by rw [Subtype.coe_eta]; exact hsrc))).hasMFDerivAt
  have h2 := hd.comp q (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)) hemb)
  rw [hconst] at h2
  have h3 := hasMFDerivAt_const (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (c := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z z) (x := q)
  have h4 := hasMFDerivAt_unique h2 h3
  have h5 : (Ah hM hMc hne F' z (embXR q.1)).comp (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (fun r : F' ⁻¹' {z} => embXR r.1) q) =
      (0 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin p)) := h4
  have := congrArg (fun L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin p) => L a) h5
  simpa using this

include hF' hz in
theorem uh_normal (hnp : n + p = m) (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p)
    (q : F' ⁻¹' {z}) :
    ∀ w ∈ tangentS hM (isSliceSubmanifold_levelXR hM hF' hz hnp) q,
      ipXR (uh hM hMc hne F' z b i q) w = 0 := fun w hw =>
  ipXR_pinvXR_eq_zero _ _ (Ah_tangentS_eq_zero hM hMc hne hF' hz hnp q hw)

include hF' in
theorem uh_tangent (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p) (q : F' ⁻¹' {z}) :
    (uh hM hMc hne F' z b i q).1 ∈ tangentM hM q.1.1 := by
  have hsrc : F' (⟨q.1.1.1, q.1.1.2⟩, q.1.2) ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z).source := by
    rw [Subtype.coe_eta]
    have : F' q.1 = z := q.2
    rw [Prod.mk.eta, this]; exact mem_extChartAt_source z
  have h1 : (uh hM hMc hne F' z b i q).1 ∈ ((tangentM hM q.1.1)ᗮ)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro v hv
    have hv' : ∀ w ∈ tangentM hM ⟨q.1.1.1, q.1.1.2⟩, ⟪v, w⟫ = 0 := fun w hw =>
      (Submodule.mem_orthogonal' _ _).1 hv w hw
    have h0 : Ah hM hMc hne F' z (embXR q.1) (v, 0) = 0 :=
      Ah_normal_eq_zero hM hMc hne hF' q.1.1.2 q.1.2 hsrc hv'
    have := ipXR_pinvXR_eq_zero (Ah hM hMc hne F' z (embXR q.1)) (b i) h0
    unfold ipXR at this
    unfold uh
    simpa using this
  rwa [Submodule.orthogonal_orthogonal] at h1

include hF' hz in
theorem uh_indep {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
    (q : F' ⁻¹' {z}) : LinearIndependent ℝ (fun i => uh hM hMc hne F' z b i q) := by
  refine LinearIndependent.of_comp (Ah hM hMc hne F' z (embXR q.1) :
    EuclideanSpace ℝ (Fin (K + 1)) × ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) ?_
  have : ((Ah hM hMc hne F' z (embXR q.1) :
      EuclideanSpace ℝ (Fin (K + 1)) × ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) ∘
      fun i => uh hM hMc hne F' z b i q) = b := by
    funext i; exact Ah_uh hM hMc hne hF' hz b i q
  rw [this]; exact hb

include hF' hz in
theorem contMDiff_uh (hnp : n + p = m) (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    letI := (isSliceSubmanifold_levelXR hM hF' hz hnp).chartedSpace;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) ∞
      (uh hM hMc hne F' z b i) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hS := isSliceSubmanifold_levelXR hM hF' hz hnp
  letI := hS.chartedSpace
  haveI := hS.isManifold
  intro q
  have hsrc : F' (⟨q.1.1.1, q.1.1.2⟩, q.1.2) ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z).source := by
    rw [Subtype.coe_eta]
    have : F' q.1 = z := q.2
    rw [Prod.mk.eta, this]; exact mem_extChartAt_source z
  have hq : embXR q.1 ∈ Wh hM hMc hne F' z := mem_Wh_of_mem hM hMc hne q.1.1.2 q.1.2 hsrc
  have hA : ContDiffAt ℝ ∞ (Ah hM hMc hne F' z) (embXR q.1) :=
    (contDiffOn_Ah hM hMc hne hF').contDiffAt ((isOpen_Wh hM hMc hne hF').mem_nhds hq)
  have hAd : ContDiffAt ℝ ∞ (fun w => adjXR (Ah hM hMc hne F' z w)) (embXR q.1) :=
    ((adjXRL (k := K + 1) (p := p)).contDiff.contDiffAt).comp (embXR q.1) hA
  have hAA : ContDiffAt ℝ ∞ (fun w => (Ah hM hMc hne F' z w).comp (adjXR (Ah hM hMc hne F' z w)))
      (embXR q.1) := hA.clm_comp hAd
  obtain ⟨u, hu⟩ := isUnit_comp_adjXR (surjective_Ah hM hMc hne hF' hz q.1 q.2)
  have hinv : ContDiffAt ℝ ∞ (fun w => Ring.inverse ((Ah hM hMc hne F' z w).comp
      (adjXR (Ah hM hMc hne F' z w)))) (embXR q.1) := by
    have := contDiffAt_ringInverse ℝ (n := ∞) u
    rw [hu] at this
    exact this.comp (embXR q.1) hAA
  have hpinv : ContDiffAt ℝ ∞ (fun w => pinvXR (Ah hM hMc hne F' z w) (b i)) (embXR q.1) := by
    unfold pinvXR
    exact (hAd.clm_comp hinv).clm_apply contDiffAt_const
  have hemb : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) ∞
      (fun r : F' ⁻¹' {z} => embXR r.1) := (contMDiff_embXR hM).comp hS.contMDiff_val
  show ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) ∞
    ((fun w => pinvXR (Ah hM hMc hne F' z w) (b i)) ∘ fun r : F' ⁻¹' {z} => embXR r.1) q
  exact ContMDiffAt.comp q hpinv.contMDiffAt hemb.contMDiffAt

/-! ### The ends -/

variable {f : M → Sph p}

include hF' in
/-- Where the homotopy is constant in time (on an open set of times), `dF̃'` is the derivative
of the extension of `f`. -/
theorem Ah_eq_At_of_const
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    {O : Set ℝ} (hO : IsOpen O) (hFO : ∀ x t, t ∈ O → F' (x, t) = f x)
    {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M) {t : ℝ} (ht : t ∈ O) (hfx : f ⟨x, hx⟩ = z) :
    Ah hM hMc hne F' z (x, t) = (At hM hMc hne f z x).comp (ContinuousLinearMap.fst ℝ _ _) := by
  have hsrc : f ⟨x, hx⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z).source := by
    rw [hfx]; exact mem_extChartAt_source z
  have hev : Fh hM hMc hne F' z =ᶠ[𝓝 (x, t)] fun q => Ft hM hMc hne f z q.1 := by
    have hopen : IsOpen {q : EuclideanSpace ℝ (Fin (K + 1)) × ℝ | q.2 ∈ O} :=
      hO.preimage continuous_snd
    filter_upwards [hopen.mem_nhds (show t ∈ O from ht)] with q hq
    simp only [Fh, Ft]
    rw [hFO _ _ hq]
  have hd : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin (K + 1)) × ℝ => Ft hM hMc hne f z q.1)
      ((At hM hMc hne f z x).comp (ContinuousLinearMap.fst ℝ _ _)) (x, t) := by
    have := (hasFDerivAt_Ft hM hMc hne hf (mem_Wt_of_mem hM hMc hne hx hsrc)).comp (x, t)
      (hasFDerivAt_fst (p := (x, t)) : HasFDerivAt (Prod.fst : EuclideanSpace ℝ (Fin (K + 1)) × ℝ →
        EuclideanSpace ℝ (Fin (K + 1))) (ContinuousLinearMap.fst ℝ _ _) _)
    exact this
  unfold Ah
  rw [hev.fderiv_eq, hd.fderiv]

include hF' in
theorem uh_end
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    {O : Set ℝ} (hO : IsOpen O) (hFO : ∀ x t, t ∈ O → F' (x, t) = f x)
    (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p) (q : F' ⁻¹' {z})
    (hq : q.1.1 ∈ f ⁻¹' {z}) (ht : q.1.2 ∈ O) :
    uh hM hMc hne F' z b i q = (pontV hM hMc hne f z b i ⟨q.1.1, hq⟩, 0) := by
  unfold uh pontV
  have hfx : f ⟨q.1.1.1, q.1.1.2⟩ = z := hq
  have : embXR q.1 = (q.1.1.1, q.1.2) := rfl
  rw [this, Ah_eq_At_of_const hM hMc hne hF' hf hO hFO q.1.1.2 ht hfx, pinvXR_comp_fst]

end hom

/-! ### The cobordism -/

section main

variable {f g : M → Sph p} {F' : M × ℝ → Sph p} {z : Sph p}

/-- **Homotopic maps have framed cobordant Pontryagin manifolds** (Milnor §7, Lemma 3, for a
homotopy constant near the ends and a common regular value `z`). -/
theorem framedCobordant_of_homotopy (hnp : n + p = m) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hF' : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ F')
    (hz : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) F' z)
    (hF0 : ∀ x t, t ≤ ε → F' (x, t) = f x) (hF1 : ∀ x t, 1 - ε ≤ t → F' (x, t) = g x)
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hzf : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f z)
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ g)
    (hzg : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) g z)
    (b : Fin p → EuclideanSpace ℝ (Fin p)) (hb : LinearIndependent ℝ b) :
    FramedCobordant hM (pontryagin hM hMc hne hf hzf hnp b hb) (pontryagin hM hMc hne hg hzg hnp b hb) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  refine ⟨{ S := F' ⁻¹' {z}
            hS := isSliceSubmanifold_levelXR hM hF' hz hnp
            ε := ε
            hε := hε
            hε' := hε'
            end0 := ?_
            end1 := ?_
            compact := ?_
            u := uh hM hMc hne F' z b
            smooth := fun i => contMDiff_uh hM hMc hne hF' hz hnp b i
            tangent := fun i q => uh_tangent hM hMc hne hF' b i q
            normal := fun i q w hw => uh_normal hM hMc hne hF' hz hnp b i q w hw
            indep := fun q => uh_indep hM hMc hne hF' hz hb q
            u_end0 := ?_
            u_end1 := ?_ }⟩
  · intro q hq
    show F' q = z ↔ f q.1 = z
    rw [← Prod.mk.eta (p := q), hF0 q.1 q.2 hq.le]
  · intro q hq
    show F' q = z ↔ g q.1 = z
    rw [← Prod.mk.eta (p := q), hF1 q.1 q.2 hq.le]
  · have hset : {q ∈ F' ⁻¹' {z} | 0 ≤ q.2 ∧ q.2 ≤ 1} =
        F' ⁻¹' {z} ∩ ({q : M × ℝ | 0 ≤ q.2} ∩ {q | q.2 ≤ 1}) := by
      ext q; simp [and_assoc]
    rw [hset]
    refine (isCompact_univ.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))).of_isClosed_subset ?_ ?_
    · exact (isClosed_singleton.preimage hF'.continuous).inter
        ((isClosed_le continuous_const continuous_snd).inter (isClosed_le continuous_snd continuous_const))
    · rintro q ⟨-, h1, h2⟩
      exact ⟨mem_univ _, h1, h2⟩
  · intro i q hq ht
    exact uh_end hM hMc hne hF' hf isOpen_Iio (fun x t ht' => hF0 x t (le_of_lt ht')) b i q hq ht
  · intro i q hq ht
    exact uh_end hM hMc hne hF' hg isOpen_Ioi (fun x t ht' => hF1 x t (le_of_lt ht')) b i q hq ht

end main

end Framed

end Milnor
