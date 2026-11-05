import Morse.Chapter2.CellPatch
import Morse.Chapter2.Submanifold
import Morse.Chapter1.ManifoldMorse

/-!
Milnor, *Morse Theory*, §3, pp. 14–19, for a submanifold of Euclidean space.

# Theorem 3.2 for a function on a submanifold `N ⊆ ℝᴷ`

**Theorem 3.2** (p. 14), paraphrased: let `f : M → ℝ` be smooth and `p` a non-degenerate critical
point of index `λ`, `c = f(p)`, such that `f⁻¹[c - ε, c + ε]` is compact and contains no critical
point other than `p`, for some `ε > 0`. Then for all sufficiently small `ε`, `M^{c+ε}` has the
homotopy type of `M^{c-ε}` with a `λ`-cell attached. (The text as reproduced in the scan reads
"a `k`-cell", probably a defect of the scan; see `Exposition/Findings.md`, "About the scan".)

`Morse/Chapter2/CellAttach.lean` proves it for `M = ℝⁿ`. This file proves it for `M = N` a slice
submanifold of a finite-dimensional real normed space `V` (Milnor's `ℝᴷ`; the companion project's
`Milnor.IsSliceSubmanifold`, with its manifold structure `hN.chartedSpace`) and `f = F|N` the
restriction of a smooth `F : V → ℝ`, the setting of `Morse.theorem_3_1_submanifold`
(`Morse/Chapter2/Submanifold.lean`). Milnor's proof (pp. 15–19) is transported through a Morse
chart of `N` at `p`:

1. *Morse coordinates* (p. 15): Lemma 2.2 on the manifold `N` (`Morse.morse_lemmaM`), applied in
   the domain of one slice chart `σ` of `N`, followed by the splitting `u = (x, y)`
   (`Morse.splitCoord`), gives a Morse patch `ψ : N → ℝ^λ × ℝ^{n-λ}` (`Morse.IsMorsePatch`) which is
   a smooth coordinate system of `N` (`Morse.exists_isMorsePatch_submanifold`).
2. *The function `F = f - μ(ξ + 2η)`* (p. 16) is `Morse.patchF f ψ μ`. It is smooth on `N`
   (`Morse.contMDiff_patchBump`), and it is the restriction of a smooth function on `V`
   (`Morse.exists_contDiff_comp_val_eq_of_chart`), so that Theorem 3.1 in the form proved for
   submanifolds applies to it.
3. *Assertion 1* and *Assertion 4*, the cell and the conclusion: `Morse/Chapter2/CellPatch.lean`,
   for any Hausdorff space.
4. *Assertion 2*: the critical points of `F` and `f` on `N` agree
   (`Morse.isCriticalPointM_patchF_iff`): in the coordinates `ψ` both are the origin only
   (`CellModel.hasFDerivAt_morseF_zero_iff`), and outside the closed ellipsoid `F = f`.
5. *Assertion 3*: Theorem 3.1 for `F` on `N` (`Morse.theorem_3_1_submanifold`).

## What Milnor's text leaves implicit (beyond `CellAttach.lean` and `CellPatch.lean`)

* **The Morse chart of a manifold.** Milnor applies Lemma 2.2 in "a coordinate system", without
  saying which. Here it is `Morse.morse_lemmaM` read in the domain of one slice chart, so that the
  whole construction takes place in a region where `N` is a graph over its tangent directions.
* **Theorem 3.1 is applied to `F`** (Assertion 3). The formalized Theorem 3.1 on a submanifold is
  for restrictions of ambient smooth functions (`Morse/Chapter2/Submanifold.lean`), so `F` must be
  extended to `V`. Milnor needs nothing of the sort, as his Theorem 3.1 is intrinsic. The bump
  `μ(ξ + 2η)` vanishes outside the compact ellipsoid `ξ + 2η ≤ 2ε`, which lies in the domain of the
  slice chart `σ : U → Z × W`; the extension is `x ↦ χ(x) · b(σ⁻¹((σ x)₁, 0))`, with `b` the bump
  and `χ` a smooth cut-off equal to `1` on the ellipsoid and supported where the formula makes
  sense (`Morse.exists_contDiff_comp_val_eq_of_chart`).
* **Hausdorffness** of `N` (a subset of `V`) is used for the closedness of the ellipsoid in `N`,
  hence for the smoothness of `F` and for the continuity of `r_t`.
* **Critical points of a function on `N`** are those of Mathlib's manifold derivative
  (`Morse.IsCriticalPointM`); in a smooth coordinate system they are the critical points of the
  local representative (`Morse.IsSmoothCoord.isCriticalPointM_iff`), which is how Milnor's
  computation of `dF` in the coordinates `u¹, …, uⁿ` (p. 17) is transported.

## Main results

* `Morse.exists_contDiff_comp_val_eq_of_chart`: a smooth function on `N` vanishing outside a
  compact subset of one slice chart domain is the restriction of a smooth function on `V`.
* `Morse.exists_isMorsePatch_submanifold`, `Morse.contMDiff_patchBump`,
  `Morse.isCriticalPointM_patchF_iff` (Assertion 2).
* `Morse.theorem_3_2_submanifold`: **Theorem 3.2 for `f = F|N`**: for all sufficiently small
  `ε > 0` there is a `λ`-cell `e^λ = χ(D^λ) ⊆ N^{c+ε}` (`χ` continuous and injective on the closed
  unit ball of `ℝ^λ`, hence an embedding) meeting `N^{c-ε}` exactly in `χ(S^{λ-1})`, such that
  `N^{c-ε} ∪ e^λ` is a strong deformation retract of `N^{c+ε}`.
* `Morse.theorem_3_2_attach_submanifold`: **Theorem 3.2 in Milnor's words**: `N^{c+ε}` is homotopy
  equivalent to the pushout `D^λ ⊔_{S^{λ-1}} N^{c-ε}` in `TopCat` along an embedding
  `S^{λ-1} → N^{c-ε}`.
-/

open Set Filter Topology Function Module CategoryTheory Limits TopCat
open scoped ContDiff Manifold

universe u

noncomputable section

namespace Morse

open CellModel

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V}

/-! ### Extending a function on `N` supported in one slice chart -/

/-- **A smooth function on `N` supported in a compact subset of one slice chart domain is the
restriction of a smooth function on `V`.** If `b` vanishes outside the compact set `K`, and `K`
lies in the domain of the slice chart `σ`, then `B(x) = χ(x) · b(σ⁻¹((σ x)₁, 0))`, for a smooth
cut-off `χ` equal to `1` on `K` and supported where `((σ x)₁, 0)` lies in the image of `σ`, is
smooth on `V` and equals `b` on `N`. -/
theorem exists_contDiff_comp_val_eq_of_chart [FiniteDimensional ℝ V]
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N)
    {b : N → ℝ} (hb : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ b) {K : Set N}
    (hK : IsCompact K) (hKσ : ∀ q ∈ K, (q : V) ∈ σ.φ.source) (hbK : ∀ q ∉ K, b q = 0) :
    ∃ B : V → ℝ, ContDiff ℝ ∞ B ∧ B ∘ Subtype.val = b := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  set O : Set V := σ.φ.source ∩ (fun x => ((σ.φ x).1, (0 : W))) ⁻¹' σ.φ.target with hO
  have hcont : ContinuousOn (fun x => ((σ.φ x).1, (0 : W))) σ.φ.source :=
    (continuous_fst.comp_continuousOn (contDiffOn_sliceChart σ).continuousOn).prodMk
      continuousOn_const
  have hOo : IsOpen O := hcont.isOpen_inter_preimage σ.φ.open_source σ.φ.open_target
  have hKO : Subtype.val '' K ⊆ O := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨hKσ q hq, σ.mk_zero_mem_target (hKσ q hq) q.2⟩
  obtain ⟨χ, hχ, -, hχO, -, hχK⟩ := exists_cutoff_mul (g := fun _ : V => (1 : ℝ)) contDiff_const
    (hK.image continuous_subtype_val) hOo hKO fun _ _ => one_ne_zero
  set g : V → ℝ := fun x => b (σ.toChart.symm (σ.φ x).1) with hg_def
  have hg : ContDiffOn ℝ ∞ g O := by
    have h1 : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ (b ∘ σ.toChart.symm) σ.toChart.target :=
      hb.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (toChart_mem_maximalAtlas hN σ))
    have h2 : ContDiffOn ℝ ∞ (fun x : V => (σ.φ x).1) O :=
      (contDiff_fst.comp_contDiffOn (contDiffOn_sliceChart σ)).mono inter_subset_left
    exact (contMDiffOn_iff_contDiffOn.1 h1).comp h2 fun x hx => hx.2
  refine ⟨fun x => χ x • g x, contDiff_smul_of_tsupport hOo hχ hg hχO, funext fun q => ?_⟩
  simp only [comp_apply, smul_eq_mul, hg_def]
  by_cases hqs : (q : V) ∈ σ.φ.source
  · have hq' : σ.toChart.symm (σ.φ q).1 = q := σ.toChart.left_inv hqs
    rw [hq']
    by_cases hqK : q ∈ K
    · have := hχK q ⟨q, hqK, rfl⟩
      rw [mul_one] at this
      rw [this, one_mul]
    · rw [hbK q hqK, mul_zero]
  · have hqK : q ∉ K := fun h => hqs (hKσ q h)
    have : χ q = 0 := image_eq_zero_of_notMem_tsupport fun h => hqs (hχO h).1
    rw [this, zero_mul, hbK q hqK]

/-! ### Morse patches of `N` -/

/-- **The lemma of Morse on `N` in split form**: around a non-degenerate critical point `p` of a
smooth `f : N → ℝ`, of index `λ`, there is a smooth coordinate system `ψ` of `N` with values in
`ℝ^λ × ℝ^{n-λ}` in which `f = f(p) - ‖x‖² + ‖y‖²`, whose domain lies in the domain of a slice
chart `σ` of `N`. -/
theorem exists_isMorsePatch_submanifold [FiniteDimensional ℝ Z]
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {f : N → ℝ}
    (hf : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ f) {p : N}
    (hp : letI := hN.chartedSpace; IsNondegenerateCriticalPointM Z f p) :
    letI := hN.chartedSpace
    ∃ (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N)
      (ψ : OpenPartialHomeomorph N
        (EuclideanSpace ℝ {i : Fin (finrank ℝ Z) // (i : ℕ) < indexM Z f p} ×
          EuclideanSpace ℝ {i : Fin (finrank ℝ Z) // indexM Z f p ≤ (i : ℕ)})),
      IsMorsePatch f p ψ ∧ IsSmoothCoord Z ψ ∧ ∀ q ∈ ψ.source, (q : V) ∈ σ.φ.source := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  obtain ⟨σ, hσ⟩ := hN p p.2
  have hU : IsOpen {q : N | (q : V) ∈ σ.φ.source} :=
    σ.φ.open_source.preimage continuous_subtype_val
  obtain ⟨y, hy, hpy, hyU, hyp, hfy⟩ := morse_lemmaM hU hσ hf.contMDiffOn hp
  set e := splitCoord (finrank ℝ Z) (indexM Z f p) with he
  refine ⟨σ, y.transHomeomorph e.toHomeomorph, ⟨hpy, ?_, ?_⟩, ⟨?_, ?_⟩, fun q hq => hyU hq⟩
  · change e (y p) = 0
    rw [hyp, map_zero]
  · intro q hq
    rw [hfy q hq]
    change _ = morseQuad (f p) (e (y q))
    simp only [morseQuad, xi, eta, he, norm_sq_splitCoord_fst, norm_sq_splitCoord_snd]
  · exact e.contDiff.contMDiff.comp_contMDiffOn hy.contMDiffOn
  · exact hy.contMDiffOn_symm.comp e.symm.contDiff.contMDiff.contMDiffOn fun v hv => hv

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- **Milnor's `F` is smooth on `N`** ("it is easily verified that `F` is a well defined smooth
function", p. 16): the bump `μ(ξ + 2η)` is smooth on the domain of the coordinate system `ψ`, and
vanishes outside the ellipsoid `ξ + 2η ≤ 2ε`, which is closed in `N`. -/
theorem contMDiff_patchBump (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    {ψ : OpenPartialHomeomorph N (X × Y)} (hψ : letI := hN.chartedSpace; IsSmoothCoord Z ψ)
    {ε : ℝ} {μ : ℝ → ℝ} (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ ψ.target)
    (hμ : IsMilnorMu ε μ) :
    letI := hN.chartedSpace
    ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ (patchBump ψ μ) := by
  let _ := hN.chartedSpace
  intro q
  have hxi : ContDiff ℝ ∞ (xi : X × Y → ℝ) := (contDiff_norm_sq ℝ).comp contDiff_fst
  have heta : ContDiff ℝ ∞ (eta : X × Y → ℝ) := (contDiff_norm_sq ℝ).comp contDiff_snd
  have hh : ContDiff ℝ ∞ (fun v : X × Y => μ (xi v + 2 * eta v)) :=
    hμ.contDiff.comp (hxi.add (contDiff_const.mul heta))
  by_cases hs : q ∈ ψ.source
  · have hev : patchBump ψ μ =ᶠ[𝓝 q] (fun v : X × Y => μ (xi v + 2 * eta v)) ∘ ψ := by
      filter_upwards [ψ.open_source.mem_nhds hs] with q' hq'
      rw [patchBump, indicator_of_mem hq']
      rfl
    exact (hh.contMDiff.contMDiffAt.comp q ((hψ.contMDiffOn q hs).contMDiffAt
      (ψ.open_source.mem_nhds hs))).congr_of_eventuallyEq hev
  · have hq : q ∉ patchEllipsoid ψ ε := fun h => hs (patchEllipsoid_subset_source hball h)
    refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_patchEllipsoid hball).isOpen_compl.mem_nhds hq] with q' hq'
    exact patchBump_eq_zero hball hμ hq'

/-- **Assertion 2** (p. 17) on `N`: `F` and `f` have the same critical points. In the coordinates
`ψ` both have only the origin; outside the closed ellipsoid they agree. -/
theorem isCriticalPointM_patchF_iff (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    {f : N → ℝ} {p : N} {ψ : OpenPartialHomeomorph N (X × Y)} (hφ : IsMorsePatch f p ψ)
    (hψ : letI := hN.chartedSpace; IsSmoothCoord Z ψ) {ε : ℝ} {μ : ℝ → ℝ}
    (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ ψ.target) (hμ : IsMilnorMu ε μ)
    (hf : letI := hN.chartedSpace; MDifferentiable 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) f)
    (hF : letI := hN.chartedSpace; MDifferentiable 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) (patchF f ψ μ)) (q : N) :
    letI := hN.chartedSpace
    IsCriticalPointM Z (patchF f ψ μ) q ↔ IsCriticalPointM Z f q := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  by_cases hs : q ∈ ψ.source
  · rw [hψ.isCriticalPointM_iff hs (hF q), hψ.isCriticalPointM_iff hs (hf q)]
    have h1 : patchF f ψ μ ∘ ψ.symm =ᶠ[𝓝 (ψ q)] morseF μ (f p) := by
      filter_upwards [ψ.open_target.mem_nhds (ψ.map_source hs)] with v hv
      rw [comp_apply, patchF_eq hφ (ψ.map_target hv), ψ.right_inv hv]
    have h2 : f ∘ ψ.symm =ᶠ[𝓝 (ψ q)] morseQuad (f p) := by
      filter_upwards [ψ.open_target.mem_nhds (ψ.map_source hs)] with v hv
      rw [comp_apply, hφ.apply_eq _ (ψ.map_target hv), ψ.right_inv hv]
    rw [isCriticalPoint_congr h1, isCriticalPoint_congr h2]
    exact (hasFDerivAt_morseF_zero_iff hμ _ _).trans (hasFDerivAt_morseQuad_zero_iff _ _).symm
  · have hq : q ∉ patchEllipsoid ψ ε := fun h => hs (patchEllipsoid_subset_source hball h)
    have hev : patchF f ψ μ =ᶠ[𝓝 q] f := by
      filter_upwards [(isClosed_patchEllipsoid hball).isOpen_compl.mem_nhds hq] with q' hq'
      exact patchF_eq_of_notMem hball hμ hq'
    unfold IsCriticalPointM
    rw [hev.mfderiv_eq]
    exact Iff.rfl

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup Y]
  [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y] in
/-- **Theorem 3.2 for a function on a submanifold** (Milnor, p. 14). Let `N ⊆ V` be a slice
submanifold of a finite-dimensional real normed space, `F : V → ℝ` smooth, `f = F|N`, and `p` a
non-degenerate critical point of `f` of index `λ = indexM Z f p`, `c = f(p)`. Suppose that for some
`ε₀ > 0`, `f⁻¹[c - ε₀, c + ε₀]` is compact and contains no critical point of `f` other than `p`.
Then for all sufficiently small `ε > 0` there is a map `χ` from the closed unit ball `D^λ` of `ℝ^λ`
to `N` (the cell `e^λ`), continuous and injective on `D^λ`, meeting `N^{c-ε}` exactly in
`χ(S^{λ-1})` and contained in `N^{c+ε}`, such that `N^{c-ε} ∪ e^λ` is a strong deformation retract
of `N^{c+ε}`. -/
theorem theorem_3_2_submanifold [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z]
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F) {p : N}
    (hp : letI := hN.chartedSpace; IsNondegenerateCriticalPointM Z (F ∘ Subtype.val) p)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Icc (F p - ε₀) (F p + ε₀)))
    (honly : letI := hN.chartedSpace; ∀ q : N, F q ∈ Icc (F p - ε₀) (F p + ε₀) →
      IsCriticalPointM Z (F ∘ Subtype.val) q → q = p) :
    letI := hN.chartedSpace
    ∃ ε₁ > 0, ∀ ε, 0 < ε → ε ≤ ε₁ →
      ∃ χ : EuclideanSpace ℝ (Fin (indexM Z (F ∘ Subtype.val) p)) → N,
        ContinuousOn χ (Metric.closedBall 0 1) ∧ InjOn χ (Metric.closedBall 0 1) ∧
        (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (indexM Z (F ∘ Subtype.val) p))) 1,
          χ z ∈ sublevel (F ∘ Subtype.val) (F p - ε) ↔ ‖z‖ = 1) ∧
        χ '' Metric.closedBall 0 1 ⊆ sublevel (F ∘ Subtype.val) (F p + ε) ∧
        IsStrongDeformationRetract
          ((↑) ⁻¹' (sublevel (F ∘ Subtype.val) (F p - ε) ∪ χ '' Metric.closedBall 0 1) :
            Set (sublevel (F ∘ Subtype.val : N → ℝ) (F p + ε))) := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfs : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ f := contMDiff_comp_val hN hF
  obtain ⟨σ, ψ, hφ, hψ, hψσ⟩ := exists_isMorsePatch_submanifold hN hfs hp
  have h0 : (0 : _) ∈ ψ.target := hφ.apply_self ▸ ψ.map_source hφ.mem_source
  obtain ⟨ε₂, hε₂, hball₂⟩ := exists_forall_ball_subset_patch_target h0
  refine ⟨min ε₀ ε₂, lt_min hε₀ hε₂, fun ε hε hεε₁ => ?_⟩
  have hball := hball₂ ε (hεε₁.trans (min_le_right _ _))
  have hεε₀ : ε ≤ ε₀ := hεε₁.trans (min_le_left _ _)
  have hμ := isMilnorMu_milnorMu hε
  set μ := milnorMu ε with hμ_def
  -- the bump is the restriction of a smooth function on `V`
  obtain ⟨B, hB, hBN⟩ := exists_contDiff_comp_val_eq_of_chart hN σ
    (contMDiff_patchBump hN hψ hball hμ) (isCompact_patchEllipsoid hball)
    (fun q hq => hψσ q (patchEllipsoid_subset_source hball hq))
    (fun q hq => patchBump_eq_zero hball hμ hq)
  set G : V → ℝ := fun x => F x - B x with hG_def
  have hG : ContDiff ℝ ∞ G := hF.sub hB
  have hGN : G ∘ Subtype.val = patchF f ψ μ := by
    funext q
    have := congrFun hBN q
    simp only [comp_apply] at this
    simp only [comp_apply, hG_def, patchF, hf_def, this]
  -- Assertion 2
  have hcritF : ∀ q : N, IsCriticalPointM Z (patchF f ψ μ) q ↔ IsCriticalPointM Z f q := by
    have hFd : MDifferentiable 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) (patchF f ψ μ) := by
      rw [← hGN]
      exact (contMDiff_comp_val hN hG).mdifferentiable (by simp)
    exact isCriticalPointM_patchF_iff hN hφ hψ hball hμ (hfs.mdifferentiable (by simp)) hFd
  -- Assertion 3: Theorem 3.1 for `F` on `N`
  have hsub : (G ∘ Subtype.val : N → ℝ) ⁻¹' Icc (f p - ε) (f p + ε) ⊆
      f ⁻¹' Icc (f p - ε₀) (f p + ε₀) := by
    intro q hq
    rw [mem_preimage, hGN] at hq
    have h2 : q ∈ sublevel f (f p + ε) := sublevel_patchF_add hφ hμ ▸ hq.2
    exact ⟨by linarith [hq.1, patchF_le (f := f) (φ := ψ) hμ q], by
      have h2' : f q ≤ f p + ε := h2
      linarith⟩
  have hK' : IsCompact ((G ∘ Subtype.val : N → ℝ) ⁻¹' Icc (f p - ε) (f p + ε)) :=
    hK.of_isClosed_subset (isClosed_Icc.preimage (hG.continuous.comp continuous_subtype_val)) hsub
  have hcrit : ∀ q : N, G q ∈ Icc (f p - ε) (f p + ε) →
      ¬IsCriticalPointM Z (G ∘ Subtype.val) q := by
    intro q hq hc
    rw [hGN, hcritF] at hc
    have hqp := honly q (hsub hq) hc
    subst hqp
    have h1 : (G ∘ Subtype.val) q = f q - μ 0 := by
      rw [hGN]
      exact patchF_apply_self hφ
    have h2 : f q - ε ≤ G q := hq.1
    have h3 : G q = f q - μ 0 := h1
    linarith [hμ.lt_apply_zero]
  have h3 := (theorem_3_1_submanifold hN hG (by linarith) hK' hcrit).2.1
  rw [hGN, sublevel_patchF_add hφ hμ] at h3
  have hk : indexM Z f p ≤ finrank ℝ Z := indexM_le_finrank f p
  exact patch_theorem_3_2 (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (negIdxEquiv hk)) hball hφ hμ
    hε h3

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup Y]
  [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y] in
/-- **Theorem 3.2 for a function on a submanifold, in Milnor's words** (p. 14): under the
hypotheses of `Morse.theorem_3_2_submanifold`, for all sufficiently small `ε > 0` there is an
embedding `φ : S^{λ-1} → N^{c-ε}` such that `N^{c+ε}` is homotopy equivalent to the pushout of
`D^λ ← S^{λ-1} → N^{c-ε}` in `TopCat` (`N^{c-ε}` with a `λ`-cell attached). -/
theorem theorem_3_2_attach_submanifold [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z]
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {F : V → ℝ} (hF : ContDiff ℝ ∞ F) {p : N}
    (hp : letI := hN.chartedSpace; IsNondegenerateCriticalPointM Z (F ∘ Subtype.val) p)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Icc (F p - ε₀) (F p + ε₀)))
    (honly : letI := hN.chartedSpace; ∀ q : N, F q ∈ Icc (F p - ε₀) (F p + ε₀) →
      IsCriticalPointM Z (F ∘ Subtype.val) q → q = p) :
    letI := hN.chartedSpace
    ∃ ε₁ > 0, ∀ ε, 0 < ε → ε ≤ ε₁ →
      ∃ φ : ∂𝔻 (indexM Z (F ∘ Subtype.val) p) ⟶
          TopCat.of (sublevel (F ∘ Subtype.val : N → ℝ) (F p - ε)),
        Function.Injective φ ∧
        Nonempty (ContinuousMap.HomotopyEquiv (sublevel (F ∘ Subtype.val : N → ℝ) (F p + ε))
          ((pushout φ (diskBoundaryInclusion (indexM Z (F ∘ Subtype.val) p)) : TopCat.{u}) :
            Type u)) := by
  let _ := hN.chartedSpace
  obtain ⟨ε₁, hε₁, H⟩ := theorem_3_2_submanifold hN hF hp hε₀ hK honly
  refine ⟨ε₁, hε₁, fun ε hε hεε₁ => ?_⟩
  obtain ⟨χ, hcont, hinj, hbdry, hsub, hsdr⟩ := H ε hε hεε₁
  exact exists_homotopyEquiv_pushout_of_cell (hF.continuous.comp continuous_subtype_val)
    (by linarith) hcont hinj hbdry hsub hsdr

end Morse
