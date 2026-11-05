import Milnor.Chapter2.LevelSet
import Milnor.Chapter2.Boundary

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §2, Lemmas 3 and 4 (pp. 12–13).

> Let `M` be a manifold without boundary and let `g : M → ℝ` have `0` as regular value.
>
> **Lemma 3.** The set of `x` in `M` with `g(x) ≥ 0` is a smooth manifold, with boundary equal
> to `g⁻¹(0)`. The proof is just like the proof of Lemma 1.
>
> **Lemma 4.** Let `X` be an `m`-manifold with boundary, `f : X → N` smooth, `m > n`. If `y ∈ N`
> is a regular value, both for `f` and for the restriction `f|∂X`, then `f⁻¹(y) ⊆ X` is a smooth
> `(m-n)`-manifold with boundary. Furthermore the boundary `∂(f⁻¹(y))` is precisely equal to the
> intersection of `f⁻¹(y)` with `∂X`.

**Lemma 3.** At a point with `g(x) = 0`, the slice chart of Lemma 1 for `g` (with target `ℝ`) has
second coordinate exactly `g`; swapping the factors gives a half-slice chart with first coordinate
`g`. At a point with `g(x) > 0` any chart of `M`, composed with a linear isomorphism
`E ≅ ℝ × Z` and a translation, and restricted to the open set where both `g` and the first
coordinate are positive, is a half-slice chart (with no boundary points in its domain).

**Lemma 4.** We take `X = {g ≥ 0}` inside a boundaryless manifold `M`, with `f` defined and
smooth on `M`. Milnor's condition "`y` is regular for `f|∂X`" is expressed as: at each
`x ∈ f⁻¹(y) ∩ g⁻¹(0)`, the kernel of `dfₓ` is not contained in the kernel of `dgₓ` (this is his
sentence "the hypothesis that `f|∂Hᵐ` is regular at `x` guarantees that this null space cannot be
completely contained in `ℝᵐ⁻¹ × 0`"). The proof is then exactly Milnor's: `f⁻¹(y)` is a
submanifold `M'` (Lemma 1), the function `π = g|M'` has `0` as a regular value because the tangent
space of `M'` is `ker dfₓ` (Lemma 2), and Lemma 3 applied to `(M', π)` gives the result.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

/-! ### Two ways of producing partial diffeomorphisms -/

section helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- An extended chart of a boundaryless manifold, as a partial diffeomorphism. -/
def PartialDiffeomorph.ofExtChartAt (x : M) : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    show ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I x) (extChartAt I x).source
    rw [extChartAt_source]
    exact contMDiffOn_extChartAt
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

@[simp] theorem PartialDiffeomorph.ofExtChartAt_source (x : M) :
    (PartialDiffeomorph.ofExtChartAt I x).source = (extChartAt I x).source := rfl

@[simp] theorem PartialDiffeomorph.ofExtChartAt_apply (x p : M) :
    (PartialDiffeomorph.ofExtChartAt I x) p = extChartAt I x p := rfl

variable {I}

/-- A homeomorphism between normed spaces that is smooth in both directions, as a partial
diffeomorphism with source and target everything. -/
def PartialDiffeomorph.ofHomeomorph {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : E ≃ₜ F) (h₁ : ContDiff ℝ ∞ h) (h₂ : ContDiff ℝ ∞ h.symm) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞ where
  toPartialEquiv := h.toEquiv.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := h₁.contMDiff.contMDiffOn
  contMDiffOn_invFun := h₂.contMDiff.contMDiffOn

@[simp] theorem PartialDiffeomorph.ofHomeomorph_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (h : E ≃ₜ F) (h₁ : ContDiff ℝ ∞ h) (h₂ : ContDiff ℝ ∞ h.symm) (u : E) :
    (PartialDiffeomorph.ofHomeomorph h h₁ h₂) u = h u := rfl

@[simp] theorem PartialDiffeomorph.ofHomeomorph_source {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (h : E ≃ₜ F) (h₁ : ContDiff ℝ ∞ h) (h₂ : ContDiff ℝ ∞ h.symm) :
    (PartialDiffeomorph.ofHomeomorph h h₁ h₂).source = univ := rfl

end helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Lemma 3 -/

/-- **Milnor's Lemma 3** (p. 12): if `0` is a regular value of the smooth function `g : M → ℝ`,
then `{g ≥ 0}` is a manifold with boundary `g⁻¹(0)`, modelled on the half-space over any `Z` of
dimension `dim M - 1`. -/
theorem isHalfSliceSubmanifold_of_regularValue {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (hZ : finrank ℝ Z + 1 = finrank ℝ E)
    {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) (h0 : IsRegularValue I 𝓘(ℝ, ℝ) g 0) :
    IsHalfSliceSubmanifold I Z {p | 0 ≤ g p} {p | g p = 0} := by
  intro p hp
  have hp' : 0 ≤ g p := hp
  rcases eq_or_lt_of_le hp' with h | h
  · -- A boundary point: use the slice chart of Lemma 1 for `g`, swapping the factors.
    have hZ' : finrank ℝ Z + finrank ℝ ℝ = finrank ℝ E := by rw [Module.finrank_self]; exact hZ
    obtain ⟨σ, hpσ, hform⟩ := exists_sliceChart_preimage (Z := Z) hZ' hg h0
      (x := p) (by simp [h.symm])
    have hform' : ∀ q ∈ σ.φ.source, (σ.φ q).2 = g q := fun q hq => by
      rw [hform q hq]
      simp [extChartAt_self_apply, chartAt_self_eq]
    let swapD : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, ℝ × Z) (Z × ℝ) (ℝ × Z) ∞ :=
      PartialDiffeomorph.ofHomeomorph (Homeomorph.prodComm Z ℝ)
        (contDiff_snd.prodMk contDiff_fst) (contDiff_snd.prodMk contDiff_fst)
    let Φ : PartialDiffeomorph I 𝓘(ℝ, ℝ × Z) M (ℝ × Z) ∞ := σ.φ.trans swapD
    have hΦ_source : Φ.source = σ.φ.source := by
      show (σ.φ.toOpenPartialHomeomorph.trans swapD.toOpenPartialHomeomorph).source = _
      rw [OpenPartialHomeomorph.trans_source]
      exact inter_eq_left.2 fun _ _ => mem_univ _
    have hΦ_apply : ∀ q, (Φ q).1 = (σ.φ q).2 := fun q => by
      show ((σ.φ.toOpenPartialHomeomorph.trans swapD.toOpenPartialHomeomorph) q).1 = _
      rw [OpenPartialHomeomorph.trans_apply]
      rfl
    refine ⟨⟨Φ, p, hp, by rw [hΦ_source]; exact hpσ, ?_, ?_⟩, by rw [hΦ_source]; exact hpσ⟩
    · intro q hq
      rw [hΦ_source] at hq
      rw [hΦ_apply, hform' q hq]
      exact Iff.rfl
    · intro q hq
      rw [hΦ_source] at hq
      rw [hΦ_apply, hform' q hq]
      exact Iff.rfl
  · -- An interior point: a chart of `M`, straightened by a linear isomorphism and a translation.
    have hE : finrank ℝ E = finrank ℝ (ℝ × Z) := by
      rw [Module.finrank_prod, Module.finrank_self]; omega
    let e : E ≃L[ℝ] ℝ × Z := ContinuousLinearEquiv.ofFinrankEq hE
    set c : ℝ := 1 - (e (extChartAt I p p)).1 with hc
    let A : E ≃ₜ ℝ × Z := e.toHomeomorph.trans (Homeomorph.addRight ((c, 0) : ℝ × Z))
    have hA : ∀ u, A u = e u + (c, 0) := fun u => rfl
    let AD : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × Z) E (ℝ × Z) ∞ :=
      PartialDiffeomorph.ofHomeomorph A (e.contDiff.add contDiff_const)
        (by
          have : (A.symm : ℝ × Z → E) = fun v => e.symm (v + -(c, 0)) := by
            funext v
            rfl
          rw [this]
          exact e.symm.contDiff.comp (contDiff_id.add contDiff_const))
    let Φ₀ : PartialDiffeomorph I 𝓘(ℝ, ℝ × Z) M (ℝ × Z) ∞ :=
      (PartialDiffeomorph.ofExtChartAt I p).trans AD
    have hΦ₀_source : Φ₀.source = (extChartAt I p).source := by
      show ((PartialDiffeomorph.ofExtChartAt I p).toOpenPartialHomeomorph.trans
        AD.toOpenPartialHomeomorph).source = _
      rw [OpenPartialHomeomorph.trans_source]
      exact inter_eq_left.2 fun _ _ => mem_univ _
    have hΦ₀_apply : ∀ q, Φ₀ q = e (extChartAt I p q) + (c, 0) := fun q => by
      show ((PartialDiffeomorph.ofExtChartAt I p).toOpenPartialHomeomorph.trans
        AD.toOpenPartialHomeomorph) q = _
      rw [OpenPartialHomeomorph.trans_apply]
      rfl
    -- The open set where `g > 0` and the first coordinate is positive.
    set s : Set M := {q | 0 < g q} ∩ (Φ₀.source ∩ Φ₀ ⁻¹' {u | 0 < u.1}) with hs
    have hs_open : IsOpen s :=
      (isOpen_lt continuous_const hg.continuous).inter
        (Φ₀.contMDiffOn.continuousOn.isOpen_inter_preimage Φ₀.open_source
          (isOpen_lt continuous_const continuous_fst))
    have hps : p ∈ s := by
      refine ⟨h, ⟨by rw [hΦ₀_source]; exact mem_extChartAt_source p, ?_⟩⟩
      show 0 < (Φ₀ p).1
      rw [hΦ₀_apply]
      simp [hc]
    let Φ := Φ₀.restrOpen s hs_open
    have hΦ_source : Φ.source = Φ₀.source ∩ s := rfl
    refine ⟨⟨Φ, p, hp, ⟨by rw [hΦ₀_source]; exact mem_extChartAt_source p, hps⟩, ?_, ?_⟩,
      ⟨by rw [hΦ₀_source]; exact mem_extChartAt_source p, hps⟩⟩
    · intro q hq
      have h1 : 0 < g q := hq.2.1
      have h2 : 0 < (Φ₀ q).1 := hq.2.2.2
      exact iff_of_true (le_of_lt h1) (le_of_lt h2)
    · intro q hq
      have h1 : 0 < g q := hq.2.1
      have h2 : 0 < (Φ₀ q).1 := hq.2.2.2
      exact iff_of_false (ne_of_gt h1) (ne_of_gt h2)

/-! ### Lemma 4 -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

/-- **Milnor's Lemma 4** (p. 13). Let `X = {g ≥ 0} ⊆ M` with `0` a regular value of `g`, let
`f : M → N` be smooth with `y` a regular value, and suppose that at every point of
`f⁻¹(y) ∩ g⁻¹(0)` the kernel of `df` is not contained in the kernel of `dg` (regularity of `y`
for `f|∂X`). Then `f⁻¹(y) ∩ X` is a manifold with boundary `f⁻¹(y) ∩ g⁻¹(0)`: precisely, inside
the submanifold `f⁻¹(y)` of Lemma 1, the set `{g ≥ 0}` is a half-slice submanifold with
boundary `{g = 0}`. -/
theorem isHalfSliceSubmanifold_levelSet {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (hZ : finrank ℝ Z + finrank ℝ F = finrank ℝ E)
    {Z' : Type*} [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] [FiniteDimensional ℝ Z']
    (hZ' : finrank ℝ Z' + 1 = finrank ℝ Z)
    {f : M → N} (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y)
    {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (hreg : ∀ x, f x = y → g x = 0 →
      ∃ v, mfderiv I J f x v = 0 ∧ mfderiv I 𝓘(ℝ, ℝ) g x v ≠ 0) :
    letI := (isSliceSubmanifold_preimage hZ hf hy).chartedSpace
    IsHalfSliceSubmanifold 𝓘(ℝ, Z) Z' {q : f ⁻¹' {y} | 0 ≤ g q.1} {q | g q.1 = 0} := by
  set hS := isSliceSubmanifold_preimage hZ hf hy
  letI := hS.chartedSpace
  haveI := hS.isManifold
  -- `π = g ∘ incl` is smooth on `f⁻¹(y)` and has `0` as a regular value.
  have hπ : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ (g ∘ (Subtype.val : f ⁻¹' {y} → M)) :=
    hg.comp hS.contMDiff_val
  have h0 : IsRegularValue 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) (g ∘ (Subtype.val : f ⁻¹' {y} → M)) 0 := by
    intro q hq
    have hq' : g q.1 = 0 := hq
    obtain ⟨v, hv1, hv2⟩ := hreg q.1 q.2 hq'
    -- `v` lies in the tangent space of `f⁻¹(y)`, i.e. in the range of `d(incl)` (Lemma 2).
    obtain ⟨w, hw⟩ := (mem_range_mfderiv_val_iff hZ hf hy q v).2 hv1
    have hval : MDifferentiableAt 𝓘(ℝ, Z) I (Subtype.val : f ⁻¹' {y} → M) q :=
      hS.contMDiff_val.mdifferentiableAt (by simp)
    have hg' : MDifferentiableAt I 𝓘(ℝ, ℝ) g q.1 := hg.mdifferentiableAt (by simp)
    have hchain : mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) (g ∘ Subtype.val) q =
        (mfderiv I 𝓘(ℝ, ℝ) g q.1).comp (mfderiv 𝓘(ℝ, Z) I Subtype.val q) := mfderiv_comp q hg' hval
    set a : ℝ := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) (g ∘ Subtype.val) q w with ha
    have hw' : a ≠ 0 := by
      rw [ha, hchain]
      show mfderiv I 𝓘(ℝ, ℝ) g q.1 (mfderiv 𝓘(ℝ, Z) I Subtype.val q w) ≠ 0
      rw [hw]
      exact hv2
    -- A nonzero linear map to `ℝ` is onto.
    intro t
    let t' : ℝ := t
    refine ⟨(t' / a) • w, ?_⟩
    have hsmul := (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) (g ∘ Subtype.val) q).map_smul (t' / a) w
    refine hsmul.trans ?_
    show (t' / a) • a = t'
    rw [smul_eq_mul, div_mul_cancel₀ t' hw']
  exact isHalfSliceSubmanifold_of_regularValue hZ' hπ h0

end Milnor
